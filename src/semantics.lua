-- Curtis Fenner, copyright (C) 2017

local Map = import "data/map.lua"

local Report = import "semantic-errors.lua"
local common = import "common.lua"
local excerpt = common.excerpt

local showTypeKind = common.showTypeKind
local showConstraintKind = common.showConstraintKind
local areTypesEqual = common.areTypesEqual

local UNKNOWN_LOCATION = freeze {begins = "???", ends = "???"}

local UNIT_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Unit",
}

local BOOLEAN_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Boolean",
}

local INT_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Int",
}

local STRING_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "String",
}



local SELF_TYPE = {
	tag = "self-type",
	role = "type",
}

-- RETURNS a Kind with the same structure, buch each GenericTypeKind replaced
-- with a TypeKind from the map
-- REQUIRES each GenericTypeKind mentioned by the kind is present in the map
local function substituteGenerics(kind, map)
	assertis(kind, "Kind")
	assertis(map, mapType("string", "TypeKind"))
	
	if kind.tag == "generic-type" then
		assert(map[kind.name], "definition for generic `#" .. kind.name .. "`")
		return map[kind.name]
	elseif kind.tag == "compound-type" then
		return {
			tag = "compound-type",
			role = "type",
			packageName = kind.packageName,
			definitionName = kind.definitionName,
			arguments = table.map(substituteGenerics, kind.arguments, map),
		}
	elseif kind.tag == "interface-constraint" then
		return {
			tag = "interface-constraint",
			role = "constraint",
			packageName = kind.packageName,
			definitionName = kind.definitionName,
			arguments = table.map(substituteGenerics, kind.arguments, map),
		}
	elseif kind.tag == "self-type" then
		assert(map.Self, "Self must be specified in map")

		return map.Self
	end

	-- All other Kinds are non-recursive
	return kind
end

-- RETURNS a signature with types converted
-- NOTE This does NOT affect requiresASTs, ensuresASTs. Those must be evaluated
-- in a context using the map!
local function substitutedSignature(signature, map)
	assertis(signature, "Signature")
	assertis(map, mapType("string", "TypeKind"))

	local newParameters = {}
	for _, p in ipairs(signature.parameters) do
		assertis(p, recordType {
			name = "string",
			type = "TypeKind",
		})
		table.insert(newParameters, {
			name = p.name,
			type = substituteGenerics(p.type, map)
		})
	end

	local newReturnTypes = {}
	for _, r in ipairs(signature.returnTypes) do
		table.insert(newReturnTypes, substituteGenerics(r, map))
	end

	local out = {
		-- These are type-independent
		memberName = signature.memberName,
		longName = signature.longName,
		bang = signature.bang,
		modifier = signature.modifier,
		foreign = signature.foreign,

		parameters = newParameters,
		returnTypes = newReturnTypes,

		-- Note! This are NOT substituted
		requiresASTs = signature.requiresASTs,
		ensuresASTs = signature.ensuresASTs,
		
		logic = signature.logic,
		eval = signature.eval,
	}

	assertis(out, "Signature")
	return out
end

-- RETURNS whether or not the ConstraintKind a is satisfied by the
-- ConstraintKind b.
-- NOTE: As Smol is currently designed, this only happens when a and b are the
-- same constraint
local function constraintSatisfiedBy(a, b)
	return showConstraintKind(a) == showConstraintKind(b)
end

-- RETURNS a resolving function (TypeAST => Kind)
-- The produced Kinds are fully valid: The referred types exist; they are used
-- with the correct arity; their arguments satisfy the correct constraints
-- REQUIRES definitionMap is finished
-- REQUIRES importsByName does not conflict with source's set of definitions,
-- and that there are no duplicate names in the set of definitions of a package
-- REQUIRES the return not be invoked until a resolver is made for each
-- definition in the map
local function makeDefinitionASTResolver(info, definitionMap)
	assertis(info, recordType {
		packageName = "string",
		importsByName = mapType("string", recordType {
			packageName = "string",
			definitionName = choiceType(constantType(false), "string"),
		}),
	})
	assertis(definitionMap, mapType("string", mapType("string", recordType {})))

	local shortNameMap = {}
	local usePackages = {
		[info.packageName] = info.source.package.location,
	}

	-- Check that all imports are valid and mark which short names can be used
	for _, importAST in ipairs(info.source.imports) do
		assertis(importAST, recordType {
			packageName = "string",
			definitionName = choiceType(constantType(false), "string"),
		})
		if importAST.definitionName then
			assert(not shortNameMap[importAST.definitionName])

			-- Check if such a definition really exists
			if not definitionMap[importAST.packageName][importAST.definitionName] then
				Report.UNKNOWN_DEFINITION_IMPORTED {
					name = importAST.packageName .. ":" .. importAST.definitionName,
					location = importAST.location,
				}
			end

			-- Remember the short name
			shortNameMap[importAST.definitionName] = {
				package = importAST.packageName,
				name = importAST.definitionName,
			}
		else
			-- Check if such a package really exists
			if usePackages[importAST.packageName] then
				Report.IMPORT_PACKAGE_TWICE {
					packageName = importAST.packageName,
					firstLocation = usePackages[importAST.packageName],
					secondLocation = importAST.location,
				}
			end

			-- Mark the package as usable
			usePackages[importAST.packageName] = importAST.location
		end
	end

	-- Get a list of short names for all members of this package
	for key, definition in pairs(definitionMap[info.packageName]) do
		assert(not shortNameMap[key])
		shortNameMap[key] = {
			package = info.packageName,
			name = key,
		}
	end

	-- RETURNS a completely valid Kind, when the constraints inserted to the
	-- list are met (up to meeting constraints when context.checkConstraints is
	-- false)
	local function resolver(ast, context)
		assertis(ast, recordType {
			tag = "string",
		})

		assertis(context, recordType {
			selfAllowed = choiceType(constantType(false), "InterfaceConstraintKind"),

			-- Whether or not to check if types have the constraints they need
			-- for this kind to be valid
			checkConstraints = "boolean",

			generics = "object",
			template = choiceType(constantType(false), mapType("string", "TypeKind")),
		})
		if context.checkConstraints then
			assertis(context.generics, recordType {
				order = listType "string",
				map = mapType("string", listType(recordType {
					constraint = "ConstraintKind",
					location = "Location",
				})),
				locations = mapType("string", "Location"),
			})
		else
			assertis(context.generics, mapType("string", "Location"))
		end

		-- Handle non-recursive type ASTs
		if ast.tag == "type-keyword" then
			return {
				tag = "keyword-type",
				role = "type",
				name = ast.name,
			}
		elseif ast.tag == "generic" then
			-- Check that the generic is in scope
			if context.checkConstraints then
				if not context.generics.map[ast.name] then
					Report.UNKNOWN_GENERIC_USED {
						name = ast.name,
						location = ast.location,
					}
				end

				-- Get from the template map
				if context.template then
					assert(context.template[ast.name])
					return context.template[ast.name]
				end
			else
				if not context.generics[ast.name] then
					Report.UNKNOWN_GENERIC_USED {
						name = ast.name,
						location = ast.location,
					}
				end
			end

			return {
				tag = "generic-type",
				role = "type",
				name = ast.name,
			}
		elseif ast.tag == "keyword-generic" then
			assert(ast.name == "Self")

			-- Check that #Self is only used inside interfaces
			if not context.selfAllowed then
				Report.SELF_OUTSIDE_INTERFACE {
					location = ast.location,
				}
			end

			return {
				tag = "self-type",
				role = "type",
			}
		end
		
		assertis(ast, recordType {
			tag = constantType("concrete-type"),
			package = choiceType(constantType(false), "string"),
			base = "string",
			arguments = "object",
		})

		local packageName, definitionName
		if not ast.package then
			-- Check that the short name alias is available
			if not shortNameMap[ast.base] then
				Report.UNKNOWN_DEFINITION_USED {
					name = ast.base,
					location = ast.location,
				}
			end

			packageName = shortNameMap[ast.base].package
			definitionName = shortNameMap[ast.base].name
		else
			-- Check that such a package is in scope
			if not usePackages[ast.package] then
				Report.UNKNOWN_PACKAGE_USED {
					package = ast.package,
					location = ast.location,
				}
			end

			-- Check that the definition exists
			if not definitionMap[ast.package][ast.base] then
				Report.UNKNOWN_DEFINITION_USED {
					name = ast.package .. ":" .. ast.base,
					location = ast.location,
				}
			end

			packageName = ast.package
			definitionName = ast.base
		end

		local definition = definitionMap[packageName][definitionName]
		assert(definition)

		-- Collect and validate the type-parameter arguments
		local arguments = {}
		for _, argumentAST in ipairs(ast.arguments) do
			local argument = resolver(argumentAST, context)
			
			-- Check that the role of the argument is a type
			if argument.role ~= "type" then
				Report.INTERFACE_USED_AS_TYPE {
					interface = showConstraintKind(argument),
					location = argumentAST.location,
				}
			end

			table.insert(arguments, argument)
		end

		-- Check that the number of type arguments is correct
		if #arguments ~= #definition.definition.generics.parameters then
			Report.WRONG_ARITY {
				name = definition.fullName,
				definitionLocation = definition.definition.location,
				expectedArity = #definition.definition.generics.parameters,
				givenArity = #arguments,
				location = ast.location,
			}
		end

		if context.checkConstraints then
			-- Check that the arguments meet the requirements imposed by the
			-- container
			local argumentMap = {}
			for i, name in ipairs(definition.genericConstraintMap.order) do
				assert(arguments[i])
				argumentMap[name] = arguments[i]
			end

			for i, argument in ipairs(arguments) do
				-- Gather which constraints are imposed on this argument by
				-- the container
				local requirements = {}
				for _, requirement in ipairs(definition.genericConstraintMap.map[definition.genericConstraintMap.order[i]]) do
					table.insert(requirements, {
						constraint = substituteGenerics(requirement.constraint, argumentMap),
						location = requirement.location,
					})
				end

				-- Gather which constraints are supplied by this argument
				local present
				if argument.tag == "self-type" then
					present = {context.selfAllowed}
				elseif argument.tag == "generic-type" then
					present = table.map(table.getter "constraint", context.generics.map[argument.name])
					assert(present)
				elseif argument.tag == "keyword-type" then
					-- TODO: Can keyword types implement interfaces?
					present = {}
				elseif argument.tag == "compound-type" then
					-- Get their implements claims and substitute using
					-- arguments
					present = {}
					local argumentDefinition = definitionMap[argument.packageName][argument.definitionName]
					local substitutionMap = {}
					for i, n in ipairs(argumentDefinition.genericConstraintMap.order) do
						assert(argument.arguments[i])
						substitutionMap[n] = argument.arguments[i]
					end
					for _, implement in ipairs(argumentDefinition.implements) do
						table.insert(present, substituteGenerics(implement.constraint, substitutionMap))
					end
				end

				-- Check each argument for satisfaction
				for _, requirement in ipairs(requirements) do
					-- Search for a matching constraint
					local satisfied = false
					for _, constraint in ipairs(present) do
						satisfied = satisfied or constraintSatisfiedBy(requirement.constraint, constraint)
					end

					if not satisfied then
						Report.TYPE_MUST_IMPLEMENT_CONSTRAINT {
							container = definition.fullName,
							nth = i,
							constraint = showConstraintKind(requirement.constraint),
							cause = requirement.location,
							type = showTypeKind(argument),
							location = ast.arguments[i].location,
						}
					end
				end
			end
		end

		-- Determine if this a ConstraintKind or a TypeKind based on the tag of
		-- the definition
		local tag, role
		if definition.tag == "interface-definition" then
			tag = "interface-constraint"
			role = "constraint"
		else
			tag = "compound-type"
			role = "type"
		end

		return {
			tag = tag,
			role = role,
			packageName = packageName,
			definitionName = definitionName,
			arguments = arguments,
		}
	end

	return resolver
end

--------------------------------------------------------------------------------

-- RETURNS a StatementIR representing executing the given statements in sequence
local function sequenceSt(statements)
	assertis(statements, listType("StatementIR"))

	if #statements == 1 then
		return statements[1]
	end

	local returns = "no"
	for _, s in ipairs(statements) do
		assert(returns ~= "yes")

		if s.returns == "maybe" then
			returns = "maybe"
		elseif s.returns == "yes" then
			returns = "yes"
		end
	end

	return {
		tag = "sequence",
		returns = returns,
		statements = statements,
	}
end

-- RETURNS a ProofSt that captures the given statement
local function proofSt(statement)
	assertis(statement, "StatementIR")

	return {
		tag = "proof",
		body = statement,
		returns = "no",
	}
end

-- For vendUniqueIdentifier
local _uniqueTick = 0

-- RETURNS a fresh identifier
local function vendUniqueIdentifier()
	_uniqueTick = _uniqueTick + 1

	return "_identifier" .. _uniqueTick
end

-- RETURNS nothing
-- CHECKS that the given types match the expected types exactly (in count and
-- content)
local function checkTypes(p)
	assertis(p, recordType {
		given = listType(recordType {type = "TypeKind"}),
		expected = listType "TypeKind",
		purpose = "string",
		givenLocation = "Location",
		expectedLocation = "Location",
	})

	if #p.given ~= #p.expected then
		Report.WRONG_VALUE_COUNT {
			expectedCount = #p.expected,
			givenCount = #p.given,
			purpose = purpose,
			givenLocation = p.givenLocation,
			expectedLocation = p.expectedLocation,
		}
	end

	for i in ipairs(p.given) do
		if not areTypesEqual(p.given[i].type, p.expected[i]) then
			Report.TYPE_MISMATCH {
				given = showTypeKind(p.given[i].type),
				expected = showTypeKind(p.expected[i]),
				purpose = string.ordinal(i) .. " " .. p.purpose,
				givenLocation = p.givenLocation,
				expectedLocation = p.expectedLocation,
			}
		end
	end
end

-- RETURNS a VTableIR
local function getVTable(implementer, constraint, context)
	assertis(implementer, "TypeKind")
	assertis(constraint, "ConstraintKind")
	assertis(context, recordType {
		constraintMap = mapType("string", listType(recordType {
			constraint = "ConstraintKind",
			name = "string",
		})),

		definitionMap = mapType("string", mapType("string", recordType {
			constraintArguments = listType(recordType {
				concerningIndex = "integer",
				constraintListIndex = "integer",
				constraint = "ConstraintKind",
			}),
		})),
	})

	if implementer.tag == "compound-type" then
		-- This can be constructed explicitly
		local definition = context.definitionMap[implementer.packageName][implementer.definitionName]
		local arguments = {}
		for _, a in ipairs(definition.constraintArguments) do
			table.insert(arguments, getVTable(implementer.arguments[a.concerningIndex], a.constraint, context))
		end

		return {
			tag = "concrete-vtable",
			interface = constraint,
			concrete = implementer,
			arguments = arguments,
		}
	elseif implementer.tag == "generic-type" then
		assert(context.constraintMap[implementer.name], "type parameter must be inscope")
		local fit = false
		for _, c in pairs(context.constraintMap[implementer.name]) do
			if common.areConstraintsEqual(c.constraint, constraint) then
				assert(not fit, "must be unique fit")
				fit = {
					tag = "parameter-vtable",
					name = c.name,
					interface = c.constraint,
				}
			end
		end
		assert(fit, "must satisfy required constraint")

		return fit
	end

	error("unknown implementer tag `" .. implementer.tag .. "`")
end

-- RETURNS a function (with definitionLocation and signature) and a
-- ConstraintKind
local function findConstraint(baseType, memberName, location, context)
	assertis(baseType, "TypeKind")
	assertis(memberName, "string")
	assertis(location, "Location")
	assertis(context, recordType {
		constraintMap = mapType("string", listType(recordType {
			constraint = "ConstraintKind",
		})),
	})

	local lookup = baseType.tag == "generic-type" and baseType.name or "Self"
	local info = context.constraintMap[lookup]
	assertis(info, listType(recordType {constraint = "ConstraintKind"}))

	local matching = false
	local matchingConstraint = false
	for _, c in ipairs(info) do
		if c.constraint.tag == "keyword-constraint" then
			error "TODO: Handle keyword-constraints"
		else
			assert(c.constraint.tag == "interface-constraint")

			local interface = context.definitionMap[c.constraint.packageName][c.constraint.definitionName]
			assert(interface.tag == "interface-definition")

			local hit = interface._functionMap[memberName]
			if hit then
				-- Check that it is not ambiguous
				if matching then
					Report.CONFLICTING_INTERFACES {
						method = memberName,
						location = location,
						interfaceOne = showConstraintKind(matchingConstraint.constraint),
						interfaceTwo = showConstraintKind(c.constraint),
					}
				end

				-- Substitute arguments from c.constraint's argument into matching
				local substitutionMap = {}
				for i, argument in ipairs(c.constraint.arguments) do
					local name = interface.genericConstraintMap.order[i]
					substitutionMap[name] = argument
				end
				substitutionMap.Self = baseType

				matchingConstraint = c
				matching = {
					signature = substitutedSignature(hit.signature, substitutionMap),
					definitionLocation = hit.definitionLocation,
				}
			end
		end
	end

	return matching, matchingConstraint
end

local compilePredicate

-- RETURNS StatementIR, out variables, impure boolean
-- The StatementIR describes how to execute the statement such that the out
-- variables are assigned with the evaluation.
-- ENSURES at least one out variable is returned
-- impure is true if executing this expression could have observable side
-- effects (because it contains a `!` action)
local function compileExpression(expressionAST, scope, context)
	assertis(expressionAST, recordType {
		tag = "string",
	})
	assertis(context, recordType {
		canUseBang = "boolean",
		proof = "boolean",
		newType = choiceType(constantType(false), "TypeKind"),

		typeResolver = "function",
		typeResolverContext = "object",
		definitionMap = mapType("string", mapType("string", recordType {
			_functionMap = mapType("string", recordType {}),
			constraintArguments = listType(recordType {
				concerningIndex = "integer",
				constraintListIndex = "integer",
				constraint = "ConstraintKind",
			}),
		})),

		constraintMap = mapType("string", listType(recordType {
			constraint = "ConstraintKind",
			name = "string",
			location = "Location",
		})),
	})

	if expressionAST.tag == "string-literal" then
		local destination = {
			name = vendUniqueIdentifier(),
			type = STRING_TYPE,
		}

		local code = {
			{
				tag = "local",
				variable = destination,
				returns = "no",
			},
			{
				tag = "string-load",
				destination = destination,
				string = expressionAST.value,
				returns = "no",
			},
		}
		return sequenceSt(code), {destination}, false
	elseif expressionAST.tag == "int-literal" then
		local destination = {
			name = vendUniqueIdentifier(),
			type = INT_TYPE,
		}

		local code = {
			{
				tag = "local",
				variable = destination,
				returns = "no",
			},
			{
				tag = "int-load",
				destination = destination,
				number = expressionAST.value,
				returns = "no",
			},
		}
		return sequenceSt(code), {destination}, false
	elseif expressionAST.tag == "identifier" then
		-- TODO
		local variable = scope:get(expressionAST.name)
		if not variable then
			Report.NO_SUCH_VARIABLE {
				name = expressionAST.name,
				location = expressionAST.location,
			}
		end

		return sequenceSt {}, {variable}, false
	elseif expressionAST.tag == "keyword" then
		if expressionAST.keyword == "unit" then
			local destination = {
				name = vendUniqueIdentifier(),
				type = UNIT_TYPE,
			}
			local code = {
				{
					tag = "local",
					variable = destination,
					returns = "no",
				},
				{
					tag = "unit",
					destination = destination,
					returns = "no",
				}
			}

			return sequenceSt(code), {destination}, false
		elseif expressionAST.keyword == "this" then
			if not scope:get("this") then
				Report.THIS_USED_OUTSIDE_METHOD {
					location = expressionAST.location,
				}
			end

			return sequenceSt {}, {scope:get("this")}, false
		elseif expressionAST.keyword == "true" or expressionAST.keyword == "false" then
			local destination = {
				name = vendUniqueIdentifier(),
				type = BOOLEAN_TYPE,
			}
			local code = {
				{
					tag = "local",
					variable = destination,
					returns = "no",
				},
				{
					tag = "boolean",
					boolean = expressionAST.keyword == "true",
					destination = destination,
					returns = "no",
				}
			}

			return sequenceSt(code), {destination}, false
		elseif expressionAST.keyword == "return" then
			if not context.proof then
				Report.RETURN_USED_IN_IMPLEMENTATION {
					location = expressionAST.location,
				}
			end

			-- Get the variable "return"
			if not scope:get("return") then
				Report.CANNOT_USE_RETURN {
					location = expressionAST.location,
				}
			end

			return sequenceSt {}, {scope:get("return")}, false
		end
		error(show(expressionAST))
	elseif expressionAST.tag == "field-access" then
		local code = {}
		local baseCode, bases, impure = compileExpression(expressionAST.base, scope, context)
		table.insert(code, baseCode)

		-- Check that there is exactly one base
		if #bases ~= 1 then
			Report.WRONG_VALUE_COUNT {
				givenCount = #bases,
				expectedCount = 1,
				purpose = "field base",
				givenLocation = expressionAST.location,
			}
		end

		-- Check that the type is a class/union
		local baseType = bases[1].type
		if baseType.tag ~= "compound-type" then
			Report.TYPE_MUST_BE {
				givenType = showTypeKind(baseType),
				purpose = "a field access base",
				givenLocation = expressionAST.location,
			}
		end

		local definition = context.definitionMap[baseType.packageName][baseType.definitionName]
		assert(definition)
		local field = definition._fieldMap[expressionAST.field]

		local substitutionMap = {}
		for i, argument in ipairs(baseType.arguments) do
			local name = definition.genericConstraintMap.order[i]
			substitutionMap[name] = argument
		end

		-- Check if the field exists
		if not field then
			Report.NO_SUCH_MEMBER {
				memberType = "field",
				container = showTypeKind(baseType),
				name = expressionAST.field,
				location = expressionAST.location,
			}
		end

		-- Substitute the field to match the baseType's arguments
		field = table.with(field, "type", substituteGenerics(field.type, substitutionMap))

		-- Create destination variable
		local destination = {
			name = vendUniqueIdentifier(),
			type = field.type,
		}
		table.insert(code, {
			tag = "local",
			variable = destination,
			returns = "no",
		})

		if definition.tag == "class-definition" then
			-- Accessing a field on a class is free
			table.insert(code, {
				tag = "field",
				name = expressionAST.field,
				base = bases[1],
				destination = destination,
				returns = "no",
			})

			return sequenceSt(code), {destination}, impure
		else
			-- Accessing a field on a union is only allowed when we know the
			-- variant
			assert(definition.tag == "union-definition")

			-- Assert that the union is of the right tag
			local isaVariable = {
				name = vendUniqueIdentifier(),
				type = BOOLEAN_TYPE,
			}
			local proof = proofSt(sequenceSt {
				{
					tag = "local",
					variable = isaVariable,
					returns = "no",
				},
				{
					tag = "isa",
					base = bases[1],
					destination = isaVariable,
					returns = "no",
					variant = expressionAST.field,
				},
				{
					tag = "verify",
					variable = isaVariable,
					checkLocation = expressionAST.location,
					conditionLocation = expressionAST.location,
					reason = table.concat {
						"the `",
						showTypeKind(baseType),
						"` union instance is a `",
						expressionAST.field,
						"`",
					},
					returns = "no",
				},
			})
			table.insert(code, proof)

			table.insert(code, {
				tag = "variant",
				variant = expressionAST.field,
				base = bases[1],
				destination = destination,
				returns = "no",
			})

			return sequenceSt(code), {destination}, impure
		end
	elseif expressionAST.tag == "isa" then
		local code = {}
		local baseCode, bases, impure = compileExpression(expressionAST.base, scope, context)
		table.insert(code, baseCode)

		local variant = expressionAST.variant

		-- Check that exactly one value is given as base
		if #bases ~= 1 then
			Report.WRONG_VALUE_COUNT {
				givenCount = #bases,
				expectedCount = 1,
				purpose = "the base of `isa " .. variant,
				givenLocation = expressionAST.location,
			}
		end

		-- Check that the type is a union type
		local baseType = bases[1].type
		if baseType.tag ~= "compound-type" then
			Report.TYPE_MUST_BE {
				givenType = showTypeKind(baseType),
				purpose = "an `isa` expression base",
				givenLocation = expressionAST.location,
			}
		end
		
		local definition = context.definitionMap[baseType.packageName][baseType.definitionName]
		assert(definition)
		if definition.tag ~= "union-definition" then
			Report.TYPE_MUST_BE {
				givenType = showTypeKind(baseType),
				purpose = "an `isa` expression base",
				givenLocation = expressionAST.location,
			}
		elseif not definition._fieldMap[variant] then
			Report.NO_SUCH_MEMBER {
				memberType = "variant",
				container = showTypeKind(baseType),
				name = variant,
				location = expressionAST.location,
			}
		end

		-- Create destination variable
		local destination = {
			name = vendUniqueIdentifier(),
			type = BOOLEAN_TYPE,
		}
		table.insert(code, {
			tag = "local",
			variable = destination,
			returns = "no",
		})

		table.insert(code, {
			tag = "isa",
			base = bases[1],
			destination = destination,
			variant = variant,
			returns = "no",
		})

		return sequenceSt(code), {destination}, impure
	elseif expressionAST.tag == "binary" then
		local methodName = common.OPERATOR_ALIAS[expressionAST.operator]
		if not methodName then
			Report.UNKNOWN_OPERATOR_USED {
				operator = expressionAST.operator,
				location = expressionAST.location,
			}
		end

		-- Simply re-write this syntactically as a method call
		local rewrite = {
			tag = "method-call",
			bang = false,
			base = expressionAST.left,
			methodName = methodName,
			arguments = {expressionAST.right},
			location = expressionAST.location,
		}
		return compileExpression(rewrite, scope, context)
	elseif expressionAST.tag == "new-expression" then
		-- Check if new is allowed here
		if not context.newType then
			Report.NEW_IN_INTERFACE {
				location = expressionAST.location,
			}
		end

		assert(context.newType.tag == "compound-type")
		local packageName = context.newType.packageName
		local definitionName = context.newType.definitionName
		local definition = context.definitionMap[packageName][definitionName]
		assert(definition)
		assert(definition.tag == "union-definition" or definition.tag == "class-definition")

		local outVariable = {
			name = vendUniqueIdentifier(),
			type = context.newType,
		}
		local code = {
			{
				tag = "local",
				variable = outVariable,
				returns = "no",
			}
		}

		local providedAt = {}
		local fieldAssignment = {}
		local initializationLocation = {}
		local impure = false
		for _, fieldAST in ipairs(expressionAST.fields) do
			-- Compile the argument
			local c, outs, i = compileExpression(fieldAST.value, scope, context)
			table.insert(code, c)

			local substitutionMap = {}
			for i, argument in ipairs(context.newType.arguments) do
				local name = definition.genericConstraintMap.order[i]
				substitutionMap[name] = argument
			end

			local field = definition._fieldMap[fieldAST.name]
			if not field then
				Report.NO_SUCH_MEMBER {
					memberType = "field",
					container = showTypeKind(context.newType),
					name = fieldAST.name,
					location = fieldAST.location,
				}
			end

			-- Use the arguments provided by newType rather than the Definition
			field = table.with(field, "type", substituteGenerics(field.type, substitutionMap))

			checkTypes {
				given = outs,
				expected = {field.type},
				purpose = "initialization of `" .. fieldAST.name .. "` field",
				givenLocation = fieldAST.location,
				expectedLocation = field.definitionLocation,
			}

			-- Check order of evaluation
			if i then
				if impure then
					Report.EVALUATION_ORDER {
						first = impure,
						second = fieldAST.location,
					}
				else
					impure = fieldAST.location
				end
			end

			-- Check if it's duplicated
			if fieldAssignment[fieldAST.name] then
				Report.DUPLICATE_INITIALIZATION {
					purpose = "field `" .. fieldAST.name .. "`",
					first = initializationLocation[fieldAST.name],
					second = fieldAST.location,
				}
			end
			initializationLocation[fieldAST.name] = fieldAST.location
			fieldAssignment[fieldAST.name] = outs[1]
		end

		if definition.tag == "class-definition" then
			-- Check that each field is assigned
			for key in pairs(definition._fieldMap) do
				if not fieldAssignment[key] then
					Report.MISSING_INITIALIZATION {
						purpose = "field `" .. key .. "`",
						location = expressionAST.location,
					}
				end
			end

			table.insert(code, {
				tag = "new-class",
				fields = fieldAssignment,
				destination = outVariable,
				returns = "no",
			})
		elseif definition.tag == "union-definition" then
			-- Check that only one field is assigned
			if #table.keys(fieldAssignment) == 0 then
				Report.MISSING_INITIALIZATION {
					purpose = "union tag",
					location = expressionAST.location,
				}
			elseif 2 <= #table.keys(fieldAssignment) then
				Report.DUPLICATE_INITIALIZATION {
					purpose = "union tag",
					first = expressionAST.location,
					second = expressionAST.location,
				}
			end

			table.insert(code, {
				tag = "new-union",
				field = next(fieldAssignment),
				value = fieldAssignment[next(fieldAssignment)],
				destination = outVariable,
				returns = "no",
			})
		end

		return sequenceSt(code), {outVariable}, impure
	elseif expressionAST.tag == "method-call" then
		local code = {}
		local baseCode, bases, impureBase = compileExpression(expressionAST.base, scope, context)
		table.insert(code, baseCode)
		
		-- Check that exactly one method base is given
		if #bases ~= 1 then
			Report.WRONG_VALUE_COUNT {
				purpose = "method base",
				givenCount = #bases,
				expectedCount = 1,
				givenLocation = expressionAST.base.location,
			}
		end

		-- Compile the arguments
		local arguments = {bases[1]}
		local impure = impureBase and expressionAST.base.location
		for _, ast in ipairs(expressionAST.arguments) do
			local c, outs, i = compileExpression(ast, scope, context)
			table.insert(code, c)

			for _, o in ipairs(outs) do
				table.insert(arguments, o)
			end

			if i then
				if impure then
					Report.EVALUATION_ORDER {
						first = impure,
						second = ast.location,
					}
				end
				impure = ast.location
			end
		end

		local baseType = bases[1].type
		if baseType.tag == "generic-type" or baseType.tag == "self-type" then
			-- Get a list of constraints associated with this base type
			if baseType.tag == "self-type" then
				assert(context.genericMap.Self)
			end

			-- Find the matching method
			local matching, matchingConstraint = findConstraint(baseType, expressionAST.methodName, expressionAST.location, context)

			-- Check that the method was found
			if not matching or matching.signature.modifier ~= "method" then
				Report.NO_SUCH_MEMBER {
					container = showTypeKind(baseType),
					memberType = "method",
					location = expressionAST.location,
				}
			end

			-- Check the bang
			if not matching.signature.bang ~= not expressionAST.bang then
				Report.BANG_MISMATCH {
					given = matching.signature.bang and "without a `!`" or "with a `!`",
					expects = matching.signature.bang and "a `!` action" or " a pure function",
					fullName = matching.signature.longName,
					location = expressionAST.location,
					signatureLocation = matching.definitionLocation,
				}
			elseif matching.signature.bang and not context.canUseBang then
				Report.BANG_NOT_ALLOWED {
					context = matching.signature.modifier .. " `" .. matching.signature.longName .. "`",
					location = expressionAST.location,
				}
			end

			-- Create the destination storage
			local destinations = {}
			for _, returnType in ipairs(matching.signature.returnTypes) do
				local destination = {
					name = vendUniqueIdentifier(),
					type = returnType,
				}
				table.insert(destinations, destination)
				table.insert(code, {
					tag = "local",
					variable = destination,
					returns = "no",
				})
			end

			-- Make the indirect call
			local call = {
				tag = "dynamic-call",
				constraint = getVTable(baseType, matchingConstraint.constraint, context),
				signature = matching.signature,
				arguments = arguments,
				destinations = destinations,
				returns = "no",
			}
			assertis(call, "DynamicCallSt")

			-- Make the requires checks
			for _, ast in ipairs(matching.signature.requiresASTs) do
				error "TODO: requires for dynamic method"
			end

			table.insert(code, call)

			-- Make the post condition assumes
			for _, ast in ipairs(matching.signature.ensuresASTs) do
				error "TODO: ensures for dynamic method"
			end

			return sequenceSt(code), destinations, expressionAST.bang
		elseif baseType.tag == "compound-type" or baseType.tag == "keyword-type" then
			local definition
			if baseType.tag == "compound-type" then
				definition = context.definitionMap[baseType.packageName][baseType.definitionName]
			else
				definition = common.builtinDefinitions[baseType.name]
				assert(definition, "no built in for " .. baseType.name)
			end
			assert(definition)
			assert(definition.tag == "class-definition" or definition.tag == "union-definition")

			-- Get the member
			local member
			local substitutionMap = {}
			if baseType.tag ~= "keyword-type" then
				member = definition._functionMap[expressionAST.methodName]

				-- Substitute generics
				if member then
					for i, argument in ipairs(baseType.arguments) do
						local name = definition.genericConstraintMap.order[i]
						substitutionMap[name] = argument
					end
					member = table.with(member, "signature", substitutedSignature(member.signature, substitutionMap))
				end
			else
				member = definition.functionMap[expressionAST.methodName]
			end
			if not member or member.signature.modifier ~= "method" then
				Report.NO_SUCH_MEMBER {
					memberType = "method",
					container = showTypeKind(baseType),
					name = expressionAST.methodName,
					location = expressionAST.location,
				}
			end

			-- Check the types
			-- NOTE: Signature's parameters INCLUDES `this`, so arguments MUST
			-- include base
			local expected = table.map(table.getter "type", member.signature.parameters)
			checkTypes {
				given = arguments,
				expected = expected,
				purpose = "argument(s) to method " .. showTypeKind(baseType) .. "." .. expressionAST.methodName,
				givenLocation = expressionAST.location,
				expectedLocation = member.definitionLocation,
			}

			-- Check bang
			if not member.signature.bang ~= not expressionAST.bang then
				Report.BANG_MISMATCH {
					modifier = member.signature.modifier,
					given = member.signature.bang and "without a `!`" or "with a `!`",
					expects = member.signature.bang and "a `!` action" or " a pure function",
					fullName = member.signature.longName,
					location = expressionAST.location,
					signatureLocation = member.definitionLocation,
				}
			elseif member.signature.bang and not context.canUseBang then
				Report.BANG_NOT_ALLOWED {
					context = member.signature.modifier .. " `" .. member.signature.longName .. "`",
					location = expressionAST.location,
				}
			end

			-- Get destinations
			local destinations = {}
			for _, returnType in ipairs(member.signature.returnTypes) do
				local destination = {
					name = vendUniqueIdentifier(),
					type = returnType,
				}
				table.insert(code, {
					tag = "local",
					variable = destination,
					returns = "no",
				})
				table.insert(destinations, destination)
			end

			-- Get vtables
			local vtables = {}
			for _, a in ipairs(definition.constraintArguments) do
				table.insert(vtables, getVTable(baseType.arguments[a.concerningIndex], a.constraint, context))
			end

			local call = {
				tag = "static-call",
				arguments = arguments,
				signature = member.signature,
				destinations = destinations,
				constraintArguments = vtables,
				returns = "no",
			}
			assertis(call, "StaticCallSt")

			-- Create the context for requires/ensures
			local proofContext = {
				canUseBang = false,
				proof = true,
				definitionMap = context.definitionMap,

				-- Type specific
				newType = substituteGenerics(definition.kind, substitutionMap),
				typeResolver = definition.resolver,

				-- Use template instantiation: their generics will NOT appear
				typeResolverContext = table.with(definition.resolverContext, "template", substitutionMap),
				constraintMap = context.constraintMap,
			}

			-- Make arguments, this, and return the appropriate values for
			-- requires/ensures
			local proofScope = Map.new()
			for i, p in ipairs(member.signature.parameters) do
				proofScope = proofScope:with(p.name, arguments[i])
			end

			-- Verify the things needed by requires
			for i, ast in ipairs(member.signature.requiresASTs) do
				local preVerify, verifyVariable = compilePredicate(ast, proofScope, proofContext, "requires")
				table.insert(code, proofSt(sequenceSt {
					preVerify,
					{
						tag = "verify",
						variable = verifyVariable,
						checkLocation = expressionAST.location,
						conditionLocation = ast.location,
						reason = "the " .. string.ordinal(i) .. " precondition",
						returns = "no",
					},
				}))
			end

			table.insert(code, call)

			if #destinations == 1 then
				-- return is allowed in ensures (but not in requires)
				proofScope = proofScope:with("return", destinations[1])
			end

			-- Assume the things allowed via ensures
			for _, ast in ipairs(member.signature.ensuresASTs) do
				local preAssume, assumeVariable = compilePredicate(ast, proofScope, proofContext, "ensures")
				table.insert(code, proofSt(sequenceSt {
					preAssume,
					{
						tag = "assume",
						variable = assumeVariable,
						returns = "no",
					}
				}))

			end

			return sequenceSt(code), destinations, impure or member.signature.bang
		end
	elseif expressionAST.tag == "static-call" then
		local baseType = context.typeResolver(expressionAST.baseType, context.typeResolverContext)

		local code = {}

		-- Compile the arguments
		local arguments = {}
		local impure = false
		for _, ast in ipairs(expressionAST.arguments) do
			local c, outs, i = compileExpression(ast, scope, context)
			table.insert(code, c)

			for _, o in ipairs(outs) do
				table.insert(arguments, o)
			end

			if i then
				if impure then
					Report.EVALUATION_ORDER {
						first = impure,
						second = ast.location,
					}
				end
				impure = ast.location
			end
		end

		if baseType.tag == "self-type" then
			-- TODO: In Interface contracts, #Self is allowed as a regular
			-- type parameter!
			error "TODO"
		elseif baseType.tag == "generic-type" then
			-- Find the matching method
			local matching, matchingConstraint = findConstraint(baseType, expressionAST.funcName, expressionAST.location, context)

			-- Check that the static was found
			if not matching or matching.signature.modifier ~= "static" then
				Report.NO_SUCH_MEMBER {
					container = showTypeKind(baseType),
					memberType = "static",
					location = expressionAST.location,
				}
			end

			local expected = table.map(table.getter "type", matching.signature.parameters)
			checkTypes {
				given = arguments,
				expected = expected,
				purpose = "argument(s) to static " .. showTypeKind(baseType) .. "." .. expressionAST.funcName,
				givenLocation = expressionAST.location,
				expectedLocation = matching.definitionLocation,
			}

			-- Check bang
			if not matching.signature.bang ~= not expressionAST.bang then
				Report.BANG_MISMATCH {
					given = matching.signature.bang and "without a `!`" or "with a `!`",
					expects = matching.signature.bang and "a `!` action" or "a pure function",
					fullName = matching.signature.longName,
					location = expressionAST.location,
					modifier = matching.signature.modifier,
					signatureLocation = matching.definitionLocation,
				}
			elseif matching.signature.bang and not context.canUseBang then
				Report.BANG_NOT_ALLOWED {
					context = matching.signature.modifier .. " `" .. matching.signature.longName .. "`",
					location = expressionAST.location,
				}
			end

			-- Get destinations
			local destinations = {}
			for _, returnType in ipairs(matching.signature.returnTypes) do
				local destination = {
					name = vendUniqueIdentifier(),
					type = returnType,
				}
				table.insert(code, {
					tag = "local",
					variable = destination,
					returns = "no",
				})
				table.insert(destinations, destination)
			end

			-- Make the indirect call
			local call = {
				tag = "dynamic-call",
				constraint = getVTable(baseType, matchingConstraint.constraint, context),
				signature = matching.signature,
				arguments = arguments,
				destinations = destinations,
				returns = "no",
			}
			assertis(call, "DynamicCallSt")
			table.insert(code, call)
			
			return sequenceSt(code), destinations, impure or matching.signature.bang
		elseif baseType.tag == "keyword-type" then
			error "TODO"
		elseif baseType.tag == "compound-type" then
			local definition = context.definitionMap[baseType.packageName][baseType.definitionName]
			assert(definition)
			assert(definition.tag == "class-definition" or definition.tag == "union-definition")

			local substitutionMap = {}
			for i, argument in ipairs(baseType.arguments) do
				local name = definition.genericConstraintMap.order[i]
				substitutionMap[name] = argument
			end

			-- Get the member
			local member = definition._functionMap[expressionAST.funcName]
			if not member or member.signature.modifier ~= "static" then
				Report.NO_SUCH_MEMBER {
					memberType = "static",
					container = showTypeKind(baseType),
					name = expressionAST.funcName,
					location = expressionAST.location,
				}
			end
			member = table.with(member, "signature", substitutedSignature(member.signature, substitutionMap))
			
			-- Check the types
			local expected = table.map(table.getter "type", member.signature.parameters)
			checkTypes {
				given = arguments,
				expected = expected,
				purpose = "argument(s) to static " .. showTypeKind(baseType) .. "." .. expressionAST.funcName,
				givenLocation = expressionAST.location,
				expectedLocation = member.definitionLocation,
			}

			-- Check bang
			if not member.signature.bang ~= not expressionAST.bang then
				Report.BANG_MISMATCH {
					given = member.signature.bang and "without a `!`" or "with a `!`",
					expects = member.signature.bang and "a `!` action" or "a pure function",
					fullName = member.signature.longName,
					location = expressionAST.location,
					modifier = member.signature.modifier,
					signatureLocation = member.definitionLocation,
				}
			elseif member.signature.bang and not context.canUseBang then
				Report.BANG_NOT_ALLOWED {
					context = member.signature.modifier .. " `" .. member.signature.longName .. "`",
					location = expressionAST.location,
				}
			end

			-- Get destinations
			local destinations = {}
			for _, returnType in ipairs(member.signature.returnTypes) do
				local destination = {
					name = vendUniqueIdentifier(),
					type = returnType,
				}
				table.insert(code, {
					tag = "local",
					variable = destination,
					returns = "no",
				})
				table.insert(destinations, destination)
			end

			-- Get constraint arguments
			local constraintArguments = {}
			for _, c in ipairs(definition.constraintArguments) do
				assert(1 <= c.concerningIndex and c.concerningIndex <= #baseType.arguments)
				local vtable = getVTable(baseType.arguments[c.concerningIndex], c.constraint, context)
				table.insert(constraintArguments, vtable)
			end

			local call = {
				tag = "static-call",
				arguments = arguments,
				destinations = destinations,
				returns = "no",
				signature = member.signature,
				constraintArguments = constraintArguments,
			}
			assertis(call, "StaticCallSt")

			-- Create the context for requires/ensures
			local proofContext = {
				canUseBang = false,
				proof = true,
				definitionMap = context.definitionMap,

				-- Type specific
				newType = substituteGenerics(definition.kind, substitutionMap),
				typeResolver = definition.resolver,

				-- Use template instantiation: their generics will NOT appear
				typeResolverContext = table.with(definition.resolverContext, "template", substitutionMap),
				constraintMap = context.constraintMap,
			}

			-- Make arguments/this the appropriate values for requires/ensures
			local proofScope = Map.new()
			for i, p in ipairs(member.signature.parameters) do
				proofScope = proofScope:with(p.name, arguments[i])
			end

			-- Verify that the function's pre-conditions hold
			for i, ast in ipairs(member.signature.requiresASTs) do
				local preVerify, verifyVariable = compilePredicate(ast, proofScope, proofContext, "requires")
				table.insert(code, proofSt(sequenceSt {
					preVerify,
					{
						tag = "verify",
						variable = verifyVariable,
						checkLocation = expressionAST.location,
						conditionLocation = ast.location,
						reason = "the " .. string.ordinal(i) .. " precondition",
						returns = "no",
					},
				}))
			end

			table.insert(code, call)

			if #destinations == 1 then
				-- return is allowed in ensures (but not in requires)
				proofScope = proofScope:with("return", destinations[1])
			end

			-- Assume that the function's post-conditions hold
			for _, e in ipairs(member.signature.ensuresASTs) do
				local preAssume, assumeVariable = compilePredicate(e, proofScope, proofContext, "ensures")
				table.insert(code, proofSt(sequenceSt {
					preAssume,
					{
						tag = "assume",
						variable = assumeVariable,
						returns = "no",
					}
				}))
			end

			return sequenceSt(code), destinations, impure or member.signature.bang
		end
		error "TODO"
	elseif expressionAST.tag == "forall-expr" then
		-- Check that quantifiers only appear in ghost contexts
		if not context.proof then
			Report.QUANTIFIER_USED_IN_IMPLEMENTATION {
				quantifier = "forall",
				location = expressionAST.location,
			}
		end

		-- Check that the variable name is fresh
		if scope:get(expressionAST.variable.name) then
			Report.VARIABLE_DEFINED_TWICE {
				name = expressionAST.variable.name,
				first = scope:get(expressionAST.variable.name).definitionLocation,
				second = expressionAST.variable.location,
			}
		end

		-- Make a new boolean variable to hold the result of the quantified
		-- statement
		local resultVariable = {
			name = vendUniqueIdentifier(),
			type = BOOLEAN_TYPE,
		}

		-- Get the type quantified over
		local variableType = context.typeResolver(expressionAST.variable.type, context.typeResolverContext)

		-- RETURNS code to execute the instantiation, the truth result variable
		-- REQUIRES v is a valid variable to instantiate on
		local function instantiate(v)
			assertis(v, "VariableIR")
			assert(areTypesEqual(v.type, variableType))

			assert(context.proof)
			local boundScope = scope:with(expressionAST.variable.name, {
				name = v.name,
				type = v.type,
				definitionLocation = expressionAST.variable.location,
			})
			local body, result = compilePredicate(expressionAST, boundScope, context, "forall")
			return body, result
		end

		-- Instantiate once to ensure that the body is fine even if it is never
		-- used
		instantiate {
			name = vendUniqueIdentifier(),
			type = variableType,
		}

		local code = sequenceSt {
			{
				tag = "local",
				variable = resultVariable,
				returns = "no",
			},
			{
				tag = "forall",
				quantified = variableType,
				instantiate = instantiate,

				-- TODO: Is this necessary?
				location = expressionAST.location,

				destination = resultVariable,
				returns = "no",

				-- Identifies this forall from all others
				-- NOTE: This MUST be DISTINCT for each re-compilation of this
				-- expression, as happens with repeated calls of
				-- ensures/requires
				unique = vendUniqueIdentifier(),
			},
		}
		return code, {resultVariable}, false
	end

	error("compileExpression: " .. expressionAST.tag)
end

-- RETURNS a StatementIR, new scope
-- The StatementIR represents the execution of the statement in the given
-- context
local function compileStatement(statementAST, scope, context)
	assertis(context, recordType {
		returnTypes = listType "TypeKind",
		canUseBang = "boolean",
		proof = "boolean",
		newType = choiceType(constantType(false), "TypeKind"),
		makePostamble = "function",

		typeResolver = "function",
		typeResolverContext = "object",
		definitionMap = mapType("string", mapType("string", recordType {
			_functionMap = mapType("string", recordType {}),
		})),

		constraintMap = mapType("string", listType(recordType {
			constraint = "ConstraintKind",
			name = "string",
			location = "Location",
		})),
	})

	if statementAST.tag == "block" then
		local statements = {}
		local scopePrime = scope
		for i, s in ipairs(statementAST.statements) do
			-- Compile the statement
			local statement, newScope = compileStatement(s, scopePrime, context)
			scopePrime = newScope
			table.insert(statements, statement)

			if statement.returns == "yes" and i ~= #statementAST.statements then
				Report.UNREACHABLE_STATEMENT {
					location = statementAST.statements[i + 1].location,
				}
			end
		end
		
		return sequenceSt(statements), scopePrime
	elseif statementAST.tag == "var-statement" then
		local code = {}
		local rhs, results = compileExpression(statementAST.value, scope, context)
		table.insert(code, rhs)
		local destinations = {}

		-- Add the new variables to the scope
		local scopePrime = scope
		for _, varAST in ipairs(statementAST.variables) do
			if scopePrime:get(varAST.name) then
				Report.VARIABLE_DEFINED_TWICE {
					name = varAST.name,
					first = scopePrime:get(varAST.name).definitionLocation,
					second = varAST.location,
				}
			end

			local destination = {
				type = context.typeResolver(varAST.type, context.typeResolverContext),
				name = varAST.name,
				definitionLocation = varAST.location,
			}
			table.insert(destinations, destination)
			scopePrime = scopePrime:with(varAST.name, destination)
		end

		checkTypes {
			purpose = "variable definition",
			given = results,
			expected = table.map(table.getter "type", destinations),
			givenLocation = statementAST.value.location,
			expectedLocation = statementAST.location,
		}

		for i in ipairs(results) do
			table.insert(code, {
				tag = "local",
				variable = destinations[i],
				returns = "no",
			})
			table.insert(code, {
				tag = "assign",
				source = results[i],
				destination = destinations[i],
				returns = "no",
			})
		end

		return sequenceSt(code), scopePrime
	elseif statementAST.tag == "return-statement" then
		local code = {}
		local toReturn = {}

		-- Compile each value
		local impure = false
		for _, a in ipairs(statementAST.values) do
			local c, outs, i = compileExpression(a, scope, context)
			assertis(c, "StatementIR")
			assert(i ~= nil)
			table.insert(code, c)

			for _, out in ipairs(outs) do
				table.insert(toReturn, out)
			end

			-- Check order of evaluation
			if i then
				if impure then
					Report.EVALUATION_ORDER {
						first = impure,
						second = a.location,
					}
				else
					impure = a.location
				end
			end
		end

		if #toReturn == 0 then
			-- `return;` is short for `return unit;`
			local unit = {
				name = vendUniqueIdentifier(),
				type = UNIT_TYPE,
			}
			table.insert(code, {
				tag = "local",
				variable = unit,
				returns = "no",
			})
			table.insert(code, {
				tag = "unit",
				destination = unit,
				returns = "no",
			})
			table.insert(toReturn, unit)
		end

		checkTypes {
			given = toReturn,
			expected = context.returnTypes,
			purpose = "returned value(s)",
			givenLocation = statementAST.location,

			-- TODO: Fix this
			expectedLocation = UNKNOWN_LOCATION,
		}

		table.insert(code, {
			tag = "return",
			sources = toReturn,
			returns = "yes",
		})

		return sequenceSt(code), scope
	elseif statementAST.tag == "do-statement" then
		-- DESIGN: Should only certain types be allowed in do statements?
		-- Should they be required to be impure?

		local c, outs, i = compileExpression(statementAST.expression, scope, context)
		return c, scope
	elseif statementAST.tag == "assign-statement" then
		local code = {}
		local rhsCode, rhsResults = compileExpression(statementAST.value, scope, context)
		table.insert(code, rhsCode)

		-- Get the destinations
		local destinations = {}
		local expectedTypes = {}
		for _, v in ipairs(statementAST.variables) do
			local destination = scope:get(v)
			if not destination then
				Report.NO_SUCH_VARIABLE {
					name = v,
					location = statementAST.location,
				}
			end
			table.insert(destinations, destination)
			table.insert(expectedTypes, destination.type)
		end
		
		-- Check that the types match
		checkTypes {
			given = rhsResults,
			expected = expectedTypes,
			purpose = "assignment values",
			givenLocation = statementAST.location,
			expectedLocation = statementAST.location,
		}

		-- Move the results
		assert(#rhsResults == #destinations)
		for i, r in ipairs(rhsResults) do
			table.insert(code, {
				tag = "assign",
				source = r,
				destination = destinations[i],
				returns = "no",
			})
		end

		return sequenceSt(code), scope
	elseif statementAST.tag == "if-statement" then
		local code = {}
		local conditionCode, conditions = compileExpression(statementAST.condition, scope, context)
		table.insert(code, conditionCode)

		-- Check that the condition is a boolean
		checkTypes {
			given = conditions,
			expected = {BOOLEAN_TYPE},
			purpose = "if condition",
			givenLocation = statementAST.condition.location,
			expectedLocation = statementAST.condition.location,
		}

		-- Compile then body, ignoring scope (scope ends)
		local body = compileStatement(statementAST.body, scope, context)

		-- Compile else/elseifs back to front, nesting
		local elseSt
		if statementAST.elseClause then
			-- Ignore new scope (scope ends)
			elseSt = compileStatement(statementAST.elseClause.body, scope, context)
		else
			elseSt = sequenceSt {}
		end

		for i = #statementAST.elseifClauses, 1, -1 do
			local clause = statementAST.elseifClauses[i]
			local conditionCode, conditions = compileExpression(clause.condition, scope, context)

			-- Check that the condition is a boolean
			checkTypes {
				given = conditions,
				expected = {BOOLEAN_TYPE},
				purpose = "if condition",
				givenLocation = clause.condition.location,
				expectedLocation = clause.condition.location,
			}

			-- Ignore new scope (scope ends)
			local body = compileStatement(clause.body, scope, context)

			local returns
			if body.returns == elseSt.returns then
				returns = body.returns
			else
				returns = "maybe"
			end

			elseSt = sequenceSt {
				conditionCode,
				{
					tag = "if",
					condition = conditions[1],
					bodyThen = body,
					bodyElse = elseSt,
					returns = returns,
				}
			}
		end

		local returns
		if body.returns == elseSt.returns then
			returns = body.returns
		else
			returns = "maybe"
		end

		table.insert(code, {
			tag = "if",
			condition = conditions[1],
			bodyThen = body,
			bodyElse = elseSt,
			returns = returns,
		})

		return sequenceSt(code), scope
	elseif statementAST.tag == "match-statement" then
		-- Compile the base
		local code = {}
		local baseCode, bases = compileExpression(statementAST.base, scope, context)
		table.insert(code, baseCode)
		if #bases ~= 1 then
			Report.WRONG_VALUE_COUNT {
				purpose = "match statement",
				givenCount = #bases,
				expectedCount = 1,
				givenLocation = statementAST.base.location,
			}
		end

		-- Check that the base is a union instance
		local baseType = bases[1].type
		if baseType.tag ~= "compound-type" then
			Report.TYPE_MUST_BE {
				givenType = showTypeKind(baseType),
				purpose = "a match statement base",
				givenLocation = statementAST.base.location,
			}
		end

		local definition = context.definitionMap[baseType.packageName][baseType.definitionName]
		assert(definition)
		if definition.tag ~= "union-definition" then
			Report.TYPE_MUST_BE {
				givenType = showTypeKind(baseType),
				purpose = "a match statement base",
				givenLocation = statementAST.base.location,
			}
		end

		-- Compile each case
		local handledCases = {}
		local caseList = {}
		local nos = 0
		local yeses = 0
		for _, caseAST in ipairs(statementAST.cases) do
			local variant = caseAST.head.variant
			if not definition._fieldMap[variant] then
				Report.NO_SUCH_MEMBER {
					memberType = "variant",
					name = variant,
					container = showTypeKind(baseType),
					location = caseAST.head.location,
				}
			end

			-- Check that the variable name is fresh
			local variable = caseAST.head.variable
			if scope:get(variable) then
				Report.VARIABLE_DEFINED_TWICE {
					name = variable,
					first = scope:get(variable).definitionLocation,
					second = caseAST.head.location,
				}
			end

			-- Check that no variant is handled twice
			if handledCases[variant] then
				Report.VARIANT_USED_TWICE {
					variant = variant,
					firstLocation = handledCases[variant].location,
					secondLocation = caseAST.head.location,
				}
			end
			handledCases[variant] = caseAST.head
			
			-- Substitute the base type's generics into the field type
			local caseTypeRaw = definition._fieldMap[variant].type
			local substitutionMap = {}
			for i, argument in ipairs(baseType.arguments) do
				local name = definition.genericConstraintMap.order[i]
				substitutionMap[name] = argument
			end
			local caseType = substituteGenerics(caseTypeRaw, substitutionMap)

			local subscope = scope:with(variable, {
				name = variable,
				type = caseType,
				definitionLocation = caseAST.head.location,
			})

			-- Compile the body, noting whether or not this structure returns
			local body = compileStatement(caseAST.body, subscope, context)
			if body.returns == "yes" then
				yeses = yeses + 1
			elseif body.returns == "no" then
				nos = nos + 1
			else
				yeses = yeses + 0.5
				nos = nos + 0.5
			end

			table.insert(caseList, {
				variable = {
					name = variable,
					type = caseType,
				},
				variant = variant,
				statement = body,
			})
		end

		-- Handle exhaustivity
		for variant in pairs(definition._fieldMap) do
			if not handledCases[variant] then
				local falseVariable = {
					name = vendUniqueIdentifier(),
					type = BOOLEAN_TYPE,
				}
				local isaVariable = {
					name = vendUniqueIdentifier(),
					type = BOOLEAN_TYPE,
				}

				table.insert(code, proofSt(sequenceSt {
					-- For asserting false
					{
						tag = "local",
						variable = falseVariable,
						returns = "no",
					},
					{
						tag = "boolean",
						boolean = false,
						destination = falseVariable,
						returns = "no",
					},

					-- Check if it is possibly the unhandled cases
					{
						tag = "local",
						variable = isaVariable,
						returns = "no",
					},
					{
						tag = "isa",
						variant = variant,
						base = bases[1],
						destination = isaVariable,
						returns = "no",
					},

					-- If it's the unhandled case, assert false
					{
						tag = "if",
						condition = isaVariable,
						bodyThen = {
							tag = "verify",
							variable = falseVariable,
							checkLocation = statementAST.location,
							conditionLocation = statementAST.location,
							reason = "the tag is not the unhandled variant `" .. variant .. "`",
							returns = "no",
						},
						bodyElse = sequenceSt {},
						returns = "no",
					},
				}))
			end
		end

		local returns
		if nos == 0 then
			returns = "yes"
		elseif yeses == 0 then
			returns = "no"
		else
			returns = "maybe"
		end

		table.insert(code, {
			tag = "match",
			base = bases[1],
			cases = caseList,
			returns = returns,
		})

		return sequenceSt(code), scope
	elseif statementAST.tag == "assert-statement" then
		local assertContext = {
			-- Universal
			definitionMap = context.definitionMap,

			-- Contextual
			canUseBang = false,
			proof = true,
			
			-- These are irrelevant to expression compilation:
			returnTypes = context.returnTypes,
			makePostamble = function() end,
			
			-- Definition scope dependent
			newType = context.newType,
			typeResolver = context.typeResolver,
			typeResolverContext = context.typeResolverContext,
			constraintMap = context.constraintMap,
		}
		local expressionCode, results = compileExpression(statementAST.expression, scope, assertContext)

		checkTypes {
			given = results,
			expected = {BOOLEAN_TYPE},
			purpose = "assert condition",
			givenLocation = statementAST.expression.location,
			expectedLocation = statementAST.expression.location,
		}

		assert(#results == 1)
		local code = {
			tag = "proof",
			body = sequenceSt {
				expressionCode,
				{
					tag = "verify",
					variable = results[1],
					checkLocation = statementAST.expression.location,
					conditionLocation = statementAST.expression.location,
					reason = "the assertion",
					returns = "no",
				}
			},
			returns = "no",
		}

		return code, scope
	end

	error("compileStatement: " .. statementAST.tag)
end

-- RETURNS a StatementIR, Variable which executes the condition and assigns the
-- result to returned Boolean variable (which is true, vacuously, when the
-- `when` conditions don't hold)
function compilePredicate(ast, callScope, proofContext, purpose)
	assertis(ast, recordType {
		condition = "ASTExpression",
		whens = listType "ASTExpression",
	})
	assertis(callScope, "object")
	assertis(proofContext, recordType {
		proof = constantType(true),
		canUseBang = constantType(false),
		definitionMap = mapType("string", "object"),

		-- Container specific
		typeResolver = "function",
		definitionMap = mapType("string", "object"),
		constraintMap = mapType("string", listType "object"),
	})
	assertis(purpose, "string")

	local resultVariable = {
		name = vendUniqueIdentifier(),
		type = BOOLEAN_TYPE,
	}

	local evalCode, insideResults = compileExpression(ast.condition, callScope, proofContext)
	checkTypes {
		given = insideResults,
		expected = {BOOLEAN_TYPE},
		purpose = purpose .. " condition",
		givenLocation = ast.condition.location,
		expectedLocation = ast.condition.location,
	}

	-- Create assumes
	evalCode = sequenceSt {
		evalCode,
		{
			tag = "assign",
			source = insideResults[1],
			destination = resultVariable,
			returns = "no",
		}
	}

	-- Wrap assumes in necessary when conditions
	for i = #ast.whens, 1, -1 do
		local whenCode, whenResults = compileExpression(ast.whens[i], callScope, proofContext)
		checkTypes {
			given = whenResults,
			expected = {BOOLEAN_TYPE},
			purpose = purpose .. " when condition",
			givenLocation = ast.whens[i].location,
			expectedLocation = ast.whens[i].location,
		}

		-- Only run the ensures conditionally
		evalCode = sequenceSt {
			whenCode,
			{
				tag = "if",
				condition = whenResults[1],
				bodyThen = evalCode,
				bodyElse = sequenceSt {},
				returns = "no",
			}
		}
	end

	local code = sequenceSt {
		{
			tag = "boolean",
			boolean = true,
			destination = resultVariable,
			returns = "no",
		},
		evalCode,
	}

	return code, resultVariable
end

--------------------------------------------------------------------------------

-- RETURNS a Semantics, an IR description of the program
local function semanticsSmol(sources, main)
	assertis(main, "string")

	-- Process package scopes
	local definitionMap = {}
	for _, source in ipairs(sources) do
		-- Create package if it does not already exist
		-- Packages need not be unique
		local packageName = source.package.name
		definitionMap[packageName] = definitionMap[packageName] or {}

		-- Get a set of imported names
		local importsByName = {}
		for _, import in ipairs(source.imports) do
			if import.definitionName then
				if importsByName[import.definitionName] then
					Report.NAME_IMPORTED_TWICE {
						name = import.definitionName,
						firstLocation = importsByName[import.definitionName].location,
						secondLocation = import.location,
					}
				end
				importsByName[import.definitionName] = import
			end
		end

		-- Get each definition in this source
		for _, definition in ipairs(source.definitions) do
			local previousDefinition = definitionMap[packageName][definition.name]
			if previousDefinition then
				-- Definition of same name already exists
				Report.DEFINITION_DEFINED_TWICE {
					fullName = previousDefinition.fullName,
					firstLocation = previousDefinition.definition.location,
					secondLocation = definition.location,
				}
			elseif importsByName[definition.name] then
				-- Import of same short name already exists
				Report.DEFINITION_DEFINED_TWICE {
					fullName = definition.name,
					firstLocation = importsByName[definition.name].location,
					secondLocation = definition.location,
				}
			end

			-- Record the existence of this definition
			definitionMap[packageName][definition.name] = {
				tag = definition.tag,
				packageName = packageName,
				fullName = packageName .. ":" .. definition.name,
				importsByName = importsByName,
				source = source,
				definition = definition,
			}
		end
	end

	-- Annotate each definition with its resolver
	for packageName, package in pairs(definitionMap) do
		for definitionName, definition in pairs(package) do
			definition.resolver = makeDefinitionASTResolver(definition, definitionMap)
			local arguments = {}
			for _, parameter in ipairs(definition.definition.generics.parameters) do
				table.insert(arguments, {
					tag = "generic-type",
					role = "type",
					name = parameter.name,
				})
			end

			-- Get the tag and role based on the definition tag
			local tag, role
			if definition.tag == "interface-definition" then
				tag = "interface-constraint"
				role = "constraint"
			else
				tag = "compound-type"
				role = "type"
			end

			-- Mark the definition with the kind that it represents
			-- This may need to be "instantiated" if the definition is
			-- parametric
			definition.kind = {
				tag = tag,
				role = role,
				arguments = arguments,
				packageName = packageName,
				definitionName = definitionName,
			}
		end
	end

	-- Get the generic requirements for all definitions
	for _, package in pairs(definitionMap) do
		for _, definition in pairs(package) do
			-- Check that generic parameters are not repeated
			local constraintMap = {}
			local genericLocationMap = {}
			local parameterNames = {}
			for _, parameterAST in ipairs(definition.definition.generics.parameters) do
				if genericLocationMap[parameterAST.name] then
					Report.GENERIC_DEFINED_TWICE {
						name = parameterAST.name,
						firstLocation = genericLocationMap[parameterAST.name],
						secondLocation = parameterAST.location,
					}
				end
				genericLocationMap[parameterAST.name] = parameterAST.location
				constraintMap[parameterAST.name] = {}
				table.insert(parameterNames, parameterAST.name)
			end
			
			assertis(definition.kind, "Kind")

			local context = {
				-- #Self is only allowed in Interface definitions
				selfAllowed = definition.tag == "interface-definition" and definition.kind,

				-- We do not yet know which generics are in scope with which
				-- constraints
				generics = genericLocationMap,
				checkConstraints = false,
				template = false,
			}

			-- Read the constraints, suppressing errors regarding no constraints
			-- Note: We MUST check them again afterwards
			for i, constraintAST in ipairs(definition.definition.generics.constraints) do
				local concerning = constraintAST.parameter.name

				-- Process the constraint, checking that it is a ConstraintKind
				-- and not a TypeKind
				local constraint = definition.resolver(constraintAST.constraint, context)
				if constraint.role ~= "constraint" then
					Report.CONSTRAINTS_MUST_BE_INTERFACES {
						is = "type parameter constraint",
						typeShown = showTypeKind(constraint),
						location = constraintAST.location,
					}
				end

				table.insert(constraintMap[concerning], {
					constraint = constraint,
					location = constraintAST.location,
					name = "smol_con_" .. concerning .. "_" .. i,
					concerningIndex = table.indexof(parameterNames, concerning),
				})
			end

			-- Record, for future checking, the constraints that each type
			-- parameter claims to implement
			definition.genericConstraintMap = {
				order = parameterNames,
				map = constraintMap,
				locations = genericLocationMap,
			}

			-- Get the constraints list
			definition.constraintArguments = {}
			for _, r in pairs(constraintMap) do
				for _, v in ipairs(r) do
					table.insert(definition.constraintArguments, v)
					v.constraintListIndex = #definition.constraintArguments
				end
			end


			-- Read the implements claims, suppressing errors regarding no
			-- constraints
			-- NOTE: We MUST check them again afterwards
			local claims = {}
			for _, claimAST in ipairs(definition.definition.implements) do
				local claim = definition.resolver(claimAST, context)
				if claim.role ~= "constraint" then
					Report.CONSTRAINTS_MUST_BE_INTERFACES {
						is = "implements claim",
						typeShown = showTypeKind(claim),
						location = claimAST.location,
					}
				end

				table.insert(claims, {
					claimLocation = claimAST.location,
					constraint = claim,
				})
			end
			
			assertis(claims, listType(recordType{
				claimLocation = "Location",
				constraint = "ConstraintKind",
			}))
			definition.implements = claims
		end
	end

	-- Check that the bits concerning constraint definitions (implements and
	-- generic constraints) themselves don't violate any constraints
	for _, package in pairs(definitionMap) do
		for _, definition in pairs(package) do
			definition.resolverContext = {
				-- #Self is only allowed in Interface definitions
				selfAllowed = definition.tag == "interface-definition" and definition.kind,

				-- We do not yet know which generics are in scope with which
				-- constraints
				generics = definition.genericConstraintMap,
				checkConstraints = true,

				-- Since a map is provided instead, no templating
				template = false,
			}

			-- Check the well-formedness of each implements claim
			for _, claimAST in ipairs(definition.definition.implements) do
				definition.resolver(claimAST, definition.resolverContext)
			end

			-- Check the well-formedness of each interface constraint
			for _, constraint in ipairs(definition.definition.generics.constraints) do
				definition.resolver(constraint.constraint, definition.resolverContext)
			end
		end
	end

	-- Collection and check the members of each definition
	for packageName, package in pairs(definitionMap) do
		for definitionName, definition in pairs(package) do
			-- RETURNS a valid Signature
			local function checkedSignature(signatureAST)
				-- Get the list of parameters
				local parameters = {}

				if signatureAST.modifier.lexeme == "method" then
					table.insert(parameters, {
						name = "this",
						type = definition.tag == "interface-definition" and SELF_TYPE or definition.kind,
					})
				end

				for _, p in ipairs(signatureAST.parameters) do
					-- Check if the name is repeated
					local previous = table.findwith(parameters, "name", p.name)
					if previous then
						Report.VARIABLE_DEFINED_TWICE {
							name = p.name,
							first = previous.definitionLocation,
							second = p.location,
						}
					end

					-- Check the type
					local type = definition.resolver(p.type, definition.resolverContext)
					if type.role ~= "type" then
						Report.INTERFACE_USED_AS_TYPE {
							interface = showConstraintKind(type),
							location = p.type.location,
						}
					end

					table.insert(parameters, {
						name = p.name,
						type = type,
						definitionLocation = p.location,
					})
				end

				return {
					modifier = signatureAST.modifier.lexeme,
					memberName = signatureAST.name,
					longName = packageName .. ":" .. definitionName .. "." .. signatureAST.name,
					foreign = false,
					bang = not not signatureAST.bang,
					parameters = parameters,
					returnTypes = table.map(
						definition.resolver,
						signatureAST.returnTypes,
						definition.resolverContext
					),

					-- To be processed after all signatures are known
					requiresASTs = signatureAST.requires,
					ensuresASTs = signatureAST.ensures,

					-- These are only filled for builtins
					logic = false,
					eval = false,
				}
			end

			if definition.tag == "class-definition" or definition.tag == "union-definition" then
				-- Get a map of field members
				local fieldMap = {}
				for _, fieldAST in ipairs(definition.definition.fields) do
					if fieldMap[fieldAST.name] then
						Report.MEMBER_DEFINED_TWICE {
							name = fieldAST.name,
							firstLocation = fieldMap[fieldAST.name].definitionLocation,
							secondLocation = fieldAST.location,
						}
					end

					-- Check that the type is in fact a type
					local type = definition.resolver(fieldAST.type, definition.resolverContext)
					if type.role ~= "type" then
						Report.INTERFACE_USED_AS_TYPE {
							interface = showConstraintKind(type),
							location = fieldAST.type.location,
						}
					end

					fieldMap[fieldAST.name] = {
						name = fieldAST.name,
						type = type,
						definitionLocation = fieldAST.location,
					}
				end

				-- Get a map of function members
				local functionMap = {}
				for _, methodAST in ipairs(definition.definition.methods) do
					-- Check if this name is fresh
					local signature = checkedSignature(methodAST.signature)
					signature.foreign = methodAST.foreign
					local previous = fieldMap[signature.memberName] or functionMap[signature.memberName]
					if previous then
						Report.MEMBER_DEFINED_TWICE {
							name = signature.memberName,
							firstLocation = previous.definitionLocation,
							secondLocation = signature.definitionLocation,
						}
					end

					functionMap[signature.memberName] = {
						signature = signature,
						bodyAST = not signature.foreign and methodAST.body,
						definitionLocation = methodAST.signature.location,
					}
				end

				definition._fieldMap = fieldMap
				definition._functionMap = functionMap
			elseif definition.tag == "interface-definition" then
				-- Get a map of function members
				local functionMap = {}
				for _, signatureAST in ipairs(definition.definition.signatures) do
					-- Check if this name is fresh
					local signature = checkedSignature(signatureAST)
					if functionMap[signature.memberName] then
						Report.MEMBER_DEFINED_TWICE {
							name = signature.memberName,
							firstLocation = functionMap[signature.memberName].definitionLocation,
							secondLocation = signatureAST.location,
						}
					end

					functionMap[signature.memberName] = {
						signature = signature,
						definitionLocation = signatureAST.location,
					}
				end
				definition._functionMap = functionMap
			else
				error("bad definition tag")
			end
		end
	end

	-- Check that each type actually implements the methods they claim to
	-- NOTE: This does NOT check that requires/ensures is acceptable, which will
	-- be checked when the method implementation is compiled
	for _, package in pairs(definitionMap) do
		for _, definition in pairs(package) do
			if definition.tag == "class-definition" or definition.tag == "union-definition" then
				for _, implement in ipairs(definition.implements) do
					local constraint = implement.constraint
					if constraint.tag == "interface-constraint" then
						local interfaceDefinition = definitionMap[constraint.packageName][constraint.definitionName]
						local substitutionMap = {
							Self = definition.kind,
						}

						-- The interface's signatures need to be transformed to
						-- substitute generics for the specified arguments
						for i, argument in ipairs(constraint.arguments) do
							substitutionMap[interfaceDefinition.genericConstraintMap.order[i]] = argument
						end

						-- Check each signature
						for name, fRaw in pairs(interfaceDefinition._functionMap) do
							local f = {
								signature = substitutedSignature(fRaw.signature, substitutionMap),
								definitionLocation = fRaw.definitionLocation,
							}

							-- Check for a function member of the same name
							local matching = definition._functionMap[name]
							if not matching then
								Report.INTERFACE_REQUIRES_MEMBER {
									claimLocation = implement.claimLocation,
									class = definition.fullName,
									interface = showConstraintKind(constraint),
									memberName = name,
									interfaceLocation = f.definitionLocation,
								}
							end

							-- Check that the modifiers match
							if matching.signature.modifier ~= f.signature.modifier then
								Report.INTERFACE_MODIFIER_MISMATCH {
									claimLocation = implement.claimLocation,
									class = definition.fullName,
									interface = showConstraintKind(constraint),
									memberName = name,
									interfaceLocation = f.definitionLocation,
									classLocation = matching.definitionLocation,

									-- Explain modifier mismatch
									interfaceModifier = f.signature.modifier,
									classModifier = matching.signature.modifier,
								}
							end

							-- Check that the bangs match
							if matching.signature.bang ~= f.signature.bang then
								Report.INTERFACE_BANG_MISMATCH {
									claimLocation = implement.claimLocation,
									class = definition.fullName,
									interface = showConstraintKind(constraint),
									memberName = name,
									modifier = f.signature.modifier,
									interfaceLocation = f.definitionLocation,
									classLocation = matching.definitionLocation,

									-- Explain bang mismatch
									expectedBang = f.signature.bang,
								}
							end

							-- Check that the parameter types match
							if #matching.signature.parameters ~= #f.signature.parameters then
								Report.INTERFACE_COUNT_MISMATCH {
									claimLocation = implement.claimLocation,
									class = definition.fullName,
									interface = showConstraintKind(constraint),
									memberName = name,
									modifier = f.signature.modifier,
									interfaceLocation = f.definitionLocation,
									classLocation = matching.definitionLocation,

									-- Explain count mismatch
									thing = "parameter",
									classCount = #matching.signature.parameters,
									interfaceCount = #f.signature.parameters,
								}
							end
							for i, a in ipairs(matching.signature.parameters) do
								local expected = f.signature.parameters[i].type
								if not areTypesEqual(a.type, expected) then
									Report.INTERFACE_TYPE_MISMATCH {
										claimLocation = implement.claimLocation,
										class = definition.fullName,
										interface = showConstraintKind(constraint),
										memberName = name,
										modifier = f.signature.modifier,
										interfaceLocation = f.definitionLocation,
										classLocation = matching.definitionLocation,

										-- Explain type mismatch
										thing = "parameter",
										index = i,
										interfaceType = showTypeKind(expected),
										classType = showTypeKind(a.type),
									}
								end
							end

							-- Check that the return types match
							if #matching.signature.returnTypes ~= #f.signature.returnTypes then
								Report.INTERFACE_COUNT_MISMATCH {
									claimLocation = implement.claimLocation,
									class = definition.fullName,
									interface = showConstraintKind(constraint),
									memberName = name,
									modifier = f.signature.modifier,
									interfaceLocation = f.definitionLocation,
									classLocation = matching.definitionLocation,

									-- Explain count mismatch
									thing = "return type",
									classCount = #matching.signature.returnTypes,
									interfaceCount = #f.signature.returnTypes,
								}
							end
							for i, r in ipairs(matching.signature.returnTypes) do
								local expected = f.signature.returnTypes[i]
								if not areTypesEqual(r, expected) then
									Report.INTERFACE_TYPE_MISMATCH {
										claimLocation = implement.claimLocation,
										class = definition.fullName,
										interface = showConstraintKind(constraint),
										memberName = name,
										modifier = f.signature.modifier,
										interfaceLocation = f.definitionLocation,
										classLocation = matching.definitionLocation,

										-- Explain type mismatch
										thing = "return type",
										index = i,
										interfaceType = showTypeKind(expected),
										classType = showTypeKind(r),
									}
								end
							end
						end
					elseif constraint.tag == "keyword-constraint" then
						error("TODO: keyword-constraint")
					else
						error("unknown constraint type")
					end
				end
			end
		end
	end

	-- Compile the bodies of every function
	local functions = {}
	for _, package in pairs(definitionMap) do
		for _, definition in pairs(package) do
			if definition.tag == "interface-definition" then
				-- Check each signature's ensures and requires clauses
				for key, f in pairs(definition._functionMap) do
					local context = {
						returnTypes = f.signature.returnTypes,

						-- Generic information, noting what Self is
						constraintMap = table.with(definition.genericConstraintMap.map, "Self", {{
							constraint = definition.kind,
							name = "self",
							location = definition.definition.location,
						}}),
						typeResolver = definition.resolver,
						typeResolverContext = definition.resolverContext,

						-- This is for checking the pre and post conditions,
						-- which cannot use bang even if this is a bang action
						canUseBang = false,

						-- Cannot use new() in an interface
						newType = false,

						proof = true,
						definitionMap = definitionMap,
					}

					-- Create the scope
					local scope = Map.new()
					for _, parameter in ipairs(f.signature.parameters) do
						scope = scope:with(parameter.name, {
							name = parameter.name,
							type = parameter.type,
							final = true,
							definitionLocation = parameter.definitionLocation,
						})
					end

					-- Compile requires checking for errors, and discard results
					for _, requiresAST in ipairs(f.signature.requiresASTs) do
						compilePredicate(requiresAST, scope, context, "requires")
					end

					-- Add returns to the scope when appropriate
					if #f.signature.returnTypes == 1 then
						scope = scope:with("return", {
							definitionLocation = f.definitionLocation,
							name = "return",
							type = f.signature.returnTypes[1],
						})
					end
					
					-- Compile ensures checking for errors, and discard results
					for _, ensuresAST in ipairs(f.signature.ensuresASTs) do
						compilePredicate(ensuresAST, scope, context, "ensures")
					end
				end
			elseif definition.tag == "class-definition" or definition.tag == "union-definition" then
				for key, f in pairs(definition._functionMap) do
					local context = {
						returnTypes = f.signature.returnTypes,
						canUseBang = f.signature.bang,
						newType = definition.kind,
						proof = false,

						-- Generic information
						constraintMap = definition.genericConstraintMap.map,

						-- RETURNS a ProofSt
						makePostamble = function(returning)
							print("TODO")
							return sequenceSt {}
						end,

						-- More global information
						typeResolver = definition.resolver,
						typeResolverContext = definition.resolverContext,
						definitionMap = definitionMap,
					}
				
					local proofContext = {
						canUseBang = false,
						proof = true,
						newType = context.newType,

						constraintMap = context.constraintMap,
						typeResolver = context.typeResolver,
						typeResolverContext = context.typeResolverContext,
						definitionMap = context.definitionMap,
					}

					-- Create the initial (argument) scope
					local scope = Map.new()
					for _, parameter in ipairs(f.signature.parameters) do
						scope = scope:with(parameter.name, {
							name = parameter.name,
							type = parameter.type,
							final = true,
							definitionLocation = parameter.definitionLocation,
						})
					end

					-- Compile each requires to an assume
					local requiresContext = {
					}
					local preambleList = {}
					for _, r in ipairs(f.signature.requiresASTs) do
						local proofScope = scope
						local preAssume, assumeVariable = compilePredicate(r, proofScope, proofContext, "requires")
						table.insert(preambleList, preAssume)
						table.insert(preambleList, {
							tag = "assume",
							variable = assumeVariable,
							returns = "no",
						})
					end

					-- The preamble is only executed statically, not dynamically
					local preamble = proofSt(sequenceSt(preambleList))

					if not f.signature.foreign then
						-- Compile the body
						assert(f.bodyAST)
						local body = compileStatement(f.bodyAST, scope, context)

						if body.returns ~= "yes" then
							if #f.signature.returnTypes == 1 and areTypesEqual(UNIT_TYPE, f.signature.returnTypes[1]) then
								-- return unit; is optional
								local unitOut = {
									name = vendUniqueIdentifier(),
									type = UNIT_TYPE,
								}
								body = sequenceSt {
									body,
									{
										tag = "local",
										variable = unitOut,
										returns = "no",
									},
									{
										tag = "unit",
										destination = unitOut,
										returns = "no",
									},
									{
										tag = "return",
										sources = {unitOut},
										returns = "yes",
									},
								}
							else
								Report.FUNCTION_DOESNT_RETURN {
									modifier = f.signature.modifier,
									name = f.signature.memberName,
									returns = table.concat(table.map(showTypeKind, f.signature.returnTypes), ", "),
									location = f.definitionLocation,
								}
							end
						end

						-- Package the function up for contract verification and
						-- code generation
						table.insert(functions, {
							namespace = showTypeKind(definition.kind),
							thisType = definition.kind,
							name = key,
							body = sequenceSt {preamble, body},
							signature = f.signature,
							constraintArguments = definition.constraintArguments,
						})
					else
						-- Still notate foreign functions
						-- (They still will need signatures in codegen, and we
						-- can catch unsupported ones)
						table.insert(functions, {
							namespace = showTypeKind(definition.kind),
							thisType = definition.kind,
							name = key,
							body = false,
							signature = f.signature,
							constraintArguments = definition.constraintArguments,
						})
					end
				end
			end
		end
	end

	assertis(functions, listType "FunctionIR")

	-- Collect the structures that need to be compiled
	local compounds = {}
	local interfaces = {}
	for _, package in pairs(definitionMap) do
		for _, definition in pairs(package) do
			if definition.tag == "interface-definition" then
				table.insert(interfaces, definition)
			else
				assert(definition.tag == "class-definition" or definition.tag == "union-definition")
				table.insert(compounds, definition)
			end
		end
	end

	-- Add foreign functions from builtins
	for keyword, builtin in pairs(common.builtinDefinitions) do
		for key, f in pairs(builtin.functionMap) do
			assert(f.signature.foreign)
			table.insert(functions, {
				namespace = keyword,
				thisType = builtin.kind,
				name = key,
				body = false,
				signature = f.signature,
				constraintArguments = {},
			})
		end
	end

	return freeze {
		builtins = common.builtinDefinitions,
		compounds = compounds,
		interfaces = interfaces,
		functions = functions,
		main = main,
	}
end

return {
	semantics = semanticsSmol,
}
