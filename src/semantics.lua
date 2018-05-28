-- Curtis Fenner, copyright (C) 2017

local Map = import "data/map.lua"

local Report = import "semantic-errors.lua"
local common = import "common.lua"
local showType = common.showType
local areInterfaceTypesEqual = common.areInterfaceTypesEqual
local excerpt = common.excerpt

local BOOLEAN_DEF = table.findwith(common.BUILTIN_DEFINITIONS, "name", "Boolean")
local UNKNOWN_LOCATION = freeze {begins = "???", ends = "???"}

local STRING_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "String",
}

-- RETURNS a description of the given TypeKind as a string of Smol code
local function showTypeKind(t)
	assertis(t, "TypeKind")

	if t.tag == "compound-type" then
		local base = t.packageName .. ":" .. t.definitionName
		if #t.arguments == 0 then
			return base
		end
		local arguments = table.map(showTypeKind, t.arguments)
		return base .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif t.tag == "self-type" then
		return "#Self"
	elseif t.tag == "generic-type" then
		return "#" .. t.name
	elseif t.tag == "keyword-type" then
		return t.name
	end
	error "unknown TypeKind tag"
end

-- RETURNS a description of the given ConstraintKind as a string of Smol code
local function showConstraintKind(c)
	assertis(c, "ConstraintKind")

	if c.tag == "interface-constraint" then
		local base = c.packageName .. ":" .. c.definitionName
		if #c.arguments == 0 then
			return base
		end
		local arguments = table.map(showTypeKind, c.arguments)
		return base .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif c.tag == "keyword-constraint" then
		return c.name
	end
	error "unknown ConstraintKind tag"
end

-- RETURNS whether or not two given types are the same
local function areTypesEqual(a, b)
	assertis(a, "TypeKind")
	assertis(b, "TypeKind")

	return showTypeKind(a) == showTypeKind(b)
end

-- RETURNS a Kind with the same structure, buch each GenericTypeKind replaced
-- with a TypeKind from the map
-- REQUIRES each GenericTypeKind mentioned by the kind is present in the map
local function substituteGenerics(kind, map)
	assertis(kind, "Kind")
	assertis(map, mapType("string", "TypeKind"))
	
	if kind.tag == "generic-type" then
		assert(map[kind.name])
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
		assertis(map.Self, "TypeKind")

		return map.Self
	end

	-- All other Kinds are non-recursive
	return kind
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
		-- Check if this is reachable
		if returns == "yes" then
			Report.UNREACHABLE_STATEMENT {
				location = s.location,
			}
		end

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

		-- TODO: replace with correct solution
		location = statements[1] and statements[1].location or UNKNOWN_LOCATION,
	}
end

-- For vendUniqueIdentifier
local _uniqueTick = 0

-- RETURNS a fresh identifier
local function vendUniqueIdentifier()
	_uniqueTick = _uniqueTick + 1

	return "_identifier" .. _uniqueTick
end

local function checkTypes(p)
	assertis(p, recordType {
		given = listType(recordType {type = "TypeKind"}),
		expected = listType "TypeKind",
		purpose = "string",
		givenLocation = "Location",
		expectedLocation = "Location",
	})

	if #p.given ~= #p.expected then
		Report.TYPE_MISMATCH {
			given = table.map(table.getter "type", p.given),
			expected = p.expected,
			purpose = p.purpose,
			givenLocation = p.givenLocation,
			expectedLocation = p.expectedLocation,
		}
	end

	for i in ipairs(p.given) do
		if not areTypesEqual(p.given[i].type, p.expected[i]) then
			Report.TYPE_MISMATCH {
				given = table.map(table.getter "type", p.given),
				expected = p.expected,
				purpose = p.purpose,
				givenLocation = p.givenLocation,
				expectedLocation = p.expectedLocation,
			}
		end
	end
end

-- RETURNS StatementIR, out variables, impure boolean
-- The StatementIR describes how to execute the statement such that the out
-- variables are assigned with the evaluation.
-- ENSURES at least one out variable is returned
-- impure is true if executing this expression could have observable side
-- effects (because it contains a `!` action)
local function compileExpression(expressionAST, scope, context)
	assertis(context, recordType {
		returnTypes = listType "TypeKind",
		canUseBang = "boolean",
		proof = "boolean",
		newType = choiceType(constantType(false), "TypeKind"),

		typeResolver = "function",
		typeResolverContext = "object",
		definitionMap = "object",
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
				location = expressionAST.location,
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
	elseif expressionAST.tag == "new-expression" then
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
				location = expressionAST.location,
			}
		}

		local providedAt = {}
		local fields = {}
		local impure = false
		for key, fieldAST in ipairs(expressionAST.fields) do
			-- Compile the argument
			local c, outs, i = compileExpression(fieldAST.value, scope, context)

			local field = definition.fieldMap[key]
			if not field then
				Report.NO_SUCH_MEMBER {
					memberType = "field",
					container = packageName .. ":" .. definitionName,
					name = key,
					location = fieldAST.location,
				}
			end

			checkTypes {
				given = outs,
				expected = {field.type},
				purpose = "initialization of `" .. key .. "` field",
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
		end

		return code, {outVariable}, impure
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
				else
					impure = ast.location
				end
			end
		end

		if baseType.tag == "self-type" then
			Report.SELF_OUTSIDE_INTERFACE {
				location = expressionAST.baseType.location,
			}
		elseif baseType.tag == "keyword-type" then
			error "TODO"
		elseif baseType.tag == "generic-type" then
			error "TODO"
		elseif baseType.tag == "compound-type" then
			local definition = context.definitionMap[baseType.packageName][baseType.definitionName]
			assert(definition)
			assert(definition.tag == "class-definition" or definition.tag == "union-definition")

			-- Get the member
			local member = definition.functionMap[expressionAST.funcName]
			if not member or member.signature.modifier ~= "static" then
				Report.NO_SUCH_MEMBER {
					memberType = "static",
					container = baseType.packageName .. ":" .. baseType.definitionName,
					name = expressionAST.funcName,
					location = expressionAST.location,
				}
			end

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
					location = expressionAST.location,
				})
				table.insert(destinations, destination)
			end

			local call = {
				tag = "static-call",
				arguments = arguments,
				destinations = destinations,
				returns = "no",
				signature = member.signature,
			}
			assertis(call, "StaticCallSt")
			table.insert(code, call)

			return sequenceSt(code), destinations, impure or member.signature.bang
		end
		error "TODO"
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
		definitionMap = "object",
	})

	if statementAST.tag == "block" then
		local statements = {}
		local scopePrime = scope
		for _, s in ipairs(statementAST.statements) do
			-- Compile the statement
			local statement, newScope = compileStatement(s, scopePrime, context)
			scopePrime = newScope
			table.insert(statements, statement)
		end
		
		return sequenceSt(statements), scopePrime
	elseif statementAST.tag == "return-statement" then
		local code = {}
		local toReturn = {}

		-- Compile each value
		local impure = false
		for _, a in ipairs(statementAST.values) do
			local c, outs, i = compileExpression(a, scope, context)
			assert(type(i) == "boolean")
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
					impure = i
				end
			end
		end

		if #types == 0 then
			-- `return;` is short for `return unit;`
			types = {{
				tag = "keyword-type",
				role = "type",
				name = "Unit",
			}}
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
	end

	error("compileStatement: " .. statementAST.tag)
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
			}

			-- Read the constraints, suppressing errors regarding no constraints
			-- Note: We MUST check them again afterwards
			for _, constraintAST in ipairs(definition.definition.generics.constraints) do
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
				})
			end

			-- Record, for future checking, the constraints that each type
			-- parameter claims to implement
			definition.genericConstraintMap = {
				order = parameterNames,
				map = constraintMap,
				locations = genericLocationMap,
			}

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
					longName = packageName .. "." .. definitionName .. "." .. signatureAST.name,
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

				definition.fieldMap = fieldMap
				definition.functionMap = functionMap
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
				definition.functionMap = functionMap
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
						for name, f in pairs(interfaceDefinition.functionMap) do
							-- Check for a function member of the same name
							local matching = definition.functionMap[name]
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
								local expected = substituteGenerics(f.signature.parameters[i].type, substitutionMap)
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
								local expected = substituteGenerics(f.signature.returnTypes[i], substitutionMap)
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
			-- Get the constraints list
			local constraintArguments = {}
			for _, genericName in ipairs(definition.genericConstraintMap.order) do
				for i, c in ipairs(definition.genericConstraintMap.map[genericName]) do
					table.insert(constraintArguments, {
						name = genericName .. "_" .. i,
						namespace = "#" .. genericName,
						constraint = c.constraint,
					})
				end
			end

			if definition.tag == "interface-definition" then
				-- Check each signature's ensures and requires clauses
				for key, f in pairs(definition.functionMap) do
					local context = {
						returnTypes = f.signature.returnTypes,

						-- This is for checking the pre and post conditions,
						-- which cannot use bang even if this is a bang action
						canUseBang = false,

						-- Cannot use new() in an interface
						newType = false,

						proof = true,
					}

					-- Compile requires checking for errors, and discard results

					-- Compile ensures checking for errors, and discard results
					print("TODO: interface signature")
				end
			elseif definition.tag == "class-definition" or definition.tag == "union-definition" then
				for key, f in pairs(definition.functionMap) do
					local context = {
						returnTypes = f.signature.returnTypes,
						canUseBang = f.signature.bang,
						newType = definition.kind,
						proof = false,

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

					-- Create the initial (argument) scope
					local scope = Map.new()
					for _, argument in ipairs(f.signature.parameters) do
						scope = scope:with(argument.name, {
							type = argument.type,
							final = true,
							definitionLocation = argument.definitionLocation,
						})
					end

					-- TODO: Compile requires
					local preamble = sequenceSt {}

					if not f.signature.foreign then
						-- Compile the body
						assert(f.bodyAST)
						local body = compileStatement(f.bodyAST, scope, context)

						-- Package the function up for contract verification and
						-- code generation
						table.insert(functions, {
							namespace = showTypeKind(definition.kind),
							thisType = definition.kind,
							name = key,
							body = sequenceSt {preamble, body},
							signature = f.signature,
							constraintArguments = constraintArguments,
						})
					else
						-- TODO: Notate these somehow
					end
				end
			end
		end
	end

	assertis(functions, listType {
		namespace = "string",
		name = "string",
		body = "StatementIR",
		signature = "Signature",
		constraintArguments = listType(recordType {
			generic = "string",
			constraint = "ConstraintKind",
		}),
	})

	return freeze {
		builtins = common.BUILTIN_DEFINITIONS,
		compounds = compounds,
		interfaces = interfaces,
		functions = functions,
		main = main,
	}
end

return {
	semantics = semanticsSmol,
}
