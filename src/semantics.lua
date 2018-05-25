-- Curtis Fenner, copyright (C) 2017

local Report = import "semantic-errors.lua"
local common = import "common.lua"
local showType = common.showType
local areTypesEqual = common.areTypesEqual
local areInterfaceTypesEqual = common.areInterfaceTypesEqual
local excerpt = common.excerpt
local variableDescription = common.variableDescription

local BOOLEAN_DEF = table.findwith(common.BUILTIN_DEFINITIONS, "name", "Boolean")
local UNKNOWN_LOCATION = freeze {begins = "???", ends = "???"}

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
		error "TODO: How should #Self be substitute?"
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
	for key, importAST in pairs(info.importsByName) do
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

	-- RETURNS nothing
	-- REQUIRES arguments be all TypeKinds and correct arity
	-- REQUIRES resolvers be set for all the definitions
	local function checkRequirements(arguments, package, name)
		assertis(arguments, listType "TypeKind")
		assertis(package, "string")
		assertis(name, "string")

		local definition = definitionMap[package][name]
		assert(definition and #definition.definition.generics == #arguments)

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
						table.insert(present, substituteGenerics(implement, substitutionMap))
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
		if definition.definition.tag == "interface-definition" then
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
			if definition.definition.tag == "interface-definition" then
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

	-- Get the generic requirements for all definintions
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
				selfAllowed = definition.definition.tag == "interface-definition" and definition.kind,

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

				table.insert(claims, claim)
			end
			
			assertis(claims, listType "ConstraintKind")
			definition.implements = claims
		end
	end

	-- Check that the bits concerning constraint definitions (implements and
	-- generic constraints) themselves don't violate any constraints
	for _, package in pairs(definitionMap) do
		for _, definition in pairs(package) do
			local context = {
				-- #Self is only allowed in Interface definitions
				selfAllowed = definition.definition.tag == "interface-definition" and definition.kind,

				-- We do not yet know which generics are in scope with which
				-- constraints
				generics = definition.genericConstraintMap,
				checkConstraints = true,
			}

			-- Check the well-formedness of each implements claim
			for _, claimAST in ipairs(definition.definition.implements) do
				definition.resolver(claimAST, context)
			end

			-- Check the well-formedness of each interface constraint
			for _, constraint in ipairs(definition.definition.generics.constraints) do
				definition.resolver(constraint.constraint, context)
			end
		end
	end

	-- Compile the remainder
	

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
