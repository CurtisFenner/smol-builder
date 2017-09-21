-- Curtis Fenner, copyright (C) 2017

local Report = import "semantic-errors.lua"

-- RETURNS the clearest possible combination of a, and b.
local function unclear(a, b)
	assertis(a, "maybe")
	assertis(b, "maybe")
	if a == b then
		return a
	end
	return "maybe"
end

-- RETURNS a string of smol representing the given type
local function showType(t)
	assertis(t, "Type+")

	if t.tag == "concrete-type+" then
		if #t.arguments == 0 then
			return t.name
		end
		local arguments = table.map(showType, t.arguments)
		return t.name .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif t.tag == "keyword-type+" then
		return t.name
	elseif t.tag == "generic+" then
		return "#" .. t.name
	end
	error("unknown Type+ tag `" .. t.tag .. "`")
end

-- RETURNS a string of smol representing the given interface type
local function showInterfaceType(t)
	assertis(t, "InterfaceType+")

	if #t.arguments == 0 then
		return t.name
	end
	local arguments = table.map(showType, t.arguments)
	return t.name .. "[" .. table.concat(arguments, ", ") .. "]"
end

local idCount = 0
-- RETURNS a unique (to this struct) local variable name
local function generateLocalID(hint)
	idCount = idCount + 1
	return "_local" .. tostring(idCount) .. "_" .. tostring(hint)
end

-- RETURNS a StatementIR representing the execution of statements in
-- sequence
local function buildBlock(statements)
	assertis(statements, listType("StatementIR"))

	local returned = "no"
	for i, statement in ipairs(statements) do
		if statement.returns == "yes" then
			assert(i == #statements)
			returned = "yes"
		elseif statement.returns == "maybe" then
			returned = "maybe"
		end
	end

	return freeze {
		tag = "block",
		returns = returned,
		statements = statements,
	}
end

-- RETURNS a LocalSt
local function localSt(variable)
	assertis(variable, "VariableIR")

	return freeze {
		tag = "local",
		variable = variable,
		returns = "no",
	}
end

-- RETURNS whether or not a and b are the same type
-- REQUIRES that type names cannot be shadowed and
-- that a and b come from the same (type) scope
local function areTypesEqual(a, b)
	assertis(a, "Type+")
	assertis(b, "Type+")

	if a.tag ~= b.tag then
		return false
	elseif a.tag == "concrete-type+" then
		if a.name ~= b.name then
			return false
		elseif #a.arguments ~= #b.arguments then
			-- XXX: should this be fixed before here?
			return false
		end
		for k in ipairs(a.arguments) do
			if not areTypesEqual(a.arguments[k], b.arguments[k]) then
				return false
			end
		end
		return true
	elseif a.tag == "keyword-type+" then
		return a.name == b.name
	elseif a.tag == "generic+" then
		return a.name == b.name
	end
	error("unknown type tag `" .. a.tag .. "`")
end

-- RETURNS whether or not a and b are the same interface
-- REQUIRES that type names cannot be shadowed and
-- that a and b come from the same (type) scope
local function areInterfaceTypesEqual(a, b)
	assertis(a, "InterfaceType+")
	assertis(b, "InterfaceType+")

	if a.name ~= b.name then
		return false
	end
	assert(#a.arguments == #b.arguments)

	for k in ipairs(a.arguments) do
		if not areTypesEqual(a.arguments[k], b.arguments[k]) then
			return false
		end
	end

	return true
end

-- assignments: map string -> Type+
-- RETURNS a function Type+ -> Type+ that substitutes the indicated
-- types for generic variables.
local function genericSubstituter(assignments)
	assertis(assignments, mapType("string", "Type+"))

	local function subs(t)
		assertis(t, choiceType("InterfaceType+", "Type+"))

		if t.tag == "interface-type" then
			return {
				tag = "interface-type",
				name = t.name,
				arguments = table.map(subs, t.arguments),
				location = t.location,
			}
		elseif t.tag == "concrete-type+" then
			return {tag = "concrete-type+",
				name = t.name,
				arguments = table.map(subs, t.arguments),
				location = t.location,
			}
		elseif t.tag == "keyword-type+" then
			return t
		elseif t.tag == "generic+" then
			if not assignments[t.name] then
				-- XXX: should this be an assert?
				Report.UNKNOWN_GENERIC_USED(t)
			end
			return assignments[t.name]
		end
		error("unknown Type+ tag `" .. t.tag .. "`")
	end
	return subs
end

--------------------------------------------------------------------------------

-- RETURNS a function Type+ -> Type+ to apply to types on the
-- class/struct/interface's definition to use the specific types
-- in this instance
local function getSubstituterFromConcreteType(type, allDefinitions)
	-- XXX: This union is not a good thing
	assertis(type, choiceType("ConcreteType+", "InterfaceType+"))
	assertis(allDefinitions, listType "Definition")

	local definition = table.findwith(allDefinitions, "name", type.name)
	assert(definition)
	assert(#definition.generics == #type.arguments)

	local assignments = {}
	for i, generic in ipairs(definition.generics) do
		assignments[generic.name] = type.arguments[i]
	end
	return genericSubstituter(assignments)
end

-- RETURNS a list of constraints (as InterfaceType+) that the given type
-- satisfies
local function getTypeConstraints(type, typeScope, allDefinitions)
	assertis(type, "Type+")
	assertis(typeScope, listType "TypeParameterIR")
	assertis(allDefinitions, listType "Definition")

	if type.tag == "concrete-type+" then
		local definition = table.findwith(allDefinitions, "name", type.name)
		assert(definition and #definition.generics == #type.arguments)

		local substitute = getSubstituterFromConcreteType(type, allDefinitions)
		local constraints = table.map(substitute, definition.implements)
		return constraints
	elseif type.tag == "keyword-type+" then
		error("TODO: getTypeConstraints(keyword-type+")
	elseif type.tag == "generic+" then
		local parameter = table.findwith(typeScope, "name", type.name)
		assert(parameter)

		return table.map(table.getter "interface", parameter.constraints)
	end
	error("unknown Type+ tag `" .. type.tag .. "`")
end

--------------------------------------------------------------------------------

-- RETURNS nothing
-- VERIFIES that the type satisfies the required constraint
local function verifyTypeSatisfiesConstraint(type, constraint, typeScope, need, allDefinitions)
	assertis(type, "Type+")
	assertis(constraint, "InterfaceType+")
	assertis(typeScope, listType "TypeParameterIR")
	assertis(need, recordType {
		container = "Definition",
		constraint = "InterfaceType+",
		nth = "integer",
	})
	assertis(allDefinitions, listType "Definition")

	for _, c in ipairs(getTypeConstraints(type, typeScope, allDefinitions)) do
		if areInterfaceTypesEqual(c, constraint) then
			return
		end
	end

	-- The type `type` does not implement the constraint `constraint`
	Report.TYPE_MUST_IMPLEMENT_CONSTRAINT {
		type = showType(type),
		constraint = showInterfaceType(constraint),
		location = type.location,
		
		nth = need.nth,
		container = need.container.name,
		cause = need.constraint.location,
	}
end

-- RETURNS nothing
-- VERIFIES that the type is entirely valid (in terms of scope, arity,
-- and constraints)
local function verifyTypeValid(type, typeScope, allDefinitions)
	assertis(type, "Type+")
	assertis(typeScope, listType "TypeParameterIR")
	assertis(allDefinitions, listType "Definition")

	if type.tag == "concrete-type+" then
		local definition = table.findwith(allDefinitions, "name", type.name)
		local substitute = getSubstituterFromConcreteType(type, allDefinitions)

		-- Check each argument
		for i, generic in ipairs(definition.generics) do
			local argument = type.arguments[i]
			assertis(argument, "Type+")

			-- Verify that the `i`th argument satisfies the constraints of
			-- the `i`th parameter
			for _, generalConstraint in ipairs(generic.constraints) do
				local instantiatedConstraint = substitute(generalConstraint.interface)

				-- TODO: better explain context
				verifyTypeSatisfiesConstraint(argument, instantiatedConstraint, typeScope, {
					container = definition,
					constraint = generalConstraint.interface,
					nth = i,
				}, allDefinitions)
			end

			-- Verify recursively
			verifyTypeValid(argument, typeScope, allDefinitions)
		end
	elseif type.tag == "keyword-type+" then
		return -- All keyword types are valid
	elseif type.tag == "generic+" then
		return -- All generic literals are valid
	else
		error("unknown Type+ tag `" .. type.tag .. "`")
	end
end

-- RETURNS nothing
local function verifyInterfaceValid(constraint, typeScope, allDefinitions)
	assertis(constraint, "InterfaceType+")
	assertis(typeScope, listType "TypeParameterIR")
	assertis(allDefinitions, listType "Definition")

	local definition = table.findwith(allDefinitions, "name", constraint.name)
	assert(definition.tag == "interface")

	local substitute = getSubstituterFromConcreteType(constraint, allDefinitions)
	
	-- Check each argument
	for i, generic in ipairs(definition.generics) do
		local argument = constraint.arguments[i]
		assertis(argument, "Type+")

		-- Verify that the i-th argument satisfies the constraints of the i-th
		-- parameter
		for _, generalConstraint in ipairs(generic.constraints) do
			local instantiatedConstraint = substitute(generalConstraint.interface)

			-- TODO: provide a clearer context for error messages
			verifyTypeSatisfiesConstraint(argument, instantiatedConstraint, typeScope, {
				container = definition,
				constraint = generalConstraint.interface,
				nth = i,
			}, allDefinitions)
		end

		-- Verify each argument in a recursive fashion
		verifyTypeValid(argument, typeScope, allDefinitions)
	end
end

--------------------------------------------------------------------------------

-- RETURNS a variable or false
local function getFromScope(scope, name)
	assertis(scope, listType(mapType("string", "object")))
	assertis(name, "string")

	for i = #scope, 1, -1 do
		if scope[i][name] then
			return scope[i][name]
		end
	end
	return nil
end

--------------------------------------------------------------------------------

local STRING_TYPE = freeze {
	tag = "keyword-type+",
	name = "String",
	location = "???",
}

local NUMBER_TYPE = freeze {
	tag = "keyword-type+",
	name = "Number",
	location = "???",
}

local BOOLEAN_TYPE = freeze {
	tag = "keyword-type+",
	name = "Boolean",
	location = "???",
}

local UNIT_TYPE = freeze {
	tag = "keyword-type+",
	name = "Unit",
	location = "???",
}

--------------------------------------------------------------------------------

-- RETURNS a Semantics, an IR description of the program
local function semanticsSmol(sources, main)
	assertis(main, "string")

	-- (1) Resolve the set of types and the set of packages that have been
	-- defined
	local isPackageDefined = {}
	local definitionSourceByFullName = {}
	for _, source in ipairs(sources) do
		local package = source.package
		assertis(package, "string")

		-- Mark this package name as defined
		-- Package names MAY be repeated between several sources
		isPackageDefined[package] = true

		-- Record the definition of all types in this package
		for _, definition in ipairs(source.definitions) do
			local fullName = package .. ":" .. definition.name

			-- Check that this type is not defined twice
			local previousDefinition = definitionSourceByFullName[fullName]
			if previousDefinition then
				Report.TYPE_DEFINED_TWICE(previousDefinition, definition)
			end

			definitionSourceByFullName[fullName] = definition
		end
	end

	-- (2) Fully qualify all local type names
	local allDefinitions = {}
	for _, source in ipairs(sources) do
		local package = source.package

		-- A bare `typename` should resolve to the type with name `typename`
		-- in package `packageScopeMap[typename].package`
		local packageScopeMap = {}
		local function defineLocalType(name, package, location)
			if packageScopeMap[name] then
				Report.TYPE_BROUGHT_INTO_SCOPE_TWICE {
					name = name,
					firstLocation = packageScopeMap[name].location,
					secondLocation = location,
				}
			end
			packageScopeMap[name] = {
				package = package,
				location = location,
			}
		end

		-- Only types in this set can be legally referred to
		local packageIsInScope = {
			[package] = true,
		}

		-- Bring each imported type/package into scope
		for _, import in ipairs(source.imports) do
			if import.class then
				-- Check that the type exists
				local importedFullName = import.package .. ":" .. import.class
				if not definitionSourceByFullName[importedFullName] then
					Report.UNKNOWN_TYPE_IMPORTED {
						location = import.location,
						name = importedFullName,
					}
				end

				defineLocalType(import.class, import.package, import.location)
			else
				-- Importing an entire package
				packageIsInScope[import.package] = true
			end
		end

		-- Bring each defined type into scope
		for _, definition in ipairs(source.definitions) do
			local location = definition.location
			defineLocalType(definition.name, source.package, location)
		end

		assertis(packageIsInScope, mapType("string", constantType(true)))

		-- RETURNS a Type+ with a fully-qualified name
		local function resolveType(t, typeScope)
			assertis(typeScope, listType(recordType {name = "string"}))

			if t.tag == "concrete-type" then
				-- Search for the type in `type`
				local package = t.package
				if not package then
					package = packageScopeMap[t.base]
					if not package then
						Report.UNKNOWN_LOCAL_TYPE_USED {
							name = t.base,
							location = t.location,
						}
					end
					package = package.package
				end
				assertis(package, "string")
				if not packageIsInScope[package] then
					Report.UNKNOWN_PACKAGE_USED {
						package = package,
						location = t.location,
					}
				end

				local fullName = package .. ":" .. t.base
				local definition = definitionSourceByFullName[fullName] 
				if not definition then
					Report.UNKNOWN_TYPE_USED {
						name = fullName,
						location = t.location,
					}
				elseif definition.tag == "interface-definition" then
					Report.INTERFACE_USED_AS_VALUE {
						interface = fullName,
						location = t.location,
					}
				end

				if #t.arguments ~= #definition.generics.parameters then
					Report.WRONG_ARITY {
						name = fullName,
						givenArity = #t.arguments,
						expectedArity = #definition.generics.parameters,
						location = t.location,
						definitionLocation = definition.location,
					}
				end

				return {
					tag = "concrete-type+",
					name = fullName,
					arguments = table.map(resolveType, t.arguments, typeScope),
					location = t.location,
				}
			elseif t.tag == "generic" then
				-- Search for the name in `typeScope`
				if not table.findwith(typeScope, "name", t.name) then
					Report.UNKNOWN_GENERIC_USED(t)
				end

				return {
					tag = "generic+",
					name = t.name,
					location = t.location,
				}
			elseif t.tag == "type-keyword" then
				return {
					tag = "keyword-type+",
					name = t.name,
					location = t.location,
				}
			end
			error("unhandled ast type tag `" .. t.tag .. "`")
		end

		-- RETURNS an InterfaceType+ (with a fully qualified name)
		local function resolveInterface(t, typeScope)
			assertis(t, recordType {
				tag = constantType "concrete-type",
				arguments = "object",
				location = "string",
				base = "string",
			})
			assertis(typeScope, listType(recordType {name = "string"}))

			-- Get the appropriate package for this type
			local package = t.package
			if not package then
				package = packageScopeMap[t.base]
				if not package then
					Report.UNKNOWN_LOCAL_TYPE_USED {
						name = t.base,
						location = t.location,
					}
				end
				package = package.package
			end
			assertis(package, "string")
			if not packageIsInScope[package] then
				Report.UNKNOWN_PACKAGE_USED {
					package = package,
					location = t.location,
				}
			end

			local fullName = package .. ":" .. t.base
			local definition = definitionSourceByFullName[fullName] 
			if not definition then
				Report.UNKNOWN_TYPE_USED {
					name = fullName,
					location = t.location,
				}
			elseif definition.tag ~= "interface-definition" then
				Report.CONSTRAINTS_MUST_BE_INTERFACES {
					is = definition.tag,
					typeShown = fullName,
					location = t.location,
				}
			end

			-- Check arity
			if #t.arguments ~= #definition.generics.parameters then
				Report.WRONG_ARITY {
					name = definition.name,
					givenArity = #t.arguments,
					expectedArity = #definition.generics,
					location = t.location,
					definitionLocation = definition.location,
				}
			end

			return {
				tag = "interface-type",
				name = fullName,
				arguments = table.map(resolveType, t.arguments, typeScope),
				location = t.location,
			}
		end

		-- RETURNS a signature
		local function compiledSignature(signature, scope, foreign)
			assertis(scope, listType("TypeParameterIR"))
			assertis(foreign, "boolean")

			return freeze {
				foreign = foreign,
				modifier = signature.modifier.keyword,
				name = signature.name,
				returnTypes = table.map(resolveType, signature.returnTypes, scope),
				parameters = table.map(function(p)
					return {
						name = p.name,
						type = resolveType(p.type, scope),
						location = p.location,
					}
				end, signature.parameters),
				location = signature.location,
				bang = signature.bang,
			}
		end

		-- RETURNS a [TypeParameterIR]
		local function compiledGenerics(generics)
			local parametersOut = {}
			local map = {}
			for _, parameterAST in ipairs(generics.parameters) do
				local parameter = {
					name = parameterAST,
					constraints = {},
				}
				table.insert(parametersOut, parameter)

				-- Check for duplicates
				if map[parameter.name] then
					Report.GENERIC_DEFINED_TWICE {
						name = parameter.name,
						firstLocation = generics.location,
						secondLocation = generics.location,
					}
				end
				map[parameter.name] = parameter
			end

			-- Create a type-scope
			local typeScope = table.map(
				function(x) return {name = x} end,
				generics.parameters)
			
			-- Associate each constraint with a generic parameter
			for _, constraintAST in ipairs(generics.constraints) do
				local constraint = resolveInterface(constraintAST.constraint, typeScope)

				-- Check that the named parameter exists
				local parameter = map[constraintAST.parameter]
				if not parameter then
					Report.UNKNOWN_GENERIC_USED(constraintAST.parameter)
				end

				-- Add this constraint to the associated generic parameter
				table.insert(parameter.constraints, {
					interface = constraint,
					location = constraintAST.location,
				})
			end

			return parametersOut
		end

		-- RETURNS a class+/union+
		local function compiledStruct(definition, tag)
			assertis(tag, "string")

			-- name, fields, generics, implements, signatures

			-- Create the full-name of the package
			local structName = package .. ":" .. definition.name

			-- Compile the set of generics introduced by this class
			local generics = compiledGenerics(definition.generics)

			local memberLocationMap = {}

			-- Compile the set of fields this class has
			local fields = {}
			for _, field in ipairs(definition.fields) do
				-- Check for duplicate members
				if memberLocationMap[field.name] then
					Report.MEMBER_DEFINED_TWICE {
						name = field.name,
						firstLocation = memberLocationMap[field.name],
						secondLocation = field.location,
					}
				end
				memberLocationMap[field.name] = field.location

				table.insert(fields, {
					name = field.name,
					type = resolveType(field.type, generics),
					location = field.location,
				})
			end

			-- Collect the list of methods/statics this class provides
			local signatures = {}
			for _, method in ipairs(definition.methods) do
				-- Check for duplicate members
				local name = method.signature.name
				if memberLocationMap[name] then
					Report.MEMBER_DEFINED_TWICE {
						name = name,
						firstLocation = memberLocationMap[name],
						secondLocation = method.location,
					}
				end
				memberLocationMap[name] = method.location
				
				local signature = compiledSignature(method.signature, generics, method.foreign)
				signature = table.with(signature, "body", method.body)
				signature = table.with(signature, "resolveType", resolveType)
				signature = table.with(signature, "resolveInterface", resolveInterface)
				signature = table.with(signature, "container", structName)
				table.insert(signatures, signature)
			end

			-- Compile the set of interfaces this class claims to implement
			local implements = table.map(resolveInterface, definition.implements, generics)

			-- Create a set of constraints
			local constraints = {}
			for gi, generic in ipairs(generics) do
				for ci, constraint in ipairs(generic.constraints) do
					constraints["#" .. gi .. "_" .. ci] = constraint.interface
				end
			end

			return freeze {
				tag = tag,
				name = structName,
				generics = generics,
				fields = fields,
				signatures = signatures,
				implements = implements,
				constraints = constraints,
				location = definition.location,
			}
		end

		local function compiledInterface(definition)
			-- Create the fully qualified name
			local name = package .. ":" .. definition.name

			-- Create the generics
			local generics = compiledGenerics(definition.generics)

			local signatures = table.map(function(raw)
					local compiled = compiledSignature(raw, generics, false)
					return table.with(compiled, "container", name)
				end, definition.signatures)

			return freeze {
				tag = "interface",
				name = name,
				generics = generics,
				signatures = signatures,
				location = definition.location,
			}
		end

		-- Create an IR representation of each definition
		for _, definition in ipairs(source.definitions) do
			if definition.tag == "class-definition" then
				local compiled = compiledStruct(definition, "class")
				assertis(compiled, "ClassIR")

				table.insert(allDefinitions, compiled)
			elseif definition.tag == "interface-definition" then
				local compiled = compiledInterface(definition)
				assertis(compiled, "InterfaceIR")

				table.insert(allDefinitions, compiled)
			elseif definition.tag == "union-definition" then
				local compiled = compiledStruct(definition, "union")
				assertis(compiled, "UnionIR")

				table.insert(allDefinitions, compiled)
			else
				error("unknown definition tag `" .. definition.tag .. "`")
			end
		end
	end

	assertis(allDefinitions, listType "Definition")

	-- (3) Verify and record all interfaces implementation

	-- Verify that `class` actually implements each interface that it claims to
	-- RETURNS nothing
	local function checkStructImplementsClaims(class)
		for _, int in ipairs(class.implements) do
			local interfaceName = int.name
			local interface = table.findwith(allDefinitions, "name", interfaceName)
			assert(interface and interface.tag == "interface")
			assert(#int.arguments == #interface.generics)

			-- Instantiate each of the interface's type parameters with the
			-- argument specified in the "implements"
			local subs = getSubstituterFromConcreteType(int, allDefinitions)

			-- Check that each signature matches
			for _, iSignature in ipairs(interface.signatures) do
				-- Search for a method/static with the same name, if any
				local cSignature = table.findwith(
					class.signatures, "name", iSignature.name)
				if not cSignature then
					Report.INTERFACE_REQUIRES_MEMBER {
						class = class.name,
						interface = showType(int),
						implementsLocation = int.location,
						memberLocation = iSignature.location,
						memberName = iSignature.name,
					}
				end

				-- Check that the modifier matches
				if cSignature.modifier ~= iSignature.modifier then
					Report.INTERFACE_REQUIRES_MODIFIER {
						name = cSignature.name,
						class = class.name,
						interface = showType(int),
						classModifier = cSignature.modifier,
						interfaceModifier = iSignature.modifier,
						classLocation = cSignature.location,
						interfaceLocation = iSignature.location,
					}
				end

				-- Check that the parameters match
				if #cSignature.parameters ~= #iSignature.parameters then
					Report.INTERFACE_PARAMETER_COUNT_MISMATCH {
						class = class.name,
						classLocation = cSignature.location,
						classCount = #cSignature.parameters,
						interface = showType(int),
						interfaceLocation = iSignature.location,
						interfaceCount = #iSignature.parameters,
					}
				end

				for k, iParameter in ipairs(iSignature.parameters) do
					local iType = subs(iParameter.type)
					local cParameter = cSignature.parameters[k]
					local cType = cParameter.type
					if not areTypesEqual(iType, cType) then
						Report.INTERFACE_PARAMETER_TYPE_MISMATCH {
							class = class.name,
							classLocation = cParameter.location,
							classType = showType(cType),
							interface = showType(int),
							interfaceLocation = iParameter.location,
							interfaceType = showType(iType),
							index = k,
						}
					end
				end

				-- Check that the return types match
				if #cSignature.returnTypes ~= #iSignature.returnTypes then
					Report.INTERFACE_RETURN_COUNT_MISMATCH {
						class = class.name,
						interface = showType(int),
						classLocation = cSignature.location,
						interfaceLocation = iSignature.location,
						classCount = #cSignature.returnTypes,
						interfaceCount = #iSignature.returnTypes,
						member = cSignature.name,
					}
				end

				for k, cType in ipairs(cSignature.returnTypes) do
					local iType = subs(iSignature.returnTypes[k])
					if not areTypesEqual(iType, cType) then
						Report.INTERFACE_RETURN_TYPE_MISMATCH {
							class = class.name,
							interface = showInterfaceType(int),
							classLocation = cType.location,
							interfaceLocation = iType.location,
							classType = showType(cType),
							interfaceType = showType(iType),
							index = k,
							member = cSignature.name,
						}
					end
				end
			end
		end
	end

	-- Verify all implementation claims
	for _, class in ipairs(allDefinitions) do
		if class.tag == "class" or class.tag == "union" then
			checkStructImplementsClaims(class)
		end
	end

	-- (4) Verify all existing Type+'s (from headers) are OKAY
	for _, definition in ipairs(allDefinitions) do
		assertis(definition, "Definition")

		-- Verify that the generic constraints are valid
		for _, parameter in ipairs(definition.generics) do
			for _, constraint in ipairs(parameter.constraints) do
				verifyInterfaceValid(constraint.interface, definition.generics, allDefinitions)
			end
		end

		if definition.tag == "class" then
			-- Verify each field
			for _, field in ipairs(definition.fields) do
				verifyTypeValid(field.type, definition.generics, allDefinitions)
			end

			-- Verify each implements
			for _, implements in ipairs(definition.implements) do
				verifyInterfaceValid(implements, definition.generics, allDefinitions)
			end

			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyTypeValid(parameter.type, definition.generics, allDefinitions)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyTypeValid(returnType, definition.generics, allDefinitions)
				end

				-- Verify the signature's body later
			end
		elseif definition.tag == "union" then
			-- Verify each field
			for _, field in ipairs(definition.fields) do
				verifyTypeValid(field.type, definition.generics, allDefinitions)
			end

			-- Verify each implements
			for _, implements in ipairs(definition.implements) do
				verifyTypeValid(implements, definition.generics, allDefinitions)
			end

			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyTypeValid(parameter.type, definition.generics, allDefinitions)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyTypeValid(returnType, definition.generics, allDefinitions)
				end
			end
		elseif definition.tag == "interface" then
			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyTypeValid(parameter.type, definition.generics, allDefinitions)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyTypeValid(returnType, definition.generics, allDefinitions)
				end
			end
		else
			error("unknown Definition tag `" .. definition.tag .. "`")
		end
	end

	-- (5) Compile all code bodies

	-- RETURNS a Definition
	local function definitionFromType(t)
		assertis(t, choiceType("ConcreteType+", "KeywordType+"))

		local definition = table.findwith(allDefinitions, "name", t.name)
		
		-- Type Finder should verify that the type exists
		assert(definition, "definition must exist")

		return definition
	end

	-- RETURNS a Definition
	local function interfaceDefinitionFromConstraint(t)
		assertis(t, "InterfaceType+")

		local definition = table.findwith(allDefinitions, "name", t.name)
		assert(definition and definition.tag == "interface")

		return definition
	end

	-- RETURNS a FunctionIR
	local function compileFunctionFromStruct(definition, containingSignature)
		assertis(definition, choiceType("ClassIR", "UnionIR"))
		assertis(containingSignature, "Signature")

		local containerType = freeze {
			tag = "concrete-type+",
			name = definition.name,
			arguments = table.map(function(p)
				return freeze {
					tag = "generic+",
					name = p.name,
					location = definition.location,
				}
			end, definition.generics),
			location = definition.location,
		}

		local thisVariable = nil
		if containingSignature.modifier == "method" then
			thisVariable = {
				name = "this",
				type = containerType,
				location = containingSignature.location,
			}
		end
		assertis(thisVariable, nullableType "VariableIR")

		-- RETURNS a (verified) Type+
		local function resolveType(parsedType)
			local typeScope = definition.generics
			local outType = containingSignature.resolveType(parsedType, typeScope)
			verifyTypeValid(outType, definition.generics, allDefinitions)
			return outType
		end

		-- RETURNS a (verified) InterfaceType+
		local function resolveInterface(parsedInterface)
			local typeScope = definition.generics
			local outType = containingSignature.resolveInterface(parsedInterface, typeScope)
			verifyTypeValid(outType, definition.generics, allDefinitions)
			return outType
		end

		-- RETURNS a ConstraintIR
		local function constraintFromStruct(interface, implementer)
			assertis(interface, "InterfaceType+")
			assertis(implementer, "Type+")

			if implementer.tag == "concrete-type+" then
				local assignments = {}
				if #implementer.arguments > 0 then
					-- Fill assignments
					error "TODO"
				end
				return freeze {
					tag = "concrete-constraint",
					interface = interface,
					concrete = implementer,
					assignments = assignments,
				}
			elseif implementer.tag == "generic+" then
				local name
				for i, generic in ipairs(definition.generics) do
					for j, c in ipairs(generic.constraints) do
						if generic.name == implementer.name and c.interface.name == interface.name then
							name = "#" .. i .. "_" .. j
						end
					end
				end
				assert(name)
				if containingSignature.modifier == "static" then
					-- Get a parameter constraint
					return freeze {
						tag = "parameter-constraint",
						interface = interface,
						name = name,
					}
				else
					-- Get a this constraint
					assert(thisVariable)
					return freeze {
						tag = "this-constraint",
						instance = thisVariable,
						interface = interface,
						name = name,
					}
				end
			end
			print(show(interface))
			print(show(implementer))
			print(string.rep(".", 80))
			error("unhandled tag: " .. show(implementer))
		end

		-- RETURNS TODO
		local function findConstraintByMember(genericType, modifier, name, location)
			assertis(genericType, "GenericType+")
			assertis(modifier, choiceType(constantType "static", constantType "method"))
			assertis(name, "string")
			assertis(location, "string")
			assert(name:sub(1, 1):lower() == name:sub(1, 1))

			local parameter, pi = table.findwith(definition.generics, "name", genericType.name)
			assert(parameter)

			local matches = {}
			for ci, constraint in ipairs(parameter.constraints) do
				local interface = interfaceDefinitionFromConstraint(constraint.interface)
				local signature = table.findwith(interface.signatures, "name", name)
				if signature then
					local constraintIR = {
						tag = "parameter-constraint",
						name = "#" .. pi .. "_" .. ci,
						location = constraint.location,
						interface = constraint.interface,
					}
					if containingSignature.modifier == "method" then
						constraintIR = {
							tag = "this-constraint",
							instance = thisVariable,
							name = "#" .. pi .. "_" .. ci,
							interface = constraint.interface,
						}
					end

					table.insert(matches, freeze {
						signature = signature,
						interface = interface,
						constraint = constraint.interface,
						constraintIR = constraintIR,
					})
				end
			end

			-- Verify exactly one constraint supplies this method name
			if #matches == 0 then
				Report.NO_SUCH_METHOD {
					modifier = modifier,
					type = showType(genericType),
					name = name,
					definitionLocation = parameter.location,
					location = location,
				}
			elseif #matches > 1 then
				Report.CONFLICTING_INTERFACES {
					method = name,
					interfaceOne = showType(matches[1].interface),
					interfaceTwo = showType(matches[2].interface),
					location = location,
				}
			end

			-- Verify the method's modifier matches
			local method = matches[1]
			if method.signature.modifier ~= modifier then
				Report.WRONG_MODIFIER {
					signatureModifier = method.signature.modifier,
					signatureLocation = method.signature.location,
					callModifier = modifier,
					location = location,
				}
			end

			local methodFullName = method.interface.name .. "." .. method.signature.name
			local out = table.with(method, "fullName", methodFullName)
			assertis(out, recordType {
				interface = "InterfaceIR",
				signature = "Signature",
				constraint = "InterfaceType+",
				constraintIR = "ConstraintIR",
				fullName = "string",
			})
			return out
		end

		-- RETURNS StatementIR, [Variable]
		local function compileExpression(pExpression, scope)
			assertis(pExpression, recordType {
				tag = "string"
			})
			assertis(scope, listType(mapType("string", "VariableIR")))

			if pExpression.tag == "string-literal" then
				local out = {
					name = generateLocalID("stringliteral"),
					type = STRING_TYPE,
					location = pExpression.location,
				}

				local block = buildBlock {
					localSt(out),
					{
						tag = "string",
						string = pExpression.value,
						destination = out,
						returns = "no",
					},
				}
				return block, freeze {out}
			elseif pExpression.tag == "number-literal" then
				local out = {
					name = generateLocalID("numberliteral"),
					type = NUMBER_TYPE,
					location = pExpression.location,
				}

				local block = buildBlock {
					localSt(out),
					{
						tag = "number",
						number = pExpression.value,
						destination = out,
						returns = "no",
					}
				}
				return block, freeze {out}
			elseif pExpression.tag == "new-expression" then
				local out = {
					name = generateLocalID("new"),
					type = containerType,
					location = pExpression.location .. ">"
				}
				assertis(out.type, "ConcreteType+")

				if containingSignature.modifier ~= "static" then
					Report.NEW_USED_OUTSIDE_STATIC {
						location = pExpression.location,
					}
				end

				local newTag
				if definition.tag == "union" then
					newTag = "new-union"
				elseif definition.tag == "class" then
					newTag = "new-class"
				end

				local newSt = {
					tag = newTag,
					type = containerType,
					returns = "no",
					constraints = {},
					destination = out,
				}

				-- All of the constraints are provided as arguments to this
				-- static function
				for constraintName, interface in pairs(definition.constraints) do
					newSt.constraints[constraintName] = freeze {
						tag = "parameter-constraint",
						name = constraintName,
						location = pExpression.location,
						interface = interface,
					}
				end

				local evaluation = {}

				-- Map is a map from field name to value variable
				local map = {}

				-- Evaluate all arguments to new
				for _, argument in ipairs(pExpression.arguments) do
					local subEvaluation, subOut = compileExpression(argument.value, scope)
					if #subOut ~= 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "field value",
							expectedCount = 1,
							givenCount = #subOut,
							location = argument.location,
						}
					end
					
					table.insert(evaluation, subEvaluation)
					assertis(evaluation, listType "StatementIR")

					local field = table.findwith(definition.fields, "name", argument.name)
					if not field then
						Report.NO_SUCH_FIELD {
							name = argument.name,
							container = showType(containerType),
							location = argument.location,
						}
					end

					if not areTypesEqual(field.type, subOut[1].type) then
						Report.TYPES_DONT_MATCH {
							purpose = "field type",
							expectedType = showType(field.type),
							expectedLocation = field.location,
							givenType = showType(subOut[1].type),
							location = argument.location,
						}
					end

					map[argument.name] = subOut[1]
				end

				-- Record the map as fields
				if definition.tag == "union" then
					newSt.field, newSt.value = next(map)

					-- Verify that exactly one field is given for union new
					if #pExpression.arguments ~= 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "new union field list",
							expectedCount = 1,
							givenCount = #pExpression.arguments,
							location = pExpression.location,
						}
					end
				elseif definition.tag == "class" then
					newSt.fields = map

					-- Check that no fields are missing for class new
					for _, field in ipairs(definition.fields) do
						if not newSt.fields[field.name] then
							Report.MISSING_VALUE {
								purpose = "new " .. showType(containerType) .. " expression",
								name = field.name,
								location = pExpression.location,
							}
						end
					end
				end


				local block = buildBlock(table.concatted(
					evaluation, {localSt(out), newSt}
				))
				return block, freeze {out}
			elseif pExpression.tag == "identifier" then
				local block = buildBlock({})
				local out = nil
				for i = #scope, 1, -1 do
					out = out or scope[i][pExpression.name]
				end
				if not out then
					Report.NO_SUCH_VARIABLE {
						name = pExpression.name,
						location = pExpression.location,
					}
				end
				return block, freeze {out}
			elseif pExpression.tag == "static-call" then
				local t = resolveType(pExpression.baseType)

				-- Evaluate the arguments
				local evaluation = {}
				local argumentSources = {}
				for _, argument in ipairs(pExpression.arguments) do
					local subEvaluation, outs = compileExpression(
						argument, scope
					)

					-- Verify each argument has exactly one value
					if #outs ~= 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "static argument",
							expectedCount = 1,
							givenCount = #outs,
							location = argument.location,
						}
					end

					table.insert(argumentSources, outs[1])
					table.insert(evaluation, subEvaluation)
				end

				if t.tag == "generic+" then
					-- Generic static function
					local static = findConstraintByMember(t, "static", pExpression.funcName, t.location)
					assert(static and static.signature.modifier == "static")
					assertis(static.constraint, "InterfaceType+")

					-- Map type variables to the type-values used for this instantiation
					local substituter = getSubstituterFromConcreteType(static.constraint, allDefinitions)

					-- Check the number of parameters
					if #static.signature.parameters ~= #pExpression.arguments then
						Report.WRONG_VALUE_COUNT {
							purpose = "static function `" .. static.fullName .. "`",
							expectedCount = #static.signature.parameters,
							givenCount = #pExpression.arguments,
							location = pExpression.location,
						}
					end

					-- Verify the argument types match the parameter types
					for i, argument in ipairs(argumentSources) do
						local parameterType = substituter(static.signature.parameters[i].type)
						if not areTypesEqual(argument.type, parameterType) then
							Report.TYPES_DONT_MATCH {
								purpose = string.ordinal(i) .. " argument to " .. fullName,
								expectedLocation = static.signature.parameters[i].location,
								givenType = showType(argument.type),
								location = argument.location,
								expectedType = showType(parameterType)
							}
						end
					end

					-- Create variables for the output
					local destinations = {}
					for _, returnType in pairs(static.signature.returnTypes) do
						local returnVariable = {
							name = generateLocalID("return"),
							type = substituter(returnType),
							location = pExpression.location,
						}
						table.insert(destinations, returnVariable)
						table.insert(evaluation, localSt(returnVariable))
					end

					-- Verify the bang matches
					if not static.signature.bang ~= not pExpression.bang then
						Report.BANG_MISMATCH {
							modifier = static.signature.modifier,
							fullName = fullName,
							expected = static.signature.bang,
							given = pExpression.bang,
							signatureLocation = static.signature.location,
							location = pExpression.location,
						}
					elseif static.signature.bang and not containingSignature.bang then
						local fullName = definition.name .. "." .. containingSignature.name
						Report.BANG_NOT_ALLOWED {
							context = containingSignature.modifier .. " " .. fullName,
							location = pExpression.location,
						}
					end

					local callSt = {
						tag = "generic-static-call",
						constraint = static.constraintIR,
						staticName = pExpression.funcName,
						arguments = argumentSources,
						destinations = destinations,
						returns = "no",
					}
					assertis(callSt, "StatementIR")
					table.insert(evaluation, callSt)

					return buildBlock(evaluation), destinations
				end

				local baseDefinition = definitionFromType(t)

				local fullName = showType(t) .. "." .. pExpression.funcName

				-- Map type variables to the type-values used for this instantiation
				local substituter = getSubstituterFromConcreteType(t, allDefinitions)

				local method = table.findwith(baseDefinition.signatures,
					"name", pExpression.funcName)
				
				if not method or method.modifier ~= "static" then
					Report.NO_SUCH_METHOD {
						modifier = "static",
						type = showType(t),
						name = pExpression.funcName,
						definitionLocation = baseDefinition.location,
						location = pExpression.location,
					}
				end

				-- Check the number of parameters
				if #method.parameters ~= #pExpression.arguments then
					Report.WRONG_VALUE_COUNT {
						purpose = "static function `" .. fullName .. "`",
						expectedCount = #method.parameters,
						givenCount = #pExpression.arguments,
						location = pExpression.location,
					}
				end

				-- Verify the argument types match the parameter types
				for i, argument in ipairs(argumentSources) do
					local parameterType = substituter(method.parameters[i].type)
					if not areTypesEqual(argument.type, parameterType) then
						Report.TYPES_DONT_MATCH {
							purpose = string.ordinal(i) .. " argument to " .. fullName,
							expectedLocation = method.parameters[i].location,
							givenType = showType(argument.type),
							location = argument.location,
							expectedType = showType(parameterType)
						}
					end
				end

				-- Collect the constraints
				local constraints = {}
				for gi, generic in ipairs(baseDefinition.generics) do
					for ci, constraint in ipairs(generic.constraints) do
						local key = "#" .. gi .. "_" .. ci
						constraints[key] = constraintFromStruct(constraint.interface, t.arguments[gi])
					end
				end

				-- Verify the bang matches
				if not method.bang ~= not pExpression.bang then
					Report.BANG_MISMATCH {
						modifier = method.modifier,
						fullName = fullName,
						expected = method.bang,
						given = pExpression.bang,
						signatureLocation = method.location,
						location = pExpression.location,
					}
				elseif method.bang and not containingSignature.bang then
					local fullName = definition.name .. "." .. containingSignature.name
					Report.BANG_NOT_ALLOWED {
						context = containingSignature.modifier .. " " .. fullName,
						location = pExpression.location,
					}
				end

				-- Create variables for the output
				local outs = {}
				for _, returnType in pairs(method.returnTypes) do
					local returnVariable = {
						name = generateLocalID("return"),
						type = substituter(returnType),
						location = pExpression.location,
					}
					table.insert(outs, returnVariable)
					table.insert(evaluation, localSt(returnVariable))
				end

				local call = {
					tag = "static-call",
					baseType = t,
					name = method.name,
					arguments = argumentSources,
					constraints = constraints,
					destinations = outs,
					returns = "no",
				}
				assertis(call, "StaticCallSt")
				table.insert(evaluation, call)
				
				return buildBlock(evaluation), freeze(outs)
			elseif pExpression.tag == "method-call" then
				-- Compile the base instance
				local baseEvaluation, baseInstanceValues =
					compileExpression(pExpression.base, scope)
				if #baseInstanceValues ~= 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "method base expression",
						expectedCount = 1,
						givenCount = #baseInstanceValues,
						location = pExpression.location,
					}
				end
				local evaluation = {baseEvaluation}
				local baseInstance = baseInstanceValues[1]

				-- Evaluate the arguments
				local arguments = {}
				for i, pArgument in ipairs(pExpression.arguments) do
					local subEvaluation, outs = compileExpression(pArgument, scope)
					
					-- Verify each argument has exactly one value
					if #outs ~= 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "method argument",
							expectedCount = 1,
							givenCount = #outs,
							location = pArgument.location,
						}
					end

					table.insert(arguments, table.with(outs[1], "location", pArgument.location))
					table.insert(evaluation, subEvaluation)
				end
				assertis(evaluation, listType "StatementIR")
				assertis(arguments, listType "VariableIR")

				if baseInstance.type.tag == "generic+" then
					-- Generic instance
					local method = findConstraintByMember(
						baseInstance.type,
						"method",
						pExpression.methodName,
						pExpression.location
					)

					local substituter = getSubstituterFromConcreteType(method.constraint, allDefinitions)
					assertis(substituter, "function")

					local methodFullName = method.fullName

					-- Verify the correct number of arguments is provided
					if #arguments ~= #method.signature.parameters then
						Report.WRONG_VALUE_COUNT {
							purpose = "interface method " .. methodFullName,
							expectedCount = #method.signature.parameters,
							givenCount = #arguments,
							location = pExpression.location,
						}
					end

					-- Verify the types of the arguments match the parameters
					for i, argument in ipairs(arguments) do
						local expectedType = substituter(method.parameters[i].type)
						if not areTypesEqual(argument.type, expectedType) then
							Report.TYPES_DONT_MATCH {
								purpose = string.ordinal(i) .. " argument to `" .. methodFullName .. "`",
								expectedType =	showType(expectedType),
								expectedLocation = method.parameters[i].location,
								givenType = showType(argument.type),
								location = argument.location,
							}
						end
					end

					-- Verify the bang matches
					if not method.signature.bang ~= not pExpression.bang then
						Report.BANG_MISMATCH {
							modifier = method.signature.modifier,
							fullName = methodFullName,
							expected = method.signature.bang,
							given = pExpression.bang,
							signatureLocation = method.signature.location,
							location = pExpression.location,
						}
					end

					-- Create destinations for each return value
					local destinations = {}
					for _, returnType in ipairs(method.signature.returnTypes) do
						local destination = {
							name = generateLocalID("return"),
							type = substituter(returnType),
							location = pExpression.location,
						}
						table.insert(destinations, destination)
						table.insert(evaluation, localSt(destination))
					end

					local callSt = {
						tag = "generic-method-call",
						baseInstance = baseInstance,
						constraint = method.constraintIR,
						methodName = pExpression.methodName,
						arguments = arguments,
						destinations = destinations,
						returns = "no",
					}
					assertis(callSt, "StatementIR")
					table.insert(evaluation, callSt)

					return buildBlock(evaluation), destinations
				end

				-- Concrete instance
				local baseDefinition = definitionFromType(baseInstance.type)
				local substituter = getSubstituterFromConcreteType(baseInstance.type, allDefinitions)
				
				-- Find the definition of the method being invoked
				local method = table.findwith(baseDefinition.signatures, "name", pExpression.methodName)
				assertis(method, "Signature")

				local methodFullName = baseDefinition.name .. "." .. pExpression.methodName
				if not method or method.modifier ~= "method" then
					Report.NO_SUCH_METHOD {
						modifier = "method",
						type = showType(baseInstance.type),
						name = pExpression.name,
						definitionLocation = baseDefinition.location,
						location = pExpression.location,
					}
				end

				-- Verify the correct number of arguments is provided
				if #arguments ~= #method.parameters then
					Report.WRONG_VALUE_COUNT {
						purpose = "interface method " .. methodFullName,
						expectedCount = #method.parameters,
						givenCount = #arguments,
						location = pExpression.location,
					}
				end

				-- Verify the types of the arguments match the parameters
				for i, argument in ipairs(arguments) do
					if not areTypesEqual(argument.type, substituter(method.parameters[i].type)) then
						Report.TYPES_DONT_MATCH {
							purpose = string.ordinal(i) .. " argument to `" .. methodFullName .. "`",
							expectedType =	showType(method.parameters[i].type),
							expectedLocation = method.parameters[i].location,
							givenType = showType(argument.type),
							location = argument.location,
						}
					end
				end

				-- Verify the bang matches
				assertis(method, "Signature")
				if not method.bang ~= not pExpression.bang then
					Report.BANG_MISMATCH {
						modifier = method.modifier,
						fullName = methodFullName,
						expected = method.bang,
						given = pExpression.bang,
						signatureLocation = method.location,
						location = pExpression.location,
					}
				elseif method.bang and not containingSignature.bang then
					Report.BANG_NOT_ALLOWED {
						context = containingSignature.modifier .. " " .. definition.name .. "." .. containingSignature.name,
						location = pExpression.location,
					}
				end

				-- Create destinations for each return value
				local destinations = {}
				for _, returnType in ipairs(method.returnTypes) do
					local destination = {
						name = generateLocalID("return"),
						type = substituter(returnType),
						location = pExpression.location,
					}
					table.insert(destinations, destination)
					table.insert(evaluation, localSt(destination))
				end

				table.insert(evaluation, {
					tag = "method-call",
					baseInstance = baseInstance,
					methodName = method.name,
					arguments = arguments,
					destinations = destinations,
					returns = "no"
				})

				return buildBlock(evaluation), destinations
			elseif pExpression.tag == "keyword" then
				if pExpression.keyword == "false" or pExpression.keyword == "true" then
					local boolean = {
						type = BOOLEAN_TYPE,
						name = generateLocalID("booleanliteral"),
						location = pExpression.location,
					}
					local execution = {
						localSt(boolean),
						{
							tag = "boolean",
							boolean = pExpression.keyword == "true",
							destination = boolean,
							returns = "no",
						},
					}
					return buildBlock(execution), {boolean}
				elseif pExpression.keyword == "this" then
					local variable = {
						type = containerType,
						name = generateLocalID("this"),
						location = pExpression.location,
					}
					local execution = {
						localSt(variable),
						{
							tag = "this",
							destination = variable,
							returns = "no",
						},
					}
					return buildBlock(execution), {variable}
				elseif pExpression.keyword == "unit" then
					local variable = {
						type = UNIT_TYPE,
						name = generateLocalID("unit"),
						location = pExpression.location,
					}
					local execution = {
						localSt(variable),
						{
							tag = "unit",
							destination = variable,
							returns = "no",
						}
					}
					return buildBlock(execution), {variable}
				end
				error("TODO: keyword `" .. pExpression.keyword .. "`")
			elseif pExpression.tag == "field" then
				local baseEvaluation, bases = compileExpression(pExpression.base, scope)
				if #bases ~= 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "base of a `." .. pExpression.field .. "` field access",
						givenCount = #bases,
						expectedCount = 1,
						location = pExpression.location,
					}
				end

				local base = bases[1]
				if base.type.tag ~= "concrete-type+" then
					Report.TYPE_MUST_BE_CLASS {
						givenType = showType(base.type),
						location = pExpression.location,
					}
				end

				local definition = definitionFromType(base.type)
				if definition.tag ~= "class" then
					Report.TYPE_MUST_BE_CLASS {
						givenType = showType(base.type),
						location = pExpression.location,
					}
				end

				local field = table.findwith(definition.fields, "name", pExpression.field)
				if not field then
					Report.NO_SUCH_FIELD {
						container = showType(base.type),
						name = pExpression.field,
						location = pExpression.location,
					}
				end

				-- TODO: verify that access is to the current class

				local result = {
					type = field.type,
					name = generateLocalID("field"),
					location = pExpression.location,
				}
				local accessStatement = {
					tag = "field",
					name = pExpression.field,
					base = base,
					destination = result,
					returns = "no",
				}
				return buildBlock {baseEvaluation, localSt(result), accessStatement}, {result}
			end

			error("TODO expression: " .. show(pExpression))
		end

		local compileBlock

		-- RETURNS a StatementIR
		local function compileStatement(pStatement, scope)
			assertis(scope, listType(mapType("string", "VariableIR")))

			if pStatement.tag == "var-statement" then
				-- Allocate space for each variable on the left hand side
				local declarations = {}
				for _, pVariable in ipairs(pStatement.variables) do
					-- Verify that the variable name is not in scope
					local previous = getFromScope(scope, pVariable.name)
					if previous then
						Report.VARIABLE_DEFINED_TWICE {
							first = previous.location,
							second = pVariable.location,
							name = pVariable.name,
						}
					end

					-- Add the variable to the current scope
					local variable = {
						name = pVariable.name,
						type = resolveType(pVariable.type),
						location = pVariable.location,
					}
					
					scope[#scope][variable.name] = variable
					table.insert(declarations, {
						tag = "local",
						variable = variable,
						returns = "no",
					})
				end

				-- Evaluate the right hand side
				local evaluation, values =
					compileExpression(pStatement.value, scope) 

				-- Check the return types match the value types
				if #values ~= #declarations then
					Report.VARIABLE_DEFINITION_COUNT_MISMATCH {
						location = pStatement.location,
						expressionLocation = pStatement.value.location,
						variableCount = #declarations,
						valueCount = #values,
					}
				end

				-- Move the evaluations into the destinations
				local moves = {}
				for i, declaration in ipairs(declarations) do
					local variable = declaration.variable
					if not areTypesEqual(variable.type, values[i].type) then
						Report.TYPES_DONT_MATCH {
							purpose = "variable `" .. variable.name .. "`",
							expectedType = showType(variable.type),
							expectedLocation = variable.location,
							givenType = showType(values[i].type),
							location = pStatement.value.location,
						}
					end

					table.insert(moves, {
						tag = "assign",
						source = values[i],
						destination = variable,
						returns = "no",
					})
				end

				assertis(declarations, listType "StatementIR")
				assertis(evaluation, "StatementIR")
				assertis(moves, listType "StatementIR")
				
				-- Combine the three steps into a single sequence statement
				local sequence = table.concatted(
					declarations, {evaluation}, moves
				)
				return buildBlock(sequence)
			elseif pStatement.tag == "return-statement" then
				local sources = {}
				local evaluation = {}
				if #pStatement.values == 1 then
					-- A single value must have exactly the target multiplicity
					local subEvaluation, subsources = compileExpression(
						pStatement.values[1], scope)
					
					if #subsources ~= #containingSignature.returnTypes then
						Report.RETURN_COUNT_MISMATCH {
							signatureCount = #containingSignature.returnTypes,
							returnCount = #subsources,
							location = pStatement.location,
						}
					end

					table.insert(evaluation, subEvaluation)
					sources = subsources
				else
					-- If multiple values are given, each must be a 1-tuple
					for _, value in ipairs(pStatement.values) do
						local subevaluation, subsources = compileExpression(value, scope)
						if #subsources ~= 1 then
							Report.WRONG_VALUE_COUNT {
								purpose = "value in multiple-value return statement",
								expectedCount = 1,
								givenCount = #subsources,
								location = value.location,
							}
						end

						table.insert(sources, subsources[1])
						table.insert(evaluation, subevaluation)
					end
				end

				local returnSt = {
					tag = "return",
					sources = sources,
					returns = "yes",
				}
				table.insert(evaluation, returnSt)

				local fullName = containingSignature.container .. "." .. containingSignature.name

				-- Check return types
				assert(#sources == #containingSignature.returnTypes)
				for i, source in ipairs(sources) do
					local expected = containingSignature.returnTypes[i]
					if not areTypesEqual(source.type, expected) then
						Report.TYPES_DONT_MATCH {
							purpose = string.ordinal(i) .. " return value of " .. fullName,
							expectedType = showType(expected),
							givenType = showType(source.type),
							expectedLocation = expected.location,
							location = source.location,
						}
					end
				end

				return buildBlock(evaluation)
			elseif pStatement.tag == "do-statement" then
				local evaluation, out = compileExpression(
					pStatement.expression,
					scope
				)
				assert(#out ~= 0)
				if #out > 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "do-statement expression",
						expectedCount = 1,
						givenCount = #out,
						location = pStatement.location,
					}
				elseif not areTypesEqual(out[1].type, UNIT_TYPE) then
					Report.TYPES_DONT_MATCH {
						purpose = "do-statement expression",
						expectedType = "Unit",
						givenType = showType(out[1].type),
						expectedLocation = pStatement.expression.location,
						location = pStatement.expression.location,
					}
				end

				return evaluation
			elseif pStatement.tag == "if-statement" then
				local conditionEvaluation, conditionOut = compileExpression(pStatement.condition, scope)
				assert(#conditionOut ~= 0)
				if #conditionOut > 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "if-statement condition",
						expectedCount = 1,
						givenCount = #conditionOut,
						location = pStatement.location,
					}
				elseif not areTypesEqual(conditionOut[1].type, BOOLEAN_TYPE) then
					Report.TYPES_DONT_MATCH {
						purpose = "if-statement condition",
						expectedType = "Boolean",
						expectedLocation = pStatement.condition.location,
						givenType = showType(conditionOut[1].type),
						location = pStatement.condition.location,
					}
				end

				-- Builds the else-if-chain IR instructions.
				-- The index is the index of the first else-if clause to include.
				-- RETURNS an IRStatement that holds the compiled tail of the else.
				local function compileElseChain(i)
					if i > #pStatement.elseifs then
						if pStatement["else"] then
							local blockIR = compileBlock(pStatement["else"].body, scope)
							assertis(blockIR, "StatementIR")
							return blockIR
						else
							return buildBlock({})
						end
					end
					local elseIfConditionEvaluation, elseIfConditionOut = compileExpression(pStatement.elseifs[i].condition, scope)
					assert(#elseIfConditionOut ~= 0)
					if #elseIfConditionOut > 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "else-if-statement condition",
							expectedCount = 1,
							givenCount = #conditionOut,
							location = pStatement.elseifs[i].location,
						}
					elseif not areTypesEqual(elseIfConditionOut[1].type, BOOLEAN_TYPE) then
						Report.TYPES_DONT_MATCH {
							purpose = "else-if-statement condition",
							expectedType = "Boolean",
							expectedLocation = pStatement.elseifs[i].condition.location,
							givenType = showType(elseIfConditionOut[1].type),
							location = pStatement.elseifs[i].condition.location,
						}
					end

					local bodyThen = compileBlock(pStatement.elseifs[i].body, scope)
					local bodyElse = compileElseChain(i + 1)
					local ifSt = freeze {
						tag = "if",
						returns = unclear(bodyThen.returns, bodyElse.returns),
						condition = elseIfConditionOut[1],
						bodyThen = bodyThen,
						bodyElse = bodyElse,
					}
					assertis(elseIfConditionEvaluation, "StatementIR")
					assertis(ifSt, "StatementIR")
					return buildBlock({elseIfConditionEvaluation, ifSt})
				end

				local bodyThen = compileBlock(pStatement.body, scope)
				local bodyElse = compileElseChain(1)

				local ifSt = freeze {
					tag = "if",
					returns = unclear(bodyThen.returns, bodyElse.returns),
					condition = conditionOut[1],
					bodyThen = bodyThen,
					bodyElse = bodyElse,
				}

				assertis(conditionEvaluation, "StatementIR")
				assertis(ifSt, "StatementIR")
				return buildBlock({conditionEvaluation, ifSt})
			end
			error("TODO: compileStatement(" .. show(pStatement) .. ")")
		end

		-- RETURNS a BlockSt
		compileBlock = function(pBlock, scope)
			assertis(scope, listType(mapType("string", "VariableIR")))

			-- Open a new scope
			table.insert(scope, {})
		
			local statements = {}
			local returned = "no"
			for i, pStatement in ipairs(pBlock.statements) do
				-- This statement is unreachable, because the previous
				-- always returns
				if returned == "yes" then
					Report.UNREACHABLE_STATEMENT {
						cause = statements[i-1].location,
						reason = "always returns",
						unreachable = pStatement.location,
					}
				end

				local statement = compileStatement(pStatement, scope)
				assertis(statement, "StatementIR")
				
				if statement.returns == "yes" then
					returned = "yes"
				elseif statement.returns == "maybe" then
					returned = "maybe"
				end
				table.insert(statements, statement)
			end
			assertis(statements, listType "StatementIR")

			-- Close the current scope
			table.remove(scope)

			return freeze {
				tag = "block",
				statements = statements,
				returns = returned,
				location = pBlock.location,
			}
		end

		-- Collect static functions' type parameters from the containing class
		local generics = {}
		if containingSignature.modifier == "static" then
			generics = definition.generics
		end

		-- Create the initial scope with the function's parameters
		local functionScope = {{}}
		for _, parameter in ipairs(containingSignature.parameters) do
			functionScope[1][parameter.name] = parameter
		end

		-- Initialize a "this" variable
		local initialization = buildBlock {}
		if containingSignature.modifier == "method" then
			initialization = buildBlock {
				localSt(thisVariable),
				{
					tag = "this",
					destination = thisVariable,
					returns = "no",
				},
			}
		end

		local body = false
		if not containingSignature.foreign then
			body = buildBlock {
				initialization,
				compileBlock(containingSignature.body, functionScope)
			}
			assertis(body, "StatementIR")
			if body.returns ~= "yes" then
				local returns = {}
				for _, returnType in ipairs(containingSignature.returnTypes) do
					table.insert(returns, showType(returnType))
				end
				returns = table.concat(returns, ", ")

				if returns ~= "Unit" then
					Report.FUNCTION_DOESNT_RETURN {
						name = containingSignature.container .. ":" .. containingSignature.name,
						modifier = containingSignature.modifier,
						location = containingSignature.body.location,
						returns = returns,
					}
				end
			end
		end

		return freeze {
			name = containingSignature.name,
			definitionName = definition.name,
			
			-- Function's generics exclude those on the `this` instance
			generics = generics,
			
			parameters = containingSignature.parameters,
			returnTypes = containingSignature.returnTypes,

			body = body,
			signature = containingSignature,
		}
	end

	local classes = {}
	local unions = {}
	local interfaces = {}
	local functions = {}

	-- Scan the definitions for all function bodies
	for _, definition in ipairs(allDefinitions) do
		if definition.tag == "class" or definition.tag == "union" then
			for _, signature in ipairs(definition.signatures) do
				local func = compileFunctionFromStruct(definition, signature)
				assertis(func, "FunctionIR")

				table.insert(functions, func)
			end
			if definition.tag == "class" then
				table.insert(classes, definition)
			else
				table.insert(unions, definition)
			end
		elseif definition.tag == "interface" then
			table.insert(interfaces, definition)
		else
			error("unknown definition tag `" .. definition.tag .. "`")
		end
	end
	
	assertis(functions, listType "FunctionIR")

	-- Check that the main class exists
	if main == "skip" then
		main = false
	else
		local mainClass = table.findwith(classes, "name", main)
		if not mainClass then
			Report.NO_MAIN {
				name = main,
			}
		end
		local mainStatic = table.findwith(mainClass.signatures, "name", "main")
		if not mainStatic or mainStatic.modifier ~= "static" then
			Report.NO_MAIN_STATIC {
				name = main,
			}
		elseif #mainStatic.parameters ~= 0 then
			Report.NO_MAIN_STATIC {
				name = main,
			}
		elseif #mainClass.generics ~= 0 then
			Report.MAIN_MUST_NOT_BE_GENERIC {
				name = main,
			}
		end
	end

	return freeze {
		classes = classes,
		unions = unions,
		interfaces = interfaces,
		functions = functions,
		main = main,
	}
end

return semanticsSmol
