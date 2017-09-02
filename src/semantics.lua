-- Curtis Fenner, copyright (C) 2017

local Report = import "semantic-errors.lua"

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

local idCount = 0
-- RETURNS a unique (to this struct) local variable name
local function generateLocalID()
	idCount = idCount + 1
	return "_local" .. tostring(idCount)
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

-- assignments: map string -> Type+
-- RETURNS a function Type+ -> Type+ that substitutes the indicated
-- types for generic variables.
local function genericSubstituter(assignments)
	assertis(assignments, mapType("string", "Type+"))

	local function subs(t)
		assertis(t, "Type+")

		if t.tag == "concrete-type+" then
			return {tag = "concrete-type+",
				name = t.name,
				arguments = table.map(subs, t.arguments),
				location = t.location,
			}
		elseif t.tag == "keyword-type+" then
			return t
		elseif t.tag == "generic+" then
			if not assignments[t.name] then
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
	assertis(type, "ConcreteType+")
	assertis(allDefinitions, listType "Definition")

	local definition = table.findwith(allDefinitions, "name", type.name)
	assert(definition)

	local assignments = {}
	for i, generic in ipairs(definition.generics) do
		assignments[generic.name] = type.arguments[i]
	end
	return genericSubstituter(assignments)
end

-- RETURNS a list of constraints (as Type+) that the given type satisfies
local function getTypeConstraints(type, typeScope, allDefinitions)
	assertis(type, "Type+")
	assertis(typeScope, listType "TypeParameterIR")
	assertis(allDefinitions, listType "Definition")

	if type.tag == "concrete-type+" then
		local definition = table.findwith(allDefinitions, "name", type.name)
		if definition.tag ~= "union" and definition.tag ~= "class" then
			error(string.rep("?", 8000))
		end

		-- TODO: Is arity already checked?
		local substitute = getSubstituterFromConcreteType(type, allDefinitions)

		local constraints = table.map(substitute, definition.implements)
		return constraints
	elseif type.tag == "keyword-type+" then
		error("TODO: getTypeConstraints(keyword-type+")
	elseif type.tag == "generic+" then
		local parameter = table.findwith(typeScope, "name", type.name)
		-- TODO: Are generics guaranteed to be in scope here?
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
	assertis(constraint, "ConcreteType+")
	assertis(typeScope, listType "TypeParameterIR")
	assertis(need, recordType {
		container = "Definition",
		constraint = "Type+",
		nth = "integer",
	})
	assertis(allDefinitions, listType "Definition")

	for _, c in ipairs(getTypeConstraints(type, typeScope, allDefinitions)) do
		if areTypesEqual(c, constraint) then
			return
		end
	end

	-- The type `type` does not implement the constraint `constraint`
	Report.TYPE_MUST_IMPLEMENT_CONSTRAINT {
		type = showType(type),
		constraint = showType(constraint),
		location = type.location,
		
		nth = need.nth,
		container = need.container.name,
		cause = need.constraint.location,
	}
end

-- RETURNS whether or not the type is instantiable, meaning usable
-- as a variable type or method parameter type
local function isTypeInstantiable(t, allDefinitions)
	assertis(t, "Type+")
	assertis(allDefinitions, listType "Definition")

	if t.tag == "concrete-type+" then
		-- Find whether or not it is an interface
		local definition = table.findwith(allDefinitions, "name", t.name)
		if definition.tag == "interface" then
			return false
		elseif definition.tag == "union" or definition.tag == "class" then
			return true
		end
		error("unknown definition tag `" .. definition.tag .. "`")
	elseif t.tag == "keyword-type+" then
		-- TODO: never type
		return true
	elseif t.tag == "generic+" then
		return true
	end
	error("unknown type tag")
end

-- RETURNS nothing
local function verifyInstantiable(t, allDefinitions)
	assertis(t, "Type+")
	assertis(allDefinitions, listType "Definition")

	if not isTypeInstantiable(t, allDefinitions) then
		Report.UNINSTANTIABLE_USED {
			location = t.location,
			type = showType(t),
		}
	end
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
			verifyInstantiable(argument, allDefinitions)

			-- Verify that the `i`th argument satisfies the constraints of
			-- the `i`th parameter
			for _, generalConstraint in ipairs(generic.constraints) do
				local constraint = substitute(generalConstraint.interface)

				-- TODO: better explain context
				verifyTypeSatisfiesConstraint(argument, constraint, typeScope, {
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
		local function typeFinder(t, typeScope)
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
				elseif not packageIsInScope[package] then
					Report.UNKNOWN_PACKAGE_USED {
						package = package,
						location = t.location,
					}
				end
				assertis(package, "string")

				local fullName = package .. ":" .. t.base
				if not definitionSourceByFullName[fullName] then
					Report.UNKNOWN_TYPE_USED {
						name = fullName,
						location = t.location,
					}
				end

				return {tag = "concrete-type+",
					name = fullName,
					arguments = table.map(typeFinder, t.arguments, typeScope),
					location = t.location,
				}
			elseif t.tag == "generic" then
				-- Search for the name in `typeScope`
				if not table.findwith(typeScope, "name", t.name) then
					Report.UNKNOWN_GENERIC_USED(t)
				end

				return {tag = "generic+",
					name = t.name,
					location = t.location,
				}
			elseif t.tag == "type-keyword" then
				return {tag = "keyword-type+",
					name = t.name,
					location = t.location,
				}
			end
			error("unhandled ast type tag `" .. t.tag .. "`")
		end

		-- RETURNS a signature
		local function compiledSignature(signature, scope)
			assertis(scope, listType("TypeParameterIR"))

			return freeze {
				foreign = not not signature.foreign,
				modifier = signature.modifier.keyword,
				name = signature.name,
				returnTypes = table.map(typeFinder, signature.returnTypes, scope),
				parameters = table.map(function(p)
					return {
						name = p.name,
						type = typeFinder(p.type, scope),
						location = p.location,
					}
				end, signature.parameters),
				location = signature.location,
			}
		end

		-- RETURNS a list[TypeParameterIR]
		local function compiledGenerics(generics)
			local list = {}
			local map = {}
			for _, parameterAST in ipairs(generics.parameters) do
				local parameter = {
					name = parameterAST,
					constraints = {},
				}
				table.insert(list, parameter)

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
				local constraint = typeFinder(
					constraintAST.constraint, typeScope)

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

			return list
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
					type = typeFinder(field.type, generics),
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
				
				local signature = compiledSignature(method.signature, generics)
				signature = table.with(signature, "body", method.body)
				signature = table.with(signature, "typeFinder", typeFinder)
				signature = table.with(signature, "container", structName)
				table.insert(signatures, signature)
			end

			-- Compile the set of interfaces this class claims to implement
			local implements = table.map(
				typeFinder, definition.implements, generics)

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
					local compiled = compiledSignature(raw, generics)
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
			local interface = table.findwith(
				allDefinitions, "name", interfaceName)
			-- TODO: check that it is an interface
			assert(interface)

			-- Instantiate each of the interface's type parameters with the
			-- argument specified in the "implements"
			local assignments = {}
			if #int.arguments ~= #interface.generics then
				Report.WRONG_ARITY {
					name = interface.name,
					givenArity = #int.arguments,
					expectedArity = #interface.generics,
					location = int.location,
					definitionLocation = interface.location,
				}
			end
			for i, argument in ipairs(int.arguments) do
				assignments[interface.generics[i].name] = argument
			end
			local subs = genericSubstituter(assignments)

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
							interface = showType(int),
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
				verifyTypeValid(
					constraint.interface,
					definition.generics,
					allDefinitions
				)
			end
		end

		if definition.tag == "class" then
			-- Verify each field
			for _, field in ipairs(definition.fields) do
				verifyInstantiable(field.type, allDefinitions)
				verifyTypeValid(field.type, definition.generics,
					allDefinitions)
			end

			-- Verify each implements
			for _, implements in ipairs(definition.implements) do
				-- XXX: is implements validated to be an interface already?
				verifyTypeValid(implements, definition.generics,
					allDefinitions)
			end

			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyInstantiable(parameter.type, allDefinitions)
					verifyTypeValid(parameter.type, definition.generics,
						allDefinitions)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyInstantiable(returnType, allDefinitions)
					verifyTypeValid(returnType, definition.generics,
						allDefinitions)
				end

				-- Verify the signature's body later
			end
		elseif definition.tag == "union" then
			-- Verify each field
			for _, field in ipairs(definition.fields) do
				verifyInstantiable(field.type, allDefinitions)
				verifyTypeValid(field.type, definition.generics,
					allDefinitions)
			end

			-- Verify each implements
			for _, implements in ipairs(definition.implements) do
				verifyTypeValid(implements, definition.generics,
					allDefinitions)
			end

			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyInstantiable(parameter.type, allDefinitions)
					verifyTypeValid(parameter.type, definition.generics,
						allDefinitions)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyInstantiable(returnType, allDefinitions)
					verifyTypeValid(returnType, definition.generics,
						allDefinitions)
				end
			end
		elseif definition.tag == "interface" then
			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyInstantiable(parameter.type, allDefinitions)
					verifyTypeValid(parameter.type, definition.generics,
						allDefinitions)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyInstantiable(returnType, allDefinitions)
					verifyTypeValid(returnType, definition.generics,
						allDefinitions)
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

	-- RETURNS a FunctionIR
	local function compileFunctionFromStruct(definition, signature)
		assertis(definition, choiceType("ClassIR", "UnionIR"))
		assertis(signature, "Signature")

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

		-- RETURNS a (verified) Type+
		local function findType(parsedType)
			local typeScope = definition.generics
			local outType = signature.typeFinder(parsedType, typeScope)
			verifyTypeValid(outType, definition.generics, allDefinitions)
			return outType
		end

		-- RETURNS a ConstraintIR
		local function constraintFromStruct(interface, implementer)
			assertis(interface, "Type+")
			assert(isTypeInstantiable(implementer, allDefinitions))

			if implementer.tag == "concrete-type+" then
				if #implementer.arguments > 0 then
					error "TODO"
				end
				return freeze {
					tag = "concrete-constraint",
					interface = interface,
					concrete = implementer,
				}
			end
			print(show(interface))
			print(show(implementer))
			print(string.rep(".", 80))
			error("unhandled tag: " .. show(implementer))
		end

		-- RETURNS StatementIR, [Variable]
		local function compileExpression(pExpression, scope)
			assertis(pExpression, recordType {
				tag = "string"
			})
			assertis(scope, listType(mapType("string", "VariableIR")))

			if pExpression.tag == "string-literal" then
				local out = {
					name = generateLocalID(),
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
					name = generateLocalID(),
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
					name = generateLocalID(),
					type = containerType,
					location = pExpression.location .. ">"
				}
				assertis(out.type, "ConcreteType+")

				if signature.modifier ~= "static" then
					Report.NEW_USED_OUTSIDE_STATIC {
						location = pExpression.location,
					}
				end

				local newSt = {
					tag = "new",
					type = containerType,
					fields = {},
					returns = "no",
					constraints = {},
					destination = out,
				}

				-- All of the constraints are provided as arguments to this
				-- static function
				for constraintName in pairs(definition.constraints) do
					newSt.constraints[constraintName] = freeze {
						tag = "parameter-constraint",
						name = constraintName,
					}
				end

				local evaluation = {}
				-- Evaluate all arguments to new
				for _, argument in ipairs(pExpression.arguments) do
					local subEvaluation, subOut = compileExpression(
						argument.value, scope)
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

					newSt.fields[argument.name] = subOut[1]
				end

				-- Check that no fields are missing
				for _, field in ipairs(definition.fields) do
					if not newSt.fields[field.name] then
						Report.MISSING_VALUE {
							purpose = "new " .. showType(containerType) .. " expression",
							name = field.name,
							location = pExpression.location,
						}
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
				local t = findType(pExpression.baseType)
				verifyInstantiable(t, allDefinitions)

				if t.tag == "generic+" then
					error("TODO: static generic calls are different")
				end

				local baseDefinition = definitionFromType(t)

				local fullName = showType(t) .. "." .. pExpression.name

				-- Map type variables to the type-values used for this instantiation
				local substituter = getSubstituterFromConcreteType(t, allDefinitions)

				local method = table.findwith(baseDefinition.signatures,
					"name", pExpression.name)
				
				if not method or method.modifier ~= "static" then
					Report.NO_SUCH_METHOD {
						modifier = "static",
						type = showType(t),
						name = pExpression.name,
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

				-- Evaluate the arguments
				local evaluation = {}
				local argumentSources = {}
				for i, argument in ipairs(pExpression.arguments) do
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

					-- Verify the type of the argument matches
					local arg = outs[1]
					local parameterType = substituter(method.parameters[i].type)
					if not areTypesEqual(arg.type, parameterType) then
						Report.TYPES_DONT_MATCH {
							purpose = string.ordinal(i) .. " argument to " .. fullName,
							expectedLocation = method.parameters[i].location,
							givenType = showType(arg.type),
							location = argument.location,
							expectedType = showType(parameterType)
						}
					end

					table.insert(evaluation, subEvaluation)
					table.insert(argumentSources, arg)
				end

				-- Collect the constraints
				local constraints = {}
				for gi, generic in ipairs(baseDefinition.generics) do
					for ci, constraint in ipairs(generic.constraints) do
						local key = "#" .. gi .. "_" .. ci
						constraints[key] = constraintFromStruct(constraint.interface, t.arguments[gi])
					end
				end

				-- Create variables for the output
				local outs = {}
				for _, returnType in pairs(method.returnTypes) do
					local returnVariable = {
						name = generateLocalID(),
						type = substituter(returnType),
						location = pExpression.location,
					}
					table.insert(outs, returnVariable)
					table.insert(evaluation, localSt(returnVariable))
				end

				table.insert(evaluation, {
					tag = "static-call",
					baseType = t,
					name = method.name,
					arguments = argumentSources,
					constraints = constraints,
					destinations = outs,
					returns = "no",
				})
				
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

				if baseInstance.type.tag == "generic+" then
					-- Generic instance
					local parameter = table.findwith(definition.generics,
						"name", baseInstance.type.name)
					assert(parameter)

					-- Find the constraint(s) which supply this method name
					local matches = {}
					for ci, constraint in ipairs(parameter.constraints) do
						local interface = definitionFromType(constraint.interface)
						local signature = table.findwith(interface.signatures, "name", pExpression.methodName)
						if signature then
							table.insert(matches, freeze {
								signature = signature,
								interface = interface,
								id = table.indexof(definition.generics, parameter) .. "_" .. ci
							})
						end
					end

					-- Verify exactly one constraint supplies this method name
					if #matches == 0 then
						Report.NO_SUCH_METHOD {
							modifier = "method",
							type = showType(baseInstance.type),
							name = pExpression.name,
							definitionLocation = parameter.location,
							location = pExpression.location,
						}
					elseif #matches > 1 then
						Report.CONFLICTING_INTERFACES {
							method = pExpression.name,
							interfaceOne = showType(matches[1].interface),
							interfaceTwo = showType(matches[2].interface),
							location = pExpression.location,
						}
					end
					local method = matches[1]

					-- Verify the types of the arguments match the parameters
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

						table.insert(arguments, outs[1])
						if not areTypesEqual(pArgument.type, method.parameters[i].type) then
							Report.TYPES_DONT_MATCH {
								purpose = string.ordinal(i) .. " argument to `" .. fullName .. "`",
								expectedType =	showType(method.parameters[i].type),
								expectedLocation = method.parameters[i].location,
								givenType = showType(pArgument.type),
								location = pArgument.location,
							}
						end
						table.insert(evaluation, subEvaluation)
					end
					assertis(evaluation, listType "StatementIR")

					local destinations = {}
					for _, returnType in ipairs(method.signature.returnTypes) do
						local destination = {
							name = generateLocalID(),
							type = returnType,
							location = pExpression.location .. ">",
						}
						table.insert(destinations, destination)
						table.insert(evaluation, {
							tag = "local",
							variable = destination,
							returns = "no",
						})
					end

					local constraint = {
						tag = "this-constraint",
						instance = baseInstance,
						name = method.id,
					}

					table.insert(evaluation, {
						tag = "generic-method-call",
						baseInstance = baseInstance,
						constraint = constraint,
						name = pExpression.methodName,
						arguments = arguments,
						destinations = destinations,
						returns = "no",
					})

					return buildBlock(evaluation), destinations
				end
				assertis(arguments, listType "VariableIR")

				-- Concrete instance
				local baseDefinition = definitionFromType(baseInstance.type)
				
				-- Find the definition of the method being invoked
				local method = table.findwith(baseDefinition.signatures,
					"name", pExpression.methodName)
				if not method or method.modifier ~= "method" then
					Report.NO_SUCH_METHOD {
						modifier = "method",
						type = showType(t),
						name = pExpression.name,
						definitionLocation = baseDefinition.location,
						location = pExpression.location,
					}
				end

				error "TODO?"

			elseif pExpression.tag == "keyword" then
				if pExpression.keyword == "false" or pExpression.keyword == "true" then
					local boolean = {
						type = BOOLEAN_TYPE,
						name = generateLocalID(),
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
						name = generateLocalID(),
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
					name = generateLocalID(),
					location = pExpression.location,
				}
				local accessStatement = {
					tag = "field",
					name = pExpression.field,
					base = base,
					destination = result,
					returns = "no",
				}
				return buildBlock {baseEvaluation, accessStatement}, {result}
			end

			error("TODO expression: " .. show(pExpression))
		end

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
						type = findType(pVariable.type),
						location = pVariable.location,
					}
					verifyInstantiable(variable.type, allDefinitions)
					
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
				if #pStatement.values == 1 then
					local evaluation, sources = compileExpression(
						pStatement.values[1], scope)
					
					if #sources ~= #signature.returnTypes then
						Report.RETURN_COUNT_MISMATCH {
							signatureCount = #signature.returnTypes,
							returnCount = #sources,
							location = pStatement.location,
						}
					end

					return buildBlock(table.concatted({evaluation}, {
						tag = "return",
						sources = sources,
						returns = "yes",
					}))
				else
					error("TODO")
				end
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
						location = pExpression.location,
					}
				elseif not areTypesEqual(out[1].type, UNIT_TYPE) then
					Report.TYPES_DONT_MATCH {
						purpose = "do-statement expression",
						expectedType = "Unit",
						expectedLocation = pExpression.expression.location,
						givenType = showType(out[1].type),
						location = pExpression.expression.location,
					}
				end

				return evaluation
			end
			error("TODO: compileStatement(" .. show(pStatement) .. ")")
		end

		-- RETURNS a BlockSt
		local function compileBlock(pBlock, scope)
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
		if signature.modifier == "static" then
			generics = definition.generics
		end

		-- Create the initial scope with the function's parameters
		local functionScope = {{}}
		for _, parameter in ipairs(signature.parameters) do
			functionScope[1][parameter.name] = parameter
		end

		local body = compileBlock(signature.body, functionScope)
		assertis(body, "StatementIR")

		return freeze {
			name = signature.name,
			definitionName = definition.name,
			
			-- Function's generics exclude those on the `this` instance
			generics = generics,
			
			parameters = signature.parameters,
			returnTypes = signature.returnTypes,

			body = body,
			signature = signature,
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

	-- TODO: check the main class exists

	return freeze {
		classes = classes,
		unions = unions,
		interfaces = interfaces,
		functions = functions,
		main = main,
	}
end

return semanticsSmol
