-- Curtis Fenner, copyright (C) 2017

local Report = import "semantic-errors.lua"
local profile = import "profile.lua"
local common = import "common.lua"
local showType = common.showType
local areTypesEqual = common.areTypesEqual
local areInterfaceTypesEqual = common.areInterfaceTypesEqual
local excerpt = common.excerpt
local variableDescription = common.variableDescription

local BOOLEAN_DEF = table.findwith(common.BUILTIN_DEFINITIONS, "name", "Boolean")
local UNKNOWN_LOCATION = freeze {begins = "???", ends = "???"}

-- RETURNS the clearest possible combination of a, and b.
local function unclear(a, b)
	assertis(a, "maybe")
	assertis(b, "maybe")
	if a == b then
		return a
	end
	return "maybe"
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
	local indicator = string.char(string.byte "A" + (idCount - 1) % 26)

	--indicator = ""
	return "_local" .. indicator .. tostring(idCount) .. "_" .. tostring(hint)
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

-- RETURNS VariableIR, LocalSt
local function generateVariable(nameHint, type, location)
	assertis(nameHint, "string")
	assertis(type, "Type+")
	assertis(location, "Location")
	
	local variable = freeze {
		name = generateLocalID(nameHint),
		type = type,
		location = location,
		description = false,
	}
	return variable, localSt(variable)
end

-- RETURNS a StatementIR representing the execution of statements in
-- sequence
local function buildBlock(statements)
	assertis(statements, listType(recordType {}))
	for i = 1, #statements do
		assertis(statements[i], "StatementIR")
	end

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

-- RETURNS a StatementIR representing the same execution, but to be ignored by
-- codegeneration
local function buildProof(statement)
	assertis(statement, "StatementIR")

	return freeze {
		tag = "proof",
		body = statement,
		returns = "no",
	}
end

-- assignments: map string -> Type+
-- RETURNS a function Type+ -> Type+ that substitutes the indicated
-- types for generic variables.
local function genericSubstituter(assignments)
	assertis(assignments, mapType("string", "Type+"))

	-- Self is a keyword; here is refers to the (more) concrete type that
	-- implements this interface
	assert(assignments.Self, "assignments.Self must be provided to genericSubstituer")

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
			return {
				tag = "concrete-type+",
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
		elseif t.tag == "self-type+" then
			return assignments.Self
		end
		error("unknown Type+ tag `" .. t.tag .. "`")
	end
	return subs
end

--------------------------------------------------------------------------------

-- RETURNS a function Type+ -> Type+ to apply to types on the in interface's
-- definition to get specific types for a given instantiation
local function getSubstituterFromInterface(int, selfType, allDefinitions)
	assertis(int, "InterfaceType+")
	assertis(allDefinitions, listType "Definition")
	assertis(selfType, "Type+")

	local definition = table.findwith(allDefinitions, "name", int.name)
	assert(definition)
	assert(#definition.generics == #int.arguments)

	-- Note that "Self" is a keyword, so it is not a valid generic name
	local assignments = {Self = selfType}
	for i, generic in ipairs(definition.generics) do
		assignments[generic.name] = int.arguments[i]
	end
	return genericSubstituter(assignments)
end

-- RETURNS a function Type+ -> Type+ to apply to types on the
-- class/union's definition to use the specific types
-- in this instance
local function getSubstituterFromConcreteType(type, allDefinitions)
	assertis(type, "Type+")
	assertis(allDefinitions, listType "Definition")

	if type.tag == "keyword-type+" then
		return genericSubstituter({Self = type})
	end
	assertis(type, "ConcreteType+")

	local definition = table.findwith(allDefinitions, "name", type.name)
	assert(definition)
	assert(#definition.generics == #type.arguments)

	local assignments = {Self = type}
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

		local substitute = getSubstituterFromConcreteType(type, allDefinitions, type)
		local constraints = table.map(substitute, definition.implements)
		return constraints
	elseif type.tag == "keyword-type+" then
		-- XXX: Right now, keyword types do not implement any interfaces,
		-- requiring explicit boxing
		return {}
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
				verifyTypeSatisfiesConstraint(
					argument,
					instantiatedConstraint,
					typeScope,
					{
						container = definition,
						constraint = generalConstraint.interface,
						nth = i,
					},
					allDefinitions
				)
			end

			-- Verify recursively
			verifyTypeValid(argument, typeScope, allDefinitions)
		end
	elseif type.tag == "keyword-type+" then
		-- All keyword types are valid
		return
	elseif type.tag == "generic+" then
		-- All generic literals are valid
		return
	elseif type.tag == "self-type+" then
		-- All #Self literals are valid
		-- TODO: Though perhaps they should be forbidden in classes/unions
		return
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

	local SELF_TYPE = freeze {tag = "self-type+", location = constraint.location}
	local substitute = getSubstituterFromInterface(constraint, SELF_TYPE, allDefinitions)

	-- Check each argument
	for i, generic in ipairs(definition.generics) do
		local argument = constraint.arguments[i]
		assertis(argument, "Type+")

		-- Verify that the i-th argument satisfies the constraints of the i-th
		-- parameter
		for _, generalConstraint in ipairs(generic.constraints) do
			local instantiatedConstraint = substitute(generalConstraint.interface)

			-- TODO: provide a clearer context for error messages
			verifyTypeSatisfiesConstraint(
				argument,
				instantiatedConstraint,
				typeScope,
				{
					container = definition,
					constraint = generalConstraint.interface,
					nth = i,
				},
				allDefinitions
			)
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

local STRING_TYPE = common.STRING_TYPE
local INT_TYPE = common.INT_TYPE
local BOOLEAN_TYPE = common.BOOLEAN_TYPE
local UNIT_TYPE = common.UNIT_TYPE
local NEVER_TYPE = common.NEVER_TYPE

local BUILTIN_DEFINITIONS = common.BUILTIN_DEFINITIONS
local OPERATOR_ALIAS = common.OPERATOR_ALIAS

--------------------------------------------------------------------------------

-- RETURNS a Definition
local function interfaceDefinitionFromConstraint(t, allDefinitions)
	assertis(t, "InterfaceType+")
	assertis(allDefinitions, listType "Definition")

	local definition = table.findwith(allDefinitions, "name", t.name)
	assert(definition and definition.tag == "interface")

	return definition
end

-- RETURNS a Definition
local function definitionFromType(t, allDefinitions)
	assertis(t, choiceType("ConcreteType+", "KeywordType+"))
	assertis(allDefinitions, listType(recordType {name = "string"}))

	if t.tag == "keyword-type+" then
		local builtin = table.findwith(BUILTIN_DEFINITIONS, "name", t.name)
		assert(builtin)
		return builtin
	end

	local definition = table.findwith(allDefinitions, "name", t.name)

	-- Type Finder should verify that the type exists
	assert(definition, "definition must exist")

	return definition
end

--------------------------------------------------------------------------------

-- RETURNS record with interface, signature, constraint, name, etc.
local function findConstraintByMember(genericType, modifier, name, location, generics, environment)
	assertis(genericType, "GenericType+")
	assertis(modifier, choiceType(constantType "static", constantType "method"))
	assertis(name, "string")
	assertis(location, "Location")
	assert(name:sub(1, 1):lower() == name:sub(1, 1))
	assertis(generics, listType "TypeParameterIR")

	assertis(environment, recordType {
		allDefinitions = listType "object",
		containingSignature = "Signature",
		thisVariable = choiceType(constantType(false), "VariableIR"),
	})

	local allDefinitions = environment.allDefinitions
	local containingSignature = environment.containingSignature
	assertis(allDefinitions, listType "Definition")
	assertis(containingSignature, "Signature")

	local parameter, pi = table.findwith(generics, "name", genericType.name)
	assert(parameter)
	assertis(parameter, recordType {
		location = "Location",
	})

	local matches = {}
	for ci, constraint in ipairs(parameter.constraints) do
		local interface = interfaceDefinitionFromConstraint(constraint.interface, allDefinitions)
		local signature = table.findwith(interface.signatures, "name", name)
		if signature then
			local constraintIR = {
				tag = "parameter-constraint",
				name = "#" .. pi .. "_" .. ci,
				location = constraint.location,
				interface = constraint.interface,
			}
			if containingSignature.modifier == "method" then
				assert(environment.thisVariable)
				constraintIR = {
					tag = "this-constraint",
					instance = table.with(environment.thisVariable, "location", location),
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

	-- TODO: get alternatives
	local alternatives = {"???"}

	-- Verify exactly one constraint supplies this method name
	if #matches == 0 then
		Report.NO_SUCH_METHOD {
			modifier = modifier,
			type = showType(genericType),
			name = name,
			definitionLocation = parameter.location,
			location = location,
			alternatives = alternatives,
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

-- generics: the generics IN SCOPE, not the generics of interface/implementer.
-- RETURNS a ConstraintIR
local function constraintFromStruct(interface, implementer, generics, containingSignature, environment, location)
	assertis(interface, "InterfaceType+")
	assertis(implementer, "Type+")
	assertis(generics, listType "TypeParameterIR")
	assertis(containingSignature, "Signature")
	assertis(environment, recordType {
		allDefinitions = listType "object",
		thisVariable = choiceType(constantType(false), "VariableIR"),
	})
	assertis(location, "Location")

	if implementer.tag == "concrete-type+" then
		local definition = definitionFromType(implementer, environment.allDefinitions)
		assert(definition)

		-- Constraints of parameterized types depend on the constraints they
		-- require
		local assignments = {}
		for i, generic in ipairs(definition.generics) do
			for j, c in ipairs(generic.constraints) do
				local key = "#" .. i .. "_" .. j

				local interface = c.interface
				assertis(interface, "InterfaceType+")

				local implementer = implementer.arguments[i]
				assertis(implementer, "Type+")

				local constraint = constraintFromStruct(
					interface,
					implementer,
					generics,
					containingSignature,
					environment,
					location
				)
				assertis(constraint, "ConstraintIR")

				assignments[key] = constraint
			end
		end

		return freeze {
			tag = "concrete-constraint",
			interface = interface,
			concrete = implementer,
			assignments = assignments,
		}
	elseif implementer.tag == "generic+" then
		local name
		for i, generic in ipairs(generics) do
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
			assert(environment.thisVariable)
			return freeze {
				tag = "this-constraint",
				instance = table.with(environment.thisVariable, "location", location),
				interface = interface,
				name = name,
			}
		end
	end
	error("unhandled tag `" .. implementer.tag .. "`")
end

--------------------------------------------------------------------------------

local function checkSingleBoolean(vs, purpose, location)
	assertis(vs, listType "VariableIR")
	assertis(purpose, "string")

	if #vs ~= 1 then
		Report.WRONG_VALUE_COUNT {
			purpose = purpose,
			expectedCount = 1,
			givenCount = #vs,
			location = location or vs[1].location,
		}
	elseif not areTypesEqual(vs[1].type, BOOLEAN_TYPE) then
		Report.EXPECTED_DIFFERENT_TYPE {
			expectedType = "Boolean",
			givenType = showType(vs[1].type),
			location = location or vs[1].location,
			purpose = purpose,
		}
	end
end

--------------------------------------------------------------------------------

-- RETURNS whether or not the given parsed expression is pure (syntactically)
local function isExprPure(expr)
	local leaf = {
		["string-literal"] = true,
		["int-literal"] = true,
		["identifier"] = true,
		["keyword"] = true,
	}
	if leaf[expr.tag] then
		return true
	end

	if expr.tag == "new-expression" then
		for _, argument in ipairs(expr.arguments) do
			if not isExprPure(argument.value) then
				return false
			end
		end
		return true
	elseif expr.tag == "static-call" then
		for _, argument in ipairs(expr.arguments) do
			if not isExprPure(argument) then
				return false
			end
		end
		return not expr.bang
	elseif expr.tag == "method-call" then
		if not isExprPure(expr.base) then
			return false
		end
		for _, argument in ipairs(expr.arguments) do
			if not isExprPure(argument) then
				return false
			end
		end
		return not expr.bang
	elseif expr.tag == "field" then
		return isExprPure(expr.base)
	elseif expr.tag == "binary" then
		return isExprPure(expr.left) and isExprPure(expr.right)
	elseif expr.tag == "isa" then
		return isExprPure(expr.base)
	elseif expr.tag == "forall-expr" then
		-- XXX: forall is always pure, but argument must be checked
		return true
	end
	error("unknown tag `" .. expr.tag .. "`")
end

local compileExpression

-- conditionExpression: AST
-- thenBody: StatementIR
-- RETURNS StatementIR
local function compileWhen(conditionExpression, thenBody, scope, subEnvironment)
	assertis(thenBody, "StatementIR")

	local conditionEval, conditionVars = compileExpression(conditionExpression, scope, subEnvironment)
	checkSingleBoolean(conditionVars, "when")
	assert(#conditionVars == 1)
	assert(areTypesEqual(conditionVars[1].type, BOOLEAN_TYPE))

	local assume = freeze {
		tag = "assume",
		variable = conditionVars[1],
		location = conditionVars[1].location,
		returns = "no",
	}

	local guarded = freeze {
		tag = "if",
		condition = conditionVars[1],
		bodyThen = buildBlock {assume, thenBody},
		bodyElse = buildBlock {},
		returns = "no",
	}

	return buildBlock {
		conditionEval, guarded,
	}
end

-- RETURNS a StatementIR
-- REQUIRES assertion has already been checked for type and value count
local function generatePreconditionVerify(assertion, method, invocation, environment, context, checkLocation)
	assertis(assertion, recordType {
		whens = listType "ASTExpression",
		condition = "ASTExpression",
	})
	assertis(method, "Signature")
	assertis(invocation, recordType {
		arguments = listType "VariableIR",
		container = "Type+",
		this = choiceType(constantType(false), "VariableIR"),
	})
	assertis(environment, recordType {
		returnOuts = choiceType(constantType(false), listType "VariableIR"),
	})
	assertis(context, "string")
	assertis(checkLocation, "Location")

	if invocation.this then
		assert(areTypesEqual(invocation.this.type, invocation.container))
	end

	local subEnvironment = freeze {
		resolveType = environment.resolveType,
		containerType = invocation.container,
		containingSignature = method,
		allDefinitions = environment.allDefinitions,
		thisVariable = invocation.this,

		-- Can be not-false when checking `ensures` at `return` statement
		returnOuts = environment.returnOuts,
	}

	local scope = {{}}
	for i, argument in ipairs(invocation.arguments) do
		scope[1][method.parameters[i].name] = argument
	end
	assertis(scope, listType(mapType("string", "VariableIR")))

	-- Evaluate the condition
	local evaluation, out = compileExpression(assertion.condition, scope, subEnvironment)
	assert(#out == 1)
	assert(areTypesEqual(out[1].type, BOOLEAN_TYPE))

	local verify = freeze {
		tag = "verify",
		variable = out[1],
		returns = "no",
		reason = context,
		conditionLocation = assertion.condition.location,
		checkLocation = checkLocation,
	}
	local out = buildBlock {
		evaluation,
		verify,
	}
	assertis(out, "StatementIR")

	-- Add a guard
	for _, when in ripairs(assertion.whens) do
		out = compileWhen(when, out, scope, subEnvironment)
	end

	return buildProof(out)
end

-- RETURNS a StatementIR
-- REQUIRES assertion has already been checked for type and value count
local function generatePostconditionAssume(assertion, method, invocation, environment, returnOuts)
	assertis(assertion, recordType {
		whens = listType "ASTExpression",
		condition = "ASTExpression",
	})
	assertis(method, "Signature")
	assertis(invocation, recordType {
		arguments = listType "VariableIR",
		this = choiceType(constantType(false), "VariableIR"),
	})
	assertis(environment, recordType {})
	assertis(environment.containerType, "Type+")
	assertis(returnOuts, choiceType(constantType(false), listType "VariableIR"))

	local subEnvironment = {
		resolveType = environment.resolveType,
		containerType = invocation.container,
		containingSignature = method,
		containerType = environment.containerType,
		allDefinitions = environment.allDefinitions,
		thisVariable = invocation.this,
		returnOuts = returnOuts,
	}

	local scope = {{}}
	for i, argument in ipairs(invocation.arguments) do
		scope[1][method.parameters[i].name] = argument
	end
	assertis(scope, listType(mapType("string", "VariableIR")))

	local evaluation, out = compileExpression(assertion.condition, scope, subEnvironment)
	assert(#out == 1)
	assert(areTypesEqual(out[1].type, BOOLEAN_TYPE))

	local assume = freeze {
		tag = "assume",
		variable = out[1],
		returns = "no",
		location = assertion.condition.location,
	}

	local out = buildBlock {
		evaluation,
		assume,
	}
	assertis(out, "StatementIR")

	-- Add a guard
	for _, when in ripairs(assertion.whens) do
		out = compileWhen(when, out, scope, subEnvironment)
	end

	return buildProof(out)
end

local NOT_SIGNATURE = table.findwith(BOOLEAN_DEF.signatures, "name", "not")
local OR_SIGNATURE = table.findwith(BOOLEAN_DEF.signatures, "name", "or")
local AND_SIGNATURE = table.findwith(BOOLEAN_DEF.signatures, "name", "and")

local function parened(s)
	assertis(s, "string")
	if s:find "%W" then
		return "(" .. s .. ")"
	end
	return s
end

-- RETURNS a StatementIR, VariableIR
local function irMethod(location, signature, base, arguments)
	assertis(location, "Location")
	assertis(signature, "Signature")
	assertis(base, "VariableIR")
	assertis(arguments, listType "VariableIR")
	
	assert(#signature.returnTypes == 1)

	local result = generateVariable(signature.name .. "_result", signature.returnTypes[1], location)
	local d1 = variableDescription(base)
	local ds = {}
	for i = 1, #arguments do
		ds[i] = variableDescription(arguments[i])
	end
	local description = parened(d1) .. "." .. signature.name .. "(" .. table.concat(ds, ", ") .. ")"
	result = table.with(result, "description", description)
	local method = freeze {
		tag = "method-call",
		baseInstance = base,
		arguments = arguments,
		destinations = {result},
		signature = signature,
		returns = "no",
	}
	return buildBlock {localSt(result), method}, result
end

-- RETURNS an Assume that var is exactly one of the tags of union
local function closedUnionAssumption(union, var)
	assertis(var, "VariableIR")

	local seq = {}
	local ises = {}
	for _, variant in ipairs(union.fields) do
		local v = generateVariable("closed_union_is" .. variant.name, BOOLEAN_TYPE, var.location)
		local description = parened(excerpt(var.location)) .. " is " .. variant.name
		v = table.with(v, "description", description)

		table.insert(ises, v)
		table.insert(seq, localSt(v))
		table.insert(seq, freeze {
			tag = "isa",
			base = var,
			destination = v,
			variant = variant.name,
			returns = "no",
		})
	end

	-- Generate any (is a or is b or is c ...)
	local isAny = ises[1]
	for i = 2, #ises do
		local compute, nextIsAny = irMethod(var.location, OR_SIGNATURE, isAny, {ises[i]})
		table.insert(seq, compute)
		isAny = nextIsAny
	end
	local any = generateVariable("any-closed", BOOLEAN_TYPE, var.location)
	any = table.with(any, "description", "???")
	table.insert(seq, localSt(any))

	table.insert(seq, {
		tag = "assume",
		variable = isAny,
		location = var.location,
		returns = "no",
	})

	-- Generate at-most-one
	for i, va in ipairs(ises) do
		for j, vb in ipairs(ises) do
			if i < j then
				local computeBoth, both = irMethod(var.location, AND_SIGNATURE, va, {vb})
				table.insert(seq, computeBoth)

				local bothNotSt, bothNot = irMethod(var.location, NOT_SIGNATURE, both, {})
				table.insert(seq, bothNotSt)
				table.insert(seq, {
					tag = "assume",
					variable = bothNot,
					location = var.location,
					returns = "no",
				})
			end
		end
	end

	return buildBlock(seq)
end

-- RETURNS a StatementIR, [VariableIR].
-- VERIFIES each expression produces only a single value
-- VERIFEIS at most one of the expressions is impure
local function compileSubexpressions(expressions, purpose, location, scope, environment)
	assertis(expressions, listType "ASTExpression")
	assertis(location, "Location")
	assertis(environment, recordType {})

	local evaluation = {}
	local outs = {}

	local impures = 0
	for i, expression in ipairs(expressions) do
		local subEvaluation, subOuts = compileExpression(expression, scope, environment)
		if #subOuts ~= 1 then
			Report.WRONG_VALUE_COUNT {
				purpose = string.ordinal(i) .. " " .. purpose,
				expectedCount = 1,
				givenCount = #subOuts,
				location = expression.location,
			}
		end
		table.insert(evaluation, subEvaluation)
		table.insert(outs, subOuts[1])

		if not isExprPure(expression) then
			impures = impures + 1
		end
	end

	if impures > 1 then
		Report.EVALUATION_ORDER {
			location = location,
		}
	end

	return buildBlock(evaluation), freeze(outs)
end

-- RETURNS StatementIR, [VariableIR]
local function compileMethod(baseInstance, arguments, methodName, bang, location, environment)
	assertis(baseInstance, "VariableIR")
	assertis(arguments, listType "VariableIR")
	assertis(methodName, "string")
	assertis(bang, "boolean")
	assertis(location, "Location")
	assertis(environment, recordType {})

	local containerType = environment.containerType
	local allDefinitions = environment.allDefinitions
	local containingDefinition = definitionFromType(containerType, allDefinitions)
	local containingSignature = environment.containingSignature

	if baseInstance.type.tag == "generic+" then
		-- Generic instance
		local method = findConstraintByMember(
			baseInstance.type,
			"method",
			methodName,
			location,
			containingDefinition.generics,
			environment
		)
		assertis(method.signature, "Signature")

		local substituter = getSubstituterFromInterface(method.constraint, baseInstance.type, allDefinitions)

		local methodFullName = method.fullName

		-- Verify the correct number of arguments is provided
		if #arguments ~= #method.signature.parameters then
			Report.WRONG_VALUE_COUNT {
				purpose = "interface method `" .. methodFullName .. "`",
				expectedCount = #method.signature.parameters,
				givenCount = #arguments,
				location = location,
			}
		end

		-- Verify the types of the arguments match the parameters
		for i, argument in ipairs(arguments) do
			local expectedType = substituter(method.signature.parameters[i].type)
			if not areTypesEqual(argument.type, expectedType) then
				Report.TYPES_DONT_MATCH {
					purpose = string.ordinal(i) .. " argument to `" .. methodFullName .. "`",
					expectedType = showType(expectedType),
					expectedLocation = method.signature.parameters[i].location,
					givenType = showType(argument.type),
					location = argument.location,
				}
			end
		end

		-- Verify the bang matches
		if not method.signature.bang ~= not bang then
			Report.BANG_MISMATCH {
				modifier = method.signature.modifier,
				fullName = methodFullName,
				expected = method.signature.bang,
				given = bang,
				signatureLocation = method.signature.location,
				location = location,
			}
		end

		-- Create destinations for each return value
		local evaluation = {}
		local destinations = {}
		for _, returnType in ipairs(method.signature.returnTypes) do
			local destination = generateVariable("gm_return", substituter(returnType), location)
			table.insert(destinations, destination)
			table.insert(evaluation, localSt(destination))
		end

		-- Generate Verify statements
		for i, require in ipairs(method.signature.requiresAST) do
			local verification = generatePreconditionVerify(
				require,
				method.signature,
				{arguments = arguments, this = baseInstance},
				environment,
				"the " .. string.ordinal(i) .. " `requires` condition for method " .. methodFullName,
				location
			)
			table.insert(evaluation, verification)
		end

		local callSt = freeze {
			tag = "generic-method-call",
			baseInstance = baseInstance,
			constraint = method.constraintIR,
			arguments = arguments,
			destinations = destinations,
			returns = "no",
			signature = method.signature,
		}
		assertis(callSt, "StatementIR")
		table.insert(evaluation, callSt)

		-- Generate Assume statements
		for _, ensure in ipairs(method.signature.ensuresAST) do
			local assumption = generatePostconditionAssume(
				ensure,
				method.signature,
				{
					arguments = arguments,
					this = baseInstance,
					container = baseInstance.type,
				},
				environment,
				destinations
			)
			table.insert(evaluation, assumption)
		end

		return buildBlock(evaluation), freeze(destinations)
	end

	-- Concrete instance
	local baseDefinition = definitionFromType(baseInstance.type, allDefinitions)
	local substituter = getSubstituterFromConcreteType(baseInstance.type, allDefinitions)

	-- Find the definition of the method being invoked
	local method = table.findwith(baseDefinition.signatures, "name", methodName)
	local alternatives = table.map(
		function(x)
			return x.name
		end,
		baseDefinition.signatures
	)
	if not method then
		Report.NO_SUCH_METHOD {
			type = showType(baseInstance.type),
			modifier = "method",
			name = methodName,
			alternatives = alternatives,
			location = location,
		}
	end
	assertis(method, "Signature")

	local methodFullName = baseDefinition.name .. "." .. methodName
	if not method or method.modifier ~= "method" then
		Report.NO_SUCH_METHOD {
			modifier = "method",
			type = showType(baseInstance.type),
			name = methodName,
			definitionLocation = baseDefinition.location,
			alternatives = alternatives,
			location = location,
		}
	end

	-- Verify the correct number of arguments is provided
	if #arguments ~= #method.parameters then
		Report.WRONG_VALUE_COUNT {
			purpose = "interface method " .. methodFullName,
			expectedCount = #method.parameters,
			givenCount = #arguments,
			location = location,
		}
	end

	-- Verify the types of the arguments match the parameters
	for i, argument in ipairs(arguments) do
		if not areTypesEqual(argument.type, substituter(method.parameters[i].type)) then
			Report.TYPES_DONT_MATCH {
				purpose = string.ordinal(i) .. " argument to `" .. methodFullName .. "`",
				expectedType = showType(method.parameters[i].type),
				expectedLocation = method.parameters[i].location,
				givenType = showType(argument.type),
				location = argument.location,
			}
		end
	end

	-- Verify the bang matches
	assertis(method, "Signature")
	if not method.bang ~= not bang then
		Report.BANG_MISMATCH {
			modifier = method.modifier,
			fullName = methodFullName,
			expected = method.bang,
			given = bang,
			signatureLocation = method.location,
			location = location,
		}
	elseif method.bang and not containingSignature.bang then
		Report.BANG_NOT_ALLOWED {
			context = containingSignature.modifier .. " `" .. containingDefinition.name .. "." .. containingSignature.name .. "`",
			location = location,
		}
	end

	-- Create destinations for each return value
	local evaluation = {}
	local destinations = {}
	for _, returnType in ipairs(method.returnTypes) do
		local destination = generateVariable(method.name .. "_result", substituter(returnType), location)
		table.insert(destinations, destination)
		table.insert(evaluation, localSt(destination))
	end

	-- Generate Verify statements
	for i, require in ipairs(method.requiresAST) do
		assert(baseInstance)
		local verification = generatePreconditionVerify(
			require,
			method,
			{arguments = arguments, this = baseInstance, container = baseInstance.type},
			environment,
			"the " .. string.ordinal(i) .. " `requires` condition for method " .. methodFullName,
			location
		)
		table.insert(evaluation, verification)
	end

	table.insert(evaluation, {
		tag = "method-call",
		baseInstance = baseInstance,
		arguments = arguments,
		destinations = destinations,
		returns = "no",
		signature = method,
	})

	-- Generate Assume statements
	for _, ensure in ipairs(method.ensuresAST) do
		local assumption = generatePostconditionAssume(
			ensure,
			method,
			{
				arguments = arguments,
				this = baseInstance,
				container = baseInstance.type,
			},
			environment,
			destinations
		)
		table.insert(evaluation, assumption)
	end

	return buildBlock(evaluation), freeze(destinations)
end

-- RETURNS StatementIR, [VariableIR]
local function compileStatic(t, argumentSources, funcName, bang, location, environment)
	assertis(t, "Type+")
	assertis(argumentSources, listType "VariableIR")
	assertis(funcName, "string")
	assertis(bang, "boolean")
	assertis(location, "Location")
	assertis(environment, recordType {})

	local allDefinitions = environment.allDefinitions
	local containingSignature = environment.containingSignature
	local containerType = environment.containerType
	local containingDefinition = definitionFromType(containerType, allDefinitions)

	if t.tag == "generic+" then
		-- Generic static function
		local static = findConstraintByMember(
			t,
			"static",
			funcName,
			t.location,
			containingDefinition.generics,
			environment
		)
		assert(static and static.signature.modifier == "static")
		assertis(static.constraint, "InterfaceType+")

		-- Map type variables to the type-values used for this instantiation
		local substituter = getSubstituterFromInterface(static.constraint, t, allDefinitions)

		local fullName = static.fullName

		-- Check the number of parameters
		if #argumentSources ~= #static.signature.parameters then
			Report.WRONG_VALUE_COUNT {
				purpose = "interface static `" .. fullName .. "`",
				expectedCount = #static.signature.parameters,
				givenCount = #argumentSources,
				location = location,
			}
		end

		-- Verify the argument types match the parameter types
		for i, argument in ipairs(argumentSources) do
			local parameterType = substituter(static.signature.parameters[i].type)
			if not areTypesEqual(argument.type, parameterType) then
				Report.TYPES_DONT_MATCH {
					purpose = string.ordinal(i) .. " argument to `" .. fullName .. "`",
					expectedLocation = static.signature.parameters[i].location,
					givenType = showType(argument.type),
					location = argument.location,
					expectedType = showType(parameterType)
				}
			end
		end

		-- Create variables for the output
		local evaluation = {}
		local destinations = {}
		for _, returnType in ipairs(static.signature.returnTypes) do
			local returnVariable = generateVariable("gs_return", substituter(returnType), location)
			table.insert(destinations, returnVariable)
			table.insert(evaluation, localSt(returnVariable))
		end

		-- Verify the bang matches
		if not static.signature.bang ~= not bang then
			Report.BANG_MISMATCH {
				modifier = static.signature.modifier,
				fullName = fullName,
				expected = static.signature.bang,
				given = bang,
				signatureLocation = static.signature.location,
				location = location,
			}
		elseif static.signature.bang and not containingSignature.bang then
			Report.BANG_NOT_ALLOWED {
				context = containingSignature.modifier .. " " .. fullName,
				location = location,
			}
		end

		-- Generate Verify statements
		for i, require in ipairs(static.signature.requiresAST) do
			local verification = generatePreconditionVerify(
				require,
				static.signature,
				{arguments = argumentSources, this = false},
				environment,
				"the " .. string.ordinal(i) .. " `requires` condition for static " .. fullName,
				location
			)
			table.insert(evaluation, verification)
		end

		local callSt = {
			tag = "generic-static-call",
			constraint = static.constraintIR,
			arguments = argumentSources,
			destinations = destinations,
			returns = "no",
			signature = static.signature,
		}
		assertis(callSt, "StatementIR")
		table.insert(evaluation, callSt)

		print("TODO: this should be replaced with a forall so that it is not recursive")
		-- Generate Assume statements
		for _, ensure in ipairs(static.signature.ensuresAST) do
			local assumption = generatePostconditionAssume(
				ensure,
				static.signature,
				{arguments = argumentSources, this = false, container = t},
				environment,
				destinations
			)
			table.insert(evaluation, assumption)
		end

		return buildBlock(evaluation), freeze(destinations)
	end

	local baseDefinition = definitionFromType(t, allDefinitions)

	local fullName = showType(t) .. "." .. funcName

	-- Map type variables to the type-values used for this instantiation
	local substituter = getSubstituterFromConcreteType(t, allDefinitions)

	local method = table.findwith(baseDefinition.signatures, "name", funcName)

	if not method or method.modifier ~= "static" then
		local alternatives = table.map(table.getter "name", baseDefinition.signatures)
		Report.NO_SUCH_METHOD {
			modifier = "static",
			type = showType(t),
			name = funcName,
			definitionLocation = baseDefinition.location,
			alternatives = alternatives,
			location = location,
		}
	end

	-- Check the number of parameters
	if #method.parameters ~= #argumentSources then
		Report.WRONG_VALUE_COUNT {
			purpose = "static function `" .. fullName .. "`",
			expectedCount = #method.parameters,
			givenCount = #argumentSources,
			location = location,
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
			constraints[key] = constraintFromStruct(
				constraint.interface,
				t.arguments[gi],
				containingDefinition.generics,
				containingSignature,
				environment,
				constraint.location
			)
		end
	end

	-- Verify the bang matches
	if not method.bang ~= not bang then
		Report.BANG_MISMATCH {
			modifier = method.modifier,
			fullName = fullName,
			expected = method.bang,
			given = bang,
			signatureLocation = method.location,
			location = location,
		}
	elseif method.bang and not containingSignature.bang then
		local fullName = containerType.name .. "." .. containingSignature.name
		Report.BANG_NOT_ALLOWED {
			context = containingSignature.modifier .. " " .. fullName,
			location = location,
		}
	end

	-- Create variables for the output
	local evaluation = {}
	local outs = {}
	for _, returnType in ipairs(method.returnTypes) do
		local returnVariable = generateVariable(method.name .. "_result", substituter(returnType), location)
		table.insert(outs, returnVariable)
		table.insert(evaluation, localSt(returnVariable))
	end

	-- Generate Verify statements
	for i, require in ipairs(method.requiresAST) do
		local verification = generatePreconditionVerify(
			require,
			method,
			{arguments = argumentSources, this = false, container = t},
			environment,
			"the " .. string.ordinal(i) .. " `requires` condition for static " .. fullName,
			location
		)
		table.insert(evaluation, verification)
	end

	local call = {
		tag = "static-call",
		baseType = t,
		arguments = argumentSources,
		constraints = constraints,
		destinations = outs,
		returns = "no",
		signature = method,
	}
	assertis(call, "StaticCallSt")
	table.insert(evaluation, call)

	-- Generate Assume statements
	for _, ensure in ipairs(method.ensuresAST) do
		local assumption = generatePostconditionAssume(
			ensure,
			method,
			{arguments = argumentSources, this = false, container = t},
			environment,
			outs
		)
		table.insert(evaluation, assumption)
	end

	return buildBlock(evaluation), freeze(outs)
end

-- RETURNS StatementIR, [Variable]
function compileExpression(pExpression, scope, environment)
	assertis(pExpression, recordType {tag = "string"})

	--assertis(scope, listType(mapType("string", "VariableIR")))
	assertis(environment, recordType {
		resolveType = "function",
		containerType = "Type+",
		containingSignature = "Signature",
		allDefinitions = listType "Definition",
		thisVariable = choiceType(constantType(false), "VariableIR"),
	})
	local resolveType = environment.resolveType
	local containerType = environment.containerType
	local allDefinitions = environment.allDefinitions
	local containingDefinition = definitionFromType(containerType, allDefinitions)
	local containingSignature = environment.containingSignature

	if pExpression.tag == "string-literal" then
		local out, outDef = generateVariable("stringliteral", STRING_TYPE, pExpression.location)

		local block = buildBlock {
			outDef,
			freeze {
				tag = "string",
				string = pExpression.value,
				destination = out,
				returns = "no",
			},
		}
		return block, freeze {out}
	elseif pExpression.tag == "int-literal" then
		local out, outDef = generateVariable("intliteral", INT_TYPE, pExpression.location)

		local block = buildBlock {
			outDef,
			{
				tag = "int",
				number = pExpression.value,
				destination = out,
				returns = "no",
			}
		}
		return block, freeze {out}
	elseif pExpression.tag == "new-expression" then
		local location = pExpression.location

		-- All of the constraints are provided as arguments to this
		-- static function
		local constraints = {}
		for constraintName, interface in spairs(containingDefinition.constraints) do
			constraints[constraintName] = freeze {
				tag = "parameter-constraint",
				name = constraintName,
				location = location,
				interface = interface,
			}
		end

		local constituents = {}
		for _, argument in ipairs(pExpression.arguments) do
			table.insert(constituents, argument.value)
		end
		local subEvaluation, fieldValues = compileSubexpressions(
			constituents,
			"arguments to new " .. showType(containerType),
			location,
			scope,
			environment
		)

		local map = {}
		local memberDefinitions = {}
		for i, value in ipairs(fieldValues) do
			local pArgument = pExpression.arguments[i]
			local fieldName = pArgument.name
			local field = table.findwith(containingDefinition.fields, "name", fieldName)
			if not field then
				Report.NO_SUCH_FIELD {
					name = fieldName,
					container = showType(containerType),
					location = pArgument.location,
				}
			end

			memberDefinitions[fieldName] = field
			map[fieldName] = value

			if not areTypesEqual(field.type, value.type) then
				Report.TYPES_DONT_MATCH {
					purpose = "field type",
					expectedType = showType(field.type),
					expectedLocation = field.location,
					givenType = showType(value.type),
					location = pArgument.location,
				}
			end
		end

		local out = generateVariable("new", containerType, location)
		local newSt = {
			tag = "new-" .. containingDefinition.tag,
			type = containerType,
			returns = "no",
			constraints = constraints,
			destination = out,
			location = location,
		}

		-- Record the map as fields
		if containingDefinition.tag == "union" then
			newSt.field, newSt.value = next(map)
			newSt.variantDefinition = memberDefinitions[newSt.field]

			-- Verify that exactly one field is given for union new
			if #fieldValues ~= 1 then
				Report.WRONG_VALUE_COUNT {
					purpose = "new union field list",
					expectedCount = 1,
					givenCount = #fieldValues,
					location = location,
				}
			end
		elseif containingDefinition.tag == "class" then
			newSt.fields = map
			newSt.memberDefinitions = memberDefinitions

			-- Check that no fields are missing for class new
			for _, field in ipairs(containingDefinition.fields) do
				if not newSt.fields[field.name] then
					Report.MISSING_VALUE {
						purpose = "new " .. showType(containerType) .. " expression",
						name = field.name,
						location = location,
					}
				end
			end
		end

		local block = buildBlock {subEvaluation, localSt(out), newSt}
		return block, freeze {out}
	elseif pExpression.tag == "identifier" then
		local block = buildBlock({})
		local found = nil
		for i = #scope, 1, -1 do
			found = found or scope[i][pExpression.name]
		end
		if not found then
			Report.NO_SUCH_VARIABLE {
				name = pExpression.name,
				location = pExpression.location,
			}
		end
		local out = freeze {
			name = found.name,
			type = found.type,
			location = pExpression.location,
			description = false,
		}
		return block, freeze {out}
	elseif pExpression.tag == "static-call" then
		local t = resolveType(pExpression.baseType)
		local n = pExpression.funcName
		local location = pExpression.location

		local argumentEvaluation, argumentSources = compileSubexpressions(
			pExpression.arguments,
			"argument to static " .. n,
			location,
			scope,
			environment
		)

		local invocation, out = compileStatic(t, argumentSources, n, pExpression.bang, location, environment)
		return buildBlock {argumentEvaluation, invocation}, out
	elseif pExpression.tag == "method-call" then
		local n = pExpression.methodName
		local location = pExpression.location

		local subEvaluation, subSources = compileSubexpressions(
			{pExpression.base, unpack(pExpression.arguments)},
			"base/argument to method " .. n,
			location,
			scope,
			environment
		)

		local baseInstance = subSources[1]
		local arguments = table.rest(subSources, 2)

		local call, out = compileMethod(baseInstance, arguments, n, pExpression.bang, location, environment)
		return buildBlock {subEvaluation, call}, out
	elseif pExpression.tag == "keyword" then
		if pExpression.keyword == "false" or pExpression.keyword == "true" then
			local boolean = generateVariable("booleanliteral", BOOLEAN_TYPE, pExpression.location)
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
			-- Check that this is a method
			if containingSignature.modifier ~= "method" then
				Report.THIS_USED_OUTSIDE_METHOD {
					location = pExpression.location,
				}
			end

			-- Annotated the variable with the current location
			local thisV = table.with(environment.thisVariable, "location", pExpression.location)

			return buildBlock {}, {thisV}
		elseif pExpression.keyword == "unit" then
			local variable = generateVariable("unit", UNIT_TYPE, pExpression.location)
			local execution = {
				localSt(variable),
				{
					tag = "unit",
					destination = variable,
					returns = "no",
				}
			}
			return buildBlock(execution), freeze {variable}
		elseif pExpression.keyword == "return" then
			local returns = environment.containingSignature.returnTypes

			if #returns ~= 1 then
				Report.WRONG_VALUE_COUNT {
					purpose = "`return` expression",
					expectedCount = 1,
					givenCount = #returns,
					location = pExpression.location,
				}
			elseif not environment.returnOuts then
				Report.RETURN_USED_IN_IMPLEMENTATION {location = pExpression.location}
			end
			assert(#returns == #environment.returnOuts)

			return buildBlock {}, freeze(environment.returnOuts)
		end
		error("TODO: keyword `" .. pExpression.keyword .. "`")
	elseif pExpression.tag == "field" then
		local baseEvaluation, bases = compileExpression(pExpression.base, scope, environment)
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
				purpose = "base of `." .. pExpression.field .. "` field access",
				givenType = showType(base.type),
				location = pExpression.location,
			}
		end

		local substituter = getSubstituterFromConcreteType(base.type, allDefinitions)
		local definition = definitionFromType(base.type, allDefinitions)
		if definition.tag == "class" then
			-- Class field access
			local field = table.findwith(definition.fields, "name", pExpression.field)
			if not field then
				Report.NO_SUCH_FIELD {
					container = showType(base.type),
					name = pExpression.field,
					location = pExpression.location,
				}
			end

			-- TODO: verify that access is to the current class

			local result = generateVariable("field", substituter(field.type), pExpression.location)
			local accessStatement = {
				tag = "field",
				name = pExpression.field,
				base = base,
				destination = result,
				returns = "no",
				fieldDefinition = field,
			}

			local block = buildBlock {
				baseEvaluation,
				localSt(result),
				accessStatement,
			}
			return block, freeze {result}
		elseif definition.tag == "union" then
			-- Union variant access
			local field = table.findwith(definition.fields, "name", pExpression.field)
			if not field then
				Report.NO_SUCH_VARIANT {
					container = definition.name,
					name = pExpression.field,
					location = pExpression.location,
				}
			end

			local result = generateVariable("variant", substituter(field.type), pExpression.location)
			local access = {
				tag = "variant",
				variant = pExpression.field,
				base = base,
				destination = result,
				returns = "no",
				variantDefinition = field,
			}

			-- Assert that the union variable comes from a closed set
			local assumeUnion = closedUnionAssumption(definition, base)

			local isVar = generateVariable("variantis", BOOLEAN_TYPE, pExpression.location)
			local isStatement = {
				tag = "isa",
				base = base,
				destination = isVar,
				variant = pExpression.field,
				returns = "no",
			}
			local verify = {
				tag = "verify",
				variable = isVar,
				checkLocation = pExpression.location,
				conditionLocation = pExpression.location,
				reason = "base is a `" .. pExpression.field .. "`",
				returns = "no",
			}

			local block = buildBlock {
				baseEvaluation,
				buildProof(buildBlock {
					assumeUnion,
					localSt(isVar),
					isStatement,
					verify,
				}),
				localSt(result),
				access,
			}

			return block, freeze {result}
		else
			Report.TYPE_MUST_BE_CLASS {
				purpose = "base of the `." .. pExpression.field .. "` field access",
				givenType = showType(base.type),
				location = pExpression.location,
			}
		end
	elseif pExpression.tag == "binary" then
		-- Compile the two operands
		profile.open("compileExpression binary recursive")
		local leftEvaluation, leftOut = compileExpression(pExpression.left, scope, environment)
		local rightEvaluation, rightOut = compileExpression(pExpression.right, scope, environment)
		profile.close("compileExpression binary recursive")

		if not isExprPure(pExpression.left) and not isExprPure(pExpression.right) then
			Report.EVALUATION_ORDER {
				location = pExpression.location,
			}
		end

		-- Verify there is one value on each side
		if #leftOut ~= 1 then
			Report.WRONG_VALUE_COUNT {
				purpose = "the left operand of `" .. pExpression.operator .. "`",
				expectedCount = 1,
				givenCount = #leftOut,
				location = pExpression.left.location,
			}
		elseif #rightOut ~= 1 then
			Report.WRONG_VALUE_COUNT {
				purpose = "the right operand of `" .. pExpression.operator .. "`",
				expectedCount = 1,
				givenCount = #rightOut,
				location = pExpression.right.location,
			}
		end

		local left, right = leftOut[1], rightOut[1]

		-- Handle specific operators
		if pExpression.operator == "==" then
			-- Check that the values are of the same type
			if not areTypesEqual(left.type, right.type) then
				Report.EQ_TYPE_MISMATCH {
					leftType = showType(left.type),
					rightType = showType(right.type),
					location = pExpression.location,
				}
			end
		end

		local operatorAsMethodName = OPERATOR_ALIAS[pExpression.operator]
		if not operatorAsMethodName then
			return Report.UNKNOWN_OPERATOR_USED {
				operator = pExpression.operator,
				location = pExpression.location,
			}
		end

		-- Rewrite the operations as a method call
		local callEvaluation, callOut = compileMethod(
			left, {right}, operatorAsMethodName, false, pExpression.location, environment
		)
		return buildBlock {leftEvaluation, rightEvaluation, callEvaluation}, callOut
	elseif pExpression.tag == "isa" then
		local baseEvaluation, baseOut = compileExpression(pExpression.base, scope, environment)
		if #baseOut ~= 1 then
			Report.WRONG_VALUE_COUNT {
				purpose = "`is " .. pExpression.variant .. "` expression",
				expectedCount = 1,
				givenCount = #baseOut,
				location = pExpression.location,
			}
		end
		local base = baseOut[1]
		local baseDefinition = definitionFromType(base.type, allDefinitions)
		if baseDefinition.tag ~= "union" then
			Report.TYPE_MUST_BE_UNION {
				purpose = "base of a `is " .. pExpression.variant .. "` expression",
				givenType = showType(base.type),
				location = pExpression.location,
			}
		end

		local result = generateVariable("isa", BOOLEAN_TYPE, pExpression.location)

		local isA = freeze {
			tag = "isa",
			destination = result,
			base = base,
			variant = pExpression.variant,
			returns = "no",
		}

		-- Check that a variant of this name exists for this union type
		local found = false
		for _, field in ipairs(baseDefinition.fields) do
			if field.name == pExpression.variant then
				found = true
			end
		end

		if not found then
			Report.NO_SUCH_VARIANT {
				container = showType(base.type),
				name = pExpression.variant,
				location = pExpression.location,
			}
		end

		local isUnion = buildProof(closedUnionAssumption(baseDefinition, base))

		return buildBlock {baseEvaluation, isUnion, localSt(result), isA}, freeze {result}
	elseif pExpression.tag == "forall-expr" then
		-- TODO: check that this is in a ghost context

		local scopeCopy = {}

		-- Check that the name is fresh
		for _, frame in ipairs(scope) do
			if frame[pExpression.variable.name] then
				Report.VARIABLE_DEFINED_TWICE {
					name = pExpression.variable.name,
					first = frame[pExpression.variable.name].location,
					second = pExpression.variable.location,
				}
			end
			local frameCopy = {}
			for key, value in pairs(frame) do
				frameCopy[key] = value
			end
			table.insert(scopeCopy, frameCopy)
		end

		-- RETURNS StatementIR, VariableIR (how to execute for this target, and
		-- what the result was)
		local function instantiate(target)
			table.insert(scopeCopy, {[pExpression.variable.name] = target})
			local code, predicates = compileExpression(
				pExpression.predicate,
				scopeCopy,
				environment
			)

			local instantiatedResult = generateVariable(
				"forall_result_" .. pExpression.variable.name,
				BOOLEAN_TYPE,
				pExpression.location
			)

			-- Check types
			checkSingleBoolean(predicates, "forall predicate")

			-- Move the result into the instantiated result
			local move = freeze {
				tag = "assign",
				destination = instantiatedResult,
				source = predicates[1],
				returns = "no",
			}
			code = buildBlock {code, move}

			if pExpression.when then
				local whenEval, whenVars = compileExpression(
					pExpression.when,
					scopeCopy,
					environment
				)

				checkSingleBoolean(whenVars, "forall when")

				-- Assume the when is true inside the if guard
				local assumePredicate = freeze {
					tag = "assume",
					variable = whenVars[1],
					location = whenVars[1].location,
					returns = "no",
				}

				-- The result is true when the guard is false (vacuously)
				local vacuous = freeze {
					tag = "boolean",
					boolean = true,
					destination = instantiatedResult,
					returns = "no",
				}

				-- Guard the execution in an if
				local ifSt = freeze {
					tag = "if",
					condition = whenVars[1],
					bodyThen = buildBlock {assumePredicate, code},
					bodyElse = vacuous,
					returns = "no",
				}

				code = buildBlock {whenEval, ifSt}
			end

			-- Close the variable's scope
			table.remove(scopeCopy)

			return code, instantiatedResult
		end

		-- Generate the code once to verify that it is valid
		-- (In particular, that preconditions hold!)
		-- Bring the variable into scope
		local variable1 = generateVariable(
			pExpression.variable.name,
			resolveType(pExpression.variable.type),
			pExpression.variable.location
		)
		local testInstantiation = instantiate(variable1)

		local result = generateVariable(
			"forall_" .. pExpression.variable.name,
			BOOLEAN_TYPE,
			pExpression.location
		)

		local forall = freeze {
			tag = "forall",
			destination = result,
			instantiate = instantiate,
			quantified = variable1.type,
			location = pExpression.location,
			returns = "no",
		}
		assertis(forall, "ForallSt")

		if not isExprPure(pExpression.predicate) then
			Report.BANG_NOT_ALLOWED {
				context = "forall predicate",
				location = pExpression.location,
			}
		elseif pExpression.when and not isExprPure(pExpression.when) then
			Report.BANG_NOT_ALLOWED {
				context = "forall when",
				location = pExpression.location,
			}
		end

		local out = buildBlock {
			localSt(variable1),
			testInstantiation,
			localSt(result),
			forall,
		}

		return out, freeze {result}
	end

	error("TODO expression")
end
local _compileExpression = compileExpression
local level = 0
compileExpression = function(p, ...)
	--local indent = string.rep("\t", level)
	--print(show(p):gsub("\n", "\n" .. indent))
	level = level + 1
	profile.open("compileExpression tag=" .. p.tag)
	local a, b = _compileExpression(p, ...)
	profile.close("compileExpression tag=" .. p.tag)
	level = level - 1
	return a, b
end

local function typeFromDefinition(definition)
	assertis(definition, choiceType("ClassIR", "UnionIR"))

	return freeze {
		tag = "concrete-type+",
		name = definition.name,
		arguments = table.map(
			function(p)
				return freeze {
					tag = "generic+",
					name = p.name,
					location = definition.location,
				}
			end,
			definition.generics
		),
		location = definition.location,
	}
end

-- RETURNS a type-resolving function (Parsed Type => Type+)
local function makeTypeResolver(containingSignature, generics, allDefinitions)
	assertis(containingSignature, "Signature")
	assertis(generics, listType "any")
	assertis(allDefinitions, listType "Definition")

	-- RETURNS a (verified) Type+
	return function(parsedType)
		local typeScope = generics
		local outType = containingSignature.resolveType(parsedType, typeScope)
		verifyTypeValid(outType, generics, allDefinitions)
		return outType
	end
end

--------------------------------------------------------------------------------

-- RETURNS a Semantics, an IR description of the program
local function semanticsSmol(sources, main)
	assertis(main, "string")

	profile.open "resolve types"

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

				return freeze {
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

				return freeze {
					tag = "generic+",
					name = t.name,
					location = t.location,
				}
			elseif t.tag == "type-keyword" then
				return freeze {
					tag = "keyword-type+",
					name = t.name,
					location = t.location,
				}
			elseif t.tag == "keyword-generic" then
				assert(t.name == "Self")
				return freeze {
					tag = "self-type+",
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
				location = "Location",
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

		-- RETURNS a Signature
		local function compiledSignature(signature, scope, foreign)
			--assertis(scope, listType("TypeParameterIR"))
			assertis(foreign, "boolean")

			return freeze {
				foreign = foreign,
				modifier = signature.modifier.keyword,
				name = signature.name,
				returnTypes = freeze(table.map(resolveType, signature.returnTypes, scope)),
				parameters = freeze(table.map(
					function(p)
						return freeze {
							name = p.name,
							type = resolveType(p.type, scope),
							location = p.location,
							description = false,
						}
					end,
					signature.parameters
				)),
				location = signature.location,
				bang = signature.bang,
				ensuresAST = signature.ensures,
				requiresAST = signature.requires,
				scope = scope,

				-- TODO: total boolean functions might have this computed:
				logic = false,

				-- TODO: total functions might have this computed:
				eval = false,
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
					location = generics.location,
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
				function(x)
					return {name = x}
				end,
				generics.parameters
			)

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

			return freeze(parametersOut)
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

				table.insert(fields, freeze {
					name = field.name,
					type = resolveType(field.type, generics),
					location = field.location,
					description = false,
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

			assertis(fields, listType "VariableIR")
			assertis(signatures, listType "Signature")

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
			local fullName = package .. ":" .. definition.name

			-- Create the generics
			local generics = compiledGenerics(definition.generics)

			local signatures = table.map(
				function(raw)
					local compiled = compiledSignature(raw, generics, false)
					return table.with(compiled, "container", fullName)
				end,
				definition.signatures
			)

			assertis(signatures, listType "Signature")

			return freeze {
				tag = "interface",
				name = fullName,
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

	profile.close "resolve types"
	profile.open "check implements"

	allDefinitions = freeze(allDefinitions)
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
			local classType = typeFromDefinition(class, allDefinitions)
			local subs = getSubstituterFromInterface(int, classType, allDefinitions)

			-- Check that each signature matches
			for _, iSignature in ipairs(interface.signatures) do
				-- Search for a method/static with the same name, if any
				local cSignature = table.findwith(class.signatures, "name", iSignature.name)
				if not cSignature then
					Report.INTERFACE_REQUIRES_MEMBER {
						class = class.name,
						interface = showInterfaceType(int),
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
						interface = showInterfaceType(int),
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
						interface = showInterfaceType(int),
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
							interface = showInterfaceType(int),
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
						interface = showInterfaceType(int),
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

	profile.close "check implements"
	profile.open "check prototypes"

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

	profile.close "check prototypes"
	profile.open "check ensures"

	-- (4.5) Verify the type of all ensures/requires
	for _, definition in ipairs(allDefinitions) do
		profile.open("check ensures of " .. definition.name)
		if definition.tag == "class" or definition.tag == "union" then
			for _, signature in ipairs(definition.signatures) do
				-- Verify the type of the signature's ensures and requires
				local scope = {{}}
				for _, parameter in ipairs(signature.parameters) do
					scope[1][parameter.name] = parameter
				end

				local containerType = typeFromDefinition(definition)
				local thisVariable = false
				if signature.modifier == "method" then
					thisVariable = freeze {
						location = UNKNOWN_LOCATION,
						name = "this",
						type = containerType,
						description = "this",
					}
				end

				local returnOuts = {}
				for i, returned in ipairs(signature.returnTypes) do
					table.insert(returnOuts, {
						location = UNKNOWN_LOCATION,
						name = "_r" .. i,
						type = returned,
						description = "return#" .. i,
					})
				end

				local environment = freeze {
					resolveType = makeTypeResolver(signature, definition.generics, allDefinitions),
					containerType = containerType,
					containingSignature = signature,
					allDefinitions = allDefinitions,
					thisVariable = thisVariable,
					returnOuts = returnOuts,
				}

				local function checkBoolean(e, purpose)
					assertis(purpose, "string")

					local _, outs = compileExpression(e, scope, environment)
					checkSingleBoolean(outs, purpose, e.location)
				end

				-- Check that each requires has type Boolean
				for _, requires in ipairs(signature.requiresAST) do
					checkBoolean(requires.condition, "requires condition")
					for _, when in ipairs(requires.whens) do
						checkBoolean(when, "requires when condition")
						if not isExprPure(when) then
							Report.BANG_NOT_ALLOWED {
								context = "requires-when",
								location = when.location,
							}
						end
					end
					if not isExprPure(requires.condition) then
						Report.BANG_NOT_ALLOWED {
							context = "requires",
							location = requires.condition.location,
						}
					end
				end

				-- Check that each ensures has type Boolean
				for _, ensures in ipairs(signature.ensuresAST) do
					checkBoolean(ensures.condition, "ensures condition")
					for _, when in ipairs(ensures.whens) do
						checkBoolean(when, "ensures when condition")
						if not isExprPure(when) then
							Report.BANG_NOT_ALLOWED {
								context = "ensures-when",
								location = when.location,
							}
						end
					end
					if not isExprPure(ensures.condition) then
						Report.BANG_NOT_ALLOWED {
							context = "ensures",
							location = ensures.condition.location,
						}
					end
				end
			end
		end
		profile.close("check ensures of " .. definition.name)
	end

	profile.close "check ensures"
	profile.open "compile bodies"

	-- (5) Compile all code bodies

	-- RETURNS a FunctionIR
	local function compileFunctionFromStruct(definition, containingSignature)
		assertis(definition, choiceType("ClassIR", "UnionIR"))
		assertis(containingSignature, "Signature")

		local containerType = typeFromDefinition(definition)

		local thisVariable = false
		if containingSignature.modifier == "method" then
			thisVariable = freeze {
				name = "this",
				type = containerType,
				location = UNKNOWN_LOCATION,
				description = "this",
			}
		end
		local resolveType = makeTypeResolver(
			containingSignature,
			definition.generics,
			allDefinitions
		)

		local environment = freeze {
			resolveType = resolveType,
			containerType = containerType,
			containingSignature = containingSignature,
			allDefinitions = allDefinitions,
			thisVariable = thisVariable,
			returnOuts = false,
		}

		local compileBlock

		-- RETURNS a StatementIR
		local function verifyForEnsures(scope, returnOuts, location)
			assertis(returnOuts, listType "VariableIR")
			assertis(scope, listType(mapType("string", "VariableIR")))
			assertis(location, "Location")

			local sequence = {}

			-- Check that all ensured statements are true at this point
			for i, ensures in ipairs(containingSignature.ensuresAST) do
				local arguments = {}
				for _, a in ipairs(containingSignature.parameters) do
					table.insert(arguments, getFromScope(scope, a.name))
				end

				local sub = table.with(environment, "returnOuts", returnOuts)

				local context = "the " .. string.ordinal(i) .. " `ensures` condition for " .. containingSignature.name
				local verify = generatePreconditionVerify(
					ensures,
					containingSignature,
					{
						arguments = arguments,
						this = thisVariable,
						container = containerType
					},
					sub,
					context,
					location
				)

				assertis(verify, "StatementIR")
				table.insert(sequence, verify)
			end
			return buildBlock(sequence)
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
						type = resolveType(pVariable.type),
						location = pVariable.location,
						description = false,
					}

					scope[#scope][variable.name] = variable
					table.insert(declarations, {
						tag = "local",
						variable = variable,
						returns = "no",
					})
				end

				-- Evaluate the right hand side
				local evaluation, values = compileExpression(pStatement.value, scope, environment)

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
				local sequence = table.concatted(declarations, {evaluation}, moves)
				return buildBlock(sequence)
			elseif pStatement.tag == "return-statement" then
				local sources = {}
				local evaluation = {}
				if #pStatement.values == 1 then
					-- A single value must have exactly the target multiplicity
					local subEvaluation, subsources = compileExpression(
						pStatement.values[1],
						scope,
						environment
					)

					if #subsources ~= #containingSignature.returnTypes then
						Report.RETURN_COUNT_MISMATCH {
							signatureCount = #containingSignature.returnTypes,
							returnCount = #subsources,
							location = pStatement.location,
						}
					end

					table.insert(evaluation, subEvaluation)
					sources = subsources
				elseif #pStatement.values == 0 then
					-- Returning no values is equivalent to returning one unit
					local unitVariable = generateVariable("unit_return", UNIT_TYPE, pStatement.location)
					local execution = buildBlock {
						localSt(unitVariable),
						{
							tag = "unit",
							destination = unitVariable,
							returns = "no",
						}
					}
					table.insert(evaluation, execution)
					table.insert(sources, unitVariable)
				else
					-- If multiple values are given, each must be a 1-tuple
					for _, value in ipairs(pStatement.values) do
						local subevaluation, subsources = compileExpression(
							value,
							scope,
							environment
						)
						if #subsources ~= 1 then
							Report.WRONG_VALUE_COUNT {
								purpose = "expression in multiple-value return statement",
								expectedCount = 1,
								givenCount = #subsources,
								location = value.location,
							}
						end

						table.insert(sources, subsources[1])
						table.insert(evaluation, subevaluation)
					end
				end

				-- Generate an ensures
				table.insert(evaluation, verifyForEnsures(scope, sources, pStatement.location))

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
				local evaluation, out = compileExpression(pStatement.expression, scope, environment)
				assert(#out ~= 0)
				if #out > 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "do-statement expression",
						expectedCount = 1,
						givenCount = #out,
						location = pStatement.location,
					}
				elseif not areTypesEqual(out[1].type, UNIT_TYPE) then
					Report.EXPECTED_DIFFERENT_TYPE {
						purpose = "do-statement expression",
						expectedType = "Unit",
						givenType = showType(out[1].type),
						location = pStatement.expression.location,
					}
				end

				return evaluation
			elseif pStatement.tag == "if-statement" then
				local conditionEvaluation, conditionOut = compileExpression(
					pStatement.condition,
					scope,
					environment
				)
				assert(#conditionOut ~= 0)
				checkSingleBoolean(
					conditionOut,
					"if-statement condition",
					pStatement.condition.location
				)

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
					local elseIfConditionEvaluation, elseIfConditionOut = compileExpression(
						pStatement.elseifs[i].condition,
						scope,
						environment
					)
					assert(#elseIfConditionOut ~= 0)
					checkSingleBoolean(elseIfConditionOut, "else-if-statement condition")

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
			elseif pStatement.tag == "match-statement" then
				-- Evaluate the base expression
				local baseEvaluation, baseOuts = compileExpression(
					pStatement.base,
					scope,
					environment
				)
				if #baseOuts ~= 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "match-statement expression",
						expectedCount = 1,
						givenCount = #baseOuts,
						location = pStatement.base.location,
					}
				end

				local base = baseOuts[1]
				assertis(base, "VariableIR")

				-- Check that the base is a union
				if base.type.tag ~= "concrete-type+" then
					Report.TYPE_MUST_BE_UNION {
						purpose = "expression in match-statement",
						givenType = showType(base.type),
						location = pStatement.base.location,
					}
				end
				local definition = definitionFromType(base.type, allDefinitions)
				if definition.tag ~= "union" then
					Report.TYPE_MUST_BE_UNION {
						purpose = "expression in match-statement",
						givenType = showType(base.type),
						location = pStatement.base.location,
					}
				end
				assertis(definition, "UnionIR")

				-- Check that the fields exist and are distinct
				local unionSubstituter = getSubstituterFromConcreteType(base.type, allDefinitions)
				local cases = {}
				for _, case in ipairs(pStatement.cases) do
					-- Create a subscope
					table.insert(scope, {})
					local sequence = {}

					-- Verify that the variable name is not in scope
					local previous = getFromScope(scope, case.head.variable)
					if previous then
						Report.VARIABLE_DEFINED_TWICE {
							first = previous.location,
							second = case.head.location,
							name = case.head.variable,
						}
					end

					-- Get the field
					local field = table.findwith(definition.fields, "name", case.head.variant)
					if not field then
						Report.NO_SUCH_VARIANT {
							container = showType(base.type),
							name = case.head.variable,
							location = case.head.location,
						}
					end
					local previous = table.findwith(cases, "variant", field.name)
					if previous then
						Report.VARIANT_USED_TWICE {
							variant = field.name,
							firstLocation = previous.location,
							secondLocation = case.head.location,
						}
					end

					-- Add the variable to the current scope
					local variable = {
						name = case.head.variable,
						type = unionSubstituter(field.type),
						location = case.head.location,
						description = false,
					}

					scope[#scope][variable.name] = variable
					table.insert(sequence, {
						tag = "local",
						variable = variable,
						returns = "no",
					})

					table.insert(sequence, {
						tag = "variant",
						variant = case.head.variant,
						base = base,
						destination = variable,
						returns = "no",
						variantDefinition = field,
					})

					local sub = compileBlock(case.body, scope)
					table.insert(sequence, sub)

					table.remove(scope)
					table.insert(cases, freeze {
						variant = field.name,
						location = case.head.location,
						statement = buildBlock(sequence),
					})
				end

				-- Sort cases by the field order
				table.sort(cases, function(a, b)
					local va = table.findwith(definition.fields, "name", a.variant)
					local vb = table.findwith(definition.fields, "name", b.variant)
					local ia = table.indexof(definition.fields, va)
					local ib = table.indexof(definition.fields, vb)
					return ia < ib
				end)

				-- Check exhaustivity
				local unhandledVariants = {}
				for _, field in ipairs(definition.fields) do
					if not table.findwith(cases, "variant", field.name) then
						table.insert(unhandledVariants, field.name)
					end
				end

				local verification

				-- Check for inexhaustivity
				if #unhandledVariants ~= 0 then
					local seq = {
						closedUnionAssumption(definition, base),
					}

					for _, variant in ipairs(unhandledVariants) do
						local isBad = generateVariable("isBad_" .. variant, BOOLEAN_TYPE, pStatement.location)
						table.insert(seq, localSt(isBad))
						table.insert(seq, {
							tag = "isa",
							base = base,
							destination = isBad,
							variant = variant,
							returns = "no",
						})

						local isNotBadSt, isNotBad = irMethod(pStatement.location, NOT_SIGNATURE, isBad, {})
						table.insert(seq, isNotBadSt)

						table.insert(seq, {
							tag = "verify",
							variable = isNotBad,
							checkLocation = pStatement.location,
							conditionLocation = pStatement.location,
							reason = "exhaustivity of match",
							returns = "no",
						})
					end
					verification = buildProof(buildBlock(seq))
				else
					verification = buildProof(closedUnionAssumption(definition, base))
				end

				-- Determine if this match returns or not
				local noCount, yesCount = 0, 0
				for _, case in ipairs(cases) do
					if case.statement.returns == "yes" then
						yesCount = yesCount + 1
					elseif case.statement.returns == "no" then
						noCount = noCount + 1
					else
						assert(case.statement.returns == "maybe")
					end
				end
				local returns
				if noCount == #cases then
					returns = "no"
				elseif yesCount == #cases then
					returns = "yes"
				else
					returns = "maybe"
				end

				local match = freeze {
					tag = "match",
					base = base,
					cases = cases,
					returns = returns,
				}
				return buildBlock {baseEvaluation, verification, match}
			elseif pStatement.tag == "assign-statement" then
				local out = {}

				-- Evaluate the right-hand-side
				local valueEvaluation, valueOut = compileExpression(
					pStatement.value,
					scope,
					environment
				)
				if #valueOut ~= #pStatement.variables then
					Report.WRONG_VALUE_COUNT {
						purpose = "assignment statement",
						expectedCount = #pStatement.variables,
						givenCount = #valueOut,
						location = pStatement.value.location,
					}
				end
				table.insert(out, valueEvaluation)

				-- Check the left hand side
				for i, pVariable in ipairs(pStatement.variables) do
					assertis(pVariable, "string")
					local variable = getFromScope(scope, pVariable)
					if not variable then
						Report.NO_SUCH_VARIABLE {
							name = pVariable,
							location = pStatement.location,
						}
					elseif not areTypesEqual(valueOut[i].type, variable.type) then
						Report.TYPES_DONT_MATCH {
							purpose = string.ordinal(i) .. " value in the assignment statement",
							expectedType = showType(variable.type),
							expectedLocation = variable.location,
							givenType = showType(valueOut[i].type),
						}
					end
					table.insert(out, freeze {
						tag = "assign",
						source = valueOut[i],
						destination = variable,
						returns = "no",
					})
				end

				return buildBlock(out)
			elseif pStatement.tag == "assert-statement" then
				-- Evaluate the right-hand-side
				-- TODO: environment must be annotated to allow `forall`
				local valueEvaluation, valueOut = compileExpression(
					pStatement.expression,
					scope,
					environment
				)
				if #valueOut ~= 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "assert statement",
						expectedCount = 1,
						givenCount = #valueOut,
						location = pStatement.expression.location,
					}
				elseif not areTypesEqual(valueOut[1].type, BOOLEAN_TYPE) then
					Report.TYPES_DONT_MATCH {
						purpose = "expression in assert statement",
						expectedType = "Boolean",
						expectedLocation = pStatement.expression.location,
						givenType = showType(valueOut[1].type),
					}
				end

				if not isExprPure(pStatement.expression) then
					Report.BANG_NOT_ALLOWED {
						context = "assert",
						location = pStatement.location,
					}
				end

				local verify = {
					tag = "verify",
					variable = valueOut[1],
					checkLocation = pStatement.location,
					conditionLocation = pStatement.location,
					reason = "the asserted condition",
					returns = "no",
				}
				assertis(verify, "VerifySt")

				local assume = {
					tag = "assume",
					variable = valueOut[1],
					returns = "no",
					location = pStatement.location,
				}
				assertis(assume, "AssumeSt")

				return buildProof(buildBlock {
					valueEvaluation,
					verify,
					assume,
				})
			end
			error("TODO: compileStatement")
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
						cause = statements[i - 1].location,
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

		-- Create assumptions for all of the hypotheses in `requires` clauses
		local assumptions = {}
		for _, requires in ipairs(containingSignature.requiresAST) do
			assertis(environment.containerType, "Type+")
			table.insert(assumptions, generatePostconditionAssume(
				requires,
				containingSignature,
				{this = thisVariable, arguments = containingSignature.parameters},
				environment,
				false
			))
		end

		local body = false
		if not containingSignature.foreign then
			body = buildBlock {
				initialization,
				buildBlock(assumptions),
				compileBlock(containingSignature.body, functionScope)
			}
			assertis(body, "StatementIR")
			if body.returns ~= "yes" then
				-- An implicit return of unit must be added
				local returns = {}
				for _, returnType in ipairs(containingSignature.returnTypes) do
					table.insert(returns, showType(returnType))
				end
				returns = table.concat(returns, ", ")

				if returns ~= "Unit" then
					-- But only for unit functions
					Report.FUNCTION_DOESNT_RETURN {
						name = containingSignature.container .. ":" .. containingSignature.name,
						modifier = containingSignature.modifier,
						location = containingSignature.body.location,
						returns = returns,
					}
				end

				-- Returning no values is equivalent to returning one unit
				local unitVariable = generateVariable("unit_return", UNIT_TYPE, containingSignature.body.location)
				unitVariable = table.with(unitVariable, "description", "unit")
				local returnSt = {
					tag = "unit",
					destination = unitVariable,
					returns = "no",
				}

				-- Check post conditions
				body = buildBlock {
					body,
					localSt(unitVariable),
					verifyForEnsures(
						functionScope,
						{unitVariable},
						containingSignature.body.location
					),
					returnSt
				}
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

	profile.close "compile bodies"
	profile.open "compile main"

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

	profile.close "compile main"

	return freeze {
		classes = classes,
		builtins = BUILTIN_DEFINITIONS,
		unions = unions,
		interfaces = interfaces,
		functions = functions,
		main = main,
	}
end

return {
	semantics = semanticsSmol,
	showType = showType,
	showInterfaceType = showInterfaceType,
	definitionFromType = definitionFromType,
}
