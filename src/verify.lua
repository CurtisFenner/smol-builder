local calculateSemantics = import "semantics.lua"
local showType = calculateSemantics.showType
local showInterfaceType = calculateSemantics.showInterfaceType

local theorem = import "theorem.lua"
local verifyTheory = import "verify-theory.lua"
local showAssertion = verifyTheory.showAssertion

local Report = import "verify-errors.lua"

local profile = import "profile.lua"

--------------------------------------------------------------------------------

REGISTER_TYPE("Action", choiceType(
	recordType {
		tag = constantType "predicate",
		value = "Assertion",
	},
	recordType {
		tag = constantType "assignment",
		destination = "VariableIR",
		value = "Assertion",
	}
))

REGISTER_TYPE("Assertion", choiceType(
	recordType {
		tag = constantType "tuple",
		index = "integer",
		value = "Assertion",
	},
	recordType {
		tag = constantType "int",
		value = "integer",
	},
	recordType {
		tag = constantType "string",
		value = "string",
	},
	recordType {
		tag = constantType "boolean",
		value = "boolean",
	},
	recordType {
		tag = constantType "this",
	},
	recordType {
		tag = constantType "unit",
	},
	recordType {
		tag = constantType "method",
		base = "Assertion",
		arguments = listType "Assertion",
		methodName = "string",
	},
	recordType {
		tag = constantType "static",
		base = "string",
		arguments = listType "Assertion",
		staticName = "string",
	},
	recordType {
		tag = constantType "variable",
		variable = "VariableIR",
	},
	recordType {
		tag = constantType "new-class",
		type = "string",
		fields = mapType("string", "Assertion"),
	},
	recordType {
		tag = constantType "new-union",
		type = "string",
		field = "string",
		value = "Assertion",
	}
))

local assertionRecursionMap = freeze {
	["new-union"] = {"value"},
	["new-class"] = {"fields{}"},
	["static"] = {"arguments{}"},
	["method"] = {"base", "arguments{}"},
	["unit"] = {},
	["this"] = {},
	["boolean"] = {},
	["string"] = {},
	["int"] = {},
	["tuple"] = {"value"},
	["variable"] = {},
}


-- RETURNS an Assertion
local function assertionReplaced(expression, variable, with)
	assertis(expression, "Assertion")
	assertis(variable, "string")
	assertis(with, "Assertion")

	if expression.tag == "variable" then
		if expression.variable.name == variable then
			return with
		end
	end

	assert(assertionRecursionMap[expression.tag])
	local copy = {}
	for key, value in pairs(expression) do
		copy[key] = value
	end
	for _, key in ipairs(assertionRecursionMap[expression.tag]) do
		if key:sub(-2) == "{}" then
			for k, v in pairs(copy[key:sub(1, -3)]) do
				copy[key:sub(1, -3)][k] = assertionReplaced(v, variable, with)
			end
		else
			copy[key] = assertionReplaced(copy[key], variable, with)
		end
	end
	return freeze(copy)
end

--------------------------------------------------------------------------------

-- RETURNS a string
local function showStatement(statement, indent)
	indent = (indent or "")
	if statement.tag == "block" then
		if #statement.statements == 0 then
			return indent .. "block {}"
		end
		local out = indent .. "block {\n"
		for _, element in ipairs(statement.statements) do
			out = out .. showStatement(element, indent .. "\t") .. "\n"
		end
		return out .. indent .. "}"
	elseif statement.tag == "assume" then
		return indent .. "assume " .. statement.variable.name .. " in\n" .. showStatement(statement.body, "\t" .. indent)
	elseif statement.tag == "verify" then
		return indent .. "verify " .. statement.variable.name .. " in\n" .. showStatement(statement.body, "\t" .. indent)
	elseif statement.tag == "local" then
		return indent .. "local " .. statement.variable.name .. " " .. showType(statement.variable.type)
	elseif statement.tag == "assign" then
		return indent .. "assign " .. statement.destination.name .. " := " .. statement.source.name
	elseif statement.tag == "method-call" then
		local destinations = table.concat(table.map(table.getter "name", statement.destinations), ", ")
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		return indent .. "method " .. destinations.. " := " .. statement.baseInstance.name .. "." .. statement.methodName .. "(" .. arguments .. ")"
	elseif statement.tag == "static-call" then
		local destinations = table.concat(table.map(table.getter "name", statement.destinations), ", ")
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		return indent .. "static " .. destinations.. " := " .. showType(statement.baseType) .. "." .. statement.staticName .. "(" .. arguments .. ")"
	else
		return indent .. statement.tag
	end
end

-- RETURNS an Assertion
local function tupleAccess(value, index)
	assertis(value, "Assertion")
	assertis(index, "integer")
	
	return {
		tag = "tuple",
		index = index,
		value = value,
	}
end

local VALUE_THIS = {tag = "this"}
local VALUE_UNIT = {tag = "unit"}

-- RETURNS an Assertion
local function valueInt(int)
	assertis(int, "integer")

	return {
		tag = "int",
		value = int,
	}
end

-- RETURNS an Assertion
local function valueString(str)
	assertis(str, "string")

	return {
		tag = "string",
		value = str,
	}
end

-- RETURNS an Assertion
local function valueBoolean(bool)
	assertis(bool, "boolean")

	return {
		tag = "boolean",
		value = bool,
	}
end

-- RETURNS an Assertion
local function variableAssertion(scope, variable)
	-- TODO: get rid of scope
	assertis(scope, listType(listType "Action"))
	assertis(variable, "VariableIR")

	return {
		tag = "variable",
		variable = variable,
	}
end

-- MODIFIES scope
-- RETURNS nothing
local function addPredicate(scope, value)
	assertis(scope, listType(listType "Action"))
	assertis(value, "Assertion")

	table.insert(scope[#scope], {
		tag = "predicate",
		value = value,
	})
end

-- RETURNS nothing
-- MODIFIES scope
local function assignRaw(scope, destination, value)
	assertis(scope, listType(listType "Action"))
	assertis(destination, "VariableIR")
	assertis(value, "Assertion")
	
	table.insert(scope[#scope], {
		tag = "assignment",
		destination = destination,
		value = value,
	})
end

-- RETURNS an assertion representing the conjunction of all inputs
local function andAssertion(assertions)
	if #assertions == 0 then
		return valueBoolean(true)
	elseif #assertions == 1 then
		return assertions[1]
	end
	local a = assertions[1]
	for i = 2, #assertions do
		a = {
			tag = "method",
			base = a,
			arguments = {assertions[i]},
			methodName = "and",
		}
	end
	return a
end

-- RETURNS a boolean indicating whether or not `scope` MUST model `predicate`
local function mustModel(scope, target)
	assertis(scope, listType(listType "Action"))
	assertis(target, "Assertion")

	-- TODO: come up with something that deals with loops
	local predicates = {}
	local assignments = {}

	-- RETURNS an Assertion
	local function inNow(a)
		assertis(a, "Assertion")
		assertis(assignments, mapType("string", "Assertion"))
		for variable, replacement in pairs(assignments) do
			a = assertionReplaced(a, variable, replacement)
		end
		return a
	end

	profile.open "translating-in-scope"

	-- Translate assignments as a substitution in all subsequent predicates
	for i, frame in ipairs(scope) do
		for j, action in ipairs(frame) do
			if action.tag == "assignment" then
				local newID = action.destination.name .. "'" .. i .. "'" .. j
				local newV = variableAssertion(scope, table.with(action.destination, "name", newID))
				table.insert(predicates, {
					tag = "method",
					methodName = "eq",
					base = inNow(action.value),
					arguments = {newV},
				})
				assignments[action.destination.name] = newV
			elseif action.tag == "predicate" then
				table.insert(predicates, inNow(action.value))
			else
				error("unknown action tag `" .. action.tag .. "`")
			end
		end
	end
	assertis(predicates, listType "Assertion")

	profile.close()

	local complexModel = {}
	--print("mustModel ? ", showAssertion(inNow(target)))
	for i, p in ipairs(predicates) do
		complexModel[p] = true
		--print(i, showAssertion(p))
	end

	local result = inNow(target)

	return theorem.modelsAssertion(verifyTheory, complexModel, result)
end

-- MODIFIES scope
-- RETURNS nothing
local function beginSubscope(scope)
	assertis(scope, listType(listType "Action"))
	assert(#scope >= 1)
	table.insert(scope, {})
end

-- MODIFIES scope
local function endSubscope(scope)
	assertis(scope, listType(listType "Action"))
	assert(#scope >= 2)
	return table.remove(scope)
end

-- RETURNS nothing
-- MODIFIES nothing
local function dumpScope(scope)
	assertis(scope, listType(listType "Action"))

	for i, frame in ipairs(scope) do
		print("$ -- Frame " .. i)
		for j, v in ipairs(frame) do
			io.write("$\t" .. j .. "\t")
			if v.tag == "assignment" then
				print(v.destination.name .. " := " .. showAssertion(v.value))
			elseif v.tag == "predicate" then
				print(showAssertion(v.value))
			else
				error("unknown action tag `" .. v.tag .. "` in dumpScope")
			end
		end
	end
end

-- RETURNS an Assertion
local function resultAssertion(scope, statement)
	assertis(scope, listType(listType "Action"))
	assertis(statement, "StatementIR")
	statement = freeze(statement)

	if statement.tag == "method-call" or statement.tag == "generic-method-call" then
		return freeze {
			tag = "method",
			base = variableAssertion(scope, statement.baseInstance),
			methodName = statement.methodName,
			arguments = table.map(function(x) return variableAssertion(scope, x) end, statement.arguments),
		}
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		local base
		if statement.tag == "static-call" then
			base = showType(statement.baseType)
		else
			base = showInterfaceType(statement.constraint.interface)
		end
		return freeze {
			tag = "static",
			base = base,
			staticName = statement.staticName,
			arguments = table.map(function(x) return variableAssertion(scope, x) end, statement.arguments),
		}
	end
	error("unknown statement tag `" .. statement.tag .. "` in resultAssertion")
end

-- MODIFIES scope
-- RETURNS nothing
local function verifyStatement(statement, scope, semantics)
	assertis(statement, "StatementIR")
	assertis(scope, listType(listType "Action"))
	assertis(semantics, "Semantics")

	local allDefinitions = table.concatted(
		semantics.classes, semantics.interfaces, semantics.unions
	)

	if statement.tag == "block" then
		for _, sub in ipairs(statement.statements) do
			verifyStatement(sub, scope, semantics)
		end
		return
	elseif statement.tag == "verify" then
		profile.open "verify VerifySt's body"
		verifyStatement(statement.body, scope, semantics)
		profile.close()

		-- Check
		local models = mustModel(scope, variableAssertion(scope, statement.variable))
		if not models then
			--print("$ !!!", models)
			--dumpScope(scope)
			--print("$ =/=>", showAssertion(variableAssertion(scope, statement.variable)))
			Report.DOES_NOT_MODEL {
				reason = statement.reason,
				conditionLocation = statement.conditionLocation,
				checkLocation = statement.checkLocation,
			}
		end
	
		return
	elseif statement.tag == "assume" then
		--print("ASSUME", statement)
		verifyStatement(statement.body, scope, semantics)

		addPredicate(scope, variableAssertion(scope, statement.variable))

		--error "TODO"
		return
	elseif statement.tag == "local" then
		-- Do nothing
		return
	elseif statement.tag == "this" then
		-- This
		assignRaw(scope, statement.destination, VALUE_THIS)
		return
	elseif statement.tag == "unit" then
		-- Unit
		assignRaw(scope, statement.destination, VALUE_UNIT)
		return
	elseif statement.tag == "field" then
		-- TODO:
		return
	elseif statement.tag == "variant" then
		-- TODO:
		return
	elseif statement.tag == "int" then
		-- Integer literal
		assignRaw(scope, statement.destination, valueInt(statement.number))
		return
	elseif statement.tag == "string" then
		-- String literal
		assignRaw(scope, statement.destination, valueString(statement.string))
		return
	elseif statement.tag == "boolean" then
		-- Boolean literal
		assignRaw(scope, statement.destination, valueBoolean(statement.boolean))
		return
	elseif statement.tag == "method-call" or statement.tag == "generic-method-call" then
		-- TODO: reject impure
		local source = resultAssertion(scope, statement)
		for i, destination in ipairs(statement.destinations) do
			if #statement.destinations > 1 then
				source = tupleAccess(source, i)
			end
			assignRaw(scope, destination, source)
		end
		return
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		-- TODO: reject impure
		local source = resultAssertion(scope, statement)
		for i, destination in ipairs(statement.destinations) do
			if #statement.destinations > 1 then
				source = tupleAccess(source, i)
			end
			assignRaw(scope, destination, source)
		end
		return
	elseif statement.tag == "return" then
		-- Do nothing
		return
	elseif statement.tag == "new-class" then
		local fields = {}
		for n, v in pairs(statement.fields) do
			fields[n] = variableAssertion(scope, v)
		end
		local rhs = {
			tag = "new-class",
			type = showType(statement.type),
			fields = fields,
		}
		assignRaw(scope, statement.destination, rhs)
		return
	elseif statement.tag == "new-union" then
		-- TODO
		local rhs = {
			tag = "new-union",
			type = showType(statement.type),
			field = statement.field,
			value = variableAssertion(scope, statement.value),
		}
		assignRaw(scope, statement.destination, rhs)
		return
	elseif statement.tag == "assign" then
		assignRaw(scope, statement.destination, variableAssertion(scope, statement.source))
		return
	elseif statement.tag == "match" then
		-- Check each case
		for _, case in ipairs(statement.cases) do
			beginSubscope(scope)
			-- TODO: add predicate
			addPredicate(scope, {"is", statement.base, statement.variant})
			verifyStatement(case.statement, scope, semantics)
			endSubscope(scope)
		end

		-- TODO: incorporate intersection (see if)
		return
	elseif statement.tag == "if" then
		-- Check then branch
		beginSubscope(scope)
		assignRaw(scope, statement.condition, valueBoolean(true))
		verifyStatement(statement.bodyThen, scope, semantics)
		endSubscope(scope)
		
		-- Check else branch
		beginSubscope(scope)
		assignRaw(scope, statement.condition, valueBoolean(false))
		verifyStatement(statement.bodyElse, scope, semantics)
		endSubscope(scope)

		-- TODO: incorporate intersection (see match)
		return
	end

	error("unhandled statement `" .. statement.tag .. "`")
end

-- RETURNS nothing
local function verifyFunction(func, semantics)
	assertis(func, "FunctionIR")
	assertis(semantics, "Semantics")
	assert(func.body)

	local beginTime = os.clock()
	profile.open("verifyFunction " .. func.name)
	verifyStatement(func.body, {{}}, semantics)
	profile.close()
end

-- RETURNS nothing
return function(semantics)
	assertis(semantics, "Semantics")

	-- Verify all functions
	for _, func in ipairs(semantics.functions) do
		if func.body then
			verifyFunction(freeze(func), semantics)
		end
	end
end
