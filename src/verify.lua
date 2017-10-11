local calculateSemantics = import "semantics.lua"

-- RETURNS a symbolic value
local function tupleAccess(value, index)
	assertis(index, "integer")
	
	-- TODO!
end

local VALUE_TRUE = {}
local VALUE_FALSE = {}
local VALUE_THIS = {}
local VALUE_UNIT = {}

local function valueInt(int)
	-- TODO
end

local function valueString(str)
	-- TODO
end

local function valueBoolean(bool)
	-- TODO
end

-- MODIFIES scope
-- RETURNS nothing
local function addPredicate(scope, value)
	-- TODO
end

-- RETURNS nothing
-- MODIFIES scope
local function assignRaw(scope, destination, value)
	assertis(scope, listType "any")
	assertis(destination, "VariableIR")
	assertis(value, "any")
	
	table.insert(scope[#scope], {
		destination = destination,
		value = value,
	})
	
	-- TODO: adopt a theory of equality
end

-- MODIFIES scope
-- RETURNS nothing
local function beginSubscope(scope)
	assertis(scope, listType "any")
	assert(#scope >= 1)
	table.insert(scope, {})
end

-- MODIFIES scope
local function endSubscope(scope)
	assertis(scope, listType "any")
	assert(#scope >= 2)
	return table.remove(scope)
end

-- MODIFIES scope
-- RETURNS nothing
local function verifyStatement(statement, scope, semantics)
	assertis(statement, "StatementIR")
	assertis(scope, listType "any")
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
		-- TODO!

		error "TODO"
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
		-- TODO:
		for i, destination in ipairs(statement.destinations) do
			-- TODO:
			local source = false
			if #statement.destinations > 1 then
				source = tupleAccess(source, i)
			end
			assignRaw(scope, destination, source)
		end
		return
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		-- TODO:
		for i, destination in ipairs(statement.destinations) do
			-- TODO:
			local source = false
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
		-- TODO:
		local rhs = false
		assignRaw(scope, statement.destination, rhs)
		return
	elseif statement.tag == "new-union" then
		-- TODO
		local rhs = false
		assignRaw(scope, statement.destination, rhs)
		return
	elseif statement.tag == "assign" then
		assignRaw(scope, statement.destination, statement.source)
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
		assignRaw(scope, statement.condition, VALUE_TRUE)
		verifyStatement(statement.bodyThen, scope, semantics)
		endSubscope(scope)
		
		-- Check else branch
		beginSubscope(scope)
		assignRaw(scope, statement.condition, VALUE_FALSE)
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

	verifyStatement(func.body, {{}}, semantics)
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
