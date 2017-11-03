local theorem = {}
local profile = import "profile.lua"

REGISTER_TYPE("Theory", recordType {
	-- argument: (self, model_t, assertion_t, truth)
	-- RETURNS true when simple assertion_t assertion provably
	-- has the specified truth value
	-- given the simple model.
	-- Need not be complete.
	inModel = "function",

	-- argument: (self, assertion_t, boolean)
	-- RETURNS false
	-- RETURNS [assertion_t], [[boolean]]
	breakup = "function",

	-- argument: self, map(assertion_t => boolean)
	-- RETURNS true if it provably inconsistent
	-- RETURNS false if it is not probably inconsistent.
	-- It is SAFE for this function to return `false` on inconsistent inputs.
	isInconsistent = "function",

	assertion_t = "any",
})

-- list: [][]T
-- return: [][]T
-- cartesian [[1], [2, 3]] is [[1, 2], [1, 3]]
local function cartesian(list)
	assertis(list, listType(listType "any"))
	assert(#list >= 1)

	if #list == 1 then
		return table.map(function(x) return {x} end, list[1])
	end
	local tail = {}
	for i = 2, #list do
		table.insert(tail, list[i])
	end
	local subs = cartesian(tail)
	local out = {}
	for _, front in ipairs(list[1]) do
		for _, sub in ipairs(subs) do
			table.insert(out, table.concatted({front}, sub))
		end
	end
	return out
end

-- RETURNS a model
-- RETURNS false if the intersection is unsatisfiable
local function intersectMaps(modelA, modelB)
	local out = {}
	for key, value in pairs(modelA) do
		out[key] = value
	end
	for key, value in pairs(modelB) do
		if out[key] ~= nil and out[key] ~= value then
			return false
		end
		out[key] = value
	end
	return out
end

-- RETURNS a type
local function model_t(theory)
	assertis(theory, "Theory")

	return mapType(theory.assertion_t, "boolean")
end

-- RETURNS a map
local function zipMap(a, b)
	assertis(a, listType "any")
	assertis(b, listType "any")
	assert(#a == #b)

	local out = {}
	for i = 1, #a do
		if out[a[i]] ~= nil and out[a[i]] ~= b[i] then
			return false
		end
		out[a[i]] = b[i]
	end
	return out
end

-- RETURNS a set of simple models such that the disjunction of the simple models
-- is equivalent to the assertion
local function assertionToSimpleModels(theory, assertion, target)
	assertis(theory, "Theory")
	assertis(assertion, theory.assertion_t)
	assertis(target, "boolean")

	local broken, choices = theory:breakup(assertion, target)
	if not broken then
		return {{[assertion] = target}}
	end

	-- Recursively build the set
	local models = {}
	for _, choice in ipairs(choices) do
		assert(#choice == #broken)

		local chains = {}
		for i, component in ipairs(broken) do
			local subs = assertionToSimpleModels(theory, component, choice[i])
			assertis(subs, listType(model_t(theory)))
			table.insert(chains, subs)
		end
		assert(#chains == #broken)
		assertis(chains, listType(listType(model_t(theory))))

		for _, chain in ipairs(cartesian(chains)) do
			local model = {}
			for _, element in ipairs(chain) do
				assertis(element, model_t(theory))

				model = intersectMaps(model, element)
				if not model then
					break
				end
			end
			if model then
				table.insert(models, model)
			end
		end
	end
	assertis(models, listType(model_t(theory)))
	return models
end

-- RETURNS nothing
-- Prints the contents of the model to standard out
local function dumpModel(theory, model)
	if not theory.showAssertion then
		return
	end
	print("model {")
	local longest = 0
	local keys = {}
	for k in pairs(model) do
		longest = math.max(longest, #theory.showAssertion(k))
		table.insert(keys, k)
	end
	table.sort(keys, function(a, b) return theory.showAssertion(a) < theory.showAssertion(b) end)
	for _, k in ipairs(keys) do
		local v = model[k]
		local s = theory.showAssertion(k)
		print("\t\t`" .. s .. "`" .. string.rep(" ", longest - #s) .. " -> " .. tostring(v))
	end
	print("}")
end

-- RETURNS a set of simple models such that the disjunction of the simple models
-- is equivalent to the complex model
local function complexToSimpleModels(theory, complex)
	assertis(theory, "Theory")
	assertis(complex, model_t(theory))

	local terms = {}
	for assertion, truth in pairs(complex) do
		table.insert(terms, assertionToSimpleModels(theory, assertion, truth))
	end
	assertis(terms, listType(listType(model_t(theory))))
	--table.sort(terms, function(a, b) return show(a) < show(b) end)

	local models = {}
	for _, chain in ipairs(cartesian(terms)) do
		local model = {}
		for _, sub in ipairs(chain) do
			model = intersectMaps(model, sub)
			if not model then
				assertis(theory.falseAssertion, theory.assertion_t)
				table.insert(models, {[theory.falseAssertion] = true})
				break
			end
		end
		if model then
			table.insert(models, model)
		end
	end
	return models
end

-- RETURNS a boolean representing the truth value of a => b.
local function modelImplies(theory, a, b)
	assertis(theory, "Theory")
	assertis(a, model_t(theory))
	assertis(b, model_t(theory))

	local todos = {}
	for key, value in pairs(b) do
		if a[key] ~= nil then
			if a[key] ~= value then
				return theory:isInconsistent(a)
			end
		else
			table.insert(todos, {assertion = key, truth = value})
		end
	end
	assertis(todos, listType(recordType {
		assertion = theory.assertion_t, truth = "boolean"
	}))

	for _, todo in ipairs(todos) do
		if not theory:inModel(a, todo.assertion, todo.truth) then
			return false
		end
	end
	return true
end

-- models: a list of simple models
-- assertion: a complex assertion
-- RETURNS a boolean
function theorem.simpleModelsAssertion(theory, models, assertion)
	assertis(theory, "Theory")
	assertis(models, listType(model_t(theory)))
	assertis(assertion, theory.assertion_t)

	local simples = assertionToSimpleModels(theory, assertion, true)
	assertis(simples, listType(model_t(theory)))

	for _, model in ipairs(models) do
		if theory:isInconsistent(model) then
		else
			local found = false
			for _, simple in ipairs(simples) do
				if modelImplies(theory, model, simple) then
					found = true
					break
				end
			end
			if not found then
				return false
			end
		end
	end
	return true
end

-- model: a complex model
-- assertion: a complex assertion
-- RETURNS a boolean
function theorem.modelsAssertion(theory, model, assertion)
	assertis(theory, "Theory")
	assertis(model, model_t(theory))
	assertis(assertion, theory.assertion_t)

	profile.open "complexToSimpleModels"
	local simples = complexToSimpleModels(theory, model)

	profile.close()

	local out = theorem.simpleModelsAssertion(theory, simples, assertion)
	return out
end

-- Plain Theory Test -----------------------------------------------------------

do
	local plaintheory = {}
	plaintheory.falseAssertion = false
	--plaintheory.showAssertion = function(x) return (show(x):gsub("%s+", " ")) end

	function plaintheory:breakup(assertion, truth)
		if type(assertion) == "string" then
			return false
		end
		if truth then
			if assertion[1] == "and" then
				return {assertion[2], assertion[3]}, {{true, true}}
			elseif assertion[1] == "or" then
				return {assertion[2], assertion[3]}, {{true, true}, {true, false}, {false, true}}
			elseif assertion[1] == "not" then
				return {assertion[2]}, {{false}}
			elseif assertion[1] == "iff" then
				return {assertion[2], assertion[3]}, {{true, true}, {false, false}}
			elseif assertion[1] == "implies" then
				return {assertion[2], assertion[3]}, {{true, true}, {false, true}, {false, false}}
			end
		else
			if assertion[1] == "and" then
				return {assertion[2], assertion[3]}, {{false, false}, {true, false}, {false, true}}
			elseif assertion[1] == "or" then
				return {assertion[2], assertion[3]}, {{false, false}}
			elseif assertion[1] == "not" then
				return {assertion[2]}, {{true}}
			elseif assertion[1] == "iff" then
				return {assertion[2], assertion[3]}, {{true, false}, {false, true}}
			elseif assertion[1] == "implies" then
				return {assertion[2], assertion[3]}, {{true, false}}
			end
		end
		error "foo"
	end

	plaintheory.assertion_t = "any"

	function plaintheory:inModel(model, assertion, target)
		return assertion == target or plaintheory:isInconsistent(model)
	end

	function plaintheory:isInconsistent(model)
		for key, value in pairs(model) do
			if type(key) == "boolean" then
				if key ~= value then
					return true
				end
			end
		end
		return false
	end

	local m1 = {
		[
			{"and", "x", "y"}
		] = true,
	}
	assert(theorem.modelsAssertion(plaintheory, m1, "y"))
	assert(not theorem.modelsAssertion(plaintheory, m1, "z"))
	assert(not theorem.modelsAssertion(plaintheory, m1, {"not", "z"}))
	assert(not theorem.modelsAssertion(plaintheory, m1, {"not", "y"}))

	local m2 = {
		[
			{"or", {"not", "x"}, "y"}
		] = true,
	}
	assert(not theorem.modelsAssertion(plaintheory, m2, "y"))
	assert(not theorem.modelsAssertion(plaintheory, m2, "x"))
	assert(not theorem.modelsAssertion(plaintheory, m2, {"not", "x"}))

	local m3_2 = {
		["x"] = true,
		[
			{"or", {"not", "x"}, "y"}
		] = true,
	}
	assert(theorem.modelsAssertion(plaintheory, m3_2, "y"))
	assert(theorem.modelsAssertion(plaintheory, m3_2, "x"))
	assert(not theorem.modelsAssertion(plaintheory, m3_2, {"not", "x"}))

	local m3_4 = {
		["x"] = false,
		[
			{"or", {"not", "x"}, "y"}
		] = true,
	}
	assert(not theorem.modelsAssertion(plaintheory, m3_4, "y"))
	assert(not theorem.modelsAssertion(plaintheory, m3_4, {"not", "y"}))
	assert(not theorem.modelsAssertion(plaintheory, m3_4, "x"))
	assert(theorem.modelsAssertion(plaintheory, m3_4, {"not", "x"}))

	local m4 = {
		[
			{"iff", "x", "y"}
		] = true,
	}
	assert(theorem.modelsAssertion(plaintheory, m4, {"implies", "x", "y"}))
	assert(theorem.modelsAssertion(plaintheory, m4, {"implies", "y", "x"}))
	assert(not theorem.modelsAssertion(plaintheory, m4, "x"))
	assert(not theorem.modelsAssertion(plaintheory, m4, "y"))
	assert(not theorem.modelsAssertion(plaintheory, m4, {"not", "x"}))
	assert(not theorem.modelsAssertion(plaintheory, m4, {"not", "y"}))

	local m5 = {
		[
			{"iff", "x", "y"}
		] = true,
		[
			{"implies", "x", "y"}
		] = true,
	}
	assert(theorem.modelsAssertion(plaintheory, m5, {"implies", "y", "x"}))
end

return theorem
