local theorem = {}

REGISTER_TYPE("Theory", recordType {
	-- argument: (self, model_t, assertion_t)
	-- RETURNS true when assertion_t provably follows from the given simple
	-- model
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

	local models = {}
	for _, chain in ipairs(cartesian(terms)) do
		local model = {}
		for _, sub in ipairs(chain) do
			model = intersectMaps(model, sub)
			if not model then
				break
			end
		end
		if model then
			table.insert(models, model)
		end
	end
	return models
end

-- RETURNS a boolean
local function modelImplies(theory, a, b)
	assertis(theory, "Theory")
	assertis(a, model_t(theory))
	assertis(b, model_t(theory))

	local todos = {}
	for key, value in pairs(b) do
		if a[key] ~= nil then
			if a[key] ~= value then
				return false
			end
		else
			table.insert(todos, key)
		end
	end
	assertis(todos, listType(theory.assertion_t))

	for _, todo in ipairs(todos) do
		if not theory:inModel(a, todo) then
			return false
		end
	end
	return true
end

-- RETURNS a boolean
function theorem.simpleModelsAssertion(theory, models, assertion)
	assertis(theory, "Theory")
	assertis(models, listType(model_t(theory)))
	assertis(assertion, theory.assertion_t)

	local simples = assertionToSimpleModels(theory, assertion, true)
	assertis(simples, listType(model_t(theory)))

	for _, model in ipairs(models) do
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
	return true
end

-- RETURNS a boolean
function theorem.modelsAssertion(theory, model, assertion)
	assertis(theory, "Theory")
	assertis(model, model_t(theory))
	assertis(assertion, theory.assertion_t)

	local simples = complexToSimpleModels(theory, model)
	return theorem.simpleModelsAssertion(theory, simples, assertion)
end

-- Tests -----------------------------------------------------------------------

local eqtheory = {}
function eqtheory:inModel(model, assertion)
	-- TODO
	print(string.rep(".", 80))
	print("eqtheory:inModel(")
	print("", show(model):gsub("%s+", " ") .. ", ")
	print("", show(assertion):gsub("%s+", " ") .. ")")
	print(string.rep(",", 80))

	return false
end

function eqtheory:breakup(assertion, truth)
	if assertion.tag == "and" then
		return {assertion.left, assertion.right}, {{true, true}}
	end
	return false
end

function eqtheory:isInconsistent(model)
	return false
end

eqtheory.assertion_t = recordType {tag = choiceType(constantType "and", constantType "=")}

local m1 = {
	[{tag = "and", left = {tag = "=", left = "x", right = "0"}, right = {tag = "=", left = "x", right = "y"}}] = true,
}
local a1 = {tag = "=", left = "y", right = "0"}

print(theorem.modelsAssertion(eqtheory, m1, a1))


os.exit(0)

return theorem
