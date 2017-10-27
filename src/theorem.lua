local theorem = {}

REGISTER_TYPE("Theory", recordType {
	-- argument: {assertion_t => boolean}
	-- RETURNS [satisfaction_t]
	satisfactions = "function",

	-- argument: (assertion_t, boolean)
	-- RETURNS false
	-- RETURNS [assertion_t], [[boolean]]
	breakup = "function",

	assertion_t = "any",
	satisfaction_t = "any",
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

-- RETURNS [{atomic Assertion => boolean}]
-- TODO: return [theory.satisfaction_t] also
-- an atomic Assertion is an Assertion a such that theory.breakup(a) == false.
function theorem.satisfactions(theory, assertion, target)
	assertis(theory, "Theory")
	assertis(assertion, theory.assertion_t)
	-- TODO: in principle, target need not be limited to booleans
	assertis(target, "boolean")

	-- Attempt to break-up the assertion into subassertions
	local broken, truths = theory.breakup(assertion, target)
	if not broken then
		local recursive = {[assertion] = target}
		local out = theory.satisfactions(recursive)
		assertis(out, listType(theory.satisfaction_t))
		if #out == 0 then
			return {}, {}
		end
		return {recursive}, out
	end
	assert(#broken >= 0)
	assertis(truths, listType(listType "boolean"))

	-- Attempt each truth-assignment of sub-parts
	local out = {}
	local outTerm = {}
	for _, truth in ipairs(truths) do
		assert(#truth == #broken)

		-- Which atomic assignments satisfy truth[i]?
		local satisfactions = {}
		for i = 1, #truth do
			satisfactions[i] = theorem.satisfactions(theory, broken[i], truth[i])
		end
		assertis(satisfactions, listType(listType(mapType(theory.assertion_t, "boolean"))))
		local chains = cartesian(satisfactions)
		assertis(chains, listType(listType(mapType(theory.assertion_t, "boolean"))))
		for _, chain in ipairs(chains) do
			assert(#chain >= 1)
			local satisfiable = true
			local merged = {}
			for i = 1, #chain do
				for key, value in pairs(chain[i]) do
					if merged[key] ~= nil and merged[key] ~= value then
						-- This chain contains a contradiction and so cannot be
						-- satisfiable
						satisfiable = false
						break
					end
					merged[key] = value
				end
			end
			satisfiable = satisfiable and theory.satisfactions(merged)
			if satisfiable and #satisfiable > 0 then
				table.insert(out, merged)
				table.insert(outTerm, satisfiable)
			end
		end
	end

	-- The assertion is not satisfiable
	return out, outTerm
end

function theorem.counterexamples(theory, assertion)
	return theorem.satisfactions(theory, assertion, false)
end

function theorem.isTautology(theory, assertion)
	local counter1, counter2 = theorem.counterexamples(theory, assertion)
	if #counter1 == 0 then
		return true
	end
	return false, counter1, counter2
end

-- Tests -----------------------------------------------------------------------

local test_theory = {
	satisfactions = function(assignment)
		local out = {}
		local LOW, HIGH = -5, 5
		for x = LOW, HIGH do
			for y = LOW, HIGH do
				for z = LOW, HIGH do
					local satisfied = true
					for f, v in pairs(assignment) do
						if f(x, y, z) ~= v then
							satisfied = false
						end
					end
					if satisfied then
						table.insert(out, {x = x, y = y, z = z})
					end
				end
			end
		end
		return out
	end,

	breakup = function(a, target)
		if type(a) == "function" then
			return false
		end
		if a[1] == "and" then
			if target then
				return {a[2], a[3]}, {{true, true}}
			end
			return {a[2], a[3]}, {{false, false}, {false, true}, {true, false}}
		elseif a[1] == "or" then
			if target then
				return {a[2], a[3]}, {{false, true}, {true, false}, {true, true}}
			end
			return {a[2], a[3]}, {{false, false}}
		elseif a[1] == "not" then
			if target then
				return {a[2]}, {{false}}
			end
			return {a[2]}, {{true}}
		elseif a[1] == "implies" then
			if target then
				return {a[2], a[3]}, {{false, true}, {false, false}, {true, true}}
			end
			return {a[2], a[3]}, {{true, false}}
		end
		error "unknown tag"
	end,

	assertion_t = choiceType("function", listType "any"),
	satisfaction_t = mapType("string", "integer"),
}

local always = function() return true end

local tests = {
	[
		function(x, y) return false end
	] = false,
	[
		function(x, y) return true end
	] = true,
	[
		function(x, y) return x ~= 0 or y ~= 0 end
	] = false,
	[
		{"or", function() return true end, function() return true end}
	] = true,
	[
		{"implies", function(x) return x == 3 end, function(x) return x*x == 9 end}
	] = true,
	[
		{"implies", function(x) return x*x == 9 end, function(x) return x == 3 end}
	] = false,
	[
		{"or", always, {"not", always}}
	] = true,
	[
		{"and", always, {"not", always}}
	] = false,
}

local slow = {
	{
		"and",
		{
			"and",
			function(x, y, z) return x > y end,
			function(x, y, z) return y > z end,
		},
		{
			"and",
			function(x, y, z) return z == 10 end,
			function(x, y, z) return x < 13 end,
		}
	}
}

-- Run tests
for x, e in pairs(tests) do
	--print("test...")
	local is, c1, counter = theorem.isTautology(test_theory, x)
	if is ~= e then
		print("isTautology " .. show(x):gsub("%s+", " ") .. " ?", is)
		print("contradictions:", show(c1))
		print("contradictions:", show(counter))
		error("\t" .. show(e))
	end
	--print("...pass")
end

return theorem
