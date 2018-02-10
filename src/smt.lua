-- A SMT Solver

local profile = import "profile.lua"

REGISTER_TYPE("Theory", recordType {
	-- argument: (self, simpleModel)
	-- RETURNS true when simple assertion_t assertion may be inhabited
	-- RETURNS false ONLY when it is provable that the model is not satisfiable
	isSatisfiable = "function",

	-- argument: (self, assertion_t, boolean)
	-- RETURNS false
	-- RETURNS [assertion_t], [[boolean]]
	breakup = "function",

	assertion_t = "any",

	-- argument: (self, assertion_t)
	-- RETURNS an object with a consistent identity (strings are simple)
	canonKey = "function",

	-- argument: (self, simpleModel, cnf)
	-- RETURNS [assertion_t]
	additionalClauses = "function",
})

-- RETURNS a shallow copy of t such that return[k] is v
local function copywith(t, k, v)
	local r = {}
	for key, value in pairs(t) do
		r[key] = value
	end
	r[k] = v
	return r
end

-- RETURNS a string representation of a CNF clause (for debugging)
local function showClause(theory, c)
	local terms = {}
	for i = 1, #c do
		terms[i] = theory:canonKey(c[i][1])
		if not c[i][2] then
			terms[i] = "~(" .. terms[i] .. ")"
		end
	end
	return "[" .. table.concat(terms, " || ") .. "]"
end

-- RETURNS a string representation of a CNF formula (for debugging)
local function showCNF(theory, n)
	local clauses = {}
	for i = 1, #n do
		clauses[i] = showClause(theory, n[i])
	end
	return "&& " .. table.concat(clauses, "\n&& ")
end

--------------------------------------------------------------------------------

-- RETURNS a CNF formula, [][](term, boolean)
-- the conjunction of CNFs a and b
local function andCNF(a, b)
	return table.concatted(a, b)
end

-- clause: a CNF clause
-- RETURNS a CNF clause, [](term, boolean)
-- RETURNS true when the given clause is always true
local function simplifyClause(theory, clause)
	local assigned = {}
	local out = {}
	for _, pair in ipairs(clause) do
		local term, truth = pair[1], pair[2]
		local key = theory:canonKey(term)
		if assigned[key] == nil then
			-- This term is fresh
			assigned[key] = truth
			table.insert(out, pair)
		elseif assigned[key] ~= truth then
			-- This clause contains P || ~P
			return true
		end
	end
	return out
end

-- a: a CNF clause (a disjunction)
-- b: a CNF clause (a disjunction)
-- RETURNS a CNF clause, [](term, boolean)
local function disjunctionOfClause(theory, a, b)
	local clause = {}
	for _, x in ipairs(a) do
		table.insert(clause, x)
	end
	for _, y in ipairs(b) do
		table.insert(clause, y)
	end

	-- TODO: simplification
	return clause
end

-- a: a CNF description
-- b: a CNF description
-- RETURNS a CNF description, [][](term, boolean)
local function disjunctionOfCNF(theory, a, b)
	local clauses = {}
	for _, x in ipairs(a) do
		for _, y in ipairs(b) do
			local v = disjunctionOfClause(theory, x, y)
			v = simplifyClause(theory, v)
			if v ~= true then
				table.insert(clauses, v)
			end
		end
	end
	return clauses
end

local toCNF

local function toCNFFromBreakup(theory, terms, assignments, normalization)
	assertis(theory, "Theory")
	assertis(terms, listType(theory.assertion_t))
	assertis(assignments, listType(listType(choiceType("boolean", constantType "*"))))
	assert(#assignments >= 1)

	--assertis(normalization, "object")

	local options = {}
	for _, assignment in ipairs(assignments) do
		local clauses = {}
		assert(#assignment == #terms)
		for i, term in ipairs(terms) do
			if assignment[i] ~= "*" then
				assert(type(assignment[i]) == "boolean")
				for _, clause in ipairs(toCNF(theory, term, assignment[i], normalization)) do
					table.insert(clauses, clause)
				end
			end
		end
		table.insert(options, clauses)
	end

	-- bigTerm is equivalent to the disjunction of `options`, a set of CNFs
	-- To create a single CNF, must distribute
	local out = options[1]
	for i = 2, #options do
		out = disjunctionOfCNF(theory, out, options[i])
	end
	return out
end

-- RETURNS a CNF description equivalent to (term == target)
-- A CNF expression is [][](term, boolean).
function toCNF(theory, bigTerm, target, normalization)
	assertis(theory, "Theory")
	assertis(bigTerm, theory.assertion_t)

	assert(type(target) == "boolean")
	assert(type(normalization) == "table")

	local terms, assignments = theory:breakup(bigTerm, target)
	if not terms then
		-- Ask the theory for a key to normalize the term
		local key = theory:canonKey(bigTerm)
		if normalization[key] == nil then
			normalization[key] = bigTerm
		end
		local unitClause = {{normalization[key], target}}
		return {unitClause}
	end

	return toCNFFromBreakup(theory, terms, assignments, normalization)
end

--------------------------------------------------------------------------------

-- RETURNS a CNF simplified using the assignment such that all terms with
-- all terms with assignments do not appear in the theory
-- RETURNS false if the given cnf is unsatisfiable given the assignment
local function simplifyCNF(cnf, assignment)
	profile.open "simplifyCNF"
	assert(type(assignment) == "table")

	local cs = {}
	for _, clause in ipairs(cnf) do
		-- Simplify a clause
		local c = {}
		local contradiction = false
		local satisfied = false

		-- Search the clause of terms with known truth assignments
		for _, term in ipairs(clause) do
			local e, truth = term[1], term[2]
			assert(type(truth) == "boolean")
			if assignment[e] ~= nil then
				if assignment[e] == truth then
					satisfied = true
				else
					-- If only false terms are left, this clause is
					-- unsatisfiable.
					contradiction = true
				end
			else
				table.insert(c, term)
			end
		end

		if not satisfied then
			-- Do not add empty clauses;
			-- empty clauses may represent True or False.
			if #c == 0 then
				assert(contradiction)
				profile.close "simplifyCNF"
				return false
			else
				table.insert(cs, c)
			end
		end
	end
	profile.close "simplifyCNF"
	return cs
end

--------------------------------------------------------------------------------

-- RETURNS a truth assignment of theory terms {[term] => boolean} that satisfies
-- the specified CNF expression. Does NOT ensure that all terms are represented.
-- RETURNS false when no satisfaction is possible
-- Does NOT modify assignment
local function cnfSAT(theory, cnf, assignment, odds)
	assert(type(assignment) == "table")
	assert(type(cnf) == "table")

	-- Find an assignment that the theory accepts
	if #cnf == 0 then
		profile.open("theory:isSatisfiable")
		local out = theory:isSatisfiable(assignment)
		profile.close("theory:isSatisfiable")
		return out and assignment
	end

	-- Find the smallest clause
	local smallestClauseIndex = 1
	for i = 2, #cnf do
		if #cnf[i] < #cnf[smallestClauseIndex] then
			smallestClauseIndex = i
		end
	end

	local smallestClause = cnf[smallestClauseIndex]
	assert(#smallestClause >= 1)
	if #smallestClause == 1 then
		profile.open "unit clause"

		-- Unit clauses have exactly one way to assign
		local term, truth = smallestClause[1][1], smallestClause[1][2]
		assert(assignment[term] == nil)
		local with = copywith(assignment, term, truth)
		local simplified = simplifyCNF(cnf, with)

		-- Ask the theory for additional clauses
		profile.open "theory:additionalClauses"
		local additional = theory:additionalClauses(with, term, simplified)
		profile.close "theory:additionalClauses"
		for _, add in ipairs(additional) do
			local addCNF = toCNF(theory, add, true, {})
			simplified = andCNF(simplified, addCNF)
		end

		if not simplified then
			profile.close "unit clause"
			return false
		end

		local out = cnfSAT(theory, simplified, with, 0)
		profile.close "unit clause"
		return out
	end

	-- Try each truth assignment of the first term in the first clause
	profile.open("decide yes")
	local t1 = smallestClause[1][1]
	local with = copywith(assignment, t1, smallestClause[1][2])
	local simplified = simplifyCNF(cnf, with)
	local out = simplified and cnfSAT(theory, simplified, with, 1)
	profile.close("decide yes")
	if out then
		return out
	end

	-- Then it can only be satisfied with no
	-- Add this to the set to prune more cases
	profile.open("decide no")
	local with = copywith(assignment, t1, not smallestClause[1][2])
	local simplified = simplifyCNF(cnf, with)
	local out = simplified and cnfSAT(theory, simplified, with, 1)
	profile.close("decide no")
	return out
end

-- RETURNS false | satisfaction
local function isSatisfiable(theory, expression)
	assert(theory)
	assert(expression)

	local cnf = toCNF(theory, expression, true, {})
	local sat = cnfSAT(theory, cnf, {}, 0)
	return sat
end

--------------------------------------------------------------------------------

-- RETURNS false, counterexample | true
local function implies(theory, givens, expression)
	profile.open("smt.implies setup")

	-- Is the case where givens are true but expression false satisfiable?
	local args = {}
	local truths = {}
	for i = 1, #givens do
		table.insert(args, givens[i])
		table.insert(truths, true)
	end

	table.insert(args, expression)
	table.insert(truths, false)

	local cnf = toCNFFromBreakup(theory, args, {truths}, {})
	profile.close("smt.implies setup")

	profile.open("smt.implies sat")
	local sat = cnfSAT(theory, cnf, {}, 0)

	profile.close("smt.implies sat")
	if sat then
		return false, sat
	end
	return true
end

--------------------------------------------------------------------------------

local plaintheory = {assertion_t = "any"}

-- Test theory
function plaintheory:isSatisfiable(model)
	local anyGood = false
	for x = 1, 2 do
		for y = 1, 2 do
			local good = true
			for k, v in pairs(model) do
				assert(type(v) == "boolean")
				if type(k) == "table" and k[1] == "f" then
					local e = k[2]
					e = e:gsub("x", tostring(x))
					e = e:gsub("y", tostring(y))
					local left, right = e:match("^(%d+) == (%d+)$")
					assert(left, "wrong pattern in `" .. e .. "`")
					if (left == right) ~= v then
						--print("\t\t\tfails for", k[2], "expected", v, "got", left == right)
						good = false
					end
				end
			end
			anyGood = anyGood or good
		end
	end
	return anyGood
end

function plaintheory:breakup(e, target)
	if type(e) == "string" then
		return false
	elseif e[1] == "f" then
		return false
	end

	if target then
		if e[1] == "and" then
			return {e[2], e[3]}, {{true, true}}
		elseif e[1] == "or" then
			return {e[2], e[3]}, {{true, "*"}, {false, true}}
		elseif e[1] == "not" then
			return {e[2]}, {{false}}
		elseif e[1] == "=>" then
			return {e[2], e[3]}, {{false, "*"}, {true, true}}
		end
	else
		if e[1] == "and" then
			return {e[2], e[3]}, {{false, "*"}, {true, false}}
		elseif e[1] == "or" then
			return {e[2], e[3]}, {{false, false}}
		elseif e[1] == "not" then
			return {e[2]}, {{true}}
		elseif e[1] == "=>" then
			return {e[2], e[3]}, {{true, false}}
		end
	end
	error("unknown `" .. show(e[1]) .. "`")
end

function plaintheory:canonKey(e)
	if type(e) == "string" then
		return string.format("%q", e)
	elseif type(e) == "function" then
		return tostring(e)
	end

	local list = {}
	for i = 1, #e do
		list[i] = plaintheory:canonKey(e[i])
	end
	return "{" .. table.concat(list, ", ") .. "}"
end

function plaintheory:additionalClauses()
	return {}
end

plaintheory = freeze(plaintheory)

local m1 = {"and", "x", "y"}
assert(true == implies(plaintheory, {m1}, "x"))
assert(true == implies(plaintheory, {m1}, "y"))
assert(not implies(plaintheory, {m1}, {"not", "z"}))
assert(not implies(plaintheory, {m1}, {"not", "x"}))
assert(not implies(plaintheory, {m1}, {"not", "y"}))
assert(not implies(plaintheory, {m1}, "z"))

local m2 = {"or", {"not", "x"}, "y"}
assert(not implies(plaintheory, {m2}, "x"))
assert(not implies(plaintheory, {m2}, "y"))
assert(not implies(plaintheory, {m2}, {"not", "x"}))
assert(not implies(plaintheory, {m2}, {"not", "y"}))

local m3 = {"or", {"not", "x"}, "y"}
assert(true == implies(plaintheory, {"x", m2}, "x"))
assert(true == implies(plaintheory, {"x", m2}, "y"))
assert(not implies(plaintheory, {"x", m2}, {"not", "x"}))
assert(not implies(plaintheory, {"x", m2}, {"not", "y"}))

local m4 = {
	{"=>", "x", "y"},
	{"not", "y"},
}
assert(not implies(plaintheory, m4, "x"))
assert(not implies(plaintheory, m4, "y"))
assert(implies(plaintheory, m4, {"not", "x"}))
assert(implies(plaintheory, m4, {"not", "y"}))

local m5 = {
	"and",
	{"f", "x == y"},
	{
		"and",
		{"or", {"f", "x == 1"}, {"f", "x == 2"}},
		{"f", "y == 2"},
	}
}
assert(not not isSatisfiable(plaintheory, m5))

assert(not implies(
	plaintheory,
	{
		{"f", "x == y"},
		{"or", {"f", "x == 1"}, {"f", "x == 2"}},
	},
	{"f", "y == 2"}
))

--------------------------------------------------------------------------------

return freeze {
	isSatisfiable = isSatisfiable,
	implies = implies,
}
