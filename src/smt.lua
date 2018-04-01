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

	-- argument: (self, simpleModel, cnf, additionalInfo)
	-- RETURNS [assertion_t], additionalInfo
	-- additionalInfo is used to manage recursive instantiations, and may be
	-- returned as nil
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
local function showClause(theory, c, assignment)
	assignment = assignment or {}
	local terms = {}
	for i = 1, #c do
		assert(#c[i] == 2)
		assertis(c[i][1], theory.assertion_t)
		terms[i] = theory:canonKey(c[i][1])
		if not c[i][2] then
			terms[i] = "~(" .. terms[i] .. ")"
		end
	end
	return "[" .. table.concat(terms, " || ") .. "]"
end

-- RETURNS a string representation of a CNF formula (for debugging)
local function showCNF(theory, n, assignment)
	assignment = assignment or {}
	local clauses = {}
	for i = 1, #n do
		clauses[i] = showClause(theory, n[i], assignment)
	end
	return "&& " .. table.concat(clauses, "\n&& ")
end

--------------------------------------------------------------------------------

-- RETURNS a CNF formula, [][](term, boolean)
-- the conjunction of CNFs a and b
local function andCNF(a, b)
	assertis(a, listType(listType(tupleType("any", "boolean"))))
	assertis(b, listType(listType(tupleType("any", "boolean"))))
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
local function simplifyCNF(theory, cnf, assignment)
	profile.open "simplifyCNF"

	local cs = {}
	for _, clause in ipairs(cnf) do
		assert(1 <= #clause)

		-- Simplify a clause
		local c = {}
		local satisfied = false

		-- Search the clause of terms with known truth assignments
		for _, term in ipairs(clause) do
			local e, truth = term[1], term[2]
			assert(type(truth) == "boolean")
			if assignment[e] == true or assignment[e] == false then
				if assignment[e] == truth then
					satisfied = true
				else
					-- If only false terms are left, this clause is
					-- unsatisfiable.
				end
			else
				table.insert(c, term)
			end
		end

		if not satisfied then
			-- Do not add empty clauses;
			-- empty clauses may represent True or False.
			if #c == 0 then
				-- An empty clause that is not satisfied only occurs from
				-- all of the terms being contradicted by the assignment
				profile.close "simplifyCNF"
				return false
			else
				assert(1 <= #c)
				table.insert(cs, c)
			end
		end
	end
	profile.close "simplifyCNF"
	return cs
end

--------------------------------------------------------------------------------

-- RETURNS the number of unique variables in the CNF formula
local function cnfSize(cnf)
	local terms = {}
	for _, clause in ipairs(cnf) do
		for _, tpair in ipairs(clause) do
			terms[tpair[1]] = true
		end
	end
	local count = 0
	for k in pairs(terms) do
		count = count + 1
	end
	return count
end

local cnfSAT

-- RETURNS a (locally weakest) version of the assignment that is unsatisfiable
-- according to the theory as a CNF clause
local function unsatisfiableCoreClause(theory, assignment, order, meta)
	assertis(theory, "Theory")
	assertis(assignment, mapType(theory.assertion_t, "boolean"))
	assertis(order, listType(theory.assertion_t))
	assert(#order == #table.keys(assignment))

	local core = {}
	local reduced = assignment

	local i = 1
	local chunk = math.ceil(#order / 6)
	local d = ""
	while i <= #order do
		local without = {}
		for k, v in pairs(reduced) do
			without[k] = v
		end

		-- Remove the first `chunk` elements
		for j = i, math.min(#order, i + chunk - 1) do
			without[order[j]] = nil
		end

		local before = os.clock()
		-- TODO: this is far too slow.
		-- Using cnfSAT instead of isSatisfiable allows us to learn things
		-- about quantified statements, which are (typically) ignored by
		-- the theory solver
		local sat = cnfSAT(theory, {}, without, meta, false)
		--local sat = theory:isSatisfiable(without)
		if not sat then
			-- Constraints [i ... i + chunk - 1] are not part of the
			-- unsatisfiable core, as it remains unsatisfiable without those
			i = i + chunk
			d = d .. (("."):rep(chunk))
			chunk = chunk * 2
			reduced = without
		else
			-- At least some of [i ... i + chunk - 1] are part of the unsat
			-- core, since it became satisifiable after lifting them
			if chunk == 1 then
				-- Thus the ONLY term MUST be in the unsatisfiable core
				table.insert(core, {order[i], not assignment[order[i]]})
				i = i + 1
				d = d ..("*")
			else
				-- Reduce the number of cores being considered
				chunk = 1
			end
		end
	end
	return core
end

local asks = 0

-- RETURNS a truth assignment of theory terms {[term] => boolean} that satisfies
-- the specified CNF expression. Does NOT ensure that all terms are represented.
-- RETURNS false, unsat CNF core when no satisfaction is possible
-- Does NOT modify assignment
-- findCores: Determines whether or not this should search for unsat. cores in
--            bad models. When false, it does not do this search.
function cnfSAT(theory, cnf, assignment, meta, findCores)
	assert(type(assignment) == "table")
	assert(type(cnf) == "table")
	assert(type(findCores) == "boolean")

	cnf = simplifyCNF(theory, cnf, assignment)
	if not cnf then
		return false, {}
	end

	-- Find an assignment that the theory accepts
	if #cnf == 0 then
		-- Ask the theory if the assignment is consistent
		asks = asks + 1

		profile.open("theory:isSatisfiable")
		local out = theory:isSatisfiable(assignment)
		profile.close("theory:isSatisfiable")

		if not out then
			-- While this satisfies the SAT, the satisfaction doesn't work in
			-- the theory.
			if not findCores then
				return false, {}
			end

			-- TODO: ideally, these would be in reverse order
			local keys = table.keys(assignment)

			-- Sort for determinism
			table.sort(keys, function(a, b) return theory:canonKey(a) < theory:canonKey(b) end)


			-- Ask the theory for a minimal explanation of why this does not
			-- work in order to prune the CNF-SAT search space
			local coreClause = unsatisfiableCoreClause(theory, assignment, keys, meta)
			assert(1 <= #coreClause)

			return false, {coreClause}
		end

		-- Ask the theory if there are any extensions that can be made
		-- (e.g., from quantifierS) that may make the model unsatisfiable
		local additional, newMeta = theory:additionalClauses(assignment, meta)
		if #additional ~= 0 then
			local newCNF = {}
			for _, addition in ipairs(additional) do
				local addCNF = toCNF(theory, addition, true, {})
				newCNF = andCNF(newCNF, addCNF)
			end
			local sat, _ = cnfSAT(theory, newCNF, assignment, newMeta, findCores)

			if not sat and findCores then
				-- TODO: ideally, these would be in reverse order
				local keys = table.keys(assignment)

				-- Sort for determinism
				table.sort(keys, function(a, b) return theory:canonKey(a) < theory:canonKey(b) end)
				local core = unsatisfiableCoreClause(theory, assignment, keys, meta)
				assert(#core >= 1)
				return false, {core}
			end

			-- We cannot use subUnsatCore, because :additionalClauses makes NEW
			-- terms.

			-- TODO:
			-- We should compute an unsat core in terms of the conflicts between
			-- quantifier terms and other terms.
			return sat, {}
		end

		-- It could not have become unsatisfiable due to additional clauses
		assert(assignment)
		return assignment
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

	-- Try each truth assignment of the first term in the first clause
	local t1 = smallestClause[1][1]
	local withPositive = copywith(assignment, t1, smallestClause[1][2])
	local cnfPositive = simplifyCNF(theory, cnf, withPositive)

	local unsatCoreCNF = {}

	if cnfPositive then
		local out, betterCNF = cnfSAT(theory, cnfPositive, withPositive, meta, findCores)
		if out then
			return out
		end
		unsatCoreCNF = betterCNF
		cnf = andCNF(cnf, betterCNF)
	else
		-- It's a contradiction for `t1` to be assigned `smallestClause[1][2]`
		-- according to simplifyCNF
	end

	-- Then it can only be satisfied with no
	-- Add this to the set to prune more cases
	local withNegative = copywith(assignment, t1, not smallestClause[1][2])
	local cnfNegative = simplifyCNF(theory, cnf, withNegative)
	if not cnfNegative then
		return false, unsatCoreCNF
	end

	local out, moreUnsatCoreCNF = cnfSAT(theory, cnfNegative, withNegative, meta, findCores)
	if out then
		return out
	end
	return false, andCNF(unsatCoreCNF, moreUnsatCoreCNF)
end

-- RETURNS false | satisfaction
local function isSatisfiable(theory, expression)
	assert(theory)
	assert(expression)
	
	local cnf = toCNF(theory, expression, true, {})
	local sat = cnfSAT(theory, cnf, {}, theory:emptyMeta(), true)
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

	-- print("\n" .. string.rep("~", 80) .. "\n")
	-- print(showCNF(theory, cnf))
	-- print()

	profile.open("smt.implies sat")
	local sat = cnfSAT(theory, cnf, {}, theory:emptyMeta(), true)
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
	for x = 1, 4 do
		for y = 1, 4 do
			local all = true
			for k, v in pairs(model) do
				assert(type(v) == "boolean")
				if type(k) ~= "string" and k[1] == "f" then
					local e = k[2]
					e = e:gsub("x", tostring(x))
					e = e:gsub("y", tostring(y))
					local left, right = e:match("^(%d+)%s*==%s*(%d+)$")
					assert(left, "wrong pattern in `" .. e .. "`")
					if (left == right) ~= v then
						all = false
					end
				end
			end
			if all then
				return true
			end
		end
	end
	return false
end

function plaintheory:breakup(e, target)
	if type(e) == "string" then
		return false
	elseif e[1] == "f" then
		return false
	elseif e[1] == "d" then
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

function plaintheory:emptyMeta()
	return {}
end

function plaintheory:additionalClauses(model, meta)
	local newMeta = {}
	for k, v in pairs(meta) do
		newMeta[k] = v
	end
	
	local out = {}
	for key, value in pairs(model) do
		if not meta[key] then
			if type(key) == "table" and key[1] == "d" then
				newMeta[key] = true
				if value then
					table.insert(out, key[2])
				else
					table.insert(out, {"not", key[2]})
				end
			end
		end
	end
	return out, newMeta
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

-- Performance test (uses unsat cores)
for N = 20, 20 do
	--print("== N (simple, sat): " .. N .. " " .. string.rep("=", 80 - #tostring(N)))
	asks = 0

	local q = {"f", "x == 1"}
	for i = 1, N do
		local clause = {
			"x == " .. math.random(6, 999),
			"x == " .. math.random(6, 999),
			"x " .. string.rep(" ", i + 1) .. " == 1"
		}

		local a = freeze {"f", table.remove(clause, math.random(#clause))}
		local b = freeze {"f", table.remove(clause, math.random(#clause))}
		local c = freeze {"f", table.remove(clause, math.random(#clause))}
		local f = {"or", a, {"or", b, c}}
		q = {"and", q, f}
	end
	assert(isSatisfiable(plaintheory, q))

	--print("== N (simple, unsat): " .. N .. " " .. string.rep("=", 80 - #tostring(N)))
	asks = 0

	local q = {"f", "x == 1"}
	for i = 1, N do
		local clause = {
			"x == " .. math.random(6, 999),
			"x == " .. math.random(6, 999),
			"x " .. string.rep(" ", i + 1) .. " == 1"
		}

		if i == N - 1 then
			clause[3] = "x == " .. math.random(6, 999)
		end

		local a = freeze {"f", table.remove(clause, math.random(#clause))}
		local b = freeze {"f", table.remove(clause, math.random(#clause))}
		local c = freeze {"f", table.remove(clause, math.random(#clause))}
		local f = {"or", a, {"or", b, c}}
		q = {"and", q, f}
	end
	assert(not isSatisfiable(plaintheory, q))
end

assert(isSatisfiable(plaintheory, {"d", {"f", "x == 1"}}))
assert(not isSatisfiable(plaintheory, {"d", {"f", "x == 99"}}))
assert(isSatisfiable(plaintheory, {"and", {"d", {"f", "x == 1"}}, {"d", {"f", "x ==  1"}} }))
assert(not isSatisfiable(plaintheory, {"and", {"d", {"f", "x == 1"}}, {"d", {"f", "x == 2"}} }))

-- Performance test (uses unsat cores for quantifiers)
for N = 20, 20 do
	--print("== N (quant): " .. N .. " " .. string.rep("=", 80 - #tostring(N)))
	asks = 0

	local q = {"f", "x == 1"}
	for i = 1, N do
		local clause = {
			"x == " .. math.random(6, 999),
			"x == " .. math.random(6, 999),
			"x " .. string.rep(" ", i + 1) .. " == 1"
		}

		local a = {"f", table.remove(clause, math.random(#clause))}
		local b = {"f", table.remove(clause, math.random(#clause))}
		local c = {"f", table.remove(clause, math.random(#clause))}
		local f = {"or", {"d", a}, {"or", {"d", b}, {"d", c}}}
		q = {"and", q, f}
	end
	assert(isSatisfiable(plaintheory, q))
end

--------------------------------------------------------------------------------

return freeze {
	isSatisfiable = isSatisfiable,
	implies = implies,
}
