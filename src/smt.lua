-- A SMT Solver

local function copywith(t, k, v)
	local r = {}
	for key, value in pairs(t) do
		r[key] = value
	end
	r[k] = v
	return r
end

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

local function showCNF(theory, n)
	local clauses = {}
	for i = 1, #n do
		clauses[i] = showClause(theory, n[i])
	end
	return table.concat(clauses, " && ")
end

-- CNF (a ^ b) => (x ^ y)
-- is, by :breakup(true),
-- [(a ^ b) ^ (x ^ y)] v ~(a ^ b)

-- ~(a ^ b) by :breakup(false) is
-- ~a v [a ^ ~b]

--------------------------------------------------------------------------------

-- A THEORY is a record with
-- :breakup(expression): false | [expression], [[boolean | "*"]]
-- :canon(expression): unique value

local theory = {}

function theory:isSatisfiable(a)
	local anyGood = false
	for x = 1, 10 do
		for y = 1, 10 do
			for z = 1, 10 do
				local good = true
				for k, v in pairs(a) do
					if type(k) == "table" and k[1] == "f" then
						if k[2](x, y, z) ~= v then
							good = false
						end
					end
				end
				anyGood = anyGood or good
			end
		end
	end
	return anyGood
end

function theory:breakup(e, target)
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
	error "unknown"
end

function theory:canonKey(e)
	if type(e) == "string" then
		return string.format("%q", e)
	elseif type(e) == "function" then
		return tostring(e)
	end

	local list = {}
	for i = 1, #e do
		list[i] = theory:canonKey(e[i])
	end
	return "{" .. table.concat(list, ", ") .. "}"
end

--------------------------------------------------------------------------------

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

-- RETURNS a CNF description equivalent to (term == target)
-- A CNF expression is [][](term, boolean).
local function toCNF(theory, bigTerm, target, normalization)
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

	assert(#assignments >= 1)
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

--------------------------------------------------------------------------------

-- RETURNS a CNF simplified using the assignment such that all terms with
-- all terms with assignments do not appear in the theory
-- RETURNS false if the given cnf is unsatisfiable given the assignment
local function simplifyCNF(cnf, assignment)
	assert(type(assignment) == "table")

	local cs = {}
	for _, clause in ipairs(cnf) do
		local c = {}
		local contradiction = false

		-- Search the clause of terms with known truth assignments
		for _, term in ipairs(clause) do
			local e, truth = term[1], term[2]
			assert(type(truth) == "boolean")
			if assignment[e] ~= nil then
				if assignment[e] ~= truth then
					-- If only false terms are left, this clause is
					-- unsatisfiable.
					contradiction = true
				end
			else
				table.insert(c, term)
			end
		end

		-- Do not add empty clauses;
		-- empty clauses may represent True or False.
		if #c == 0 then
			if contradiction then
				return false
			end
		else
			table.insert(cs, c)
		end
	end
	return cs
end

--------------------------------------------------------------------------------

-- RETURNS a truth assignment of theory terms {[term] => boolean} that satisfies
-- the specified CNF expression. Does NOT ensure that all terms are represented.
-- RETURNS false when no satisfaction is possible
-- Does NOT modify assignment
local function cnfSAT(theory, cnf, assignment)
	assert(type(assignment) == "table")
	assert(type(cnf) == "table")
	--print("cnfSAT: ", showCNF(theory, cnf))
	--print("{")
	--for key, value in pairs(assignment) do
	--	print("", theory:canonKey(key), "=>", value)
	--end
	--print("}")
	--print()

	-- Find an assignment that the theory accepts
	if not theory:isSatisfiable(assignment) then
		return false
	elseif #cnf == 0 then
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
	if #smallestClause == 1 then
		-- Unit clauses have exactly one way to assign
		local term, truth = smallestClause[1][1], smallestClause[1][2]
		assert(assignment[term] == nil)
		local with = copywith(assignment, term, truth)
		local simplified = simplifyCNF(cnf, with)
		return simplified and cnfSAT(theory, simplified, with)
	end

	-- Try each truth assignment of the first term in the first clause
	local t1 = smallestClause[1][1]
	local with = copywith(assignment, t1, smallestClause[1][2])
	local simplified = simplifyCNF(cnf, with)
	local out = simplified and cnfSAT(theory, simplified, with)
	if out then
		return out
	end

	local with = copywith(assignment, t1, not smallestClause[1][2])
	local simplified = simplifyCNF(cnf, with)
	local out = simplified and cnfSAT(theory, simplified, with)
	if out then
		return out
	end
	return false
end

-- RETURNS false | satisfaction
local function isSatisfiable(theory, expression)
	assert(theory)
	assert(expression)

	local cnf = toCNF(theory, expression, true, {})
	local sat = cnfSAT(theory, cnf, {})
	return sat
end

--------------------------------------------------------------------------------

local function harness(e)
	print(string.rep("-", 80))
	print(theory:canonKey(e))
	local result = isSatisfiable(theory, e)
	if result then
		print("sat")
		for k, v in pairs(result) do
			print("", theory:canonKey(k), "=>", v)
		end
	else
		print("unsat")
	end
end

harness {"and", {"=>", "P", "Q"}, "R"}
harness {"=>", {"=>", "P", "Q"}, {"=>", "R", "S"}}
harness {"or", {"=>", "P", "Q"}, {"=>", "R", "S"}}
harness {"f", function(x, y, z) return x == 1 and y == 2 and z == 3 end}
