-- A SMT Solver

local profile = import "profile.lua"
local ansi = import "ansi.lua"

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

-- RETURNS a type
local function CNFType(theory)
	return recordType {_theory = constantType(theory)}
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
	local cs = "[" .. table.concat(terms, " || ") .. "]"
	return cs
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

local CNF = {}

-- PRIVATE
-- RETURNS a prepared clause, a maximum number of free tokens
local function cnfPrepareClause(theory, rawClause, index, assignment)
	assert(#rawClause > 0)
	assert(assignment)

	-- freeCount is the size of the free set
	local free = {}
	local freeCount = 0
	local dropped = {}
	local clause = {free = free, sat = {}, unsat = {}, satCount = 0}
	for _, tuple in ipairs(rawClause) do
		local key = theory:canonKey(tuple[1])
		if dropped[key] then
			-- Ignore: used in "a or ~a"
		elseif free[key] ~= nil then
			-- Redundant "a or a" or "a or ~a" cases
			if free[key][2] ~= tuple[2] then
				-- "a or ~a" case
				dropped[key] = true
				freeCount = freeCount - 1
				free[key] = nil
				assert(clause == table.remove(index[key]))
			end
		else
			-- Add new term to the free set
			free[key] = tuple
			index[key] = index[key] or {}
			table.insert(index[key], clause)
			freeCount = freeCount + 1
		end
	end
	local maxCount = freeCount

	-- Reclassify as necessary
	for key, tuple in pairs(clause.free) do
		if assignment[key] == tuple[2] then
			-- Has been satisfied
			freeCount = freeCount - 1
			clause.sat[key] = clause.free[key]
			clause.free[key] = nil
			clause.satCount = clause.satCount + 1
		elseif assignment[key] == not tuple[2] then
			-- Has been contradicted
			freeCount = freeCount - 1
			clause.unsat[key] = clause.free[key]
			clause.free[key] = nil
		end
	end
	clause.freeCount = freeCount

	return clause, maxCount
end

-- RETURNS a fresh CNF
-- clauses: a [][](term, boolean)
function CNF.new(theory, clauses, rawAssignment)
	assert(rawAssignment)

	-- Make enough room for the largest clause
	local unsatisfiedClausesBySize = {}
	local largest = 0
	for _, clause in ipairs(clauses) do
		largest = math.max(largest, #clause)
	end
	for i = 1, largest do
		unsatisfiedClausesBySize[i] = {}
	end

	-- Encode the assignment
	local assignment = {}
	for k, v in pairs(rawAssignment) do
		assignment[theory:canonKey(k)] = v
	end
	
	local instance = {
		_unsatisfiedClausesBySize = unsatisfiedClausesBySize,
		_index = {},
		_theory = theory,
		_satisfiedCount = 0,
		_contradictCount = 0,
		_allClauses = {},
		_learned = {},
		_assignment = assignment,
	}
	setmetatable(instance, {__index = CNF})
	
	-- Index the clauses
	for _, rawClause in ipairs(clauses) do
		instance:addClause(rawClause)
	end
	instance._learned = {}
	return instance
end

function CNF:show()
	local cs = {}
	for _, clause in ipairs(self._allClauses) do
		local c = {}
		for _, t in pairs(clause.free) do
			table.insert(c, t)
		end
		if #c > 0 then
			table.insert(cs, c)
		end
	end
	return showCNF(self._theory, cs)
end

function CNF:validate()
	do return end
	for _, clause in ipairs(self._allClauses) do
		assert(clause.freeCount == #table.keys(clause.free))
		if clause.freeCount > 0 then
			if clause.satCount == 0 then
				assert(self._unsatisfiedClausesBySize[clause.freeCount][clause])
			else
				assert(not self._unsatisfiedClausesBySize[clause.freeCount][clause])
			end
		end
		for i = 1, #self._unsatisfiedClausesBySize do
			if self._unsatisfiedClausesBySize[i][clause] then
				assert(i == clause.freeCount)
			end
		end
	end
end

-- Finds an unassigned term and returns a preferred truth value for it
-- RETURNS term, boolean
function CNF:pickUnassigned()
	self:validate()

	assert(not self:isDecided())
	for i = 1, #self._unsatisfiedClausesBySize do
		local clause = next(self._unsatisfiedClausesBySize[i])
		if clause then
			local key = next(clause.free)
			assert(type(key) == "string")
			local tuple = clause.free[key]
			return tuple[1], tuple[2]
		end
	end
	error "All terms are assigned"
end

-- REQUIRES term is an unassigned term for this CNF
-- MODIFIES this
-- RETURNS nothing
function CNF:assign(term, truth)
	self:validate()

	local key = self._theory:canonKey(term)
	self._assignment[key] = truth
	for _, clause in ipairs(self._index[key]) do
		local tuple = clause.free[key]
		assert(tuple and #tuple == 2)
		assert(type(tuple[2]) == "boolean")
		clause.free[key] = nil
		if tuple[2] == truth then
			clause.sat[key] = tuple
			clause.satCount = clause.satCount + 1
			if clause.satCount == 1 then
				self._satisfiedCount = self._satisfiedCount + 1
			end
		else
			clause.unsat[key] = tuple
		end

		-- Reduce free size
		self._unsatisfiedClausesBySize[clause.freeCount][clause] = nil
		clause.freeCount = clause.freeCount - 1

		if clause.satCount == 0 then
			if clause.freeCount == 0 then
				-- May not be satisfied; remains referenced by index
				self._contradictCount = self._contradictCount + 1
			else
				-- May still be satisfied
				self._unsatisfiedClausesBySize[clause.freeCount][clause] = true
			end
		else
			-- Already satisfied; remains referenced by index
		end
	end

	self:validate()
end

-- REQUIRES term is assigned for this CNF
-- MODIFIES this
-- RETURNS nothing
function CNF:unassign(term)
	self:validate()

	local key = self._theory:canonKey(term)
	assert(self._assignment[key] ~= nil)
	self._assignment[key] = nil
	for _, clause in ipairs(self._index[key]) do

		if clause.freeCount > 0 then
			self._unsatisfiedClausesBySize[clause.freeCount][clause] = nil
		end

		if clause.sat[key] then
			-- This clause was satisfied (at least in part) by term
			assert(1 <= clause.satCount)

			clause.free[key] = clause.sat[key]
			clause.freeCount = clause.freeCount + 1
			clause.sat[key] = nil
			clause.satCount = clause.satCount - 1
			if clause.satCount == 0 then
				-- This was the only satisfying term
				self._unsatisfiedClausesBySize[clause.freeCount][clause] = true
				self._satisfiedCount = self._satisfiedCount - 1
			end
		else
			-- This term is not part of the satisfaction of clause
			assert(clause.unsat[key])

			clause.free[key] = clause.unsat[key]
			clause.freeCount = clause.freeCount + 1
			if clause.satCount == 0 and clause.freeCount == 1 then
				-- This was fully false, but now might be satisfied
				assert(1 <= self._contradictCount)
				self._contradictCount = self._contradictCount - 1
			end
			
			if clause.satCount == 0 then
				self._unsatisfiedClausesBySize[clause.freeCount][clause] = true
			end
		end
	end

	self:validate()
end

-- RETURNS boolean
function CNF:isTautology()
	return #self._allClauses == self._satisfiedCount
end

-- RETURNS boolean
function CNF:isContradiction()
	return self._contradictCount ~= 0
end

-- RETURNS is decided, is tautology.
function CNF:isDecided()
	local isTautology = self:isTautology()
	local isContradiction = self:isContradiction()
	if isTautology or isContradiction then
		return true, isTautology
	end
	return false
end

function CNF:addClause(rawClause)
	self:validate()

	assert(1 <= #rawClause)

	local clause, max = cnfPrepareClause(self._theory, rawClause, self._index, self._assignment)

	if max == 0 then
		-- It is a tautology and did not change anything
		return
	end

	-- Grow as necessary
	for i = #self._unsatisfiedClausesBySize + 1, max do
		self._unsatisfiedClausesBySize[i] = {}
	end

	-- Add to appropriate place
	if clause.satCount == 0 and clause.freeCount > 0 then
		-- Not yet satisfied but still might be satisfiable
		self._unsatisfiedClausesBySize[clause.freeCount][clause] = true
	elseif clause.satCount > 0 then
		-- Already satisfied under current assignment
		self._satisfiedCount = self._satisfiedCount + 1
	else
		assert(clause.satCount == 0)
		assert(clause.freeCount == 0)

		-- Already contradicted by current assignment
		self._contradictCount = self._contradictCount + 1
	end

	table.insert(self._learned, rawClause)
	table.insert(self._allClauses, clause)

	self:validate()
end

-- RETURNS a list of [](term, truth) raw clauses
function CNF:learnedClauses()
	return self._learned
end

--------------------------------------------------------------------------------

-- RETURNS a shallow copy of t such that return[k] is v
local function copywith(t, k, v)
	local r = {}
	for key, value in pairs(t) do
		r[key] = value
	end
	r[k] = v
	return r
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
-- RETURNS a CNF description
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

-- RETURNS a (locally weakest) version of the assignment that is unsatisfiable
-- according to the theory as a CNF
local function unsatisfiableCoreClause(theory, assignment, order, meta)
	assertis(theory, "Theory")
	assertis(assignment, mapType(theory.assertion_t, "boolean"))
	assertis(order, listType(theory.assertion_t))
	assert(#order == #table.keys(assignment))

	-- Make a shallow copy, to slowly reduce
	local reduced = {}
	for k, v in pairs(assignment) do
		reduced[k] = v
	end

	local core = {}

	-- i is the lowest index that we are still unsure about
	local i = 1
	local chunk = math.ceil(#order / 6)
	while i <= #order do
		-- Remove the first `chunk` elements
		for j = i, math.min(#order, i + chunk - 1) do
			reduced[order[j]] = nil
		end

		local before = os.clock()

		-- Use the theory to determine if the model is unsatisfiable
		local sat = theory:isSatisfiable(reduced)
		if not sat then
			-- Constraints [i ... i + chunk - 1] are not part of the
			-- unsatisfiable core, as it remains unsatisfiable without those
			i = i + chunk
			chunk = chunk * 2
		else
			-- Restore the first `chunk` elements
			for j = i, math.min(#order, i + chunk - 1) do
				reduced[order[j]] = assignment[order[j]]
			end

			-- At least some of [i ... i + chunk - 1] are part of the unsat
			-- core, since it became satisifiable after lifting them
			if chunk == 1 then
				-- Thus the ONLY term MUST be in the unsatisfiable core
				table.insert(core, {order[i], not assignment[order[i]]})
				i = i + 1

				-- Optimistically increase chunk size
				chunk = math.floor(1 + (#order - i) / 6)
			else
				-- Reduce the number of cores being considered
				chunk = math.ceil(chunk / 2)
			end
		end
	end

	return {core}
end

-- Collapses an unsat-core using instatiated terms to refer instead to only
-- quantifiers.
-- assignment: must assign a truth value to each quantifier in `map`
-- map: maps each quantifier to a CNF that it implies
-- RETURNS a CNF
local function quantifierCore(theory, assignment, map, cnf)
	assertis(theory, "Theory")
	local rawCNF = listType(listType(tupleType(theory.assertion_t, "boolean")))
	assertis(assignment, mapType(theory.assertion_t, "boolean"))
	assertis(map, mapType(theory.assertion_t, rawCNF))
	assertis(cnf, rawCNF)

	-- Associate extra terms with their quantifiers
	local toQuantifier = {}
	for quantifier, instantiatedCNF in pairs(map) do
		assert(type(assignment[quantifier]) == "boolean")

		for _, clause in ipairs(instantiatedCNF) do
			for i, term in ipairs(clause) do
				local key = theory:canonKey(term[1])
				toQuantifier[key] = toQuantifier[key] or {}
				table.insert(toQuantifier[key], {
					quantifier = quantifier,
					clause = clause,
					truth = term[2],
					i = i,
				})
			end
		end
	end

	local output = {}
	local patterning = {}
	for _, must in ipairs(cnf) do
		-- Determine the "pattern" in terms of free terms
		local pattern = {}
		local filler = {}
		for _, t in ipairs(must) do
			local key = theory:canonKey(t[1])
			if not toQuantifier[key] then
				table.insert(pattern, {key = key, t = t})
			else
				table.insert(filler, {key = key, t = t})
			end
		end

		if #pattern == #must then
			-- The theory (for some odd reason) made a free clause
			table.insert(output, must)
		else
			-- The clause is not free
			local patternIDs = {}
			for i = 1, #pattern do
				patternIDs[i] = pattern[i].key .. "::" .. tostring(pattern[i].t)
			end
			table.sort(patternIDs)
			local patternID = table.concat(patternIDs, " ## ")

			local opposing = {}
			for i = 1, #filler do
				opposing[i] = {}
				local key = filler[i].key
				for _, triple in ipairs(toQuantifier[key]) do
					if triple.truth == not filler[i].t[2] then
						-- Opposes quantifier
						table.insert(opposing[i], triple)
					end
				end
			end
			assert(#opposing == #filler)
			assertis(opposing, listType(listType(recordType {
				truth = "boolean",
				i = "integer",
				clause = listType(tupleType(theory.assertion_t, "boolean")),
				quantifier = theory.assertion_t,
			})))

			for _, opposingTuple in ipairs(table.cartesian(opposing)) do
				-- Check that each quantifier is distinct
				-- TODO: what happens when two terms from the same quantifier
				-- are mentioned?
				local distinct = true
				local indexForQuantifier = {}
				local product = 1
				for _, t in ipairs(opposingTuple) do
					if indexForQuantifier[t.quantifier] then
						distinct = false
						break
					end
					indexForQuantifier[t.quantifier] = t.i
					product = product * #t.clause
				end

				if distinct then
					local indexTuple = {}
					local quantifierTuple = {}
					for q, i in spairs(indexForQuantifier, tostring) do
						table.insert(quantifierTuple, theory:canonKey(q))
						table.insert(indexTuple, i)
					end
					local qKey = table.concat(quantifierTuple, " ## ")
					local iKey = table.concat(indexTuple, ",")

					-- Record this as progress toward completing some grid
					if not patterning[patternID] then
						-- The first mention of the pattern
						patterning[patternID] = {
							pattern = pattern,
							instances = {},
						}
					end

					-- Set up the pattern for this particular combination of
					-- quantifier clauses
					if not patterning[patternID].instances[qKey] then
						patterning[patternID].instances[qKey] = {
							limit = product,
							count = 0,
							map = {},
						}
					end
					local p = patterning[patternID]
					if not p.instances[qKey].map[iKey] then
						p.instances[qKey].map[iKey] = true
						p.instances[qKey].count = p.instances[qKey].count + 1

						-- Check if we have completed a matrix
						if p.instances[qKey].limit == p.instances[qKey].count then
							local newClause = {}
							for i = 1, #pattern do
								newClause[i] = pattern[i].t
							end

							-- Negate each quantifier
							for q in spairs(indexForQuantifier, tostring) do
								assertis(q, theory.assertion_t)
								assertis(assignment[q], "boolean")
								table.insert(newClause, {q, not assignment[q]})
							end
							table.insert(output, newClause)
						end
					end
				end
			end
		end
		assertis(patterning, mapType("string", recordType {
			pattern = listType(recordType {
				t = tupleType(theory.assertion_t, "boolean"),
			}),
			instances = recordType {},
		}))

		-- TODO: combine partial matches into looser cores
	end

	return output
end

local asks = 0
local theoryTime = 0
local internals = 0

-- RETURNS a truth assignment of theory terms {[term] => boolean} that satisfies
-- the specified CNF expression. Does NOT ensure that all terms are represented.
-- RETURNS false when no such satisfaction exists
-- noModify: When true, ensures that `assignment` is not modified
-- MODIFIES assignment (when the assignment is satisfiable, and not noModify)
-- MODIFIES cnf to strengthen its clauses
local function cnfSAT(theory, cnf, assignment, meta, noModify)
	assert(type(assignment) == "table")
	assertis(cnf, CNFType(theory))
	assert(type(noModify) == "boolean")

	internals = internals + 1
	if cnf:isContradiction() then
		print("UNCOMMON")
		return false
	end

	-- Find an assignment that the theory accepts
	if cnf:isTautology() then
		-- Ask the theory if the assignment is consistent
		profile.open("theory:isSatisfiable")
		asks = asks + 1
		local beforeTime = os.clock()
		local out = theory:isSatisfiable(assignment)
		theoryTime = theoryTime + os.clock() - beforeTime
		profile.close("theory:isSatisfiable")

		if not out then
			-- While this satisfies the CNF, the satisfaction doesn't work in
			-- the theory.

			-- TODO: ideally, these would be in reverse order
			local keys = table.keys(assignment)

			-- Sort for determinism
			table.sort(keys, function(a, b)
				return theory:canonKey(a) < theory:canonKey(b)
			end)

			-- Ask the theory for a minimal explanation of why this does not
			-- work in order to prune the CNF-SAT search space
			local coreClauses = unsatisfiableCoreClause(theory, assignment, keys, meta)
			for _, coreClause in ipairs(coreClauses) do
				cnf:addClause(coreClause)
			end
			return false
		end

		-- Ask the theory if there are any extensions that can be made
		-- (e.g., from quantifierS) that may make the model unsatisfiable
		local additional, newMeta = theory:additionalClauses(assignment, meta)
		if next(additional) ~= nil then
			-- Track which terms originate from which quantifiers
			local expansionClauses = {}
			local newClauses = {}
			for quantified, results in pairs(additional) do
				expansionClauses[quantified] = {}
				for _, result in ipairs(results) do
					local addCNF = toCNF(theory, result, true, {})
					for _, clause in ipairs(addCNF) do
						table.insert(expansionClauses[quantified], clause)
						table.insert(newClauses, clause)
					end
				end
			end

			local newCNF = CNF.new(theory, newClauses, assignment)
			local sat = cnfSAT(theory, newCNF, assignment, newMeta, noModify)
			if not sat then
				-- The core may use NEW terms; if we return them, we could
				-- INCREASE the size of the CNF, which would be
				-- counterproductive.
				-- Deduce which of these contradict assignments for the
				-- quantifiers instead of the instantiations.
				local core = newCNF:learnedClauses()
				local coreClauses = quantifierCore(theory, assignment, expansionClauses, core)
				for _, coreClause in ipairs(coreClauses) do
					cnf:addClause(coreClause)
				end
				return false
			end

			return sat
		end

		-- It could not have become unsatisfiable due to additional clauses
		assert(assignment)
		return assignment
	end

	-- Try each truth assignment of the first term in the first clause
	local term, prefer = cnf:pickUnassigned()
	assert(assignment[term] == nil, "pickUnassigned should prevent this")

	local before = #cnf:learnedClauses()
	-- Assignment is now positive
	assignment[term] = prefer
	cnf:assign(term, prefer)

	if not cnf:isContradiction() then
		local out = cnfSAT(theory, cnf, assignment, meta, noModify)
		if out then
			if noModify then
				-- Restore assignment
				assignment[term] = nil
				cnf:unassign(term)
			end
			return out
		end
	end
	cnf:unassign(term)

	-- Add this to the set to prune more cases
	-- Assignment is now negative
	assignment[term] = not prefer
	cnf:assign(term, not prefer)
	if not cnf:isContradiction() then
		local out = cnfSAT(theory, cnf, assignment, meta, noModify)
		if out then
			if noModify then
				-- Restore assignment
				assignment[term] = nil
				cnf:unassign(term)
			end
			return out
		end
	end
	assignment[term] = nil
	cnf:unassign(term)
	return false
end

-- Determine whether or not `expression` is satisfiable in the given `theory`.
-- RETURNS false | satisfaction
local function isSatisfiable(theory, expression)
	assert(theory)
	assert(expression)

	local clauses = toCNF(theory, expression, true, {})
	local cnf = CNF.new(theory, clauses, {})
	local sat = cnfSAT(theory, cnf, {}, theory:emptyMeta(), false)
	return sat
end

--------------------------------------------------------------------------------

-- Determine whether or not `givens` together imply `expression` in the given
-- `theory`.
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

	local clauses = toCNFFromBreakup(theory, args, {truths}, {})
	profile.close("smt.implies setup")

	profile.open("smt.implies sat")
	local cnf = CNF.new(theory, clauses, {})
	local sat = cnfSAT(theory, cnf, {}, theory:emptyMeta(), false)
	profile.close("smt.implies sat")

	if sat then
		return false, sat
	end
	return true
end

--------------------------------------------------------------------------------

-- plaintheory is an implementation of a Theory used to test the SMT solver
local plaintheory = {assertion_t = "any"}

-- Test theory
function plaintheory:isSatisfiable(model)
	for x = 1, 2 do
		for y = 1, 2 do
			local all = true
			for k, v in pairs(model) do
				assert(type(v) == "boolean")
				if type(k) ~= "string" and k[1] == "f" then
					local e = k[2]
					local left = e:match "^%S+"
					local right = e:match "%S+$"
					assert(left and right, "wrong pattern")

					-- Plug in variables
					if left == "x" then
						left = x
					elseif left == "y" then
						left = y
					else
						left = tonumber(left)
					end
					if right == "x" then
						right = x
					elseif right == "y" then
						right = y
					else
						right = tonumber(right)
					end

					-- Evaluate equality
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
					out[key] = {key[2]}
				else
					out[key] = {{"not", key[2]}}
				end
			end
		end
	end
	return out, newMeta
end

plaintheory = freeze(plaintheory)

-- Establish the domain of the theory
assert(not isSatisfiable(plaintheory, {"f", "x == 0"}), "unsat x == 0")
assert(isSatisfiable(plaintheory, {"f", "x == 1"}), "sat x == 1")
assert(isSatisfiable(plaintheory, {"f", "x == 2"}), "sat x == 2")
assert(not isSatisfiable(plaintheory, {"f", "x == 3"}), "unsat x == 3")

do
	-- Test CNF library
	local problem = CNF.new(plaintheory, {
		-- Tautology
		{{"a", true}, {"a", false}},
		{{"a", true}, {"b", true}, {"b", true}},
		{{"x", true}, {"y", true}, {"z", false}, {"a", true}, {"b", false}},
	}, {})

	assert(not problem:isDecided())
	assert(not problem:isTautology())
	assert(not problem:isContradiction())
	local v1, prefer1 = problem:pickUnassigned()
	assert(prefer1)
	assert(v1 == "a" or v1 == "b")
	problem:assign(v1, not prefer1)
	assert(not problem:isDecided(), "must not yet be decided")
	local v2, prefer2 = problem:pickUnassigned()
	assert(v1 ~= v2)
	assert(v2 == "a" or v2 == "b")
	assert(prefer2 == true)
	problem:assign(v2, not prefer2)
	assert(problem:isDecided(), "must be decided")
	assert(problem:isContradiction(), "must be contradiction")
	assert(not problem:isTautology(), "must not be tautology")
	problem:unassign(v2)
	assert(not problem:isDecided(), "must no longer be decided")
	assert(not problem:isContradiction(), "must no longer be contradiction")
	assert(not problem:isTautology(), "must still not be tautology")
	problem:unassign(v1)
	assert(not problem:isDecided())
	problem:assign("a", false)
	problem:assign("b", true)
	assert(not problem:isDecided())
	problem:assign("z", false)
	assert(problem:isDecided(), "problem is now decided")
	assert(problem:isTautology(), "problem is now tautology")
	assert(not problem:isContradiction(), "problem is not a contradiction")
end

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
assert(isSatisfiable(plaintheory, m5), "sat m5")

assert(not implies(
	plaintheory,
	{
		{"f", "x == y"},
		{"or", {"f", "x == 1"}, {"f", "x == 2"}},
	},
	{"f", "y == 2"}
))

-- Performance test (uses unsat cores)
for N = 30, 200, 10 do
	--print("== N (simple, sat): " .. N .. " " .. string.rep("=", 80 - #tostring(N)))
	asks = 0
	internals = 0
	theoryTime = 0
	local beforeTime = os.clock()

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
	assert(isSatisfiable(plaintheory, q), "must be sat")

	--print("== N (simple, unsat): " .. N .. " " .. string.rep("=", 80 - #tostring(N)))
	local afterTime = os.clock()
	print("NO QUANTIFIERS:")
	print(asks .. " invocations of theory:isSatisfiable (" .. math.floor(theoryTime / asks * 1e6) .. "us each)")
	print(internals .. " invocations of cnfSAT (" .. math.floor((afterTime - theoryTime) / internals * 1e6) .. "us each)")
	print("Elapsed for N=" .. N .. " test: " .. afterTime - beforeTime)
	print("\tElapsed in theory: " .. string.format("%.3f", theoryTime))
	print()
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
	--assert(not isSatisfiable(plaintheory, q))
end

assert(isSatisfiable(plaintheory, {"d", {"f", "x == 1"}}))
assert(not isSatisfiable(plaintheory, {"d", {"f", "x == 99"}}))
assert(isSatisfiable(plaintheory, {"and", {"d", {"f", "x == 1"}}, {"d", {"f", "x ==  1"}}}))
assert(not isSatisfiable(plaintheory, {"and", {"d", {"f", "x == 1"}}, {"d", {"f", "x == 2"}}}))

-- Performance test (uses unsat cores for quantifiers)
for N = 50, 200, 10 do
	--print("== N (quant): " .. N .. " " .. string.rep("=", 80 - #tostring(N)))
	asks = 0
	internals = 0
	theoryTime = 0
	local beforeTime = os.clock()

	local q = {"f", "x == 1"}
	for i = 1, N do
		local clause = {
			"x == " .. math.random(6, 999),
			"x " .. string.rep(" ", i + 1) .. " == 2",
			"x " .. string.rep(" ", i + 1) .. " == 1"
		}

		local a = {"f", table.remove(clause, math.random(#clause))}
		local b = {"f", table.remove(clause, math.random(#clause))}
		local c = {"f", table.remove(clause, math.random(#clause))}
		local f = {"or", {"d", a}, {"or", {"d", b}, {"d", c}}}
		q = {"and", q, {"d", f}}
	end
	assert(isSatisfiable(plaintheory, q))

	local afterTime = os.clock()
	print("WITH QUANTIFIERS:")
	print(asks .. " invocations of theory:isSatisfiable (" .. math.floor(theoryTime / asks * 1e6) .. "us each)")
	print(internals .. " invocations of cnfSAT (" .. math.floor((afterTime - theoryTime) / internals * 1e6) .. "us each)")
	print("Elapsed for N=" .. N .. " test: " .. afterTime - beforeTime)
	print()
end

--------------------------------------------------------------------------------

return freeze {
	isSatisfiable = isSatisfiable,
	implies = implies,
}
