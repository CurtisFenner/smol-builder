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

--------------------------------------------------------------------------------

local CNF = {}

-- PRIVATE
-- RETURNS a prepared clause, a maximum number of free tokens
function CNF:_prepareClause(rawClause)
	assert(#rawClause > 0)
	assert(self._assignment)

	local canonicalizedClause = {}
	local maxCount = 0
	for i = 1, #rawClause do
		local truth = rawClause[i][2]
		local key = self:canonicalize(rawClause[i][1])
		if canonicalizedClause[key] == nil then
			canonicalizedClause[key] = truth
			maxCount = maxCount + 1
		elseif canonicalizedClause[key] ~= truth then
			-- "x or v or ~v" case
			-- Drop clause
			return {}, 0
		end
	end

	-- freeCount is the size of the free set
	local clause = {
		free = {},
		freeCount = 0,
		sat = {},
		satCount = 0,
		unsat = {},
	}
	for key, truth in pairs(canonicalizedClause) do
		self._index[key] = self._index[key] or {}
		table.insert(self._index[key], clause)
		if self._assignment[key] == truth then
			-- Satisfied term
			clause.sat[key] = {key, truth}
			clause.satCount = clause.satCount + 1
		elseif self._assignment[key] == not truth then
			-- Contradicted term
			clause.unsat[key] = {key, truth}
		else
			-- Free term
			clause.free[key] = {key, truth}
			clause.freeCount = clause.freeCount + 1
		end
	end

	return clause, maxCount
end

-- RETURNS a fresh CNF
-- clauses: a [][](term, boolean)
function CNF.new(theory, clauses, rawAssignment)
	assert(rawAssignment)
	assert(theory)

	-- Make enough room for the largest clause
	local unsatisfiedClausesBySize = {}
	local largest = 0
	for _, clause in ipairs(clauses) do
		largest = math.max(largest, #clause)
	end
	for i = 1, largest do
		unsatisfiedClausesBySize[i] = {}
	end

	local instance = {
		_unsatisfiedClausesBySize = unsatisfiedClausesBySize,
		_index = {},
		_theory = theory,
		_satisfiedCount = 0,
		_contradictCount = 0,
		_allClauses = {},
		_learned = {},
		_canon = {},
		_isCanon = {},
		_assignment = {},
	}
	setmetatable(instance, {__index = CNF})

	-- Canonicalize the assignment
	for k, v in pairs(rawAssignment) do
		assert(type(v) == "boolean")
		local canonicalized = instance:canonicalize(k)
		assert(nil == instance._assignment[canonicalized], "not canonicalized")
		instance._assignment[canonicalized] = v
	end

	-- Index the clauses
	for _, rawClause in ipairs(clauses) do
		instance:addClause(rawClause)
	end
	instance._learned = {}
	return instance
end

-- RETURNS an equivalent term to term, canonicalize by the canon key
function CNF:canonicalize(term)
	if self._isCanon[term] then
		return term
	end

	local key = self._theory:canonKey(term)
	local out = self._canon[key]
	if not out then
		self._canon[key] = term
		self._isCanon[term] = true
		return term
	end
	return out
end

-- RETURNS the set of free terms in this
function CNF:freeTermSet()
	local out = {}
	local added = {}
	for _, clause in ipairs(self._allClauses) do
		for _, t in pairs(clause.free) do
			if not added[t[1]] then
				added[t[1]] = true
				table.insert(out, t[1])
			end
		end
	end
	return out
end

-- RETURNS nothing
-- For debugging
function CNF:validate()
	do
		return
	end
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
			local tuple = clause.free[key]
			assert(key == tuple[1])
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

	-- Update the assignment map
	local key = self:canonicalize(term)
	assert(self._assignment[key] == nil)
	self._assignment[key] = truth

	-- Update the clauses mentioning this term
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

	-- Update the assignment map
	local key = self:canonicalize(term)
	assert(self._assignment[key] ~= nil)
	self._assignment[key] = nil

	-- Update the clauses mentioning this term
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

	local clause, max = self:_prepareClause(rawClause)
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

-- RETURNS a map from theory terms => booleans which is the current truth
-- assignment
function CNF:getAssignment()
	local out = {}
	for k, v in pairs(self._assignment) do
		out[k] = v
	end
	return out
end

--------------------------------------------------------------------------------

-- a: a CNF description
-- b: a CNF description
-- RETURNS a CNF description
local function disjunctionOfCNF(theory, a, b)
	local clauses = {}
	for _, x in ipairs(a) do
		for _, y in ipairs(b) do
			local disjunction = {}
			for _, t in ipairs(x) do
				table.insert(disjunction, t)
			end
			for _, t in ipairs(y) do
				table.insert(disjunction, t)
			end
			table.insert(clauses, disjunction)
		end
	end
	return clauses
end

local toCNF

local function toCNFFromBreakup(theory, terms, assignments, normalization)
	assertis(theory, "Theory")
	assertis(terms, listType(theory.assertion_t))
	local maybeBool = choiceType("boolean", constantType "*")
	assertis(assignments, listType(listType(maybeBool)))
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

-- RETURNS a (locally weakest) version of the assignment that is unsatisfiable
-- according to the theory as a CNF
local function unsatisfiableCoreClause(theory, assignment, order)
	assertis(theory, "Theory")
	assertis(assignment, mapType(theory.assertion_t, "boolean"))
	assertis(order, listType(theory.assertion_t))
	assert(#order == #table.keys(assignment))

	if theory:isSatisfiable(assignment) then
		return {}
	end

	-- Make a shallow copy, to slowly reduce
	local reduced = {}
	for k, v in pairs(assignment) do
		reduced[k] = v
	end

	local core = {}
	local coreIndex = {}

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
				coreIndex[i] = true
				i = i + 1

				-- Optimistically increase chunk size
				chunk = math.floor(1 + (#order - i) / 6)
			else
				-- Reduce the number of cores being considered
				chunk = math.ceil(chunk / 2)
			end
		end
	end

	local smallerAssignment = {}
	local smallerOrder = {}
	for i = 1, #order do
		if not coreIndex[i] then
			smallerAssignment[order[i]] = assignment[order[i]]
			table.insert(smallerOrder, order[i])
		end
	end
	local cores = unsatisfiableCoreClause(
		theory,
		smallerAssignment,
		smallerOrder
	)
	table.insert(cores, core)
	return cores
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

-- RETURNS a truth assignment of theory terms {[term] => boolean} that satisfies
-- the specified CNF expression. Does NOT ensure that all terms are represented.
-- RETURNS false when no such satisfaction exists
-- MODIFIES cnf to strengthen its clauses
local function cnfSAT(theory, cnf, meta)
	local stack = {}
	while true do
		if false then
			-- Debug printing
			local assignment = cnf:getAssignment()
			local keys = table.keys(assignment)
			for _, t in ipairs(cnf:freeTermSet()) do
				table.insert(keys, t)
			end
			table.sort(keys, function(a, b) return theory:canonKey(a) < theory:canonKey(b) end)
			local description = {}
			for i = 1, #keys do
				if assignment[keys[i]] == nil then
					description[i] = "."
				elseif assignment[keys[i]] then
					description[i] = "#"
				else
					description[i] = "@"
				end
			end
			print(table.concat(description))
		end

		if cnf:isTautology() then
			local currentAssignment = cnf:getAssignment()
			local out, conflicting = theory:isSatisfiable(currentAssignment)
			if not out then
				assert(conflicting)

				-- While this truth model satisfies the CNF, the satisfaction
				-- doesn't work in the theory
				local keys = table.keys(conflicting)
				table.sort(keys, function(a, b)
					return theory:canonKey(a) < theory:canonKey(b)
				end)

				-- Ask the theory for a minimal explanation why this didn't work
				local coreClauses = unsatisfiableCoreClause(
					theory,
					conflicting,
					keys
				)
				for _, coreClause in ipairs(coreClauses) do
					cnf:addClause(coreClause)
				end
			else
				-- Expand quantified statements using the theory
				local additional, newMeta = theory:additionalClauses(
					currentAssignment,
					meta
				)

				if next(additional) == nil then
					-- There are no quantifiers to expand; we are done!
					return currentAssignment
				end

				-- Expand the additions
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

				-- Recursively solve the new SAT problem
				local newCNF = CNF.new(theory, newClauses, currentAssignment)
				local sat = cnfSAT(theory, newCNF, newMeta)
				if sat then
					-- Even after expanding quantifiers, the formula remained
					-- satisfiable
					return sat
				end

				-- Reject the current assignment in its entirety
				local notCurrent = {}
				for k, v in pairs(currentAssignment) do
					table.insert(notCurrent, {k, not v})
				end
				cnf:addClause(notCurrent)

				-- Attempt to generalize the learned core clauses
				-- (cnf cannot mention new terms that may have been
				-- introduced by instantiation)
				local core = newCNF:learnedClauses()
				local coreClauses = quantifierCore(
					theory,
					currentAssignment,
					expansionClauses,
					core
				)
				for _, coreClause in ipairs(coreClauses) do
					cnf:addClause(coreClause)
				end
			end
		elseif cnf:isContradiction() then
			-- Some assignment made by the SAT solver is bad
			-- TODO: conflict clauses
			while true do
				if #stack == 0 then
					-- There are no choices to undo
					return false
				end

				local variable = stack[#stack].variable
				local preferred = stack[#stack].preferTruth
				if stack[#stack].first then
					-- Flip the assignment
					stack[#stack].first = false
					cnf:unassign(variable)
					cnf:assign(variable, not preferred)
					break
				else
					-- Backtrack
					cnf:unassign(variable)
					stack[#stack] = nil
				end
			end
		else
			-- Make a choice
			local term, prefer = cnf:pickUnassigned()
			table.insert(stack, {
				variable = term,
				preferTruth = prefer,
				first = true,
			})
			cnf:assign(term, prefer)
		end
	end
end

--------------------------------------------------------------------------------

-- Determine whether or not `expression` is satisfiable in the given `theory`.
-- RETURNS false | satisfaction
local function isSatisfiable(theory, expression)
	assert(theory)
	assert(expression)

	local clauses = toCNF(theory, expression, true, {})
	local cnf = CNF.new(theory, clauses, {})
	local sat = cnfSAT(theory, cnf, theory:emptyMeta())
	return sat
end

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
	local sat = cnfSAT(theory, cnf, theory:emptyMeta())
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
	return false, model
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
	local problem = CNF.new(
		plaintheory,
		{
			-- Tautology
			{{"a", true}, {"a", false}},
			{{"a", true}, {"b", true}, {"b", true}},
			{{"x", true}, {"y", true}, {"z", false}, {"a", true}, {"b", false}},
		},
		{}
	)

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
for N = 50, 0, 10 do
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
assert(isSatisfiable(
	plaintheory,
	{"and", {"d", {"f", "x == 1"}}, {"d", {"f", "x ==  1"}}}
))
assert(not isSatisfiable(
	plaintheory,
	{"and", {"d", {"f", "x == 1"}}, {"d", {"f", "x == 2"}}}
))

-- Performance test (uses unsat cores for quantifiers)
for N = 50, 0, 10 do
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
end

--------------------------------------------------------------------------------

return freeze {
	isSatisfiable = isSatisfiable,
	implies = implies,
}
