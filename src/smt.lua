-- A SMT Solver

local Map = import "data/map.lua"
local Rope = import "data/rope.lua"
local ansi = import "ansi.lua"
local Stopwatch = import "stopwatch.lua"

REGISTER_TYPE("TheoryModel", recordType {
	-- RETURNS true when the model may be inhabited
	-- RETURNS false ONLY when it is provable that the model is not satisfiable
	-- MODIFIES nothing
	isSatisfiable = "function",

	-- RETURNS new model
	-- MODIFIES nothing
	-- self:assign(assertion_t, boolean)
	assigned = "function",
})

REGISTER_TYPE("Theory", recordType {
	isSatisfiable = "nil",

	-- argument: (self, assertion_t, boolean)
	-- RETURNS false
	-- RETURNS [assertion_t], [[boolean]]
	breakup = "function",

	assertion_t = "any",

	-- argument: (self, assertion_t)
	-- RETURNS an object with a consistent identity (strings are simple)
	canonKey = "function",

	-- argument: (self, simpleModel, cnf, additionalInfo)
	-- RETURNS {assertion_t => {true, false => [assertion_t]}}, additionalInfo
	-- additionalInfo is used to manage recursive instantiations, and may be
	-- returned as nil
	additionalClauses = "function",

	-- RETURNS an empty "model" which can have theory terms assigned truths
	-- via :assign(term, truth)
	-- and :unassign()
	-- and :isSatisfiable()
	makeEmptyModel = "function",
})

--------------------------------------------------------------------------------

local CNF = {}

-- RETURNS a fresh CNF
-- clauses: a [][](term, boolean)
function CNF.new(theory, rawClauses, rawAssignment)
	assert(rawAssignment, "needs rawAssignment")
	assert(theory, "needs theory")
	assert(rawClauses, "needs raw clauses")

	local instance = {
		_clauses = {
			unit = {},
			horn = {},
			sat = {},
			contradiction = {},
			other = {},
		},
		_theory = theory,
		_assignment = {},

		-- Canonicalization
		_canon = {},
		_isCanon = {},

		-- {term => []clause}
		_termUsages = {},
	}
	setmetatable(instance, {__index = CNF})

	-- Canonicalize the assignment
	for k, v in pairs(rawAssignment) do
		assert(type(v) == "boolean")
		local canonicalized = instance:_canonicalize(k)
		assert(nil == instance._assignment[canonicalized], "not canonicalized")
		instance._assignment[canonicalized] = v
	end

	-- Index the clauses
	for _, rawClause in ipairs(rawClauses) do
		instance:addClause(rawClause)
	end

	-- No new terms should be created in canonicalization after this point
	instance._constructed = true
	return instance
end

function CNF:printStats()
	print("CNF:")
	print("", #table.keys(self._assignment) .. " assignments")
	print("", "Clauses:")
	print("", "", #table.keys(self._clauses.other) .. " other clauses")
	print("", "", #table.keys(self._clauses.horn) .. " horn clauses")
	print("", "", #table.keys(self._clauses.unit) .. " unit clauses")
	print("", "--")
	print("", "", #table.keys(self._clauses.sat) .. " satisified clauses")
	print("", "", #table.keys(self._clauses.contradiction) .. " contradiction clauses")
	print()
end

-- RETURNS all clauses that have been added to this CNF databse
function CNF:allRawClauses()
	local list = {}

	for _, class in pairs(self._clauses) do
		for clause in pairs(class) do
			table.insert(list, clause.raw)
		end
	end

	return list
end

-- RETURNS an equivalent term to term, canonicalize by the canon key
-- REQUIRES term is not a new term (after CNF.new returns)
function CNF:_canonicalize(term)
	if self._isCanon[term] then
		return term
	end

	local key = self._theory:canonKey(term)
	local out = self._canon[key]
	if not out then
		assert(not self._constructed, "canonicalize invoked on fresh term")
		self._canon[key] = term
		self._termUsages[term] = {
			all = {},
			byClass = {},
		}
		for key in pairs(self._clauses) do
			self._termUsages[term].byClass[key] = {
				[true] = {},
				[false] = {},
			}
		end
		self._isCanon[term] = true
		return term
	end
	return out
end

-- RETURNS nothing
-- For debugging
function CNF:validate()

end

-- Finds an unassigned term and returns a preferred truth value for it
-- RETURNS term, boolean prefer, boolean forced
-- REQUIRES this is not decided
function CNF:pickUnassigned()
	self:validate()

	assert(not self:isDecided())

	-- Solve unit clauses
	local unitClause = next(self._clauses.unit)
	if unitClause then
		local term = next(unitClause.freeLiterals)
		assert(term ~= nil)
		return term, unitClause.freeLiterals[term], true
	end
	
	-- If there are non-horn clauses, this is a "hard" CNF
	local otherClause = next(self._clauses.other)
	if otherClause then
		-- Find interesting terms to prioritize
		-- TODO: (1) Pure terms are easy
		-- TODO: (2) Terms which appear only positively in horn clauses and more
		-- positively than negatively can be flipped
		
		-- TODO: order terms that appear in these clauses
		-- Pick a positive term, to move this clause towards being a Horn clause
		for term, truth in pairs(otherClause.freeLiterals) do
			if truth then
				return term, true, false
			end
		end

		error "unreachable"
	end

	-- Horn CNFs without unit clauses are always satisfiable by assigning
	-- each free negative literal to true
	local hornClause = next(self._clauses.horn)
	if hornClause then
		-- Assign every negated literal to true
		-- This is guaranteed to satisfy a CNF of all Horn clauses without
		-- any unit clauses
		for term, truth in pairs(hornClause.freeLiterals) do
			if not truth then
				return term, false, false
			end
		end

		error "unreachable"
	end

	error "unreachable"
end

-- RETURNS a map of assignments made
-- MODIFIES this
function CNF:forceAssignments()
	self:validate()

	local map = {}
	while not self:isDecided() do
		local term, truth, force = self:pickUnassigned()
		if not force then
			return map
		end
		map[term] = truth
		self:assign(term, truth)
	end
	return map
end

-- REQUIRES term is an unassigned term for this CNF
-- MODIFIES this
-- RETURNS nothing
function CNF:assign(term, truth)
	self:validate()

	-- Update the assignment map
	local key = self:_canonicalize(term)
	assert(self._assignment[key] == nil, "term must not already be assigned")

	-- Move all of the clauses
	for _, clause in ipairs(self._termUsages[key].all) do
		local class = self:_classifyClause(clause)
		assert(self._clauses[class][clause])
		self._clauses[class][clause] = nil
	end

	self._assignment[key] = truth

	for _, clause in ipairs(self._termUsages[key].all) do
		local class = self:_classifyClause(clause)
		self._clauses[class][clause] = true
	end

	self:validate()
end

-- REQUIRES term is assigned for this CNF
-- MODIFIES this
-- RETURNS nothing
function CNF:unassign(term)
	self:validate()

	-- Update the assignment map
	local key = self:_canonicalize(term)
	assert(self._assignment[key] ~= nil)

	-- Move all of the clauses
	for _, clause in ipairs(self._termUsages[key].all) do
		local class = self:_classifyClause(clause)
		assert(self._clauses[class][clause])
		self._clauses[class][clause] = nil
	end

	self._assignment[key] = nil

	for _, clause in ipairs(self._termUsages[key].all) do
		local class = self:_classifyClause(clause)
		self._clauses[class][clause] = true
	end

	self:validate()
end

-- RETURNS "horn" | "sat" | "contradiction" | "unit" | "other"
-- MODIFIES clause to have correct freeLiterals set
function CNF:_classifyClause(clause)
	local positive = 0
	local negative = 0
	local sat = false
	clause.freeLiterals = {}
	for key, truth in pairs(clause.allLiterals) do
		if self._assignment[key] == nil then
			if truth then
				positive = positive + 1
			else
				negative = negative + 1
			end
			clause.freeLiterals[key] = truth
		elseif self._assignment[key] == truth then
			-- This clause is already satisfied
			sat = true
		end
	end

	if sat then
		return "sat"
	end

	if positive + negative == 0 then
		-- This clause is not satisfied and has no free literals
		return "contradiction"
	elseif positive + negative == 1 then
		-- This clasue has only one free literal
		return "unit"
	elseif positive <= 1 then
		-- This is a Horn clause
		return "horn"
	end
	return "other"
end

-- RETURNS nothing
-- MODIFIES this
function CNF:addClause(rawClause)
	self:validate()
	assert(1 <= #rawClause)

	-- Canonicalize and deup the literals in the raw clause
	local allLiterals = {}
	for _, t in ipairs(rawClause) do
		local rawKey = t[1]
		local truth = t[2]
		local key = self:_canonicalize(rawKey)
		if allLiterals[key] ~= nil and allLiterals[key] ~= true then
			-- x or ~x
			-- is always TRUE and does not change the clause database
			return
		end
		allLiterals[key] = truth
	end

	-- Create the clause
	local clause = {
		allLiterals = allLiterals,

		-- Updated by classifyClause
		freeLiterals = {},

		raw = rawClause,
	}

	-- Index the term references
	for key in pairs(allLiterals) do
		table.insert(self._termUsages[key].all, clause)
	end

	-- Index the clause
	local class = self:_classifyClause(clause)
	self._clauses[class][clause] = true

	self:validate()
end

-- RETURNS boolean
function CNF:isTautology()
	local noUnit = next(self._clauses.unit) == nil
	local noHorn = next(self._clauses.horn) == nil
	local noOther = next(self._clauses.other) == nil
	local noContradiction = next(self._clauses.contradiction) == nil
	return noContradiction and noUnit and noHorn and noOther 
end

-- RETURNS boolean
function CNF:isContradiction()
	return next(self._clauses.contradiction) ~= nil
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

local toCNF

-- RETURNS a CNF as a Rope of lists of literals
-- assignments: [][]("*" | true | false)
local function toCNFFromBreakup(theory, terms, assignments, normalization)
	local cnfs = {}
	for _, assignment in ipairs(assignments) do
		local clauses = Rope.empty()
		assert(#assignment == #terms)
		for i, term in ipairs(terms) do
			if assignment[i] ~= "*" then
				-- assert(type(assignment[i]) == "boolean")
				local subCNF = toCNF(theory, term, assignment[i], normalization)
				clauses = clauses .. subCNF
			end
		end
		table.insert(cnfs, clauses)
	end

	-- bigTerm is equivalent to the disjunction of `cnfs`, a set of CNFs
	-- To create a single CNF, must distribute disjunctions
	local out = cnfs[1]
	for i = 2, #cnfs do
		local right = cnfs[i]
		local cnfDisjunction = Rope.empty()
		for _, leftClause in out:traverse() do
			for _, rightClause in right:traverse() do
				local truth = {}
				local clauseDisjunction = {}
				for _, literal in ipairs(leftClause) do
					-- assert(truth[literal[1]] == nil)
					truth[literal[1]] = literal[2]
					table.insert(clauseDisjunction, literal)
				end
				for _, literal in ipairs(rightClause) do
					if truth[literal[1]] == nil then
						truth[literal[1]] = literal[2]
						table.insert(clauseDisjunction, literal)
					elseif truth[literal[1]] ~= literal[2] then
						truth = false
						break
					end
				end
				if truth then
					cnfDisjunction = cnfDisjunction .. Rope.singleton(clauseDisjunction)
				end
			end
		end
		out = cnfDisjunction
	end

	return out
end

-- RETURNS a CNF description equivalent to (term == target)
-- A CNF expression is Rope [](term, boolean).
function toCNF(theory, bigTerm, target, normalization)
	local terms, assignments = theory:breakup(bigTerm, target)
	if not terms then
		-- Ask the theory for a key to normalize the term
		local key = theory:canonKey(bigTerm)
		if normalization[key] == nil then
			normalization[key] = bigTerm
		end
		local literal = {normalization[key], target}
		local unitClause = {literal}
		return Rope.singleton(unitClause)
	end

	local output = toCNFFromBreakup(theory, terms, assignments, normalization)

	return output
end

--------------------------------------------------------------------------------

-- RETURNS a locally minimized set
-- REQUIRES set is initially good
-- REQUIRES isGood mutates nothing
local function minimizeSet(set, isGood)
	assert(isGood(set), "initial set must be good")

	-- Make a copy
	local keys = {}
	local reduced = {}
	for key, value in pairs(set) do
		reduced[key] = value
		table.insert(keys, key)
	end

	local goods = 0
	local i = 1
	local chunk = math.ceil(#keys / 6)
	while i <= #keys do
		for j = i, math.min(#keys, i + chunk - 1) do
			reduced[keys[j]] = nil
		end

		goods = goods + 1
		if isGood(reduced) then
			i = i + chunk
			chunk = math.ceil(chunk * 1.2)
		else
			-- Restore the old values
			for j = i, math.min(#keys, i + chunk - 1) do
				reduced[keys[j]] = set[keys[j]]
			end

			if chunk == 1 then
				i = i + 1

				-- Optimistically increase chunk size
				chunk = math.ceil(1 + (#keys - i) / 6)
			else
				chunk = math.ceil(chunk / 6)
			end
		end
	end

	return reduced
end

-- RETURNS a truth assignment of theory terms {[term] => boolean} that satisfies
-- the specified CNF expression. Does NOT ensure that all terms are represented.
-- RETURNS false when no such satisfaction exists
-- MODIFIES cnf to strengthen its clauses
local function cnfSAT(theory, cnf, meta, initialModel)
	local modelStack = {[0] = initialModel}
	local stack = {}

	-- Get those initial, unchangeable variable assignments
	local preAssignment = {}
	for k, v in pairs(cnf:getAssignment()) do
		preAssignment[k] = v
	end

	for term, prefer in pairs(cnf:forceAssignments()) do
		table.insert(stack, {
			variable = term,
			preferTruth = prefer,
			first = true,
			implied = true,
		})
	end

	while true do
		local debugCore
		if false then
			-- Debug printing
			local description = {}

			local assignment = cnf:getAssignment()
			local keys = table.keys(assignment)

			function debugCore(core)
				local s = {table.unpack(description)}
				for _, k in ipairs(core) do
					local key = k[1]
					local index = table.indexof(keys, key)
					assert(index)
					local sym = k[2] and "+" or "-"
					s[index] = ansi.red(sym) .. s[index]:sub(2, -2) .. ansi.red(sym)
				end
				print(table.concat(s))
				print()
			end

			-- for _, t in ipairs(cnf:freeTermSet()) do
			-- 	table.insert(keys, t)
			-- end
			table.sort(keys, function(a, b)
				return theory:canonKey(a) < theory:canonKey(b)
			end)

			local isImplied = {}
			for _, s in ipairs(stack) do
				if s.implied then
					isImplied[s.variable] = true
				end
			end

			for i = 1, #keys do
				if assignment[keys[i]] == nil then
					description[i] = "."
				elseif assignment[keys[i]] then
					description[i] = "1"
				else
					description[i] = "0"
				end

				if preAssignment[keys[i]] ~= nil then
					description[i] = ansi.gray(description[i])
				elseif isImplied[keys[i]] then
					description[i] = ansi.blue(description[i])
				end

				description[i] = " " .. description[i] .. " "
			end
			print(table.concat(description))
			print()
		end

		-- Make a choice
		local down = 0
		while not cnf:isDecided() do
			down = down + 1
			local term, prefer, implied = cnf:pickUnassigned()
			table.insert(stack, {
				variable = term,
				preferTruth = prefer,
				first = true,
				implied = implied,
			})
			cnf:assign(term, prefer)
		end

		if cnf:isTautology() then
			-- Update the model with changes since last theory consulation
			local model = modelStack[#modelStack]
			for i = #modelStack + 1, #stack do
				local truth = stack[i].preferTruth
				if not stack[i].first then
					truth = not truth
				end
				model = model:assigned(stack[i].variable, truth)
				modelStack[i] = model
			end

			-- Ask the theory whether or not the CNF satisfaction actually
			-- works in the given theory
			local out, conflicting = model:isSatisfiable()
			if not out then
				assert(conflicting)

				-- While this truth model satisfies the CNF, the satisfaction
				-- doesn't work in the theory.
				-- The core clause "explains" the problem and is a constraint
				-- that the current assignment violates
				local coreClause = {}
				for k, v in pairs(conflicting) do
					table.insert(coreClause, {k, not v})
				end
				cnf:addClause(coreClause)
			else
				-- Expand quantified statements using the theory
				local additional, newMeta = theory:additionalClauses(model, meta)

				local currentAssignment = cnf:getAssignment()
				if next(additional) == nil then
					-- There are no quantifiers to expand:
					-- we have found a satisfaction
					return currentAssignment
				end

				-- Expand the additions to CNF
				local newClauses = {}
				for quantified, branch in pairs(additional) do
					-- For disjunctive clause w,
					-- x => w === ~x or w
					-- which is also a disjunctive clause
					for truth, results in pairs(branch) do
						for _, result in ipairs(results) do
							local addCNF = toCNF(theory, result, true, {})
							for _, clause in addCNF:traverse() do
								local implication = {{quantified, not truth}, table.unpack(clause)}
								table.insert(newClauses, implication)
							end
						end
					end
				end

				-- Recursively solve the new SAT problem, including the clauses
				-- from quantifier instantiations
				local newCNF = CNF.new(theory, newClauses, currentAssignment)
				local sat = cnfSAT(theory, newCNF, newMeta, model)
				if sat then
					-- Even after expanding quantifiers, the formula remained
					-- satisfiable
					return currentAssignment
				end

				-- The "proof" that cnfSAT makes for unsatisfiable is enough
				-- additional clauses so that unit propagation results in a
				-- contradiction.
				newCNF:forceAssignments()
				assert(newCNF:isContradiction())

				-- Reduce the current assignment using the above contradiction
				local assignmentCore = minimizeSet(currentAssignment, function(m)
					-- Reset the new CNF
					for k in pairs(newCNF:getAssignment()) do
						newCNF:unassign(k)
					end

					-- Do the partial assignment
					for k, v in pairs(m) do
						newCNF:assign(k, v)
					end

					-- Do unit propagation
					newCNF:forceAssignments()
					return newCNF:isContradiction()
				end)

				-- Negate the core contradictory map to get a new clause
				local learnedClause = {}
				for k, v in pairs(assignmentCore) do
					table.insert(learnedClause, {k, not v})
				end

				-- Learn about which quantifiers conflict with each other
				if #learnedClause == 0 then
					return false
				end
				cnf:addClause(learnedClause)
			end
		elseif cnf:isContradiction() then
			-- Get decision set
			local decisionSet = {}
			local assignment = cnf:getAssignment()
			for _, s in ipairs(stack) do
				if not s.implied then
					decisionSet[s.variable] = assignment[s.variable]
				end
			end

			-- Find the core of the problem; this is an expensive form of
			-- conflict-driven clause-learning (CDCL)
			local newCNF = CNF.new(theory, cnf:allRawClauses(), preAssignment)
			local problemCore = minimizeSet(decisionSet, function(m)
				-- Reset the new CNF
				for k in pairs(newCNF:getAssignment()) do
					if preAssignment[k] == nil then
						newCNF:unassign(k)
					end
				end

				-- Do the partial assignment
				for k, v in pairs(m) do
					newCNF:assign(k, v)
				end

				-- Do unit propagation
				newCNF:forceAssignments()
				return newCNF:isContradiction()
			end)
			
			if #table.keys(problemCore) == 0 then
				return false
			else
				local coreClause = {}
				for k, v in pairs(problemCore) do
					table.insert(coreClause, {k, not v})
				end
				cnf:addClause(coreClause)
				-- debugCore(coreClause)
			end

			-- Some assignment made by the SAT solver is bad
			-- TODO: conflict clauses
			while true do
				if #stack == 0 then
					-- There are no choices to undo
					return false
				end

				assert(#modelStack <= #stack)
				if #modelStack == #stack then
					table.remove(modelStack)
				end

				local variable = stack[#stack].variable
				local preferred = stack[#stack].preferTruth
				if stack[#stack].first and not stack[#stack].implied then
					-- Flip the assignment
					stack[#stack].first = false
					cnf:unassign(variable)
					cnf:assign(variable, not preferred)

					if not cnf:isContradiction() then
						break
					end
				else
					-- Backtrack
					cnf:unassign(variable)
					stack[#stack] = nil
				end
			end
		end
	end
end

--------------------------------------------------------------------------------

-- Determine whether or not `expression` is satisfiable in the given `theory`.
-- RETURNS false | satisfaction
local function isSatisfiable(theory, expression)
	assert(theory)
	assert(expression)

	local clausesRope = toCNF(theory, expression, true, {})
	local clausesList = {}
	for i, v in clausesRope:traverse() do
		clausesList[i] = v
	end
	local cnf = CNF.new(theory, clausesList, {})
	local sat = cnfSAT(theory, cnf, theory:emptyMeta(), theory:makeEmptyModel())
	return sat
end

-- Determine whether or not `givens` together imply `expression` in the given
-- `theory`.
-- RETURNS false, counterexample | true
local function implies(theory, givens, expression)
	-- Is the case where givens are true but expression false satisfiable?
	local args = {}
	local truths = {}
	for i = 1, #givens do
		table.insert(args, givens[i])
		table.insert(truths, true)
	end

	table.insert(args, expression)
	table.insert(truths, false)

	local before = os.clock()
	local clausesRope = toCNFFromBreakup(theory, args, {truths}, {})
	local clausesList = {}
	for i, v in clausesRope:traverse() do
		clausesList[i] = v
	end
	local cnf = CNF.new(theory, clausesList, {})
	local sat = cnfSAT(theory, cnf, theory:emptyMeta(), theory:makeEmptyModel())

	if sat then
		return false, sat
	end
	return true
end

--------------------------------------------------------------------------------

-- plaintheory is an implementation of a Theory used to test the SMT solver
local plaintheory = {assertion_t = "any"}

function plaintheory.makeEmptyModel()
	return {
		isSatisfiable = plaintheory.checkModel,
		assigned = plaintheory.modelAssigned,
		_assignment = Map.new(),
	}
end

-- Test theory
function plaintheory.checkModel(model)
	for x = 1, 2 do
		for y = 1, 2 do
			local all = true
			for k, v in model._assignment:traverse() do
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

	-- No sat
	local map = {}
	for k, v in model._assignment:traverse() do
		map[k] = v
	end
	return false, map
end

function plaintheory.modelAssigned(model, key, truth)
	return {
		isSatisfiable = plaintheory.checkModel,
		assigned = plaintheory.modelAssigned,
		_assignment = model._assignment:with(key, truth),
	}
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
	error("unknown `" .. show(e) .. "`")
end

function plaintheory:canonKey(e)
	if type(e) == "string" then
		return string.format("%q", e)
	elseif type(e) == "function" then
		return tostring(e)
	end

	local list = {"{", plaintheory:canonKey(e[1])}
	for i = 2, #e do
		table.insert(list, ", ")
		table.insert(list, plaintheory:canonKey(e[i]))
	end
	table.insert(list, "}")
	return table.concat(list, "")
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
	for key, value in model._assignment:traverse() do
		if not meta[key] then
			if type(key) == "table" and key[1] == "d" then
				newMeta[key] = true
				out[key] = {
					[true] = {key[2]},
					[false] = {{"not", key[2]}},
				}
			end
		end
	end
	return out, newMeta
end

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
	-- assert(prefer1)
	-- assert(v1 == "a" or v1 == "b")
	-- problem:assign(v1, not prefer1)
	-- assert(not problem:isDecided(), "must not yet be decided")
	-- local v2, prefer2 = problem:pickUnassigned()
	-- assert(v1 ~= v2)
	-- assert(v2 == "a" or v2 == "b")
	-- assert(prefer2 == true)
	-- problem:assign(v2, not prefer2)
	-- assert(problem:isDecided(), "must be decided")
	-- assert(problem:isContradiction(), "must be contradiction")
	-- assert(not problem:isTautology(), "must not be tautology")
	-- problem:unassign(v2)
	-- assert(not problem:isDecided(), "must no longer be decided")
	-- assert(not problem:isContradiction(), "must no longer be contradiction")
	-- assert(not problem:isTautology(), "must still not be tautology")
	-- problem:unassign(v1)
	-- assert(not problem:isDecided())
	-- problem:assign("a", false)
	-- problem:assign("b", true)
	-- assert(not problem:isDecided())
	-- problem:assign("z", false)
	-- assert(problem:isDecided(), "problem is now decided")
	-- assert(problem:isTautology(), "problem is now tautology")
	-- assert(not problem:isContradiction(), "problem is not a contradiction")
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

		local a = {"f", table.remove(clause, math.random(#clause))}
		local b = {"f", table.remove(clause, math.random(#clause))}
		local c = {"f", table.remove(clause, math.random(#clause))}
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

		local a = {"f", table.remove(clause, math.random(#clause))}
		local b = {"f", table.remove(clause, math.random(#clause))}
		local c = {"f", table.remove(clause, math.random(#clause))}
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

-- Performance test (Horn clauses are easy to check satisfiability)
for n = 50, 0 do
	print("--", n, "------------")
	for clauseCount = 50, 1e9, 50 do
		local problem = "ground"
		for i = 1, clauseCount do
			-- Make a Horn clause
			local a = "v" .. math.random(n)
			local b = {"not", "v" .. math.random(n)}
			local c = {"not", "v" .. math.random(n)}
			local clause = {"or", a, {"or", b, c}}

			problem = {"and", problem, clause}
		end

		--print("SAT on " .. n .. "-term 3CNF of " .. clauseCount .. " Horn clauses")
		local before = os.clock()
		isSatisfiable(plaintheory, problem)
		local after = os.clock()
		print("*", clauseCount, after - before)
	end
end

--------------------------------------------------------------------------------

return {
	isSatisfiable = isSatisfiable,
	implies = implies,
}
