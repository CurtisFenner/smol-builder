local Stopwatch = import "stopwatch.lua"

local theory = {
	assertion_t = "Assertion",
}

local Rope = import "data/rope.lua"
local Map = import "data/map.lua"
local UnionFind = import "data/unionfind.lua"

local common = import "common.lua"
local showTypeKind = common.showTypeKind

local areTypesEqual = common.areTypesEqual

local STRING_TYPE = common.STRING_TYPE
local INT_TYPE = common.INT_TYPE
local BOOLEAN_TYPE = common.BOOLEAN_TYPE
local UNIT_TYPE = common.UNIT_TYPE
local NEVER_TYPE = common.NEVER_TYPE

local typeOfAssertion = common.typeOfAssertion

--------------------------------------------------------------------------------

-- list: [](A, B)
-- RETURNS {A => B}
local function listToMap(list)
	assertis(list, listType(tupleType("any", "any")))

	local m = {}
	for _, pair in ipairs(list) do
		m[pair[1]] = pair[2]
	end
	return m
end

-- Represents a canonicalizing system
local HashCache = {}
function HashCache.new()
	return setmetatable({_data = {}}, {__index = HashCache})
end

-- RETURNS previously placed value if keys is not new
-- RETURNS value otherwise
-- MODIFIES this if the value was not present so that future :place(keys)
-- calls return value
-- NOTE: a value of `nil` will not be placed into this map and will just return
-- any existing value
-- `HashCache` is not a valid key.
-- REQUIRES at least one key is given
function HashCache:place(keys, value)
	assert(#keys ~= 0)

	local map = self._data
	for i = 1, #keys do
		if map[keys[i]] == nil then
			map[keys[i]] = {}
		end
		map = map[keys[i]]
	end

	if map[HashCache] == nil then
		map[HashCache] = value
	end

	return map[HashCache]
end

--------------------------------------------------------------------------------

-- RETURNS an Assertion representing a.not()
local function notAssertion(a)
	assertis(a, "Assertion")

	return {
		tag = "fn",
		arguments = {a},
		signature = common.builtinDefinitions.Boolean.functionMap["not"].signature,
		index = 1,
		typeArguments = {},
	}
end
notAssertion = memoized(1, notAssertion)

-- RETURNS an EqAssertion representing a == b
local function eqAssertion(a, b, t)
	assertis(a, "Assertion")
	assertis(b, "Assertion")
	assertis(t, "TypeKind")

	local p = {
		tag = "eq",
		left = a,
		right = b,
	}
	return p
end
eqAssertion = memoized(3, eqAssertion)

-- RETURNS an Assertion
local function variableAssertion(variable)
	assertis(variable, "VariableIR")

	return {
		tag = "variable",
		variable = variable,
	}
end
variableAssertion = memoized(1, variableAssertion)

-- RETURNS an Assertion
local function constantAssertion(constant)
	if type(constant) == "number" then
		-- Assert that constant is finite and an integer
		assert(constant % 1 == 0)

		return {
			tag = "int",
			value = constant,
		}
	elseif type(constant) == "string" then
		return {
			tag = "string",
			value = constant,
		}
	elseif type(constant) == "boolean" then
		return {
			tag = "boolean",
			value = constant,
		}
	end
	error("Unknown constant type value")
end
constantAssertion = memoized(1, constantAssertion)

--------------------------------------------------------------------------------

local validateModel

-- RETURNS a string
local showSkip = {}
local function showAssertion(assertion)
	if showSkip[assertion] then
		return showSkip[assertion]
	end

	assertis(assertion, "Assertion")

	if assertion.tag == "unit" then
		return "(unit)"
	elseif assertion.tag == "this" then
		return "(this)"
	elseif assertion.tag == "variable" then
		return "(var " .. assertion.variable.name .. ")"
	elseif assertion.tag == "new-class" then
		local fields = {}
		for f, v in spairs(assertion.fields) do
			table.insert(fields, f .. "=" .. showAssertion(v))
		end
		table.sort(fields)
		fields = table.concat(fields, " ")
		return "(new-class " .. assertion.type .. " " .. fields .. ")"
	elseif assertion.tag == "fn" then
		local arguments = {}
		for _, v in ipairs(assertion.arguments) do
			table.insert(arguments, showAssertion(v))
		end
		arguments = table.concat(arguments, " ")
		local fn = assertion.signature.longName
		return "(fn " .. fn .. " [" .. arguments .. "])"
	elseif assertion.tag == "int" then
		return "(int " .. tostring(assertion.value) .. ")"
	elseif assertion.tag == "boolean" then
		return "(boolean " .. tostring(assertion.value) .. ")"
	elseif assertion.tag == "field" then
		return "(field " .. showAssertion(assertion.base) .. " " .. assertion.fieldName .. ")"
	elseif assertion.tag == "eq" then
		return "(" .. showAssertion(assertion.left) .. " == " .. showAssertion(assertion.right) .. ")"
	elseif assertion.tag == "gettag" then
		return "(gettag " .. showAssertion(assertion.base) .. ")"
	elseif assertion.tag == "string" then
		return "(string " .. string.format("%q", assertion.value) .. ")"
	elseif assertion.tag == "variant" then
		return "(variant " .. string.format("%q", assertion.variantName) .. " " .. showAssertion(assertion.base) .. ")"
	elseif assertion.tag == "symbol" then
		return "(symbol " .. assertion.symbol .. ")"
	elseif assertion.tag == "forall" then
		return "(forall " .. showTypeKind(assertion.quantified) .. " " .. assertion.unique .. " " .. assertion.instance .. ")"
	end
	error("unknown assertion tag `" .. assertion.tag .. "` in showAssertion")
end
showAssertion = memoized(1, showAssertion)

function theory:canonKey(e)
	return showAssertion(e)
end

local TERMINAL_TAG = {
	["unit"] = true,
	["this"] = true,
	["variable"] = true,
	["int"] = true,
	["boolean"] = true,
	["string"] = true,
	["symbol"] = true,
}

-- RETURNS a Lua value for types representable as literals that is suitable,
-- e.g., in the .eval of a Signature
-- RETURNS nil when the Assertion has no statically determinable literal
-- evaluation
local function isLiteralAssertion(e)
	assertis(e, "Assertion")

	if e.tag == "int" then
		return e.value
	elseif e.tag == "string" then
		return e.value
	elseif e.tag == "boolean" then
		return e.value
	end

	return nil
end

local globalCanon = HashCache.new()

local function showVTable(v)
	assertis(v, "VTableIR")

	if v.tag == "parameter-vtable" then
		return "(" .. v.name .. ")"
	elseif v.tag == "concrete-vtable" then
		local arguments = {}
		for _, a in ipairs(v.arguments) do
			table.insert(arguments, showVTable(a))
		end
		local base = common.showTypeKind(v.concrete) .. " is " .. common.showConstraintKind(v.interface)
		return "(" .. base .. ")[" .. table.concat(arguments, ", ") .. "]"
	end
	error "unreachable"
end

local function identifyConstraintArguments(as)
	assertis(as, listType "VTableIR")

	local m = {}
	for i = 1, #as do
		m[i] = showVTable(as[i])
	end
	return table.concat(m, ", ")
end

local m_scan

local function m_fresh(self, object)
	assertis(object, "Assertion")

	if object.tag == "int" then
		local keys = {"int", object.value}
		return globalCanon:place(keys, object)
	elseif object.tag == "string" then
		local keys = {"string", object.value}
		return globalCanon:place(keys, object)
	elseif object.tag == "boolean" then
		local keys = {"boolean", object.value}
		return globalCanon:place(keys, object)
	elseif object.tag == "unit" then
		local keys = {"unit"}
		return globalCanon:place(keys, object)
	elseif object.tag == "variable" then
		local keys = {
			"variable",
			object.variable.name,
			showTypeKind(object.variable.type),
		}
		return globalCanon:place(keys, object)
	elseif object.tag == "fn" then
		local keys = {
			"fn",
			object.index,
			object.signature.longName,
			identifyConstraintArguments(object.typeArguments),
		}
		local arguments = {}
		for _, a in ipairs(object.arguments) do
			local argument = m_scan(self, a)
			table.insert(arguments, argument)
			table.insert(keys, argument)
		end

		return globalCanon:place(keys, {
			tag = "fn",
			arguments = arguments,
			signature = object.signature,
			index = object.index,
			typeArguments = object.typeArguments,
		})
	elseif object.tag == "field" then
		local keys = {
			"field",
			object.fieldName,
		}
		local base = m_scan(self, object.base)
		table.insert(keys, base)
		return globalCanon:place(keys, {
			tag = "field",
			base = base,
			fieldName = object.fieldName,
			fieldType = object.fieldType,
		})
	elseif object.tag == "eq" then
		local left = m_scan(self, object.left)
		local right = m_scan(self, object.right)
		local keys = {"eq", left, right}
		return globalCanon:place(keys, {
			tag = "eq",
			left = left,
			right = right,
		})
	elseif object.tag == "gettag" then
		local base = m_scan(self, object.base)
		local keys = {"gettag", base}
		return globalCanon:place(keys, {
			tag = "gettag",
			base = base,
		})
	elseif object.tag == "symbol" then
		local keys = {"symbol", object.symbol}
		return globalCanon:place(keys, object)
	elseif object.tag == "variant" then
		local base = m_scan(self, object.base)
		local keys = {"variant", object.variantName, base}
		return globalCanon:place(keys, {
			tag = "variant",
			variantName = object.variantName,
			variantType = object.variantType,
			base = base,
		})
	elseif object.tag == "forall" then
		local keys = {"forall", object.unique, object.instance}
		return globalCanon:place(keys, object)
	end

	error("unhandled tag `" .. object.tag .. "`")
end

-- Canonicalizes objects so that syntactically equivalent subtrees become the
-- same reference
function m_scan(self, object)
	if self.relevant[object] ~= nil then
		return object
	end

	local canonicalized = m_fresh(self, object)
	self.relevant[canonicalized] = canonicalized
	return canonicalized
end

local cID = 0
local function newConst()
	cID = cID + 1
	return "const." .. cID
end

local TRUE_ASSERTION = {tag = "boolean", value = true}
local FALSE_ASSERTION = {tag = "boolean", value = false}

local INT_ASSERTIONS = {
	[10] = {tag = "int", value = 10},
	[3] = {tag = "int", value = 3},
	[2] = {tag = "int", value = 2},
	[1] = {tag = "int", value = 1},
	[0] = {tag = "int", value = 0},
	[-1] = {tag = "int", value = -1},
}

-- RETURNS a list of clauses
local function quantifierClauses(model, term, truth)
	assert(term.tag == "forall")

	if truth then
		-- Find all terms of the specified sort
		-- Instantiate for all interesting terms

		-- TODO: PERFORMANCE: filter by triggers, see
		-- https://doi.org/10.1007/978-3-540-73595-3_12
		local opportunities = {}
		for x in model._eq:traverse() do
			assertis(x, "Assertion")

			local tx = typeOfAssertion(x)
			assertis(tx, "TypeKind")

			if areTypesEqual(tx, term.quantified) then
				table.insert(opportunities, x)
			end
		end

		-- Apply SIMPLIFY style relevance matching
		local freshConstantName = newConst() .. "triggervar"
		local templateConstraints, instantiationResult, boundVariable = term:instantiate(freshConstantName)
		assertis(templateConstraints, "Assertion")
		assertis(instantiationResult, "Assertion")
		assertis(boundVariable, "VariableIR")

		-- TODO: https://doi.org/10.1007/978-3-540-73595-3_12
		-- (1) Find all potential trigger terms from templateConstraints/instantiationResult.
		-- (2) Find those that are not equal to anything in the model
		-- (3) For each instantiation opportunity, determine if any found in (2) become
		--     equal to a model term after applying boundVariable = opportunity.

		local out = {}
		for _, x in ipairs(opportunities) do
			-- Instantiate an example of a forall instance
			local constantName = newConst() .. "forall" .. tostring(term.unique)
			local newTerm, res, var = term:instantiate(constantName)

			-- x is the same as constant
			table.insert(out, eqAssertion(x, variableAssertion(var), term.quantified))

			-- The predicate holds for `x`
			table.insert(out, newTerm)
			table.insert(out, res)
		end
		return out
	else
		-- Instantiate with an arbitrary new constant
		-- (There exists not P(c))
		local constantName = newConst() .. "exists" .. tostring(term.unique)
		local newTerm, res = term:instantiate(constantName)

		-- Push the negative through for exists
		return {newTerm, notAssertion(res)}
	end
end

-- RETURNS an empty map
function theory:emptyMeta()
	return {}
end

-- Learn additional clauses from the inclusion of `term` in `model`
-- (Added to support quantifiers)
-- model: the model so far
-- cnf: the remaining clauses to satisfy
-- term: the key just added to model
function theory:additionalClauses(model, meta)
	assertis(model, "SmolModel")
	assert(meta)

	local newMeta = {}
	for k, v in pairs(meta) do
		newMeta[k] = v
	end

	local out = {}

	for term, truth in model._quantifiers:traverse() do
		if term.tag == "forall" then
			if not meta[term.unique] then
				out[term] = {
					[true] = quantifierClauses(model, term, true),
					[false] = quantifierClauses(model, term, false),
				}
				newMeta[term.unique] = true
			else
				-- This quantifier has already been instantiated
				-- NOTE: Foralls are identified by .unique AND by .instnace
				-- Multiple quantifiers with difference .instance values SHOULD
				-- be instantiated all at once
			end
		end
	end

	return out, newMeta
end

-- RETURNS false when the tag is terminal
-- RETURNS a string identifying the structure, a list of sub-assertions
local function recursiveStructure(e)
	assertis(e, "Assertion")

	if TERMINAL_TAG[e.tag] or e.tag == "forall" then
		return false
	elseif e.tag == "field" then
		return "field-" .. e.fieldName, {e.base}
	elseif e.tag == "variant" then
		return "variant-" .. e.variantName, {e.base}
	elseif e.tag == "gettag" then
		return "gettag", {e.base}
	elseif e.tag == "fn" then
		if #e.arguments == 0 then
			return false
		end
		return "fn-" .. e.signature.longName .. "[" .. tostring(identifyConstraintArguments(e.typeArguments)) .. "]", e.arguments
	elseif e.tag == "eq" then
		return "eq", {e.left, e.right}
	end
	error("unknown Assertion tag `" .. e.tag .. "`")
end

-- RETURNS a set of expression and all their subexpressions
local function recursiveComponents(e)
	assertis(e, "Assertion")

	local stack = {e}
	local set = {[e] = true}
	while #stack > 0 do
		local _, children = recursiveStructure(table.remove(stack))
		if children then
			for _, child in ipairs(children) do
				if not set[child] then
					set[child] = true
					table.insert(stack, child)
				end
			end
		end
	end
	return set
end

-- RETURNS a Lua constant, reason when the function can be evaluated statically
-- RETURNS nil otherwise
local function fnLiteralEvaluation(expression, eq)
	assertis(expression, "Assertion")
	assert(expression.tag == "fn")

	if not expression.signature.eval then
		return nil
	end

	-- Attempt to evaluate each argument to a constant
	local argumentLiterals = {}
	local reasons = {}
	for i, argument in ipairs(expression.arguments) do
		-- Evaluate each argument, stopping if a contradiction is reached
		for _, equivalent in eq:withTryInit(argument):classOf(argument):traverse() do
			local literal = isLiteralAssertion(equivalent)
			if literal ~= nil then
				table.insert(argumentLiterals, literal)

				for _, set in ipairs(eq:reasonEq(argument, equivalent)) do
					for _, reason in ipairs(set) do
						table.insert(reasons, reason)
					end
				end
				break
			end
		end

		if argumentLiterals[i] == nil then
			-- This argument literal could not be evaluated
			return nil
		end
	end

	-- All the arguments were successfully evaluated
	return expression.signature.eval(table.unpack(argumentLiterals)), reasons
end

--------------------------------------------------------------------------------

-- RETURNS nothing
-- Checks some invariants of the smol model
function validateModel(model)
	do
		return
	end

	for a, c in model._eq:traverse() do
		for _, t in c:traverse() do
			if t.tag == "fn" then
				local con = fnLiteralEvaluation(t, model._eq)
				if con ~= nil then
					if model._eq:specialsOf("literal", t):size() == 0 then
						print("CONCERNING:", theory:canonKey(t))
						error("Constant evaluation doesn't agree with cached literals-of")
					end
				end
			end
		end
	end
end

-- RETURNS whether or not the given model is satisfiable in a quantifier free
-- theory of uninterpreted functions
-- as a part of the 'theory' interface for the SMT solver
local function modelSatisfiable(self)
	assertis(self, "SmolModel")

	validateModel(self)

	if self._contradiction then
		return false, self._contradiction
	end

	-- Check that != are not equal
	for _, bin in self._negatives:traverse() do
		local a, b = bin.left, bin.right
		if self._eq:query(a, b) then
			-- This model is inconsistent; explain the contradiction
			local limited = {}
			for _, reason in ipairs(bin.reasons) do
				table.insert(limited, reason)
			end
			for _, set in ipairs(self._eq:reasonEq(a, b)) do
				for _, reason in ipairs(set) do
					table.insert(limited, reason)
				end
			end
			assert(1 <= #limited)

			return false, listToMap(limited)
		end
	end

	return true
end

REGISTER_TYPE("SmolModel", recordType {
	assigned = "function",
	isSatisfiable = "function",

	_canon = "object",

	-- TODO: UnionFind
	_eq = "object",

	-- TODO: Rope(record)
	_negatives = "object",

	-- TODO: Map(Assertion => boolean)
	_quantifiers = "object",

	-- TODO: Map
	_assignments = "object",

	-- TODO: Map(canon Assertion => raw Assertion)
	_rawVersion = "object",

	-- TODO: Map(raw Assertion => boolean)
	_rawAssignment = "object",

	-- TODO: Map(string => canon Assertion)
	_functionMap = "object",

	-- TODO: Map(representative Assertion => Map(canon Assertion => true))
	_mentionMap = "object",

	_contradiction = choiceType(constantType(false), mapType("Assertion", "boolean")),
})

-- RETURNS false when the assertion is not function-like
-- RETURN key (string), UF, set of representatives otherwise
-- where 'key' is equal for all equal functions (the same function applied to
-- equal arguments)
local function makeKeyOfFunction(f, eq)
	assertis(f, "Assertion")
	assertis(eq, "object")

	-- Find the arguments of the function-like assertion
	local id, children = recursiveStructure(f)
	if not id then
		-- Assertions without arguments don't need to be handled like this
		return false
	end

	-- Compute a canonical form for the function, as a string
	eq = eq:withTryInit(f)
	local functionIDs = {id}
	local representatives = {}
	local reasons = {}
	for _, child in ipairs(children) do
		eq = eq:withTryInit(child)
		local representative = eq:representativeOf(child)
		table.insert(functionIDs, tostring(representative))
		table.insert(representatives, representative)
	end
	return table.concat(functionIDs, "@"), eq, representatives
end

-- RETURNS a set of reasons explaining why the two function values should be
-- considered equal
-- REQUIRES a and b are the same kind of function and should be equal
local function reasonFnsEqual(f1, f2, eq)
	assertis(f1, "Assertion")
	assertis(f2, "Assertion")
	assertis(eq, "object")

	local s1, c1 = recursiveStructure(f1)
	local s2, c2 = recursiveStructure(f2)

	assert(s1 and s2)
	assert(s1 == s2)
	assert(#c1 == #c2)
	local reasons = {}
	for i = 1, #c1 do
		for _, set in ipairs(eq:reasonEq(c1[i], c2[i])) do
			for _, reason in ipairs(set) do
				table.insert(reasons, reason)
			end
		end
	end
	return reasons
end

-- RETURNS modified eq, functionMap, mentionMap
local function recheckFunction(subassertion, eqQueue, eq, functionMap, mentionMap, canon)
	assertis(subassertion, "Assertion")

	local key, newEq, reps = makeKeyOfFunction(subassertion, eq)
	if key then
		eq = newEq
		if not functionMap:get(key) then
			functionMap = functionMap:with(key, subassertion)
		end
		local other = functionMap:get(key)
		if other ~= subassertion then
			-- Functions with the same canonicalized key should be equal
			if not eq:query(subassertion, other) then
				local reasons = reasonFnsEqual(subassertion, other, eq)
				table.insert(eqQueue, {
					left = subassertion,
					right = other,
					reasons = reasons,
				})
			end
		end

		if subassertion.tag == "fn" then
			-- Perform constant evaluation of functions of constant arguments
			local wasAsConstant = eq:specialsOf("literal", subassertion)
			if #wasAsConstant == 0 then
				local literal, reasons = fnLiteralEvaluation(subassertion, eq)
				if literal ~= nil then
					local literalExpression = constantAssertion(literal)
					local before = theory:canonKey(literalExpression)
					literalExpression = canon:scan(literalExpression)
					assert(before == theory:canonKey(literalExpression))
					eq = eq:withTryInit(literalExpression)
					if not eq:query(literalExpression, subassertion) then
						table.insert(eqQueue, {
							left = subassertion,
							right = literalExpression,
							reasons = reasons,
						})
					end
				end
			end
		end

		-- Mark this assertion to be notified if a representative is
		-- superceded
		for _, rep in ipairs(reps) do
			local previousSet = mentionMap:get(rep) or Map.new()
			mentionMap = mentionMap:with(rep, previousSet:with(subassertion, true))
		end
	end

	return eq, functionMap, mentionMap
end

-- RETURNS a new version of the model acknowleding the new assignment,
-- doing all work iteratively so that this is fast as well as contradiction
-- detection is fast
local function modelAssigned(self, key, truth)
	assertis(self, "SmolModel")
	validateModel(self)

	local eq = self._eq
	local assertion = self._canon:scan(key)

	if self._assignments:get(assertion) == truth then
		-- No change
		return self
	elseif self._assignments:get(assertion) ~= nil then
		-- Contradiction
		local keyOne = self._rawVersion:get(assertion)
		local truthOne = self._assignments:get(assertion)
		return {
			_contradiction = {
				[keyOne] = truthOne,
				[key] = truth,
			},

			assigned = modelAssigned,
			isSatisfiable = modelSatisfiable,

			_quantifiers = self._quantifiers,
			_canon = self._canon,
			_eq = eq,
			_negatives = self._negatives,
			_assignments = self._assignments:with(assertion, truth),
			_rawVersion = self._rawVersion:with(assertion, key),
			_rawAssignment = self._rawAssignment:with(key, truth),

			_mentionMap = self._mentionMap,
			_functionMap = self._functionMap,
		}
	end

	local quantifiers = self._quantifiers
	local neq = self._negatives
	local functionMap = self._functionMap
	local mentionMap = self._mentionMap

	local eqQueue = {}

	-- Identify all the functions in this new term and canonicalize and index
	-- them using the UF data structure
	for subassertion in pairs(recursiveComponents(assertion)) do
		eq, functionMap, mentionMap = recheckFunction(
			subassertion,
			eqQueue,
			eq,
			functionMap,
			mentionMap,
			self._canon
		)
	end

	if assertion.tag == "forall" then
		-- Quantifiers are unhandled here
		quantifiers = quantifiers:with(assertion, truth)
	else
		if assertion.tag == "eq" then
			local left = self._canon:scan(assertion.left)
			local right = self._canon:scan(assertion.right)
			assert(theory:canonKey(left) == theory:canonKey(assertion.left))
			assert(theory:canonKey(right) == theory:canonKey(assertion.right))

			if truth then
				-- a = b joins union find
				table.insert(eqQueue, {
					left = left,
					right = right,
					reasons = {{key, truth}},
				})
			else
				-- a != b joins list of disequalities
				eq = eq:withTryInit(left)
				eq = eq:withTryInit(right)
				neq = neq .. Rope.singleton {
					left = left,
					right = right,
					reasons = {{key, truth}},
				}
			end
		end

		if truth then
			table.insert(eqQueue, {
				left = self._canon:scan(TRUE_ASSERTION),
				right = assertion,
				reasons = {{key, truth}},
			})
		else
			table.insert(eqQueue, {
				left = self._canon:scan(FALSE_ASSERTION),
				right = assertion,
				reasons = {{key, truth}},
			})
		end
	end

	local contradiction = self._contradiction

	while 0 < #eqQueue do
		local was = eqQueue
		eqQueue = {}
		for _, r in ipairs(was) do
			-- This may be the first mention of these objects to the UF
			eq = eq:withTryInit(r.left)
			eq = eq:withTryInit(r.right)

			local oldLeftRep = eq:representativeOf(r.left)
			local oldRightRep = eq:representativeOf(r.right)

			-- Join the objects in the UF data-structure
			eq = eq:withUnion(r.left, r.right, r.reasons)

			-- One of the representatives may have just been dethroned
			local newRep = eq:representativeOf(r.left)
			assert(newRep == oldLeftRep or newRep == oldRightRep)
			local staleRep = false
			if newRep ~= oldLeftRep then
				staleRep = oldLeftRep
			elseif newRep ~= oldRightRep then
				staleRep = oldRightRep
			end
			if staleRep then
				-- Merge maps
				if not mentionMap:get(newRep) then
					mentionMap = mentionMap:with(newRep, Map.new())
				end
				if mentionMap:get(staleRep) then
					for mention in mentionMap:get(staleRep):traverse() do
						assertis(mention, "Assertion")

						local merged = mentionMap:get(newRep):with(mention, true)
						mentionMap = mentionMap:with(newRep, merged)
					end
				end

				-- Find functions that are now equal via their arguments being
				-- equal
				if mentionMap:get(newRep) then
					for mentioner in mentionMap:get(newRep):traverse() do
						eq, functionMap, mentionMap = recheckFunction(
							mentioner,
							eqQueue,
							eq,
							functionMap,
							mentionMap,
							self._canon
						)
					end
				end
			end

			-- Check if this has created a contradiction
			if not contradiction then
				-- Check that we haven't violated symbol/literal distinctness
				local symbols = eq:specialsOf("symbol", r.left)
				local literals = eq:specialsOf("literal", r.left)

				if 1 < symbols:size() then
					local reasons = table.concatted(table.unpack(eq:reasonEq(symbols:get(1), symbols:get(2))))
					contradiction = listToMap(reasons)
				elseif 1 < literals:size() then
					local reasons = table.concatted(table.unpack(eq:reasonEq(literals:get(1), literals:get(2))))
					contradiction = listToMap(reasons)
				end
			end
		end
	end

	local out = {
		assigned = modelAssigned,
		isSatisfiable = modelSatisfiable,

		_quantifiers = quantifiers,
		_canon = self._canon,
		_eq = eq,
		_negatives = neq,
		_assignments = self._assignments:with(assertion, truth),
		_rawVersion = self._rawVersion:with(assertion, key),
		_rawAssignment = self._rawAssignment:with(key, truth),
		_contradiction = contradiction,

		_mentionMap = mentionMap,
		_functionMap = functionMap,
	}
	assertis(out, "SmolModel")
	validateModel(out)
	return out
end

-- RETURNS a SmolModel with no assignments
function theory:makeEmptyModel()
	local canon = {scan = m_scan; relevant = {}}
	local out = {
		assigned = modelAssigned,
		isSatisfiable = modelSatisfiable,
		_canon = canon,
		_assignments = Map.new(),
		_quantifiers = Map.new(),
		_rawAssignment = Map.new(),
		_rawVersion = Map.new(),
		_contradiction = false,
		_mentionMap = Map.new(),
		_functionMap = Map.new(),
	}

	local aTrue = canon:scan(TRUE_ASSERTION)
	local aFalse = canon:scan(FALSE_ASSERTION)
	out._negatives = Rope.singleton {
		left = aTrue,
		right = aFalse,
		reasons = {},
	}
	out._eq = UnionFind.new {
		symbol = function(x)
			return x.tag == "symbol"
		end,
		literal = function(x)
			return isLiteralAssertion(x) ~= nil
		end,
	}
	out._eq = out._eq:withInit(aTrue):withInit(aFalse)

	assertis(out, "SmolModel")
	validateModel(out)
	return out
end

local IFF = {
	[true] = {{true, true}, {false, false}},
	[false] = {{true, false}, {false, true}},
}

function theory:breakup(assertion, target)
	assertis(assertion, "Assertion")

	if assertion.tag == "fn" then
		local signature = assertion.signature
		assertis(signature, "Signature")

		local logic = signature.logic
		if not logic then
			return false
		end

		local values = {}
		for _, argument in ipairs(assertion.arguments) do
			table.insert(values, argument)
		end

		for _, row in ipairs(logic[target]) do
			assert(#row == #values)
		end

		return values, logic[target]
	elseif assertion.tag == "eq" then
		if areTypesEqual(BOOLEAN_TYPE, typeOfAssertion(assertion.left)) then
			-- if and only if
			return {assertion.left, assertion.right}, IFF[target]
		end
	end

	return false
end

--------------------------------------------------------------------------------

assertis(theory, "Theory")
return {
	theory = theory,
	notAssertion = notAssertion,
	eqAssertion = eqAssertion,
	variableAssertion = variableAssertion,
}
