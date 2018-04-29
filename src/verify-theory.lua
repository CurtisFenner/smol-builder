local profile = import "profile.lua"

local theory = {
	assertion_t = "Assertion",
	satisfaction_t = "any",
}

local UnionFind = import "unionfind.lua"

local common = import "common.lua"
local showType = common.showType

local BUILTIN_DEFINITIONS = common.BUILTIN_DEFINITIONS
local BOOLEAN_DEF = table.findwith(BUILTIN_DEFINITIONS, "name", "Boolean")
local makeEqSignature = common.makeEqSignature

local areTypesEqual = common.areTypesEqual

local STRING_TYPE = common.STRING_TYPE
local INT_TYPE = common.INT_TYPE
local BOOLEAN_TYPE = common.BOOLEAN_TYPE
local UNIT_TYPE = common.UNIT_TYPE
local NEVER_TYPE = common.NEVER_TYPE

local typeOfAssertion = common.typeOfAssertion

--------------------------------------------------------------------------------

-- RETURNS an Assertion representing a.not()
local function notAssertion(a)
	assertis(a, "Assertion")

	return freeze {
		tag = "fn",
		arguments = {a},
		signature = table.findwith(BOOLEAN_DEF.signatures, "memberName", "not"),
		index = 1,
	}
end
notAssertion = memoized(1, notAssertion)

-- RETURNS an Assertion representing a == b
local function eqAssertion(a, b, t)
	assertis(a, "Assertion")
	assertis(b, "Assertion")
	assertis(t, "Type+")

	local p = freeze {
		tag = "fn",
		arguments = {a, b},
		signature = makeEqSignature(t),
		index = 1,
	}
	assertis(p, "FnAssertion")
	return p
end
eqAssertion = memoized(3, eqAssertion)

-- RETURNS an Assertion
local function variableAssertion(variable)
	assertis(variable, "VariableIR")

	return freeze {
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

		return freeze {
			tag = "int",
			value = constant,
		}
	elseif type(constant) == "string" then
		return freeze {
			tag = "string",
			value = constant,
		}
	elseif type(constant) == "boolean" then
		return freeze {
			tag = "boolean",
			value = constant,
		}
	end
	error("Unknown constant type value")
end
constantAssertion = memoized(1, constantAssertion)

-- RETURNS an Assertion
local function fnAssertion(signature, arguments, index)
	assertis(signature, "Signature")
	assertis(arguments, listType("Assertion"))
	assertis(index, "integer")

	return freeze {
		tag = "fn",
		signature = signature,
		arguments = arguments,
		index = index,
	}
end
fnAssertion = memoized(4, fnAssertion)

--------------------------------------------------------------------------------

-- RETURNS a string
local showSkip = {}
local function showAssertion(assertion)
	if showSkip[assertion] then
		return showSkip[assertion]
	end

	assertis(assertion, "Assertion")
	assert(isimmutable(assertion))

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
	elseif assertion.tag == "isa" then
		return "(isa " .. assertion.variant .. " " .. showAssertion(assertion.base) .. ")"
	elseif assertion.tag == "string" then
		return "(string " .. string.format("%q", assertion.value) .. ")"
	elseif assertion.tag == "variant" then
		return "(variant " .. string.format("%q", assertion.variantName) .. " " .. showAssertion(assertion.base) .. ")"
	elseif assertion.tag == "forall" then
		local loc = assertion.location.begins
		if type(loc) ~= "string" then
			loc = loc.filename .. ":" .. loc.index
		end
		return "(forall " .. showType(assertion.quantified) .. " " .. loc .. ")"
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
}

-- RETURNS a description of the value of an assertion
-- a Lua boolean, number, string
-- RETURNS nil when the value is not known at compile time
local function evaluateConstantAssertion(e, lowerConstant)
	assertis(e, "Assertion")
	assertis(lowerConstant, "function")

	if e.tag == "int" then
		return e.value
	elseif e.tag == "string" then
		return e.value
	elseif e.tag == "boolean" then
		return e.value
	elseif e.tag == "fn" then
		local signature = e.signature
		if e.signature.memberName == "eq" and #e.arguments == 2 then
			if showAssertion(e.arguments[1]) == showAssertion(e.arguments[2]) then
				return true
			end
		end

		if signature.eval == false then
			return nil
		end

		local arguments = {}
		for i, a in ipairs(e.arguments) do
			arguments[i] = lowerConstant(a)
			if arguments[i] == nil then
				return nil
			end
		end

		return signature.eval(unpack(arguments))
	end

	-- No static representation is possible
	return nil
end

local m_scan

local function scanned(self, children)
	local out = {}
	for i = 1, #children do
		out[i] = m_scan(self, children[i])
	end
	return out
end

-- Canonicalizes objects so that syntactically equivalent subtrees become the
-- same reference
function m_scan(self, object)
	assertis(object, "Assertion")

	local shown = showAssertion(object)
	if self.relevant[shown] then
		return self.relevant[shown]
	end

	local function ref(child)
		local s = showAssertion(child)
		assert(s ~= shown)
		assert(self.relevant[s], "child in map")
		self.referencedBy[child] = self.referencedBy[child] or {}
		table.insert(self.referencedBy[child], self.relevant[shown])
	end

	if TERMINAL_TAG[object.tag] then
		self.relevant[shown] = object
	elseif object.tag == "fn" then
		local canon = fnAssertion(
			object.signature,
			scanned(self, object.arguments),
			object.index
		)
		self.relevant[shown] = canon
		for _, argument in ipairs(canon.arguments) do
			ref(argument)
		end
	elseif object.tag == "field" then
		local canon = freeze {
			tag = "field",
			base = self:scan(object.base),
			fieldName = object.fieldName,
			definition = object.definition,
		}
		self.relevant[shown] = canon
		ref(canon.base)
	elseif object.tag == "variant" then
		local canon = freeze {
			tag = "variant",
			base = self:scan(object.base),
			variantName = object.variantName,
			definition = object.definition,
		}
		self.relevant[shown] = canon
		ref(canon.base)
	elseif object.tag == "isa" then
		local canon = freeze {
			tag = "isa",
			base = self:scan(object.base),
			variant = object.variant,
		}
		self.relevant[shown] = canon
		ref(canon.base)
	elseif object.tag == "forall" then
		-- Comparing by object identity is OK
		self.relevant[shown] = object
	end

	assert(self.relevant[shown], "unhandled tag `" .. object.tag .. "`")
	showSkip[self.relevant[shown]] = shown
	return self.relevant[shown]
end

local cID = 0
local function newConst()
	cID = cID + 1
	return "const." .. cID
end

local TRUE_ASSERTION = freeze {tag = "boolean", value = true}
local FALSE_ASSERTION = freeze {tag = "boolean", value = false}

local INT_ASSERTIONS = freeze {
	[10] = {tag = "int", value = 10},
	[3] = {tag = "int", value = 3},
	[2] = {tag = "int", value = 2},
	[1] = {tag = "int", value = 1},
	[0] = {tag = "int", value = 0},
	[-1] = {tag = "int", value = -1},
}

-- RETURNS a list of clauses
local function quantifierClauses(model, term, canon)
	assert(term.tag == "forall")

	if model[term] then
		-- Find all terms of the specified sort
		-- Instantiate for all interesting terms

		-- TODO: PERFORMANCE: filter by triggers, see
		-- https://doi.org/10.1007/978-3-540-73595-3_12
		local opportunities = {}
		for _, x in spairs(canon.relevant) do
			assertis(x, "Assertion")

			local tx = typeOfAssertion(x)
			assertis(tx, "Type+")

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
			-- TODO: this is a terrible heuristic
			if (x.tag == "variable" and (x.variable.name:find "local" or not x.variable.name:find "[^a-zA-Z0-9']")) or x.tag == "fn" then
				-- Instantiate an example of a forall instance
				local constantName = newConst() .. "forall" .. tostring(term.unique)
				local newTerm, res, var = term:instantiate(constantName)

				-- x is the same as constant
				table.insert(out, eqAssertion(x, variableAssertion(var), term.quantified))

				-- The predicate holds for `x`
				table.insert(out, newTerm)
				table.insert(out, res)
			end
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
	assert(meta)

	-- Collect all in-scope/relevant constants
	local canon = {scan = m_scan; relevant = {}, referencedBy = {}}
	canon:scan(TRUE_ASSERTION)
	canon:scan(FALSE_ASSERTION)
	for _, v in spairs(INT_ASSERTIONS) do
		canon:scan(v)
	end
	for v in pairs(model) do
		canon:scan(v)
	end

	local newMeta = {}
	for k, v in pairs(meta) do
		newMeta[k] = v
	end

	local out = {}

	for term in pairs(model) do
		if term.tag == "forall" then
			if not newMeta[term.unique] then
				out[term] = quantifierClauses(model, term, canon)
				newMeta[term.unique] = true
			else
				-- This quantifier has already been instantiated
			end
		end
	end

	return out, newMeta
end

-- RETURNS a string such that for x, y
-- if approximateStructure(x) ~= approximateStructure(y)
-- then x, y have different structure and thus childrenSame(x, y) is false
local function approximateStructure(x)
	assertis(x, "Assertion")
	if x.tag == "fn" then
		return "fn-" .. x.signature.longName
	elseif x.tag == "field" then
		return "field-" .. x.fieldName
	else
		return x.tag
	end
end
approximateStructure = memoized(1, approximateStructure)

-- RETURNS a list of raw reasons when assertions x, y are equivalent due to
-- being equal functions of equal arguments
-- RETURNS false when they are not equal
local function childrenSame(eq, x, y)
	assert(eq)
	assertis(x, "Assertion")
	assertis(y, "Assertion")
	assert(not eq:query(x, y))

	if x.tag ~= y.tag then
		-- Elements that are structurally different cannot be shown
		-- to be the same here
		return false
	elseif TERMINAL_TAG[x.tag] then
		-- Terminal elements that aren't in the same representative group
		-- cannot be shown to be equal here
		return false
	elseif x.tag == "fn" then
		if x.signature.longName ~= y.signature.longName then
			return false
		end

		-- The same method name on the same base type must be the same
		-- signature
		assert(#x.arguments == #y.arguments)
		for i in ipairs(x.arguments) do
			if not eq:query(x.arguments[i], y.arguments[i]) then
				return false
			end
		end

		-- The reason these functions are equal is that their arguments are
		-- equal: explain why their arguments are equal
		local reasonSets = {}
		for i in ipairs(x.arguments) do
			for _, s in ipairs(eq:reasonEq(x.arguments[i], y.arguments[i])) do
				table.insert(reasonSets, s)
			end
		end
		return table.concatted(unpack(reasonSets))
	elseif x.tag == "field" then
		if x.fieldName ~= y.fieldName then
			return false
		end
		if not eq:query(x.base, y.base) then
			return false
		end
		return table.concatted(unpack(eq:reasonEq(x.base, y.base)))
	elseif x.tag == "isa" then
		if x.variant ~= y.variant then
			return false
		end
		if not eq:query(x.base, y.base) then
			return false
		end
		return table.concatted(unpack(eq:reasonEq(x.base, y.base)))
	elseif x.tag == "variant" then
		if x.variantName ~= y.variantName then
			return false
		end
		if not eq:query(x.base, y.base) then
			return false
		end
		return table.concatted(unpack(eq:reasonEq(x.base, y.base)))
	end
	error("TODO childrenSame for tag `" .. x.tag .. "`")
end

-- RETURNS a set (map from Assertion to true)
local function thoseReferencingAny(canon, list)
	assertis(list, listType "Assertion")

	local out = {}
	for _, element in pairs(list) do
		local references = canon.referencedBy[element]
		if references then
			for i = 1, #references do
				out[references[i]] = true
			end
		end
	end
	return out
end

-- RETURNS nothing
local function union(canon, eq, bin)
	assertis(bin, recordType {
		left = "Assertion",
		right = "Assertion",
		raws = listType "Assertion",
	})

	if not eq:query(bin.left, bin.right) then
		local thoseThatReferenceA = thoseReferencingAny(canon, eq:classOf(bin.left))
		local thoseThatReferenceB = thoseReferencingAny(canon, eq:classOf(bin.right))
		eq:union(bin.left, bin.right, bin.raws)

		-- Union all functions of equal arguments
		for x in pairs(thoseThatReferenceA) do
			for y in pairs(thoseThatReferenceB) do
				if not eq:query(x, y) then
					local reasonsSame = childrenSame(eq, x, y)
					if reasonsSame then
						local reasons = table.concatted(reasonsSame, bin.raws)
						eq:union(x, y, reasons)
					end
				end
			end
		end
	end
end

-- RETURNS whether or not the given model is satisfiable in a quantifier free
-- theory of uninterpreted functions
-- as a part of the 'theory' interface for the SMT solver
function theory:isSatisfiable(modelInput)
	assertis(modelInput, mapType("Assertion", "boolean"))

	local unquantifiedModel = {}
	for key, value in pairs(modelInput) do
		if key.tag == "forall" then
			-- Do not handle here.
			-- See theory:additionalClauses.
		else
			-- Regular, non-quantifier expression
			unquantifiedModel[key] = value
		end
	end

	-- 1) Generate a list of relevant subexpressions
	local canon = {scan = m_scan; relevant = {}, referencedBy = {}}
	local trueAssertion = canon:scan(TRUE_ASSERTION)
	local falseAssertion = canon:scan(FALSE_ASSERTION)

	local simple = {}
	for key, truth in pairs(unquantifiedModel) do
		local object = canon:scan(key)

		-- After canonicalizing, two expressions with different truth
		-- assignments could be in the map
		if simple[object] ~= nil and simple[object].truth ~= truth then
			-- This model is inconsistent
			-- TODO: be more specific
			return false, {
				[key] = truth,
				[simple[object].raw] = simple[object].truth,
			}
		end
		simple[object] = {
			truth = truth,
			raw = key,
		}
	end
	assertis(simple, mapType("Assertion", recordType {
		raw = "Assertion",
		truth = "boolean",
	}))
	assertis(canon.relevant, mapType("string", "Assertion"))
	assertis(canon.referencedBy, mapType("Assertion", listType("Assertion")))

	-- 2) Find all positive == assertions
	local positiveEq, negativeEq = {}, {}
	for assertion, about in spairs(simple, showAssertion) do
		if assertion.tag == "fn" and assertion.signature.memberName == "eq" then
			assert(#assertion.arguments == 2)
			local left = canon:scan(assertion.arguments[1])
			local right = canon:scan(assertion.arguments[2])
			if about.truth then
				table.insert(positiveEq, {
					left = left,
					right = right,
					raws = {about.raw},
				})
			else
				table.insert(negativeEq, {
					left = left,
					right = right,
					raws = {about.raw},
				})
			end
		end

		if about.truth then
			table.insert(positiveEq, {
				left = trueAssertion,
				right = assertion,
				raws = {about.raw},
			})
		else
			table.insert(positiveEq, {
				left = falseAssertion,
				right = assertion,
				raws = {about.raw},
			})
		end
	end
	table.insert(negativeEq, {
		left = falseAssertion,
		right = trueAssertion,
		raws = {},
	})

	-- 3) Use each positive == assertion to join representatives
	local eq = UnionFind.new()
	for _, expression in pairs(canon.relevant) do
		eq:init(expression)
	end

	local byStructure = {}
	for _, x in spairs(canon.relevant) do
		local s = approximateStructure(x)
		byStructure[s] = byStructure[s] or {}
		table.insert(byStructure[s], x)
	end

	-- Union find
	while #positiveEq > 0 do
		local nEq = #positiveEq
		for _, bin in ipairs(positiveEq) do
			union(canon, eq, bin)
		end
		positiveEq = {}
	end

	-- 4) Use each negative == assertion to separate groups
	local rejects = {}
	for _, bin in ipairs(negativeEq) do
		local a, b = bin.left, bin.right

		if eq:query(a, b) then
			local began = os.clock()

			-- This model is inconsistent; explain the contradiction
			local limited = {}
			for _, a in ipairs(bin.raws) do
				table.insert(limited, a)
			end
			for _, s in ipairs(eq:reasonEq(a, b)) do
				for _, a in ipairs(s) do
					table.insert(limited, a)
				end
			end

			assert(1 <= #limited)

			local restricted = {}
			for _, key in ipairs(limited) do
				assert(modelInput[key] ~= nil)
				restricted[key] = modelInput[key]
			end

			table.insert(rejects, {
				elapsed = os.clock() - began,
				model = restricted,
				size = #table.keys(restricted),
			})
		end
	end

	if #rejects ~= 0 then
		return false, rejects[1].model
	end

	return true
end

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
		assertis(values, listType "Assertion")

		for _, row in ipairs(logic[target]) do
			assert(#row == #values)
		end

		return freeze(values), logic[target]
	end

	return false
end

--------------------------------------------------------------------------------

-- Tests

theory.evaluateConstantAssertion = evaluateConstantAssertion

theory = freeze(theory)
assertis(theory, "Theory")
return {
	theory = theory,
	notAssertion = notAssertion,
	eqAssertion = eqAssertion,
	variableAssertion = variableAssertion,
}
