local profile = import "profile.lua"
local Stopwatch = import "stopwatch.lua"

local theory = {
	assertion_t = "Assertion",
	satisfaction_t = "any",
}

local UnionFind = import "unionfind.lua"

local common = import "common.lua"
local showType = common.showType

local BUILTIN_DEFINITIONS = common.BUILTIN_DEFINITIONS
local BOOLEAN_DEF = table.findwith(BUILTIN_DEFINITIONS, "name", "Boolean")

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

-- RETURNS an EqAssertion representing a == b
local function eqAssertion(a, b, t)
	assertis(a, "Assertion")
	assertis(b, "Assertion")
	assertis(t, "Type+")

	local p = freeze {
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

local function m_ref(self, object, child)
	local sChild = showAssertion(child)
	local sObject = showAssertion(object)
	assert(sChild ~= sObject)
	assert(self.relevant[sChild], "child must already be in map")

	self.referencedBy[child] = self.referencedBy[child] or {}
	table.insert(self.referencedBy[child], self.relevant[sObject])
end

local globalCanon = {}

-- Canonicalizes objects so that syntactically equivalent subtrees become the
-- same reference
local function m_scan(self, object)
	assertis(object, "Assertion")

	local shown = showAssertion(object)
	if self.relevant[shown] then
		return self.relevant[shown]
	end

	local pre = globalCanon[shown]
	if pre ~= nil then
		self.relevant[shown] = pre

		if TERMINAL_TAG[pre.tag] then
			-- Do nothing
		elseif pre.tag == "fn" then
			for _, argument in ipairs(pre.arguments) do
				assert(argument == m_scan(self, argument))
				m_ref(self, pre, argument)
			end
		elseif pre.tag == "field" or pre.tag == "variant" or pre.tag == "gettag" then
			assert(pre.base == m_scan(self, pre.base))
			m_ref(self, pre, pre.base)
		elseif pre.tag == "forall" then
			-- Do nothing
		elseif pre.tag == "eq" then
			assert(pre.left == m_scan(self, pre.left))
			assert(pre.right == m_scan(self, pre.right))
			m_ref(self, pre, pre.left)
			m_ref(self, pre, pre.right)
		else
			error("unhandled tag " .. pre.tag)
		end

		return pre
	end

	if TERMINAL_TAG[object.tag] then
		self.relevant[shown] = object
	elseif object.tag == "fn" then
		local arguments = {}
		for _, argument in ipairs(object.arguments) do
			table.insert(arguments, m_scan(self, argument))
		end
		local canon = fnAssertion(
			object.signature,
			arguments,
			object.index
		)
		self.relevant[shown] = canon
		for _, argument in ipairs(arguments) do
			m_ref(self, canon, argument)
		end
	elseif object.tag == "field" then
		local canon = freeze {
			tag = "field",
			base = self:scan(object.base),
			fieldName = object.fieldName,
			definition = object.definition,
		}
		self.relevant[shown] = canon
		m_ref(self, canon, canon.base)
	elseif object.tag == "variant" then
		local canon = freeze {
			tag = "variant",
			base = self:scan(object.base),
			variantName = object.variantName,
			definition = object.definition,
		}
		self.relevant[shown] = canon
		m_ref(self, canon, canon.base)
	elseif object.tag == "gettag" then
		local canon = freeze {
			tag = "gettag",
			base = self:scan(object.base),
		}
		self.relevant[shown] = canon
		m_ref(self, canon, canon.base)
	elseif object.tag == "forall" then
		-- Comparing by object identity is OK
		self.relevant[shown] = object
	elseif object.tag == "eq" then
		local canon = freeze {
			tag = "eq",
			left = self:scan(object.left),
			right = self:scan(object.right),
		}
		self.relevant[shown] = canon
		m_ref(self, canon, canon.left)
		m_ref(self, canon, canon.right)
	end

	assert(self.relevant[shown], "unhandled tag `" .. object.tag .. "`")
	showSkip[self.relevant[shown]] = shown
	globalCanon[shown] = self.relevant[shown]
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
		return "fn-" .. e.signature.longName, e.arguments
	elseif e.tag == "eq" then
		return "eq", {e.left, e.right}
	end
	error("unknown Assertion tag `" .. e.tag .. "`")
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
		for _, equivalent in ipairs(eq:classOf(argument)) do
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
	return expression.signature.eval(unpack(argumentLiterals)), reasons
end

-- RETURNS whether or not the given model is satisfiable in a quantifier free
-- theory of uninterpreted functions
-- as a part of the 'theory' interface for the SMT solver
function theory:isSatisfiable(modelInput)
	assertis(modelInput, mapType("Assertion", "boolean"))

	local watch = Stopwatch.new(string.format("theory(%d)", #table.keys(modelInput)), 0.1)

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

	watch:clock("canon", function()
		for key, truth in pairs(unquantifiedModel) do
			local object = canon:scan(key)

			-- After canonicalizing, two expressions with different truth
			-- assignments could be in the map
			if simple[object] ~= nil and simple[object].truth ~= truth then
				-- This model is inconsistent
				-- TODO: be more specific
				watch:finish()
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
	end)

	assertis(simple, mapType("Assertion", recordType {
		raw = "Assertion",
		truth = "boolean",
	}))
	assertis(canon.relevant, mapType("string", "Assertion"))
	assertis(canon.referencedBy, mapType("Assertion", listType("Assertion")))

	-- 2) Find all positive == assertions
	local positiveEq, negativeEq = {}, {}

	watch:clock("separate eq", function()
		for assertion, about in spairs(simple, showAssertion) do
			if assertion.tag == "eq" then
				local left = canon:scan(assertion.left)
				local right = canon:scan(assertion.right)
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
	end)

	table.insert(negativeEq, {
		left = falseAssertion,
		right = trueAssertion,
		raws = {},
	})

	-- 3) Use each positive == assertion to join representatives
	local eq = UnionFind.new()
	local symbols = {}
	for _, expression in pairs(canon.relevant) do
		eq:init(expression)
		if expression.tag == "symbol" then
			table.insert(symbols, expression)
		end
	end

	-- Distinct symbols are not equal
	for i = 1, #symbols do
		for j = 1, i - 1 do
			table.insert(negativeEq, {
				left = symbols[i],
				right = symbols[j],
				raws = {},
			})
		end
	end

	-- Union find
	local it = 0
	while #positiveEq > 0 do
		it = it + 1

		watch:clock("union(" .. #positiveEq .. ")", function()
			for _, bin in ipairs(positiveEq) do
				eq:union(bin.left, bin.right, bin.raws)
			end
		end)

		positiveEq = {}

		watch:clock("function unioning", function()
			local byStructure = {}
			for _, expression in pairs(canon.relevant) do
				local id, subs = recursiveStructure(expression)
				if id then
					assert(#subs >= 1)
					-- A recursive expression
					local keyStrings = {id}
					for _, sub in ipairs(subs) do
						table.insert(keyStrings, tostring(eq:classOf(sub)))
					end

					local key = table.concat(keyStrings, ", ")
					local other = byStructure[key]
					if other then
						if not eq:query(expression, other) then
							-- Functions of equal arguments are equal
							local _, otherSubs = recursiveStructure(other)
							assert(#otherSubs == #subs)
							local reasons = {}
							for i in ipairs(subs) do
								for _, set in ipairs(eq:reasonEq(subs[i], otherSubs[i])) do
									for _, reason in ipairs(set) do
										table.insert(reasons, reason)
									end
								end
							end
							table.insert(positiveEq, {
								left = other,
								right = expression,
								raws = reasons,
							})
						end
					else
						byStructure[key] = expression
					end
				end
			end
		end)

		-- Evaluate constant functions
		watch:clock("constant eval", function()
			for _, expression in pairs(canon.relevant) do
				if expression.tag == "fn" then
					local literal, reasons = fnLiteralEvaluation(expression, eq)
					if literal ~= nil then
						local literalExpression = constantAssertion(literal)
						literalExpression = canon:scan(literalExpression)
						eq:tryinit(literalExpression)

						for _, reason in ipairs(reasons) do
							assert(modelInput[reason] ~= nil)
						end

						if not eq:query(literalExpression, expression) then
							table.insert(positiveEq, {
								left = expression,
								right = literalExpression,
								raws = reasons,
							})
						end
					end
				end
			end
		end)
	end

	-- 4) Use each negative == assertion to separate groups
	local rejects = {}
	watch:clock("!=", function()
		for _, bin in ipairs(negativeEq) do
			local a, b = bin.left, bin.right

			if eq:query(a, b) then
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
				table.insert(rejects, limited)
			end
		end
	end)

	-- 5) Check that constants don't disagree
	for _, expression in pairs(canon.relevant) do
		local literal = isLiteralAssertion(expression)
		if literal ~= nil then
			for _, equivalent in ipairs(eq:classOf(expression)) do
				local otherLiteral = isLiteralAssertion(equivalent)
				if otherLiteral ~= nil and otherLiteral ~= literal then
					table.insert(rejects, table.concatted(unpack(eq:reasonEq(expression, equivalent))))
				end
			end
		end
	end

	if #rejects ~= 0 then
		local best = rejects[1]

		local restricted = {}
		for _, key in ipairs(best) do
			assert(modelInput[key] ~= nil)
			restricted[key] = modelInput[key]
		end

		watch:finish()
		return false, restricted
	end

	watch:finish()
	return true
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
		assertis(values, listType "Assertion")

		for _, row in ipairs(logic[target]) do
			assert(#row == #values)
		end

		return freeze(values), logic[target]
	elseif assertion.tag == "eq" then
		if areTypesEqual(BOOLEAN_TYPE, typeOfAssertion(assertion.left)) then
			-- if and only if
			return freeze {assertion.left, assertion.right}, IFF[target]
		end
	end

	return false
end

--------------------------------------------------------------------------------

theory = freeze(theory)
assertis(theory, "Theory")
return {
	theory = theory,
	notAssertion = notAssertion,
	eqAssertion = eqAssertion,
	variableAssertion = variableAssertion,
}
