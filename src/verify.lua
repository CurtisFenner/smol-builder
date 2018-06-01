local smt = import "smt.lua"

local verifyTheory = (import "verify-theory.lua").theory
local notAssertion = (import "verify-theory.lua").notAssertion
local eqAssertion = (import "verify-theory.lua").eqAssertion
local variableAssertion = (import "verify-theory.lua").variableAssertion

local Report = import "verify-errors.lua"

local ansi = import "ansi.lua"

--------------------------------------------------------------------------------

local common = import "common.lua"

local STRING_TYPE = common.STRING_TYPE
local INT_TYPE = common.INT_TYPE
local BOOLEAN_TYPE = common.BOOLEAN_TYPE
local UNIT_TYPE = common.UNIT_TYPE
local NEVER_TYPE = common.NEVER_TYPE

local typeOfAssertion = common.typeOfAssertion

local excerpt = common.excerpt

local assertionExprString = common.assertionExprString
local showTypeKind = common.showTypeKind

--------------------------------------------------------------------------------

REGISTER_TYPE("Action", choiceType(
	recordType {
		tag = constantType "predicate",
		value = "Assertion",
	},
	recordType {
		tag = constantType "assignment",
		destination = "VariableIR",
		value = "Assertion",
	},
	recordType {
		tag = constantType "branch",
		branches = listType(recordType {
			condition = "Assertion",
			scope = listType "Action",
		})
	}
))

REGISTER_TYPE("Assertion", choiceType(
	recordType {
		tag = constantType "int",
		value = "integer",
	},
	recordType {
		tag = constantType "string",
		value = "string",
	},
	recordType {
		tag = constantType "boolean",
		value = "boolean",
	},
	recordType {
		tag = constantType "this",
		type = "TypeKind",
	},
	recordType {
		tag = constantType "unit",
	},
	recordType {
		tag = constantType "variable",
		variable = "VariableIR",
	},
	recordType {
		tag = constantType "fn",
		arguments = listType "Assertion",
		signature = "Signature",
		index = "integer",
	},
	recordType {
		tag = constantType "field",
		base = "Assertion",
		fieldName = "string",
		definition = "nil",
	},
	recordType {
		tag = constantType "eq",
		left = "Assertion",
		right = "Assertion",
	},
	recordType {
		tag = constantType "gettag",
		base = "Assertion",
	},
	recordType {
		tag = constantType "symbol",
		symbol = "string",
	},
	recordType {
		tag = constantType "variant",
		variantName = "string",
		base = "Assertion",
	},
	recordType {
		tag = constantType "forall",
		quantified = "TypeKind",
		location = "Location",

		-- (self, constantName string) => Assertion
		instantiate = "function",

		-- A unique object per (lexically) unique forall
		-- N.B.: When unique matches, these MAY be different foralls, as they
		-- may be closed-over different bindings
		unique = "string",

		-- For different usages of the same forall
		instance = "string",
	}
))

-- RETURNS an Assertion representing a && b
local function andAssertion(a, b)
	assertis(a, "Assertion")
	assertis(b, "Assertion")

	local BUILTIN_LOC = {
		begins = "builtin",
		ends = "builtin",
	}

	local p = freeze {
		tag = "fn",
		arguments = {a, b},
		signature = common.builtinDefinitions.Boolean.functionMap["and"].signature,
		index = 1,
	}
	return p
end

-- RETURNS an Assertion representing a => b
local function impliesAssertion(a, b)
	assertis(a, "Assertion")
	assertis(b, "Assertion")

	local BUILTIN_LOC = {
		begins = "builtin",
		ends = "builtin",
	}

	local p = freeze {
		tag = "fn",
		arguments = {a, b},
		signature = common.builtinDefinitions.Boolean.functionMap["implies"].signature,
		index = 1,
	}
	return p
end

-- RETURNS an Assertion
local function assertionReplaced(expression, map)
	--assertis(expression, "Assertion")
	--assertis(map, mapType("string", recordType {value = "Assertion"}))

	local tag = expression.tag
	if tag == "variable" then
		if map[expression.variable.name] then
			return map[expression.variable.name].value
		end
		return expression
	end

	if tag == "unit" or tag == "this" or tag == "symbol" then
		return expression
	elseif tag == "forall" then
		return expression
	elseif tag == "boolean" or tag == "int" or tag == "string" then
		return expression
	elseif tag == "field" or tag == "gettag" or tag == "variant" then
		local subBase = assertionReplaced(expression.base, map)
		if subBase == expression.base then
			return expression
		end
		return freeze(table.with(expression, "base", subBase))
	elseif tag == "eq" then
		return freeze {
			tag = "eq",
			left = assertionReplaced(expression.left, map),
			right = assertionReplaced(expression.right, map),
		}
	end

	assert(tag == "fn", tag)

	local anyDifferent = false
	local newArguments = {}
	for _, a in ipairs(expression.arguments) do
		local newArgument = assertionReplaced(a, map)
		if newArgument ~= a then
			anyDifferent = true
		end
		table.insert(newArguments, newArgument)
	end
	if not anyDifferent then
		return expression
	end
	return table.with(expression, "arguments", newArguments)
end

--------------------------------------------------------------------------------

local VALUE_THIS = freeze {tag = "this"}
local VALUE_UNIT = freeze {tag = "unit"}

-- RETURNS an Assertion
local function valueInt(int)
	assertis(int, "integer")

	return freeze {
		tag = "int",
		value = int,
	}
end
valueInt = memoized(1, valueInt)

-- RETURNS an Assertion
local function valueString(str)
	assertis(str, "string")

	return freeze {
		tag = "string",
		value = str,
	}
end
valueString = memoized(1, valueString)

local trueBoolean = freeze {
	tag = "boolean",
	value = true,
}
local falseBoolean = freeze {
	tag = "boolean",
	value = false,
}

-- RETURNS an Assertion
local function valueBoolean(bool)
	assertis(bool, "boolean")

	if bool then
		return trueBoolean
	end
	return falseBoolean
end

local uniqueNameID = 1000
local function uniqueVariable(type)
	assertis(type, "TypeKind")

	uniqueNameID = uniqueNameID + 1

	return freeze {
		type = type,
		name = "__unique" .. uniqueNameID,
	}
end

-- MODIFIES scope
-- RETURNS nothing
local function addPredicate(scope, value)
	assertis(scope, listType "Action")
	assertis(value, "Assertion")

	table.insert(scope, freeze {
		tag = "predicate",
		value = value,
	})
end

-- RETURNS nothing
-- MODIFIES scope
local function assignRaw(scope, destination, value)
	assertis(scope, listType "Action")
	assertis(destination, "VariableIR")
	assertis(value, "Assertion")

	table.insert(scope, freeze {
		tag = "assignment",
		destination = destination,
		value = value,
	})
end

-- RETURNS nothing
-- MODIFIES scope
local function addMerge(scope, branches)
	-- Learn the disjunction of branches
	assertis(scope, listType "Action")
	assertis(branches, listType(recordType {
		scope = listType "Action",
		condition = "Assertion",
	}))

	local action = freeze {
		tag = "branch",
		branches = branches,
	}
	assertis(action, "Action")
	table.insert(scope, action)
end

-- RETURNS a Symbol Assertion
local function variantSymbol(type, variant)
	assertis(type, "TypeKind")
	assertis(variant, "string")

	-- TODO: be more specific and include type
	return freeze {
		tag = "symbol",
		symbol = variant,
	}
end

-- RETURNS an Assertion
-- MODIFIES scope
local snapshotID = 0
local function addSnapshot(scope, assertion)
	assertis(scope, listType "Action")
	assertis(assertion, "Assertion")

	snapshotID = snapshotID + 1
	local name = "snapshot'" .. snapshotID
	local variable = freeze {
		type = typeOfAssertion(assertion),
		name = name,
	}
	assignRaw(scope, variable, assertion)

	return variableAssertion(variable)
end

-- RETURNS a list of true Assertion predicates, inNow
-- path: a string used to generate unique names
local function getPredicateSet(scope, assignments, path, skip)
	assertis(scope, listType "Action")
	assertis(assignments, mapType("string", recordType {
		value = "Assertion",
		definition = "VariableIR",
	}))
	assertis(path, "string")
	skip = skip or 0

	-- TODO: come up with something that deals with loops
	local predicates = {}

	-- RETURNS an Assertion
	local function inNow(a)
		assertis(a, "Assertion")
		a = assertionReplaced(a, assignments)
		return a
	end

	-- Translate assignments as a substitution in all subsequent predicates
	for i, action in ipairs(scope) do
		if action.tag == "assignment" then
			local t = action.destination.type

			local newID = action.destination.name .. "'" .. i .. "'" .. path
			local newVariable = freeze {
				type = action.destination.type,
				location = action.destination.location,
				name = newID,
				description = action.destination.description,
			}
			local newV = variableAssertion(newVariable)

			-- Record the value of this new assignment at this time
			local current = inNow(action.value)
			local p = eqAssertion(current, newV, t)

			-- Update the mapping to point to the new variable
			assignments[action.destination.name] = freeze {
				value = newV,
				definition = action.destination,
			}

			table.insert(predicates, p)
		elseif action.tag == "predicate" then
			table.insert(predicates, inNow(action.value))
		elseif action.tag == "branch" then
			-- Learn the facts of both, predicated by condition => ...
			for bi, branch in ipairs(action.branches) do
				local condition = inNow(branch.condition)
				local notCondition = notAssertion(condition)

				local branchAssignments = {}
				for key, value in pairs(assignments) do
					branchAssignments[key] = value
				end

				local branchPredicates = getPredicateSet(
					branch.scope,
					branchAssignments,
					path .. "'" .. bi
				)
				for _, p in ipairs(branchPredicates) do
					table.insert(predicates, impliesAssertion(condition, p))
				end

				-- Capture modified variables into a select operation
				for variable, newValue in pairs(branchAssignments) do
					local oldValue = assignments[variable]
					if oldValue == nil or newValue.value ~= oldValue.value then
						-- Create new dummy variable
						local id = "merged'" .. variable .. "'" .. path .. "'" .. i
						local merged = variableAssertion(table.with(newValue.definition, "name", id))
						assignments[variable] = freeze {
							value = merged,
							definition = newValue.definition,
						}

						if oldValue then
							-- Given it old meaning when condition does not hold
							-- (Leave undefined when there was no old value)
							local isOld = eqAssertion(merged, oldValue.value, oldValue.definition.type)
							table.insert(predicates, impliesAssertion(notCondition, isOld))
						end

						-- Give it new meaning when condition does hold
						local isNew = eqAssertion(merged, newValue.value, newValue.definition.type)
						table.insert(predicates, impliesAssertion(condition, isNew))
					end
				end
			end
		else
			error("unknown action tag `" .. action.tag .. "`")
		end

		if i == skip then
			-- Wipe out predicates learned before this point
			predicates = {}
		end
	end
	assertis(predicates, listType "Assertion")
	return predicates, inNow
end

-- RETURNS a boolean indicating whether or not `scope` MUST model `predicate`
local function mustModel(scope, target)
	local predicates, inNow = getPredicateSet(scope, {}, "")

	assertis(target, "Assertion")
	local result = inNow(target)

	local tautology, counter = smt.implies(verifyTheory, predicates, result)

	if not tautology then
		local explanation = {}
		for assertion, truth in pairs(counter) do
			local shown = assertionExprString(assertion) .. "\n\t\t" .. verifyTheory:canonKey(assertion)
			table.insert(explanation, {expression = shown, truth = truth})
		end
		return false, explanation
	end

	return tautology
end

-- RETURNS an Assertion
local function resultAssertion(statement, index)
	assertis(statement, "StatementIR")
	statement = freeze(statement)
	assert(statement.tag == "static-call" or statement.tag == "dynamic-call")
	assertis(index, "integer")

	local arguments = table.map(variableAssertion, statement.arguments)

	-- eq is a special name
	if statement.signature.memberName == "eq" then
		assert(#arguments == 2)

		return freeze {
			tag = "eq",
			left = arguments[1],
			right = arguments[2],
		}
	end

	return freeze {
		tag = "fn",
		arguments = arguments,
		signature = statement.signature,
		index = index,
	}
end

-- RETURNS an Assertion
local function fieldAssertion(statement)
	assertis(statement, "FieldSt")

	return freeze {
		tag = "field",
		fieldName = statement.name,
		base = variableAssertion(statement.base),
	}
end

-- RETURNS an Assertion
local function variantAssertion(statement)
	assertis(statement, "VariantSt")

	return freeze {
		tag = "variant",
		variantName = statement.variant,
		base = variableAssertion(statement.base),
	}
end

-- RETURNS a mutable list of Actions, a copy of the given scope.
local function scopeCopy(scope)
	assertis(scope, listType "Action")

	local out = {}
	for _, action in ipairs(scope) do
		-- Actions are immutable, so these can be copied by keeping a reference
		table.insert(out, action)
	end
	return out
end

-- RETURNS the subset of the new scope that is not in the old scope
local function scopeAdditional(old, new)
	-- Right now assumes that the new scope has the old scope as a prefix
	assert(#new >= #old)
	for i = 1, #old do
		assert(old[i] == new[i])
	end

	local out = {}
	for i = #old + 1, #new do
		table.insert(out, new[i])
	end
	return out
end

-- RETURNS a list of VariableIRs
local function localsInStatement(statement)
	assertis(statement, "StatementIR")

	if statement.tag == "local" then
		return {statement.variable}
	elseif statement.tag == "sequence" then
		local out = {}
		for _, child in ipairs(statement.statements) do
			for _, e in ipairs(localsInStatement(child)) do
				table.insert(out, e)
			end
		end
		return out
	elseif statement.tag == "match" then
		local out = {}
		for _, case in ipairs(statement.cases) do
			for _, e in ipairs(localsInStatement(case.statement)) do
				table.insert(out, e)
			end
		end
		return out
	end

	local terminal = {
		assume = {},
		verify = {},

		-- Proofs are recursive
		proof = {"body"},

		string = {},
		nothing = {},
		assign = {},
		["return"] = {},
		["if"] = {"bodyThen", "bodyElse"},
		int = {},
		["new-class"] = {},
		["new-union"] = {},
		["static-call"] = {},
		["method-call"] = {},
		["generic-method-call"] = {},
		["generic-static-call"] = {},
		boolean = {},
		field = {},
		this = {},
		unit = {},
		variant = {},
		isa = {},
		forall = {},
	}

	local out = {}
	for _, property in ipairs(terminal[statement.tag]) do
		for _, e in ipairs(localsInStatement(statement[property])) do
			table.insert(out, e)
		end
	end
	return out
end

-- MODIFIES scope
-- RETURNS nothing
local function verifyStatement(statement, scope, semantics)
	assertis(statement, "StatementIR")
	assertis(scope, listType "Action")
	assertis(semantics, "Semantics")

	local allDefinitions = table.concatted(
		semantics.compounds,
		semantics.interfaces
	)
	allDefinitions = freeze(allDefinitions)

	if statement.tag == "sequence" then
		for _, sub in ipairs(statement.statements) do
			verifyStatement(sub, scope, semantics)
		end
		return
	elseif statement.tag == "verify" then
		-- Check that this variable is true in the current scope
		local models, counter = mustModel(scope, variableAssertion(statement.variable))
		if not models then
			Report.DOES_NOT_MODEL {
				reason = statement.reason,
				conditionLocation = statement.conditionLocation,
				checkLocation = statement.checkLocation,
				counter = counter,
			}
		end

		return
	elseif statement.tag == "assume" then
		-- Make this expression become true in the current scope
		addPredicate(scope, variableAssertion(statement.variable))

		return
	elseif statement.tag == "local" then
		-- Do nothing
		return
	elseif statement.tag == "this" then
		-- This
		local this = table.with(VALUE_THIS, "type", statement.destination.type)
		assignRaw(scope, statement.destination, this)
		return
	elseif statement.tag == "unit" then
		-- Unit
		assignRaw(scope, statement.destination, VALUE_UNIT)
		return
	elseif statement.tag == "field" then
		local assertion = fieldAssertion(statement)
		assignRaw(scope, statement.destination, assertion)
		return
	elseif statement.tag == "variant" then
		-- TODO: verify isa
		local assertion = variantAssertion(statement)
		assignRaw(scope, statement.destination, assertion)
		return
	elseif statement.tag == "int-load" then
		-- Integer literal
		assignRaw(scope, statement.destination, valueInt(statement.number))
		return
	elseif statement.tag == "string-load" then
		-- String literal
		assignRaw(scope, statement.destination, valueString(statement.string))
		return
	elseif statement.tag == "boolean" then
		-- Boolean literal
		assignRaw(scope, statement.destination, valueBoolean(statement.boolean))
		return
	elseif statement.tag == "static-call" or statement.tag == "dynamic-call" then
		for i, destination in ipairs(statement.destinations) do
			local source = resultAssertion(statement, i)
			assignRaw(scope, destination, source)
		end
		return
	elseif statement.tag == "return" then
		-- Do nothing
		return
	elseif statement.tag == "new-class" then
		local fields = {}
		for n, v in pairs(statement.fields) do
			fields[n] = variableAssertion(v)
		end

		assertis(statement.destination.type, "CompoundTypeKind")

		local instance = variableAssertion(uniqueVariable(statement.destination.type))
		assignRaw(scope, statement.destination, instance)

		for fieldName, value in pairs(statement.fields) do
			local assertion = freeze {
				tag = "field",
				base = instance,
				fieldName = fieldName,
			}
			assertis(assertion, "Assertion")
			assertis(value, "VariableIR")
			local t = value.type
			local eq = eqAssertion(assertion, variableAssertion(value), t)
			assertis(eq, "Assertion")
			addPredicate(scope, eq)
		end

		return
	elseif statement.tag == "new-union" then
		-- Record the tag
		addPredicate(scope, freeze {
			tag = "eq",
			left = {
				tag = "gettag",
				base = variableAssertion(statement.destination),
			},
			right = variantSymbol(statement.destination.type, statement.field),
		})

		-- Record the variant contents
		local extract = freeze {
			tag = "variant",
			variantName = statement.field,
			base = variableAssertion(statement.destination),
		}
		assertis(extract, "Assertion")

		local right = variableAssertion(statement.value)
		addPredicate(scope, eqAssertion(extract, right, statement.value.type))
		return
	elseif statement.tag == "assign" then
		assignRaw(scope, statement.destination, variableAssertion(statement.source))
		return
	elseif statement.tag == "match" then
		local branches = {}

		-- Check each case
		assert(#statement.cases > 0)
		local posts = {}
		for _, case in ipairs(statement.cases) do
			local subscope = scopeCopy(scope)

			local condition = freeze {
				tag = "eq",
				left = {
					tag = "gettag",
					base = variableAssertion(statement.base),
				},
				right = variantSymbol(statement.base.type, case.variant),
			}

			-- Remember whether or not the condition was true when we started
			-- evaluating it
			local snappedCondition = addSnapshot(scope, condition, statement.base.location)

			-- Add variant predicate
			addPredicate(subscope, condition)
			verifyStatement(case.statement, subscope, semantics)

			if case.statement.returns ~= "yes" then
				table.insert(branches, {
					scope = subscope,
					condition = condition,
				})
			else
				-- After the branch, we can assume the condition didn't hold
				-- since those paths returned
				table.insert(posts, notAssertion(snappedCondition))
			end
		end

		if #branches == 0 then
			-- The code after this is unreachable, so the scope is irrelevant
			assert(statement.returns == "yes")
			return
		end

		-- Learn the disjunction of the new statements
		addMerge(scope, branches)

		-- Learn things from cut branches
		for _, post in ipairs(posts) do
			addPredicate(scope, post)
		end

		return
	elseif statement.tag == "if" then
		local conditionAssertion = variableAssertion(statement.condition)

		-- Capture the truth value of the condition at evaluation time
		local snappedCondition = addSnapshot(
			scope,
			conditionAssertion
		)


		-- Evaluate the then body with condition given
		local thenScope = scopeCopy(scope)
		addPredicate(thenScope, conditionAssertion)
		verifyStatement(statement.bodyThen, thenScope, semantics)

		-- Evaluate the else body with negation of the condtion given
		local elseScope = scopeCopy(scope)
		addPredicate(elseScope, notAssertion(conditionAssertion))
		verifyStatement(statement.bodyElse, elseScope, semantics)

		-- Learn the disjunction of new statements
		local posts = {}
		local branches = {}
		if statement.bodyThen.returns ~= "yes" then
			local newThen = scopeAdditional(scope, thenScope)
			table.insert(branches, {scope = newThen, condition = conditionAssertion})
		else
			-- Learn the cut; may assume not(condition)
			table.insert(posts, notAssertion(snappedCondition))
		end

		if statement.bodyElse.returns ~= "yes" then
			local newElse = scopeAdditional(scope, elseScope)
			table.insert(branches, {
				scope = newElse,
				condition = notAssertion(conditionAssertion),
			})
		else
			-- Learn the cut; may assume condition
			table.insert(posts, snappedCondition)
		end

		if #branches == 0 then
			-- No code follows here
			assert(statement.returns == "yes")
			return
		end

		-- Learn the disjunction of the new statements
		addMerge(scope, branches)

		-- Learn things from cut branches
		for _, post in ipairs(posts) do
			addPredicate(scope, post)
		end

		return
	elseif statement.tag == "isa" then
		assertis(statement, "IsASt")
		assignRaw(scope, statement.destination, freeze {
			tag = "eq",
			left = {
				tag = "gettag",
				base = variableAssertion(statement.base),
			},
			right = variantSymbol(statement.base.type, statement.variant),
		})
		return
	elseif statement.tag == "proof" then
		verifyStatement(statement.body, scope, semantics)
		return
	elseif statement.tag == "forall" then
		local subscopePrime = scopeCopy(scope)

		-- RETURNS background assertions, result value, VariableIR made from name
		local function instantiate(self, name)
			assertis(name, "string")

			-- Get an arbitrary instantiation
			local arbitrary = freeze {
				name = name,
				type = statement.quantified,
				location = statement.location,
				description = false,
			}
			assertis(arbitrary, "VariableIR")

			local subscope = scopeCopy(subscopePrime)
			local inCode, instanceTruth = statement.instantiate(arbitrary)
			verifyStatement(inCode, subscope, semantics)

			-- Discover the newly learned facts in this hypothetical
			local learnedPredicates, inNow = getPredicateSet(subscope, {}, "", #subscopePrime)

			local post = {}
			for _, p in ipairs(learnedPredicates) do
				table.insert(post, p)
			end

			-- Return the conjunction
			if #post == 0 then
				return trueBoolean
			end
			local u = post[1]
			for i = 2, #post do
				u = andAssertion(u, post[i])
			end

			assertis(instanceTruth, "VariableIR")
			local finalInstantiationTruth = inNow(variableAssertion(instanceTruth), true)
			return u, finalInstantiationTruth, arbitrary
		end

		-- Create a forall expression
		assignRaw(scope, statement.destination, freeze {
			tag = "forall",
			quantified = statement.quantified,
			instantiate = instantiate,
			location = statement.location,

			-- All "versions" of this assertion can be grouped
			unique = statement.unique,

			-- But they can be difference because they are "closed"
			-- over different values
			instance = tostring(math.random()),
		})

		return
	end

	error("unhandled statement `" .. statement.tag .. "`")
end

-- RETURNS nothing
local function verifyFunction(func, semantics)
	assertis(func, "FunctionIR")
	assertis(semantics, "Semantics")
	assert(func.body)

	--local modifier = func.signature.modifier
	--local fullName = func.signature.longName
	--print("== " .. modifier .. " " .. fullName .. " " .. string.rep("=", 80))
	--print(common.showStatement(func.body))

	verifyStatement(func.body, {}, semantics)
end

-- RETURNS nothing
return function(semantics)
	for _, c in ipairs(semantics.compounds) do
		assertis(c, recordType {
			tag = choiceType(constantType("union-definition"), constantType("class-definition")),
			fieldMap = mapType("string", recordType {
				name = "string",
				type = "TypeKind",
			}),
			constraintArguments = "object",
		})
		assertis(c.constraintArguments, listType(recordType {
			name = "string",
			index = "integer",
			constraint = "ConstraintKind",
		}))
	end
	assertis(semantics, "Semantics")

	-- Verify all functions
	for _, func in ipairs(semantics.functions) do
		if func.body then
			verifyFunction(freeze(func), semantics)
		end
	end
end
