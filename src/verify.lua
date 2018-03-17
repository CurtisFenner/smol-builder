local calculateSemantics = import "semantics.lua"
local showType = calculateSemantics.showType
local showInterfaceType = calculateSemantics.showInterfaceType

local smt = import "smt.lua"

local verifyTheory = (import "verify-theory.lua").theory
local notAssertion = (import "verify-theory.lua").notAssertion
local eqAssertion = (import "verify-theory.lua").eqAssertion
local variableAssertion = (import "verify-theory.lua").variableAssertion

local Report = import "verify-errors.lua"

local profile = import "profile.lua"
local ansi = import "ansi.lua"

--------------------------------------------------------------------------------

local common = import "common.lua"

local STRING_TYPE = common.STRING_TYPE
local INT_TYPE = common.INT_TYPE
local BOOLEAN_TYPE = common.BOOLEAN_TYPE
local UNIT_TYPE = common.UNIT_TYPE
local NEVER_TYPE = common.NEVER_TYPE

local BUILTIN_DEFINITIONS = common.BUILTIN_DEFINITIONS

local BOOLEAN_DEF = table.findwith(BUILTIN_DEFINITIONS, "name", "Boolean")

local typeOfAssertion = common.typeOfAssertion

local excerpt = common.excerpt
local variableDescription = common.variableDescription

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

REGISTER_TYPE("MethodAssertion", recordType {
	tag = constantType "method",
	base = "Assertion",
	arguments = listType "Assertion",
	signature = "Signature",
	index = "integer",

	-- XXX: delete this
	methodName = "nil",
})

REGISTER_TYPE("FieldAssertion", recordType {
	tag = constantType "field",
	base = "Assertion",
	fieldName = "string",
	definition = "VariableIR",
})

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
		type = "Type+",
	},
	recordType {
		tag = constantType "unit",
	},
	"FieldAssertion",
	"MethodAssertion",
	recordType {
		tag = constantType "static",
		base = "string",
		arguments = listType "Assertion",
		signature = "Signature",
		index = "integer",

		-- XXX: delete this
		staticName = "nil",
	},
	recordType {
		tag = constantType "variable",
		variable = "VariableIR",
	},
	recordType {
		tag = constantType "isa",
		variant = "string",
		base = "Assertion",
	},
	recordType {
		tag = constantType "variant",
		variantName = "string",
		base = "Assertion",
		definition = "VariableIR",
	},
	recordType {
		tag = constantType "forall",
		quantified = "Type+",
		location = "Location",

		-- (self, constantName string) => Assertion
		instantiate = "function",
	}
))

-- RETURNS a string (as executable Smol code)
local function assertionExprString(a, grouped)
	assertis(a, "Assertion")
	if a.tag == "int" then
		return tostring(a.value)
	elseif a.tag == "string" then
		return tostring(a.value)
	elseif a.tag == "boolean" then
		return tostring(a.value)
	elseif a.tag == "this" then
		return "this"
	elseif a.tag == "unit" then
		return "unit"
	elseif a.tag == "field" then
		local base = assertionExprString(a.base)
		return base .. "." .. a.fieldName
	elseif a.tag == "method" then
		local base = assertionExprString(a.base, true)
		local arguments = {}
		for _, v in ipairs(a.arguments) do
			table.insert(arguments, assertionExprString(v))
		end

		-- Search for aliasing operator
		local operatorName = table.indexof(common.OPERATOR_ALIAS, a.signature.name)
		if operatorName and #arguments == 1 then
			local inner = base .. " " .. operatorName .. " " .. assertionExprString(a.arguments[1])
			if grouped then
				return "(" .. inner .. ")"
			end
			return inner
		end

		return base .. "." .. a.signature.name .. "(" .. table.concat(arguments, ", ") .. ")"
	elseif a.tag == "static" then
		local arguments = {}
		for _, v in ipairs(a.arguments) do
			table.insert(arguments, assertionExprString(v))
		end
		return a.base .. "." .. a.signature.name .. "(" .. table.concat(arguments, ", ") .. ")"
	elseif a.tag == "variable" then
		local result = variableDescription(a.variable)
		if grouped and result:find "%s" then
			return "(" .. result .. ")"
		end
		return result
	elseif a.tag == "isa" then
		local inner = assertionExprString(a.base, true) .. " is " .. a.variant
		if grouped then
			return "(" .. inner .. ")"
		end
		return inner
	elseif a.tag == "variant" then
		local base = assertionExprString(a.base)
		return base .. "." .. a.variantName
	elseif a.tag == "forall" then
		local inner = excerpt(a.location)
		if grouped then
			return "(" .. inner .. ")"
		end
		return inner
	end

	error("unhandled `" .. a.tag .. "`")
end

-- RETURNS an Assertion representing a && b
local function andAssertion(a, b)
	assertis(a, "Assertion")
	assertis(b, "Assertion")

	local BUILTIN_LOC = {
		begins = "builtin",
		ends = "builtin",
	}

	local p = freeze {
		tag = "method",
		base = a,
		arguments = {b},
		signature = table.findwith(BOOLEAN_DEF.signatures, "name", "and"),
		index = 1,
	}
	assertis(p, "MethodAssertion")
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
		tag = "method",
		base = a,
		arguments = {b},
		signature = table.findwith(BOOLEAN_DEF.signatures, "name", "implies"),
		index = 1,
	}
	assertis(p, "MethodAssertion")
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

	if tag == "unit" or tag == "this" then
		return expression
	elseif tag == "forall" then
		return expression
	elseif tag == "boolean" or tag == "int" or tag == "string" then
		return expression
	elseif tag == "field" or tag == "isa" or tag == "variant" then
		local subBase = assertionReplaced(expression.base, map)
		if subBase == expression.base then
			return expression
		end
		return table.with(expression, "base", subBase)
	elseif tag == "method" then
		-- base + arguments
		local newBase = assertionReplaced(expression.base, map)
		if expression.base ~= newBase then
			expression = table.with(expression, "base", newBase)
		end

		-- Do not return! Fall through for common handling of method/static
	end

	assert(tag == "method" or tag == "static")

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

-- RETURNS a string
local function showStatement(statement, indent)
	-- RETURNS a string representing a list of VariableIR destinations
	local function showDestinations(destinations)
		return table.concat(table.map(table.getter "name", destinations), ", ")
	end

	indent = (indent or "")
	local color = ansi.blue
	if statement.tag == "verify" or statement.tag == "assume" or statement.tag == "proof" then
		color = ansi.red
	elseif statement.tag == "block" then
		color = ansi.gray
	end

	local pre = indent .. color(statement.tag)
	if statement.tag == "block" then
		if #statement.statements == 0 then
			return pre .. " {}"
		end
		local out = pre .. " {\n"
		for _, element in ipairs(statement.statements) do
			out = out .. showStatement(element, indent .. "\t") .. "\n"
		end
		return out .. indent .. "}"
	elseif statement.tag == "proof" then
		return pre .. " {\n" .. showStatement(statement.body, indent .. "\t") .. "\n" .. indent .. "}"
	elseif statement.tag == "assume" then
		return pre .. " " .. statement.variable.name
	elseif statement.tag == "verify" then
		local x = {}
		table.insert(x, pre)
		table.insert(x, " ")
		table.insert(x, statement.variable.name)
		table.insert(x, " // ")
		table.insert(x, show(statement.reason))
		return table.concat(x)
	elseif statement.tag == "local" then
		return pre .. " " .. statement.variable.name .. " " .. showType(statement.variable.type)
	elseif statement.tag == "assign" then
		return pre .. " " .. statement.destination.name .. " := " .. statement.source.name
	elseif statement.tag == "isa" then
		local x = {
			pre .. " ",
			statement.destination.name,
			" := ",
			statement.base.name,
			" is ",
			statement.variant,
		}
		return table.concat(x)
	elseif statement.tag == "method-call" then
		local destinations = showDestinations(statement.destinations)
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = statement.baseInstance.name .. "." .. statement.signature.name .. "(" .. arguments .. ")"
		return pre .. " " .. destinations .. " := " .. rhs
	elseif statement.tag == "static-call" then
		local destinations = showDestinations(statement.destinations)
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = showType(statement.baseType) .. "." .. statement.signature.name .. "(" .. arguments .. ")"
		return pre .. " " .. destinations .. " := " .. rhs
	elseif statement.tag == "generic-method-call" then
		local destinations = showDestinations(statement.destinations)
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = statement.baseInstance.name .. "." .. statement.signature.name .. "(" .. arguments .. ")"
		return pre .. " " .. destinations .. " := " .. rhs
	elseif statement.tag == "return" then
		local out = {}
		for _, s in ipairs(statement.sources) do
			table.insert(out, s.name)
		end
		return pre .. " " .. table.concat(out, ", ")
	elseif statement.tag == "if" then
		local x = {}
		table.insert(x, pre)
		table.insert(x, " ")
		table.insert(x, statement.condition.name)
		table.insert(x, " then\n")
		table.insert(x, showStatement(statement.bodyThen, indent .. "\t"))
		table.insert(x, "\n" .. indent .. "else\n")
		table.insert(x, showStatement(statement.bodyElse, indent .. "\t"))
		return table.concat(x, "")
	elseif statement.tag == "this" then
		return pre .. " " .. statement.destination.name
	elseif statement.tag == "field" then
		local rhs = statement.base.name .. "." .. statement.name
		return pre .. " " .. statement.destination.name .. " := " .. rhs
	elseif statement.tag == "variant" then
		local rhs = statement.base.name .. "." .. statement.variant
		return pre .. " " .. statement.destination.name .. " := " .. rhs
	elseif statement.tag == "new-class" then
		local rhs = {}
		for k, v in spairs(statement.fields) do
			table.insert(rhs, k .. " -> " .. v.name)
		end
		rhs = table.concat(rhs, ", ")
		local t = showType(statement.type)
		return pre .. " " .. statement.destination.name .. " := new " .. t .. "(" .. rhs .. ")"
	elseif statement.tag == "new-union" then
		local rhs = statement.field .. " -> " .. statement.value.name
		local t = showType(statement.type)
		return pre .. " " .. statement.destination.name .. " := new " .. t .. "(" .. rhs .. ")"
	else
		return pre .. " <?>"
	end
end

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
local function uniqueVariable(type, location)
	assertis(type, "Type+")
	assertis(location, "Location")

	uniqueNameID = uniqueNameID + 1

	return freeze {
		location = location,
		type = type,
		name = "__unique" .. uniqueNameID,
		description = false,
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

-- RETURNS an Assertion
-- MODIFIES scope
local snapshotID = 0
local function addSnapshot(scope, assertion, location)
	assertis(scope, listType "Action")
	assertis(assertion, "Assertion")
	assertis(location, "Location")

	snapshotID = snapshotID + 1
	local name = "snapshot'" .. snapshotID
	local variable = freeze {
		type = typeOfAssertion(assertion),
		name = name,
		location = location,
		description = false,
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
		profile.open("action " .. action.tag)
		if action.tag == "assignment" then
			local t = action.destination.type

			local newID = action.destination.name .. "'" .. i .. "'" .. path

			--	.. "'" .. verifyTheory:canonKey(action.value):gsub("[^a-zA-Z0-9]+", "_")
			local newVariable = freeze {
				type = action.destination.type,
				location = action.destination.location,
				name = newID,
				description = action.destination.description,
			}
			local newV = variableAssertion(newVariable)

			-- Record the value of this new assignment at this time
			profile.open("inNow")
			local current = inNow(action.value)
			profile.close("inNow")
			local p = eqAssertion(current, newV, t)

			-- Update the mapping to point to the new variable
			assignments[action.destination.name] = freeze {
				value = newV,
				definition = action.destination,
			}

			--assertis(p, "Assertion")
			table.insert(predicates, p)
		elseif action.tag == "predicate" then
			table.insert(predicates, inNow(action.value))
		elseif action.tag == "branch" then
			-- Learn the facts of both, predicated by condition => ...
			for bi, branch in ipairs(action.branches) do
				profile.open("setup branch")
				local condition = inNow(branch.condition)
				local notCondition = notAssertion(condition)

				local branchAssignments = {}
				for key, value in pairs(assignments) do
					branchAssignments[key] = value
				end
				profile.close("setup branch")

				profile.open("recursive getPredicateSet")
				local branchPredicates = getPredicateSet(
					branch.scope,
					branchAssignments,
					path .. "'" .. bi
				)
				for _, p in ipairs(branchPredicates) do
					table.insert(predicates, impliesAssertion(condition, p))
				end
				profile.close("recursive getPredicateSet")

				profile.open("merge")

				-- Capture modified variables into a select operation
				for variable, newValue in pairs(branchAssignments) do
					local oldValue = assignments[variable]
					if oldValue == nil then
						oldValue = newValue
					elseif newValue.value ~= oldValue.value then
						-- Create new dummy variable
						local id = "merged'" .. variable .. "'" .. path .. "'" .. i
						local merged = variableAssertion(table.with(newValue.definition, "name", id))
						assignments[variable] = freeze {
							value = merged,
							definition = newValue.definition,
						}

						-- Given it old meaning when condition does not hold
						local isOld = eqAssertion(merged, oldValue.value, oldValue.definition.type)
						table.insert(predicates, impliesAssertion(notCondition, isOld))

						-- Give it new meaning when condition does hold
						local isNew = eqAssertion(merged, newValue.value, newValue.definition.type)
						table.insert(predicates, impliesAssertion(condition, isNew))
					end
				end
				profile.close("merge")
			end
		else
			error("unknown action tag `" .. action.tag .. "`")
		end
		profile.close("action " .. action.tag)

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
	profile.open "translating-in-scope"
	local predicates, inNow = getPredicateSet(scope, {}, "")
	profile.close "translating-in-scope"

	assertis(target, "Assertion")
	local result = inNow(target)

	--print("=?=> " .. verifyTheory:canonKey(result))
	local tautology, counter = smt.implies(verifyTheory, predicates, result)

	--print("<-", tautology)

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

-- RETURNS nothing
-- MODIFIES nothing
local function dumpScope(scope)
	assertis(scope, listType "Action")

	for i, v in ipairs(scope) do
		io.write("$ -- " .. i .. "\t")
		if v.tag == "assignment" then
			print(v.destination.name .. " := " .. verifyTheory:canonKey(v.value))
		elseif v.tag == "predicate" then
			print(verifyTheory:canonKey(v.value))
		elseif v.tag == "branch" then
			print("branch TODO")
		else
			error("unknown action tag `" .. v.tag .. "` in dumpScope")
		end
	end
end

-- RETURNS an Assertion
local function resultAssertion(statement, index)
	assertis(statement, "StatementIR")
	statement = freeze(statement)

	if statement.tag == "method-call" or statement.tag == "generic-method-call" then
		assertis(index, "integer")

		return freeze {
			tag = "method",
			base = variableAssertion(statement.baseInstance),
			arguments = table.map(variableAssertion, statement.arguments),

			signature = statement.signature,
			index = index,
		}
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		assertis(index, "integer")

		local base
		if statement.tag == "static-call" then
			base = showType(statement.baseType)
		else
			base = showInterfaceType(statement.constraint.interface)
		end
		return freeze {
			tag = "static",
			base = base,
			arguments = table.map(variableAssertion, statement.arguments),
			signature = statement.signature,
			index = index,
		}
	end
	error("unknown statement tag `" .. statement.tag .. "` in resultAssertion")
end

-- RETURNS an Assertion
local function fieldAssertion(scope, statement)
	assertis(statement, "FieldSt")

	return freeze {
		tag = "field",
		fieldName = statement.name,
		base = variableAssertion(statement.base),
		definition = statement.fieldDefinition,
	}
end

-- RETURNS an Assertion
local function variantAssertion(scope, statement)
	assertis(statement, "VariantSt")

	return freeze {
		tag = "variant",
		variantName = statement.variant,
		base = variableAssertion(statement.base),
		definition = statement.variantDefinition,
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
	elseif statement.tag == "block" then
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
		semantics.classes,
		semantics.interfaces,
		semantics.unions
	)
	allDefinitions = freeze(allDefinitions)

	if statement.tag == "block" then
		for _, sub in ipairs(statement.statements) do
			verifyStatement(sub, scope, semantics)
		end
		return
	elseif statement.tag == "verify" then
		profile.open("verifyStatement verify " .. statement.reason)

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

		profile.close("verifyStatement verify " .. statement.reason)
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
		local assertion = fieldAssertion(scope, statement)
		assignRaw(scope, statement.destination, assertion)
		return
	elseif statement.tag == "variant" then
		-- TODO: verify isa
		local assertion = variantAssertion(scope, statement)
		assignRaw(scope, statement.destination, assertion)
		return
	elseif statement.tag == "int" then
		-- Integer literal
		assignRaw(scope, statement.destination, valueInt(statement.number))
		return
	elseif statement.tag == "string" then
		-- String literal
		assignRaw(scope, statement.destination, valueString(statement.string))
		return
	elseif statement.tag == "boolean" then
		-- Boolean literal
		assignRaw(scope, statement.destination, valueBoolean(statement.boolean))
		return
	elseif statement.tag == "method-call" or statement.tag == "generic-method-call" then
		-- TODO: reject impure
		for i, destination in ipairs(statement.destinations) do
			local source = resultAssertion(statement, i)
			assignRaw(scope, destination, source)
		end
		return
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		-- TODO: reject impure
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

		assertis(statement.type, "ConcreteType+")

		local instance = variableAssertion(uniqueVariable(statement.type, statement.location))
		assignRaw(scope, statement.destination, instance)

		for fieldName, value in pairs(statement.fields) do
			local fieldAssertion = freeze {
				tag = "field",
				base = instance,
				fieldName = fieldName,
				definition = statement.memberDefinitions[fieldName],
			}
			assertis(fieldAssertion, "Assertion")
			assertis(value, "VariableIR")
			local t = value.type
			local eq = eqAssertion(fieldAssertion, variableAssertion(value), t)
			assertis(eq, "Assertion")
			addPredicate(scope, eq)
		end

		return
	elseif statement.tag == "new-union" then
		-- Record the tag
		addPredicate(scope, freeze {
			tag = "isa",
			variant = statement.field,
			base = variableAssertion(statement.destination),
		})

		-- Record the variant contents
		local extract = freeze {
			tag = "variant",
			variantName = statement.field,
			base = variableAssertion(statement.destination),
			definition = statement.variantDefinition,
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
				tag = "isa",
				base = variableAssertion(statement.base),
				variant = case.variant,
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
			conditionAssertion,
			statement.condition.location
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
			tag = "isa",
			base = variableAssertion(statement.base),
			variant = statement.variant,
		})
		return
	elseif statement.tag == "proof" then
		profile.open "verifyStatement proof"
		verifyStatement(statement.body, scope, semantics)
		profile.close "verifyStatement proof"
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
			local inCode, inOut = statement.instantiate(arbitrary)
			verifyStatement(inCode, subscope, semantics)

			-- Discover the newly learned facts in this hypothetical
			local learnedPredicates, inNow = getPredicateSet(subscope, {}, "", #subscopePrime)

			--print()
			--print(string.rep("+ ", 40))
			--print("instantiate with name", name)

			--print()
			--print("facts are")
			local post = {}
			for _, p in ipairs(learnedPredicates) do
				--print("", verifyTheory:canonKey(p))
				table.insert(post, p)
			end

			--print(string.rep("+ ", 40))
			--print()

			-- Return the conjunction
			if #post == 0 then
				return trueBoolean
			end
			local u = post[1]
			for i = 2, #post do
				u = andAssertion(u, post[i])
			end

			assertis(inOut, "VariableIR")
			return u, inNow(variableAssertion(inOut)), arbitrary
		end

		-- Create a forall expression
		assignRaw(scope, statement.destination, freeze {
			tag = "forall",
			quantified = statement.quantified,
			instantiate = instantiate,
			location = statement.location,
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

	--print("== " .. func.name .. " " .. string.rep("=", 80 - 4 - #func.name))
	--print(showStatement(func.body))

	profile.open("verifyFunction " .. func.name)
	verifyStatement(func.body, {}, semantics)
	profile.close("verifyFunction " .. func.name)
end

-- RETURNS nothing
return function(semantics)
	assertis(semantics, "Semantics")

	-- Verify all functions
	for _, func in ipairs(semantics.functions) do
		if func.body then
			verifyFunction(freeze(func), semantics)
		end
	end
end
