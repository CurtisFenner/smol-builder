local calculateSemantics = import "semantics.lua"
local showType = calculateSemantics.showType
local showInterfaceType = calculateSemantics.showInterfaceType

local smt = import "smt.lua"
local verifyTheory = import "verify-theory.lua"

local Report = import "verify-errors.lua"

local profile = import "profile.lua"
local ansi = import "ansi.lua"

--------------------------------------------------------------------------------

local provided = import "provided.lua"

local STRING_TYPE = provided.STRING_TYPE
local INT_TYPE = provided.INT_TYPE
local BOOLEAN_TYPE = provided.BOOLEAN_TYPE
local UNIT_TYPE = provided.UNIT_TYPE
local NEVER_TYPE = provided.NEVER_TYPE

local BUILTIN_DEFINITIONS = provided.BUILTIN_DEFINITIONS

local BOOLEAN_DEF = table.findwith(BUILTIN_DEFINITIONS, "name", "Boolean")

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
	methodName = "string",
	signature = choiceType("Signature", "Signature"),
})

REGISTER_TYPE("FieldAssertion", recordType {
	tag = constantType "field",
	base = "Assertion",
	fieldName = "string",
})

REGISTER_TYPE("Assertion", choiceType(
	recordType {
		tag = constantType "tuple",
		index = "integer",
		value = "Assertion",
	},
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
		staticName = "string",
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
	}
))

local function excerpt(location)
	assertis(location, "Location")

	local begins = location.begins
	local ends = location.ends

	if type(begins) == "string" or type(ends) == "string" then
		-- Internal code
		return "<at " .. begins .. ">"
	end

	local source = begins.sourceLines
	local out = ""
	for line = begins.line, ends.line do
		local low = 1
		local high = #source[line]
		if line == begins.line then
			low = begins.column
		end
		if line == ends.line then
			high = ends.column
		end
		for i = low, high do
			out = out .. source[line]:sub(i, i)
		end
	end
	return out
end

-- RETURNS a string (as executable Smol code)
local function assertionExprString(a, grouped)
	assertis(a, "Assertion")
	if a.tag == "tuple" then
		print("TODO: cannot show tuple expression!")
		return assertionExprString(a.value) .. "[" .. a.index .. "]"
	elseif a.tag == "int" then
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
		local hit = false
		for key, v in pairs(provided.OPERATOR_ALIAS) do
			if v == a.methodName then
				hit = key
			end
		end

		if hit and #arguments == 1 then
			local inner = base .. " " .. hit .. " " .. assertionExprString(a.arguments[1])
			if grouped then
				return "(" .. inner .. ")"
			end
			return inner
		end

		return base .. "." .. a.methodName .. "(" .. table.concat(arguments, ", ") .. ")"
	elseif a.tag == "static" then
		local arguments = {}
		for _, v in ipairs(a.arguments) do
			table.insert(arguments, assertionExprString(v))
		end
		return a.base .. "." .. a.staticName .. "(" .. table.concat(arguments, ", ") .. ")"
	elseif a.tag == "variable" then
		if not a.variable.name:find("['_]") then
			return a.variable.name
		end
		local inner = excerpt(a.variable.location)
		if grouped and inner:find("%s") then
			return "(" .. inner .. ")"
		end
		return inner
	elseif a.tag == "isa" then
		local inner = assertionExprString(a.base, true) .. " is " .. a.variant
		if grouped then
			return "(" .. inner .. ")"
		end
		return inner
	elseif a.tag == "variant" then
		local base = assertionExprString(a.base)
		return base .. "." .. a.variantName
	end
end

local assertionRecursionMap = freeze {
	["static"] = {"arguments{}"},
	["method"] = {"base", "arguments{}"},
	["field"] = {"base"},
	["unit"] = {},
	["this"] = {},
	["boolean"] = {},
	["string"] = {},
	["int"] = {},
	["tuple"] = {"value"},
	["variable"] = {},
	["isa"] = {"base"},
	["variant"] = {"base"},
}

-- RETURNS a Signature for t.eq(t)
local function makeEqSignature(t)
	assertis(t, "Type+")


	if t.name == "Boolean" then
		return table.findwith(BOOLEAN_DEF.signatures, "name", "eq")
	end

	local unknown = freeze {begins = "???", ends = "???"}

	local eqSignature = freeze {
		name = "eq",
		parameters = {
			freeze {name = "left", type = t, location = unknown},
			freeze {name = "right", type = t, location = unknown}
		},
		returnTypes = {BOOLEAN_TYPE},
		modifier = "method",
		container = showType(t),
		bang = false,
		foreign = true,
		ensuresAST = {},
		requiresAST = {},
		logic = false,
		eval = false,
	}

	assertis(eqSignature, "Signature")

	return eqSignature
end

-- RETURNS an Assertion representing the negation of a
local function notAssertion(a)
	assertis(a, "Assertion")

	return freeze {
		tag = "method",
		methodName = "not",
		base = a,
		arguments = {},

		signature = table.findwith(BOOLEAN_DEF.signatures, "name", "not"),
	}
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
		methodName = "implies",
		base = a,
		arguments = {b},
		signature = table.findwith(BOOLEAN_DEF.signatures, "name", "implies")
	}
	assertis(p, "MethodAssertion")
	return p
end

-- RETURNS an Assertion
local function assertionReplaced(expression, variable, with)
	assertis(expression, "Assertion")
	assertis(variable, "string")
	assertis(with, "Assertion")

	if expression.tag == "variable" then
		if expression.variable.name == variable then
			return with
		end
	end

	assert(assertionRecursionMap[expression.tag])
	local copy = {}
	for key, value in pairs(expression) do
		copy[key] = value
	end
	for _, key in ipairs(assertionRecursionMap[expression.tag]) do
		if key:sub(-2) == "{}" then
			local pre = key:sub(1, -3)
			local m = {}
			for k, v in pairs(copy[pre]) do
				m[k] = assertionReplaced(v, variable, with)
			end
			copy[pre] = m
		else
			copy[key] = assertionReplaced(copy[key], variable, with)
		end
	end
	return freeze(copy)
end

--------------------------------------------------------------------------------

-- RETURNS a string
local function showStatement(statement, indent)
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
		local destinations = table.concat(table.map(table.getter "name", statement.destinations), ", ")
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = statement.baseInstance.name .. "." .. statement.methodName .. "(" .. arguments .. ")"
		return pre .. " " .. destinations.. " := " .. rhs
	elseif statement.tag == "static-call" then
		local destinations = table.concat(table.map(table.getter "name", statement.destinations), ", ")
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = showType(statement.baseType) .. "." .. statement.staticName .. "(" .. arguments .. ")"
		return pre .. " " .. destinations.. " := " .. rhs
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
	else
		return pre .. " <?>"
	end
end

-- RETURNS an Assertion
local function tupleAccess(value, index)
	assertis(value, "Assertion")
	assertis(index, "integer")

	return freeze {
		tag = "tuple",
		index = index,
		value = value,
	}
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

-- RETURNS an Assertion
local function variableAssertion(variable)
	assertis(variable, "VariableIR")

	return freeze {
		tag = "variable",
		variable = variable,
	}
end

local uniqueNameID = 1000
local function uniqueVariable(type)
	assertis(type, "Type+")
	uniqueNameID = uniqueNameID + 1

	return freeze {
		location = freeze {
			begins = "???",
			ends = "???",
		},
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

local function eqAssertion(a, b, t)
	assertis(a, "Assertion")
	assertis(b, "Assertion")
	assertis(t, "Type+")

	local p = freeze {
		tag = "method",
		methodName = "eq",
		base = a,
		arguments = {b},
		signature = makeEqSignature(t),
	}
	assertis(p, "MethodAssertion")
	return p
end

-- RETURNS a list of true Assertion predicates, inNow
-- path: a string used to generate unique names
local function getPredicateSet(scope, assignments, path)
	assertis(scope, listType "Action")
	assertis(assignments, mapType("string", recordType{
		value = "Assertion",
		definition = "VariableIR",
	}))
	assertis(path, "string")

	-- TODO: come up with something that deals with loops
	local predicates = {}

	-- RETURNS an Assertion
	local function inNow(a)
		assertis(a, "Assertion")
		for variable, replacement in pairs(assignments) do
			assertis(replacement, recordType {
				value = "Assertion",
				definition = "VariableIR",
			})
			a = assertionReplaced(a, variable, replacement.value)
		end
		return a
	end
	-- Translate assignments as a substitution in all subsequent predicates
	for i, action in ipairs(scope) do
		if action.tag == "assignment" then
			local t = action.destination.type

			local newID = action.destination.name .. "'" .. i .. "'" .. path
				.. "'" .. verifyTheory:canonKey(action.value):gsub("[^a-zA-Z0-9]+", "_")
			local newV = variableAssertion(table.with(action.destination, "name", newID))
			
			-- Record the value of this new assignment at this time
			local p = eqAssertion(inNow(action.value), newV, t)

			-- Update the mapping to point to the new variable
			assignments[action.destination.name] = freeze {
				value = newV,
				definition = action.destination,
			}

			assertis(p, "Assertion")
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

				local branchPredicates = getPredicateSet(branch.scope, branchAssignments, path .. "'" .. bi)
				for _, p in ipairs(branchPredicates) do
					table.insert(predicates, impliesAssertion(condition, p))
				end

				-- Capture modified variables into a select operation
				for variable, newValue in pairs(branchAssignments) do
					local oldValue = assignments[variable]
					if oldValue == nil then
						oldValue = newValue
					elseif newValue.value ~= oldValue.value then
						-- Create new dummy variable
						local id = "merged'" .. variable .. "'" .. path .. "'" .. i
						local merged = variableAssertion(
							table.with(newValue.definition, "name", id)
						)
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
			end
		else
			error("unknown action tag `" .. action.tag .. "`")
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

	--print("\n\n\n\n")
	--for i, p in ipairs(predicates) do
	--	print("& " .. verifyTheory:canonKey(p))
	--end

	assertis(target, "Assertion")
	local result = inNow(target)
	--print("=?=> " .. verifyTheory:canonKey(result))
	local tautology, counter = smt.implies(verifyTheory, predicates, result)
	--print("<-", tautology)

	if not tautology then
		local explanation = {}
		for assertion, truth in pairs(counter) do
			local shown = assertionExprString(assertion)
			--.. "\t" .. verifyTheory:canonKey(assertion)
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
local function resultAssertion(statement)
	assertis(statement, "StatementIR")
	statement = freeze(statement)

	if statement.tag == "method-call" or statement.tag == "generic-method-call" then
		return freeze {
			tag = "method",
			base = variableAssertion(statement.baseInstance),
			methodName = statement.methodName,
			arguments = table.map(variableAssertion, statement.arguments),

			signature = statement.signature,
		}
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		local base
		if statement.tag == "static-call" then
			base = showType(statement.baseType)
		else
			base = showInterfaceType(statement.constraint.interface)
		end
		return freeze {
			tag = "static",
			base = base,
			staticName = statement.staticName,
			arguments = table.map(variableAssertion, statement.arguments),
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
	}
end

-- RETURNS an Assertion
local function variantAssertion(scope, statement)
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

-- RETURNS a assertion representing the disjunction of all facts given in each
-- list
local function scopeDisjunction(a, b)
	assertis(a, listType "Action")
	assertis(b, listType "Action")

	error "TODO!"
end

-- MODIFIES scope
-- RETURNS nothing
local function verifyStatement(statement, scope, semantics)
	assertis(statement, "StatementIR")
	assertis(scope, listType "Action")
	assertis(semantics, "Semantics")

	local allDefinitions = table.concatted(
		semantics.classes, semantics.interfaces, semantics.unions
	)
	allDefinitions = freeze(allDefinitions)

	if statement.tag == "block" then
		for _, sub in ipairs(statement.statements) do
			verifyStatement(sub, scope, semantics)
		end
		return
	elseif statement.tag == "verify" then
		-- Check that this variable is true in the current scope
		local models, counter = mustModel(scope, variableAssertion(statement.variable))
		if not models then
			--print("$ !!!", models)
			--dumpScope(scope)
			--print("$ =/=>", verifyTheory:canonKey(variableAssertion(statement.variable)))
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
		assignRaw(scope, statement.destination, VALUE_THIS)
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
		local source = resultAssertion(statement)
		for i, destination in ipairs(statement.destinations) do
			if #statement.destinations > 1 then
				source = tupleAccess(source, i)
			end
			assignRaw(scope, destination, source)
		end
		return
	elseif statement.tag == "static-call" or statement.tag == "generic-static-call" then
		-- TODO: reject impure
		local source = resultAssertion(statement)
		for i, destination in ipairs(statement.destinations) do
			if #statement.destinations > 1 then
				source = tupleAccess(source, i)
			end
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

		local instance = variableAssertion(uniqueVariable(statement.type))
		assignRaw(scope, statement.destination, instance)

		for fieldName, value in pairs(statement.fields) do
			local fieldAssertion = freeze {
				tag = "field",
				base = instance,
				fieldName = fieldName,
			}
			assertis(value, "VariableIR")
			local eq = freeze {
				tag = "method",
				base = fieldAssertion,
				arguments = {variableAssertion(value)},
				methodName = "eq",
				signature = makeEqSignature(value.type),
			}
			assertis(eq, "MethodAssertion")
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
		}
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
		for _, case in ipairs(statement.cases) do
			local subscope = scopeCopy(scope)

			local condition = freeze {
				tag = "isa",
				base = variableAssertion(statement.base),
				variant = case.variant,
			}

			-- Add variant predicate
			addPredicate(subscope, condition)
			verifyStatement(case.statement, subscope, semantics)
			
			if case.statement.returns ~= "yes" then
				table.insert(branches, {
					scope = subscope,
					condition = condition,
				})
			end
		end

		if #branches == 0 then
			-- The code after this is unreachable, so the scope is irrelevant
			assert(statement.returns == "yes")
			return
		end

		-- Learn the disjunction of the new statements
		addMerge(scope, branches)
		return
	elseif statement.tag == "if" then
		local conditionAssertion = variableAssertion(statement.condition)

		-- Evaluate the then body with condition given
		local thenScope = scopeCopy(scope)
		addPredicate(thenScope, conditionAssertion)
		verifyStatement(statement.bodyThen, thenScope, semantics)

		-- Evaluate the else body with negation of the condtion given
		local elseScope = scopeCopy(scope)
		addPredicate(elseScope, notAssertion(conditionAssertion))
		verifyStatement(statement.bodyElse, elseScope, semantics)

		-- Learn the disjunction of new statements
		local branches = {}
		if statement.bodyThen.returns ~= "yes" then
			local newThen = scopeAdditional(scope, thenScope)
			table.insert(branches, {
				scope = newThen,
				condition = conditionAssertion
			})
		end
		if statement.bodyElse.returns ~= "yes" then
			local newElse = scopeAdditional(scope, elseScope)
			table.insert(branches, {
				scope = newElse,
				condition = notAssertion(conditionAssertion)
			})
		end

		if #branches == 0 then
			-- No code follows here
			assert(statement.returns == "yes")
			return
		end

		addMerge(scope, branches)
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
		verifyStatement(statement.body, scope, semantics)
		return
	end

	error("unhandled statement `" .. statement.tag .. "`")
end

-- RETURNS nothing
local function verifyFunction(func, semantics)
	assertis(func, "FunctionIR")
	assertis(semantics, "Semantics")
	assert(func.body)

	print("== " .. func.name .. " " .. string.rep("=", 80 - 4 - #func.name))
	print(showStatement(func.body))

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
