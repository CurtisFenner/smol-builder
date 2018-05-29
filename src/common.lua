-- common.lua contains functions in common to many files (semantics, codegen,
-- verification)

local tokenization = import "tokenization.lua"
local syntax = import "syntax.lua"
local ansi = import "ansi.lua"

-- RETURNS a parse object, or quits with a syntax error
local function parseKind(s, k)
	local tokens = tokenization(s, "<compiler-core>")
	return syntax.parseKind(tokens, k)
end

-- RETURNS a string containing the contents of the source code within this
-- Location
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
		out = out .. source[line]:sub(low, high)
	end
	return out
end

local function locationBrief(location)
	assertis(location, "Location")

	local begins, ends = location.begins, location.ends
	if type(begins) == "string" or type(ends) == "string" then
		-- Internal code
		return "<at " .. begins .. ">"
	end

	return begins.filename .. ":" .. begins.line .. ":" .. begins.column
end

-- RETURNS a string representing the variable
local function variableDescription(variable)
	assertis(variable, "VariableIR")

	if variable.description then
		return variable.description
	end

	-- TODO: eliminate type
	return excerpt(variable.location)
end

-- RETURNS whether or not a and b are the same type
-- REQUIRES that type names cannot be shadowed and
-- that a and b come from the same (type) scope
local function areTypesEqual(a, b)
	assertis(a, "Type+")
	assertis(b, "Type+")

	if a.tag ~= b.tag then
		return false
	elseif a.tag == "concrete-type+" then
		if a.name ~= b.name then
			return false
		elseif #a.arguments ~= #b.arguments then
			-- XXX: should this be fixed before here?
			return false
		end
		for k in ipairs(a.arguments) do
			if not areTypesEqual(a.arguments[k], b.arguments[k]) then
				return false
			end
		end
		return true
	elseif a.tag == "keyword-type+" then
		return a.name == b.name
	elseif a.tag == "generic+" then
		return a.name == b.name
	end
	error("unknown type tag `" .. a.tag .. "`")
end

-- RETURNS whether or not a and b are the same interface
-- REQUIRES that type names cannot be shadowed and
-- that a and b come from the same (type) scope
local function areInterfaceTypesEqual(a, b)
	assertis(a, "InterfaceType+")
	assertis(b, "InterfaceType+")

	if a.name ~= b.name then
		return false
	end
	assert(#a.arguments == #b.arguments)

	for k in ipairs(a.arguments) do
		if not areTypesEqual(a.arguments[k], b.arguments[k]) then
			return false
		end
	end

	return true
end

--------------------------------------------------------------------------------

local STRING_TYPE = freeze {
	tag = "keyword-type",
	role = "type",
	name = "String",
}

local INT_TYPE = freeze {
	tag = "keyword-type",
	role = "type",
	name = "Int",
}

local BOOLEAN_TYPE = freeze {
	tag = "keyword-type",
	role = "type",
	name = "Boolean",
}

local UNIT_TYPE = freeze {
	tag = "keyword-type",
	role = "type",
	name = "Unit",
}

local NEVER_TYPE = freeze {
	tag = "keyword-type",
	role = "type",
	name = "Never",
}

-- TODO: This is not a real type!
local SYMBOL_TYPE = freeze {
	tag = "keyword-type",
	role = "type",
	name = "_Symbol",
}

--------------------------------------------------------------------------------

local OPERATOR_ALIAS = {
	["=="] = "eq",
	["/"] = "quotient",
	["*"] = "product",
	["+"] = "sum",
	["-"] = "difference",
	["<"] = "lessThan",
	["++"] = "concatenate",
	["=>"] = "implies",
	["&&"] = "and",
}

--------------------------------------------------------------------------------

local BUILTIN_LOC = freeze {
	begins = "builtin",
	ends = "builtin",
}

local function dummy(name, type)
	return freeze {
		name = name,
		type = type,
		location = BUILTIN_LOC,
		description = false,
	}
end

local BOOLEAN_DEF = freeze {
	type = BOOLEAN_TYPE,
	name = "Boolean",
	tag = "builtin",
	signatures = {
		{
			memberName = "eq",
			longName = "Boolean:eq",

			parameters = {dummy("other", BOOLEAN_TYPE)},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = {
				[true] = {{true, true}, {false, false}},
				[false] = {{true, false}, {false, true}},
			},
			eval = function(a, b)
				return a == b
			end,
		},
		{
			memberName = "and",
			longName = "Boolean:and",

			parameters = {dummy("right", BOOLEAN_TYPE)},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = {
				[true] = {{true, true}},
				[false] = {{false, false}, {false, true}, {true, false}},
			},
			eval = function(a, b)
				return a and b
			end,
		},
		{
			memberName = "or",
			longName = "Boolean:or",

			parameters = {dummy("right", BOOLEAN_TYPE)},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = {
				[true] = {{true, "*"}, {false, true}},
				[false] = {{false, false}},
			},
			eval = function(a, b)
				return a or b
			end,
		},
		{
			memberName = "implies",
			longName = "Boolean:implies",

			parameters = {dummy("right", BOOLEAN_TYPE)},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = {
				[true] = {{false, "*"}, {true, true}},
				[false] = {{true, false}},
			},
			eval = function(a, b)
				return not a or b
			end,
		},
		{
			memberName = "not",
			longName = "Boolean:not",

			parameters = {},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = {
				[true] = {{false}},
				[false] = {{true}},
			},
			eval = function(a)
				return not a
			end,
		},
	},
}

local BUILTIN_DEFINITIONS = freeze {
	{
		type = STRING_TYPE,
		name = "String",
		tag = "builtin",
		signatures = {
			{
				memberName = "concatenate",
				longName = "String:concatenate",

				parameters = {dummy("right", STRING_TYPE)},
				returnTypes = {STRING_TYPE},
				modifier = "method",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b)
					return a .. b
				end,
			},
			{
				memberName = "eq",
				longName = "String:eq",

				parameters = {dummy("right", STRING_TYPE)},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b)
					return a == b
				end,
			}
		},
	},
	BOOLEAN_DEF,
	{
		type = UNIT_TYPE,
		name = "Unit",
		tag = "builtin",
		signatures = {},
	},
	{
		type = NEVER_TYPE,
		name = "Never",
		tag = "builtin",
		signatures = {},
	}
}

--------------------------------------------------------------------------------

-- RETURNS a string of smol representing the given type
local function showType(t)
	assertis(t, "Type+")

	if t.tag == "concrete-type+" then
		if #t.arguments == 0 then
			return t.name
		end
		local arguments = table.map(showType, t.arguments)
		return t.name .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif t.tag == "keyword-type+" then
		return t.name
	elseif t.tag == "generic+" then
		return "#" .. t.name
	end
	error("unknown Type+ tag `" .. t.tag .. "`")
end

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
	elseif a.tag == "fn" then
		local arguments = {}
		for _, v in ipairs(a.arguments) do
			table.insert(arguments, assertionExprString(v))
		end
		if a.signature.modifier == "method" then
			local base = table.remove(arguments, 1)
			return base .. "." .. a.signature.memberName .. "(" .. table.concat(arguments, ", ") .. ")"
		else
			return a.signature.longName .. "(" .. table.concat(arguments, ", ") .. ")"
		end
	elseif a.tag == "variable" then
		local result = variableDescription(a.variable)
		if grouped and result:find "%s" then
			return "(" .. result .. ")"
		end
		return result
	elseif a.tag == "variant" then
		local base = assertionExprString(a.base)
		return base .. "." .. a.variantName
	elseif a.tag == "forall" then
		local inner = excerpt(a.location)
		if grouped then
			return "(" .. inner .. ")"
		end
		return inner
	elseif a.tag == "eq" then
		local i = assertionExprString(a.left) .. " == " .. assertionExprString(a.right)
		if grouped then
			return "(" .. i .. ")"
		end
		return i
	elseif a.tag == "gettag" then
		-- TODO: fix this
		return "$tag(" .. assertionExprString(a.base) .. ")"
	elseif a.tag == "symbol" then
		return "$symbol(" .. a.symbol .. ")"
	end

	error("unhandled `" .. a.tag .. "`")
end

--------------------------------------------------------------------------------

-- RETURNS a Type+
local function typeOfAssertion(assertion)
	assertis(assertion, "Assertion")

	if assertion.tag == "int" then
		return INT_TYPE
	elseif assertion.tag == "string" then
		return STRING_TYPE
	elseif assertion.tag == "boolean" then
		return BOOLEAN_TYPE
	elseif assertion.tag == "this" then
		return assertion.type
	elseif assertion.tag == "unit" then
		return UNIT_TYPE
	elseif assertion.tag == "fn" then
		return assertion.signature.returnTypes[assertion.index]
	elseif assertion.tag == "field" then
		return assertion.definition.type
	elseif assertion.tag == "variable" then
		return assertion.variable.type
	elseif assertion.tag == "isa" then
		return BOOLEAN_TYPE
	elseif assertion.tag == "variant" then
		return assertion.definition.type
	elseif assertion.tag == "forall" then
		return BOOLEAN_TYPE
	elseif assertion.tag == "symbol" then
		return SYMBOL_TYPE
	elseif assertion.tag == "gettag" then
		return SYMBOL_TYPE
	elseif assertion.tag == "eq" then
		return BOOLEAN_TYPE
	end

	error("unhandled tag " .. assertion.tag)
end

--------------------------------------------------------------------------------

-- RETURNS a string
-- DEBUG USE ONLY
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
		local rhs = statement.baseInstance.name .. "." .. statement.signature.memberName .. "(" .. arguments .. ")"
		return pre .. " " .. destinations .. " := " .. rhs
	elseif statement.tag == "static-call" then
		local destinations = showDestinations(statement.destinations)
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = statement.signature.longName .. "(" .. arguments .. ")"
		return pre .. " " .. destinations .. " := " .. rhs
	elseif statement.tag == "generic-method-call" then
		local destinations = showDestinations(statement.destinations)
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = statement.baseInstance.name .. "." .. statement.signature.memberName .. "(" .. arguments .. ")"
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

--------------------------------------------------------------------------------

local function simpleSignature(container, modifier, name, from, to, eval)
	local ps = {}
	for i, t in ipairs(from) do
		table.insert(ps, {
			type = t,
			name = "arg" .. tostring(i),
		})
	end

	return {
		longName = container .. ":" .. name,
		memberName = name,
		returnTypes = to,
		modifier = modifier,
		parameters = ps,
		foreign = true,
		bang = false,
		requiresASTs = {},
		ensuresASTs = {},
		logic = false,
		eval = eval,
	}
end

return {
	STRING_TYPE = STRING_TYPE,
	INT_TYPE = INT_TYPE,
	BOOLEAN_TYPE = BOOLEAN_TYPE,
	UNIT_TYPE = UNIT_TYPE,
	NEVER_TYPE = NEVER_TYPE,
	BUILTIN_DEFINITIONS = BUILTIN_DEFINITIONS,
	OPERATOR_ALIAS = OPERATOR_ALIAS,

	-- Helpers
	areTypesEqual = areTypesEqual,
	areInterfaceTypesEqual = areInterfaceTypesEqual,
	assertionExprString = assertionExprString,
	showType = showType,

	typeOfAssertion = typeOfAssertion,

	excerpt = excerpt,
	locationBrief = locationBrief,
	variableDescription = variableDescription,

	showStatement = showStatement,

	builtinDefinitions = {
		Int = {
			tag = "class-definition",

			-- Functions
			functionMap = {
				-- method isPositive() Boolean
				isPositive = {
					signature = simpleSignature("Int", "method", "isPositive", {INT_TYPE}, {BOOLEAN_TYPE}, function(n)
						return 0 < n
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method negate() Int
				negate = {
					signature = simpleSignature("Int", "method", "negate", {INT_TYPE}, {INT_TYPE}, function(n)
						return -n
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method lessThan(Int) Boolean
				lessThan = {
					-- TODO: Add ensures/requires
					signature = simpleSignature("Int", "method", "lessThan", {INT_TYPE, INT_TYPE}, {BOOLEAN_TYPE}, function(a, b)
						return a < b
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method eq(Int) Boolean
				eq = {
					signature = simpleSignature("Int", "method", "eq", {INT_TYPE, INT_TYPE}, {BOOLEAN_TYPE}, function(a, b)
						return a == b
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method quotient(Int) Int
				quotient = {
					signature = simpleSignature("Int", "method", "quotient", {INT_TYPE, INT_TYPE}, {INT_TYPE}, function(a, b)
						return math.floor(a / b)
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method product(Int) Int
				product = {
					signature = simpleSignature("Int", "method", "product", {INT_TYPE, INT_TYPE}, {INT_TYPE}, function(a, b)
						return a * b
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method sum(Int) Int
				-- TODO: ordered field axiom
				sum = {
					signature = simpleSignature("Int", "method", "sum", {INT_TYPE, INT_TYPE}, {INT_TYPE}, function(a, b)
						return a + b
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},

				-- method difference(Int) Int
				difference = {
					signature = simpleSignature("Int", "method", "difference", {INT_TYPE, INT_TYPE}, {INT_TYPE}, function(a, b)
						return a - b
					end),
					bodyAST = false,
					definitionLocation = BUILTIN_LOC,
				},
			},

			-- No fields
			fieldMap = {},

			-- Int type
			kind = {
				tag = "keyword-type",
				role = "type",
				name = "Int",
			},
		}
	}
}
