-- common.lua contains functions in common to many files (semantics, codegen,
-- verification)

local tokenization = import "tokenization.lua"
local syntax = import "syntax.lua"

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
	tag = "keyword-type+",
	name = "String",
	location = {begins = "???", ends = "???"},
}

local INT_TYPE = freeze {
	tag = "keyword-type+",
	name = "Int",
	location = {begins = "???", ends = "???"},
}

local BOOLEAN_TYPE = freeze {
	tag = "keyword-type+",
	name = "Boolean",
	location = {begins = "???", ends = "???"},
}

local UNIT_TYPE = freeze {
	tag = "keyword-type+",
	name = "Unit",
	location = {begins = "???", ends = "???"},
}

local NEVER_TYPE = freeze {
	tag = "keyword-type+",
	name = "Never",
	location = {begins = "???", ends = "???"},
}

-- TODO: This is not a real type!
local SYMBOL_TYPE = freeze {
	tag = "keyword-type+",
	name = "_Symbol",
	location = {begins = "???", ends = "???"},
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

local INT_DEF = freeze {
	type = INT_TYPE,
	name = "Int",
	tag = "builtin",
	signatures = {
		{
			memberName = "isPositive",
			longName = "Int:isPositive",

			parameters = {},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = false,
			eval = function(n)
				return n > 0
			end,
		},
		{
			memberName = "negate",
			longName = "Int:negate",

			parameters = {},
			returnTypes = {INT_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = false,
			eval = function(n)
				return -n
			end,
		},
		{
			memberName = "lessThan",
			longName = "Int:lessThan",

			parameters = {dummy("right", INT_TYPE)},
			returnTypes = {BOOLEAN_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {
				-- Transitive
				parseKind("ensures forall (middle Int) return when (this < middle).and(middle < right)", "ensures"),

				-- Antireflexive
				parseKind("ensures return.not() when this == right", "ensures"),

				-- Antisymmetric
				parseKind("ensures return.not() when right < this", "ensures"),
			},
			requiresAST = {},
			logic = false,
			eval = function(a, b)
				return a < b
			end,
		},
		{
			memberName = "eq",
			longName = "Int:eq",

			parameters = {dummy("right", INT_TYPE)},
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
		},
		{
			memberName = "quotient",
			longName = "Int:quotient",

			parameters = {dummy("right", INT_TYPE)},
			returnTypes = {INT_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = false,
			eval = function(a, b)
				return math.floor(a / b)
			end,
		},
		{
			memberName = "product",
			longName = "Int:product",

			parameters = {dummy("right", INT_TYPE)},
			returnTypes = {INT_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = false,
			eval = function(a, b)
				return a * b
			end,
		},
		{
			memberName = "sum",
			longName = "Int:sum",

			parameters = {dummy("right", INT_TYPE)},
			returnTypes = {INT_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {
				parseKind("ensures this < return when 0 < right", "ensures"),
			},
			requiresAST = {},
			logic = false,
			eval = function(a, b)
				return a + b
			end,
		},
		{
			memberName = "difference",
			longName = "Int:difference",

			parameters = {dummy("right", INT_TYPE)},
			returnTypes = {INT_TYPE},
			modifier = "method",
			foreign = true,
			bang = false,
			ensuresAST = {},
			requiresAST = {},
			logic = false,
			eval = function(a, b)
				return a - b
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
	INT_DEF,
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

return freeze {
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
}
