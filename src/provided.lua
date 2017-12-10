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

--------------------------------------------------------------------------------

local OPERATOR_ALIAS = {
	["=="] = "eq",
	["/"] = "quotient",
	["*"] = "product",
	["+"] = "sum",
	["-"] = "difference",
	["<"] = "lessThan",
	["++"] = "concatenate",
}

--------------------------------------------------------------------------------

local BUILTIN_LOC = {
	begins = "builtin",
	ends = "builtin",
}

local BUILTIN_DEFINITIONS = freeze {
	{
		type = INT_TYPE,
		name = "Int",
		tag = "builtin",
		signatures = {
			{
				name = "isPositive",
				parameters = {},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(n) return n > 0 end,
			},
			{
				name = "negate",
				parameters = {},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(n) return -n end,
			},
			{
				name = "lessThan",
				parameters = {{location = BUILTIN_LOC, name = "one", type = INT_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a < b end,
			},
			{
				name = "eq",
				parameters = {{location = BUILTIN_LOC, name = "other", type = INT_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a == b end,
			},
			{
				name = "quotient",
				parameters = {{location = BUILTIN_LOC, name = "other", type = INT_TYPE}},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return math.floor(a / b) end,
			},
			{
				name = "product",
				parameters = {{location = BUILTIN_LOC, name = "other", type = INT_TYPE}},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a * b end,
			},
			{
				name = "sum",
				parameters = {{location = BUILTIN_LOC, name = "other", type = INT_TYPE}},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a + b end,
			},
			{
				name = "difference",
				parameters = {{location = BUILTIN_LOC, name = "other", type = INT_TYPE}},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a - b end,
			},
		},
	},
	{
		type = STRING_TYPE,
		name = "String",
		tag = "builtin",
		signatures = {
			{
				name = "concatenate",
				parameters = {{location = BUILTIN_LOC, name = "other", type = STRING_TYPE}},
				returnTypes = {STRING_TYPE},
				modifier = "method",
				container = "String",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a .. b end,
			},
			{
				name = "eq",
				parameters = {{location = BUILTIN_LOC, name = "other", type = STRING_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "String",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b) return a == b end,
			}
		},
	},
	{
		type = BOOLEAN_TYPE,
		name = "Boolean",
		tag = "builtin",
		signatures = {
			{
				name = "eq",
				parameters = {{location = BUILTIN_LOC, name = "other", type = BOOLEAN_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Boolean",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = {
					[true] = {{true, true}, {false, false}},
					[false] = {{true, false}, {false, true}},
				},
				eval = function(a, b) return a == b end,
			},
			{
				name = "and",
				parameters = {{location = BUILTIN_LOC, name = "right", type = BOOLEAN_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Boolean",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = {
					[true] = {{true, true}},
					[false] = {{false, false}, {false, true}, {true, false}},
				},
				eval = function(a, b) return a and b end,
			},
			{
				name = "or",
				parameters = {{location = BUILTIN_LOC, name = "right", type = BOOLEAN_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Boolean",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = {
					[true] = {{true, "*"}, {false, true}},
					[false] = {{false, false}},
				},
				eval = function(a, b) return a or b end,
			},
			{
				name = "implies",
				parameters = {{location = BUILTIN_LOC, name = "right", type = BOOLEAN_TYPE}},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Boolean",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = {
					[true] = {{false, "*"}, {true, true}},
					[false] = {{true, false}},
				},
				eval = function(a, b) return not a or b end,
			},
			{
				name = "not",
				parameters = {},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Boolean",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = {
					[true] = {{false}},
					[false] = {{true}},
				},
				eval = function(a) return not a end,
			},
		},
	},
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

return freeze {
	STRING_TYPE = STRING_TYPE,
	INT_TYPE = INT_TYPE,
	BOOLEAN_TYPE = BOOLEAN_TYPE,
	UNIT_TYPE = UNIT_TYPE,
	NEVER_TYPE = NEVER_TYPE,
	BUILTIN_DEFINITIONS = BUILTIN_DEFINITIONS,
	OPERATOR_ALIAS = OPERATOR_ALIAS,
}
