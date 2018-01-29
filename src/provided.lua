-- provided.lua contains functions in common to many files (semantics, codegen,
-- verification)

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
			name = "eq",
			parameters = {dummy("other", BOOLEAN_TYPE)},
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
			eval = function(a, b)
				return a == b
			end,
		},
		{
			name = "and",
			parameters = {dummy("right", BOOLEAN_TYPE)},
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
			eval = function(a, b)
				return a and b
			end,
		},
		{
			name = "or",
			parameters = {dummy("right", BOOLEAN_TYPE)},
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
			eval = function(a, b)
				return a or b
			end,
		},
		{
			name = "implies",
			parameters = {dummy("right", BOOLEAN_TYPE)},
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
			eval = function(a, b)
				return not a or b
			end,
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
			eval = function(a)
				return not a
			end,
		},
	},
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
				eval = function(n)
					return n > 0
				end,
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
				eval = function(n)
					return -n
				end,
			},
			{
				name = "lessThan",
				parameters = {dummy("right", INT_TYPE)},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b)
					return a < b
				end,
			},
			{
				name = "eq",
				parameters = {dummy("right", INT_TYPE)},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "Int",
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
				name = "quotient",
				parameters = {dummy("right", INT_TYPE)},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
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
				name = "product",
				parameters = {dummy("right", INT_TYPE)},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
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
				name = "sum",
				parameters = {dummy("right", INT_TYPE)},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
				foreign = true,
				bang = false,
				ensuresAST = {},
				requiresAST = {},
				logic = false,
				eval = function(a, b)
					return a + b
				end,
			},
			{
				name = "difference",
				parameters = {dummy("right", INT_TYPE)},
				returnTypes = {INT_TYPE},
				modifier = "method",
				container = "Int",
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
	},
	{
		type = STRING_TYPE,
		name = "String",
		tag = "builtin",
		signatures = {
			{
				name = "concatenate",
				parameters = {dummy("right", STRING_TYPE)},
				returnTypes = {STRING_TYPE},
				modifier = "method",
				container = "String",
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
				name = "eq",
				parameters = {dummy("right", STRING_TYPE)},
				returnTypes = {BOOLEAN_TYPE},
				modifier = "method",
				container = "String",
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

--------------------------------------------------------------------------------

-- RETURNS a Signature for t.eq(t)
local function makeEqSignature(t)
	assertis(t, "Type+")

	if t.name == "Boolean" then
		return table.findwith(BOOLEAN_DEF.signatures, "name", "eq")
	end

	local unknown = freeze {begins = "???", ends = "???"}

	local eqSignature = freeze {
		name = "eq",
		parameters = {dummy("left", t), dummy("right", t)},
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
	elseif assertion.tag == "method" then
		return assertion.signature.returnTypes[assertion.index]
	elseif assertion.tag == "field" then
		return assertion.definition.type
	elseif assertion.tag == "static" then
		return assertion.signature.returnTypes[assertion.index]
	elseif assertion.tag == "variable" then
		return assertion.variable.type
	elseif assertion.tag == "isa" then
		return BOOLEAN_TYPE
	elseif assertion.tag == "variant" then
		return assertion.definition.type
	elseif assertion.tag == "forall" then
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
	showType = showType,
	makeEqSignature = makeEqSignature,

	typeOfAssertion = typeOfAssertion,
}
