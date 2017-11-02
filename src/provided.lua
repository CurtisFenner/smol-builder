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

return freeze {
	STRING_TYPE = STRING_TYPE,
	INT_TYPE = INT_TYPE,
	BOOLEAN_TYPE = BOOLEAN_TYPE,
	UNIT_TYPE = UNIT_TYPE,
	NEVER_TYPE = NEVER_TYPE,
}
