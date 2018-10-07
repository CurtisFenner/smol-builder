-- common.lua contains functions in common to many files (semantics, codegen,
-- verification)

local tokenization = import "tokenization.lua"
local syntax = import "syntax.lua"
local ansi = import "ansi.lua"

--------------------------------------------------------------------------------

-- RETURNS a parse object, or quits with a syntax error
local function parseKind(s, k)
	local tokens = tokenization(s, "<compiler-core>")
	return syntax.parseKind(tokens, k)
end

--------------------------------------------------------------------------------

local STRING_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "String",
}

local INT_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Int",
}

local BOOLEAN_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Boolean",
}

local UNIT_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Unit",
}

local NEVER_TYPE = {
	tag = "keyword-type",
	role = "type",
	name = "Never",
}

-- TODO: This is not a real Smol type!
local SYMBOL_TYPE = {
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

local function simpleSignature(container, modifier, name, from, to, extra)
	local ps = {}
	for i, t in ipairs(from) do
		table.insert(ps, {
			type = t,
			name = "arg" .. tostring(i),
		})
	end

	if modifier == "method" then
		ps[1].name = "this"
	end

	return {
		longName = container .. ":" .. name,
		memberName = name,
		returnTypes = to,
		modifier = modifier,
		parameters = ps,
		foreign = true,
		bang = false,
		requiresASTs = extra.requiresASTs or {},
		ensuresASTs = extra.ensuresASTs or {},
		logic = false,
		eval = extra.eval or false,
	}
end

local function p(name, t)
	return {
		name = name,
		type = t,
	}
end

-- RETURNS a fake location
local function fakeLocation()
	return {
		file = {
			filename = "<internal>",
			lines = {"<internal code>"},
		},
		from = {line = 1, column = 1, index = 1},
		to = {line = 1, column = 15, index = 15},
	}
end

local BUILTIN_DEFINITIONS = {
	-- Boolean
	Boolean = {
		isBuiltIn = true,
		tag = "class-definition",
		constraintArguments = {},
		genericConstraintMap = {
			order = {},
			map = {},
			locations = {},
		},

		fieldMap = {},
		kind = {
			tag = "keyword-type",
			role = "type",
			name = "Boolean",
		},

		-- Functions
		functionMap = {
			-- method eq(Boolean) Boolean
			eq = {
				signature = {
					foreign = true,
					longName = "Boolean:eq",
					memberName = "eq",
					modifier = "method",
					parameters = {p("left", BOOLEAN_TYPE), p("right", BOOLEAN_TYPE)},
					returnTypes = {BOOLEAN_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = {
						[true] = {{true, true}, {false, false}},
						[false] = {{true, false}, {false, true}},
					},
					eval = function(a, b)
						return a == b
					end,
				},
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method and(Boolean) Boolean
			["and"] = {
				signature = {
					foreign = true,
					longName = "Boolean:and",
					memberName = "and",
					modifier = "method",
					parameters = {p("left", BOOLEAN_TYPE), p("right", BOOLEAN_TYPE)},
					returnTypes = {BOOLEAN_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = {
						[true] = {{true, true}},
						[false] = {{false, false}, {false, true}, {true, false}},
					},
					eval = function(a, b)
						return a and b
					end,
				},
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method or(Boolean) Boolean
			["or"] = {
				signature = {
					foreign = true,
					longName = "Boolean:or",
					memberName = "or",
					modifier = "method",
					parameters = {p("left", BOOLEAN_TYPE), p("right", BOOLEAN_TYPE)},
					returnTypes = {BOOLEAN_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = {
						[true] = {{true, "*"}, {"*", true}},
						[false] = {{false, false}},
					},
					eval = function(a, b)
						return a or b
					end,
				},
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method implies(Boolean) Boolean
			["implies"] = {
				signature = {
					foreign = true,
					longName = "Boolean:implies",
					memberName = "implies",
					modifier = "method",
					parameters = {p("left", BOOLEAN_TYPE), p("right", BOOLEAN_TYPE)},
					returnTypes = {BOOLEAN_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = {
						[true] = {{false, "*"}, {true, true}},
						[false] = {{true, false}},
					},
					eval = function(a, b)
						return not a or b
					end,
				},
				bodyAST = false,
				constraintArguments = {},
				definitionLocation = fakeLocation(),
			},

			-- method not(Boolean) Boolean
			["not"] = {
				signature = {
					foreign = true,
					longName = "Boolean:not",
					memberName = "not",
					modifier = "method",
					parameters = {p("left", BOOLEAN_TYPE)},
					returnTypes = {BOOLEAN_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = {
						[true] = {{false}},
						[false] = {{true}},
					},
					eval = function(a)
						return not a
					end,
				},
				bodyAST = false,
				constraintArguments = {},
				definitionLocation = fakeLocation(),
			},
		},
	},

	-- Int
	Int = {
		isBuiltIn = true,
		tag = "class-definition",
		constraintArguments = {},
		genericConstraintMap = {
			order = {},
			map = {},
			locations = {},
		},

		-- No fields
		fieldMap = {},

		-- Int type
		kind = {
			tag = "keyword-type",
			role = "type",
			name = "Int",
		},

		-- Functions
		functionMap = {
			-- method isPositive() Boolean
			isPositive = {
				signature = simpleSignature("Int", "method", "isPositive", {INT_TYPE}, {BOOLEAN_TYPE}, {
					eval = function(n)
						return 0 < n
					end,
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method negate() Int
			negate = {
				signature = simpleSignature("Int", "method", "negate", {INT_TYPE}, {INT_TYPE}, {
					eval = function(n)
						return -n
					end,
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method lessThan(Int) Boolean
			lessThan = {
				-- TODO: Add ensures/requires
				signature = simpleSignature("Int", "method", "lessThan", {INT_TYPE, INT_TYPE}, {BOOLEAN_TYPE}, {
					eval = function(a, b)
						return a < b
					end,
					ensuresASTs = {
						-- Transitive
						parseKind("ensures (forall (middle Int) return if (this < middle).and(middle < arg2))", "ensures"),

						-- Antireflexive
						parseKind("ensures return.not() when this == arg2", "ensures"),

						-- Antisymmetric
						parseKind("ensures return.not() when arg2 < this", "ensures"),

						-- Total order
						parseKind("ensures (this == arg2).or(arg2 < this) when return.not()", "ensures"),
					},
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method eq(Int) Boolean
			eq = {
				signature = simpleSignature("Int", "method", "eq", {INT_TYPE, INT_TYPE}, {BOOLEAN_TYPE}, {
					eval = function(a, b)
						return a == b
					end,
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method quotient(Int) Int
			quotient = {
				signature = simpleSignature("Int", "method", "quotient", {INT_TYPE, INT_TYPE}, {INT_TYPE}, {
					eval = function(a, b)
						return math.floor(a / b)
					end,
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method product(Int) Int
			product = {
				signature = simpleSignature("Int", "method", "product", {INT_TYPE, INT_TYPE}, {INT_TYPE}, {
					eval = function(a, b)
						return a * b
					end,
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method sum(Int) Int
			-- TODO: ordered field axiom
			sum = {
				signature = simpleSignature("Int", "method", "sum", {INT_TYPE, INT_TYPE}, {INT_TYPE}, {
					eval = function(a, b)
						return a + b
					end,
					ensuresASTs = {
						-- Ordered field
						parseKind("ensures this < return when 0 < arg2", "ensures"),

						-- Inverse
						parseKind("ensures (return - arg2) == this", "ensures"),

						-- Commutative
						parseKind("ensures return == (arg2 + this)", "ensures"),

						-- Identity
						parseKind("ensures return == this when arg2 == 0", "ensures"),
					},
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method difference(Int) Int
			difference = {
				signature = simpleSignature("Int", "method", "difference", {INT_TYPE, INT_TYPE}, {INT_TYPE}, {
					eval = function(a, b)
						return a - b
					end,
				}),
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},
		},
	},

	-- String
	String = {
		isBuiltIn = true,
		tag = "class-definition",
		constraintArguments = {},
		genericConstraintMap = {
			order = {},
			map = {},
			locations = {},
		},

		fieldMap = {},
		kind = {
			tag = "keyword-type",
			role = "type",
			name = "String",
		},

		functionMap = {
			-- method concatenate(String) String
			["concatenate"] = {
				signature = {
					foreign = true,
					longName = "String:concatenate",
					memberName = "concatenate",
					modifier = "method",
					parameters = {p("left", STRING_TYPE), p("right", STRING_TYPE)},
					returnTypes = {STRING_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = false,
					eval = function(a, b)
						return a .. b
					end,
				},
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},

			-- method eq(String) Boolean
			["eq"] = {
				signature = {
					foreign = true,
					longName = "String:eq",
					memberName = "eq",
					modifier = "method",
					parameters = {p("left", STRING_TYPE), p("right", STRING_TYPE)},
					returnTypes = {BOOLEAN_TYPE},
					bang = false,
					requiresASTs = {},
					ensuresASTs = {},
					logic = false,
					eval = function(a, b)
						return a == b
					end,
				},
				bodyAST = false,
				definitionLocation = fakeLocation(),
				constraintArguments = {},
			},
		},
	},
}

for _, d in pairs(BUILTIN_DEFINITIONS) do
	d.resolverContext = {
		selfAllowed = false,
		generics = {},
		checkConstraints = true,
		template = false,
	}
	d.resolver = function(ast)
		assert(ast.tag == "type-keyword", "TODO: non built ins")
		return {
			tag = "keyword-type",
			role = "type",
			name = ast.name,
		}
	end
end

--------------------------------------------------------------------------------

return {
	STRING_TYPE = STRING_TYPE,
	INT_TYPE = INT_TYPE,
	BOOLEAN_TYPE = BOOLEAN_TYPE,
	UNIT_TYPE = UNIT_TYPE,
	NEVER_TYPE = NEVER_TYPE,
	OPERATOR_ALIAS = OPERATOR_ALIAS,

	builtinDefinitions = BUILTIN_DEFINITIONS,
}
