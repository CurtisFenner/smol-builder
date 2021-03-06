-- common.lua contains functions in common to many files (semantics, codegen,
-- verification)

local tokenization = import "tokenization.lua"
local syntax = import "syntax.lua"
local ansi = import "ansi.lua"

--------------------------------------------------------------------------------

-- RETURNS a description of the given TypeKind as a string of Smol code
local function showTypeKind(t)
	assertis(t, "TypeKind")

	if t.tag == "compound-type" then
		local base = t.packageName .. ":" .. t.definitionName
		if #t.arguments == 0 then
			return base
		end
		local arguments = table.map(showTypeKind, t.arguments)
		return base .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif t.tag == "self-type" then
		return "#Self"
	elseif t.tag == "generic-type" then
		return "#" .. t.name
	elseif t.tag == "keyword-type" then
		return t.name
	end
	error "unknown TypeKind tag"
end

-- RETURNS a description of the given ConstraintKind as a string of Smol code
local function showConstraintKind(c)
	assertis(c, "ConstraintKind")

	if c.tag == "interface-constraint" then
		local base = c.packageName .. ":" .. c.definitionName
		if #c.arguments == 0 then
			return base
		end
		local arguments = table.map(showTypeKind, c.arguments)
		return base .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif c.tag == "keyword-constraint" then
		return c.name
	end
	error "unknown ConstraintKind tag"
end

-- RETURNS a description of the given Signature as a string of Smol code
local function showSignature(s)
	assertis(s, "Signature")

	local parameters = {}
	for _, p in ipairs(s.parameters) do
		table.insert(parameters, showTypeKind(p.type))
	end
	local parameterList = "(" .. table.concat(parameters, ", ") .. ") "

	local returnTypes = table.map(showTypeKind, s.returnTypes)
	local returnList = table.concat(returnTypes, ", ")
	return s.modifier .. " " .. s.memberName .. parameterList .. returnList
end

-- RETURNS whether or not two given types are the same
local function areTypesEqual(a, b)
	assertis(a, "TypeKind")
	assertis(b, "TypeKind")

	return showTypeKind(a) == showTypeKind(b)
end

-- RETURNS whether or not two given constraint kinds are the same
local function areConstraintsEqual(a, b)
	assertis(a, "ConstraintKind")
	assertis(b, "ConstraintKind")

	return showConstraintKind(a) == showConstraintKind(b)
end

--------------------------------------------------------------------------------

-- RETURNS a parse object, or quits with a syntax error
local function parseKind(s, k)
	local tokens = tokenization(s, "<compiler-core>")
	return syntax.parseKind(tokens, k)
end

-- RETURNS a string containing the contents of the source code within this
-- Location
local function excerpt(location)
	assertis(location, "Location")

	local from, to = location.from, location.to
	local source = location.file.lines

	local out = ""
	for line = from.line, to.line do
		local low = 1
		local high = #source[line]
		if line == from.line then
			low = from.column
		end
		if line == to.line then
			high = to.column
		end
		out = out .. source[line]:sub(low, high)
	end
	return out
end

-- RETURNS a string
local function locationBrief(location)
	assertis(location, "Location")

	local from = location.from

	return location.file.filename .. ":" .. from.line .. ":" .. from.column
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
		return a.variable.name
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

-- RETURNS a TypeKind
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
		return assertion.fieldType
	elseif assertion.tag == "variable" then
		return assertion.variable.type
	elseif assertion.tag == "isa" then
		return BOOLEAN_TYPE
	elseif assertion.tag == "variant" then
		return assertion.variantType
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
	elseif statement.tag == "sequence" then
		color = ansi.gray
	end

	local pre = indent .. color(statement.tag)
	if statement.tag == "sequence" then
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
		return pre .. " " .. statement.variable.name .. " " .. showTypeKind(statement.variable.type)
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
	elseif statement.tag == "static-call" then
		local destinations = showDestinations(statement.destinations)
		local arguments = table.concat(table.map(table.getter "name", statement.arguments), ", ")
		local rhs = statement.signature.longName .. "(" .. arguments .. ")"
		return pre .. " " .. destinations .. " := " .. rhs
	elseif statement.tag == "dynamic-call" then
		local arguments = showDestinations(statement.arguments)
		local rhs = statement.signature.longName .. "(" .. arguments .. ") via <?>"
		local lhs = showDestinations(statement.destinations)
		return pre .. " " .. lhs .. " := " .. rhs
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
	elseif statement.tag == "match" then
		local x = {}
		table.insert(x, pre)
		table.insert(x, " ")
		table.insert(x, statement.base.name)
		table.insert(x, "\n")
		for _, c in ipairs(statement.cases) do
			table.insert(x, indent .. "case " .. c.variant)
			table.insert(x, "\n")
			table.insert(x, showStatement(c.statement, indent .. "\t"))
			table.insert(x, "\n")
		end
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
			table.insert(rhs, k .. " = " .. v.name)
		end
		rhs = table.concat(rhs, ", ")
		local t = showTypeKind(statement.destination.type)
		return pre .. " " .. statement.destination.name .. " := new " .. t .. "(" .. rhs .. ")"
	elseif statement.tag == "new-union" then
		local rhs = statement.field .. " -> " .. statement.value.name
		local t = showTypeKind(statement.destination.type)
		return pre .. " " .. statement.destination.name .. " := new " .. t .. "(" .. rhs .. ")"
	elseif statement.tag == "boolean" then
		local rhs = tostring(statement.boolean)
		return pre .. " " .. statement.destination.name .. " := " .. rhs
	elseif statement.tag == "int-load" then
		local rhs = tostring(statement.number)
		return pre .. " " .. statement.destination.name .. " := " .. rhs
	else
		return pre .. " <?>"
	end
end

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

	-- Helpers
	areTypesEqual = areTypesEqual,
	areConstraintsEqual = areConstraintsEqual,
	assertionExprString = assertionExprString,
	showTypeKind = showTypeKind,
	showConstraintKind = showConstraintKind,
	showSignature = showSignature,

	typeOfAssertion = typeOfAssertion,

	excerpt = excerpt,
	locationBrief = locationBrief,

	showStatement = showStatement,

	builtinDefinitions = BUILTIN_DEFINITIONS,
}
