local parser = import "parser.lua"

parser.config = {
	locationSpan = function(from, to)
		assert(from.file == to.file, "span must be in one file")

		return {
			file = from.file,
			from = from.from,
			to = to.to,
		}
	end,

	locationFinal = function(file)
		return {
			line = #file.lines + 1,
			column = 1,
			index = 0,
		}
	end,

	locationInitial = function(file)
		return {
			line = 1,
			column = 1,
			index = 0,
		}
	end,
}

local Stream = parser.Stream

-- PARSER for literal lexeme (keywords, punctuation, etc.)
local function LEXEME(lexeme)
	assert(type(lexeme) == "string", "lexeme must be string")

	return parser.token(function(token)
		assert(type(token.lexeme) == "string")
		if token.lexeme == lexeme then
			return token
		end
	end)
end

local K_COMMA = LEXEME ","
local K_SEMICOLON = LEXEME ";"
local K_PIPE = LEXEME "|"
local K_DOT = LEXEME "."
local K_EQUAL = LEXEME "="
local K_SCOPE = LEXEME ":"
local K_BANG = LEXEME "!"

local K_CURLY_OPEN = LEXEME "{"
local K_CURLY_CLOSE = LEXEME "}"
local K_ROUND_OPEN = LEXEME "("
local K_ROUND_CLOSE = LEXEME ")"
local K_SQUARE_OPEN = LEXEME "["
local K_SQUARE_CLOSE = LEXEME "]"

local K_CASE = LEXEME "case"
local K_CLASS = LEXEME "class"
local K_DO = LEXEME "do"
local K_ELSE = LEXEME "else"
local K_ELSEIF = LEXEME "elseif"
local K_FOREIGN = LEXEME "foreign"
local K_IF = LEXEME "if"
local K_IMPORT = LEXEME "import"
local K_INTERFACE = LEXEME "interface"
local K_IS = LEXEME "is"
local K_MATCH = LEXEME "match"
local K_METHOD = LEXEME "method"
local K_NEW = LEXEME "new"
local K_PACKAGE = LEXEME "package"
local K_RETURN = LEXEME "return"
local K_STATIC = LEXEME "static"
local K_THIS = LEXEME "this"
local K_UNIT_VALUE = LEXEME "unit"
local K_FALSE = LEXEME "false"
local K_TRUE = LEXEME "true"
local K_UNION = LEXEME "union"
local K_VAR = LEXEME "var"

local K_ASSERT = LEXEME "assert"
local K_ENSURES = LEXEME "ensures"
local K_REQUIRES = LEXEME "requires"
local K_WHEN = LEXEME "when"
local K_FORALL = LEXEME "forall"

-- Built-in types
local K_STRING = LEXEME "String"
local K_UNIT_TYPE = LEXEME "Unit"
local K_NEVER = LEXEME "Never"
local K_INT = LEXEME "Int"
local K_BOOLEAN = LEXEME "Boolean"
local K_SELF = LEXEME "#Self"

-- PARSER for token tag ("typename", "identifier", "operator", etc)
local function TOKEN(tokenType, field)
	assert(type(tokenType) == "string")
	assert(type(field) == "string" or field == nil)

	return function(stream, parsers)
		assert(parsers)
		if stream:size() == 0 then
			return nil
		end
		if stream:head().tag == tokenType then
			if field then
				return stream:head()[field], stream:rest()
			else
				return stream:head(), stream:rest()
			end
		end
		return nil
	end
end
local T_IDENTIFIER = TOKEN("identifier", "lexeme")
local TR_IDENTIFIER = TOKEN("identifier")
local T_TYPENAME = TOKEN("typename", "lexeme")
local TR_TYPENAME = TOKEN("typename")
local T_GENERIC = TOKEN("generic")
local T_INTEGER_LITERAL = TOKEN("integer-literal")
local T_STRING_LITERAL = TOKEN("string-literal")
local T_OPERATOR = TOKEN("operator")

local function parserOtherwise(p, value)
	assert(type(p) == "function")
	return parser.map(p, function(x)
		return x or value
	end)
end

--------------------------------------------------------------------------------

local tree = import "tree.lua"

local ExprMethodCall = tree.MethodCallTree
local TypeTree = tree.TypeTree

--------------------------------------------------------------------------------

-- DEFINES the grammar for the language
local parsers = {
	-- Represents an entire source file
	["source"] = parser.composite {
		tag = "source",
		{"package", parser.named "package", "a package definition"},
		{"imports", parser.query "import*"},
		{"definitions", parser.query "definition*"},
		{"_", parser.endOfStream(), "another definition"},
	},

	-- Represents a package declaration
	["package"] = parser.composite {
		tag = "package",
		{"_", K_PACKAGE},
		{"name", TR_IDENTIFIER, "an identifier"},
		{"_", K_SEMICOLON, "`;` to finish package declaration"},
	},

	-- Represents an import
	["import"] = parser.composite {
		tag = "import",
		{"_", K_IMPORT},
		{"packageName", TR_IDENTIFIER, "an imported package name"},
		{
			-- string | false
			"objectName",
			parser.optional(parser.composite {
				tag = "***type name",
				{"_", K_SCOPE},
				{"#class", TR_TYPENAME, "a type name"},
			})
		},
		{"_", K_SEMICOLON, "`;` after import"},
	},

	-- Represents a top-level definition
	["definition"] = parser.choice {
		parser.named "class-definition",
		parser.named "union-definition",
		parser.named "interface-definition",
	},

	-- Represents a class
	["class-definition"] = parser.composite {
		tag = "class-definition",
		{
			"header",
			parser.composite {
				tag = "class-header",
				{"_", K_CLASS},
				{"name", TR_TYPENAME, "a type name"},
				{
					"generics",
					parserOtherwise(parser.query "generics?", {
						parameters = {},
						constraints = {},
					})
				},
				{"implements", parserOtherwise(parser.query "implements?", {})},
			},
		},
		{"_", K_CURLY_OPEN, "`{` to begin class body"},
		{"fields", parser.query "field-definition*"},
		{"methods", parser.query "method-definition*"},
		{"_", K_CURLY_CLOSE, "`}`"},
	},
	["implements"] = parser.composite {
		tag = "***implements",
		{"_", K_IS},
		{
			"#interfaces",
			parser.query "concrete-type,1+",
			"one or more interface names",
		},
	},

	-- Represents a union
	["union-definition"] = parser.composite {
		tag = "union-definition",
		{
			"header",
			parser.composite {
				tag = "union-header",
				{"_", K_UNION},
				{"name", TR_TYPENAME, "a type name"},
				{
					"generics",
					parserOtherwise(parser.query "generics?", {
						parameters = {},
						constraints = {},
					})
				},
				{"implements", parserOtherwise(parser.query "implements?", {})},
			},
		},
		{"_", K_CURLY_OPEN, "`{` to begin union body"},
		{"fields", parser.query "field-definition*"},
		{"methods", parser.query "method-definition*"},
		{"_", K_CURLY_CLOSE, "`}`"},
	},

	-- Represents an interface
	["interface-definition"] = parser.composite {
		tag = "interface-definition",
		{
			"header",
			parser.composite {
				tag = "interface-header",
				{"_", K_INTERFACE},
				{"name", TR_TYPENAME, "a type name"},
				{
					"generics",
					parserOtherwise(parser.query "generics?", {
						parameters = {},
						constraints = {},
					})
				},
			},
		},
		{"_", K_CURLY_OPEN, "`{` to begin interface body"},
		{"signatures", parser.zeroOrMore(parser.composite {
			tag = "***signature",
			{"#signature", parser.named "signature"},
			{"_", K_SEMICOLON, "`;` after interface member"},
		})},
		{"_", K_CURLY_CLOSE, "`}` to end interface body"},
		{"implements", parser.constant {}},
	},

	-- Represents a generics definition
	["generics"] = parser.composite {
		tag = "generics",
		{"_", K_SQUARE_OPEN},
		{
			"parameters",
			parser.delimited(T_GENERIC, "1+", ",", "generic parameter"),
			"generic parameter variables",
		},
		{"constraints", parserOtherwise(parser.query "generic-constraints?", {})},
		{"_", K_SQUARE_CLOSE, "`]` to end list of generics"},
	},

	["generic-constraints"] = parser.composite {
		tag = "generic constraints",
		{"_", K_PIPE},
		{"#constraints", parser.query "generic-constraint,1+", "generic constraints"},
	},

	["generic-constraint"] = parser.composite {
		tag = "constraint",
		{"parameter", T_GENERIC},
		{"_", K_IS, "`is` after generic parameter"},
		{"constraint", parser.named "concrete-type", "a type constraint after `is`"},
	},

	-- Represents a smol Type
	["type"] = parser.choice {
		-- Built in special types
		K_STRING,
		K_INT,
		K_BOOLEAN,
		K_UNIT_TYPE,
		K_SELF,

		-- User defined types
		T_GENERIC,
		parser.named "concrete-type",
	},

	["concrete-type"] = parser.composite {
		tag = "concrete-type",
		{
			"package",

			--: string | false
			parser.query "package-scope?",
		},
		{"base", T_TYPENAME},

		--: string
		{"arguments", parserOtherwise(parser.query "type-arguments?", {})},

		--: [ Type ]
	},

	["package-scope"] = parser.composite {
		tag = "***package-scope",
		{"#name", T_IDENTIFIER},
		{"_", K_SCOPE},
	},

	["type-arguments"] = parser.composite {
		tag = "***list of type arguments",
		{"_", K_SQUARE_OPEN},
		{"#arguments", parser.query "type,1+", "type arguments"},
		{"_", K_SQUARE_CLOSE, "`]`"},
	},

	["field-definition"] = parser.composite {
		tag = "field-definition",
		{"_", K_VAR},
		{"name", TR_IDENTIFIER, "the field's name after `var`"},
		{"type", parser.named "type", "the field's type after field name"},
		{"_", K_SEMICOLON, "`;` after field type"},
	},

	["method-definition"] = parser.choice {
		parser.named "foreign-method-definition",
		parser.named "real-method-definition",
	},

	["real-method-definition"] = parser.composite {
		tag = "method-definition",
		{"signature", parser.named "signature"},
		{"body", parser.named "block", "a method body"},
		{"foreign", parser.constant(false)},
	},

	["foreign-method-definition"] = parser.composite {
		tag = "foreign-method-definition",
		{"_", K_FOREIGN},
		{"signature", parser.named "signature"},
		{"_", K_SEMICOLON, "a `;` after foreign signature"},
		{"foreign", parser.constant(true)},
	},

	-- Represents a function signature, including name, scope,
	-- parameters, and return type.
	["signature"] = parser.composite {
		tag = "signature",
		{"modifier", parser.named "method-modifier"},
		{"name", TR_IDENTIFIER, "a method name"},
		{"bang", parser.optional(K_BANG)},
		{"_", K_ROUND_OPEN, "`(` after method name"},
		{"parameters", parser.query "variable,0+"},
		{"_", K_ROUND_CLOSE, "`)` after method parameters"},
		{"returnTypes", parser.query "type,1+", "a return type"},
		{"requires", parser.zeroOrMore(parser.named "requires")},
		{"ensures", parser.zeroOrMore(parser.named "ensures")},
	},

	["requires"] = parser.composite {
		tag = "requires",
		{"_", K_REQUIRES},
		{"condition", parser.named "expression", "an expression"},
		{
			"whens",
			parserOtherwise(
				parser.optional(parser.composite {
					tag = "when",
					location = false,
					{"_", K_WHEN},
					{"#when", parser.query "expression,1+", "an expression"},
				}),
				{}
			),
		},
	},
	["ensures"] = parser.composite {
		tag = "ensures",
		{"_", K_ENSURES},
		{"condition", parser.named "expression", "an expression"},
		{
			"whens",
			parserOtherwise(
				parser.optional(parser.composite {
					tag = "when",
					location = false,
					{"_", K_WHEN},
					{"#when", parser.query "expression,1+", "an expression"},
				}),
				{}
			),
		},
	},

	["method-modifier"] = parser.choice {
		K_METHOD,
		K_STATIC,
	},

	-- Represents a smol statement / control structure
	["statement"] = parser.choice {
		parser.named "var-statement",
		parser.named "do-statement",
		parser.named "if-statement",
		parser.named "match-statement",
		parser.named "assert-statement",
		parser.named "return-statement",
		parser.named "assign-statement",
	},

	["block"] = parser.composite {
		tag = "block",
		{"_", K_CURLY_OPEN},
		{"statements", parser.query "statement*"},
		{"_", K_CURLY_CLOSE, "`}` to end statement block"},
	},

	["variable"] = parser.composite {
		tag = "variable",
		{"name", TR_IDENTIFIER},
		{"type", parser.named "type", "a type after variable name"},
	},

	["return-statement"] = parser.composite {
		tag = "return-statement",
		{"_", K_RETURN},
		{"values", parser.query "expression,0+"},
		{"_", K_SEMICOLON, "`;` to end return-statement"},
	},

	["assert-statement"] = parser.composite {
		tag = "assert-statement",
		{"_", K_ASSERT},
		{
			"expression",
			parser.named "expression",
			"an expression to assert the truth of after `assert`",
		},
		{"_", K_SEMICOLON, "`;` to end assert-statement"},
	},

	["do-statement"] = parser.composite {
		tag = "do-statement",
		{"_", K_DO},
		{"expression", parser.named "expression", "an expression to execute after `do`"},
		{"_", K_SEMICOLON, "`;` to end do-statement"},
	},

	["assign-statement"] = parser.composite {
		tag = "assign-statement",
		{"variables", parser.delimited(T_IDENTIFIER, "1+", ",", "a variable name")},
		{"_", K_EQUAL, "`=` after variable"},
		{"value", parser.named "expression", "an expression after `=`"},
		{"_", K_SEMICOLON, "`;` to end assign-statement"},
	},

	["var-statement"] = parser.composite {
		tag = "var-statement",
		{"_", K_VAR},
		{
			"variables",
			parser.query "variable,1+",
			"one or more comma-separated variables",
		},
		{"_", K_EQUAL, "`=` after the variable in the var-statement"},
		{"value", parser.named "expression", "an expression after `=`"},
		{"_", K_SEMICOLON, "`;` to end var-statement"},
	},

	["if-statement"] = parser.composite {
		tag = "if-statement",
		{"_", K_IF},
		{"condition", parser.named "expression", "expected a condition in `if` statement"},
		{"body", parser.named "block", "expected a block to follow `if` condition"},
		{"elseifClauses", parser.query "else-if-clause*"},
		{"elseClause", parser.query "else-clause?"},
	},

	["else-if-clause"] = parser.composite {
		tag = "else-if-clause",
		{"_", K_ELSEIF},
		{"condition", parser.named "expression", "expected a condition in `elseif` clause"},
		{"body", parser.named "block", "expected a block to follow `elseif` condition"},
	},

	["else-clause"] = parser.composite {
		tag = "else-clause",
		{"_", K_ELSE},
		{"body", parser.named "block", "expected a block to follow `else`"},
	},

	["match-statement"] = parser.composite {
		tag = "match-statement",
		{"_", K_MATCH},
		{"base", parser.named "expression", "expected an expression to match on"},
		{"_", K_CURLY_OPEN, "expected a `{`"},
		{"cases", parser.query "case+", "expected at least one case"},
		{"_", K_CURLY_CLOSE, "expected a `}`"},
	},

	["case"] = parser.composite {
		tag = "case",
		{"_", K_CASE},
		{
			"head",
			parser.composite {
				tag = "case-head",
				{"variable", T_IDENTIFIER, "expected a variable name"},
				{"_", K_IS, "expected `is`"},
				{"variant", T_IDENTIFIER, "expected a union tag name"},
			},
		},
		{"body", parser.named "block", "expected a block to follow case"},
	},

	["isa"] = parser.composite {
		tag = "isa",
		{"_", K_IS},
		{"variant", T_IDENTIFIER, "expected a variant identifier"},
	},

	-- Expressions!
	["expression"] = parser.map(
		parser.composite {
			tag = "***expression",
			{"base", parser.named "atom"},
			{"operations", parser.query "operation*"},
			{"isa", parser.query "isa?"},
		},
		function(x)
			-- XXX: no precedence yet; reject unparenthesized
			local out = x.base
			assert(type(out.tag) == "string")

			local isa = x.isa

			if #x.operations >= 2 then
				quit("You must explicitly parenthesize the operators ", x.operations[2].location)
			end

			for _, operation in ipairs(x.operations) do
				out = {
					tag = "binary",
					left = out,
					right = operation.operand,
					operator = operation.operator.lexeme,
				}
				assert(type(out.operator) == "string")
			end

			if isa then
				return {
					tag = "isa",
					base = out,
					variant = isa.variant,
				}
			end

			assert(out)
			return out
		end,
		true
	),

	["operation"] = parser.composite {
		tag = "***operation",
		{"operator", T_OPERATOR},
		{"operand", parser.named "atom", "atom after operator"},
	},

	["new-expression"] = parser.composite {
		tag = "new-expression",
		{"_", K_NEW},
		{"_", K_ROUND_OPEN, "`(` after `new`"},
		{"fields", parser.query "named-argument,0+"},
		{"_", K_ROUND_CLOSE, "`)` to end `new` expression"},
	},

	["named-argument"] = parser.composite {
		tag = "named-argument",
		{"name", T_IDENTIFIER},
		{"_", K_EQUAL},
		{"value", parser.named "expression", "an expression after `=`"},
	},

	["atom"] = parser.map(
		parser.composite {
			tag = "***atom",
			{"base", parser.named "atom-base"},
			{"accesses", parser.query "access*"},
		},
		function(x, ticket)
			local out = x.base
			for _, access in ipairs(x.accesses) do
				local location = parser.config.locationSpan(
					out.location,
					access.location
				)
				if access.tag == "method-access" then
					out = ExprMethodCall.new(out, access, location, ticket)
				else
					assert(access.tag == "field-access")
					out = {
						tag = "field-expression",
						base = out,
						field = access.field,
						location = location,
					}
				end
			end
			return out
		end,
		true
	),

	["method-access"] = parser.composite {
		tag = "method-access",
		{"_", K_DOT},
		{"methodName", TR_IDENTIFIER, "a method/field name"},

		-- What follows is optional, since a field access is also possible
		{"bang", parser.optional(K_BANG)},
		{
			"arguments",
			parser.composite {
				tag = "arguments",
				{"_", K_ROUND_OPEN},
				{"#arguments", parser.query "expression,0+"},
				{"_", K_ROUND_CLOSE, "`)` to end method arguments"},
			}
		}
	},
	["field-access"] = parser.composite {
		tag = "field-access",
		{"_", K_DOT},
		{"field", TR_IDENTIFIER, "a field name"},
	},

	["access"] = parser.choice {
		parser.named "method-access",
		parser.named "field-access",
	},

	["static-call"] = parser.composite {
		tag = "static-call",
		{"baseType", parser.named "type"},
		{"_", K_DOT, "`.` after type name"},
		{"funcName", TR_IDENTIFIER, "a static method's name"},
		{"bang", parser.optional(K_BANG)},
		{"_", K_ROUND_OPEN, "`(` after static method name"},
		{"arguments", parser.query "expression,0+"},
		{"_", K_ROUND_CLOSE, "`)` to end static method call"},
	},

	["forall"] = parser.composite {
		tag = "forall-expr",
		{"_", K_FORALL},
		{"_", K_ROUND_OPEN, "`(` after `forall`"},
		{"variable", parser.named "variable", "variable after `forall (`"},
		{"_", K_ROUND_CLOSE, "`)` after variable"},
		{"condition", parser.named "expression", "predicate expression"},
		{
			"whens",
			parserOtherwise(
				parser.optional(parser.composite {
					tag = "forall-when",
					location = false,
					{"_", K_IF},
					{"#when", parser.query "expression,1+", "an expression"},
				}),
				{}
			),
		}
	},

	["atom-base"] = parser.choice {
		parser.named "new-expression",
		K_THIS,
		K_TRUE,
		K_FALSE,
		K_UNIT_VALUE,
		parser.named "forall",
		T_STRING_LITERAL,
		T_INTEGER_LITERAL,
		parser.named "static-call",
		TR_IDENTIFIER,
		parser.composite {
			tag = "***parenthesized expression",
			{"_", K_ROUND_OPEN},
			{"#expression", parser.named "expression", "expression"},
			{"_", K_ROUND_CLOSE, "`)`"},
		},
		K_RETURN,
	},
}

-- tokens: a list of tokens,
-- with tokens.file being a file for location generation.
-- RETURNS an AST of the given kind
local function parseKind(tokens, kind, ticket)
	assert(tokens.file, "tokens need file source")
	local stream = Stream(tokens)

	local grammar = setmetatable({ticket = ticket}, {__index = parsers})
	local source = parsers[kind](stream, grammar)
	return source
end

-- tokens: a list of tokens,
-- with tokens.file being a file for location generation.
-- RETURNS a Source AST
local function parseFile(tokens, ticket)
	assert(type(ticket) == "string")
	return parseKind(tokens, "source", ticket)
end

return {
	parseFile = parseFile,
	parseKind = parseKind,
}
