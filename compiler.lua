-- A transpiler for Smol -> ???
-- Curtis Fenner, copyright (C) 2017

local ARGV = arg

local INVOKATION = ARGV[0] .. " " .. table.concat(ARGV, ", ")
	.. "\non " .. os.date("!%c")
	.. "\nsmol version 0??"

--------------------------------------------------------------------------------

local function import(name)
	local directory = ARGV[0]:gsub("[^/\\]+$", "")
	return dofile(directory .. name)
end

import "extend.lua"
import "types.lua"

local parser = import "parser.lua"
local ansi = import "ansi.lua"

--------------------------------------------------------------------------------

-- DISPLAYS the concatenation of the input,
-- and terminates the program.
-- DOES NOT RETURN.
local function quit(first, ...)
	if not first:match("^[A-Z]+:\n$") then
		print(table.concat{ansi.red("ERROR"), ":\n", first, ...})
		os.exit(45)
	else
		print(table.concat{ansi.cyan(first), ...})
		os.exit(40)
	end
end

-- Lexer -----------------------------------------------------------------------

-- RETURNS a list of tokens.
-- source: the contents of a source file.
-- filename: a human-readable name indicating this source file.
local function lexSmol(source, filename)
	assert(isstring(source))
	assert(isstring(filename))

	-- Normalize line end-ings
	source = source:gsub("\r*\n\r*", "\n")
	source = source:gsub("\r", "\n")
	source = source .. "\n"

	local IS_KEYWORD = {
		["case"] = true,
		["class"] = true,
		["do"] = true,
		["foreign"] = true,
		["import"] = true,
		["interface"] = true,
		["is"] = true,
		["match"] = true,
		["method"] = true,
		["new"] = true,
		["package"] = true,
		["return"] = true,
		["static"] = true,
		["union"] = true,
		["var"] = true,
		-- built-in types
		["Boolean"] = true,
		["Never"] = true,
		["Number"] = true,
		["String"] = true,
		["Unit"] = true,
		-- values
		["this"] = true,
		["true"] = true,
		["false"] = true,
	}

	-- Define token parsing rules
	local TOKENS = {
		{ -- type keywords, type names
			"[A-Z][A-Za-z0-9]*",
			function(x)
				if IS_KEYWORD[x] then
					return {tag = "type-keyword", name = x}
				end
				return {tag = "typename", name = x}
			end
		},
		{ -- keywords, local identifiers
			"[a-z][A-Za-z0-9]*",
			function(x)
				if IS_KEYWORD[x] then
					return {tag = "keyword", keyword = x}
				end
				return {tag = "identifier", name = x}
			end
		},
		{ -- generic type parameters
			"#[A-Z][A-Za-z0-9]*",
			function(x)
				return {tag = "generic", name = x:sub(2)}
			end
		},
		{ -- whitespace
			"%s+",
			function(x) return false end
		},
		{ -- comments
			"//[^\n]*", -- (greedy)
			function(x) return false end
		},
		{ -- punctuation (braces, commas, etc)
			"[.,:;|()%[%]{}]",
			function(x) return {tag = "punctuation"} end
		},
		{ -- assignment
			"=",
			function(x) return {tag = "assign"} end
		},
		{ -- operators
			"[+%-*/%^<>=]+",
			function(x) return {tag = "operator"} end
		},
		{ -- integer literals
			"[0-9]+",
			function(x)
				return {tag = "integer-literal", value = tonumber(x)}
			end
		},
	}

	local QUOTE = "\""
	local BACKSLASH = "\\"

	-- Create a list of the lines in the program, for location messages
	local sourceLines = {}
	for line in (source .. "\n"):gmatch("(.-)\n") do
		line = line:gsub("\r", "")
		line = line:gsub("\t", "    ") -- TODO: this should be aligned
		table.insert(sourceLines, line)
	end

	local tokens = {}

	-- Track the location into the source file each token is
	local line = 1
	local column = 1
	local function advanceCursor(str)
		assert(isstring(str))
		for c in str:gmatch(".") do
			if c == "\r" then
				-- Carriage returns do not affect reported cursor location
			elseif c == "\n" then
				column = 1
				line = line + 1
			elseif c == "\t" then
				-- XXX: This reports column (assuming tab = 4)
				-- rather than character.
				-- (VSCode default behavior when tabs are size 4)
				-- (Atom default behavior counts characters)
				column = math.ceil(column/4)*4 + 1
			else
				column = column + 1
			end
		end
	end

	while #source > 0 do
		-- Compute human-readable description of location
		local sourceContext = "\t" .. line .. ":\t" .. sourceLines[line]
			.. "\n\t\t" .. string.rep(" ", column-1) .. ansi.red("^")

		local location = "at " .. filename .. ":" .. line .. ":" .. column
			.. "\n" .. sourceContext .. "\n"

		-- Tokenize string literals
		if source:sub(1, 1) == QUOTE then
			local SPECIAL = {
				n = "\n",
				t = "\t",
				r = "\r",
				["0"] = string.char(0),
				[QUOTE] = QUOTE,
				[BACKSLASH] = BACKSLASH,
			}
			local content = ""
			local escaped = false
			for i = 2, #source do
				local c = source:sub(i, i)
				if c == "\n" then
					quit("The compiler found an unfinished string literal",
						" that begins ", location)
				end
				if escaped then
					if not SPECIAL[c] then
						quit("The compiler found an unknown escape sequence",
							" `\\", c, "`",
							" in a string literal that begins ", location)
					end
					content = content .. SPECIAL[c]
					escaped = not escaped
				elseif c == BACKSLASH then
					escaped = true
				elseif c == QUOTE then
					-- Update location
					advanceCursor(source:sub(1, i))
					local lexeme = source:sub(1, i)
					-- String literal is complete
					source = source:sub(i+1)
					table.insert(tokens, freeze {
						tag = "string-literal",
						value = content,
						location = location,
						lexeme = lexeme,
					})
					break
				else
					content = content .. c
				end
			end
		else
			-- Search for matching token parsing rule
			local matched = false
			for _, tokenRule in ipairs(TOKENS) do
				local match = source:match("^" .. tokenRule[1])
				if match then
					-- Consume token and add to token stream
					local token = tokenRule[2](match)
					assert(type(token) == "table" or rawequal(token, false),
						"token must be table `" .. tokenRule[1] .. "`")
					if token then
						token.location = location
						token.lexeme = match
						table.insert(tokens, freeze(token))
					end

					-- Advance the cursor through the text file
					advanceCursor(match)
					source = source:sub(#match+1)

					matched = true
					break
				end
			end

			-- Check for an unlexible piece of source
			if not matched then
				quit("The compiler could not recognize any token ", location)
			end
		end
	end

	return freeze(tokens)
end

-- Stream ----------------------------------------------------------------------

REGISTER_TYPE("Token", recordType {
	location = "string",
	tag = "string",
	lexeme = "string",
})

-- REPRESENTS a streamable sequence of tokens
local function Stream(list, offset)
	offset = offset or 0
	assert(isinteger(offset), "offset must be an integer")
	assertis(list, listType "Token")

	return freeze {
		_list = list,
		_offset = offset,
		head = function(self)
			return self._list[1 + self._offset]
		end,
		rest = function(self)
			assert(self:size() > 0, "stream:rest() requires stream:size() > 0")
			return Stream(self._list, self._offset + 1)
		end,
		size = function(self)
			return #self._list - self._offset
		end,
		location = function(self)
			if self:size() == 0 then
				-- TODO: get file name
				return "end-of-file"
			else
				return self:head().location
			end
		end,
	}
end

-- Parsing Smol ----------------------------------------------------------------

local function parseSmol(tokens)
	local stream = Stream(tokens)

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

	local K_CURLY_OPEN = LEXEME "{"
	local K_CURLY_CLOSE = LEXEME "}"
	local K_ROUND_OPEN = LEXEME "("
	local K_ROUND_CLOSE = LEXEME ")"
	local K_SQUARE_OPEN = LEXEME "["
	local K_SQUARE_CLOSE = LEXEME "]"

	local K_CLASS = LEXEME "class"
	local K_DO = LEXEME "do"
	local K_FOREIGN = LEXEME "foreign"
	local K_IMPORT = LEXEME "import"
	local K_INTERFACE = LEXEME "interface"
	local K_IS = LEXEME "is"
	local K_METHOD = LEXEME "method"
	local K_NEW = LEXEME "new"
	local K_PACKAGE = LEXEME "package"
	local K_RETURN = LEXEME "return"
	local K_STATIC = LEXEME "static"
	local K_THIS = LEXEME "this"
	local K_FALSE = LEXEME "false"
	local K_TRUE = LEXEME "true"
	local K_UNION = LEXEME "union"
	local K_VAR = LEXEME "var"

	-- Built-in types
	local K_STRING = LEXEME "String"
	local K_UNIT = LEXEME "Unit"
	local K_NEVER = LEXEME "Never"
	local K_NUMBER = LEXEME "Number"
	local K_BOOLEAN = LEXEME "Boolean"

	-- PARSER for token tag ("typename", "identifier", "operator", etc)
	local function TOKEN(tokenType, field)
		assertis(tokenType, "string")
		assertis(field, "string")

		return function(stream, parsers)
			assert(parsers)
			if stream:size() == 0 then
				return nil
			end
			if stream:head().tag == tokenType then
				return stream:head()[field], stream:rest()
			end
			return nil
		end
	end
	local T_IDENTIFIER = TOKEN("identifier", "lexeme")
	local T_TYPENAME = TOKEN("typename", "lexeme")
	local T_GENERIC = TOKEN("generic", "name")
	local T_INTEGER_LITERAL = TOKEN("integer-literal", "value")
	local T_STRING_LITERAL = TOKEN("string-literal", "value")
	local T_OPERATOR = TOKEN("operator", "lexeme")

	local function parserOtherwise(p, value)
		assert(type(p) == "function")
		return parser.map(p, function(x) return x or value end)
	end

	-- DEFINES the grammar for the language
	local parsers = {
		-- Represents an entire source file
		["source"] = parser.query [[(source
			package =package !a_package_definition
			import* =imports
			definition* =definitions
		)]],

		-- Represents a package declaration
		["package"] = parser.composite {
			tag = "***package",
			{"_", K_PACKAGE},
			{"#name", T_IDENTIFIER, "an identifier"},
			{"_", K_SEMICOLON, "`;` to finish package declaration"},
		},

		-- Represents an import
		["import"] = parser.composite {
			tag = "import",
			{"_", K_IMPORT},
			{"package", T_IDENTIFIER, "an imported package name"},
			{
				"class", -- string | false
				parser.optional(parser.composite {
					tag = "***type name",
					{"_", K_SCOPE},
					{"#class", T_TYPENAME, "a type name"},
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
			{"foreign", parser.query "`foreign`?"},
			{"_", K_CLASS},
			{"name", T_TYPENAME, "a type name"},
			{"generics", parserOtherwise(parser.query "generics?", {
				parameters = {},
				constraints = {},
			})},
			{"implements", parserOtherwise(parser.query "implements?", {})},
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
			{"_", K_UNION},
			{"name", T_TYPENAME, "a type name"},
			{"generics", parserOtherwise(parser.query "generics?", {
				parameters = {},
				constraints = {},
			})},
			{"implements", parserOtherwise(parser.query "implements?", {})},
			{"_", K_CURLY_OPEN, "`{` to begin union body"},
			{"fields", parser.query "field-definition*"},
			{"methods", parser.query "method-definition*"},
			{"_", K_CURLY_CLOSE, "`}`"},
		},

		-- Represents an interface
		["interface-definition"] = parser.composite {
			tag = "interface-definition",
			{"_", K_INTERFACE},
			{"name", T_TYPENAME, "a type name"},
			{"generics", parserOtherwise(parser.query "generics?", {
				parameters = {},
				constraints = {},
			})},
			{"_", K_CURLY_OPEN, "`{` to begin interface body"},
			{"signatures", parser.query "interface-signature*"},
			{"_", K_CURLY_CLOSE, "`}` to end interface body"},
		},

		-- Represents a generics definition
		["generics"] = parser.composite {
			tag = "generics",
			{"_", K_SQUARE_OPEN},
			{
				"parameters",
				parser.delimited(T_GENERIC, "1+", ",", "generic parameter"),
				"generic parameter variables"
			},
			{
				"constraints",
				parserOtherwise(parser.query "generic-constraints?", {})
			},
			{"_", K_SQUARE_CLOSE, "`]` to end list of generics"},
		},

		["generic-constraints"] = parser.composite {
			tag = "***",
			{"_", K_PIPE},
			{
				"#constraints",
				parser.query "generic-constraint,1+",
				"generic constraints"
			},
		},

		["generic-constraint"] = parser.composite {
			tag = "constraint",
			{"parameter", T_GENERIC},
			{"_", K_IS, "`is` after generic parameter"},
			{"constraint", parser.named "concrete-type", "a type constrain after `is`"},
		},

		-- Represents a smol Type
		["type"] = parser.choice {
			-- Built in special types
			K_STRING,
			K_NUMBER,
			K_BOOLEAN,
			K_UNIT,
			K_NEVER,
			-- User defined types
			parser.map(T_GENERIC, function(x)
				return {tag = "generic", name = x, location = "???"}
			end),
			parser.named "concrete-type",
		},

		["concrete-type"] = parser.composite {
			tag = "concrete-type",
			{
				"package", --: string | false
				parser.query "package-scope?",
			},
			{"base", T_TYPENAME}, --: string
			{
				"arguments",
				parserOtherwise(parser.query "type-arguments?", freeze {})
			}, --: [ Type ]
		},

		["package-scope"] = parser.composite {
			tag = "***package-scope",
			{"#name", T_IDENTIFIER},
			{"_", K_SCOPE},
		},

		["type-arguments"] = parser.composite {
			tag = "***",
			{"_", K_SQUARE_OPEN},
			{"#arguments", parser.query "type,1+", "type arguments"},
			{"_", K_SQUARE_CLOSE, "`]`"},
		},

		["field-definition"] = parser.composite {
			tag = "field-definition",
			{"_", K_VAR},
			{"name", T_IDENTIFIER, "the field's name after `var`"},
			{"type", parser.named "type", "the field's type after field name"},
			{"_", K_SEMICOLON, "`;` after field type"},
		},

		["method-definition"] = parser.composite {
			tag = "method-definition",
			{"signature", parser.named "signature"},
			{"body", parser.named "block", "a method body"},
		},

		["interface-signature"] = parser.composite {
			tag = "***signature",
			{"#signature", parser.named "signature"},
			{"_", K_SEMICOLON, "`;` after interface method"},
		},

		-- Represents a function signature, including name, scope,
		-- parameters, and return type.
		["signature"] = parser.composite {
			tag = "signature",
			{"foreign", parser.query "`foreign`?"},
			{"modifier", parser.named "method-modifier"},
			{"name", T_IDENTIFIER, "a method name"},
			{"_", K_ROUND_OPEN, "`(` after method name"},
			{"parameters", parser.query "variable,0+"},
			{"_", K_ROUND_CLOSE, "`)` after method parameters"},
			{
				"returnTypes",
				parser.query "type,1+",
				"a return type"
			},
		},

		["method-modifier"] = parser.choice {
			K_METHOD,
			K_STATIC,
		},

		-- Represents a smol statement / control structure
		["statement"] = parser.choice {
			parser.named "return-statement",
			parser.named "do-statement",
			parser.named "var-statement",
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
			{"name", T_IDENTIFIER},
			{"type", parser.named "type", "a type after variable name"},
		},

		["return-statement"] = parser.composite {
			tag = "return-statement",
			{"_", K_RETURN},
			{"values", parser.query "expression,0+"},
			{"_", K_SEMICOLON, "`;` to end return-statement"},
		},

		["do-statement"] = parser.composite {
			tag = "do-statement",
			{"_", K_DO},
			{
				"expression",
				parser.named "expression",
				"an expression to execute after `do`"
			},
			{"_", K_SEMICOLON, "`;` to end do-statement"},
		},

		["assign-statement"] = parser.composite {
			tag = "assign-statement",
			{"variables", parser.query "expression,1+"}, -- XXX: this should be a variable
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

		-- Expressions!
		["expression"] = parser.map(parser.composite {
			tag = "***expression",
			{"base", parser.named "atom"},
			{"operations", parser.query "operation*"},
		}, function(x)
			-- XXX: no precedence yet; assume left-associative
			local out = x.base
			assertis(out.tag, "string")
			for _, operation in ipairs(x.operations) do
				out = {
					tag = "binary",
					left = out,
					right = operation.operand,
					operator = operation.operator,
				}
				assert(isstring(out.operator))
				if out.left.tag == "binary" then
					if out.left.operator ~= out.operator then
						print("warning: operator precedence is not yet implemented")
					end
				end
			end
			assert(out)
			return out
		end),

		["operation"] = parser.composite {
			tag = "***operation",
			{"operator", T_OPERATOR},
			{"operand", parser.named "atom", "atom after operator"},
		},

		["new-expression"] = parser.composite {
			tag = "new-expression",
			{"_", K_NEW},
			{"_", K_ROUND_OPEN, "`(` after `new`"},
			{"arguments", parser.query "named-argument,0+"},
			{"_", K_ROUND_CLOSE, "`)` to end `new` expression"},
		},

		["named-argument"] = parser.composite {
			tag = "named-argument",
			{"name", T_IDENTIFIER},
			{"_", K_EQUAL},
			{"value", parser.named "expression", "an expression after `=`"},
		},

		["atom"] = parser.map(parser.composite {
			tag = "***atom",
			{"base", parser.named "atom-base"},
			{"accesses", parser.query "access*"},
		}, function(x)
			local out = x.base
			for _, access in ipairs(x.accesses) do
				out = table.with(access, "base", out)
			end
			return out
		end),

		["access"] = parser.map(parser.composite {
			tag = "***access",
			{"_", K_DOT},
			{"name", T_IDENTIFIER, "a method/field name"},
			-- N.B.: Optional, since a field access is also possible...
			{"arguments", parser.optional(parser.composite{
				tag = "***arguments",
				{"_", K_ROUND_OPEN},
				{"#arguments", parser.query "expression,0+"},
				{"_", K_ROUND_CLOSE, "`)` to end"},
			})},
		}, function(x)
			if x.arguments then
				return {
					tag = "method-call",
					arguments = x.arguments,
					methodName = x.name, --: string
					location = x.location,
				}
			end
			return {
				tag = "field",
				field = x.name, --: string
				location = x.location,
			}
		end),

		["atom-base"] = parser.choice {
			parser.named "new-expression",
			K_THIS,
			K_TRUE,
			K_FALSE,
			parser.map(T_STRING_LITERAL, function(v)
				return {tag = "string-literal", value = v}
			end),
			parser.map(T_INTEGER_LITERAL, function(v)
				return {tag = "number-literal", value = v}
			end),
			parser.composite { -- static method call
				tag = "static-call",
				{"baseType", parser.named "type"},
				{"_", K_DOT, "`.` after type name"},
				{"name", T_IDENTIFIER, "a static method's name"},
				{"_", K_ROUND_OPEN, "`(` after static method name"},
				{"arguments", parser.query "expression,0+"},
				{"_", K_ROUND_CLOSE, "`)` to end static method call"},
			},
			parser.map(T_IDENTIFIER, function(n)
				return {tag = "identifier", name = n}
			end),
			parser.composite {
				tag = "***parenthesized expression",
				{"_", K_ROUND_OPEN},
				{"#expression", parser.named "expression", "expression"},
				{"_", K_ROUND_CLOSE, "`)`"},
			},
		},
	}

	-- Sequence of definitions
	local source, rest = parsers.source(stream, parsers)
	assert(rest ~= nil)
	if rest:size() ~= 0 then
		quit("The compiler expected another definition ", rest:location())
	end

	return source
end

-- Semantics / Verification ----------------------------------------------------

REGISTER_TYPE("Semantics", recordType {
	classes = listType "ClassIR",
	unions = listType "UnionIR",
	interfaces = listType "InterfaceIR",
	functions = listType "FunctionIR",
	main = "string",
})

REGISTER_TYPE("ClassIR", recordType {
	tag = constantType "class",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "ConcreteType+",
	signatures = listType "Signature",
	constraints = mapType("string", "ConcreteType+"),
})

REGISTER_TYPE("UnionIR", recordType {
	tag = constantType "union",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "ConcreteType+",
	signatures = listType "Signature",	
	constraints = mapType("string", "ConcreteType+"),
})

REGISTER_TYPE("InterfaceIR", recordType {
	tag = constantType "interface",
	name = "string",
	signatures = listType "Signature",
	generics = listType "TypeParameterIR",
})

REGISTER_TYPE("Definition", choiceType("ClassIR", "UnionIR", "InterfaceIR"))

REGISTER_TYPE("TypeParameterIR", recordType {
	name = "string", -- Type parameter name (e.g., "#Right")
	constraints = listType(recordType {
		interface = "ConcreteType+",
	}),
})

REGISTER_TYPE("FunctionIR", recordType {
	name = "string",
	parameters = listType "VariableIR",
	generics = listType "TypeParameterIR",
	returnTypes = listType "Type+",
	body = "BlockSt",
})

REGISTER_TYPE("maybe", choiceType(
	constantType "yes",
	constantType "no",
	constantType "maybe"
))

REGISTER_TYPE("StatementIR", intersectType("AbstractStatementIR", choiceType(
	"AssignSt",
	"BlockSt",
	"GenericMethodCallSt",
	"LocalSt",
	"NewSt",
	"NumberLoadSt",
	"ReturnSt",
	"StaticCallSt",
	"StringLoadSt",
	"NothingSt"
)))

REGISTER_TYPE("AbstractStatementIR", recordType {
	tag = "string",
	returns = "maybe",
})

EXTEND_TYPE("BlockSt", "AbstractStatementIR", recordType {
	tag = constantType "block",
	statements = listType "StatementIR",
})

EXTEND_TYPE("StringLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "string",
	destination = "VariableIR",
	string = "string",
	returns = constantType "no",	
})

EXTEND_TYPE("LocalSt", "AbstractStatementIR", recordType {
	tag = constantType "local",
	variable = "VariableIR",
	returns = constantType "no",	
})

EXTEND_TYPE("NothingSt", "AbstractStatementIR", recordType {
	tag = constantType "nothing",
	returns = constantType "no",	
})

EXTEND_TYPE("AssignSt", "AbstractStatementIR", recordType {
	tag = constantType "assign",
	source = "VariableIR",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("ReturnSt", "AbstractStatementIR", recordType {
	tag = constantType "return",
	sources = listType "VariableIR",
	returns = constantType "yes",
})

EXTEND_TYPE("NumberLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "number",
	number = "number",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NewSt", "AbstractStatementIR", recordType {
	tag = constantType "new",
	fields = mapType("string", "VariableIR"),
	type = "ConcreteType+",
	constraints = mapType("string", "ConstraintIR"),	
	returns = constantType "no",
})

EXTEND_TYPE("StaticCallSt", "AbstractStatementIR", recordType {
	tag = constantType "static-call",
	constraints = mapType("string", "ConstraintIR"),
	baseType = "Type+",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	name = "string",
})

EXTEND_TYPE("MethodCallSt", "AbstractStatementIR", recordType {
	tag = constantType "method-call",
	baseInstance = "VariableIR",
	name = "string",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("GenericMethodCallSt", "AbstractStatementIR", recordType {
	tag = constantType "generic-method-call",
	baseInstance = "VariableIR",
	constraint = "ConstraintIR",
	name = "string",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
})

REGISTER_TYPE("Signature", recordType {
	name = "string",
	parameters = listType "VariableIR",
	returnTypes = listType "Type+",
	modifier = choiceType(constantType "static", constantType "method"),
	container = "string",
})

REGISTER_TYPE("VariableIR", recordType {
	name = "string",
	type = "Type+",
	location = "string",
})

REGISTER_TYPE("ConstraintIR", choiceType(
	recordType {
		tag = constantType "this-constraint",
		instance = "VariableIR",
		name = "string",
	},
	recordType {
		tag = constantType "parameter-constraint",
		name = "string",
	},
	recordType {
		tag = constantType "concrete-constraint",
		interface = "ConcreteType+",
		concrete = "ConcreteType+",
	}
))

--------------------------------------------------------------------------------

REGISTER_TYPE("Type+", choiceType(
	"ConcreteType+", "KeywordType+", "GenericType+"
))

REGISTER_TYPE("ConcreteType+", recordType {
	tag = constantType "concrete-type+",

	name = "string",
	arguments = listType "Type+",

	location = "string",
})

REGISTER_TYPE("KeywordType+", recordType {
	tag = constantType "keyword-type+",

	name = "string",

	location = "string",
})

REGISTER_TYPE("GenericType+", recordType {
	tag = constantType "generic+",

	name = "string", -- e.g., "Foo" for `#Foo`

	location = "string",
})

--------------------------------------------------------------------------------

REGISTER_TYPE("ImplIR", choiceType(
	"LocalImplIR", "FieldImplIR", "BuildImplIR"
))

REGISTER_TYPE("LocalImplIR", recordType {
	tag = constantType "local-impl-ir",

	name = "string",
})

REGISTER_TYPE("FieldImplIR", recordType {
	tag = constantType "field-impl-ir",

	object = "string", -- IR variable
	field = "string", -- e.g., "#2"
})

REGISTER_TYPE("BuildImplIR", recordType {
	tag = constantType "build-impl-ir",

	base = "string",
	arguments = listType "ImplIR",
})

--------------------------------------------------------------------------------

-- TYPE Statement (ir-var = string)
-- tag: "var-ir" => name: ir-var, type: Type
-- tag: "string-load-ir" => dst: ir-var, value: string
-- tag: "number-load-ir" => dst: ir-var, value: number
-- tag: "call-ir" =>
--     func: string,
--     arguments: [ir-var],
--     dsts: [ir-var], 
--     constraints: [Impl],
-- tag: "interface-ir" =>
--     impl: Impl,
--     func: string,
--     arguments: [ir-var],
--     dsts: [ir-var],
-- tag: "new-ir" =>
--     record: {string (field name) => ir-var},
--     constraints: [Impl],
--     dst: ir-var,
-- tag: "field-ir" => dst: ir-var, object: ir-var, field: string
-- tag: "return-ir" => values: [ir-var]

--------------------------------------------------------------------------------

local Report = {}

function Report.TYPE_DEFINED_TWICE(first, second)
	assertis(first.name, "string")
	assertis(second.name, "string")
	assert(first.name == second.name)

	local name = first.name

	quit("The type `", name, "` was already defined ",
		first.location,
		".\nHowever, you are attempting to redefine it ",
		second.location)
end

function Report.GENERIC_DEFINED_TWICE(p)
	quit("The generic variable `#", p.name, "` was already defined ",
		p.firstLocation,
		".\nHowever, you are attempting to redefine it ",
		p.secondLocation)
end

function Report.MEMBER_DEFINED_TWICE(p)
	quit("The member `" .. p.name .. "` was already defined ",
		p.firstLocation,
		".\nHowever, you are attempting to redefine it ",
		p.secondLocation)
end

function Report.TYPE_BROUGHT_INTO_SCOPE_TWICE(p)
	p = freeze(p)
	local name = p.name
	local first = p.firstLocation
	local second = p.secondLocation
	assertis(name, "string")

	quit("TYPE BROUGHT INTO SCOPE TWICE")
end

function Report.UNKNOWN_TYPE_IMPORTED(p)
	p = freeze(p)
	quit("A type called `", p.name, "` has not been defined.",
		"\nHowever, you are trying to import it ", p.location)
end

function Report.UNKNOWN_PACKAGE_USED(p)
	p = freeze(p)
	quit("The package `", p.package, "` has not been imported.",
		"\nHowever, you are trying to use it ", p.location)
end

function Report.UNKNOWN_GENERIC_USED(p)
	quit("A generic variable called `#" .. p.name .. "` has not been defined.",
		"\nHowever, you are trying to use it ", p.location)
end

function Report.UNKNOWN_TYPE_USED(p)
	quit("No type called `" .. p.name .. "` has been defined.",
		"\nHowever, you are trying to use it ", p.location)
end

function Report.UNKNOWN_LOCAL_TYPE_USED(p)
	quit("There is no type called `" .. p.name .. "` in scope.",
		"\nHowever, you are trying to use it ", p.location)
end

function Report.INTERFACE_REQUIRES_MEMBER(p)
	quit("The class/union `", p.class, "` claims to implement interface",
		" `", p.interface, "` ", p.implementsLocation,
		"\nHowever, `" .. p.class .. "` does not implement the required",
		" member `" .. p.memberName .. "` which is defined ",
		p.memberLocation)
end

function Report.WRONG_ARITY(p)
	quit("The type `", p.name, "` was defined ", p.definitionLocation,
		"to take exactly ", p.expectedArity, " type arguments.",
		"\nHowever, it is provided with ", p.givenArity, " ",
		p.location)
end

function Report.INTERFACE_REQUIRES_MODIFIER(p)
	quit("The class/union `", p.class, "` claims to implement interface",
		" `", p.interface, "`.",
		"\nThe interface `", p.interface, "` defines a ", p.interfaceModifier,
		" member called `", p.name, "` ", p.interfaceLocation,
		"\nHowever, `", p.class, "` defines `", p.name, "` to be a ",
		p.classModifier, " ", p.classLocation)
end

function Report.INTERFACE_PARAMETER_COUNT_MISMATCH(p)
	quit("The class/union `", p.class, "` claims to implement interface",
		" `", p.interface, "`.",
		"\nThe interface `", p.interface, "` defines a member called `",
		p.name, "` with ", p.interfaceCount, " parameter(s) ",
		p.interfaceLocation,
		"\nHowever, `", p.class, "` defines `", p.name, "` with ",
		p.classCount, " parameter(s)", p.classLocation)
end

function Report.INTERFACE_PARAMETER_TYPE_MISMATCH(p)
	quit("The class/union `", p.class, "` claims to implement interface",
		" `", p.interface, "`.",
		"\nThe interface `", p.interface, "` defines a member called `",
		p.name, "` with the ", string.ordinal(p.index),
		" parameter of type `", p.interfaceType, "` ",
		p.interfaceLocation,
		"\nHowever, `", p.class, "` defines `", p.name, "` with the ",
		string.ordinal(p.index), " parameter of type `",
		p.classType, "` ", p.classLocation)
end

function Report.INTERFACE_RETURN_COUNT_MISMATCH(p)
	quit("The class/union `", p.class, "` claims to implement interface",
		" `", p.interface, "`.",
		"\nThe interface `", p.interface, "` defines a member called `",
		p.member, "` with ", p.interfaceCount, " return value(s) ",
		p.interfaceLocation,
		"\nHowever, `", p.class, "` defines `", p.member, "` with ",
		p.classCount, " return values(s) ", p.classLocation)
end

function Report.INTERFACE_RETURN_TYPE_MISMATCH(p)
	quit("The class/union `", p.class, "` claims to implement interface",
		" `", p.interface, "`.",
		"\nThe interface `", p.interface, "` defines a member called `",
		p.member, "` with the ", string.ordinal(p.index),
		" return-value of type `", p.interfaceType, "` ",
		p.interfaceLocation,
		"\nHowever, `", p.class, "` defines `", p.member, "` with the ",
		string.ordinal(p.index), " return-value of type `",
		p.classType, "` ", p.classLocation)
end

function Report.CONSTRAINTS_MUST_BE_INTERFACES(p)
	quit("Constraints must be interfaces.",
		"\nHowever, the ", p.is, " `", p.typeShown, "` is used as a constraint",
		p.location)
end

function Report.TYPE_MUST_IMPLEMENT_CONSTRAINT(p)
	quit("The type `", p.container, "` requires its ",
		string.ordinal(p.nth), " type-parameter to implement ", p.constraint,
		" ", p.cause,
		"\nHowever, the type `", p.type, "` does not implement `",
		p.constraint, "` ", p.location)
end

function Report.VARIABLE_DEFINITION_COUNT_MISMATCH(p)
	quit(p.valueCount, " value(s) are provided but ", p.variableCount,
		" variable(s) are defined ", p.location)
end

function Report.VARIABLE_DEFINED_TWICE(p)
	quit("The variable `", p.name, "` is first defined ", p.first,
		"While it is still in scope, you attempt to define another variable ",
		"with the same name ", p.second)
end

function Report.UNINSTANTIABLE_USED(p)
	quit("The type `", p.type, "` is not instantiable,",
		" so you cannot use it as the type of a variable or value as you are ",
		p.location)
end

function Report.WRONG_VALUE_COUNT(p)
	quit("The ", p.purpose, " needs ", p.expectedCount, " value(s),",
		" but was given ", p.givenCount, " ", p.location)
end

function Report.TYPES_DONT_MATCH(p)
	assertis(p.expectedType, "string")
	assertis(p.givenType, "string")
	assertis(p.location, "string")
	quit("The ", p.purpose, " expects `", p.expectedType, "` as defined ",
		p.expectedLocation,
		"\nHowever, `", p.givenType, "` was provided at ", p.location)
end

function Report.NO_SUCH_FIELD(p)
	quit("The type `", p.container, "` does not have a field called `",
		p.name, "`",
		"\nHowever, you try to access `", p.name, "` ", p.location)
end

function Report.NO_SUCH_VARIABLE(p)
	quit("There is no variable named `", p.name, "` in scope ", p.location)
end

function Report.NEW_USED_OUTSIDE_STATIC(p)
	quit("You can only use `new` expressions in static methods.",
		"\nHowever, you try to invoke `new` ", p.location)
end

function Report.NO_SUCH_METHOD(p)
	quit("The type `", p.type, "` does not have a ", p.modifier, " called `",
		p.name, "`",
		"\nHowever, you try to call `", p.type, ".", p.name, "` ", p.location)
end

function Report.CONFLICTING_INTERFACES(p)
	quit("The method `", p.method, "` is ambiguous ", p.location,
		"because `", p.method, "` is defined in both `", p.interfaceOne,
		"` and `", p.interfaceTwo, "`")
end

--------------------------------------------------------------------------------

-- RETURNS a Semantics, an IR description of the program
local function semanticsSmol(sources, main)
	assertis(main, "string")

	-- (1) Resolve the set of types and the set of packages that have been
	-- defined
	local isPackageDefined = {}
	local definitionSourceByFullName = {}
	for _, source in ipairs(sources) do
		local package = source.package
		assertis(package, "string")

		-- Mark this package name as defined
		-- Package names MAY be repeated between several sources
		isPackageDefined[package] = true

		-- Record the definition of all types in this package
		for _, definition in ipairs(source.definitions) do
			local fullName = package .. ":" .. definition.name

			-- Check that this type is not defined twice
			local previousDefinition = definitionSourceByFullName[fullName]
			if previousDefinition then
				Report.TYPE_DEFINED_TWICE(previousDefinition, definition)
			end

			definitionSourceByFullName[fullName] = definition
		end
	end

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

	-- (2) Fully qualify all local type names
	local allDefinitions = {}

	-- RETURNS whether or not the type is instantiable, meaning usable
	-- as a variable type or method parameter type
	local function isTypeInstantiable(t)
		assertis(t, "Type+")

		if t.tag == "concrete-type+" then
			-- Find whether or not it is an interface
			local definition = definitionSourceByFullName[t.name]
			if definition.tag == "interface-definition" then
				return false
			end
			return true
		elseif t.tag == "keyword-type+" then
			-- TODO: never type
			return true
		elseif t.tag == "generic+" then
			return true
		end
		error("unknown type tag")
	end

	local function verifyInstantiable(t)
		assertis(t, "Type+")

		if not isTypeInstantiable(t) then
			Report.UNINSTANTIABLE_USED {
				location = t.location,
				type = showType(t),
			}
		end
	end

	for _, source in ipairs(sources) do
		local package = source.package

		-- A bare `typename` should resolve to the type with name `typename`
		-- in package `packageScopeMap[typename].package`
		local packageScopeMap = {}
		local function defineLocalType(name, package, location)
			if packageScopeMap[name] then
				Report.TYPE_BROUGHT_INTO_SCOPE_TWICE {
					name = name,
					firstLocation = packageScopeMap[name].location,
					secondLocation = location,
				}
			end
			packageScopeMap[name] = {
				package = package,
				location = location,
			}
		end

		-- Only types in this set can be legally referred to
		local packageIsInScope = {
			[package] = true,
		}

		-- Bring each imported type/package into scope
		for _, import in ipairs(source.imports) do
			if import.class then
				-- Check that the type exists
				local importedFullName = import.package .. ":" .. import.class
				if not definitionSourceByFullName[importedFullName] then
					Report.UNKNOWN_TYPE_IMPORTED {
						location = import.location,
						name = importedFullName,
					}
				end

				defineLocalType(import.class, import.package, import.location)
			else
				-- Importing an entire package
				packageIsInScope[import.package] = true
			end
		end

		-- Bring each defined type into scope
		for _, definition in ipairs(source.definitions) do
			local location = definition.location
			defineLocalType(definition.name, source.package, location)
		end

		assertis(packageIsInScope, mapType("string", constantType(true)))

		-- RETURNS a Type+ with a fully-qualified name
		local function typeFinder(t, scope)
			assertis(scope, listType(recordType {name = "string"}))

			if t.tag == "concrete-type" then
				-- Search for the type in `type`
				local package = t.package
				if not package then
					package = packageScopeMap[t.base]
					if not package then
						Report.UNKNOWN_LOCAL_TYPE_USED {
							name = t.base,
							location = t.location,
						}
					end
					package = package.package
				elseif not packageIsInScope[package] then
					Report.UNKNOWN_PACKAGE_USED {
						package = package,
						location = t.location,
					}
				end
				assertis(package, "string")

				local fullName = package .. ":" .. t.base
				if not definitionSourceByFullName[fullName] then
					Report.UNKNOWN_TYPE_USED {
						name = fullName,
						location = t.location,
					}
				end

				return {tag = "concrete-type+",
					name = fullName,
					arguments = table.map(typeFinder, t.arguments, scope),
					location = t.location,
				}
			elseif t.tag == "generic" then
				-- Search for the name in `scope`
				if not table.findwith(scope, "name", t.name) then
					Report.UNKNOWN_GENERIC_USED(t)
				end

				return {tag = "generic+",
					name = t.name,
					location = t.location,
				}
			elseif t.tag == "type-keyword" then
				return {tag = "keyword-type+",
					name = t.name,
					location = t.location,
				}
			end
			error("unhandled ast type tag `" .. t.tag .. "`")
		end

		-- RETURNS a signature
		local function compiledSignature(signature, scope)
			assertis(scope, listType("TypeParameterIR"))

			local signature = freeze {
				foreign = signature.foreign,
				modifier = signature.modifier.keyword,
				name = signature.name,
				returnTypes = table.map(typeFinder, signature.returnTypes, scope),
				parameters = table.map(function(p)
					return {
						name = p.name,
						type = typeFinder(p.type, scope),
						location = p.location,
					}
				end, signature.parameters),
				location = signature.location,
			}

			-- Verify the signature only uses instantiable types
			for _, returnType in ipairs(signature.returnTypes) do
				verifyInstantiable(returnType)
			end
			for _, parameter in ipairs(signature.parameters) do
				verifyInstantiable(parameter.type)
			end

			return signature
		end

		-- RETURNS a list[TypeParameterIR]
		local function compiledGenerics(generics)
			local list = {}
			local map = {}
			for _, parameterAST in ipairs(generics.parameters) do
				local parameter = {
					name = parameterAST,
					constraints = {},
				}
				table.insert(list, parameter)

				-- Check for duplicates
				if map[parameter.name] then
					Report.GENERIC_DEFINED_TWICE {
						name = parameter.name,
						firstLocation = generics.location,
						secondLocation = generics.location,
					}
				end
				map[parameter.name] = parameter
			end

			-- Create a type-scope
			local typeScope = table.map(
				function(x) return {name = x} end,
				generics.parameters)
			
			-- Associate each constraint with a generic parameter
			for _, constraintAST in ipairs(generics.constraints) do
				local constraint = typeFinder(
					constraintAST.constraint, typeScope)

				-- Check that the named parameter exists
				local parameter = map[constraintAST.parameter]
				if not parameter then
					Report.UNKNOWN_GENERIC_USED(constraintAST.parameter)
				end

				-- Add this constraint to the associated generic parameter
				table.insert(parameter.constraints, {
					interface = constraint,
					location = constraintAST.location,
				})
			end

			return list
		end

		-- RETURNS a class+/union+
		local function compiledStruct(definition, tag)
			assertis(tag, "string")

			-- name, fields, generics, implements, signatures

			-- Create the full-name of the package
			local structName = package .. ":" .. definition.name

			-- Compile the set of generics introduced by this class
			local generics = compiledGenerics(definition.generics)

			local memberLocationMap = {}

			-- Compile the set of fields this class has
			local fields = {}
			for _, field in ipairs(definition.fields) do
				-- Check for duplicate members
				if memberLocationMap[field.name] then
					Report.MEMBER_DEFINED_TWICE {
						name = field.name,
						firstLocation = memberLocationMap[field.name],
						secondLocation = field.location,
					}
				end
				memberLocationMap[field.name] = field.location

				table.insert(fields, {
					name = field.name,
					type = typeFinder(field.type, generics),
					location = field.location,
				})

				verifyInstantiable(fields[#fields].type)
			end

			-- Collect the list of methods/statics this class provides
			local signatures = {}
			for _, method in ipairs(definition.methods) do
				-- Check for duplicate members
				local name = method.signature.name
				if memberLocationMap[name] then
					Report.MEMBER_DEFINED_TWICE {
						name = name,
						firstLocation = memberLocationMap[name],
						secondLocation = method.location,
					}
				end
				memberLocationMap[name] = method.location
				
				local signature = compiledSignature(method.signature, generics)
				signature = table.with(signature, "body", method.body)
				signature = table.with(signature, "typeFinder", typeFinder)
				signature = table.with(signature, "container", structName)
				table.insert(signatures, signature)
			end

			-- Compile the set of interfaces this class claims to implement
			local implements = table.map(
				typeFinder, definition.implements, generics)

			-- Create a set of constraints
			local constraints = {}
			for gi, generic in ipairs(generics) do
				for ci, constraint in ipairs(generic.constraints) do
					constraints["#" .. gi .. "_" .. ci] = constraint.interface
				end
			end

			return freeze {
				tag = tag,

				name = structName,
				generics = generics,
				fields = fields,
				signatures = signatures,
				implements = implements,

				constraints = constraints,

				location = definition.location,
			}
		end

		local function compiledInterface(definition)
			-- Create the fully qualified name
			local name = package .. ":" .. definition.name

			-- Create the generics
			local generics = compiledGenerics(definition.generics)

			local signatures = table.map(function(raw)
					local compiled = compiledSignature(raw, generics)
					return table.with(compiled, "container", name)
				end, definition.signatures)

			return freeze {
				tag = "interface",

				name = name,
				generics = generics,
				signatures = signatures,

				location = definition.location,
			}
		end

		-- Create an IR representation of each definition
		for _, definition in ipairs(source.definitions) do
			if definition.tag == "class-definition" then
				local compiled = compiledStruct(definition, "class")
				assertis(compiled, "ClassIR")

				table.insert(allDefinitions, compiled)
			elseif definition.tag == "interface-definition" then
				local compiled = compiledInterface(definition)
				assertis(compiled, "InterfaceIR")

				table.insert(allDefinitions, compiled)
			elseif definition.tag == "union-definition" then
				local compiled = compiledStruct(definition, "union")
				assertis(compiled, "UnionIR")

				table.insert(allDefinitions, compiled)
			else
				error("unknown definition tag `" .. definition.tag .. "`")
			end
		end
	end

	assertis(allDefinitions, listType "Definition")

	-- (3) Verify and record all interfaces implementation

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

	-- assignments: map string -> Type+
	-- RETURNS a function Type+ -> Type+ that substitutes the indicated
	-- types for generic variables.
	local function genericSubstituter(assignments)
		assertis(assignments, mapType("string", "Type+"))

		local function subs(t)
			assertis(t, "Type+")

			if t.tag == "concrete-type+" then
				return {tag = "concrete-type+",
					name = t.name,
					arguments = table.map(subs, t.arguments),
					location = t.location,
				}
			elseif t.tag == "keyword-type+" then
				return t
			elseif t.tag == "generic+" then
				if not assignments[t.name] then
					Report.UNKNOWN_GENERIC_USED(t)
				end
				return assignments[t.name]
			end
			error("unknown Type+ tag `" .. t.tag .. "`")
		end
		return subs
	end

	-- Verify that `class` actually implements each interface that it claims to
	-- RETURNS nothing
	local function checkStructImplementsClaims(class)
		for _, int in ipairs(class.implements) do
			local interfaceName = int.name
			local interface = table.findwith(
				allDefinitions, "name", interfaceName)
			-- TODO: check that it is an interface
			assert(interface)

			-- Instantiate each of the interface's type parameters with the
			-- argument specified in the "implements"
			local assignments = {}
			if #int.arguments ~= #interface.generics then
				Report.WRONG_ARITY {
					name = interface.name,
					givenArity = #int.arguments,
					expectedArity = #interface.generics,
					location = int.location,
					definitionLocation = interface.location,
				}
			end
			for i, argument in ipairs(int.arguments) do
				assignments[interface.generics[i].name] = argument
			end
			local subs = genericSubstituter(assignments)

			-- Check that each signature matches
			for _, iSignature in ipairs(interface.signatures) do
				-- Search for a method/static with the same name, if any
				local cSignature = table.findwith(
					class.signatures, "name", iSignature.name)
				if not cSignature then
					Report.INTERFACE_REQUIRES_MEMBER {
						class = class.name,
						interface = showType(int),
						implementsLocation = int.location,
						memberLocation = iSignature.location,
						memberName = iSignature.name,
					}
				end

				-- Check that the modifier matches
				if cSignature.modifier ~= iSignature.modifier then
					Report.INTERFACE_REQUIRES_MODIFIER {
						name = cSignature.name,
						class = class.name,
						interface = showType(int),
						classModifier = cSignature.modifier,
						interfaceModifier = iSignature.modifier,
						classLocation = cSignature.location,
						interfaceLocation = iSignature.location,
					}
				end

				-- Check that the parameters match
				if #cSignature.parameters ~= #iSignature.parameters then
					Report.INTERFACE_PARAMETER_COUNT_MISMATCH {
						class = class.name,
						classLocation = cSignature.location,
						classCount = #cSignature.parameters,
						interface = showType(int),
						interfaceLocation = iSignature.location,
						interfaceCount = #iSignature.parameters,
					}
				end
				for k, iParameter in ipairs(iSignature.parameters) do
					local iType = subs(iParameter.type)
					local cParameter = cSignature.parameters[k]
					local cType = cParameter.type
					if not areTypesEqual(iType, cType) then
						Report.INTERFACE_PARAMETER_TYPE_MISMATCH {
							class = class.name,
							classLocation = cParameter.location,
							classType = showType(cType),
							interface = showType(int),
							interfaceLocation = iParameter.location,
							interfaceType = showType(iType),
							index = k,
						}
					end
				end

				-- Check that the return types match
				if #cSignature.returnTypes ~= #iSignature.returnTypes then
					Report.INTERFACE_RETURN_COUNT_MISMATCH {
						class = class.name,
						interface = showType(int),
						classLocation = cSignature.location,
						interfaceLocation = iSignature.location,
						classCount = #cSignature.returnTypes,
						interfaceCount = #iSignature.returnTypes,
						member = cSignature.name,
					}
				end
				for k, cType in ipairs(cSignature.returnTypes) do
					local iType = subs(iSignature.returnTypes[k])
					if not areTypesEqual(iType, cType) then
						Report.INTERFACE_RETURN_TYPE_MISMATCH {
							class = class.name,
							interface = showType(int),
							classLocation = cType.location,
							interfaceLocation = iType.location,
							classType = showType(cType),
							interfaceType = showType(iType),
							index = k,
							member = cSignature.name,
						}
					end
				end
			end
		end
	end

	-- Verify all implementation claims
	for _, class in ipairs(allDefinitions) do
		if class.tag == "class" or class.tag == "union" then
			checkStructImplementsClaims(class)
		end
	end

	-- RETURNS a function Type+ -> Type+ to apply to types on the
	-- class/struct/interface's definition to use the specific types
	-- in this instance
	local function getSubstituterFromConcreteType(type)
		assertis(type, "ConcreteType+")

		local definition = table.findwith(allDefinitions, "name", type.name)

		local assignments = {}
		for i, generic in ipairs(definition.generics) do
			assignments[generic.name] = type.arguments[i]
		end
		return genericSubstituter(assignments)
	end

	-- RETURNS a list of constraints (as Type+) that the given type satisfies
	local function getTypeConstraints(type, scope)
		assertis(type, "Type+")
		assertis(scope, listType "TypeParameterIR")

		if type.tag == "concrete-type+" then
			local definition = table.findwith(allDefinitions, "name", type.name)
			if definition.tag ~= "union" and definition.tag ~= "class" then
				error(string.rep("?", 8000))
			end

			-- TODO: Is arity already checked?
			local substitute = getSubstituterFromConcreteType(type)

			local constraints = table.map(substitute, definition.implements)
			return constraints
		elseif type.tag == "keyword-type+" then
			error("TODO: getTypeConstraints(keyword-type+")
		elseif type.tag == "generic+" then
			local parameter = table.findwith(scope, "name", type.name)
			-- TODO: Are generics guaranteed to be in scope here?
			assert(parameter)

			return table.map(table.getter "interface", parameter.constraints)
		end
		error("unknown Type+ tag `" .. type.tag .. "`")
	end

	-- RETURNS nothing
	-- VERIFIES that the type satisfies the required constraint
	local function verifyTypeSatisfiesConstraint(type, constraint, scope, need)
		assertis(type, "Type+")
		assertis(constraint, "ConcreteType+")
		assertis(scope, listType "TypeParameterIR")
		assertis(need, recordType {
			container = "Definition",
			constraint = "Type+",
			nth = "integer",
		})

		for _, c in ipairs(getTypeConstraints(type, scope)) do
			if areTypesEqual(c, constraint) then
				return
			end
		end

		-- The type `type` does not implement the constraint `constraint`
		Report.TYPE_MUST_IMPLEMENT_CONSTRAINT {
			type = showType(type),
			constraint = showType(constraint),
			location = type.location,
			
			nth = need.nth,
			container = need.container.name,
			cause = need.constraint.location,
		}
	end

	-- RETURNS nothing
	-- VERIFIES that the type is entirely valid (in terms of scope, arity,
	-- and constraints)
	local function verifyTypeValid(type, scope)
		assertis(type, "Type+")
		assertis(scope, listType "TypeParameterIR")

		if type.tag == "concrete-type+" then
			local definition = table.findwith(allDefinitions, "name", type.name)
			local substitute = getSubstituterFromConcreteType(type)

			-- Check each argument
			for i, generic in ipairs(definition.generics) do
				local argument = type.arguments[i]
				verifyInstantiable(argument)

				-- Verify that the `i`th argument satisfies the constraints of
				-- the `i`th parameter
				for _, generalConstraint in ipairs(generic.constraints) do
					local constraint = substitute(generalConstraint.interface)

					-- TODO: better explain context
					verifyTypeSatisfiesConstraint(argument, constraint, scope, {
						container = definition,
						constraint = generalConstraint.interface,
						nth = i,
					})
				end

				-- Verify recursively
				verifyTypeValid(argument, scope)
			end
		elseif type.tag == "keyword-type+" then
			return -- All keyword types are valid
		elseif type.tag == "generic+" then
			return -- All generic literals are valid
		else
			error("unknown Type+ tag `" .. type.tag .. "`")
		end
	end

	-- (4) Verify all existing Type+'s (from headers) are OKAY
	for _, definition in ipairs(allDefinitions) do
		assertis(definition, "Definition")

		-- Verify that the generic constraints are valid
		for _, parameter in ipairs(definition.generics) do
			for _, constraint in ipairs(parameter.constraints) do
				verifyTypeValid(constraint.interface, definition.generics)
			end
		end

		if definition.tag == "class" then
			-- Verify each field
			for _, field in ipairs(definition.fields) do
				verifyTypeValid(field.type, definition.generics)
			end

			-- Verify each implements
			for _, implements in ipairs(definition.implements) do
				verifyTypeValid(implements, definition.generics)
			end

			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyTypeValid(parameter.type, definition.generics)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyTypeValid(returnType, definition.generics)
				end

				-- Verify the signature's body later
			end
		elseif definition.tag == "union" then
			-- Verify each field
			for _, field in ipairs(definition.fields) do
				verifyTypeValid(field.type, definition.generics)
			end

			-- Verify each implements
			for _, implements in ipairs(definition.implements) do
				verifyTypeValid(implements, definition.generics)
			end

			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyTypeValid(parameter.type, definition.generics)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyTypeValid(returnType, definition.generics)
				end
			end
		elseif definition.tag == "interface" then
			-- Verify each signature
			for _, signature in ipairs(definition.signatures) do
				-- Verify each signature parameter type
				for _, parameter in ipairs(signature.parameters) do
					verifyTypeValid(parameter.type, definition.generics)
				end

				-- Verify each signature return type
				for _, returnType in ipairs(signature.returnTypes) do
					verifyTypeValid(returnType, definition.generics)
				end
			end
		else
			error("unknown Definition tag `" .. definition.tag .. "`")
		end
	end

	-- (5) Compile all code bodies
	local function targetSignatureIdentifier(signature)
		assertis(signature, "Signature")

		return signature.container:gsub(":", "_") .. "_" .. signature.name
	end

	local STRING_TYPE = freeze {
		tag = "keyword-type+",
		name = "String",
		location = "???",
	}

	local NUMBER_TYPE = freeze {
		tag = "keyword-type+",
		name = "Number",
		location = "???",
	}

	local functions = {}

	local function definitionFromType(t)
		assertis(t, choiceType("ConcreteType+", "KeywordType+"))

		local definition = table.findwith(allDefinitions, "name", t.name)
		assert(definition, show(t)) -- Type Finder should verify that the type exists

		return definition
	end

	-- RETURNS a FunctionIR
	local function compileFunctionFromStruct(definition, signature)
		assertis(definition, choiceType("ClassIR", "UnionIR"))
		assertis(signature, "Signature")

		local containerType = freeze {
			tag = "concrete-type+",
			name = definition.name,
			arguments = table.map(function(p)
				return freeze {
					tag = "generic+",
					name = p.name,
					location = definition.location,
				}
			end, definition.generics),
			location = definition.location,
		}

		-- RETURNS a (verified) Type+
		local function findType(parsedType)
			local typeScope = definition.generics
			local outType = signature.typeFinder(parsedType, typeScope)
			verifyTypeValid(outType, definition.generics)
			return outType
		end

		-- RETURNS a variable or false
		local function getFromScope(scope, name)
			assertis(scope, listType(mapType("string", "object")))
			assertis(name, "string")

			for i = #scope, 1, -1 do
				if scope[i][name] then
					return scope[i][name]
				end
			end
			return nil
		end

		local idCount = 0
		-- RETURNS a unique (to this struct) local variable name
		local function generateLocalID()
			idCount = idCount + 1
			return "_local" .. tostring(idCount)
		end

		-- RETURNS a StatementIR representing the execution of statements in
		-- sequence
		local function buildBlock(statements)
			assertis(statements, listType("StatementIR"))

			local returned = "no"
			for i, statement in ipairs(statements) do
				if statement.returns == "yes" then
					assert(i == #statements)
					returned = "yes"
				elseif statement.returns == "maybe" then
					returned = "maybe"
				end
			end

			return freeze {
				tag = "block",
				returns = returned,
				statements = statements,
			}
		end

		-- RETURNS a LocalSt
		local function localSt(variable)
			assertis(variable, "VariableIR")

			return freeze {
				tag = "local",
				variable = variable,
				returns = "no",
			}
		end

		-- RETURNS a ConstraintIR
		local function constraintFrom(interface, implementer)
			assertis(interface, "Type+")
			assert(isTypeInstantiable(implementer))

			if implementer.tag == "concrete-type+" then
				if #implementer.arguments > 0 then
					error "TODO"
				end
				return freeze {
					tag = "concrete-constraint",
					interface = interface,
					concrete = implementer,
				}
			end
			print(show(interface))
			print(show(implementer))
			print(string.rep(".", 80))
			error("unhandled tag: " .. show(implementer))
		end

		-- RETURNS StatementIR, [Variable]
		local function compileExpression(pExpression, scope)
			assertis(pExpression, recordType {
				tag = "string"
			})
			assertis(scope, listType(mapType("string", "VariableIR")))

			if pExpression.tag == "string-literal" then
				local out = {
					name = generateLocalID(),
					type = STRING_TYPE,
					location = pExpression.location .. ">"
				}

				local block = buildBlock {
					localSt(out),
					{
						tag = "string",
						string = pExpression.value,
						destination = out,
						returns = "no",
					}
				}
				return block, freeze {out}
			elseif pExpression.tag == "number-literal" then
				local out = {
					name = generateLocalID(),
					type = NUMBER_TYPE,
					location = pExpression.location .. ">"
				}

				local block = buildBlock {
					localSt(out),
					{
						tag = "number",
						number = pExpression.value,
						destination = out,
						returns = "no",
					}
				}
				return block, freeze {out}
			elseif pExpression.tag == "new-expression" then
				local out = {
					name = generateLocalID(),
					type = containerType,
					location = pExpression.location .. ">"
				}
				assertis(out.type, "ConcreteType+")

				if signature.modifier ~= "static" then
					Report.NEW_USED_OUTSIDE_STATIC {
						location = pExpression.location,
					}
				end

				local newSt = {
					tag = "new",
					type = containerType,
					fields = {},
					returns = "no",
					constraints = {}
				}
				
				-- All of the constraints are provided as arguments to this
				-- static function
				for constraintName in pairs(definition.constraints) do
					newSt.constraints[constraintName] = freeze {
						tag = "parameter-constraint",
						name = constraintName,
					}
				end

				local evaluation = {}
				for _, argument in ipairs(pExpression.arguments) do
					local subEvaluation, subOut = compileExpression(
						argument.value, scope)
					if #subOut ~= 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "field value",
							expectedCount = 1,
							givenCount = #subOut,
							location = argument.location,
						}
					end
					
					table.insert(evaluation, subEvaluation)
					local field = table.findwith(definition.fields,
						"name", argument.name)

					if not field then
						Report.NO_SUCH_FIELD {
							name = argument.name,
							container = showType(containerType),
							location = argument.location,
						}
					end
					newSt.fields[argument.name] = subOut[1]

					if not areTypesEqual(field.type, subOut[1].type) then
						Report.TYPES_DONT_MATCH {
							purpose = "field type",
							expectedType = showType(field.type),
							expectedLocation = field.location,
							givenType = showType(subOut[1].type),
							location = argument.location,
						}
					end
				end

				local block = buildBlock(table.concatted(
					evaluation, {localSt(out), newSt}
				))
				return block, freeze {out}
			elseif pExpression.tag == "identifier" then
				local block = buildBlock({})
				local out = nil
				for i = #scope, 1, -1 do
					out = out or scope[i][pExpression.name]
				end
				if not out then
					Report.NO_SUCH_VARIABLE {
						name = pExpression.name,
						location = pExpression.location,
					}
				end
				return block, freeze {out}
			elseif pExpression.tag == "static-call" then
				local t = findType(pExpression.baseType)
				verifyInstantiable(t)

				if t.tag == "generic+" then
					error("TODO: static generic calls are different")
				end

				local baseDefinition = definitionFromType(t)

				local fullName = showType(t) .. "." .. pExpression.name

				-- Map type variables to the type-values used for this instantiation
				local substituter = getSubstituterFromConcreteType(t)

				local method = table.findwith(baseDefinition.signatures,
					"name", pExpression.name)
				
				if not method or method.modifier ~= "static" then
					Report.NO_SUCH_METHOD {
						modifier = "static",
						type = showType(t),
						name = pExpression.name,
						definitionLocation = baseDefinition.location,
						location = pExpression.location,
					}
				end

				-- Check the number of parameters
				if #method.parameters ~= #pExpression.arguments then
					Report.WRONG_ARGUMENT_COUNT {
						signatureCount = #method.parameter,
						argumentCount = #pExpression.arguments,
						location = pExpression.location,
					}
				end

				-- Evaluate the arguments
				local evaluation = {}
				local argumentSources = {}
				for i, argument in ipairs(pExpression.arguments) do
					local subEvaluation, outs = compileExpression(
						argument, scope
					)

					-- Verify each argument has exactly one value
					if #outs ~= 1 then
						Report.WRONG_VALUE_COUNT {
							purpose = "static argument",
							expectedCount = 1,
							givenCount = #outs,
							location = argument.location,
						}
					end

					-- Verify the type of the argument matches
					local arg = outs[1]
					local parameterType = substituter(method.parameters[i].type)
					if not areTypesEqual(arg.type, parameterType) then
						Report.TYPES_DONT_MATCH {
							purpose = string.ordinal(i) .. " argument to " .. fullName,
							expectedLocation = method.parameters[i].location,
							givenType = showType(arg.type),
							location = argument.location,
							expectedType = showType(parameterType)
						}
					end

					table.insert(evaluation, subEvaluation)
					table.insert(argumentSources, arg)
				end

				-- Collect the constraints
				local constraints = {}
				for gi, generic in ipairs(baseDefinition.generics) do
					for ci, constraint in ipairs(generic.constraints) do
						local key = "#" .. gi .. "_" .. ci
						constraints[key] = constraintFrom(constraint.interface, t.arguments[gi])
					end
				end

				-- Create variables for the output
				local outs = {}
				for _, returnType in pairs(method.returnTypes) do
					local returnVariable = {
						name = generateLocalID(),
						type = substituter(returnType),
						location = pExpression.location,
					}
					table.insert(outs, returnVariable)
					table.insert(evaluation, localSt(returnVariable))
				end

				table.insert(evaluation, {
					tag = "static-call",
					baseType = t,
					name = method.name,
					arguments = argumentSources,
					constraints = constraints,
					destinations = outs,
					returns = "no",
				})
				
				return buildBlock(evaluation), freeze(outs)
			elseif pExpression.tag == "method-call" then
				-- Compile the base instance
				local baseEvaluation, baseInstanceValues =
					compileExpression(pExpression.base, scope)
				if #baseInstanceValues ~= 1 then
					Report.WRONG_VALUE_COUNT {
						purpose = "method base expression",
						expectedCount = 1,
						givenCount = #baseInstanceValues,
						location = pExpression.location,
					}
				end
				local evaluation = {baseEvaluation}
				local baseInstance = baseInstanceValues[1]

				if baseInstance.type.tag == "generic+" then
					-- Generic instance
					local parameter = table.findwith(definition.generics,
						"name", baseInstance.type.name)
					assert(parameter)

					-- Find the constraint(s) which supply this method name
					local matches = {}
					for ci, constraint in ipairs(parameter.constraints) do
						local interface = definitionFromType(constraint.interface)
						local signature = table.findwith(interface.signatures, "name", pExpression.methodName)
						if signature then
							table.insert(matches, freeze {
								signature = signature,
								interface = interface,
								id = table.indexof(definition.generics, parameter) .. "_" .. ci
							})
						end
					end

					-- Verify exactly one constraint supplies this method name
					if #matches == 0 then
						Report.NO_SUCH_METHOD {
							modifier = "method",
							type = showType(baseInstance.type),
							name = pExpression.name,
							definitionLocation = baseDefinition.location,
							location = pExpression.location,
						}
					elseif #matches > 1 then
						Report.CONFLICTING_INTERFACES {
							method = pExpression.name,
							interfaceOne = showType(matches[1].interface),
							interfaceTwo = showType(matches[2].interface),
							location = pExpression.location,
						}
					end
					local method = matches[1]

					-- Verify the types of the arguments match the parameters
					-- Evaluate the arguments
					local arguments = {}
					for _, pArgument in ipairs(pExpression.arguments) do
						local subEvaluation, outs = compileExpression(pArgument, scope)
						
						-- Verify each argument has exactly one value
						if #outs ~= 1 then
							Report.WRONG_VALUE_COUNT {
								purpose = "method argument",
								expectedCount = 1,
								givenCount = #outs,
								location = pArgument.location,
							}
						end

						table.insert(arguments, outs[1])
						if not areTypesEqual(argument.type, method.parameters[i].type) then
							Report.TYPES_DONT_MATCH {
								purpose = string.ordinal(i) .. " argument to `" .. fullName .. "`",
								expectedType =	showType(method.parameters[i].type),
								expectedLocation = method.parameters[i].location,
								givenType = argument.type,
								location = pArgument.location,
							}
						end
						table.insert(evaluation, subEvaluation)
					end
					assertis(evaluation, listType "StatementIR")

					local destinations = {}
					for _, returnType in ipairs(method.signature.returnTypes) do
						local destination = {
							name = generateLocalID(),
							type = returnType,
							location = pExpression.location .. ">",
						}
						table.insert(destinations, destination)
						table.insert(evaluation, {
							tag = "local",
							variable = destination,
							returns = "no",
						})
					end

					local constraint = {
						tag = "this-constraint",
						instance = baseInstance,
						name = method.id,
					}

					table.insert(evaluation, {
						tag = "generic-method-call",
						baseInstance = baseInstance,
						constraint = constraint,
						name = pExpression.methodName,
						arguments = arguments,
						destinations = destinations,
						returns = "no",
					})

					return buildBlock(evaluation), destinations
				end
				assertis(arguments, listType "VariableIR")

				-- Concrete instance
				local baseDefinition = definitionFromType(baseInstance.type)
				
				-- Find the definition of the method being invoked
				local method = table.findwith(baseDefinition.signatures,
					"name", pExpression.methodName)
				if not method or method.modifier ~= "method" then
					Report.NO_SUCH_METHOD {
						modifier = "method",
						type = showType(t),
						name = pExpression.name,
						definitionLocation = baseDefinition.location,
						location = pExpression.location,
					}
				end

			elseif pExpression.tag == "keyword" then
				if pExpression.keyword == "false" then
					local boolean = {
						type = BOOLEAN_TYPE,
						name = generateLocalID(),
					}
					error "TODO"
				end
				error("TODO: keyword `" .. pExpression.keyword .. "`")
			end

			error("TODO expression: " .. show(pExpression))
		end

		-- RETURNS a StatementIR
		local function compileStatement(pStatement, scope)
			assertis(scope, listType(mapType("string", "VariableIR")))

			if pStatement.tag == "var-statement" then
				-- Allocate space for each variable on the left hand side
				local declarations = {}
				for _, pVariable in ipairs(pStatement.variables) do
					-- Verify that the variable name is not in scope
					local previous = getFromScope(scope, pVariable.name)
					if previous then
						Report.VARIABLE_DEFINED_TWICE {
							first = previous.location,
							second = pVariable.location,
							name = pVariable.name,
						}
					end

					-- Add the variable to the current scope
					local variable = {
						name = pVariable.name,
						type = findType(pVariable.type),
						location = pVariable.location,
					}
					verifyInstantiable(variable.type)
					
					scope[#scope][variable.name] = variable
					table.insert(declarations, {
						tag = "local",
						variable = variable,
						returns = "no",
					})
				end

				-- Evaluate the right hand side
				local evaluation, values =
					compileExpression(pStatement.value, scope) 

				-- Check the return types match the value types
				if #values ~= #declarations then
					Report.VARIABLE_DEFINITION_COUNT_MISMATCH {
						location = pStatement.location,
						expressionLocation = pStatement.value.location,
						variableCount = #declarations,
						valueCount = #values,
					}
				end

				-- Move the evaluations into the destinations
				local moves = {}
				for i, declaration in ipairs(declarations) do
					local variable = declaration.variable
					if not areTypesEqual(variable.type, values[i].type) then
						Report.TYPES_DONT_MATCH {
							purpose = "variable `" .. variable.name .. "`",
							expectedType = showType(variable.type),
							expectedLocation = variable.location,
							givenType = showType(values[i].type),
							location = pStatement.value.location,
						}
					end

					table.insert(moves, {
						tag = "assign",
						source = values[i],
						destination = variable,
						returns = "no",
					})
				end

				assertis(declarations, listType "StatementIR")
				assertis(evaluation, "StatementIR")
				assertis(moves, listType "StatementIR")
				
				-- Combine the three steps into a single sequence statement
				local sequence = table.concatted(
					declarations, {evaluation}, moves
				)
				return buildBlock(sequence)
			elseif pStatement.tag == "return-statement" then
				if #pStatement.values == 1 then
					local evaluation, sources = compileExpression(
						pStatement.values[1], scope)
					
					if #sources ~= #signature.returnTypes then
						Report.RETURN_COUNT_MISMATCH {
							signatureCount = #signature.returnTypes,
							returnCount = #sources,
							location = pStatement.location,
						}
					end

					return buildBlock(table.concatted({evaluation}, {
						tag = "return",
						sources = sources,
						returns = "yes",
					}))
				else
					error("TODO")
				end
			end
			error("TODO: compileStatement(" .. show(pStatement) .. ")")
		end

		-- RETURNS a BlockSt
		local function compileBlock(pBlock, scope)
			assertis(scope, listType(mapType("string", "VariableIR")))

			-- Open a new scope
			table.insert(scope, {})
		
			local statements = {}
			local returned = "no"
			for i, pStatement in ipairs(pBlock.statements) do
				-- This statement is unreachable, because the previous
				-- always returns
				if returned == "yes" then
					Report.UNREACHABLE_STATEMENT {
						cause = statements[i-1].location,
						reason = "always returns",
						unreachable = pStatement.location,
					}
				end

				local statement = compileStatement(pStatement, scope)
				assertis(statement, "StatementIR")
				
				if statement.returns == "yes" then
					returned = "yes"
				elseif statement.returns == "maybe" then
					returned = "maybe"
				end
				table.insert(statements, statement)
			end
			assertis(statements, listType "StatementIR")

			-- Close the current scope
			table.remove(scope)

			return freeze {
				tag = "block",
				statements = statements,
				returns = returned,
				location = pBlock.location,
			}
		end

		-- Collect static functions' type parameters from the containing class
		local generics = {}
		if signature.modifier == "static" then
			generics = definition.generics
		end

		-- Create the initial scope with the function's parameters
		local functionScope = {{}}
		for _, parameter in ipairs(signature.parameters) do
			functionScope[1][parameter.name] = parameter
		end

		local body = compileBlock(signature.body, functionScope)
		assertis(body, "StatementIR")

		return freeze {
			name = targetSignatureIdentifier(signature),
			
			-- Function's generics exclude those on the `this` instance
			generics = generics,
			
			parameters = signature.parameters,
			returnTypes = signature.returnTypes,

			body = body,
		}
	end

	-- Scan the definitions for all function bodies
	for _, definition in ipairs(allDefinitions) do
		if definition.tag == "class" or definition.tag == "union" then
			for _, signature in ipairs(definition.signatures) do
				local func = compileFunctionFromStruct(definition, signature)
				assertis(func, "FunctionIR")

				table.insert(functions, func)
			end
		end
	end
	
	assertis(functions, listType "FunctionIR")
end

-- Transpilation ---------------------------------------------------------------

local sourceFromSemantics = {}

-- RETURNS a string representing a Lua program with the indicated semantics
function sourceFromSemantics.lua(semantics)
	local output = {
		"-- THIS FILE GENERATED BY SMOL COMPILER:\n\t-- ",
		INVOKATION:gsub("\n", "\n\t-- "),
		"\n"
	}

	error("TODO")

	return table.concat(output)
end

-- Main ------------------------------------------------------------------------

if #arg ~= 2 then
	quit("USAGE:\n", "\tlua compiler.lua"
		.. " <directory containing .smol files>"
		.. " <mainpackage:Mainclass>"
		.. "\n\n\tFor example, `lua compiler.lua foo/ main:Main")
end
local directory = arg[1]
local mainFunction = arg[2]

-- Collect a set of source files to compile
local sourceFiles = {}
-- XXX: portability
local PATH_SEP = "/" -- XXX
for line in io.popen("ls " .. directory):lines() do -- XXX
	if line:match("^.+%.smol$") then
		table.insert(sourceFiles, {
			path = directory .. PATH_SEP .. line,
			short = line,
		})
	end
end

-- Load and parse source files
local sourceParses = {}
for _, sourceFile in ipairs(sourceFiles) do
	local file = io.open(sourceFile.path, "r")
	if not file then
		quit("The compiler could not open source file `", sourceFile.path, "`")
	end
	local contents = file:read("*all")
	file:close()

	-- Lex contents
	local tokens = lexSmol(contents, sourceFile.short)

	-- Parse contents
	table.insert(sourceParses, parseSmol(tokens))
end

local semantics = semanticsSmol(sourceParses, mainFunction)
