-- A transpiler for Smol -> ???
-- Curtis Fenner, copyright (C) 2017

local ARGV = arg

INVOKATION = ARGV[0] .. " " .. table.concat(ARGV, " ")
	.. "\non " .. os.date("!%c")
	.. "\nsmol version 0??"

--------------------------------------------------------------------------------

function import(name)
	local directory = ARGV[0]:gsub("[^/\\]+$", "")
	return dofile(directory .. name)
end

--------------------------------------------------------------------------------

local ansi = import "ansi.lua"

-- DISPLAYS the concatenation of the input,
-- and terminates the program.
-- DOES NOT RETURN.
function quit(first, ...)
	if not first:match("^[A-Z]+:\n$") then
		print(table.concat{ansi.red("ERROR"), ":\n", first, ...})
		os.exit(45)
	else
		print(table.concat{ansi.cyan(first), ...})
		os.exit(40)
	end
end

--------------------------------------------------------------------------------

import "extend.lua"
import "types.lua"

local parser = import "parser.lua"
local calculateSemantics = import "semantics.lua"
local codegen = {
	c = import "codegen/genc.lua",
}
local verify = import "verify.lua"

--------------------------------------------------------------------------------

local function quitUsage()
	quit("USAGE:\n", "\tlua compiler.lua"
		.. " --sources <sequence of one-or-more .smol files>"
		.. " --main <mainpackage:Mainclass>"
		.. "\n\n\tFor example, `lua compiler.lua --sources foo.smol --main main:Main`")
end

local commandMap = {}
local commandFlag = false
for i = 1, #ARGV do
	local flag = ARGV[i]:match("^%-%-(.*)$")
	if flag then
		if commandMap[flag] then
			quitUsage()
		end
		commandMap[flag] = {}
		commandFlag = flag
	elseif not commandFlag then
		quitUsage()
	else
		table.insert(commandMap[commandFlag], ARGV[i])
	end
end

-- Check the command line arguments
if not commandMap.main or #commandMap.main ~= 1 then
	quitUsage()
elseif not commandMap.sources or #commandMap.sources == 0 then
	quitUsage()
end

local LOCATION_MODE = "column"
if commandMap.location then
	-- TODO: assert that it is correct
	LOCATION_MODE = commandMap.location[1]
end

if commandMap.color then
	ansi.enabled = true
elseif commandMap.nocolor then
	ansi.enabled = false
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
		["if"] = true,
		["else"] = true,
		["elseif"] = true,
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

		-- verification
		["assert"] = true,
		["ensures"] = true,
		["requires"] = true,
		
		-- built-in types
		["Boolean"] = true,
		["Int"] = true,
		["Never"] = true,
		["String"] = true,
		["Unit"] = true,

		-- values
		["this"] = true,
		["true"] = true,
		["false"] = true,
		["unit"] = true,
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
			"[.,:;!|()%[%]{}]",
			function(x) return {tag = "punctuation"} end
		},
		{
			-- operators and assignment
			"[+%-*/<>=%%^]+",
			function(x)
				if x == "=" then
					return {tag = "assign"}
				end
				return {tag = "operator"}
			end
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
	if LOCATION_MODE == "index" then
		column = 0
	end
	local function advanceCursor(str)
		assert(isstring(str))
		for c in str:gmatch(".") do
			if c == "\r" then
				-- Carriage returns do not affect reported cursor location
			elseif c == "\n" then
				column = 1
				line = line + 1
				if LOCATION_MODE == "index" then
					column = 0
				end
			elseif c == "\t" and LOCATION_MODE ~= "index" then
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
		if LOCATION_MODE == "index" then
			location = location .. "@" .. filename .. ":" .. line .. ":" .. column
		end

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
	local K_BANG = parser.token(function(token)
		if token.lexeme == "!" then
			return true
		end
	end)

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

	local K_REQUIRES = LEXEME "requires"
	local K_ASSERT = LEXEME "assert"
	local K_ENSURES = LEXEME "ensures"

	-- Built-in types
	local K_STRING = LEXEME "String"
	local K_UNIT_TYPE = LEXEME "Unit"
	local K_NEVER = LEXEME "Never"
	local K_INT = LEXEME "Int"
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
			tag = "generic constraints",
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
			K_INT,
			K_BOOLEAN,
			K_UNIT_TYPE,
			K_NEVER,
			-- User defined types
			parser.map(T_GENERIC, function(x)
				return {tag = "generic", name = x}
			end, true),
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
			tag = "***list of type arguments",
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

		["interface-signature"] = parser.composite {
			tag = "***signature",
			{"#signature", parser.named "signature"},
			{"_", K_SEMICOLON, "`;` after interface method"},
		},

		-- Represents a function signature, including name, scope,
		-- parameters, and return type.
		["signature"] = parser.composite {
			tag = "signature",
			{"modifier", parser.named "method-modifier"},
			{"name", T_IDENTIFIER, "a method name"},
			{"bang", parser.optional(K_BANG)},
			{"_", K_ROUND_OPEN, "`(` after method name"},
			{"parameters", parser.query "variable,0+"},
			{"_", K_ROUND_CLOSE, "`)` after method parameters"},
			{
				"returnTypes",
				parser.query "type,1+",
				"a return type"
			},
			{"requires", parser.zeroOrMore(parser.named "requires")},
			{"ensures", parser.zeroOrMore(parser.named "ensures")},
		},

		["requires"] = parser.composite {
			tag = "requires",
			{"_", K_REQUIRES},
			{"#expression", parser.named "expression", "an expression"},
		},
		["ensures"] = parser.composite {
			tag = "ensures",
			{"_", K_ENSURES},
			{"#expression", parser.named "expression", "an expression"},
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
			parser.named "if-statement",
			parser.named "match-statement",
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
			{"elseifs", parser.query "else-if-clause*"},
			{"else", parser.query "else-clause?"},
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
			{"variable", T_IDENTIFIER, "expected a variable name"},
			{"variant", T_IDENTIFIER, "expected a union tag name"},
			{"body", parser.named "block", "expected a block to follow case"},
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

		-- Expressions!
		["expression"] = parser.map(parser.composite {
			tag = "***expression",
			{"base", parser.named "atom"},
			{"operations", parser.query "operation*"},
		}, function(x)
			-- XXX: no precedence yet; assume left-associative
			local out = x.base
			assertis(out.tag, "string")

			if #x.operations >= 2 then
				quit("You must explicitly parenthesize the operators ", x.operations[2].location)
			end

			for _, operation in ipairs(x.operations) do
				out = {
					tag = "binary",
					left = out,
					right = operation.operand,
					operator = operation.operator,
				}
				assert(isstring(out.operator))
			end
			assert(out)
			return out
		end, true),

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
		end, true),

		["method-access"] = parser.composite {
			tag = "method-call",
			{"_", K_DOT},
			{"methodName", T_IDENTIFIER, "a method/field name"},
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
			tag = "field",
			{"_", K_DOT},
			{"field", T_IDENTIFIER, "a field name"},
		},

		["access"] = parser.choice {
			parser.named "method-access",
			parser.named "field-access"
		},

		["static-call"] = parser.composite {
			tag = "static-call",
			{"baseType", parser.named "type"},
			{"_", K_DOT, "`.` after type name"},
			{"funcName", T_IDENTIFIER, "a static method's name"},
			{"bang", parser.optional(K_BANG)},
			{"_", K_ROUND_OPEN, "`(` after static method name"},
			{"arguments", parser.query "expression,0+"},
			{"_", K_ROUND_CLOSE, "`)` to end static method call"},
		},

		["atom-base"] = parser.choice {
			parser.named "new-expression",
			K_THIS,
			K_TRUE,
			K_FALSE,
			K_UNIT_VALUE,
			parser.map(T_STRING_LITERAL, function(v)
				return {tag = "string-literal", value = v}
			end, true),
			parser.map(T_INTEGER_LITERAL, function(v)
				return {tag = "int-literal", value = v}
			end, true),
			parser.named "static-call",
			parser.map(T_IDENTIFIER, function(n)
				return {tag = "identifier", name = n}
			end, true),
			parser.composite {
				tag = "***parenthesized expression",
				{"_", K_ROUND_OPEN},
				{"#expression", parser.named "expression", "expression"},
				{"_", K_ROUND_CLOSE, "`)`"},
			},
			K_RETURN,
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
	interfaces = listType "InterfaceIR",
	builtins = listType(recordType {
		tag = constantType "builtin",
		name = "string",
		signatures = listType "Signature",
		type = "KeywordType+",
	}),
	unions = listType "UnionIR",
	functions = listType "FunctionIR",
	main = choiceType("string", constantType(false)),
})

REGISTER_TYPE("ClassIR", recordType {
	tag = constantType "class",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "InterfaceType+",
	signatures = listType "Signature",
	constraints = mapType("string", "InterfaceType+"),
	builtin = constantType(nil),
})

REGISTER_TYPE("UnionIR", recordType {
	tag = constantType "union",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "InterfaceType+",
	signatures = listType "Signature",	
	constraints = mapType("string", "InterfaceType+"),
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
		interface = "InterfaceType+",
	}),
})

REGISTER_TYPE("FunctionIR", recordType {
	name = "string",
	parameters = listType "VariableIR",
	generics = listType "TypeParameterIR",
	returnTypes = listType "Type+",
	body = choiceType(constantType(false), "BlockSt"),
	signature = "Signature",
	definitionName = "string",
})

REGISTER_TYPE("Signature", recordType {
	name = "string",
	parameters = listType "VariableIR",
	returnTypes = listType "Type+",
	modifier = choiceType(constantType "static", constantType "method"),
	container = "string",
	foreign = "boolean",
	bang = "boolean",
	requires = listType "ASTExpression",
	ensures = listType "ASTExpression",
})

REGISTER_TYPE("ASTExpression", recordType {
	tag = "string",
	-- TODO
})

REGISTER_TYPE("maybe", choiceType(
	constantType "yes",
	constantType "no",
	constantType "maybe"
))

REGISTER_TYPE("StatementIR", intersectType("AbstractStatementIR", choiceType(
	-- Execution
	"AssignSt",
	"BlockSt",
	"BooleanLoadSt",
	"FieldSt",
	"GenericMethodCallSt",
	"GenericStaticCallSt",
	"LocalSt",
	"MatchSt",
	"MethodCallSt",
	"NewClassSt",
	"NewUnionSt",
	"IntLoadSt",
	"ReturnSt",
	"IfSt",
	"StaticCallSt",
	"StringLoadSt",
	"ThisSt",
	"UnitSt",
	"VariantSt",

	-- Verification
	"AssumeSt",
	"VerifySt",

	-- Nothing
	"NothingSt"
)))

REGISTER_TYPE("AbstractStatementIR", recordType {
	tag = "string",
	returns = "maybe",
})

EXTEND_TYPE("AssumeSt", "AbstractStatementIR", recordType {
	tag = constantType "assume", 
	body = "StatementIR",
	variable = "VariableIR",
	location = "string",
})

EXTEND_TYPE("VerifySt", "AbstractStatementIR", recordType {
	tag = constantType "verify",
	body = "StatementIR",
	variable = "VariableIR",
	location = "string",
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

EXTEND_TYPE("IfSt", "AbstractStatementIR", recordType {
	tag = constantType "if",
	condition = "VariableIR",
	bodyThen = "StatementIR",
	bodyElse = "StatementIR",
})

EXTEND_TYPE("IntLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "int",
	number = "number",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NewClassSt", "AbstractStatementIR", recordType {
	tag = constantType "new-class",
	fields = mapType("string", "VariableIR"),
	type = "ConcreteType+",
	constraints = mapType("string", "ConstraintIR"),
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NewUnionSt", "AbstractStatementIR", recordType {
	tag = constantType "new-union",
	type = "ConcreteType+",
	field = "string",
	value = "VariableIR",
	constraints = mapType("string", "ConstraintIR"),
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("StaticCallSt", "AbstractStatementIR", recordType {
	tag = constantType "static-call",
	constraints = mapType("string", "ConstraintIR"),
	baseType = "Type+",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	staticName = "string",
})

EXTEND_TYPE("MethodCallSt", "AbstractStatementIR", recordType {
	tag = constantType "method-call",
	baseInstance = "VariableIR",
	methodName = "string",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("GenericMethodCallSt", "AbstractStatementIR", recordType {
	tag = constantType "generic-method-call",
	baseInstance = "VariableIR",
	constraint = "ConstraintIR",
	methodName = "string",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("GenericStaticCallSt", "AbstractStatementIR", recordType {
	tag = constantType "generic-static-call",
	constraint = "ConstraintIR",
	staticName = "string",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("BooleanLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "boolean",
	boolean = "boolean",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("FieldSt", "AbstractStatementIR", recordType {
	tag = constantType "field",
	name = "string",
	base = "VariableIR",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("ThisSt", "AbstractStatementIR", recordType {
	tag = constantType "this",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("UnitSt", "AbstractStatementIR", recordType {
	tag = constantType "unit",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("VariantSt", "AbstractStatementIR", recordType {
	tag = constantType "variant",
	destination = "VariableIR",
	base = "VariableIR",
	variant = "string",
	returns = constantType "no",
})

EXTEND_TYPE("MatchSt", "AbstractStatementIR", recordType {
	tag = constantType "match",
	base = "VariableIR",
	cases = listType(recordType {
		variant = "string",
		statement = "StatementIR",
	}),
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
		interface = "InterfaceType+",
		name = "string",
	},
	recordType {
		tag = constantType "parameter-constraint",
		interface = "InterfaceType+",
		name = "string",
	},
	recordType {
		tag = constantType "concrete-constraint",
		interface = "InterfaceType+",
		concrete = "ConcreteType+",
		assignments = mapType("string", "ConstraintIR"),
	}
))

--------------------------------------------------------------------------------

REGISTER_TYPE("Type+", choiceType(
	"ConcreteType+", "KeywordType+", "GenericType+"
))

REGISTER_TYPE("InterfaceType+", recordType {
	tag = constantType "interface-type",
	name = "string",
	arguments = listType "Type+",
	location = "string",
})

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

-- Main ------------------------------------------------------------------------

local function commonPrefix(list)
	assert(#list >= 1)
	local out = list[1]
	for i = 2, #list do
		while list[i]:sub(1, #out) ~= out do
			-- Shorten
			out = out:sub(1, -2)
		end
	end
	return out
end

local common = commonPrefix(commandMap.sources):gsub("%.[a-zA-Z0-9]+$", ""):gsub("[a-zA-Z_0-9]+$", "")
local sourceFiles = {}
for _, source in ipairs(commandMap.sources) do
	table.insert(sourceFiles, {
		path = source,
		short = source:sub(#common + 1),
	})
end

table.insert(sourceFiles, {
	path = "<compiler-core>",
	short = "<compiler-core>",
	contents = [[
package core;

class Out {
	foreign static println!(message String) Unit;
}

class Array[#T] {
	foreign static make() Array[#T];
	foreign method get(index Int) #T;
	foreign method set(index Int, value #T) Array[#T];
	foreign method append(value #T) Array[#T];
	foreign method pop() Array[#T];
	foreign method size() Int;

	method swap(a Int, b Int) Array[#T] {
		return this.set(a, this.get(b)).set(b, this.get(a));
	}
}

class ASCII {
	foreign static formatInt(value Int) String;
}

class ArrayShower[#T | #T is Showable] {
	static inner(array Array[#T], index Int) String {
		if array.size() == index {
			return "";
		} elseif index == 0 {
			return array.get(0).show() ++ ArrayShower[#T].inner(array, 1);
		}
		return (", " ++ array.get(index).show()) ++ ArrayShower[#T].inner(array, index + 1);
	}

	static show(array Array[#T]) String {
		var inner String = ArrayShower[#T].inner(array, 0);
		return ("[" ++ inner) ++ "]";
	}
}

interface Showable {
	static showType() String;
	method show() String;
}

union Option[#T] {
	var some #T;
	var none Unit;

	static makeSome(value #T) Option[#T] {
		return new(some = value);
	}

	static makeNone() Option[#T] {
		return new(none = unit);
	}
}

interface Orderable[#T] {
	// RETURNS true when this is smaller than other in this ordering.
	method lessThan(other #T) Boolean;
}

interface Eq[#T] {
	// RETURNS true when these elements are equal such that
	// (a == b) => f(a) == f(b)
	method eq(other #T) Boolean;
}

]]
})

-- Load and parse source files
local sourceParses = {}
for _, sourceFile in ipairs(sourceFiles) do
	local contents = sourceFile.contents
	if not contents then
		local file, err = io.open(sourceFile.path, "r")
		if not file then
			quit("The compiler could not open source file `", sourceFile.path, "`")
		end
		contents = file:read("*all")
		file:close()
		if not contents then
			quit("The compiler could not read from the source file `", sourceFile.path, "`")
		end
	end
	assert(contents)

	-- Lex contents
	local tokens = lexSmol(contents, sourceFile.short)

	-- Parse contents
	table.insert(sourceParses, parseSmol(tokens))
end

assert(#commandMap.main == 1)
local mainFunction = commandMap.main[1]

local semantics = calculateSemantics.semantics(sourceParses, mainFunction)

verify(semantics)

if semantics.main then
	-- TODO: read target
	local arguments = {out = "output.c"}
	local TARGET = "c"
	codegen[TARGET](semantics, arguments)
else
	print("Successfully compiled " .. #sourceFiles .. " file(s)")
end
