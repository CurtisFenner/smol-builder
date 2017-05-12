-- A transpiler for Smol -> ???
-- Curtis Fenner, copyright (C) 2017

local INVOKATION = arg[0] .. " " .. table.concat(arg, ", ")
	.. "\non " .. os.date("!%c")
	.. "\nsmol version 0??"

--------------------------------------------------------------------------------

if arg[#arg] == "--profile" then
	-- Enable profiling
	table.remove(arg)

-- <profiler.lua> --------------------------------------------------------------

	local profile = {}
	profile.paused = true
	profile.stack = {}
	profile.aliases = {}
	profile.heavy = {clock = 0, count = 1, beginClock = os.clock()}

	function profile.noteStack()
		local leafFrame = profile.stack[#profile.stack]
		local elapsed = leafFrame.endClock - leafFrame.beginClock

		-- Increment the total clock for all functions in the stack
		local leaf = profile.heavy
		leaf.aliases = {["<root>"] = true, "<root>"}
		
		-- Clock
		for _, frame in ipairs(profile.stack) do
			leaf[frame.id] = leaf[frame.id] or {count = 0, clock = 0}
			leaf = leaf[frame.id]

			-- Clock totals
			leaf.aliases = profile.aliases[frame.id]
		end

		-- Increment the coun for the leaf frame
		leaf.count = leaf.count + 1
		leaf.clock = leaf.clock + elapsed
	end

	function profile.hook(event)
		-- XXX: assumes coroutines aren't used, who knows how coroutines affect
		-- this!

		if profile.paused then
			return
		end
		profile.paused = true
		-- Cease

		if event == "call" then
			local info = debug.getinfo(2)
			local id = info.source .. ":" .. tostring(info.linedefined)
			if info.source == "=[C]" then
				id = "[C] " .. tostring(info.func)
			end
			local alias = info.name
			if not info.namewhat:find("%S") then
				alias = "<anonymous>"
			end

			-- Record the name
			profile.aliases[id] = profile.aliases[id] or {}
			if not profile.aliases[id][alias] then
				profile.aliases[id][alias] = true
				table.insert(profile.aliases[id], alias)
			end

			table.insert(profile.stack, {
				id = id,
				alias = alias,
				beginClock = os.clock(),
			})
		else
			if #profile.stack > 0 then
				-- Record the elapsed time / count
				profile.stack[#profile.stack].endClock = os.clock()

				profile.noteStack()
				table.remove(profile.stack)
			else
				profile.heavy.clock = os.clock() - profile.heavy.beginClock
				print("\n--profile GENERATING PROFILE REPORT:")
				print("\n--profile PROFILE REPORT `"
					.. profile.report() .. "` GENERATED.")
				profile.paused = true
				return
			end
		end

		-- Continue 
		profile.paused = false
	end
	function profile.report()
		local function jsonify(object, out)
			assert(type(out) == "table")

			if type(object) == "number" or type(object) == "boolean" then
				table.insert(out, tostring(object))
			elseif type(object) == "string" then
				table.insert(out, '"' .. object .. '"') -- XXX
			else
				assert(type(object) == "table", "got " .. type(object))
				if #object > 0 then
					table.insert(out, "[")
					local first = true
					for _, value in ipairs(object) do
						if not first then
							table.insert(out, ", ")
						end
						first = false
						jsonify(value, out)
					end
					table.insert(out, "]\n")
				else
					table.insert(out, "{")
					local first = true
					for key, value in pairs(object) do
						if not first then
							table.insert(out, ", ")
						end
						first = false
						assert(type(key) == "string")
						table.insert(out, '"')
						table.insert(out, key)
						table.insert(out, '":')
						jsonify(value, out)
					end
					table.insert(out, "}\n")
				end
			end
		end

		-- JSONify the profile and write it to a file
		local filename = "profiled.js" -- .. tostring(os.time()) .. ".js"
		local report = io.open(filename, "wb")
		local out = {}
		jsonify(profile.heavy, out)
		report:write("profiledata(\n")
		report:write(table.concat(out))
		report:write("\n);\n")
		report:close()

		return filename
	end

	debug.sethook(profile.hook, "cr")
	-- Begin
	profile.paused = false

-- </profiler.lua> -------------------------------------------------------------

end

--------------------------------------------------------------------------------

-- DISPLAYS the concatenation of the input,
-- and terminates the program.
-- DOES NOT RETURN.
local function quit(...)
	print(table.concat{...})
	os.exit(1)
end

local debugPrint = function() end

setmetatable(_G, {
	__index = function(_, key)
		error("read of global key `" .. tostring(key) .. "`", 2)
	end,
	__newindex = function(_, key)
		error("write to global key `" .. tostring(key) .. "`", 2)
	end,
})

setmetatable(string, {
	__index = function(_, key)
		error("strings have no `" .. tostring(key) .. "` field", 2)
	end,
})

function string.prepad(str, with, length)
	assert(type(with) == "string", "with must be string")
	assert(type(length) == "number", "length must be number")
	assert(#with == 1, "TODO: support #with > 1")

	return string.rep(with, length - #str) .. str
end

function string.postpad(str, with, length)
	assert(type(with) == "string", "with must be string")
	assert(type(length) == "number", "length must be number")
	assert(#with == 1, "TODO: support #with > 1")

	return str .. string.rep(with, length - #str)
end

-- Redefine `pairs` to use `__pairs` metamethod
local oldp41rs = pairs
local function pairs(object)
	assert(type(object) == "table" or type(object) == "userdata",
		"object must be table or userdata in pairs()")
	-- TODO: deal with locked metatables
	local metatable = getmetatable(object)
	if metatable and metatable.__pairs then
		return metatable.__pairs(object)
	end
	return oldp41rs(object)
end

-- Redefine `ipairs` to respect `__index` metamethod
local ipairs
do
	local function iterator(list, i)
		if list[i+1] == nil then
			return nil
		end
		return i+1, list[i+1]
	end
	ipairs = function(list)
		return iterator, list, 0
	end
end

--------------------------------------------------------------------------------

-- RETURNS a string representing a literal 'equivalent' to the object
-- (excluding references and non-serializable objects like functions)
local show
do
	local escapedCharacter = {
		["\a"] = [[\a]],
		["\b"] = [[\b]],
		["\f"] = [[\f]],
		["\n"] = [[\n]],
		["\r"] = [[\r]],
		["\t"] = [[\t]],
		["\v"] = [[\v]],
		["\\"] = [[\\]],
		["\""] = [[\"]],
		["\0"] = [[\0]],
	}
	for i = 0, 31 do
		local c = string.char(i)
		if not escapedCharacter[c] then
			escapedCharacter[c] = "\\" .. tostring(i):prepad("0", 3)
		end
	end
	for i = 128, 255 do
		escapedCharacter[string.char(i)] = "\\" .. tostring(i)
	end
	local function showAdd(object, out)
		if type(object) == "string" then
			-- Turn into a string literal
			table.insert(out, [["]])
			for character in object:gmatch "." do
				table.insert(out, escapedCharacter[character] or character)
			end
			table.insert(out, [["]])
		elseif type(object) == "table" or type(object) == "userdata" then
			table.insert(out, "{ ")
			for key, value in pairs(object) do
				table.insert(out, "[")
				showAdd(key, out)
				table.insert(out, "]=")
				showAdd(value, out)
				table.insert(out, ", ")
			end
			table.insert(out, "}")
		else
			table.insert(out, tostring(object))
		end
	end

	show = function(object)
		local out = {}
		showAdd(object, out)
		return table.concat(out)
	end
end

local function freeze(object)
	assert(type(object) == "table" or type(object) == "userdata")

	local out = newproxy(true)
	local metatable = getmetatable(out)
	metatable.__index = function(_, key)
		if object[key] == nil then
			local available = {}
			for key, value in pairs(object) do
				table.insert(available,
					tostring(key) .. "=" .. tostring(value))
			end

			if type(key) == "number" then
				-- XXX: allow reading one past end of arrays
				local previous = object[key-1]
				if previous ~= nil then
					return nil
				end
			end
			error("frozen object has no field `"
				.. tostring(key) .. "`: available `"
				.. show(object) .. "`", 2)
		end
		return object[key]
	end
	metatable.__newindex = function(_, key)
		error("cannot write to field `"
			.. tostring(key) .. "` on frozen object", 2)
	end
	metatable.__pairs = function()
		return pairs(object)
	end
	metatable.__len = function()
		return #object
	end
	
	return out
end

-- Lexer -----------------------------------------------------------------------

-- RETURNS a list of tokens.
-- source: the contents of a source file.
-- filename: a human-readable name indicating this source file.
local function lexSmol(source, filename)
	assert(type(source) == "string")
	assert(type(filename) == "string")

	-- Normalize line end-ings
	source = source:gsub("\r*\n\r*", "\n")
	source = source:gsub("\r", "\n")
	source = source .. "\n"

	local IS_KEYWORD = {
		case = true,
		class = true,
		["do"] = true,
		foreign = true,
		import = true,
		interface = true,
		is = true,
		match = true,
		method = true,
		new = true,
		package = true,
		["return"] = true,
		static = true,
		this = true,
		union = true,
		var = true,
		-- built-in types
		String = true,
		Number = true,
		Boolean = true,
		Unit = true,
		Never = true,
	}

	-- Define token parsing rules
	local TOKENS = {
		{ -- local type
			"[A-Z][A-Za-z0-9]*",
			function(x) return {tag = "typename", name = x} end
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
		{ -- generic parameters
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
			"//[^\n]*",
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

	local tokens = {}
	-- Track the location into the source file each token is
	local line = 1
	local column = 1
	local function advanceColumn(str)
		assert(type(str) == "string" and #str >= 1)
		if #str == 1 then
			if str == "\r" then
			elseif str == "\t" then
				column = column + 4 -- XXX: fix this
			else
				column = column + 1
			end
			return
		end
		for c in str:gmatch(".") do
			advanceColumn(c)
		end
	end

	while #source > 0 do
		-- Compute human-readable description of location
		local context = source:gsub("%s+", " ")
		if #context > 35 then
			context = context:sub(1, 35-3) .. "..."
		end
		local location = "at " .. filename .. ":" .. line .. ":" .. column
			.. "\n\t(near `" .. context .. "`)"

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
					quit("found an unfinished string literal" .. location)
				end
				if escaped then
					if not SPECIAL[c] then
						quit("unknown escape sequence `\\"
							.. c .. "`" .. location)
					end
					content = content .. SPECIAL[c]
					escaped = not escaped
				elseif c == BACKSLASH then
					escaped = true
				elseif c == QUOTE then
					-- Update location
					advanceColumn(source:sub(1, i))
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
					for c in match:gmatch(".") do
						if c == "\n" then
							line = line + 1
							column = 1
						else
							advanceColumn(c)
						end
					end
					source = source:sub(#match+1)

					matched = true
					break
				end
			end

			-- Check for an unlexible piece of source
			if not matched then
				quit("could not recognize any token " .. location
					.. " (near `" .. source:sub(1, 15) .. "...`)")
			end
		end
	end

	return tokens
end

-- Stream ----------------------------------------------------------------------

-- REPRESENTS a streamable sequence of tokens
local function Stream(list, offset)
	offset = offset or 0
	assert(type(list) == "table", "list must be table")
	assert(type(offset) == "number", "offset must be number")
	for i = 1, #list do
		assert(type(list[i].location) == "string",
			"token must have string location; ") -- .. show(list[i]))
		assert(type(list[i].lexeme) == "string",
			"token must have string lexeme; ") -- .. show(list[i]))
	end

	return {
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

-- Parser ----------------------------------------------------------------------

local function parseSmol(tokens)
	local stream = Stream(tokens)

	local function parserGenerator(grammar)
		local parsers = {}
		for key, value in pairs(grammar) do
			assert(type(value) == "function",
				"parser for `" .. key .. "` must be a function")

			parsers[key] = value
		end

		return parsers
	end

	-- PARSER for a sequence of 0 or more `object`s separated by nothing
	local function zeroOrMore(object)
		assert(type(object) == "function")

		return function(stream, parsers)
			assert(parsers)

			local list = {}
			while true do
				local element, rest = object(stream, parsers)
				if not rest then
					-- no more elements can be parsed
					return list, stream
				end

				-- add the element to the list
				table.insert(list, element)
				stream = rest
			end
		end
	end

	-- PARSER for `parser` but applying `f` to the returned object
	local function parserMap(parser, f)
		assert(type(parser) == "function")
		assert(type(f) == "function")
		return function(stream, parsers)
			assert(parsers)
			local object, rest = parser(stream, parsers)
			if not rest then
				return nil
			end

			return f(object), rest
		end
	end

	-- PARSER for `parser` but only extracting `field`
	local function parserExtractor(parser, field)
		assert(type(field) == "string")
		return parserMap(parser, function(x)
			return x[field]
		end)
	end

	-- PARSER for trying each option in order upon failure
	local function choice(options)
		assert(type(options) == "table")
		assert(#options >= 1)
		for i = 1, #options do
			assert(type(options[i]) == "function",
				"option " .. i .. " must be a parser")
		end

		return function(stream, parsers)
			assert(parsers)

			for _, option in ipairs(options) do
				local element, rest = option(stream, parsers)
				if rest then
					return element, rest
				end
			end
			return nil
		end
	end

	-- PARSERS a sequence of members into a dictionary
	-- INVALIDATES `components` input table
	local function composite(components)
		-- validate input
		assert(type(components) == "table")
		assert(type(components.tag) == "string",
			"components.tag must be string")

		-- A human readable context of the fields
		local context = " in " .. components.tag

		for i = 1, #components do
			assert(#components[i] >= 2)
			assert(type(components[i][1]) == "string",
				"component must provide key as string")
			assert(components[i][1] ~= "tag",
				"component cannot use key 'tag'")
			assert(components[i][1] ~= "location",
				"component cannot use key 'location'")

			assert(type(components[i][2]) == "function",
				"component must provide member as parser"
				.. " (key `" .. components[i][1] .. "`"
				.. "; " .. i .. " of " .. #components ..  ")")

			assert(#components[i] <= 3)
			assert(components[i][3] == nil
				or type(components[i][3]) == "string")
		end

		return function(stream, parsers)
			-- Annotate metadata
			local object = {
				tag = components.tag,
				location = stream:location(),
			}

			-- Parse fields in sequence
			for _, component in ipairs(components) do
				-- Attempt to parse one field
				local key = component[1]
				local memberParser = component[2]
				local required = component[3]

				local member, rest = memberParser(stream, parsers)

				if rest then
					-- Attach (non-underscore) field to object
					if key ~= "_" then
						object[key] = member
					end
					stream = rest
				elseif required then
					-- This member was a required cut
					quit("expected ", required, context, " ", stream:location())
				else
					-- This failed to parse
					return nil
				end
			end

			-- Successfully parsed all components
			return freeze(object), stream
		end
	end

	-- PARSER for `object` or <nothing>
	local function optional(object)
		assert(type(object) == "function")

		return function(stream, parsers)
			assert(parsers)

			local element, rest = object(stream, parsers)
			if not rest then
				return false, stream
			end
			return element, rest
		end
	end

	-- PARSER for `name` grammar
	local function G(name)
		assert(type(name) == "string", "name must be string")

		return function(stream, parsers)
			assert(parsers)
			assert(parsers[name], "parser for `" .. name .. "` must be defined")

			return parsers[name](stream, parsers)
		end
	end

	-- PARSER for literal lexeme (keywords, punctuation, etc.)
	local function LEXEME(lexeme)
		assert(type(lexeme) == "string", "lexeme must be string")

		return function(stream, parsers)
			assert(stream, "stream!")
			assert(parsers, "parsers!")
			if stream:size() == 0 then
				return nil
			end
			if stream:head().lexeme == lexeme then
				debugPrint("LEXEME", lexeme, stream:location())
				return stream:head(), stream:rest()
			end
			return nil
		end
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
	local K_UNION = LEXEME "union"
	local K_VAR = LEXEME "var"

	-- Built-in types
	local K_STRING = LEXEME "String"
	local K_UNIT = LEXEME "Unit"
	local K_NEVER = LEXEME "Never"
	local K_NUMBER = LEXEME "Number"
	local K_BOOLEAN = LEXEME "Boolean"

	-- PARSER for token tag ("typename", "identifier", "operator", etc)
	local function TOKEN(tokenType)
		assert(type(tokenType) == "string", "tokenType must be string")

		return function(stream, parsers)
			assert(parsers)
			if stream:size() == 0 then
				return nil
			end
			if stream:head().tag == tokenType then
				debugPrint("TOKEN", tokenType, stream:location())
				return stream:head(), stream:rest()
			end
			return nil
		end
	end
	local T_IDENTIFIER = TOKEN "identifier"
	local T_TYPENAME = TOKEN "typename"
	local T_GENERIC = TOKEN "generic"
	local T_INTEGER_LITERAL = TOKEN "integer-literal"
	local T_STRING_LITERAL = TOKEN "string-literal"
	local T_OPERATOR = TOKEN "operator"

	-- HELPER meaning object repeated 0 or more times,
	-- separated by commas
	local function commad(object, count, expected)
		assert(type(object) == "function", "object must be function")
		assert(type(expected) == "string", "expected must be string")
		assert(type(count) == "string", "count format must be string")
		assert(type(count) == "string", "count format must be string")
		local minCount = 0
		local maxCount = math.huge
		local matchAtLeast = count:match("^(%d+)%+$")
		if matchAtLeast then
			minCount = tonumber(matchAtLeast)
		else
			error("unknown comma'd count pattern `" .. count .. "`")
		end

		return function(stream, parsers)
			assert(parsers)

			-- Consume the first element of the list
			local first, rest = object(stream, parsers)
			if not rest then
				if minCount <= 0 and 0 <= maxCount then
					return {}, stream
				end
				return nil
			end
			stream = rest

			local list = {first}
			while true do
				-- Consume a comma
				local _, rest = K_COMMA(stream, parsers)
				if not rest then
					if minCount <= #list and #list <= maxCount then
						return list, stream
					end
					return nil
				end
				stream = rest

				-- Consume an object
				local element, rest = object(stream, parsers)
				if not rest then
					-- After a comma, an object of the proper
					-- type must follow
					quit("expected " .. expected .. " after `,` at "
						.. stream:location())
				end
				table.insert(list, element)
				stream = rest
			end
		end
	end

	-- DEFINES the grammar for the language
	local parsers = parserGenerator {
		-- Represents an import
		import = composite {
			tag = "import",
			{"_", K_IMPORT},
			{"name", T_IDENTIFIER, "an imported package name"},
			{"class", optional(parserExtractor(composite { -- string | false
				tag = "***type name",
				{"_", K_DOT},
				{"class", T_TYPENAME, "a type name"},
			}, "class"))},
			{"_", K_SEMICOLON, "`;` after import"},
		},

		variable = composite {
			tag = "variable",
			{"name", T_IDENTIFIER},
			{"type", G "type", "a type after variable name"},
		},

		-- Type
		type = choice {
			-- Built in special types
			K_STRING,
			K_NUMBER,
			K_BOOLEAN,
			K_UNIT,
			K_NEVER,
			-- User defined types
			T_GENERIC,
			G "concrete-type",
		},
		["concrete-type"] = composite {
			tag = "concrete-type",
			{"scope", optional(G "scope")}, --: string | false
			{"base", T_TYPENAME}, --: {lexeme = string}
			{"arguments", optional(G "type-arguments")}, --: [ Type ]
		},
		["scope"] = parserExtractor(composite {
			tag = "scope",
			{"name", T_IDENTIFIER},
			{"_", K_SCOPE},
		}, "name"),
		["type-arguments"] = parserExtractor(composite {
			tag = "***",
			{"_", K_SQUARE_OPEN},
			{"arguments", commad(G "type", "1+", "type argument"), "type arguments"},
			{"_", K_SQUARE_CLOSE, "`]` to end type arguments"},
		}, "arguments"),

		-- Represents a generics definition
		generics = composite {
			tag = "generics",
			{"_", K_SQUARE_OPEN},
			{
				"parameters",
				commad(T_GENERIC, "1+", "generic parameter variable"),
				"generic parameter variables"
			},
			{"constraints", optional(G "generic-constraints")},
			{"_", K_SQUARE_CLOSE, "`]` to end list of generics"},
		},
		["generic-constraints"] = parserExtractor(composite {
			tag = "***",
			{"_", K_PIPE},
			{
				"constraints",
				commad(G "generic-constraint", "1+", "generic constraint"),
				"generic constraints"
			},
		}, "constraints"),
		["generic-constraint"] = composite {
			tag = "constraint",
			{"parameter", T_GENERIC},
			{"_", K_IS, "`is` after generic parameter"},
			{"constraint", G "type", "a type constrain after `is`"},
		},

		-- Represents a union
		union = composite {
			tag = "union",
			{"_", K_UNION},
			{"name", T_TYPENAME, "a type name"},
			{"generics", optional(G "generics")},
			{"_", K_CURLY_OPEN, "`{` to begin union body"},
			{"fields", zeroOrMore(G "field-definition")},
			{"methods", zeroOrMore(G "method-definition")},
			{"_", K_CURLY_CLOSE, "`}` to close union body"},
		},

		-- Represents a class
		class = composite {
			tag = "class-definition",
			{"_", K_CLASS},
			{"name", T_TYPENAME, "a type name"},
			{"generics", optional(G "generics")},
			{"implements", optional(G "implements")},
			{"_", K_CURLY_OPEN, "`{` to begin class body"},
			{"fields", zeroOrMore(G "field-definition")},
			{"methods", zeroOrMore(G "method-definition")},
			{"_", K_CURLY_CLOSE, "`}` to close class body"},
		},
		implements = parserExtractor(composite {
			tag = "***implements",
			{"_", K_IS},
			{
				"interfaces",
				commad(G "concrete-type", "1+", "an interface name")
			},
		}, "interfaces"),
		["field-definition"] = composite {
			tag = "field-definition",
			{"_", K_VAR},
			{"name", T_IDENTIFIER, "the field's name after `var`"},
			{"type", G "type", "the field's type after field name"},
			{"_", K_SEMICOLON, "`;` after field type"},
		},
		["method-definition"] = composite {
			tag = "method-definition",
			{"signature", G "signature"},
			{"body", G "block", "a method body"},
		},

		-- Statements!
		block = composite {
			tag = "block",
			{"_", K_CURLY_OPEN},
			{"statements", zeroOrMore(G "statement")},
			{"_", K_CURLY_CLOSE, "`}` to end statement block"},
		},
		statement = choice {
			G "return-statement",
			G "do-statement",
			G "var-statement",
			G "assign-statement",
		},
		["return-statement"] = composite {
			tag = "return-statement",
			{"_", K_RETURN},
			{"values", commad(G "expression", "0+", "an expression to return")},
			{"_", K_SEMICOLON, "`;` to end return-statement"},
		},
		["do-statement"] = composite {
			tag = "do-statement",
			{"_", K_DO},
			{
				"expression",
				G "expression",
				"an expression to execute after `do`"
			},
			{"_", K_SEMICOLON, "`;` to end do-statement"},
		},
		["assign-statement"] = composite {
			tag = "assign-statement",
			{"variables", commad(G "expression", "1+", "a variable")},
			{"_", K_EQUAL, "`=` after variable"},
			{"value", G "expression", "an expression after `=`"},
			{"_", K_SEMICOLON, "`;` to end assign-statement"},
		},
		["var-statement"] = composite {
			tag = "var-statement",
			{"_", K_VAR},
			{"name", T_IDENTIFIER, "a variable name after `var`"},
			{"type", G "type", "the variable's type after variable's name"},
			{"_", K_EQUAL, "`=` after the variable in the var-statement"},
			{"value", G "expression", "an expression after `=`"},
			{"_", K_SEMICOLON, "`;` to end var-statement"},
		},

		-- Expressions!
		expression = parserMap(composite {
			tag = "***expression",
			{"base", G "atom"},
			{"operations", zeroOrMore(G "operation")},
		}, function(x)
			-- XXX: no precedence yet; assume left-associative
			local out = x.base
			assert(out)
			for _, operation in ipairs(x.operations) do
				out = {
					tag = "binary",
					left = out,
					right = operation.operand,
					operator = operation.operator.lexeme,
				}
				assert(type(out.operator) == "string")
				if out.left.tag == "binary" then
					if out.left.operator ~= out.operator then
						print("warning: operator precedence is not yet implemented")
					end
				end
			end
			assert(out)
			return out
		end),
		operation = composite {
			tag = "***operation",
			{"operator", T_OPERATOR},
			{"operand", G "atom", "atom after operator"},
		},

		["new-expression"] = composite {
			tag = "new-expression",
			{"_", K_NEW},
			{"_", K_ROUND_OPEN, "`(` after `new`"},
			{
				"arguments",
				commad(G "named-argument", "0+", "a constructor argument")
			},
			{"_", K_ROUND_CLOSE, "`)` to end `new` expression"},
		},
		["named-argument"] = composite {
			tag = "named-argument",
			{"name", T_IDENTIFIER},
			{"_", K_EQUAL},
			{"value", G "expression", "an expression after `=`"},
		},

		atom = parserMap(composite {
			tag = "***atom",
			--
			{"base", G "atom-base"},
			{"accesses", zeroOrMore(G "access")},
		}, function(x)
			local out = x.base
			for _, access in ipairs(x.accesses) do
				out = {
					tag = "access",
					base = out,
					access = access,
				}
			end
			return out
		end),

		access = parserMap(composite {
			tag = "***call",
			{"_", K_DOT},
			{"name", T_IDENTIFIER, "a method/field name"},
			-- N.B.: Optional, since a field access is also possible...
			{"call", optional(composite{
				tag = "***arguments",
				{"_", K_ROUND_OPEN},
				{"arguments", commad(G "expression", "0+", "an expression")},
				{"_", K_ROUND_CLOSE, "`)` to end"},
			})},
		}, function(x)
			if x.call then
				return {
					tag = "call",
					arguments = x.call.arguments,
					name = x.name,
				}
			end
			return {
				tag = "field",
				name = x.name,
			}
		end),

		["atom-base"] = choice {
			G "new-expression",
			K_THIS,
			T_STRING_LITERAL,
			T_INTEGER_LITERAL,
			composite { -- static method call
				tag = "static-call",
				{"base-type", G "type"},
				{"_", K_DOT, "`.` after type name"},
				{"name", T_IDENTIFIER, "a static method's name"},
				{"_", K_ROUND_OPEN, "`(` after static method name"},
				{"arguments", commad(G "expression", "0+", "an expression")},
				{"_", K_ROUND_CLOSE, "`)` to end static method call"},
			},
			T_IDENTIFIER,
			parserExtractor(composite {
				tag = "***parenthesized expression",
				{"_", K_ROUND_OPEN},
				{"expression", G "expression", "expression"},
				{"_", K_ROUND_CLOSE, "`)`"},
			}, "expression"),
		},

		-- Represents an interface
		interface = composite {
			tag = "interface-definition",
			{"_", K_INTERFACE},
			{"name", T_TYPENAME, "a type name"},
			{"generics", optional(G "generics")},
			{"_", K_CURLY_OPEN, "`{` to begin interface body"},
			{"signatures", zeroOrMore(G "interface-signature")},
			{"_", K_CURLY_CLOSE, "`}` to end interface body"},
		},
		["interface-signature"] = parserExtractor(composite {
			tag = "***signature",
			{"signature", G "signature"},
			{"_", K_SEMICOLON, "`;` after interface method"},
		}, "signature"),

		-- Represents a function signature, including name, scope,
		-- parameters, and return type.
		signature = composite {
			tag = "signature",
			{"foreign", optional(K_FOREIGN)},
			{"modifier", G "method-modifier"},
			{"name", T_IDENTIFIER, "a method name"},
			{"_", K_ROUND_OPEN, "`(` after method name"},
			{"parameters", commad(G "variable", "0+", "a parameter")},
			{"_", K_ROUND_CLOSE, "`)` after method parameters"},
			{
				"returns",
				commad(G "type", "1+", "a return type"),
				"a return type"
			},
		},

		["method-modifier"] = choice {
			K_METHOD,
			K_STATIC,
		},

		-- Represents a top-level definition
		definition = choice {
			G "class",
			G "union",
			G "interface",
		},

		-- Represents a package declaration
		package = composite {
			tag = "package",
			{"_", K_PACKAGE},
			{"name", T_IDENTIFIER, "an identifier"},
			{"_", K_SEMICOLON, "`;` to finish package declaration"},
		},

		-- Represents an entire source file
		program = composite {
			tag = "program",
			{"package", G "package", "a package definition to begin file"},
			{"imports", zeroOrMore(G "import")},
			{"definitions", zeroOrMore(G "definition")},
		},
	}

	-- Sequence of definitions
	local program, rest = parsers.program(stream, parsers)
	assert(rest ~= nil)
	if rest:size() ~= 0 then
		quit("expected another definition at " .. rest:location())
	end

	return program
end

-- Semantics / Verification ----------------------------------------------------

-- RETURNS a semantic description of the program
local function semanticsSmol(sources, main)
	assert(type(main) == "string")

	local output = {}
	error("TODO")
	return output
end

-- Transpilation ---------------------------------------------------------------

local sourceFromSemantics = {}

-- TYPE Semantics
-- Semantics.structs : [Struct]
-- Semantics.unions : [Union]
-- Semantics.interfaces : [Interface]
-- Semantics.functions : [Function]
-- Semantics.main : string

-- TYPE Struct
-- Struct.name: string
-- Struct.fields: [{name: string, type: string}]
-- Struct.typeParameters: [string]
-- Struct.typeConstraints: [{parameter: string, constraint: string}]
-- Struct.implements: [string]

-- TYPE Interface
-- Interface.name: string
-- Interface.methods: [ {
--     name: string,
--     parameters: [string],
--     returnTypes: [string],
--     static: boolean
-- } ]
-- Interface.parameters: [string]
-- Interface.constraints: [{parameteR: string, constraint: string}]

-- TYPE Function
-- Function.name: string
-- Function.parameters: [{name: string, type: string}]
-- Function.typeParameters: [string] | false
-- Function.typeConstraints: [{parameter: string, constraint: string}] | false
-- Function.returnType: string
-- Function.body: Statement

-- TYPE Statement
-- tag: "var" | "string" | "number" | "new" | "interface-static"
--    | "field" | "call" | "interface-method" | "return"

-- RETURNS a string representing a Lua program with the indicated semantics
function sourceFromSemantics.lua(semantics)

	local function luaizeFunction(name)
		assert(type(name) == "string", "luaizeFunction requires string")

		return (name:gsub(":", "_"))
	end

	local function luaizeConstraint(name)
		if type(name) == "string" then
			assert(type(name) == "string", "luaizeConstraint requires string")
			assert(name:sub(1, 1) == "#")

			return "_con_" .. name:sub(2)
		end
		local base = name.type
		local interface = name.interface
		assert(type(base) == "string")
		assert(type(interface) == "string")

		return "impl_" .. luaizeFunction(interface)
			.. "_for_".. luaizeFunction(base)
	end

	-- Lua target may ignore
	-- semantics.structs, semantics.unions, semantics.interfaces

	local output = {
		"-- THIS FILE GENERATED BY SMOL COMPILER:\n\t-- ",
		INVOKATION:gsub("\n", "\n\t-- "),
		"\n"
	}
	local function outputHeader(name)
		local line = "\n-- " .. name .. " "
		table.insert(output, line:postpad("-", 80))
		table.insert(output, "\n\n")
	end

	local function generateStatement(statement, indentation)
		assert(type(statement.tag) == "string")
		if statement.tag == "block" then
			-- XXX: always implicitly surrounded by Lua block
			for _, s in ipairs(statement.statements) do
				generateStatement(s, indentation .. "\t")
			end
		elseif statement.tag == "var" then
			table.insert(output, indentation)
			table.insert(output, "local " .. statement.name)
			table.insert(output, "\n")		
		elseif statement.tag == "string" then
			assert(type(statement.value) == "string")

			table.insert(output, indentation)
			table.insert(output, statement.dst .. " = ")
			table.insert(output, "{value = ")
			table.insert(output, show(statement.value))
			table.insert(output, "}")
			table.insert(output, "\n")			
		elseif statement.tag == "field" then
			local field = statement.name
			local object = statement.object
			assert(type(field) == "string")
			assert(type(object) == "string")

			table.insert(output, indentation)
			table.insert(output,
				statement.dst .. " = " .. object .. "." .. field)
			table.insert(output, "\n")
		elseif statement.tag == "number" then
			table.insert(output, indentation)
			table.insert(output, statement.dst .. " = ")
			table.insert(output, "{value = ")
			table.insert(output, show(statement.value))
			table.insert(output, "}")
			table.insert(output, "\n")
		elseif statement.tag == "interface-method" then
			local methodName = statement.name
			assert(type(methodName) == "string")
			local object = statement.object
			assert(type(object) == "string")
			local argumentList = statement.arguments

			local interfaceInformation = statement.interface
			assert(#interfaceInformation == 2)
			
			local methodLua = interfaceInformation[1]
				.. "['" .. interfaceInformation[2] .. "']."
				.. methodName

			local arguments = {object}
			for _, argument in ipairs(argumentList) do
				table.insert(arguments, argument)
			end

			table.insert(output, indentation)
			table.insert(output, statement.dst .. " = " .. methodLua)
			table.insert(output, "(")
			table.insert(output, table.concat(arguments, ", "))
			table.insert(output, ")\n")
		elseif statement.tag == "call" then
			assert(type(statement.func) == "string")
			assert(statement.dsts, show(statement))

			-- Constraint arguments come after
			local arguments = {}
			for _, argument in ipairs(statement.arguments) do
				table.insert(arguments, argument)
			end
			for _, constraint in ipairs(statement.constraints) do
				if type(constraint) == "string" then
					table.insert(arguments, luaizeConstraint(constraint))
				else
					table.insert(arguments, luaizeConstraint(constraint))
				end
			end

			-- Destination variables
			table.insert(output, indentation)
			for i = 1, #statement.dsts do
				table.insert(output, statement.dsts[i])
				if i == #statement.dsts then
					table.insert(output, " = ")
				else
					table.insert(output, ", ")
				end
			end

			-- Lua function invocation
			table.insert(output, luaizeFunction(statement.func))
			table.insert(output, "(")
			table.insert(output, table.concat(arguments, ", "))
			table.insert(output, ")\n")
		elseif statement.tag == "return" then
			table.insert(output, indentation)
			table.insert(output, "return ")
			table.insert(output, table.concat(statement.values, ", "))
			table.insert(output, "\n")
		elseif statement.tag == "new" then
			table.insert(output, indentation)
			table.insert(output, statement.dst .. " =")
			table.insert(output, "{ ")
			for key, value in pairs(statement.record) do
				table.insert(output, key .. " = " .. value .. "; ")
			end
			assert(statement.constraints ~= nil)
			for i, constraint in ipairs(statement.constraints) do
				table.insert(output, "['#" .. i .. "'] = ")
				table.insert(output, luaizeConstraint(constraint))
				table.insert(output, "; ")
			end

			table.insert(output, "}\n")
		else
			error("unknown statement tag `" .. statement.tag .. "`")
		end
	end

	outputHeader("Foreign functions")
	-- Body of all foreign functions / types
	table.insert(output, [[
-- method Number:show() String
function Number_show(number)
	return {value = tostring(number.value)}
end

-- method String:concat(String) String
function String_concat(left, right)
	return {value = left.value .. right.value}
end

-- static system:Out:println(String) Unit
function system_Out_println(str)
	print(str.value)
end

-- Number is coding:Showable
impl_coding_Showable_for_Number = {
	show = Number_show;
}

]])

	-- Forward declare all functions
	outputHeader("Function forward declarations")
	for _, fn in ipairs(semantics.functions) do
		table.insert(output, "local " .. luaizeFunction(fn.name) .. ";\n")
	end

	-- Forward declare all impls
	outputHeader("Interface impl forward declarations")
	for _, struct in ipairs(semantics.structs) do
		for _, impl in ipairs(struct.implements) do
			table.insert(output, "local ")
			table.insert(output, luaizeConstraint{
				type = struct.name, interface = impl
			})
			table.insert(output, ";\n")
		end
	end

	-- Define the body of each function
	outputHeader("Function definitions")
	for _, fn in ipairs(semantics.functions) do
		-- Collect type-parameters and type-constraints as Lua parameters
		local allParameters = {}
		for _, parameter in ipairs(fn.parameters) do
			assert(type(parameter.name) == "string")
			assert(type(parameter.type) == "string")
			table.insert(allParameters, parameter.name)
		end
		if fn.typeParameters then
			for _, typeParameter in ipairs(fn.typeParameters) do
				assert(type(typeParameter) == "string")
				assert(typeParameter:sub(1, 1) == "#")
			end
			for _, typeConstraint in ipairs(fn.typeConstraints) do
				local constraintOn = typeConstraint.parameter
				assert(type(constraintOn) == "string",
					"function typeConstraint.parameter must be string")

				local constraintName = typeConstraint.name
				assert(type(constraintName) == "string")
				assert(constraintName:sub(1, 1) == "#")

				local constraintType = typeConstraint.constraint

				table.insert(allParameters, luaizeConstraint(constraintName))
			end
		end

		-- Generate Lua function signature
		table.insert(output, luaizeFunction(fn.name) .. " = function(")
		table.insert(output, table.concat(allParameters, ", "))
		table.insert(output, ")\n")
		table.insert(output, "\tlocal _;\n")

		for _, parameter in ipairs(allParameters) do
			table.insert(output, "\tassert(nil ~= " .. parameter .. ")\n")
		end

		-- Generate Lua body
		generateStatement(fn.body, "")

		-- Generate closing of Lua function
		table.insert(output, "end\n\n")
	end

	-- Initialize all impls
	outputHeader("Initialize impls")

	for _, struct in ipairs(semantics.structs) do
		for _, impl in ipairs(struct.implements) do
			-- Search for the interface with the given name
			local interfaces = {}
			for _, interface in ipairs(semantics.interfaces) do
				if interface.name == impl then
					table.insert(interfaces, interface)
				end
			end
			assert(#interfaces == 1)
			local interface = interfaces[1]
			
			table.insert(output,
				luaizeConstraint{type = struct.name, interface = impl})
			table.insert(output, " = {\n")
			for _, method in ipairs(interface.methods) do
				table.insert(output, "\t")
				table.insert(output, method.name)
				table.insert(output, " = ")
				table.insert(output,
					luaizeFunction(struct.name .. ":" .. method.name))
				table.insert(output, ",\n")
			end
			table.insert(output, "}\n\n")
		end
	end

	outputHeader("Main Entry")

	table.insert(output, luaizeFunction(semantics.main .. ":main"))
	table.insert(output, "()\n")

	return table.concat(output)
end

-- Main ------------------------------------------------------------------------

if #arg ~= 2 then
	quit("usage:\n\tlua compiler.lua"
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
		quit("could not open source file `" .. sourceFile.path .. "`")
	end
	local contents = file:read("*all")
	file:close()

	-- Lex contents
	local tokens = lexSmol(contents, sourceFile.short)

	-- Parse contents
	table.insert(sourceParses, parseSmol(tokens))
end

--local semantics = semanticsSmol(sourceParses, mainFunction)
