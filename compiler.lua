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
local function quit(first, ...)
	if not first:match("^[A-Z]+:\n$") then
		print(table.concat{"ERROR:\n", first, ...})
	else
		print(table.concat{first, ...})
	end
	os.exit(1)
end

local debugPrint = function() end

-- Prevent the use of global variables
setmetatable(_G, {
	__index = function(_, key)
		error("read of global key `" .. tostring(key) .. "`", 2)
	end,
	__newindex = function(_, key)
		error("write to global key `" .. tostring(key) .. "`", 2)
	end,
})

-- Prevent (unintentional) accesses of undefined methods and fields on strings
setmetatable(string, {
	__index = function(_, key)
		error("strings have no `" .. tostring(key) .. "` field", 2)
	end,
})

-- RETURNS whether or not instance is a Lua string
local function isstring(instance)
	return type(instance) == "string"
end

-- RETURNS whether or not instance is a Lua object (table or userdata)
local function isobject(instance)
	return type(instance) == "userdata" or type(instance) == "table"
end

-- RETURNS whether or not instance is a Lua number
local function isnumber(instance)
	return type(instance) == "number"
end

-- RETURNS whether or not instance is a Lua boolean
local function isboolean(instance)
	return type(instance) == "boolean"
end

-- RETURNS whether or not instance is a Lua number that is integral
local function isinteger(instance)
	return type(instance) == "number" and instance%1 == 0
end

-- RETURNS whether or not instance is a Lua function
local function isfunction(instance)
	return type(instance) == "function"
end

-- RETURNS the n-th (English) ordinal as a word
function string.ordinal(n)
	assert(isinteger(n), "n must be an integer")
	-- 1st, 2nd, 3rd, 4th, 5th, 6th, 7th, 8th, 9th, 10th
	-- ...
	-- 21st, 22nd, 23rd, 24th, ... 29th
	-- ...
	if 10 <= n%100 and n%100 <= 20 then
		return n .. "th"
	elseif n%10 == 1 then
		return n .. "st"
	elseif n%10 == 2 then
		return n .. "nd"
	elseif n%10 == 3 then
		return n .. "rd"
	end
	return n .. "th"
end

function string.prepad(str, with, length)
	assert(isstring(with), "with must be a string")
	assert(isinteger(length), "length must be an integer")
	assert(#with == 1, "TODO: support #with > 1")

	return string.rep(with, length - #str) .. str
end

function string.postpad(str, with, length)
	assert(isstring(with), "with must be a string")
	assert(isinteger(length), "length must be an integer")
	assert(#with == 1, "TODO: support #with > 1")

	return str .. string.rep(with, length - #str)
end

-- Redefine `pairs` to use `__pairs` metamethod
local oldp41rs = pairs
local function pairs(object)
	assert(isobject(object),
		"object must be reference type in pairs()")
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
	local specialCharacterRepresentation = {
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
		if not specialCharacterRepresentation[c] then
			specialCharacterRepresentation[c] = "\\" .. tostring(i):prepad("0", 3)
		end
	end
	for i = 128, 255 do
		specialCharacterRepresentation[string.char(i)] = "\\" .. tostring(i)
	end

	-- RETURNS nothing
	-- MODIFIES out by appending strings to it
	local function showAdd(object, indent, out)
		if isstring(object) then
			-- Turn into a string literal
			table.insert(out, [["]])
			for character in object:gmatch "." do
				table.insert(out,
					specialCharacterRepresentation[character] or character)
			end
			table.insert(out, [["]])
		elseif isobject(object) then
			table.insert(out, "{")
			for key, value in pairs(object) do
				table.insert(out, "\n" .. indent .. "\t[")
				showAdd(key, indent .. "\t", out)
				table.insert(out, "] = ")
				showAdd(value, indent .. "\t", out)
				table.insert(out, ",")
			end
			table.insert(out, "\n" .. indent .. "}")
		else
			table.insert(out, tostring(object))
		end
	end

	-- RETURNS a nearly-valid Lua expression literal representing the
	-- (acyclic) Lua value
	show = function(value)
		local out = {}
		showAdd(value, "", out)
		return table.concat(out)
	end
end

-- RETURNS a copy of `object` that cannot be modified, and that errors
-- when a non-existent key is read.
local function freeze(object)
	assert(isobject(object))

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
				if previous ~= nil or key == 1 then
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

-- Generic Helpers -------------------------------------------------------------

-- RETURNS a frozen version of `object` such that accesses to key `key`
-- produce `newValue` instead of referring to `object`'s definition
local function withkv(object, key, newValue)
	local newObject = {}
	for k, v in pairs(object) do
		newObject[k] = v
	end

	newObject[key] = newValue
	return freeze(newObject)
end

-- RETURNS a list produced by mapping each element of `list` through `f`
local function map(f, list)
	local out = {}
	for k, v in pairs(list) do
		out[k] = f(v)
	end
	return out
end

local function getter(key)
	assert(key ~= nil)

	return function(object)
		return object[key]
	end
end

local function findwith(list, property, value)
	for _, element in ipairs(list) do
		if element[property] == value then
			return element
		end
	end
end

local function identity(x)
	return x
end

-- Lua Type Specifications -----------------------------------------------------

local _TYPE_SPECS = {}

-- RETURNS nothing
local function REGISTER_TYPE(name, predicate)
	assert(isstring(name), "name must be a string")
	assert(isfunction(predicate))
	assert(not _TYPE_SPECS[name],
		"Type `" .. name .. "` has already been defined")

	table.insert(_TYPE_SPECS, {name = name, predicate = predicate})
end

-- RETURNS a type predicate
local function TYPE_PREDICATE(name)
	if isfunction(name) then
		return name
	end

	assert(isstring(name),
		"name must be a string but instead it's a " .. type(name))

	local found = findwith(_TYPE_SPECS, "name", name)
	assert(found, "No type called `" .. name .. "` has been registered")
	return found.predicate
end

-- RETURNS a string representing the type of an object
local function typefull(object)
	for i = #_TYPE_SPECS, 1, -1 do
		if _TYPE_SPECS[i].predicate(object) then
			return _TYPE_SPECS[i].name
		end
	end
	error("unregistered primitive `" .. type(object) .. "`")
end

-- ASSERTS that `value` is of the specified type `t`
local function assertis(value, t)
	local spec = TYPE_PREDICATE(t)

	if not spec(value) then
		error("value must be a `" .. t .. "`, however it is a `"
			.. typefull(value) .. "`", 2)
	end
end

-- RETURNS a type-predicate
local function constantType(value)
	return function(object)
		return object == value
	end
end

-- RETURNS a type-predicate
local function recordType(record)
	assert(isobject(record))

	for key, value in pairs(record) do
		assert(isstring(key), "record key must be string")
		assert(isstring(value) or isfunction(value),
			"record value must be string or predicate")
	end

	local function predicate(object)
		for key, predicate in pairs(record) do
			if not TYPE_PREDICATE(predicate)(object[key]) then
				return false
			end
		end
		-- TODO: what if it has EXTRA fields?
		return true
	end

	return predicate
end

-- RETURNS a type-predicate
local function listType(element)
	assert(isstring(element) or isfunction(element),
		"listType element must be a type name (string) or a type-predicate")
	
	local function predicate(object)
		if not isobject(object) then
			return false
		end
		for key, value in pairs(object) do
			if not isinteger(key) then
				return false
			elseif key ~= 1 and object[key-1] == nil then
				return false
			end
		end
		return true
	end

	return predicate
end

-- RETURNS a type-predicate
local function mapType(from, to)
	local function predicate(object)
		local from = TYPE_PREDICATE(from)
		local to = TYPE_PREDICATE(to)
		if not isobject(object) then
			return false
		end
		for key, value in pairs(object) do
			if not from(key) or not to(value) then
				return false
			end
		end
		return true
	end

	return predicate
end

-- RETURNS a type-predicate
local function choiceType(...)
	local choices = {...}
	assert(#choices >= 1)

	local function predicate(object)
		for _, p in ipairs(choices) do
			if p(object) then
				return true
			end
		end
		return false
	end

	return predicate
end

-- Register the primitive types
REGISTER_TYPE("object", isobject)
REGISTER_TYPE("number", isnumber)
REGISTER_TYPE("integer", isinteger)
REGISTER_TYPE("string", isstring)
REGISTER_TYPE("function", isfunction)
REGISTER_TYPE("boolean", isboolean)
REGISTER_TYPE("nil", constantType(nil))

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
		["this"] = true,
		["union"] = true,
		["var"] = true,
		-- built-in types
		["Boolean"] = true,
		["Never"] = true,
		["Number"] = true,
		["String"] = true,
		["Unit"] = true,
	}

	-- Define token parsing rules
	local TOKENS = {
		{ -- type keywords, type names
			"[A-Z][A-Za-z0-9]*",
			function(x)
				if IS_KEYWORD[x] then
					return {tag = "type-keyword", keyword = x}
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
		local sourceContext = source:gsub("%s+", " ")
		if #sourceContext > 35 then
			sourceContext = sourceContext:sub(1, 35-3) .. "..."
		end
		local location = "at " .. filename .. ":" .. line .. ":" .. column
			.. "\n\t(at `" .. sourceContext .. "`)\n"

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
							" in a string literal that begins", location)
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
				quit("The compiler could not recognize any token ", location,
					" (near `" .. source:sub(1, 15) .. "...`)")
			end
		end
	end

	return tokens
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
	assert(type(list) == "table", "list must be table")
	assert(isinteger(offset), "offset must be an integer")
	assertis(list, listType "Token")

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

			local out = f(object)
			assert(out ~= nil)
			if isobject(out) then
				out = withkv(out, "location", stream:location())
			end
			return out, rest
		end
	end

	-- PARSER for `parser` but only extracting `field`
	local function parserExtractor(parser, ...)
		local fields = {...}
		assertis(fields, listType "string")
		assert(1 <= #fields)

		return parserMap(parser, function(x)
			for _, field in ipairs(fields) do
				x = x[field]
			end
			return x
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
		assert(isstring(components.tag), "components.tag must be string")

		-- A human readable context of the fields
		local contextMiddle = " in " .. components.tag
		local contextBegin = " to begin " .. components.tag
		local contextFinish = " to finish " .. components.tag

		for i = 1, #components do
			assert(#components[i] >= 2)
			assert(isstring(components[i][1]),
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
			assert(components[i][3] == nil or isstring(components[i][3]))
		end

		return function(stream, parsers)
			-- Annotate metadata
			local object = {
				tag = components.tag,
				location = stream:location(),
			}

			-- Parse fields in sequence
			for i, component in ipairs(components) do
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
					-- This member was a required cut; report an error with
					-- the input
					local context = contextMiddle
					if i == 1 then
						context = contextBegin
					elseif i == #components then
						context = contextFinish
					end
					quit("The compiler expected ", required, context,
						" ", stream:location())
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

	-- HELPER meaning object repeated several times,
	-- separated by commas.
	-- count: "N+" means "N or more things", N >= 0.
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
					quit("The compiler expected ", expected, " after `,` ",
						stream:location())
				end
				table.insert(list, element)
				stream = rest
			end
		end
	end

	local function parserOtherwise(p, value)
		assert(type(p) == "function")
		return parserMap(p, function(x) return x or value end)
	end

	-- DEFINES the grammar for the language
	local parsers = {
		-- Represents an entire source file
		["source"] = composite {
			tag = "source",
			{"package", G "package", "a package definition"}, --: string
			{"imports", zeroOrMore(G "import")},
			{"definitions", zeroOrMore(G "definition")},
		},

		-- Represents a package declaration
		["package"] = parserExtractor(composite {
			tag = "***package",
			{"_", K_PACKAGE},
			{"name", T_IDENTIFIER, "an identifier"},
			{"_", K_SEMICOLON, "`;` to finish package declaration"},
		}, "name"),

		-- Represents an import
		["import"] = composite {
			tag = "import",
			{"_", K_IMPORT},
			{"package", T_IDENTIFIER, "an imported package name"},
			{"class", optional(parserExtractor(composite { -- string | false
				tag = "***type name",
				{"_", K_DOT},
				{"class", T_TYPENAME, "a type name"},
			}, "class"))},
			{"_", K_SEMICOLON, "`;` after import"},
		},

		-- Represents a top-level definition
		["definition"] = choice {
			G "class-definition",
			G "union-definition",
			G "interface-definition",
		},

		-- Represents a class
		["class-definition"] = composite {
			tag = "class-definition",
			{"_", K_CLASS},
			{"name", T_TYPENAME, "a type name"},
			{"generics", parserOtherwise(optional(G "generics"), {
				parameters = {},
				constraints = {},
			})},
			{"implements", parserOtherwise(optional(G "implements"), {})},
			{"_", K_CURLY_OPEN, "`{` to begin class body"},
			{"fields", zeroOrMore(G "field-definition")},
			{"methods", zeroOrMore(G "method-definition")},
			{"_", K_CURLY_CLOSE, "`}`"},
		},

		-- Represents a union
		["union-definition"] = composite {
			tag = "union-definition",
			{"_", K_UNION},
			{"name", T_TYPENAME, "a type name"},
			{"generics", parserOtherwise(optional(G "generics"), {
				parameters = {},
				constraints = {},
			})},
			{"_", K_CURLY_OPEN, "`{` to begin union body"},
			{"fields", zeroOrMore(G "field-definition")},
			{"methods", zeroOrMore(G "method-definition")},
			{"_", K_CURLY_CLOSE, "`}`"},
		},

		-- Represents an interface
		["interface-definition"] = composite {
			tag = "interface-definition",
			{"_", K_INTERFACE},
			{"name", T_TYPENAME, "a type name"},
			{"generics", parserOtherwise(optional(G "generics"), {
				parameters = {},
				constraints = {},
			})},
			{"_", K_CURLY_OPEN, "`{` to begin interface body"},
			{"signatures", zeroOrMore(G "interface-signature")},
			{"_", K_CURLY_CLOSE, "`}` to end interface body"},
		},

		-- Represents a generics definition
		["generics"] = composite {
			tag = "generics",
			{"_", K_SQUARE_OPEN},
			{
				"parameters",
				commad(T_GENERIC, "1+", "generic parameter variable"),
				"generic parameter variables"
			},
			{
				"constraints",
				parserOtherwise(optional(G "generic-constraints"), {})
			},
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
			{"constraint", G "concrete-type", "a type constrain after `is`"},
		},

		-- Represents a smol Type
		["type"] = choice {
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
			{
				"package", --: string | false
				optional(G "package-scope"),
			},
			{"base", T_TYPENAME}, --: string
			{
				"arguments",
				parserOtherwise(optional(G "type-arguments"), freeze {})
			}, --: [ Type ]
		},

		["package-scope"] = parserExtractor(composite {
			tag = "***package-scope",
			{"name", T_IDENTIFIER},
			{"_", K_SCOPE},
		}, "name"),

		["type-arguments"] = parserExtractor(composite {
			tag = "***",
			{"_", K_SQUARE_OPEN},
			{
				"arguments",
				commad(G "type", "1+", "type argument"),
				"type arguments"
			},
			{"_", K_SQUARE_CLOSE, "`]`"},
		}, "arguments"),

		["implements"] = parserExtractor(composite {
			tag = "***implements",
			{"_", K_IS},
			{
				"interfaces",
				commad(G "concrete-type", "1+", "an interface name"),
				"one or more interface names",
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

		["interface-signature"] = parserExtractor(composite {
			tag = "***signature",
			{"signature", G "signature"},
			{"_", K_SEMICOLON, "`;` after interface method"},
		}, "signature"),

		-- Represents a function signature, including name, scope,
		-- parameters, and return type.
		["signature"] = composite {
			tag = "signature",
			{"foreign", optional(K_FOREIGN)},
			{"modifier", G "method-modifier"},
			{"name", T_IDENTIFIER, "a method name"},
			{"_", K_ROUND_OPEN, "`(` after method name"},
			{"parameters", commad(G "variable", "0+", "a parameter")},
			{"_", K_ROUND_CLOSE, "`)` after method parameters"},
			{
				"returnTypes",
				commad(G "type", "1+", "a return type"),
				"a return type"
			},
		},

		["method-modifier"] = choice {
			K_METHOD,
			K_STATIC,
		},

		-- Represents a smol statement / control structure
		["statement"] = choice {
			G "return-statement",
			G "do-statement",
			G "var-statement",
			G "assign-statement",
		},

		["block"] = composite {
			tag = "block",
			{"_", K_CURLY_OPEN},
			{"statements", zeroOrMore(G "statement")},
			{"_", K_CURLY_CLOSE, "`}` to end statement block"},
		},

		["variable"] = composite {
			tag = "variable",
			{"name", T_IDENTIFIER},
			{"type", G "type", "a type after variable name"},
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
			{
				"variables",
				commad(G "variable", "1+", "a variable"),
				"one or more variables",
			},
			{"_", K_EQUAL, "`=` after the variable in the var-statement"},
			{"value", G "expression", "an expression after `=`"},
			{"_", K_SEMICOLON, "`;` to end var-statement"},
		},

		-- Expressions!
		["expression"] = parserMap(composite {
			tag = "***expression",
			{"base", G "atom"},
			{"operations", zeroOrMore(G "operation")},
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

		["operation"] = composite {
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

		["atom"] = parserMap(composite {
			tag = "***atom",
			{"base", G "atom-base"},
			{"accesses", zeroOrMore(G "access")},
		}, function(x)
			local out = x.base
			for _, access in ipairs(x.accesses) do
				out = withkv(access, "base", out)
			end
			return out
		end),

		["access"] = parserMap(composite {
			tag = "***access",
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
					tag = "method-call",
					arguments = x.call.arguments,
					func = x.name, --: string
					location = x.location,
				}
			end
			return {
				tag = "field",
				field = x.name, --: string
				location = x.location,
			}
		end),

		["atom-base"] = choice {
			G "new-expression",
			K_THIS,
			parserMap(T_STRING_LITERAL, function(v)
				return {tag = "string-literal", value = v}
			end),
			parserMap(T_INTEGER_LITERAL, function(v)
				return {tag = "number-literal", value = v}
			end),
			composite { -- static method call
				tag = "static-call",
				{"base-type", G "type"},
				{"_", K_DOT, "`.` after type name"},
				{"name", T_IDENTIFIER, "a static method's name"},
				{"_", K_ROUND_OPEN, "`(` after static method name"},
				{"arguments", commad(G "expression", "0+", "an expression")},
				{"_", K_ROUND_CLOSE, "`)` to end static method call"},
			},
			parserMap(T_IDENTIFIER, function(n)
				return {tag = "identifier", name = n}
			end),
			parserExtractor(composite {
				tag = "***parenthesized expression",
				{"_", K_ROUND_OPEN},
				{"expression", G "expression", "expression"},
				{"_", K_ROUND_CLOSE, "`)`"},
			}, "expression"),
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
	structs = listType "StructIR",
	unions = listType "UnionIR",
	interfaces = listType "InterfaceIR",
	functions = listType "FunctionIR",
	main = "string",
})

REGISTER_TYPE("StructIR", recordType {
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "Type",
})

REGISTER_TYPE("UnionIR", recordType {
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
})

REGISTER_TYPE("InterfaceIR", recordType {
	name = "string",
	statics = listType("SignatureIR"),
	methods = listType("SignatureIR"),
	generics = listType("TypeParameterIR"),
})

REGISTER_TYPE("TypeParameterIR", recordType {
	name = "string", -- Type parameter name (e.g., "#Right")
	constraints = listType(recordType {
		interface = "ConcreteType+",
		name = "string", -- e.g., "#2"
	}),
})

REGISTER_TYPE("FunctionIR", recordType {
	name = "string",
	parameters = listType "VariableIR",
	generics = listType "TypeParameterIR",
	returnTypes = listType "Type+",
	body = "Body-IR",
})

REGISTER_TYPE("VariableIR", recordType {
	name = "string",
	type = "Type+",
})

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
	tag = constantType "GenericType+",
	
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

local REPORT = {}

function REPORT.TYPE_DEFINED_TWICE(first, second)
	assertis(first.name, "string")
	assertis(second.name, "string")
	assert(first.name == second.name)

	local name = first.name

	quit("The type `", name, "` was already defined ",
		first.location,
		".\nHowever, you are attempting to redefine it ",
		second.location)
end

function REPORT.TYPE_BROUGHT_INTO_SCOPE_TWICE(p)
	p = freeze(p)
	local name = p.name
	local first = p.firstLocation
	local second = p.secondLocation
	assertis(name, "string")

	quit("TYPE BROUGHT INTO SCOPE TWICE")
end

function REPORT.UNKNOWN_TYPE_IMPORTED(p)
	p = freeze(p)
	quit("The type `", p.name, "` has not been defined.",
		"\nHowever, you are trying to import it ", p.location)
end

function REPORT.UNKNOWN_PACKAGE_USED(p)
	p = freeze(p)
	quit("The package `", p.package, "` has not been imported.",
		"\nHowever, you are trying to use it ", p.location)
end

--------------------------------------------------------------------------------

-- RETURNS an IR description of the program
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

	-- (2) Fully qualify all local type names
	local classDefinitions = {}
	local interfaceDefinitions = {}
	local unionDefinitions = {}
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
		local classes = {}
		local interfaces = {}
		local unions = {}
		for _, definition in ipairs(source.definitions) do
			local location = definition.location
			defineLocalType(definition.name, source.package, location)
			if definition.tag == "class-definition" then
				table.insert(classes, definition)
			elseif definition.tag == "interface-definition" then
				table.insert(interfaces, definition)
			elseif definition.tag == "union-definition" then
				table.insert(unions, definition)
			else
				error("unknown definition tag `" .. definition.tag .. "`")
			end
		end

		assertis(packageIsInScope, mapType("string", constantType(true)))

		-- Verifies that a type is properly-in-scope
		local function typeFinder(t)
			if t.tag == "concrete-type" then
				local package = t.package
				if not package then
					package = packageScopeMap[t.name]
					if not package then
						Report.UNKNOWN_LOCAL_TYPE_USED {
							name = t.name,
							location = t.location,
						}
					end
				elseif not packageIsInScope[package] then
					Report.UNKNOWN_PACKAGE_USED {
						package = package,
						location = t.location,
					}
				end
				return {tag = "ConcreteType+",
					name = package .. ":" .. t.name,
					arguments = map(typeFinder, t.arguments),
					location = t.location,
				}
			elseif t.tag == "generic" then
				return {tag = "GenericType+",
					name = t.name,
					location = t.location,
				}
			elseif t.tag == "type-keyword" then
				return {tag = "KeywordType+",
					name = t.name,
					location = t.location,
				}
			end
			error("unhandled ast type tag `" .. t.tag .. "`")
		end


	end

	-- (3) Compile all code bodies
	assertis(classDefinitions, listType "StructIR")
	assertis(interfaceDefinitions, listType "InterfaceIR")
	assertis(unionDefinitions, listType "UnionIR")

end

-- RETURNS a semantic description of the program
local function semanticsSmolOld(sources, main)
	assert(isstring(main))

	-- (2) Resolve the full name and arity of all types
	local classSignatures = {}
	local interfaceSignatures = {}
	local unionSignatures = {}
	for _, source in ipairs(sources) do
		local packageName = source.package.name

		-- A bare `typename` should resolve to `packageMap[typename]:typename`.
		local packageMap = {}
		local importLocation = {}

		-- The set of package scopes which may be referred to by this source
		-- file.
		local packageIsAvailable = {
			[packageName] = true
		}

		-- (i) Scan imports
		for _, import in ipairs(source.imports) do
			if import.class then
				local importedFullName =
					import.package .. ":" .. import.class

				-- Check that this name hasn't been imported twice
				if packageMap[import.class] then
					quit("The type `", import.class,
						" has already been imported ",
						importLocation[import.class],
						"\nHowever, you are trying to import a type ",
						"with the same name ", import.location)
				elseif not typeSourceDefinitions[importedFullName] then
					quit("The type `", importedFullName, "`",
						" has not been defined. However, you are trying to",
						" import it ", import.location)
				end
				
				packageMap[import.class] = import.package
				importLocation[import.class] = import.location
			else
				-- Verify that this package name can be imported
				if import.package == packageName then
					quit("The package `", packageName, "` cannot import",
						" itself. However, you are trying to",
						" `import ", packageName, "` ", import.location)
				elseif not packageNameDefined[import.package] then
					quit("There is no package called `", import.package,
						"`. However, you are trying to import it ",
						import.location)
				end

				-- The package may be referred to
				packageIsAvailable[import.package] = true
			end
		end
		-- (ii) Scan locally defined types
		for _, definition in ipairs(source.definitions) do
			local name = definition.name
			assertis(name, "string")

			-- Check that the type has not been imported
			if packageMap[name] then
				assert(importLocation[name])
				quit("The name `", name, "` was imported ",
					importLocation[name], ".\nHowever, you are attempting to ",
					"define a type with the name `", name, "` ",
					definition.location)
			end

			packageMap[name] = packageName
		end

		-- REQUIRES t is a Type
		-- RETURNS Type
		local function normalizeTypePackage(t, genericsInScope)
			assert(isobject(genericsInScope),
				"genericsInScope must be an object")
			assertis(packageMap, mapType("string", "string"))
			t = freeze(t)

			if t.tag == "concrete-type" then
				local package
				if t.package then
					-- Check that the referenced package has been imported
					if not packageIsAvailable[t.package] then
						quit("The package `", t.package,
							"` hasn't been imported. However, ",
							"a type refers to it ", t.location)
					end

					package = t.package
				else
					if not packageMap[t.base] then
						quit("There is no type called `", t.base,
							"` in scope ", t.location)
					end

					package = packageMap[t.base]
				end
				assertis(package, "string")

				local fullName = package .. ":" .. t.base
				if not typeSourceDefinitions[fullName] then
					quit("There is no type called `", fullName, "`. ",
						"However, it is mentioned ", t.location)
				end

				-- Check that the number of type parameters is correct
				local sourceDefinition = typeSourceDefinitions[fullName]
				local expectedArity = #sourceDefinition.generics.parameters
				local appliedArity = #t.arguments
				if expectedArity ~= appliedArity then
					quit("The type `", fullName, "` expects exactly ",
						expectedArity, " type parameters.",
						"\nHowever, ", appliedArity, " were applied ",
						t.location)
				end

				-- Normalize all type parameters
				local arguments = {}
				for _, argument in ipairs(t.arguments) do
					table.insert(arguments,
						normalizeTypePackage(argument, genericsInScope))
				end

				return freeze {
					tag = "concrete-type",
					name = fullName,
					arguments = arguments,
					location = t.location,
				}
			elseif t.tag == "generic" then
				-- Check that it is in-scope
				if not genericsInScope[t.name] then
					quit("There is no generic `#" .. t.name .. "` in scope.",
					"\nHowever, it is referenced ", t.location)
				end
				return t
			elseif t.tag == "type-keyword" then
				return t
			end
			error("unknown type tag `" .. t.tag .. "`")
		end

		-- RETURNS generics
		-- context: a human-readable string of context (e.g., "class Foo")
		local function normalizeGenericsPackage(generics, context)
			assert(isobject(generics))
			assert(isstring(context), "context must be string")

			-- Build a list of type parameters
			local out = {}
			local outScope = {}
			local genericByName = {}
			for _, parameter in ipairs(generics.parameters) do
				assert(parameter.tag == "generic")
				assert(isstring(parameter.name))

				-- Check that this generic type hasn't been used before
				if genericByName[parameter.name] then
					quit("In " .. context .. ", the type parameter `",
						parameter.name, "` is defined twice.\n",
						"The first definition is ",
						genericByName[parameter.name].location,
						"The second definition is ", parameter.location)
				end

				local generic = {
					name = parameter.name,
					constraints = {},

					source = parameter,
					location = parameter.location,
				}

				-- Record the generic
				genericByName[parameter.name] = generic
				table.insert(out, generic)
				outScope[generic.name] = generic
			end

			-- outScope is "frozen" here, however we want to allow
			-- reads to find absence (for error checking).
			-- TODO: improve that

			local id = 0
			-- Add each constraint to the appropriate type parameter
			for _, constraint in ipairs(generics.constraints) do
				-- Find the matching parameter
				local parameterName = constraint.parameter.name
				local parameter = genericByName[parameterName]
				if not parameter then
					quit("There is no type parameter called `",
						parameterName, "` in ", context)
				end
				local interface = normalizeTypePackage(
					constraint.constraint, outScope)

				-- Add that interface to the list of constraint
				id = id + 1
				table.insert(parameter.constraints, {
					interface = interface,
					name = "#" .. id,
				})

				-- TODO: prevent duplicate interfaces
			end

			return freeze(out), outScope
		end

		local function normalizeSignaturePackage(signature, genericScope)
			assert(isobject(genericScope), "genericScope must be an object")

			local methodName = signature.name

			-- Normalize parameter types
			local parameters = {}
			for _, p in ipairs(signature.parameters) do
				table.insert(parameters, {
					name = p.name,
					type = normalizeTypePackage(p.type, genericScope),
					location = p.location,
				})
			end 
			
			-- Normalize return types
			local returns = {}
			for _, t in ipairs(signature.returnTypes) do
				table.insert(returns, normalizeTypePackage(t, genericScope))
			end

			-- Static function
			return {
				name = methodName,
				modifier = signature.modifier,
				parameters = parameters,
				returnTypes = returns,
				location = signature.location,
				source = signature,
			}
		end

		-- (iii) Rescan all local definitions and emit all signatures with
		-- fully-qualified types.
		for _, definition in ipairs(source.definitions) do
			local fullName = packageName .. ":" .. definition.name

			if definition.tag == "class-definition" then
				-- (a) type parameters / type constraints
				local generics, genericScope = normalizeGenericsPackage(
					definition.generics, "class " .. fullName)

				-- map[string]source
				-- Used for complaining about duplicates
				local memberSourceDefinition = {}

				-- (b) fields
				local fields = {}
				for _, field in ipairs(definition.fields) do
					-- Check that a named hasn't already been defined
					if memberSourceDefinition[field.name] then
						local previousField =
							memberSourceDefinition[field.name]
						quit("In `", fullName, "` a field named `",
							field.name, "` is defined twice.\n",
							"The first definition is ",
							previousField.location,
							"The second definition is ",
							field.location)
					end
					memberSourceDefinition[field.name] = field

					-- Add the field
					table.insert(fields, {
						name = field.name,
						type = normalizeTypePackage(field.type, genericScope),
						location = field.location,
					})
				end
				
				-- (c) methods and static functions
				local statics = {}
				local methods = {}
				for _, method in ipairs(definition.methods) do
					-- Normalize the member's signature
					local signature = normalizeSignaturePackage(
						method.signature, genericScope)

					-- Include NOT-NORMALIZED body
					local m = withkv(
						signature, "body", method.body
					)

					if m.modifier == "static" then
						table.insert(statics, m)
					else
						table.insert(methods, m)
					end
				end

				-- (d) interface implementations
				local implements = {}
				for _, interface in ipairs(definition.implements) do
					table.insert(implements,
						normalizeTypePackage(interface, genericScope))
				end

				-- Record this class's signature
				table.insert(classSignatures, freeze {
					name = fullName,

					implements = implements,
					generics = generics,

					fields = fields,
					statics = statics,
					methods = methods,

					source = definition,
					location = definition.location,

					normalizeTypePackage = normalizeTypePackage,
				})
			elseif definition.tag == "interface-definition" then
				-- Get in-scope generics
				local generics, genericScope = normalizeGenericsPackage(
					definition.generics, "interface " .. fullName)

				-- Add all members
				local statics = {}
				local methods = {}
				for _, signature in ipairs(definition.signatures) do
					local m = normalizeSignaturePackage(signature, genericScope)
					if m.modifier == "static" then
						table.insert(statics, m)
					else
						table.insert(methods, m)
					end
				end

				-- Record this interface's signature
				table.insert(interfaceSignatures, freeze {
					name = fullName,
					generics = generics,
					statics = statics,
					methods = methods,

					source = definition,
					location = definition.location,

					normalizeTypePackage = normalizeTypePackage,
				})
			elseif definition.tag == "union-definition" then
				-- (a) type parameters / type constraints
				local generics, genericScope = normalizeGenericsPackage(
					definition.generics, "interface " .. fullName)
				assert(genericScope)

				-- map[string]source
				-- Used for complaining about duplicates
				local memberSourceDefinition = {}

				-- (b) fields
				local fields = {}
				for _, field in ipairs(definition.fields) do
					-- Check that a named hasn't already been defined
					if memberSourceDefinition[field.name] then
						local previousField =
							memberSourceDefinition[field.name]
						quit("In `", fullName, "` a field named `",
							field.name, "` is defined twice.\n",
							"The first definition is ",
							previousField.location,
							"The second definition is ",
							field.location)
					end
					memberSourceDefinition[field.name] = field

					-- Add the field
					table.insert(fields, freeze {
						name = field.name,
						type = normalizeTypePackage(field.type, genericScope),
						location = field.location,
					})
				end

				-- (c) methods and static functions
				local statics = {}
				local methods = {}
				for _, method in ipairs(definition.methods) do
					-- Normalize signature
					local signature = normalizeSignaturePackage(
						method.signature, genericScope)

					-- Include NOT-NORMALIZED body
					local m = withkv(signature, "body", method.body)

					if m.modifier == "static" then
						table.insert(statics, m)
					else
						table.insert(methods, m)
					end
				end

				-- Record the union's signature
				table.insert(unionSignatures, freeze {
					name = fullName,
					fields = fields,
					generics = generics,

					methods = methods,
					statics = statics,

					source = definition,
					location = definition.location,

					normalizeTypePackage = normalizeTypePackage,					
				})
			else
				error("unknown definition tag `" .. definition.tag .. "`")
			end
		end
	end

	local function getDefinition(name)
		assert(isstring(name), "name must be a string")
		for _, class in ipairs(classSignatures) do
			if class.name == name then
				return class, "class"
			end
		end
		for _, interface in ipairs(interfaceSignatures) do
			if interface.name == name then
				return interface, "interface"
			end
		end
		for _, union in ipairs(unionSignatures) do
			if union.name == name then
				return union, "union"
			end
		end
		error("attempt to get the definition for a non-existant type")
	end

	-- RETURNS whether or not the types 'a' and 'b' are exactly equal
	local function areEqualTypes(a, b)
		a, b = freeze(a), freeze(b)

		if a.tag ~= b.tag then
			return false
		end
		if a.tag == "generic" then
			return a.name == b.name
		elseif a.tag == "concrete-type" then
			-- Check the base name is the same
			if a.name ~= b.name then
				return false
			end
			-- Check the arguments are the same
			assert(#a.arguments == #b.arguments)
			for i in ipairs(a.arguments) do
				if not areEqualTypes(a.arguments[i], b.arguments[i]) then
					return false
				end
			end
			return true
		elseif a.tag == "type-keyword" then
			return a.keyword == b.keyword
		end
		error("unknown type tag `" .. a.tag .. "`")
	end

	-- RETURNS string which is smol code representing type
	local function typeDescribe(t)
		t = freeze(t)
		if t.tag == "generic" then
			return "#" .. t.name
		elseif t.tag == "concrete-type" then
			local out = t.name
			if #t.arguments > 0 then
				for i, argument in ipairs(t.arguments) do
					if i == 1 then
						out = out .. "["
					else
						out = out .. ", "
					end
					out = out .. typeDescribe(argument)
				end
				out = out .. "]"
			end
			return out
		elseif t.tag == "type-keyword" then
			return t.keyword
		end
		error("unknown type tag `" .. t.tag .. "`")
	end

	-- RETURNS a type with generics substituted
	-- genericMap: [string] => type
	local function instantiateGenerics(t, genericMap)
		assert(isobject(t), "t must be an object")
		assert(isstring(t.tag), "type must have a string tag")
		assert(isobject(genericMap))

		local function recursive(u)
			return instantiateGenerics(u, genericMap)
		end

		if t.tag == "concrete-type" then
			return freeze {
				tag = "concrete-type",
				name = t.name,
				arguments = map(recursive, t.arguments),
				location = t.location, -- XXX: is this the right location?
			}
		elseif t.tag == "generic" then
			local match = genericMap[t.name]
			assert(match)
			return match
		elseif t.tag == "type-keyword" then
			return t
		end
		error("unknown type tag `" .. tostring(t.tag) .. "`")
	end

	-- RETURNS NOTHING
	local function checkClassImplements(class, implements, interface)
		-- RETURNS a type from `interface` with implement arguments substituted
		local genericMap = {}
		for i, generic in ipairs(interface.generics) do
			genericMap[generic.name] = implements.arguments[i]
		end

		local function parameterSubstituted(t)
			return instantiateGenerics(t, genericMap)
		end

		-- Check that each static and each method in the interface is
		-- implemented with the correct signature
		local memberRepositories = {
			{r="statics", k="static function"},
			{r="methods", k="method"},
		}
		for _, rk in pairs(memberRepositories) do
			local REPOSITORY = rk.r
			local KIND = rk.k
			for _, signature in ipairs(interface[REPOSITORY]) do
				assert(isstring(signature.name))

				local CLAIM = "class " .. class.name .. " claims to implement"
						.. " interface " .. interface.name .. ".\n"

				local impl = findwith(class[REPOSITORY], "name", signature.name)
				if not impl then
					quit(CLAIM,
						"However, it does not implement a ", KIND, " called ",
						signature.name)
				end

				local HOWEVER = "However, "
					.. KIND .. " `" .. signature.name .. "`"
				local LOCATION = "\n\nThe interface's function signature"
					.. " is defined " .. signature.location
					.. "\nThe " .. KIND .. " is implemented at "
					.. impl.location

				-- Check that parameter types are the same
				if #signature.parameters ~= #impl.parameters then
					quit(CLAIM, HOWEVER, " takes ", #impl.parameters,
						" parameter(s), rather than ", #signature.parameters,
						" parameter(s).", LOCATION)
				end
				for i, generalExpected in ipairs(signature.parameters) do
					local expected = parameterSubstituted(generalExpected.type)
					local got = impl.parameters[i].type
					if not areEqualTypes(expected, got) then
						quit(CLAIM, HOWEVER, " takes `", typeDescribe(got), "`",
							" rather than `", typeDescribe(expected), "`",
							" as the ", string.ordinal(i), " parameter.",
							LOCATION)
					end
				end

				-- Check that return types are the same
				if #signature.returnTypes ~= #impl.returnTypes then
					quit(CLAIM, HOWEVER, " returns ",
						#impl.returnTypes, " rather than ",
						#signature.returnTypes, " values.",
						LOCATION)
				end
				for i, generalExpected in ipairs(signature.returnTypes) do
					local expected = parameterSubstituted(generalExpected)
					if not areEqualTypes(expected, impl.returnTypes[i]) then
						quit(CLAIM, HOWEVER, " returns ",
							"`", typeDescribe(impl.returnTypes[i]), "`",
							" rather than `", typeDescribe(expected), "`",
							LOCATION)
					end
				end
			end
		end

		-- All methods are implemented as expected!
	end

	-- (3) Check that each class actually implements each interface that it
	-- claims to
	for _, class in ipairs(classSignatures) do
		for _, impl in ipairs(class.implements) do
			local definition, definitionType = getDefinition(impl.name)
			assert(definition)
			if definitionType ~= "interface" then
				quit("The type `", impl.name, "` is a ", definitionType,
					" rather than an interface, so class " .. class.name,
					" cannot implement it.",
					"\nHowever, class " .. class.name,
					" claims to implement it ", impl.location)
			end
			checkClassImplements(class, impl, definition)
		end
	end

	-- RETURNS nothing
	local function checkTypeImplements(t, constraint, genericScope)
		assert(isobject(genericScope), "genericScope must be an object")

		if t.tag == "generic" then
			error "TODO: lookup genericScope"
		elseif t.tag == "type-keyword" then
			local map = nil
			if t.keyword == "Number" then
				map = {
					["core:Showable"] = true,
					["core:Readable[Number]"] = true,
				}
			elseif t.keyword == "String" then
				map = {
					["core:Showable"] = true,
					["core:Readable[String]"] = true,
				}
			elseif t.keyword == "Boolean" then
				map = {
					["core:Showable"] = true,
					["core:Readable[Boolean]"] = true,
				}
			end
			assert(map)
			return map[typeDescribe(t)] or false
		elseif t.tag == "concrete-type" then
			error "TODO: refer to definition"
		end
		error("unknown type tag `" .. t.tag .. "`")
	end

	-- (4) Check that all type bounds are satisfied; compile!
	local function normalizeType(un, generics, normalizeTypePackage)
		assert(isobject(un), "generics must be an object")
		assert(isobject(generics), "generics must be an object")
		assert(isfunction(normalizeTypePackage),
			"normalizeTypePackage must be a function")

		-- (a) Do package normalization
		local scope = {}
		for _, generic in ipairs(generics) do
			scope[generic.name] = generic
		end
		local t = normalizeTypePackage(un, scope)

		-- (b) Check that all implementation requirements are satisfied
		if t.tag == "generic" then
			return t
		elseif t.tag == "type-keyword" then
			return t
		elseif t.tag == "concrete-type" then
			local definition = getDefinition(t.name)

			-- Normalize and validate type arguments;
			-- Collect the assignment of generic variables
			local genericMap = {}
			for i, argument in ipairs(t.arguments) do
				genericMap[definition.generics[i].name] =
					normalizeType(argument, generics, normalizeTypePackage)
			end
			
			-- ex.: definition: `class Box[#T | #T is Readable[#T]]`
			-- ex.: t: `Box[Number]`
			-- ex.: genericMap: {`#T` => `Number`}
			-- Verify that each constraint is satisfied
			for i, argument in ipairs(t.arguments) do
				local genericConstraints = definition.generics[i].constraints
				for _, genericConstraint in ipairs(genericConstraints) do
					-- ex.: genericConstraint.interface: `Readable[#T]`
					local constraintType = instantiateGenerics(
						genericConstraint.interface,
						genericMap)
					-- ex.: constraintType: `Readable[Number]`
					checkTypeImplements(argument, constraintType, generics)
				end
			end

			return t
		end
		error("unknown type tag `" .. t.tag .. "`")
	end

	-- Defines the Number type and its members
	local TYPE_NUMBER = {
		tag = "type-keyword",
		keyword = "Number",

		-- XXX: can we use this in getMembers?
		fields = {},
		methods = {},
		statics = {},
		generics = {},
	}

	local function getMembers(t, context)
		assert(isobject(t), "type must be an object")
		assert(isobject(context), "context must be an object")
		assert(isobject(context.generics), "context.generics must be an object")

		if t.tag == "generic" then
			-- Look up generic context to get a list of available
			-- statics/methods based on interfaces
			error("TODO: getMembers(generic)")
		elseif t.tag == "concrete-type" then
			-- Look up type with getDefinition
			local definition, definitionKind = getDefinition(t.name)
			if definitionKind == "class" then
				-- methods, statics, fields:
				local methods = {}
				
				-- RETURNS a type
				-- Instantiate a member type using the specified arguments
				local function instantiateMember(u)
					assert(isobject(u))

					-- Build generic map
					local genericMap = {}
					for i, generic in ipairs(definition.generics) do
						local name = generic.name
						local argument = t.arguments[i]
						genericMap[name] = argument
					end

					-- Use generic map for substitution
					return instantiateGenerics(u, genericMap)
				end

				-- Instantiate all methods
				local methods = {}
				for _, method in ipairs(definition.methods) do
					-- Instantiate return types and parameters
					local returnTypes =
						map(instantiateMember, method.returnTypes)
					local parameters = map(function(x)
						return {
							name = x.name,
							type = instantiateMember(x.type)
						}
					end, method.parameters)

					table.insert(methods, freeze {
						name = method.name,
						returnTypes = returnTypes,
						parameters = parameters,
					})
				end

				-- Instantiate all statics
				local statics = {}
				for _, static in ipairs(definition.statics) do
					-- Instantiate return types and parameters
					local returnTypes =
						map(instantiateMember, static.returnTypes)
					local parameters = map(function(x)
						return {
							name = x.name,
							type = instantiateMember(x.type)
						}
					end, static.parameters)

					table.insert(statics, freeze {
						name = static.name,
						returnTypes = returnTypes,
						parameters = parameters,
					})
				end

				local fields = {}
				for _, field in ipairs(definition.fields) do
					-- Instantiate field's type
					table.insert(fields, freeze {
						name = field.name,
						type = instantiateMember(field.type),
					})
				end

				return freeze {
					methods = methods,
					statics = statics,
					fields = fields,
					generics = definition.generics,
				}
			elseif definitionKind == "interface" then
				-- (Used only as helper)
				error("TODO")
			elseif definitionKind == "union" then
				error("TODO")
			end
		elseif t.tag == "type-keyword" then
			-- Use static list
			if t.keyword == "Number" then
				return TYPE_NUMBER
			end
			error("unknown type keyword `" .. t.keyword .. "`")
		end
	
		error("unknown type tag `" .. t.tag .. "`")
	end

	-- RETURNS (a list of IR-statements, expression info)
	-- expression info: a list of {name = string, type = Type}
	local function compileExpression(ast, normalizer, context)
		assert(isobject(ast))
		assert(isstring(ast.tag))
		assert(isobject(context), "context must be an object")
		assert(isinteger(context.unique))

		local function recursive(e, ...)
			assert(... == nil)
			local a, b, c = compileExpression(e, normalizer, context)
			assert(c == nil)
			assert(isobject(a), "1st from compileExpression must be an object")
			assert(isobject(b), "2nd from compileExpression must be an object")
			return a, b
		end

		-- RETURNS an identifier unique to the current statement compilation
		local function tmp(hint)
			if not isstring(hint) then
				assert(hint == nil)
			end
			local id = "_tmp_" .. tostring(context.unique)
			if hint then
				id = id .. "_" .. hint
			end
			context.unique = context.unique + 1
			return id
		end

		if ast.tag == "integer-literal" then
			local id = tmp("int")
			local out = {
				{tag = "var",
					name = id,
					type = "Number",
				},
				{tag = "number",
					value = ast.value,
					dst = id,
				},
			}
			local info = {
				{name = id, type = TYPE_NUMBER},
			}
			return out, info
		elseif ast.tag == "identifier" then
			local name = ast.name

			-- (1) Look up the variable in scope
			local type = nil
			for _, scope in ipairs(context.scopes) do
				if scope[name] then
					type = scope[name].type
					break
				end
			end

			if not type then
				quit("No variable called `", name, "` is in scope ",
					ast.location) 
			end

			return {}, {{name = name, type = type}}
		elseif ast.tag == "method-call" then
			local out, baseInfo = recursive(ast.base)
			if #baseInfo ~= 1 then
				quit("You are trying to access a method/field on something with " .. #baseInfo .. " values (rather than 1) ", ast.location)
			end
			local baseType = baseInfo[1].type
			local baseSrc = baseInfo[1].name

			local members = getMembers(baseType, context)
			local name = ast.func
			assertis(name, "string")

			local method = findwith(members.methods, "name", name)
			if not method then
				quit("The type `", typeDescribe(baseType), "` does not",
					" define a method called `", name, "`.",
					"\nHowever, you are trying to call it ",
					ast.location)
			end

			local argumentsInfo = {}
			for i, argument in ipairs(ast.arguments) do
				local irs, info = recursive(argument)
				for _, ir in ipairs(irs) do
					table.insert(out, ir)
				end

				-- Check the plurality of the argument
				if #info ~= 1 then
					quit("The ", string.ordinal(i), " argument to a method call is ", #info, " values (rather than 1) ", ast.access.location)
				end

				table.insert(argumentsInfo, info[1])
			end

			-- Verify the argument types match the parameter types
			if #argumentsInfo ~= #method.parameters then
				quit("Member function `",
					typeDescribe(baseType) .. "." .. name,
					"` expects ", #method.parameters, " arguments,",
					" but it was given ", #argumentsInfo, " ",
					ast.location)
			end
			for i, argument in ipairs(argumentsInfo) do
				local expected = method.parameters[i].type
				local got = argument.type

				if not areEqualTypes(expected, got) then
					quit("The ", string.ordinal(i), " argument to the",
					" method `",
					typeDescribe(baseType) .. "." .. name,
					"` expects the type `", typeDescribe(expected), "`.",
					"\nHowever, a value of type `", typeDescribe(got), "`",
					" was passed ", ast.location)
				end
			end

			error("TODO")
		elseif ast.tag == "static-call" then
			local out = {}
			local name = ast.name
			assert(isstring(name))
			local baseType = normalizer(ast["base-type"])

			local members = getMembers(baseType, context)

			local static = findwith(members.statics, "name", name)
			if not static then
				quit("The type `", typeDescribe(baseType), "` does not define",
					" a static function called `", name, "`.",
					"\nHowever, you try to call it ", ast.location)
			end
			
			-- Compile each argument
			local argumentsInfo = {}
			for i, argument in ipairs(ast.arguments) do
				local irs, info = recursive(argument)
				for _, ir in ipairs(irs) do
					table.insert(out, ir)
				end
				if #info ~= 1 then
					quit("The ", string.ordinal(i), " argument to a",
						" static function ", argument.location,
						" returns ", #info, " values rather than 1, so it",
						" cannot be used as a function argument.")
				end
				table.insert(argumentsInfo, info[1])
			end

			-- Validate the arguments
			if #static.parameters ~= #ast.arguments then
				quit("static function expected ", #static.parameters, " parameters but ", #ast.arguments, " were given ", ast.location)
			end
			for i, argument in ipairs(argumentsInfo) do
				local expected = static.parameters[i].type
				local got = argument.type
				if not areEqualTypes(expected, got) then
					quit("The ", string.ordinal(i),
						" argument to the static function `",
						typeDescribe(baseType), ".", name,
						"` expects the type `", typeDescribe(expected), "`.",
						"\nHowever, a value of type `", typeDescribe(got), "`",
						" is used ", ast.location)
				end
			end

			-- Create variables for each return
			local outputInfo = {}
			for _, returnType in ipairs(static.returnTypes) do
				local name = tmp()
				table.insert(outputInfo, {
					name = name,
					type = returnType,
				})
				table.insert(out, {tag = "var",
					name = name,
					type = returnType,
				})
			end
			
			-- Execute the call
			if baseType.tag == "generic" then
				error("TODO: static interface call")
			elseif baseType.tag == "concrete-type"
			or baseType.tag == "type-keyword" then
				-- Simple static function
				local func = baseType.name .. ":" .. static.name

				local arguments = map(getter "name", argumentsInfo)

				-- Refer to the class's generics to get constraints:
				local constraints = {}
				for _, generic in ipairs(members.generics) do
					for _, constraint in ipairs(generic.constraints) do
						error("TODO!")
					end
				end
				
				table.insert(out, {tag = "call",
					func = func,
					arguments = arguments,
					constraints = constraints,
					dsts = map(function(x) return x.name end, outputInfo),
				})
			end

			return out, outputInfo
		end

		error("unknown expression tag `" .. ast.tag .. "`")
	end

	-- RETURNS a list of IR-statements
	-- MODIFIES funcOut.body to be a list
	-- MODIFIES context
	local function compileStatement(ast, normalizer, context)
		local function recursive(x)
			return compileStatement(x, normalizer, context)
		end

		if ast.tag == "block" then
			-- Open a new variable scope
			table.insert(context.scopes, {})

			local statements = {}
			for _, statement in ipairs(ast.statements) do
				for _, ir in ipairs(recursive(statement)) do
					table.insert(statements, ir)
				end
			end

			local compiled = {tag = "block",
				statements = statements,
			}

			-- Close variable scope
			table.remove(context.scopes)
			return {compiled}
		elseif ast.tag == "var-statement" then
			local out = {}

			-- (1) Define variables
			local variableTypes = {}
			for _, variable in ipairs(ast.variables) do
				-- (i) Normalize type
				local variableType = normalizer(variable.type)
				local name = variable.name.name
				assert(isstring(name))

				-- (ii) Check for shadowing
				for _, scope in ipairs(context.scopes) do
					if scope[name] then
						quit("You tried to define the variable `",
							name, "` ", variable.location,
							"However, a variable called `", name, "`",
							" that was defined ", scope[name].location,
							" is still in-scope.")
					end
				end

				-- (iii) Add variable to current scope
				local currentScope = context.scopes[#context.scopes]
				currentScope[name] = {
					type = variableType,
					location = variable.location,
				}

				-- (iv) Output var IR statement
				table.insert(out, {tag = "var",
					name = name,
					type = variableType,
				})
				table.insert(variableTypes, variableType)
			end

			-- (2) Assign variables
			-- (i) Compile expression and output IR statements
			local irs, expressionInfo =
				compileExpression(ast.value, normalizer, context)
			for _, ir in ipairs(irs) do
				table.insert(out, ir)
			end

			-- (ii) Verify that types match
			if #expressionInfo ~= #ast.variables then
				quit("You try to define " .. #ast.variables .. " variable(s) ",
					ast.location, "However, the initial expression provides ",
					#expressionInfo, " values instead of ", #ast.variables)
			end
			for i, variableType in ipairs(variableTypes) do
				if not areEqualTypes(expressionInfo[i].type, variableType) then
					quit("Variable `", ast.variables[i].name, "` is declared",
						" with type `", typeDescribe(variableType), "`.",
						"\nHowever, its initial value is of type `",
						typeDescribe(expressionInfo[i].type), "`")
				end
			end

			-- (iii) Output each assignment
			for i, info in ipairs(expressionInfo) do
				table.insert(out, {tag = "assign",
					source = expressionInfo[i].name,
					dst = ast.variables[i].name,
				})
			end

			return out
		end
		error("unknown statement type `" .. ast.tag .. "`")
	end

	local compiled = {
		structs = {},
		functions = {},
	}

	-- (a) Classes
	for _, class in ipairs(classSignatures) do
		local function typeNormalizer(t, ...)
			assert(... == nil)

			return normalizeType(t, class.generics, class.normalizeTypePackage)
		end

		local structOut = {}
		structOut.name = class.name

		-- TODO: Validate generic constraints

		-- Validate all fields
		structOut.fields = {}
		for _, field in ipairs(class.fields) do
			table.insert(structOut.fields, {
				name = field.name,
				type = typeNormalizer(field.type)
			})
		end

		-- Validate and compile statics
		for _, static in ipairs(class.statics) do
			local funcOut = {
				modifier = "static",
				class = class,
			}

			funcOut.name = static.name

			funcOut.parameters = {}
			local parameterScope = {}
			for _, parameter in ipairs(static.parameters) do
				local parameterType = typeNormalizer(parameter.type)
				table.insert(funcOut.parameters, {
					name = parameter.name,
					type = parameterType,
				})
				parameterScope[parameter.name] = {
					type = parameterType,
					location = parameter.location,
				}
			end

			funcOut.returnTypes = {}
			for _, returnType in ipairs(static.returnTypes) do
				table.insert(funcOut.returnTypes, typeNormalizer(returnType))
			end

			local scopes = {parameterScope}
			funcOut.body = compileStatement(static.body, typeNormalizer, {
				unique = 0,
				scopes = scopes,
				generics = class.generics,
			})
			table.insert(compiled.functions, funcOut)
		end
	end

	-- TODO
	return nil
end

-- Transpilation ---------------------------------------------------------------

local sourceFromSemantics = {}

-- RETURNS a string representing a Lua program with the indicated semantics
function sourceFromSemantics.lua(semantics)
	-- RETURNS a valid Lua identifier
	local function luaizeFunction(name)
		assert(isstring(name), "luaizeFunction requires string")

		return (name:gsub(":", "_"))
	end

	local output = {
		"-- THIS FILE GENERATED BY SMOL COMPILER:\n\t-- ",
		INVOKATION:gsub("\n", "\n\t-- "),
		"\n"
	}

	-- OUTPUTS a comment indicating the begin of a new section of the file
	local function outputHeader(name)
		local line = "\n-- " .. name .. " "
		table.insert(output, line:postpad("-", 80))
		table.insert(output, "\n\n")
	end

	-- OUTPUTS a Lua serialization of the given statement
	local function generateStatement(statement, indentation)
		assert(isstring(statement.tag))
		if statement.tag == "block-ir" then
			-- XXX: always implicitly surrounded by Lua block;
			-- need not create `do` `end` pair
			for _, s in ipairs(statement.statements) do
				generateStatement(s, indentation .. "\t")
			end
		elseif statement.tag == "var-ir" then
			table.insert(output, indentation)
			table.insert(output, "local " .. statement.name)
			table.insert(output, ";\n")		
		elseif statement.tag == "string-load-ir" then
			assert(isstring(statement.value))

			table.insert(output, indentation)
			table.insert(output, statement.dst .. " = ")
			table.insert(output, "{value = ")
			table.insert(output, show(statement.value))
			table.insert(output, "}")
			table.insert(output, "\n")			
		elseif statement.tag == "number-load-ir" then
			table.insert(output, indentation)
			table.insert(output, statement.dst .. " = ")
			table.insert(output, "{value = ")
			table.insert(output, show(statement.value))
			table.insert(output, "}")
			table.insert(output, "\n")
		elseif statement.tag == "field-ir" then
			local field = statement.name
			local object = statement.object
			assert(isstring(field))
			assert(isstring(object))

			table.insert(output, indentation)
			table.insert(output,
				statement.dst .. " = " .. object .. "." .. field)
			table.insert(output, "\n")
		elseif statement.tag == "call-ir" then
			local func = statement.func
			assertis(func, "string")

			local luaArguments = {}

			error("TODO")
		elseif statement.tag == "interface-ir" then

			error("TODO")
		elseif statement.tag == "return-ir" then
			-- OUTPUT Lua return
			table.insert(output, indentation)
			table.insert(output, "return ")
			table.insert(output, table.concat(statement.values, ", "))
			table.insert(output, "\n")
		elseif statement.tag == "new-ir" then
			error("TODO")
		else
			error("unknown statement tag `" .. statement.tag .. "`")
		end
	end

	outputHeader("Foreign functions")
	-- OUTPUT the body of all foreign functions and types
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

	-- OUTPUT the definition (including the body) of each function
	outputHeader("Function definitions")
	for _, fn in ipairs(semantics.functions) do
		-- Collect type-parameters and type-constraints as Lua parameters
		local allParameters = {}
		for _, parameter in ipairs(fn.parameters) do
			assert(isstring(parameter.name))
			assert(isstring(parameter.type))
			table.insert(allParameters, parameter.name)
		end
		if fn.generics then
			for _, generic in ipairs(fn.generics) do
				assert(isstring(generic.name))

				for _, constraint in ipairs(generic.constraints) do
					assert(isstring(constraint.name))
					assert(isstring(constraint.interface))
					assert(constraint.name:sub(1, 1) == "#") -- e.g., "#2"

					-- Lua target does not need constraint.interface since
					-- the type of parameter is not specified
					table.insert(allParameters,
						luaizeConstraint(constraint.name))
				end

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
			
			-- OUTPUT initialize for this impl
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
