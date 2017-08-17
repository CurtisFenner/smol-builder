-- A transpiler for Smol -> ???
-- Curtis Fenner, copyright (C) 2017

local INVOKATION = arg[0] .. " " .. table.concat(arg, ", ")
	.. "\non " .. os.date("!%c")
	.. "\nsmol version 0??"

--------------------------------------------------------------------------------

local color = {}
color.enabled = true or package.config:sub(1, 1) == "/"
function color._format(text, format)
	if not color.enabled then
		return text
	end
	return format:gsub("%[", "\27[") .. text .. "\27[0m"
end
function color.blue(text)
	return color._format(text, "[34m[1m")
end
function color.red(text)
	return color._format(text, "[31m[1m")
end
function color.cyan(text)
	return color._format(text, "[36m[1m")
end

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
		print(table.concat{color.red("ERROR"), ":\n", first, ...})
		os.exit(45)
	else
		print(table.concat{color.cyan(first), ...})
		os.exit(40)
	end
end

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

-- RETURNS a string of length at least `length` that is formed by concatenating
-- a prefix with `str`. The prefix is made up of repetitions of `with`.
function string.prepad(str, with, length)
	assert(isstring(with), "with must be a string")
	assert(isinteger(length), "length must be an integer")
	assert(#with == 1, "TODO: support #with > 1")

	return string.rep(with, length - #str) .. str
end

-- RETURNS a list formed by the concatenation of the arguments
function table.concatted(...)
	local out = {}
	for _, list in ipairs{...} do
		for _, element in ipairs(list) do
			table.insert(out, element)
		end
	end
	return out
end

-- RETURNS a list of keys into the given table
-- Indices of lists are guaranteed to be returned in order;
-- Otherwise, the order is not specified
function table.keys(t)
	local marked = {}
	local out = {}
	for i in ipairs(t) do
		table.insert(out, i)
		marked[i] = true
	end
	for i in pairs(t) do
		if not marked[i] then
			table.insert(out, i)
		end
	end
	return out
end

-- RETURNS a new table with weak keys
function table.weak()
	return setmetatable({}, {__mode = "k"})
end

-- A map from immutable objects to booleans
-- REQUIRES that all keys are immutable
local IMMUTABLE_OBJECTS = table.weak()

-- RETURNS (conservatively) whether or not `x` is immutable
local function isImmutable(x)
	-- Not-a-number does not count as immutable
	if x ~= x then
		return false
	end

	-- These core types are immutable
	if type(x) == "number" or type(x) == "string" then
		return true
	elseif type(x) == "boolean" then
		return true
	end

	-- Consult the set of immutable objects
	return IMMUTABLE_OBJECTS[x] or false
end

-- RETURNS a function that behaves like `f`, 
-- REQUIRES `f` take exactly `count` non-nil arguments
-- REQUIRES `f` return only immutable objects
local function memoized(count, f)
	assert(isinteger(count), "count must be an integer")
	assert(count >= 0, "count must be non-negative")
	assert(isfunction(f), "f must be a function")

	-- TODO: address leaking of saved return-values
	local cache = table.weak()

	local memoizedF = function(...)
		local arguments = {...}
		assert(arguments[count+1] == nil)

		-- Check that the arguments are immutable
		for i = 1, count do
			if not isImmutable(arguments[i]) then
				return f(...)
			end
		end

		-- Search for the arguments in the cache
		local c = cache
		for i = 1, count-1 do
			if c[arguments[i]] == nil then
				c[arguments[i]] = table.weak()
			end
			c = c[arguments[i]]
		end

		-- Check the cache
		local key = arguments[count]
		local saved = c[key]
		if saved then
			return unpack(saved)
		end

		-- Add to the cache
		saved = {f(...)}
		c[key] = saved
		return unpack(saved)
	end

	IMMUTABLE_OBJECTS[memoizedF] = true
	return memoizedF
end

-- Redefine `pairs` to use `__pairs` metamethod
local function pairs(object)
	assert(isobject(object),
		"object must be reference type in pairs();"
		.. "\ngot `" .. type(object) .. "`")
	-- TODO: deal with locked metatables
	local metatable = getmetatable(object)
	if metatable and metatable.__pairs then
		return metatable.__pairs(object)
	end
	return next, object
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
local show;
do
	local specialRepresentation = {
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
		if not specialRepresentation[c] then
			specialRepresentation[c] = "\\" .. tostring(i):prepad("0", 3)
		end
	end
	for i = 128, 255 do
		specialRepresentation[string.char(i)] = "\\" .. tostring(i)
	end

	-- RETURNS nothing
	-- MODIFIES out by appending strings to it
	local function showAdd(object, indent, out)
		if indent > 10 then
			table.insert(out, "...")
		elseif isstring(object) then
			-- Turn into a string literal
			table.insert(out, [["]])
			for character in object:gmatch "." do
				table.insert(out, specialRepresentation[character] or character)
			end
			table.insert(out, [["]])
		elseif isobject(object) then
			table.insert(out, "{")
			for key, value in pairs(object) do
				table.insert(out, "\n" .. string.rep("\t", indent) .. "\t[")
				showAdd(key, indent + 1, out)
				table.insert(out, "] = ")
				showAdd(value, indent + 1, out)
				table.insert(out, ",")
			end
			table.insert(out, "\n" .. string.rep("\t", indent) .. "}")
		else
			table.insert(out, tostring(object))
		end
	end

	-- RETURNS a nearly-valid Lua expression literal representing the
	-- (acyclic) Lua value
	show = function(value)
		local out = {}
		showAdd(value, 0, out)
		return table.concat(out)
	end
end

-- RETURNS an immutable copy of `object` that errors when a non-existent key
-- is read.
-- REQUIRES all components are immutable, including functions
local function freeze(object)
	if not isobject(object) then
		return object
	end

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

	IMMUTABLE_OBJECTS[out] = true
	return out
end

-- Generic Helpers -------------------------------------------------------------

-- RETURNS the last element of a list
function table.last(list)
	return list[#list]
end

-- RETURNS a function that accesses `property`
function table.getter(property)
	return function(object) return object[property] end
end

-- RETURNS a frozen version of `object` such that accesses to key `key`
-- produce `newValue` instead of referring to `object`'s definition
function table.with(object, key, newValue)
	local newObject = {}
	for k, v in pairs(object) do
		newObject[k] = v
	end

	newObject[key] = newValue
	return freeze(newObject)
end

-- RETURNS a list produced by mapping each element of `list` through `f`
function table.map(f, list, ...)
	assert(type(f) == "function",
		"the first argument to table.map must be a function")
	local out = {}
	for k, v in ipairs(list) do
		out[k] = f(v, ...)
	end
	return out
end

-- RETURNS an element of `list` such that `return[property] == value`
function table.findwith(list, property, value)
	for _, element in ipairs(list) do
		if element[property] == value then
			return element
		end
	end
end

-- Lua Type Specifications -----------------------------------------------------

local _TYPE_SPEC_BY_NAME = {}

-- RETURNS nothing
local function REGISTER_TYPE(name, t)
	assert(isstring(name), "name must be a string")
	assert(not _TYPE_SPEC_BY_NAME[name],
		"Type `" .. name .. "` has already been defined")
	assert(isobject(t))

	local function describe()
		return name
	end

	_TYPE_SPEC_BY_NAME[name] = freeze {
		predicate = t.predicate,
		describe = describe,
	}
end

-- RETURNS a type predicate
local function TYPE_PREDICATE(t)
	-- Search for the saved predicate
	local p
	local found = _TYPE_SPEC_BY_NAME[t]
	if found then
		p = found.predicate
	else
		assert(type(t) ~= "string", "unknown type name `" .. tostring(t) .. "`")
		p = t.predicate
	end

	return memoized(1, function(object)
		local okay, reason = p(object)
		if not okay and not reason then
			error(show(t) .. " // " .. show(debug.getinfo(p)))
		end

		-- Indicate type names when known
		if reason and isstring(t) then
			reason = reason .. " (/ " .. t .. ")"
		end

		return okay, reason
	end)
end
TYPE_PREDICATE = memoized(1, TYPE_PREDICATE)

-- RETURNS a string representing the type `t`
local function TYPE_DESCRIPTION(t)
	if type(t) == "string" then
		assert(_TYPE_SPEC_BY_NAME[t])
		return t
	end

	return t.describe()
end
TYPE_DESCRIPTION = memoized(1, TYPE_DESCRIPTION)

-- ASSERTS that `value` is of the specified type `t`
local function assertis(value, t)
	local predicate = TYPE_PREDICATE(t)
	local okay, reason = predicate(value)
	if not okay then
		if reason then
			reason = "(because " .. reason .. ")"
		else
			reason = "<no reason from " .. tostring(t) .. ">"
		end
		error("value must be a `" .. TYPE_DESCRIPTION(t) .. "`."
			.. "\nHowever it is not: " .. reason .. "\n" .. show(value), 2)
	end
end

--------------------------------------------------------------------------------

-- RETURNS a type-predicate
local function constantType(value)
	return freeze {
		predicate = function(object)
			return object == value, "value must be `" .. show(value) .. "`"
		end,
		describe = function() return show(value) end,
	}
end
constantType = memoized(1, constantType)

-- RETURNS a type-predicate
local function recordType(record)
	assert(isobject(record))

	for key, value in pairs(record) do
		assert(isstring(key), "record key must be string")
	end

	local function predicate(object)
		if not isobject(object) then
			return false, "is not an object (for record type)"
		end

		-- Make a shallow copy in order to avoid tripping freeze() asserts
		local shallow = {}
		for key, value in pairs(object) do
			shallow[key] = value
		end

		-- Validate every key present in `record`
		for key, p in pairs(record) do
			local predicate, reason = TYPE_PREDICATE(p)

			local okay, reason = predicate(shallow[key])
			if not okay then
				return false, reason .. " in key " .. show(key)
			end
		end

		return true
	end

	local function describe(object)
		local kv = {}
		for key, value in pairs(record) do
			table.insert(kv, key .. " = " .. TYPE_DESCRIPTION(value))
		end
		table.sort(kv)

		return "{" .. table.concat(kv, ", ") .. "}"
	end

	return freeze {predicate = predicate, describe = describe}
end
recordType = memoized(1, recordType)

-- RETURNS a type-predicate
local function listType(elementType)
	assert(elementType)

	local function predicate(object)
		if not isobject(object) then
			return false, "value is not an object (for list type)"
		end

		for key, value in pairs(object) do
			if not isinteger(key) then
				return false, "value has non-integer key " .. show(key)
			elseif key ~= 1 and object[key-1] == nil then
				return false, "value is missing key " .. show(key-1)
			end

			local predicate = TYPE_PREDICATE(elementType)
			local okay, reason = predicate(value)
			if not okay then
				if not reason then
					return false, "bad value at index " .. show(key)
				end
				return false, reason .. " at index " .. show(key)
			end
		end

		return true
	end

	local function describe()
		return "[" .. TYPE_DESCRIPTION(elementType) .. "]"
	end

	return freeze {predicate = predicate, describe = describe}
end
listType = memoized(1, listType)

-- RETURNS a type-predicate
local function mapType(from, to)
	assert(from)
	assert(to)

	local function predicate(object)
		local from = TYPE_PREDICATE(from)
		local to = TYPE_PREDICATE(to)
		if not isobject(object) then
			return false, "value is not an object (for map type)"
		end
	
		for key, value in pairs(object) do
			local okay, reason = from(key)
			if not okay then
				return false, reason .. " for key `" .. tostring(key) .. "`"
			end

			if not to(value) then
				return false,
					reason .. " for value at key `" .. tostring(key) .. "`"
			end
		end

		return true
	end

	local function describe()
		local map = TYPE_DESCRIPTION(from) .. " => " .. TYPE_DESCRIPTION(to)
		return "{" .. map .. "}"
	end

	return freeze {predicate = predicate, describe = describe}
end
mapType = memoized(2, mapType)

-- RETURNS a type-predicate
local function choiceType(...)
	local choices = {...}
	assert(#choices >= 2, "choiceType must be given at least 2 choices")

	local function predicate(object)
		local reasons = {}
		for _, p in ipairs(choices) do
			local okay, reason = TYPE_PREDICATE(p)(object)
			if okay then
				return true
			end

			table.insert(reasons, reason)
		end
		return false, "(" .. table.concat(reasons, ") or (") .. ")"
	end

	local function describe()
		local c = {}
		for _, choice in ipairs(choices) do
			table.insert(c, TYPE_DESCRIPTION(choice))
		end
		table.sort(c)

		return "(" .. table.concat(c, " | ") .. ")"
	end

	return freeze {predicate = predicate, describe = describe}
end

-- RETURNS a type-predicate
local function intersectType(...)
	local types = {...}
	assert(#types >= 2)

	local function predicate(object)
		for _, p in ipairs(types) do
			local okay, reason = TYPE_PREDICATE(p)(object)
			if not okay then
				return false, reason
			end
		end
		return true
	end

	local function describe()
		local c = {}
		for _, type in ipairs(types) do
			table.insert(c, TYPE_DESCRIPTION(type))
		end
		table.sort(c)

		return "(" .. table.concat(c, " & ") .. ")"
	end

	return freeze {predicate = predicate, describe = describe}
end

local function EXTEND_TYPE(child, parent, definition)
	REGISTER_TYPE(child, intersectType(parent, definition))
end

-- RETURNS a type-predicate
local function predicateType(f)
	assert(isfunction(f), "f must be a function")

	local function describe()
		return "<predicate " .. tostring(f) .. ">"
	end

	local function predicate(object)
		local okay = f(object)
		if okay then
			return true
		end
		
		return false, "value does not satisfy predicate from line "
			.. debug.getinfo(f).linedefined
	end

	return freeze {predicate = predicate, describe = describe}
end
predicateType = memoized(1, predicateType)

-- RETURNS a type-predicate
local function nullableType(t)
	assert(t)

	return choiceType(constantType(nil), t)
end
nullableType = memoized(1, nullableType)

-- RETURNS a type-predicate
local function tupleType(...)
	local ts = {...}

	local function predicate(value)
		if not isobject(value) then
			return false, "value is not an object (for tuple type)"
		end

		if #value ~= #ts then
			return false, "value does not have length " .. #ts
		end
		
		for i = 1, #ts do
			local okay, reason = TYPE_PREDICATE(ts[i])(value[i])
			if not okay then
				return false, reason .. " in element " .. i
			end
		end

		return true
	end

	local function describe()
		local s = {}
		for _, t in ipairs(ts) do
			table.insert(s, TYPE_DESCRIPTION(t))
		end
		return "(" .. table.concat(s, ", ") .. ")"
	end

	return freeze {predicate = predicate, describe = describe}
end

--------------------------------------------------------------------------------

-- Register the primitive types
REGISTER_TYPE("object", predicateType(isobject))
REGISTER_TYPE("number", predicateType(isnumber))
REGISTER_TYPE("integer", predicateType(isinteger))
REGISTER_TYPE("string", predicateType(isstring))
REGISTER_TYPE("function", predicateType(isfunction))
REGISTER_TYPE("boolean", predicateType(isboolean))
REGISTER_TYPE("nil", constantType(nil))
REGISTER_TYPE("any", predicateType(function() return true end))

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
			.. "\n\t\t" .. string.rep(" ", column-1) .. color.red("^")

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

-- Parser ----------------------------------------------------------------------

REGISTER_TYPE("Parser", predicateType(isfunction))

local parser = {}

-- RETURNS a parser for a sequence of 0 or more `object`s
-- REQUIRES `object` is a parser
function parser.zeroOrMore(object)
	assertis(object, "Parser")

	return function(stream, grammar)
		assert(grammar)

		local list = {}
		while true do
			local element, rest = object(stream, grammar)
			if not rest then
				return list, stream
			end
			
			table.insert(list, element)
			stream = rest
		end
	end
end

-- RETURNS a parser of Bs
-- REQUIRES `p` is a parser of As
-- REQUIRES `f` is a map from As to Bs
function parser.map(parser, f)
	assertis(parser, "Parser")
	assertis(f, "function")

	return function(stream, grammar)
		assert(grammar)

		local object, rest = parser(stream, grammar)
		if not rest then
			return nil
		end

		local out = f(object)
		assert(out ~= nil)

		if isobject(out) then
			out = table.with(out, "location", stream:location())
		end
		return out, rest
	end
end

-- RETURNS a parser
function parser.choice(options)
	assertis(options, listType "Parser")
	assert(#options >= 1)

	return function(stream, grammar)
		assert(grammar)

		for _, option in ipairs(options) do
			local element, rest = option(stream, grammar)
			if rest then
				return element, rest
			end
		end

		return nil
	end
end

-- CONVENIENCE This is implemented in terms of sequence, option, and map
-- RETURNS a parser for a record type
function parser.composite(components)
	-- validate input
	assertis(components, "object")
	assertis(components.tag, "string")

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

		local extracts = {}

		-- Parse fields in sequence
		for i, component in ipairs(components) do
			-- Attempt to parse one field
			local key = component[1]
			local memberParser = component[2]
			local required = component[3]

			if key:sub(1, 1) == "#" then
				table.insert(extracts, key)
			end

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

		assert(#extracts <= 1)
		if #extracts == 1 then
			object = object[extracts[1]]
		end

		-- Successfully parsed all components
		return freeze(object), stream
	end
end

-- RETURNS a parser for `object` or false
function parser.optional(object)
	assertis(object, "Parser")

	return function(stream, grammar)
		assert(grammar)

		local element, rest = object(stream, grammar)
		if not rest then
			return false, stream
		end

		return element, rest
	end
end

-- HELPER parsing `object` repeated several times, delimited by `delimiter`
-- count: "N+" means "N or more things", N >= 0.
function parser.delimited(object, count, delimiter, expected)
	assert(type(object) == "function", "object must be function")
	assert(type(expected) == "string", "expected must be string")
	assert(type(count) == "string", "count format must be string")
	assert(type(count) == "string", "count format must be string")
	local minCount = 0
	local maxCount = math.huge
	local matchAtLeast = count:match "^(%d+)%+$"
	if matchAtLeast then
		minCount = tonumber(matchAtLeast)
	else
		error("unknown delimited'd count pattern `" .. count .. "`")
	end

	local delimiterParser = parser.token(function(token)
		if token.lexeme == delimiter then
			return token
		end
	end)

	return function(stream, grammar)
		assert(grammar)

		-- Consume the first element of the list
		local first, rest = object(stream, grammar)
		if not rest then
			if minCount <= 0 and 0 <= maxCount then
				return {}, stream
			end
			return nil
		end
		stream = rest

		local list = {first}
		while true do
			-- Consume a delimiter
			local _, rest = delimiterParser(stream, grammar)
			if not rest then
				if minCount <= #list and #list <= maxCount then
					return list, stream
				end
				return nil
			end

			stream = rest

			-- Consume an object
			local element, rest = object(stream, grammar)
			if not rest then
				-- After a delimiter, an object of the proper
				-- type must follow
				quit("The compiler expected ", expected,
					" after `" .. delimiter .. "` ",
					stream:location())
			end

			table.insert(list, element)
			stream = rest
		end
	end
end

-- RETURNS a parser for the type named `name`
function parser.named(name)
	assertis(name, "string")

	return function(stream, grammar)
		assert(grammar)
		assert(grammar[name], "a parser for `" .. name .. "` must be defined")

		return grammar[name](stream, grammar)
	end
end

-- RETURNS a Parser[T]
-- predicate: Token => T
function parser.token(predicate)
	assertis(predicate, "function")

	return function(stream, grammar)
		assert(stream)
		assert(grammar)

		if stream:size() == 0 then
			return nil
		end

		local object = predicate(stream:head())
		if object ~= nil then
			return object, stream:rest()
		end
	end
end

-- CONVENIENCE METHOD in terms of the other parsers
-- RETURNS a parser
function parser.query(query, tag)
	local function describe(query)
		-- TODO
		return "(" .. query .. ")"
	end

	if not query:find("%s") then
		if query:sub(-1) == "`" then
			-- Lexeme literal
			assert(query:sub(1, 1) == "`")
			return parser.token(function(token)
				if token.lexeme == query:sub(2, -2) then
					return token
				end
			end)
		elseif query:sub(-1) == "?" then
			-- Optional
			return parser.optional(parser.query(query:sub(1, -2)))
		elseif query:sub(-1) == "*" then
			-- Kleene star
			return parser.zeroOrMore(parser.query(query:sub(1, -2)))
		elseif query:match "%A%d%+$" then
			-- Delimited
			local before, delimiter, count = query:match "^(.+)(%A+)(%d+%+)$"
			return parser.delimited(parser.query(before), count, delimiter,
				describe(before))
		elseif query == query:lower() then
			-- Named
			return parser.named(query)
		elseif query == query:upper() then
			-- Token type
			return parser.token(function(token)
				return token.type == query:lower()
			end)
		end
		error("unrecognized parser-query `" .. query .. "`")
	end

	-- Separate into (whitespace separated) tokens
	local sequence = {}
	for token in query:gmatch("%S+") do
		if token:sub(1, 1) == "(" then
			local tag = token:sub(2)
			assert(tag ~= "")
			table.insert(sequence, {parent = sequence, tag = tag})
			sequence = table.last(sequence)
		elseif token == ")" then
			sequence = sequence.parent
			assert(sequence, "too many `)`")
		else
			table.insert(sequence, token)
		end
	end
	assert(not sequence.parent, "too many `(`")

	-- Parse individual tokens
	local stack = {}
	local modifierStack = {}
	for _, element in ipairs(sequence) do
		assert(#stack == #modifierStack)

		if type(element) == "string" then
			local modifiers = table.last(modifierStack)

			-- Process special modifiers
			if element:sub(1, 1) == "." then
				-- Extract a field
				local accessor = table.getter(element:sub(2))
				table.insert(stack, parser.map(table.remove(stack), accessor))
			elseif element:sub(1, 1) == "=" then
				-- Name a field
				modifiers["="] = element:sub(2)
			elseif element:sub(1, 1) == "!" then
				-- Require a field
				modifiers["!"] = element:sub(2):gsub("_", " ")
			else
				local newModifiers = {}
				if element:sub(1, 1) == "`" then
					newModifiers["="] = "_"
				end
				table.insert(stack, parser.query(element))
				table.insert(modifierStack, newModifiers)
			end
		else
			assert(#element >= 2, "unnecessary parenthesis")

			local serialized = table.concat(element, " ")
			table.insert(stack, parser.query(serialized, element.tag))
			table.insert(modifierStack, {})
		end
	end

	if #stack == 1 then
		return stack[1]
	end

	assertis(tag, "string")
	local components = {tag = tag}
	for i = 1, #stack do
		table.insert(components, {
			modifierStack[i]["="],
			stack[i],
			modifierStack[i]["!"],
		})
	end

	return parser.composite(components)
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

		["atom-base"] = parser.choice {
			parser.named "new-expression",
			K_THIS,
			parser.map(T_STRING_LITERAL, function(v)
				return {tag = "string-literal", value = v}
			end),
			parser.map(T_INTEGER_LITERAL, function(v)
				return {tag = "number-literal", value = v}
			end),
			parser.composite { -- static method call
				tag = "static-call",
				{"base-type", parser.named "type"},
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
})

REGISTER_TYPE("UnionIR", recordType {
	tag = constantType "union",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "ConcreteType+",
	signatures = listType "Signature",	
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
	"LocalSt",
	"NumberLoadSt",
	"ReturnSt",
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

			return freeze {
				tag = tag,

				name = structName,
				generics = generics,
				fields = fields,
				signatures = signatures,
				implements = implements,

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
			-- TODO
			return {}
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

	-- RETURNS a FunctionIR
	local function compileFunctionFromStruct(definition, signature)
		assertis(definition, choiceType("ClassIR", "UnionIR"))
		assertis(signature, "Signature")

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

		-- RETURNS StatementIR, [Variable]
		local function compileExpression(pExpression, scope)
			assertis(pExpression, recordType {
				tag = "string"
			})

			if pExpression.tag == "string-literal" then
				local out = {
					name = generateLocalID(),
					type = STRING_TYPE,
					location = pExpression.location .. ">"
				}
				return buildBlock {{
					tag = "string",
					string = pExpression.value,
					destination = out,
					returns = "no",
				}}, {out}
			elseif pExpression.tag == "number-literal" then
				local out = {
					name = generateLocalID(),
					type = NUMBER_TYPE,
					location = pExpression.location .. ">"
				}
				return buildBlock {{
					tag = "number",
					number = pExpression.value,
					destination = out,
					returns = "no",
				}}, {out}
			end

			error("TODO: " .. show(pExpression))
		end

		-- RETURNS a StatementIR
		local function compileStatement(pStatement, scope)
			assertis(scope, listType(mapType("string", "object")))

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
						Report.VARIABLE_DEFINITION_TYPE_MISMATCH {

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
			assertis(scope, listType(mapType("string", "object")))

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

		local body = compileBlock(signature.body, {})
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
