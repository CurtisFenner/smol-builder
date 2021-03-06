-- Curtis Fenner, copyright (C) 2017
-- Defines
-- + `show`
-- Defines
-- + isstring, isobject, isnumber, isboolean, isinteger, isfunction
-- Defines
-- + memoized
-- Defines
-- + REGISTER_TYPE, EXTEND_TYPE
-- Defines
-- + assertis
-- Defines
-- + constantType, recordType, listType, mapType, choiceType, intersectType,
-- + predicateType, nullableType, tupleType

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
	if indent > 6 then
		table.insert(out, "...")
	elseif isstring(object) then
		-- Turn into a string literal
		table.insert(out, [["]])
		for character in object:gmatch "." do
			table.insert(out, specialRepresentation[character] or character)
		end
		table.insert(out, [["]])
	elseif isobject(object) then
		local internal = {}
		table.insert(out, "{")
		for key, value in pairs(object) do
			local line = {}
			table.insert(line, "\n" .. string.rep("\t", indent) .. "\t[")
			showAdd(key, indent + 1, line)
			table.insert(line, "] = ")
			if rawequal(key, "location") then
				table.insert(line, "<location...>")
			else
				showAdd(value, indent + 1, line)
			end
			table.insert(line, ",")
			table.insert(internal, table.concat(line))
		end
		table.sort(internal)
		for i = 1, #internal do
			if #internal > 1000 and i > 3 and i <= #internal - 3 then
				local el = "\n" .. string.rep("\t", indent) .. "...;"
				if out[#out] ~= el then
					table.insert(out, el)
				end
			else
				local line = internal[i]
				table.insert(out, line)
			end
		end
		table.insert(out, "\n" .. string.rep("\t", indent) .. "}")
	else
		table.insert(out, tostring(object))
	end
end

-- RETURNS a nearly-valid Lua expression literal representing the
-- (acyclic) Lua value
function show(value)
	local out = {}
	showAdd(value, 0, out)
	return table.concat(out)
end

local realUnpack = table.unpack or _G.unpack
if rawget(_G, "unpack") then
	-- Make 5.1 look like 5.2
	_G.unpack = nil
end

function table.unpack(object)
	if getmetatable(object) then
		local asList = {}
		for i = 1, #object do
			asList[i] = object[i]
		end
		return realUnpack(asList)
	end
	return realUnpack(object)
end

--------------------------------------------------------------------------------

-- RETURNS whether or not instance is a Lua string
function isstring(instance)
	return type(instance) == "string"
end

-- RETURNS whether or not instance is a Lua object (table or userdata)
function isobject(instance)
	return type(instance) == "table"
end

-- RETURNS whether or not instance is a Lua number
function isnumber(instance)
	return type(instance) == "number"
end

-- RETURNS whether or not instance is a Lua boolean
function isboolean(instance)
	return type(instance) == "boolean"
end

-- RETURNS whether or not instance is a Lua number that is integral
function isinteger(instance)
	return type(instance) == "number" and instance % 1 == 0
end

-- RETURNS whether or not instance is a Lua function
function isfunction(instance)
	return type(instance) == "function"
end

-- A map from immutable objects to booleans
-- REQUIRES that all keys are immutable
local IMMUTABLE_OBJECTS = table.weak()

-- RETURNS (conservatively) whether or not `x` is immutable
function isimmutable(x)
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
function memoized(count, f)
	assert(isinteger(count), "count must be an integer")
	assert(count >= 0, "count must be non-negative")
	assert(isfunction(f), "f must be a function")

	-- TODO: address leaking of saved return-values
	local cache = table.weak()

	local memoizedF = function(...)
		local arguments = {...}
		assert(arguments[count + 1] == nil, "memoized function given too many arguments!")

		-- Check that the arguments are immutable
		for i = 1, count do
			if not isimmutable(arguments[i]) then
				return f(...)
			end
		end

		-- Search for the arguments in the cache
		local c = cache
		for i = 1, count - 1 do
			if c[arguments[i]] == nil then
				c[arguments[i]] = table.weak()
			end
			c = c[arguments[i]]
		end

		-- Check the cache
		local key = arguments[count]
		local saved = c[key]
		if saved then
			return table.unpack(saved)
		end

		-- Add to the cache
		saved = {f(...)}
		c[key] = saved
		return table.unpack(saved)
	end

	IMMUTABLE_OBJECTS[memoizedF] = true
	return memoizedF
end

-- Lua Type Specifications -----------------------------------------------------

local _TYPE_SPEC_BY_NAME = {}

-- RETURNS nothing
function REGISTER_TYPE(name, t)
	assert(isstring(name), "name must be a string")
	assert(not _TYPE_SPEC_BY_NAME[name], "Type `" .. name .. "` has already been defined")
	assert(isobject(t), "type description must be an object")

	local function describe()
		return name
	end

	_TYPE_SPEC_BY_NAME[name] = {
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
		local message = "_TYPE_SPEC_BY_NAME[" .. tostring(t) .. "]"
		assert(_TYPE_SPEC_BY_NAME[t], message)
		return t
	end

	return t.describe()
end
TYPE_DESCRIPTION = memoized(1, TYPE_DESCRIPTION)

local function _assertis(value, t)
	local predicate = TYPE_PREDICATE(t)
	local okay, reason = predicate(value)
	if not okay then
		if reason then
			reason = "(because " .. reason .. ")"
		else
			reason = "<no reason from " .. tostring(t) .. ">"
		end
		error(
			"value must be a `" .. TYPE_DESCRIPTION(t) .. "`." .. "\nHowever it is not: " .. reason .. "\n" .. show(value),
			2
		)
	end

	return true
end
_assertis = memoized(2, _assertis)

local normalizedT = {}

-- ASSERTS that `value` is of the specified type `t`
local queryCount = {}
function assertis(value, t)
	do return true end

	-- TYPE_DESCRIPTION must be injective
	-- Normalize types so that memoization works
	local x = TYPE_DESCRIPTION(t)
	normalizedT[x] = normalizedT[x] or t
	queryCount[x] = queryCount[x] or setmetatable({}, {__mode = "k"})
	queryCount[x][t] = queryCount[x][t] or 0
	
	if math.exp(-queryCount[x][t]) < math.random() then
		-- Assume that objects change less over time and that a repeatedly
		-- checked object still matches the type
		return
	end
	queryCount[x][t] = queryCount[x][t] + 1

	return _assertis(value, normalizedT[x])
end
assertis = memoized(2, assertis)

--------------------------------------------------------------------------------

-- RETURNS a type-predicate
function constantType(value)
	return {
		predicate = function(object)
			return object == value, "value must be `" .. show(value) .. "`"
		end,
		describe = function()
			return show(value)
		end,
	}
end
constantType = memoized(1, constantType)

-- RETURNS a type-predicate
local recordMemoize = {}
function recordType(record)
	assert(isobject(record), "record type must be given a table")

	local keys = {}
	for key, value in pairs(record) do
		table.insert(keys, {key = key, value = value})
		assert(isstring(key), "record key must be string")
	end
	table.sort(keys, function(a, b)
		return a.key < b.key
	end)
	local recordID = ""

	-- XXX: show() isn't necessary injective!!!
	for _, kv in ipairs(keys) do
		recordID = recordID .. show(kv.key) .. " => " .. show(kv.value) .. "; "
	end
	if recordMemoize[recordID] then
		return recordMemoize[recordID]
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
	predicate = memoized(1, predicate)

	local function describe(object)
		local kv = {}
		for key, value in pairs(record) do
			table.insert(kv, key .. " = " .. TYPE_DESCRIPTION(value))
		end
		table.sort(kv)

		return "{" .. table.concat(kv, ", ") .. "}"
	end

	local out = {predicate = predicate, describe = describe}
	recordMemoize[recordID] = out
	return out
end
recordType = memoized(1, recordType)

-- RETURNS a type-predicate
-- listlikeType is less strict than listType in that it allows extra fields.
-- However, it does not allow holes.
function listlikeType(elementType)
	local p =false
	local function predicate(object)
		if not isobject(object) then
			return false, "value is not an object (for list-like type)"
		end

		if not p then
			p = TYPE_PREDICATE(elementType)
		end

		for key, value in pairs(object) do
			if type(key) ~= "number" then
				-- Ignored
			else
				if key % 1 ~= 0 or key < 1 then
					return false, "value has non-integer number key"
				elseif key ~= 1 and object[key - 1] == nil then
					return false, "value is missing index " .. show(key - 1)
				end

				local okay, reason = predicate(value)
				if not okay then
					if not reason then
						return false, "bad value at index " .. show(key)
					end
					return false, reason .. " at index " .. show(key)
				end
			end
		end

		return true
	end

	local function describe()
		return "[~ " .. TYPE_DESCRIPTION(elementType) .. "]"
	end

	return {predicate = predicate, describe = describe}
end

-- RETURNS a type-predicate
function listType(elementType)
	assert(elementType)

	local p
	local function predicate(object)
		if not isobject(object) then
			return false, "value is not an object (for list type)"
		end

		if not p then
			p = TYPE_PREDICATE(elementType)
		end

		for key, value in pairs(object) do
			if not isinteger(key) then
				return false, "value has non-integer key " .. show(key)
			elseif key ~= 1 and object[key - 1] == nil then
				return false, "value is missing index " .. show(key - 1)
			end

			local okay, reason = p(value)
			if not okay then
				if not reason then
					return false, "bad value at index " .. show(key)
				end
				return false, reason .. " at index " .. show(key)
			end
		end

		return true
	end
	predicate = memoized(1, predicate)

	local function describe()
		return "[" .. TYPE_DESCRIPTION(elementType) .. "]"
	end

	return {predicate = predicate, describe = describe}
end
listType = memoized(1, listType)

-- RETURNS a type-predicate
function mapType(from, to)
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

			local okay, reason = to(value)
			if not okay then
				return false, reason .. " for value at key `" .. tostring(key) .. "`"
			end
		end

		return true
	end
	predicate = memoized(1, predicate)

	local function describe()
		local map = TYPE_DESCRIPTION(from) .. " => " .. TYPE_DESCRIPTION(to)
		return "{" .. map .. "}"
	end

	return {predicate = predicate, describe = describe}
end
mapType = memoized(2, mapType)

-- RETURNS a type-predicate
function choiceType(...)
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
	predicate = memoized(1, predicate)

	local function describe()
		local c = {}
		for _, choice in ipairs(choices) do
			table.insert(c, TYPE_DESCRIPTION(choice))
		end
		table.sort(c)

		return "(" .. table.concat(c, " | ") .. ")"
	end

	return {predicate = predicate, describe = describe}
end

-- RETURNS a type-predicate
function intersectType(...)
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
	predicate = memoized(1, predicate)

	local function describe()
		local c = {}
		for _, type in ipairs(types) do
			table.insert(c, TYPE_DESCRIPTION(type))
		end
		table.sort(c)

		return "(" .. table.concat(c, " & ") .. ")"
	end

	return {predicate = predicate, describe = describe}
end

function EXTEND_TYPE(child, parent, definition)
	REGISTER_TYPE(child, intersectType(parent, definition))
end

-- RETURNS a type-predicate
function predicateType(f)
	assert(isfunction(f), "f must be a function")

	local function describe()
		return "<predicate " .. tostring(f) .. ">"
	end

	local function predicate(object)
		local okay = f(object)
		if okay then
			return true
		end

		return false, "value does not satisfy predicate from line " .. debug.getinfo(f).linedefined
	end

	return {predicate = predicate, describe = describe}
end
predicateType = memoized(1, predicateType)

-- RETURNS a type-predicate
function nullableType(t)
	assert(t)

	return choiceType(constantType(nil), t)
end
nullableType = memoized(1, nullableType)

-- RETURNS a type-predicate
function tupleType(...)
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

	return {predicate = predicate, describe = describe}
end

--------------------------------------------------------------------------------

-- Register the primitive types
REGISTER_TYPE("object", predicateType(isobject))
REGISTER_TYPE("number", predicateType(isnumber))
REGISTER_TYPE("integer", predicateType(isinteger))
REGISTER_TYPE("string", predicateType(isstring))
REGISTER_TYPE("function", predicateType(isfunction))
REGISTER_TYPE("boolean", predicateType(isboolean))
REGISTER_TYPE("false", constantType(false))
REGISTER_TYPE("true", constantType(true))
REGISTER_TYPE("nil", constantType(nil))
REGISTER_TYPE("any", predicateType(function()
	return true
end))

--------------------------------------------------------------------------------

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
