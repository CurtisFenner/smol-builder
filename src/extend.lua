-- Curtis Fenner, copyright (C) 2017
-- Helper methods added to the string and table libraries

-- RETURNS the n-th (English) ordinal as a word
function string.ordinal(n)
	assert(type(n) == "number", "n must be an integer")
	assert(n % 1 == 0, "n must be an integer")

	-- 1st, 2nd, 3rd, 4th, 5th, 6th, 7th, 8th, 9th, 10th
	-- ...
	-- 21st, 22nd, 23rd, 24th, ... 29th
	-- ...
	if 10 <= n % 100 and n % 100 <= 20 then
		return n .. "th"
	elseif n % 10 == 1 then
		return n .. "st"
	elseif n % 10 == 2 then
		return n .. "nd"
	elseif n % 10 == 3 then
		return n .. "rd"
	end
	return n .. "th"
end

-- RETURNS a string of length at least `length` that is formed by concatenating
-- a prefix with `str`. The prefix is made up of repetitions of `with`.
function string.prepad(str, with, length)
	assert(type(with) == "string", "with must be a string")
	assert(type(length) == "number", "length must be an integer")
	assert(length % 1 == 0, "length must be an integer")

	local paddingSize = length - #str
	return string.rep(with, paddingSize):sub(1, paddingSize) .. str
end

-- RETURNS a list formed by the concatenation of the arguments
function table.concatted(...)
	local out = {}
	for _, list in ipairs {...} do
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

-- Protect immutable tables
local realinsert = table.insert
function table.insert(list, ...)
	if isimmutable(list) then
		error("cannot table.insert on immutable list")
	end
	return realinsert(list, ...)
end

local realremove = table.remove
function table.remove(list, ...)
	if isimmutable(list) then
		error("cannot table.remove on immutable list")
	end
	return realremove(list, ...)
end

-- RETURNS the last element of a list
function table.last(list)
	return list[#list]
end

-- RETURNS a function that accesses `property`
function table.getter(property)
	return function(object)
		return object[property]
	end
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

-- RETURNS whether or not a table has a given key
-- TODO: fix to be fast on frozen objects
function table.haskey(object, key)
	if not getmetatable(object) then
		return object[key] ~= nil
	end

	for k, v in pairs(object) do
		if key == k then
			return true
		end
	end
	return false
end

-- RETURNS a list produced by mapping each element of `list` through `f`
function table.map(f, list, ...)
	assert(
		type(f) == "function",
		"the first argument to table.map must be a function"
	)
	local out = {}
	for k, v in ipairs(list) do
		out[k] = f(v, ...)
	end
	return out
end

-- RETURNS an element of `list` such that `return[property] == value`
function table.findwith(list, property, value)
	for key, element in ipairs(list) do
		if element[property] == value then
			return element, key
		end
	end
end

-- RETURNS an index of `list` such that `list[return] == element`
-- REQUIRES `list` not have two distinct keys with the same element value
function table.indexof(list, element)
	local index = nil
	for i, v in pairs(list) do
		if v == element then
			assert(index == nil)
			index = i
		end
	end
	return index
end

function table.rest(object, from)
	local out = {}
	for i = from, #object do
		out[i - from + 1] = object[i]
	end
	return out
end

-- RETURNS the cartesian product of the lists
function table.cartesian(lists)
	assert(1 <= #lists)
	local out = {}
	local index = {}
	for i = 1, #lists do
		if #lists[i] == 0 then
			return {}
		end
		index[i] = 1
	end
	while true do
		local row = {}
		for i = 1, #index do
			row[i] = lists[i][index[i]]
		end
		table.insert(out, row)

		-- Increment
		for i = #index, 0, -1 do
			if i == 0 then
				return out
			end
			index[i] = index[i] + 1
			if index[i] > #lists[i] then
				index[i] = 1
			else
				break
			end
		end
	end
end

local function ripairsit(list, i)
	if i - 1 >= 1 then
		return i - 1, list[i - 1]
	end
end

function ripairs(list)
	return ripairsit, list, #list + 1
end

function spairs(t, vf)
	local keys = {}
	for key in pairs(t) do
		keys[#keys + 1] = key
	end
	vf = vf or function(x)
		return x
	end
	table.sort(keys, function(a, b)
		return vf(a) < vf(b)
	end)
	local i = 0
	return function()
		i = i + 1
		if i <= #keys then
			return keys[i], t[keys[i]]
		end
	end
end
