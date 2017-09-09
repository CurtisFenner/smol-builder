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
	assert(type(with) == "string", "with must be a string")
	assert(type(length) == "number", "length must be an integer")
	assert(length % 1 == 0, "length must be an integer")
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
	for key, element in ipairs(list) do
		if element[property] == value then
			return element, key
		end
	end
end

-- RETURNS an index of `list` such that `list[return] == element`
function table.indexof(list, element)
	for i, v in pairs(list) do
		if v == element then
			return i
		end
	end
end
