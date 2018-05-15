-- Persistent, immutable maps

local Map = {}
Map.__index = Map

local Rope = import "rope.lua"

local identities = setmetatable({}, {__mode = 'k'})
local newID = 1

-- RETURNS the identity of an object given as an integer
local function getIdentity(object)
	local m = identities[object]
	if m ~= nil then
		return m
	end
	newID = newID + 1
	identities[object] = newID
	return newID
end

function Map.new()
	local out = {
		_rope = Rope.empty(),
	}
	return setmetatable(out, Map)
end

function Map:_getIndex(key)
	local keyID = getIdentity(key)

	local lo = 1
	local hi = self._rope:size()
	while lo <= hi do
		local mid = math.floor((lo + hi) / 2)
		assert(lo <= mid and mid <= hi)

		local pivot = self._rope:get(mid)
		local pivotID = getIdentity(pivot[1])
		if pivotID == keyID then
			assert(key == pivot[1])
			return mid
		elseif pivotID < keyID then
			lo = mid + 1
		else
			hi = mid - 1
		end
	end
	return nil
end

-- RETURNS the value associated with key, or nil if no value is yet associated
function Map:get(key)
	local i = self:_getIndex(key)
	if not i then
		return nil
	end
	return self._rope:get(i)[2]
end

-- RETURNS a new map with key now pointing to value and all other pairs
-- unchanged
function Map:with(key, value)
	if self:get(key) == value then
		return self
	elseif value == nil then
		local i = self:_getIndex(key)

		-- Remove this key from the rope
		local before = self._rope:slice(1, i - 1)
		local after = self._rope:slice(i + 1, self._rope:size())
		local out = {
			_rope = before .. after,
		}
		return setmetatable(out, Map)
	elseif self:get(key) ~= nil then
		local i = self:_getIndex(key)

		-- Remove this key from the rope
		local before = self._rope:slice(1, i - 1)
		local after = self._rope:slice(i + 1, self._rope:size())
		local out = {
			_rope = before .. Rope.singleton {key, value} .. after,
		}
		return setmetatable(out, Map)
	end

	if self._rope:size() == 0 then
		local out = {
			_rope = Rope.singleton {key, value},
		}
		return setmetatable(out, Map)
	end

	-- Insert a new key
	local keyID = getIdentity(key)
	local lo = 1
	local hi = self._rope:size()

	if getIdentity(self._rope:get(hi)[1]) < keyID then
		local out = {
			_rope = self._rope .. Rope.singleton {key, value},
		}
		return setmetatable(out, Map)
	elseif keyID < getIdentity(self._rope:get(lo)[1]) then
		local out = {
			_rope = Rope.singleton {key, value} .. self._rope,
		}
		return setmetatable(out, Map)
	end

	assert(2 <= self._rope:size())

	while lo + 1 < hi do
		assert(getIdentity(self._rope:get(lo)[1]) < keyID)
		assert(keyID < getIdentity(self._rope:get(hi)[1]))

		local mid = math.floor((lo + hi) / 2)
		local pivotID = getIdentity(self._rope:get(mid)[1])
		if pivotID < keyID then
			lo = mid
		else
			hi = mid
		end
	end

	local before = self._rope:slice(1, lo)
	local after = self._rope:slice(hi, self._rope:size())
	assert(lo + 1 == hi)
	local out = {
		_rope = before .. Rope.singleton {key, value} .. after,
	}
	return setmetatable(out, Map)
end

--------------------------------------------------------------------------------

if false then
	local m = Map.new()
	assert(m:get("foo") == nil)

	local m2 = m:with("foo", "bar")
	assert(m:get("foo") == nil)
	assert(m2:get("foo") == "bar")
	
	local m3 = m2:with("foo", "qux")
	assert(m3:get("foo") == "qux")

	local t = {}
	local m = Map.new()
	for _ = 1, 1000 do
		for _ = 1, math.random(0, 10) do
			local k = math.random(100)
			t[k] = nil
			m = m:with(k, nil)
		end
		for _ = 1, math.random(0, 10) do
			local k = math.random(100)
			local v = math.random()
			t[k] = v
			m = m:with(k, v)
		end

		for i = 1, 100 do
			assert(t[i] == m:get(i))
		end
	end
end

--------------------------------------------------------------------------------

return Map
