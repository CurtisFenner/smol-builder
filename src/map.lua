-- Persistent, immutable maps

local Map = {}
Map.__index = Map

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
		_root = false,
	}
	return setmetatable(out, Map)
end

local function search(tree, key)
	if not tree then
		-- Empty
		return nil
	elseif tree[1] == 0 then
		-- Leaf: (0, leaf key, leaf value)
		if tree[2] == key then
			return tree[3]
		end
		return nil
	end

	-- Branch: (+height, left subtree, pivot key, right subtree)
	local pivot = getIdentity(tree[3])
	if getIdentity(key) <= pivot then
		-- Search in left subtree
		return search(tree[2], key)
	else
		-- Search in right subtree
		return search(tree[4], key)
	end
end

-- RETURNS the value associated with key, or nil if no value is yet associated
function Map:get(key)
	return search(self._root, key)
end

local max = math.max

local function close(a, b)
	return -1 <= a - b and a - b <= 1
end

local function inserted(tree, key, value)
	if not tree then
		-- Insert into empty makes single leaf
		return {0, key, value}
	elseif tree[1] == 0 then
		-- Insert into leaf to make single branch
		local newLeaf = {0, key, value}
		if tree[2] == key then
			-- Update existing key
			return newLeaf
		elseif getIdentity(key) < getIdentity(tree[2]) then
			return {1, newLeaf, key, tree}
		else
			return {1, tree, tree[2], newLeaf}
		end
	end

	-- Insert into branch (+height, left subtree, pivot key, right subtree)
	assert(1 <= tree[1])
	assert(tree[2] and tree[4])
	local newLeft, newRight
	if getIdentity(key) <= getIdentity(tree[3]) then
		-- Insert into left subtree
		newLeft = inserted(tree[2], key, value)
		newRight = tree[4]
	else
		newLeft = tree[2]
		newRight = inserted(tree[4], key, value)
	end

	-- Check balance factor
	local d = newLeft[1] - newRight[1]
	if -1 <= d and d <= 1 then
		-- Resulting tree is balanced
		local height = 1 + max(newLeft[1], newRight[1])
		return {height, newLeft, tree[3], newRight}
	end
	
	if d == -2 then
		-- newRight is too heavy
		assert(close(newLeft[1], newRight[2][1]))
		if close(1 + max(newLeft[1], newRight[2][1]), newRight[4][1]) then
			local outLeft = {1 + max(newLeft[1], newRight[2][1]), newLeft, tree[3], newRight[2]}
			return {1 + max(outLeft[1], newRight[4][1]), outLeft, newRight[3], newRight[4]}
		end

		-- split newRight[2]
		assert(newRight[2][1] ~= 0)
		local x, kxy, y = newRight[2][2], newRight[2][3], newRight[2][4]
		local outLeft = {1 + max(newLeft[1], x[1]), newLeft, tree[3], x}
		local outRight = {1 + max(y[1], newRight[4][1]), y, newRight[3], newRight[4]}
		assert(close(outLeft[1], outRight[1]))
		return {1 + max(outLeft[1], outRight[1]), outLeft, kxy, outRight}
	elseif d == 2 then
		-- newLeft is too heavy
		assert(close(newLeft[4][1], newRight[1]))
		if close(newLeft[2][1], 1 + max(newLeft[4][1], newRight[1])) then
			local outRight = {1 + max(newLeft[4][1], newRight[1]), newLeft[4], tree[3], newRight}
			return {1 + max(newLeft[2][1], outRight[1]), newLeft[2], newLeft[3], outRight}
		end
		
		-- split newLeft[4]
		assert(newLeft[4][1] ~= 0)
		local x, kxy, y = newLeft[4][2], newLeft[4][3], newLeft[4][4]
		local outLeft = {1 + max(newLeft[2][1], x[1]), newLeft[2], newLeft[3], x}
		local outRight = {1 + max(y[1], newRight[1]), y, tree[3], newRight}
		assert(close(outLeft[1], outRight[1]))
		return {1 + max(outLeft[1], outRight[1]), outLeft, kxy, outRight}
	end
	error "unreachable"
end

-- RETURNS a new map with key now pointing to value and all other pairs
-- unchanged
function Map:with(key, value)
	assert(key == key and key ~= nil, "key cannot be nil or NaN")

	local out = {
		_root = inserted(self._root, key, value),
	}
	return setmetatable(out, Map)
end

--------------------------------------------------------------------------------

local function smallestPair(tree)
	if not tree then
		return nil
	elseif tree[1] == 0 then
		return tree[2], tree[3]
	end
	return smallestPair(tree[2])
end

local function successorPair(tree, key)
	if not tree then
		return nil
	elseif tree[1] == 0 then
		return nil
	end

	if getIdentity(key) <= getIdentity(tree[3]) then
		local k, v = successorPair(tree[2], key)
		if k == nil then
			return smallestPair(tree[4])
		end
		return k, v
	end
	return successorPair(tree[4], key)
end

-- RETURNS the "next" key (traversal order is unspecified) and value
-- REQUIRES key is either nil (to get "first" key) or a valid key in this map
function Map:next(key)
	if key == nil then
		local k, v = smallestPair(self._root)
		if v == nil and k ~= nil then
			-- nil values aren't removed from the map, but shouldn't be
			-- revealed in traversal
			return self:next(k)
		end
		return k, v
	end

	local k, v = successorPair(self._root, key)
	if v == nil and k ~= nil then
		-- nil values shouldn't be revealed in traversal
		return self:next(k)
	end
	return k, v
end

function Map:traverse()
	return Map.next, self, nil
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

		local toVisit = {}
		for k, v in pairs(t) do
			toVisit[k] = true
		end
		for k, v in m:traverse() do
			if not toVisit[k] then
				error("should not have (re) visited " .. tostring(k))
			end
			toVisit[k] = false
			assert(t[k] == v)
			assert(m:get(k) == v)
		end
		for k, v in pairs(toVisit) do
			assert(t[k] == m:get(k))
			assert(not v, "should have visited " .. tostring(k))
		end
	end
end

if false then
	print("Beginning:")
	local m = Map.new()
	local before = os.clock()
	local N = 80000
	for i = 1, N do
		m = m:with(i, math.random())
	end

	local s = 0
	for k, v in m:traverse() do
		s = s + k * v
	end

	local elapsed = os.clock() - before
	print("Nonsense:", s)
	print("N:", N)
	print("Elapsed:", elapsed)
	print("Per op:", elapsed / (N * 2))
end

--------------------------------------------------------------------------------

return Map
