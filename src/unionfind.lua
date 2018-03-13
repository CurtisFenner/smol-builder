-- Union find

local UnionFind = {}

-- RETURNS an empty UnionFind data structure
function UnionFind.new()
	return setmetatable({representatives = {}, _classes = {}}, {__index = UnionFind})
end

function UnionFind:init(e)
	assert(self.representatives[e] == nil, "e has already been added")
	self:tryinit(e)
end

-- MODIFIES this so that it now accepts e as an argument to query and union
-- RETURNS whether or not the element is new
function UnionFind:tryinit(e)
	if self.representatives[e] == nil then
		self.representatives[e] = e
		self._classes[e] = {e}
		return true
	end
	return false
end

function UnionFind:_root(e)
	local parent = self.representatives[e]
	assert(parent ~= nil, "e has not yet been init()'d")

	if parent == e then
		return parent
	end
	local root = self:_root(parent)
	self.representatives[e] = root
	return root
end

-- MODIFIES this so that a and b are now equal
function UnionFind:union(a, b)
	local ra = self:_root(a)
	local rb = self:_root(b)
	if ra == rb then
		return false
	end

	if math.random() < 0.5 then
		self.representatives[ra] = rb

		-- Move classes
		for _, x in ipairs(self._classes[ra]) do
			table.insert(self._classes[rb], x)
		end
	else
		self.representatives[rb] = ra

		-- Move classes
		for _, x in ipairs(self._classes[rb]) do
			table.insert(self._classes[ra], x)
		end
	end

	return true
end

-- RETURNS boolean
function UnionFind:query(a, b)
	local ra = self:_root(a)
	local rb = self:_root(b)

	return ra == rb
end

-- RETURNS {element => []element}
function UnionFind:classes()
	local out = {}
	local map = {}
	for key, root in pairs(self.representatives) do
		map[root] = map[root] or {}
		table.insert(map[root], key)
		out[key] = map[root]
	end
	return out
end

-- RETURNS []element
function UnionFind:classOf(a)
	return self._classes[self:_root(a)]
end

-- TEST

local u = UnionFind.new()
for i = 1, 20 do
	u:init(i)
end

u:union(1, 5)
u:union(1, 4)
assert(#u:classOf(4) == 3)
assert(#u:classOf(1) == 3)
assert(#u:classOf(5) == 3)
assert(#u:classOf(2) == 1)

return UnionFind
