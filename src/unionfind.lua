-- Union find

local UnionFind = {}

-- RETURNS an empty UnionFind data structure
function UnionFind.new()
	return setmetatable({representatives = {}}, {__index = UnionFind})
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
	else
		self.representatives[rb] = ra
	end

	return true
end

-- RETURNS boolean
function UnionFind:query(a, b)
	local ra = self:_root(a)
	local rb = self:_root(b)

	return ra == rb
end

-- RETURNS [[element]]
function UnionFind:classes()
	local map = {}
	for key, root in pairs(self.representatives) do
		map[root] = map[root] or {}
		table.insert(map[root], key)
	end
	local out = {}
	for _, class in pairs(map) do
		table.insert(out, class)
	end
	return out
end

-- RETURNS [element] all equal to query
function UnionFind:classOf(query)
	assert(self.representatives[query] ~= nil)

	local classes = self:classes()
	for _, class in ipairs(classes) do
		for _, element in ipairs(class) do
			if element == query then
				return class
			end
		end
	end

	error("unreachable")
end

return UnionFind
