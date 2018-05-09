-- Union find

local UnionFind = {}

-- RETURNS an empty UnionFind data structure
function UnionFind.new()
	local instance = {
		_representatives = {},
		_classes = {},
		_graph = {},
	}
	return setmetatable(instance, {__index = UnionFind})
end

function UnionFind:init(e)
	assert(self._representatives[e] == nil, "e has already been added")
	self:tryinit(e)
end

-- MODIFIES this so that it now accepts e as an argument to query and union
-- RETURNS whether or not the element is new
function UnionFind:tryinit(e)
	if self._representatives[e] == nil then
		self._representatives[e] = e
		self._classes[e] = {e}
		self._graph[e] = {}
		return true
	end
	return false
end

function UnionFind:_root(e)
	local parent = self._representatives[e]
	assert(parent ~= nil, "e has not yet been init()'d")

	if parent == e then
		return parent
	end
	local root = self:_root(parent)
	self._representatives[e] = root
	return root
end

-- MODIFIES this so that a and b are now equal
function UnionFind:union(a, b, reason)
	assert(reason ~= nil, "reason ~= nil")

	if a ~= b then
		-- Update the graph
		table.insert(self._graph[a], {from = a, to = b, reason = reason})
		table.insert(self._graph[b], {from = b, to = a, reason = reason})
	end

	local ra = self:_root(a)
	local rb = self:_root(b)
	if ra == rb then
		-- We already knew these were in the same component
		return false
	end

	-- Update the representatives
	if math.random() < 0.5 then
		self._representatives[ra] = rb

		-- Move classes
		for _, x in ipairs(self._classes[ra]) do
			table.insert(self._classes[rb], x)
		end
	else
		self._representatives[rb] = ra

		-- Move classes
		for _, x in ipairs(self._classes[rb]) do
			table.insert(self._classes[ra], x)
		end
	end

	return true
end

-- RETURNS a list of reasons
function UnionFind:reasonEq(a, b)
	assert(self:query(a, b))

	-- Breadth first search for b
	local frontier = {a}
	local parent = {[a] = {}}
	for i = 1, math.huge do
		assert(i <= #frontier)
		local top = frontier[i]

		if top == b then
			-- Done!
			local reasons = {}
			local p = b
			while true do
				local incomingEdge = parent[p]
				p = incomingEdge.from
				if not p then
					return reasons
				end
				assert(incomingEdge.reason ~= nil)
				table.insert(reasons, incomingEdge.reason)
			end
		end

		for _, outEdge in ipairs(self._graph[top]) do
			if not parent[outEdge.to] then
				parent[outEdge.to] = outEdge

				assert(outEdge.to ~= nil)
				table.insert(frontier, outEdge.to)
			end
		end
	end
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
	for key, root in pairs(self._representatives) do
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

do
	-- Test classes
	local u = UnionFind.new()
	for i = 1, 20 do
		u:init(i)
	end

	u:union(1, 5, "one")
	u:union(1, 4, "two")
	assert(#u:classOf(4) == 3)
	assert(#u:classOf(1) == 3)
	assert(#u:classOf(5) == 3)
	assert(#u:classOf(2) == 1)
end

do
	-- Test reasons
	local u = UnionFind.new()
	for i = 1, 10 do
		u:init(i)
	end

	u:union(1, 2, "a")
	u:union(3, 4, "b")
	u:union(4, 5, "c")
	u:union(1, 3, "d")
	u:union(6, 7, "e")
	u:union(6, 8, "f")
	u:union(1, 8, "g")

	assert(u:query(1, 5))
	local reason15 = u:reasonEq(1, 5)
	assert(table.indexof(reason15, "c"))
	assert(table.indexof(reason15, "d"))
	assert(not table.indexof(reason15, "e"))
	assert(not table.indexof(reason15, "f"))

	-- Redundant (implementation detail)
	assert(not table.indexof(reason15, "g"))
end

do
	-- Test reasons
	local u = UnionFind.new()
	u:init "P.left"
	u:init "R"
	u:init "u.left"
	u:init "left"
	u:init "getLeft(P)"
	u:init "Q"
	u:init "u"
	u:init("P")

	u:union("P.left", "R", 1)
	u:union("u.left", "left", 2)
	u:union("getLeft(P)", "Q", 3)
	u:union("Q", "R", 5)
	u:union("u", "P", 7)
	u:union("P.left", "u.left", 7)

	assert(u:query("Q", "left"))
	local reasoning = u:reasonEq("Q", "left")
	assert(table.indexof(reasoning, 1))
	assert(table.indexof(reasoning, 5))
	assert(table.indexof(reasoning, 7))
end

return UnionFind
