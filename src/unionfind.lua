-- Persistent union-find (disjoint set) data structure

local Rope = import "rope.lua"
local Map = import "map.lua"

local UnionFind = {}
UnionFind.__index = UnionFind

-- RETURNS an empty UnionFind data structure
function UnionFind.new()
	local instance = {
		_representatives = Map.new(),
		_classes = Map.new(),
		_graph = Map.new(),
	}
	return setmetatable(instance, UnionFind)
end

-- RETURNS a new UnionFind that will now accept e as an argument to query
-- and withUnion
-- REQUIRES the argument has not been initialized before
function UnionFind:withInit(e)
	assert(self._representatives:get(e) == nil, "e has already been added")
	return self:withTryInit(e)
end

-- RETURNS a new UnionFind that will now accept e as an argument to query
-- and withUnion
function UnionFind:withTryInit(e)
	if self._representatives:get(e) ~= nil then
		return self
	end
	
	local out = {
		_representatives = self._representatives:with(e, e),
		_classes = self._classes:with(e, Rope.singleton(e)),
		_graph = self._graph:with(e, Rope.empty())
	}

	return setmetatable(out, UnionFind)
end

function UnionFind:_root(e)
	local parent = self._representatives:get(e)
	assert(parent ~= nil, "e has not yet been init()'d")

	if parent == e then
		return parent
	end
	local root = self:_root(parent)

	-- Path compression is externally invisible, so we can mutate
	self._representatives = self._representatives:with(e, root)
	return root
end

-- RETURNS a new UnionFind like this except that a and b are now equal
function UnionFind:withUnion(a, b, reason)
	assert(reason ~= nil, "reason ~= nil")

	local outGraph = self._graph

	if a ~= b then
		-- Update the graph
		outGraph = outGraph:with(a, outGraph:get(a) .. Rope.singleton {from = a, to = b, reason = reason})
		outGraph = outGraph:with(b, outGraph:get(b) .. Rope.singleton {from = b, to = a, reason = reason})
	end

	local ra = self:_root(a)
	local rb = self:_root(b)
	if ra == rb then
		-- We already knew these were in the same component
		local out = {
			_representatives = self._representatives,
			_classes = self._classes,
			_graph = outGraph,
		}
		return setmetatable(out, UnionFind)
	end

	-- Update the representatives and classes
	local outRepresentatives
	local outClasses
	if math.random() < 0.5 then
		outRepresentatives = self._representatives:with(ra, rb)
		outClasses = self._classes:with(rb, self._classes:get(rb) .. self._classes:get(ra))
	else
		outRepresentatives = self._representatives:with(rb, ra)
		outClasses = self._classes:with(ra, self._classes:get(ra) .. self._classes:get(rb))
	end

	local out = {
		_representatives = outRepresentatives,
		_classes = outClasses,
		_graph = outGraph,
	}
	return setmetatable(out, UnionFind)
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

		for _, outEdge in self._graph:get(top):traverse() do
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

-- RETURNS []element
function UnionFind:classOf(a)
	return self._classes:get(self:_root(a))
end

do
	-- Test classes
	local u = UnionFind.new()
	for i = 1, 20 do
		u = u:withInit(i)
	end

	u = u:withUnion(1, 5, "one")
	u = u:withUnion(1, 4, "two")
	assert(u:classOf(4):size() == 3)
	assert(u:classOf(1):size() == 3)
	assert(u:classOf(5):size() == 3)
	assert(u:classOf(2):size() == 1)
end

do
	-- Test reasons
	local u = UnionFind.new()
	for i = 1, 10 do
		u = u:withInit(i)
	end

	u = u:withUnion(1, 2, "a")
	u = u:withUnion(3, 4, "b")
	u = u:withUnion(4, 5, "c")
	u = u:withUnion(1, 3, "d")
	u = u:withUnion(6, 7, "e")
	u = u:withUnion(6, 8, "f")
	u = u:withUnion(1, 8, "g")

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
	u = u:withInit "P.left"
	u = u:withInit "R"
	u = u:withInit "u.left"
	u = u:withInit "left"
	u = u:withInit "getLeft(P)"
	u = u:withInit "Q"
	u = u:withInit "u"
	u = u:withInit "P"

	u = u:withUnion("P.left", "R", 1)
	u = u:withUnion("u.left", "left", 2)
	u = u:withUnion("getLeft(P)", "Q", 3)
	u = u:withUnion("Q", "R", 5)
	u = u:withUnion("u", "P", 7)
	u = u:withUnion("P.left", "u.left", 7)

	assert(u:query("Q", "left"))
	local reasoning = u:reasonEq("Q", "left")
	assert(table.indexof(reasoning, 1))
	assert(table.indexof(reasoning, 5))
	assert(table.indexof(reasoning, 7))
end

return UnionFind
