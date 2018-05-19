-- Persistent union-find (disjoint set) data structure

local Rope = import "rope.lua"
local Map = import "map.lua"

local UnionFind = {}
UnionFind.__index = UnionFind

-- RETURNS an empty UnionFind data structure
function UnionFind.new(special)
	assertis(special, mapType("string", "function"))

	local instance = {
		_representatives = Map.new(),
		_classes = Map.new(),
		_graph = Map.new(),
		_special = special,
		_specialsPer = {},
	}

	-- Each per is a rope of special elements in that class
	for k, v in pairs(special) do
		instance._specialsPer[k] = Map.new()
	end

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
		_graph = self._graph:with(e, Rope.empty()),
		_special = self._special,
		_specialsPer = {}
	}

	for k, v in pairs(self._special) do
		local rope
		if v(e) then
			-- e is the only special value of this class
			rope = Rope.singleton(e)
		else
			-- e is not special, so this singleton class has no special values
			rope = Rope.empty()
		end
		out._specialsPer[k] = self._specialsPer[k]:with(e, rope)
	end

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
		local aOut = outGraph:get(a) or Rope.empty()
		local bOut = outGraph:get(b) or Rope.empty()
		outGraph = outGraph:with(a, aOut .. Rope.singleton {from = a, to = b, reason = reason})
		outGraph = outGraph:with(b, bOut .. Rope.singleton {from = b, to = a, reason = reason})
	end

	local ra = self:_root(a)
	local rb = self:_root(b)
	if ra == rb then
		-- We already knew these were in the same component
		local out = {
			_representatives = self._representatives,
			_classes = self._classes,
			_graph = outGraph,
			_special = self._special,
			_specialsPer = self._specialsPer,
		}
		return setmetatable(out, UnionFind)
	end

	-- Update the representatives and classes
	local outRepresentatives
	local outClasses

	local child, parent
	if math.random() < 0.5 then
		child, parent = ra, rb
	else
		child, parent = rb, ra
	end
	outRepresentatives = self._representatives:with(child, parent)

	-- Update the component sets
	local componentUnion = self._classes:get(parent) .. self._classes:get(child)
	outClasses = self._classes:with(parent, componentUnion)
	outClasses = outClasses:with(child, nil)

	local out = {
		_representatives = outRepresentatives,
		_classes = outClasses,
		_graph = outGraph,
		_special = self._special,
		_specialsPer = {},
	}

	for k in pairs(self._special) do
		local merged = self._specialsPer[k]:get(child) .. self._specialsPer[k]:get(parent)
		out._specialsPer[k] = self._specialsPer[k]:with(parent, merged)
	end

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

-- RETURNS an object equal to a such that all other things equal to a have the
-- same representative
function UnionFind:representativeOf(a)
	return self:_root(a)
end

-- RETURNS a set of objects equal to a that are special, according to 
-- predicates past to UnionFind's constructor
function UnionFind:specialsOf(k, a)
	assert(self._special[k], "unknown special class")
	
	return self._specialsPer[k]:get(self:_root(a))
end

function UnionFind:traverse()
	return self._classes:traverse()
end

do
	-- Test classes
	local u = UnionFind.new {}
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
	local u = UnionFind.new {}
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
	local u = UnionFind.new {}
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
