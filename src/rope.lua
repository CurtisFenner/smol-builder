-- Curtis Fenner
-- Source: https://github.com/CurtisFenner/lua-datastructures

--------------------------------------------------------------------------------
-- A ROPE is a string-like (or list-like) data structure that provides fast
-- random access as well as fast slicing and fast concatenation.
-- In particular, it provides
	-- :get(index) in O(log n)
	-- :slice(start, finish) in O(log n)
	-- :concat(other) in O(log n)
-- all _persistently_, meaning they do not modify the original object but
-- instead produce copies (with as much sharing as possible to avoid leaking
-- memory)

-- A Rope is different from a string, which provides
	-- :get(index) in O(1)
	-- :slice(start, finish)
		-- in O(1) by forcing the larger string to remain around in memory,
		-- which can leak memory when very large strings are repeatedly pared
		-- down OR
		-- in O(n) by copying the substring
	-- :concat(other) in O(n) by copying

-- Since computers are typically restricted to 48 bit addresses, in practice a
-- data structure can have no more than 2^48 elements. This makes Ropes at most
-- a (fairly large) constant factor slower than strings for random access.
-- Ropes are significantly more efficient than strings for concatenation and
-- slicing.

-- Ropes cannot be efficiently interned; thus equality on ropes is O(n).
-- However, hashing could be used to efficiently compare with a high probability
-- of success (NOTE that such an approach can be attacked maliciously!)

-- Ropes are implemented in a way similar to balanced search trees.
-- This implementation is based on an AVL tree.
-- An AVL TREE is a balanced binary search tree with an invariant that
-- the height of the left child must not differ from the height of the right
-- child by more than one. This guarantees that the height (aka depth) of the
-- tree is at most logarithmic in the size of the tree.
-- The size of the subtrees implicitly determine the keys using in the search
-- tree: if there are N elements to your left, you are at index N+1.
-- Because the keys are implicit, they don't need to be updated in a
-- concatenation, along O(log n) concatenation.
--------------------------------------------------------------------------------

-- OVERVIEW

-- Rope.empty()
-- Make a new size 0 rope

-- Rope.singleton(element)
-- Make new size 1 rope with element

-- Rope.concat(a, b)
-- a .. b
-- Make a new rope of the elements of a followed by the elements of b

-- Rope:slice(from, to)
-- Make a new rope using only the elements at indices from, from+1, ..., to
-- (inclusive)

-- Rope:size()
-- Get the number of elements in this rope

-- Rope:get(index)
-- Get the element at the given index, numbered from 1 to rope:size(), inclusive

-- Rope:traverse()
-- Get a stateless generator for iterating over the rope in order with
-- (index, value) pairs, akin to ipairs.

--------------------------------------------------------------------------------

-- IMPLEMENTATION

local Rope = {}
Rope.__index = Rope

-- RETURNS nothing
-- Dynamically check that all of the rope's invariants hold
function Rope:_validate()
	assert(type(self._size) == "number")
	assert(type(self._height) == "number")
	assert(self._height <= self._size)

	-- Either empty or singleton or pair
	if self._size == 0 then
		assert(self._height == 0)
		assert(self._value == nil)
		assert(self._left == nil)
		assert(self._right == nil)
	elseif self._size == 1 then
		assert(self._value ~= nil)
		assert(self._height == 1)
		assert(self._left == nil)
		assert(self._right == nil)
	else
		assert(self._value == nil)
		assert(self._left ~= nil)
		assert(self._right ~= nil)
		self._left:_validate()
		self._right:_validate()

		-- AVL balancing invariant:
		-- The heights of the left and right children must not differ by more
		-- than one.
		-- This guarantees the height of the tree is at most logarithmic in its
		-- size.
		assert(math.abs(self._left._height - self._right._height) <= 1)
		assert(self._height < 2 * (1 + math.log(self._size) / math.log(2)))
	end
end

-- RETURNS an empty rope
-- O(1) worst case
function Rope.empty()
	return setmetatable({_size = 0, _height = 0}, Rope)
end

-- RETURNS a singleton rope of just element
-- O(1) worst case
function Rope.singleton(element)
	assert(element ~= nil)
	return setmetatable({_size = 1, _height = 1, _value = element}, Rope)
end

function Rope:_show()
	if self._size == 0 then
		return "()"
	elseif self._size == 1 then
		return tostring(self._value)
	end
	return "(" .. self._left:_show() .. " "  .. self._right:_show() .. ")"
end

-- RETURNS a rope formed by subslicing
-- left, right inclusive
-- O(log n) worst case
function Rope:slice(left, right)
	if self._size < left or right < 1 then
		return Rope.empty()
	elseif left == right then
		return Rope.singleton(self:get(left))
	elseif left <= 1 and self._size <= right then
		return self
	end

	local slicedLeft = self._left:slice(left, right)
	local offset = self._left._size
	local slicedRight = self._right:slice(left - offset, right - offset)
	return Rope.concat(slicedLeft, slicedRight)
end

-- RETURNS a rope formed by the concatenation of two ropes
-- O(log n) worst case
function Rope.concat(left, right)
	assert(getmetatable(left) == Rope, "left must be a rope")
	assert(getmetatable(right) == Rope, "right must be a rope")

	-- Some simple base cases to handle
	if left._size == 0 then
		return right
	elseif right._size == 0 then
		return left
	end

	-- AVL height balancing invariant
	local difference = left._height - right._height
	if -1 <= difference and difference <= 1 then
		-- We are done
		local instance = {
			_size = left._size + right._size,
			_height = 1 + math.max(left._height, right._height),
			_left = left,
			_right = right,
		}
		return setmetatable(instance, Rope)
	end

	if left._height < right._height then
		-- The right tree is heavier.
		-- Find a subtree on the left spine of right tree that can be directly
		-- concatenated with left. This will adjust the height each of its
		-- ancestors by at most one -- this looks just like inserting in AVL
		-- trees, and can also be fixed by rotations.
		local subtree = right
		local rightSiblings = {}
		repeat
			table.insert(rightSiblings, subtree._right)
			subtree = subtree._left
		until math.abs(subtree._height - left._height) <= 1

		-- Join directly
		subtree = Rope.concat(left, subtree)

		-- Back up along the spine
		while #rightSiblings > 0 do
			local rightSibling = table.remove(rightSiblings)

			if math.abs(subtree._height - rightSibling._height) <= 1 then
				-- No rotation is necessary
				subtree = Rope.concat(subtree, rightSibling)
			else
				-- Subtree got heavier so we need to rotate
				assert(subtree._left and subtree._right)
				assert(subtree._left._height ~= subtree._right._height)
				if subtree._left._height > subtree._right._height then
					-- Away from `rightSibling` is heavier
					local newRight = Rope.concat(subtree._right, rightSibling)
					subtree = Rope.concat(subtree._left, newRight)
				else
					-- Nearer `rightSibling` is heavier
					local mid = subtree._right
					assert(mid._left and mid._right)

					local newLeft = Rope.concat(subtree._left, mid._left)
					local newRight = Rope.concat(mid._right, rightSibling)
					subtree = Rope.concat(newLeft, newRight)
				end
			end
		end
		return subtree
	else
		-- SEE ABOVE
		local subtree = left
		local leftSiblings = {}
		repeat
			table.insert(leftSiblings, subtree._left)
			subtree = subtree._right
		until math.abs(subtree._height - right._height) <= 1
		
		subtree = Rope.concat(subtree, right)

		-- Back up along the spine
		while #leftSiblings > 0 do
			local leftSibling = table.remove(leftSiblings)

			if math.abs(subtree._height - leftSibling._height) <= 1 then
				subtree = Rope.concat(leftSibling, subtree)
			else
				assert(subtree._left and subtree._right)
				assert(subtree._left.height ~= subtree._right._height)
				if subtree._right._height > subtree._left._height then
					-- Away from `leftSibling` is heavier
					local newLeft = Rope.concat(leftSibling, subtree._left)
					subtree = Rope.concat(newLeft, subtree._right)
				else
					-- Nearer `leftSibling` is heavier
					local mid = subtree._left
					assert(mid._left and mid._right)

					local newLeft = Rope.concat(leftSibling, mid._left)
					local newRight = Rope.concat(mid._right, subtree._right)
					subtree = Rope.concat(newLeft, newRight)
				end
			end
		end
		return subtree
	end
end

-- REQUIRES i be an in-bounds index
-- RETURNS the ith element of this rope, numbered 1 to size
-- O(log n) worst case
function Rope:get(i)
	assert(type(i) == "number", "index must be a number")
	if i < 1 or self._size < i then
		error(i .. " is out of bounds of rope of size " .. self._size, 2)
	end

	-- Search this a bit like a binary search tree, where the key at this node
	-- is implicitly 1 + (size of left child).
	if self._size == 1 then
		return self._value
	elseif i <= self._left._size then
		-- ith value occurs in left side
		return self._left:get(i)
	else
		-- ith value occurs in right side
		return self._right:get(i - self._left._size)
	end
end

-- RETURNS the number of elements in this rope
-- O(1) worst case
function Rope:size()
	return self._size
end

--------------------------------------------------------------------------------

-- RETURNS whether or not this rope and the other are the same length and 
-- contain equal elements at the same positions
-- NOTE: may behave strangely with NaNs as elements.
function Rope:__eq(other)
	assert(getmetatable(other) == Rope)

	if self._size ~= other then
		return false
	end
	for i = 1, #self._size do
		if self:get(i) ~= other:get(i) then
			return false
		end
	end
	return true
end

-- RETURNS a rope formed from the first n elements of this rope
-- Convenience method equivalent to self:slice(1, n)
-- O(log n) worst case
function Rope:prefix(n)
	return self:slice(1, n)
end

-- RETURNS a rope formed from the last n elements of this rope
-- Convenience method equivalent to self:slice(self:size() - n + 1, self:size())
-- O(log n) worst case
function Rope:suffix(n)
	return self:slice(self:size() - n + 1, self:size())
end

-- REQUIRES i is an in-boudns index
-- RETURNS a rope with the ith element replaced by v
-- Convenience method in terms of concatenation with suffix and prefix
function Rope:replaced(i, v)
	local singleton = Rope.singleton(v)
	return self:slice(1, i - 1) .. singleton .. self:slice(i + 1, self._size)
end

function Rope:_iterator(i)
	assert(0 <= i and i <= self._size)
	if i == self._size then
		return nil
	end

	return i + 1, self:get(i + 1)
end

-- RETURNS an iterator tuple suitable for iterating over this rope
-- The iterator produces <i, ith value> pairs in order like `ipairs`
-- The iterator is stateless.
-- O(log n) worst case per iteration
function Rope:traverse()
	return Rope._iterator, self, 0
end

Rope.__concat = Rope.concat

--------------------------------------------------------------------------------

if false then
	-- Test rope by comparing it to naive O(n) list implementation
	math.randomseed(0)

	local function naiveConcat(a, b)
		local out = {}
		for _, x in ipairs(a) do
			table.insert(out, x)
		end
		for _, x in ipairs(b) do
			table.insert(out, x)
		end
		return out
	end

	local function naiveSlice(t, a, b)
		local out = {}
		for i = a, b do
			table.insert(out, t[i])
		end
		return out
	end

	local function randomList()
		local t = {}
		for i = 1, math.random(0, 4) do
			t[i] = math.random(100)
		end
		if #t == 0 then
			return t, Rope.empty()
		end
		local r = {}
		for i = 1, #t do
			r[i] = Rope.singleton(t[i])
		end
		while #r > 1 do
			local i = math.random(#r - 1)
			local after = table.remove(r, i + 1)
			r[i] = Rope.concat(r[i], after)
		end
		r[1]:_validate()
		return t, r[1]
	end

	local function assertSame(n, r)
		local o = {}
		for i, v in r:traverse() do
			assert(i == #o + 1)
			table.insert(o, v)
		end
		assert(
			#n == r:size(),
			("sizes must match; got %d; expected %d"):format(r:size(), #n)
		)
		for i = 1, #n do
			assert(o[i] == n[i], "elements must match")
			assert(o[i] == r:get(i))
		end
	end

	local ts = {{randomList()}, {randomList()}}
	for i = 1, 10000 do
		-- Concat a random pair
		local u = ts[math.random(#ts)]
		local v = ts[math.random(#ts)]
		local correct = naiveConcat(u[1], v[1])
		local res = Rope.concat(u[2], v[2])
		res:_validate()
		assertSame(correct, res)
		table.insert(ts, {correct, res})

		-- Add a random seed
		table.insert(ts, {randomList()})

		-- Add a random slice
		if u[2]:size() > 0 then
			local i = math.random(1, u[2]:size())
			local j = math.random(1, u[2]:size())
			local res = u[2]:slice(i, j)
			res:_validate()
			local correct = naiveSlice(u[1], i, j)
			assertSame(correct, res)
			table.insert(ts, {correct, res})
		end
	end
	print(string.format("Passed tests! Made %d ropes", #ts))
end

if false then
	-- Make the fibonacci sequence by concatenating tally marks!
	local a = Rope.empty()
	local b = Rope.singleton("|")
	local accumulated = Rope.empty()
	for i = 1, 100 do
		print(a:size())
		a, b = b, a .. b
		accumulated = accumulated .. a .. Rope.singleton("\n")
	end

	-- Good luck doing this with strings. There are nearly 10^21 characters in
	-- this string, made in less than 1/100th of a second!
	local breaks = 0
	for i, c in accumulated:traverse() do
		io.write(c)
		if c == "\n" then
			breaks = breaks + 1
		end
		if breaks > 10 then
			print(string.format(
				"Printed %d characters from a rope made of %.1e characters",
				i,
				accumulated:size()
			))
			break
		end
	end
end

return Rope
