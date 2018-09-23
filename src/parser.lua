-- A PEG parsing library
local parser = {}

-- RETURNS a parser for a sequence of 0 or more `object`s
-- REQUIRES `object` is a parser
function parser.zeroOrMore(object)
	return function(stream, grammar)
		assert(grammar)

		local list = {}
		while true do
			local element, rest = object(stream, grammar)
			if not rest then
				return list, stream
			end

			table.insert(list, element)
			stream = rest
		end
	end
end

-- RETURNS a parser of Bs
-- REQUIRES `p` is a parser of As
-- REQUIRES `f` is a map from As to Bs
function parser.map(p, f, includeLocation)
	assert(type(f) == "function")

	return function(stream, grammar)
		assert(grammar)

		local begins = stream:location()

		local object, rest = p(stream, grammar)
		if not rest then
			return nil
		end

		local out = f(object)
		assert(out ~= nil)

		if includeLocation then
			local ends = rest:priorLocation()
			local with = {}
			for k, v in pairs(out) do
				with[k] = v
			end
			with.location = parser.config.locationSpan(begins, ends)
			out = with
		end
		return out, rest
	end
end

-- RETURNS a parser
function parser.choice(options)
	assert(type(options) == "table", "parser.choice expects a list")
	assert(#options >= 1)

	return function(stream, grammar)
		assert(grammar)

		for _, option in ipairs(options) do
			local element, rest = option(stream, grammar)
			if rest then
				return element, rest
			end
		end

		return nil
	end
end

-- CONVENIENCE This is implemented in terms of sequence, option, and map
-- RETURNS a parser for a record type
function parser.composite(components)
	-- validate input
	assert(type(components) == "table")
	assert(type(components.tag) == "string")

	-- A human readable context of the fields
	local contextMiddle = " in " .. components.tag
	local contextBegin = " to begin " .. components.tag
	local contextFinish = " to finish " .. components.tag

	-- Validate the structure of the composite definition
	for i = 1, #components do
		local row = components[i]
		assert(#row >= 2)
		assert(type(row[1]) == "string", "component must provide key as string")
		assert(row[1] ~= "tag", "component cannot use key 'tag'")
		assert(row[1] ~= "location", "component cannot use key 'location'")

		assert(type(row[2]) == "function", string.format(
			"not-a-parser given for key `%s` at %d/%d)",
			row[1],
			i,
			#components
		))

		assert(#row <= 3)
		assert(row[3] == nil or type(row[3]) == "string")
	end

	return function(stream, parsers)
		-- Annotate metadata
		local begins = stream:location()
		local object = {
			tag = components.tag,
		}

		local extracts = {}

		-- Parse fields in sequence
		for i, component in ipairs(components) do
			-- Attempt to parse one field
			local key = component[1]
			local memberParser = component[2]
			local required = component[3]

			if key:sub(1, 1) == "#" then
				table.insert(extracts, key)
			end

			local member, rest = memberParser(stream, parsers)

			if rest then
				-- Attach (non-underscore) field to object
				if key ~= "_" then
					object[key] = member
				end
				stream = rest
				local ends = rest:priorLocation()
				object.location = parser.config.locationSpan(begins, ends)
			elseif required then
				-- This member was a required cut; report an error with
				-- the input
				local context = contextMiddle
				if i == 1 then
					context = contextBegin
				elseif i == #components then
					context = contextFinish
				end
				quit(
					"The compiler expected ",
					required,
					context,
					" ",
					stream:location()
				)
			else
				-- This failed to parse
				return nil
			end
		end

		assert(#extracts <= 1)
		if #extracts == 1 then
			local fullLocation = object.location
			object = object[extracts[1]]
			if isobject(object) and components.location ~= false then
				object = table.with(object, "location", fullLocation)
			end
		end

		-- Successfully parsed all components
		return object, stream
	end
end

function parser.oneOrMore(object)
	local composite = parser.composite {
		tag = "_",
		{"first", object},
		{"rest", parser.zeroOrMore(object)},
	}

	local function f(object)
		return {object.first, table.unpack(object.rest)}
	end

	return parser.map(composite, f)
end

-- RETURNS a parser for `object` or false
function parser.optional(object)
	assert(type(object) == "function")

	return function(stream, grammar)
		assert(grammar)

		local element, rest = object(stream, grammar)
		if not rest then
			return false, stream
		end

		return element, rest
	end
end

-- RETURNS a parser that consumes no input and produces `value`
function parser.constant(value)
	assert(value ~= nil)

	return function(stream, grammar)
		assert(grammar)

		return value, stream
	end
end

-- HELPER parsing `object` repeated several times, delimited by `delimiter`
-- count: "N+" means "N or more things", N >= 0.
function parser.delimited(object, count, delimiter, expected)
	assert(type(object) == "function", "object must be function")
	assert(type(expected) == "string", "expected must be string")
	assert(type(count) == "string", "count format must be string")
	assert(type(count) == "string", "count format must be string")
	local minCount = 0
	local maxCount = math.huge
	local matchAtLeast = count:match "^(%d+)%+$"
	if matchAtLeast then
		minCount = tonumber(matchAtLeast)
	else
		error("unknown delimited'd count pattern `" .. count .. "`")
	end

	local delimiterParser = parser.token(function(token)
		if token.lexeme == delimiter then
			return token
		end
	end)

	return function(stream, grammar)
		assert(grammar)

		local from = stream:location()

		-- Consume the first element of the list
		local first, rest = object(stream, grammar)
		if not rest then
			if minCount <= 0 and 0 <= maxCount then
				return {}, stream
			end
			return nil
		end
		stream = rest

		local list = {first}
		while true do
			-- Consume a delimiter
			local _, rest = delimiterParser(stream, grammar)
			if not rest then
				if minCount <= #list and #list <= maxCount then
					local to = stream:priorLocation()
					list.location = parser.config.locationSpan(from, to)
					return list, stream
				end
				return nil
			end

			stream = rest

			-- Consume an object
			local element, rest = object(stream, grammar)
			if not rest then
				-- After a delimiter, an object of the proper
				-- type must follow
				quit(
					"The compiler expected ",
					expected,
					" after `" .. delimiter .. "` ",
					stream:location()
				)
			end

			table.insert(list, element)
			stream = rest
		end
	end
end

-- RETURNS a parser for the type named `name`
function parser.named(name)
	assert(type(name) == "string")

	return function(stream, grammar)
		assert(grammar)
		assert(grammar[name], "a parser for `" .. name .. "` must be defined")

		return grammar[name](stream, grammar)
	end
end

-- RETURNS a Parser[T]
-- predicate: Token => T
function parser.token(predicate)
	assert(type(predicate) == "function")

	return function(stream, grammar)
		assert(stream)
		assert(grammar)

		if stream:size() == 0 then
			return nil
		end

		local object = predicate(stream:head())
		if object ~= nil then
			return object, stream:rest()
		end
	end
end

-- CONVENIENCE METHOD in terms of the other parsers
-- RETURNS a parser
function parser.query(query, tag)
	local function describe(query)
		return "(" .. query .. ")"
	end

	if not query:find("%s") then
		if query:sub(-1) == "`" then
			-- Lexeme literal
			assert(query:sub(1, 1) == "`")
			return parser.token(function(token)
				if token.lexeme == query:sub(2, -2) then
					return token
				end
			end)
		elseif query:sub(-1) == "?" then
			-- Optional
			return parser.optional(parser.query(query:sub(1, -2)))
		elseif query:sub(-1) == "*" then
			-- Kleene star
			return parser.zeroOrMore(parser.query(query:sub(1, -2)))
		elseif query:match "%A%d%+$" then
			-- Delimited
			local before, delimiter, count = query:match "^(.+)(%A+)(%d+%+)$"
			return parser.delimited(
				parser.query(before),
				count,
				delimiter,
				describe(before)
			)
		elseif query:sub(-1) == "+" then
			return parser.oneOrMore(parser.query(query:sub(1, -2)))
		elseif query == query:lower() then
			-- Named
			return parser.named(query)
		elseif query == query:upper() then
			-- Token type
			return parser.token(function(token)
				return token.type == query:lower()
			end)
		end
		error("unrecognized parser-query `" .. query .. "`")
	end

	-- Separate into (whitespace separated) tokens
	local sequence = {}
	for token in query:gmatch("%S+") do
		if token:sub(1, 1) == "(" then
			local tag = token:sub(2)
			assert(tag ~= "")
			table.insert(sequence, {parent = sequence, tag = tag})
			sequence = table.last(sequence)
		elseif token == ")" then
			sequence = sequence.parent
			assert(sequence, "too many `)`")
		else
			table.insert(sequence, token)
		end
	end
	assert(not sequence.parent, "too many `(`")

	-- Parse individual tokens
	local stack = {}
	local modifierStack = {}
	for _, element in ipairs(sequence) do
		assert(#stack == #modifierStack)

		if type(element) == "string" then
			local modifiers = table.last(modifierStack)

			-- Process special modifiers
			if element:sub(1, 1) == "." then
				-- Extract a field
				local accessor = table.getter(element:sub(2))
				table.insert(stack, parser.map(table.remove(stack), accessor))
			elseif element:sub(1, 1) == "=" then
				-- Name a field
				modifiers["="] = element:sub(2)
			elseif element:sub(1, 1) == "!" then
				-- Require a field
				modifiers["!"] = element:sub(2):gsub("_", " ")
			else
				local newModifiers = {}
				if element:sub(1, 1) == "`" then
					newModifiers["="] = "_"
				end
				table.insert(stack, parser.query(element))
				table.insert(modifierStack, newModifiers)
			end
		else
			assert(#element >= 2, "unnecessary parenthesis")

			local serialized = table.concat(element, " ")
			table.insert(stack, parser.query(serialized, element.tag))
			table.insert(modifierStack, {})
		end
	end

	if #stack == 1 then
		return stack[1]
	end

	assert(type(tag) == "string")
	local components = {tag = tag}
	for i = 1, #stack do
		table.insert(components, {
			modifierStack[i]["="],
			stack[i],
			modifierStack[i]["!"],
		})
	end

	return parser.composite(components)
end

function parser.endOfStream()
	return function(stream)
		if stream:size() ~= 0 then
			return nil
		end
		return true, stream
	end
end

-- REPRESENTS a streamable sequence of tokens
function parser.Stream(list, offset)
	if offset then
		offset = offset or 0
		assert(type(offset) == "number", "offset must be an integer")
		assert(offset % 1 == 0, "offset must be an integer")
	else
		offset = 0

		-- Validate that it looks like a list of tokens
		for i = 1, #list do
			assert(list[i].location)
		end
	end
	assert(list.file, "needs list.file")

	return {
		_list = list,
		_offset = offset,
		head = function(self)
			return self._list[1 + self._offset]
		end,
		rest = function(self)
			assert(self:size() > 0, "stream:rest() requires stream:size() > 0")
			return parser.Stream(self._list, self._offset + 1)
		end,
		size = function(self)
			return #self._list - self._offset
		end,
		location = function(self)
			if self:size() == 0 then
				return parser.config.locationFinal(self._list.file)
			else
				return self:head().location
			end
		end,
		priorLocation = function(self)
			if self._offset == 0 then
				return parser.config.locationInitial(self._list.file)
			end
			return self._list[self._offset].location
		end,
	}
end

return parser
