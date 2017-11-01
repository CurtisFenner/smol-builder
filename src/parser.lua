-- Curtis Fenner, copyright (C) 2017
-- Parser ----------------------------------------------------------------------

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
function parser.map(parser, f, includeLocation)
	assert(type(f) == "function")

	return function(stream, grammar)
		assert(grammar)

		local begins = stream:location()

		local object, rest = parser(stream, grammar)
		if not rest then
			return nil
		end

		local out = f(object)
		assert(out ~= nil)

		if includeLocation then
			local ends = rest:priorLocation()
			out = table.with(out, "location", {begins = begins.begins, ends = ends.ends})
		end
		return out, rest
	end
end

-- RETURNS a parser
function parser.choice(options)
	assert(type(options) == "table" or type(options) == "userdata",
		"parser.choice expects a list")
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
	assert(type(components) == "table" or type(components) == "userdata")
	assert(type(components.tag) == "string")

	-- A human readable context of the fields
	local contextMiddle = " in " .. components.tag
	local contextBegin = " to begin " .. components.tag
	local contextFinish = " to finish " .. components.tag

	for i = 1, #components do
		assert(#components[i] >= 2)
		assert(type(components[i][1]) == "string",
			"component must provide key as string")
		assert(components[i][1] ~= "tag",
			"component cannot use key 'tag'")
		assert(components[i][1] ~= "location",
			"component cannot use key 'location'")

		assert(type(components[i][2]) == "function",
			"component must provide member as parser"
			.. " (key `" .. components[i][1] .. "`"
			.. "; " .. i .. " of " .. #components ..  ")")

		assert(#components[i] <= 3)
		assert(components[i][3] == nil or type(components[i][3]) == "string")
	end

	return function(stream, parsers)
		-- Annotate metadata
		local frontLocation = stream:location()
		local object = {
			tag = components.tag,
			location = {
				begins = frontLocation.begins,
				ends = frontLocation.ends,
			},
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
				object.location.ends = rest:priorLocation().ends
			elseif required then
				-- This member was a required cut; report an error with
				-- the input
				local context = contextMiddle
				if i == 1 then
					context = contextBegin
				elseif i == #components then
					context = contextFinish
				end
				quit("The compiler expected ", required, context,
					" ", stream:location())
			else
				-- This failed to parse
				return nil
			end
		end

		assert(#extracts <= 1)
		if #extracts == 1 then
			object = object[extracts[1]]
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
		return {object.first, unpack(object.rest)}
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
				quit("The compiler expected ", expected,
					" after `" .. delimiter .. "` ",
					stream:location())
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
			return parser.delimited(parser.query(before), count, delimiter,
				describe(before))
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

return parser
