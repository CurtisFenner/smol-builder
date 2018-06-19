-- RETURNS a list of tokens.
-- source: the contents of a source file.
-- filename: a human-readable name indicating this source file.
local function lexSmol(source, filename)
	assert(isstring(source))
	assert(isstring(filename))

	-- Normalize line end-ings
	source = source:gsub("\r*\n\r*", "\n")
	source = source:gsub("\r", "\n")
	source = source .. "\n"

	local IS_KEYWORD = {
		["case"] = true,
		["class"] = true,
		["do"] = true,
		["foreign"] = true,
		["if"] = true,
		["else"] = true,
		["elseif"] = true,
		["import"] = true,
		["interface"] = true,
		["is"] = true,
		["match"] = true,
		["method"] = true,
		["new"] = true,
		["package"] = true,
		["return"] = true,
		["static"] = true,
		["union"] = true,
		["var"] = true,

		-- verification
		["assert"] = true,
		["ensures"] = true,
		["forall"] = true,
		["requires"] = true,
		["when"] = true,

		-- built-in types
		["Boolean"] = true,
		["Int"] = true,
		["Never"] = true,
		["Self"] = true,
		["String"] = true,
		["Unit"] = true,

		-- values
		["this"] = true,
		["true"] = true,
		["false"] = true,
		["unit"] = true,
	}

	-- Define token parsing rules
	local TOKENS = {
		{
			-- type keywords, type names
			"[A-Z][A-Za-z0-9]*",
			function(x)
				if IS_KEYWORD[x] then
					return {tag = "type-keyword", name = x}
				end
				return {tag = "typename", name = x}
			end
		},
		{
			-- keywords, local identifiers
			"[a-z][A-Za-z0-9]*",
			function(x)
				if IS_KEYWORD[x] then
					return {tag = "keyword", keyword = x}
				end
				return {tag = "identifier", name = x}
			end
		},
		{
			-- generic type parameters
			"#[A-Z][A-Za-z0-9]*",
			function(x)
				if IS_KEYWORD[x:sub(2)] then
					return {tag = "keyword-generic", name = x:sub(2)}
				end
				return {tag = "generic", name = x:sub(2)}
			end
		},
		{
			-- whitespace
			"%s+",
			function(x)
				return false
			end
		},
		{
			-- comments
			"//[^\n]*",

			-- (greedy)
			function(x)
				return false
			end
		},
		{
			-- punctuation (braces, commas, etc)
			"[.,:;!|()%[%]{}]",
			function(x)
				return {tag = "punctuation"}
			end
		},
		{
			-- operators and assignment
			"[+%-*/<>=%%^]+",
			function(x)
				if x == "=" then
					return {tag = "assign"}
				end
				return {tag = "operator"}
			end
		},
		{
			-- integer literals
			"[0-9]+",
			function(x)
				return {tag = "integer-literal", value = tonumber(x)}
			end
		},
	}

	local QUOTE = "\""
	local BACKSLASH = "\\"

	-- Create a list of the lines in the program, for location messages
	local sourceLines = {}
	for line in (source .. "\n"):gmatch("(.-)\n") do
		line = line:gsub("\r", "")
		repeat
			local index = line:find("\t")
			if index then
				local spaces = string.rep(" ", 4 - (index - 1) % 4)
				line = line:sub(1, index - 1) .. spaces .. line:sub(index + 1)
			end
		until not index
		line = line:gsub("\t", "    ")

		-- TODO: this should be aligned
		table.insert(sourceLines, line)
	end

	local tokens = {}

	-- Track the location into the source file each token is
	local line = 1
	local column = 1
	local index = 0

	-- RETURNS a Location of the last non-whitespace character
	local function advanceCursor(str)
		assert(isstring(str))
		local final = {line = line, column = column, index = index}
		for c in str:gmatch(".") do
			if c:match "%S" then
				final = {line = line, column = column, index = index}
			end
			if c == "\r" then
				-- Carriage returns do not affect reported cursor location
			elseif c == "\n" then
				column = 1
				index = 0
				line = line + 1
			elseif c == "\t" then
				-- XXX: This reports column (assuming tab = 4)
				-- rather than character.
				-- (VSCode default behavior when tabs are size 4)
				-- (Atom default behavior counts characters)
				column = math.ceil(column / 4) * 4 + 1
				index = index + 1
			else
				column = column + 1
				index = index + 1
			end
		end
		final.filename = filename
		final.sourceLines = sourceLines
		return final
	end

	while #source > 0 do
		local location = {
			begins = freeze {
				filename = filename,
				sourceLines = sourceLines,
				line = line,
				column = column,
				index = index,
			},
		}

		-- Tokenize string literals
		if source:sub(1, 1) == QUOTE then
			local SPECIAL = {
				n = "\n",
				t = "\t",
				r = "\r",
				["0"] = string.char(0),
				[QUOTE] = QUOTE,
				[BACKSLASH] = BACKSLASH,
			}
			local content = ""
			local escaped = false
			for i = 2, #source do
				local c = source:sub(i, i)
				if c == "\n" or c == "\r" then
					location.ends = advanceCursor(source:sub(1, i - 1))
					quit(
						"The compiler found an unfinished string literal ",
						location
					)
				end
				if escaped then
					if not SPECIAL[c] then
						location.ends = advanceCursor(source:sub(1, i))
						quit(
							"The compiler found an unknown escape sequence",
							" `\\",
							c,
							"`",
							" in a string literal ",
							location
						)
					end
					content = content .. SPECIAL[c]
					escaped = not escaped
				elseif c == BACKSLASH then
					escaped = true
				elseif c == QUOTE then
					-- Update location
					location.ends = advanceCursor(source:sub(1, i))
					local lexeme = source:sub(1, i)

					-- String literal is complete
					source = source:sub(i + 1)
					table.insert(tokens, freeze {
						tag = "string-literal",
						value = content,
						location = location,
						lexeme = lexeme,
					})
					break
				else
					content = content .. c
				end
			end
		else
			-- Search for matching token parsing rule
			local matched = false
			for _, tokenRule in ipairs(TOKENS) do
				local match = source:match("^" .. tokenRule[1])
				if match then
					-- Consume token and add to token stream
					local token = tokenRule[2](match)
					assert(
						type(token) == "table" or rawequal(token, false),
						"token must be table `" .. tokenRule[1] .. "`"
					)

					location.ends = advanceCursor(match)
					if token then
						token.location = location
						token.lexeme = match
						table.insert(tokens, freeze(token))
					end

					-- Advance the cursor through the text file
					source = source:sub(#match + 1)

					matched = true
					break
				end
			end

			-- Check for an unlexible piece of source
			if not matched then
				local badToken = table.with(location, "ends", location.begins)
				quit("The compiler could not recognize any token ", badToken)
			end
		end
	end

	return freeze(tokens)
end

return lexSmol
