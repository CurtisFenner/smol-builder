-- Curtis Fenner
-- ANSI formatting helpers

local ansi = {}
ansi.enabled = true or package.config:sub(1, 1) == "/"

function ansi._format(text, format)
	if not ansi.enabled then
		return text
	end
	return format:gsub("%[", "\27[") .. text .. "\27[0m"
end

function ansi.resetMark()
	if not ansi.enabled then
		return ""
	end
	return "\27[0m"
end

function ansi.blue(text)
	return ansi._format(text, "[34m[1m")
end

function ansi.red(text)
	return ansi._format(text, "[31m[1m")
end

function ansi.cyan(text)
	return ansi._format(text, "[36m[1m")
end

function ansi.gray(text)
	return ansi._format(text, "[30m[1m")
end

function ansi.foldFormatting(fs)
	if #fs <= 3 then
		return fs
	end
	return {fs[#fs - 2], fs[#fs - 1], fs[#fs]}
end

function ansi.measure(text)
	assert(not text:find "\r")

	local lines = {}
	local width = 0
	for line in (text .. "\n"):gmatch "[^\n]+\n" do
		local formats = {}
		for x in line:gmatch "\27%[%d+m" do
			table.insert(formats, x)
		end
		local toMeasure = line:gsub("\27%[%d+m", "")
		local line = line:sub(1, -2)
		table.insert(lines, {text = line, width = #toMeasure, formats = formats})
	end
	return lines
end

function ansi.tabless(s, t)
	t = t or 8

	-- TODO: do this properly
	return (s:gsub("\t", string.rep(" ", t)))
end

function ansi.horizontal(...)
	local columns = {...}
	if #columns == 1 then
		return columns[1]
	elseif #columns == 2 then
		local a = ansi.tabless(ansi.resetMark() .. columns[1])
		local b = ansi.tabless(ansi.resetMark() .. columns[2])

		local la = ansi.measure(a)
		local lb = ansi.measure(b)

		local leftFormat = {}
		local rightFormat = {}

		local widest = 0
		for _, line in ipairs(la) do
			widest = math.max(widest, line.width)
		end

		local output = {}
		for i = 1, math.max(#la, #lb) do
			if la[i] then
				table.insert(output, table.concat(leftFormat))
				table.insert(output, la[i].text)
				table.insert(output, string.rep(" ", widest - la[i].width))

				-- Update formatting state for left side
				for _, f in ipairs(la[i].formats) do
					table.insert(leftFormat, f)
				end
				leftFormat = ansi.foldFormatting(leftFormat)
			else
				table.insert(output, string.rep(" ", widest))
			end
			if lb[i] then
				table.insert(output, table.concat(rightFormat))
				table.insert(output, lb[i].text)

				-- Update formatting state for right side
				for _, f in ipairs(lb[i].formats) do
					table.insert(rightFormat, f)
				end
				rightFormat = ansi.foldFormatting(rightFormat)
			end
			table.insert(output, "\n")
		end
		return table.concat(output)
	end
	local u = ansi.horizontal(columns[1], columns[2])
	for i = 3, #columns do
		u = ansi.horizontal(u, columns[i])
	end
	return u
end

return ansi
