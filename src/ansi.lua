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

return ansi
