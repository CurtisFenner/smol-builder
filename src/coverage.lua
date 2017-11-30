local visited = {}

local writeTarget = table.remove(arg, 1)
local file, err = io.open(writeTarget, "w")
if err then
	print(err)
	os.exit(1)
end

local toExecute = table.remove(arg, 1)

local function trace(event)
	local info = debug.getinfo(2)
	local location = info.short_src .. ":" .. info.currentline
	if not visited[location] then
		file:write(location .. "\n")
		file:flush()
		visited[location] = true
	end
end
debug.sethook(trace, "c")

dofile(toExecute)

file:close()
