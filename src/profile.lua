local profile = {}

local stack = {}

function profile.open(message)
	--print(string.rep("    ", #stack) .. "(( " .. message)
	table.insert(stack, {message = message, time = os.clock()})
end

function profile.close()
	local top = table.remove(stack)
	local elapsed = os.clock() - top.time
	--print(string.rep("    ", #stack) .. ")) " .. top.message .. " " .. string.format("%.2f", elapsed))
end

return profile
