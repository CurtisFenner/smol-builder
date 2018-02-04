local profile = {}

local stack = {[0] = {skipped = 0}}
local summary = {}

-- Times elapsed quicker than this threshold will not be printed as the program
-- is running.
local PRINT_SECONDS = 0.1

function profile.open(message)
	assert(type(message) == "string", "type of message must be a string")
	table.insert(stack, {
		message = message,
		time = os.clock(),
		shown = false,
		skipped = 0,
	})
end

function profile.close(message)
	local top = stack[#stack]
	local parent = stack[#stack - 1]
	assert(top, "top")
	assert(
		top.message == message,
		"top.message is `" .. top.message .. "` but you gave `" .. message .. "`"
	)
	local elapsed = os.clock() - top.time

	if elapsed >= PRINT_SECONDS then
		for i = 1, #stack do
			if not stack[i].shown then
				print("|" .. string.rep("    ", i - 1) .. "(( " .. stack[i].message)
				stack[i].shown = true
			end
		end
		if top.skipped ~= 0 then
			print("|" .. string.rep("    ", #stack) .. "(( x" .. top.skipped .. " skipped )) ")
		end
		local alignment = "|" .. string.rep("    ", #stack - 1)
		print(alignment .. ")) " .. top.message .. " " .. string.format("%.3f", elapsed))
	else
		parent.skipped = parent.skipped + 1
	end

	table.remove(stack)

	summary[message] = summary[message] or {
		message = message,
		count = 0,
		min = math.huge,
		max = 0,
		sum = 0,
	}
	summary[message].count = summary[message].count + 1
	summary[message].min = math.min(summary[message].min, elapsed)
	summary[message].max = math.max(summary[message].max, elapsed)
	summary[message].sum = summary[message].sum + elapsed
end

function profile.peek()
	return stack[#stack].message
end

function profile.summarize()
	local longest = 0
	local list = {}
	for key, value in pairs(summary) do
		longest = math.max(longest, #key)
		table.insert(list, value)
	end
	table.sort(list, function(a, b)
		return a.sum > b.sum
	end)
	local function f(n)
		return string.format("%.3f", n)
	end
	for _, item in ipairs(list) do
		local mean = item.sum / item.count
		local pad = string.rep(" ", longest - #item.message)
		print(pad .. item.message .. "\tx" .. item.count .. "\t[" .. f(item.min) .. " -- " .. f(mean) .. " -- " .. f(item.max) .. "] for sum " .. f(item.sum))
	end
end

function profile.clocked(f, s)
	return function(...)
		profile.open(s)
		local out = {f(...)}
		profile.close(s)
		return unpack(out)
	end
end

local function busywait(t)
	local stop = os.clock() + t
	while os.clock() < stop do
	end
	return os.clock() - stop
end

return freeze(profile)
