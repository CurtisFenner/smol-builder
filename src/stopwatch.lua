local Stopwatch = {}

function Stopwatch.new(title, limit)
	assert(type(title) == "string")

	local instance = {
		_title = title,
		_count = 1,
		_clocks = {},
		_began = os.clock(),
		_limit = limit or 0,
		_beforeTime = false,
		_beforeName = false,
	}
	return setmetatable(instance, {__index = Stopwatch})
end

function Stopwatch:before(name)
	assert(not self._beforeTime, "missing :after() call")
	self._beforeName = name
	self._beforeTime = os.clock()

	self._clocks[name] = self._clocks[name] or {
		time = 0,
		count = 0,
	}
end

function Stopwatch:after(name)
	assert(self._beforeTime, "missing :before() call")
	assert(self._beforeName == name, "names must match")

	local elapsed = os.clock() - self._beforeTime
	self._clocks[name].time = self._clocks[name].time + elapsed
	self._clocks[name].count = self._clocks[name].count + 1

	self._beforeName = false
	self._beforeTime = false
end

function Stopwatch:clock(name, f)
	self:before(name)
	local r = {f()}
	self:after(name)
	return table.unpack(r)
end

function Stopwatch:tick()
	self._count = self._count + 1
end

function Stopwatch:finish()
	local totalTime = os.clock() - self._began
	if totalTime < self._limit or true then
		return
	end

	local message = {self._title, " took ", totalTime, "s\n"}
	local ps = {}
	local longest = 0
	local remaining = totalTime
	for k, v in pairs(self._clocks) do
		longest = math.max(longest, #k)
		table.insert(ps, {name = k, count = v.count, time = v.time})
		remaining = remaining - v.time
	end
	table.insert(ps, {
		name = "REMAINING",
		time = remaining,
		count = self._count,
	})
	table.sort(ps, function(a, b) return a.time > b.time end)
	for _, v in pairs(ps) do
		table.insert(message, "\t")
		table.insert(message, v.name)
		table.insert(message, ": ")
		table.insert(message, string.rep(" ", longest - #v.name))
		table.insert(message, string.format("%.3fs     %.3fsea * %d\n", v.time, v.time / v.count, v.count))
	end
	print(table.concat(message))
end

return Stopwatch
