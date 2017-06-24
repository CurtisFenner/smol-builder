-- Test script for the Lua smol compiler

local filter = arg[1] or ""

--------------------------------------------------------------------------------

local function printHeader(text)
	print("\n-- " .. text .. " " .. string.rep("-", 80 - #text - 4) .. "\n")
end

local passes = {}
local fails = {}

function PASS(p)
	assert(p.name)
	table.insert(passes, p)
	print("PASS: " .. p.name)
end

function FAIL(p)
	assert(p.name)
	assert(p.expected)
	assert(p.got)
	table.insert(fails, p)
	print("FAIL: " .. p.name)
end

function REPORT()
	printHeader("Detailed Results")

	for _, pass in ipairs(passes) do
		print("PASS: " .. pass.name)
	end

	for _, fail in ipairs(fails) do
		print("FAIL: " .. fail.name)
		print("\tExpected: " .. fail.expected)
		print("\tBut got:  " .. fail.got)
		print()
	end

	printHeader("Summary Results")
	print("Passed: " .. #passes)
	print("Failed: " .. #fails)
	if #fails == 0 and #passes > 0 then
		print("Happy! :D")
		os.exit(0)
	else
		print("Sad. :(")
		os.exit(1)
	end
end

--------------------------------------------------------------------------------

local function compiler(sources, main)
	assert(type(sources) == "string")
	assert(type(main) == "string")

	local command = table.concat {
		"lua compiler.lua",
		" ", sources,
		" ", main,
	}

	return os.execute(command)
end

-- (1) Run all negative tests
for test in io.popen("ls tests-negative", "r"):lines() do
	if test:find(filter, 1, true) then
		printHeader("TEST " .. test)
		local status = compiler("tests-negative/" .. test, "test:Test")
		if status ~= 45 and status ~= 45*256 then
			FAIL {name = test, expected = 45, got = status}
		else
			PASS {name = test}
		end
	end
end

-- (2) TODO: run all positive tests
for test in io.popen("ls tests-positive", "r"):lines() do
	if test:find(filter, 1, true) then
		printHeader("TEST " .. test)
		local status = compiler("tests-positive/" .. test, "test:Test")
		if status ~= 0 then
			FAIL {name = test, expected = 0, got = status}
		else
			PASS {name = test}
		end
	end
end

-- (3) Report
REPORT()
