-- Test script for the Lua smol compiler

local filter = arg[1] or ""

--------------------------------------------------------------------------------

local function printHeader(text, symbol, align)
	symbol = symbol or "-"
	align = align or "left"

	local middle = " " .. text .. " "
	local remaining = 80 - #middle
	local left, right

	if align == "left" then
		left = 2
		right = remaining - left
	elseif align == "center" then
		left = math.floor(remaining / 2) - 1
		right = remaining - left
	else
		error "unknown alignment"
	end

	assert(left + #middle + right == 80 or #middle+4 >= 80)
	print("")
	print(symbol:rep(left) .. middle .. symbol:rep(right))
	print("")
end

function string.spaces(s)
	return (s:gsub("\t", "    ")) -- TODO
end

local function printBox(lines)
	local WIDTH = 80
	local bar = "+" .. string.rep("-", WIDTH-2) .. "+"
	local out = {bar}
	for _, line in ipairs(lines) do
		local row = string.spaces("|\t" .. line)
		row = row .. string.rep(" ", WIDTH - 1 - #row) .. "|"
		table.insert(out, row)
	end
	table.insert(out, bar)
	print(table.concat(out, "\n"))
end

--------------------------------------------------------------------------------

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
	printHeader("Detailed Results", "@", "center")

	for _, pass in ipairs(passes) do
		print("PASS: " .. pass.name)
	end

	for _, fail in ipairs(fails) do
		printBox {
			"FAIL: " .. fail.name,
			"\tExpected: " .. fail.expected,
			"\tBut got:  " .. fail.got,
			fail.reason and "\t" .. fail.reason,
		}
		print()
	end

	printHeader("Summary Results", "@", "center")
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
		"lua src/compiler.lua",
		" ", sources,
		" ", main,
	}

	local status = os.execute(command)
	while status > 255 do
		status = status / 256
	end
	return status
end

-- (1) Run all negative tests
for test in io.popen("ls tests-negative", "r"):lines() do
	if test:find(filter, 1, true) then
		printHeader("TEST " .. test)
		local status = compiler("tests-negative/" .. test, "test:Test")
		if status ~= 45 then
			FAIL {name = test, expected = 45, got = status}
		else
			PASS {name = test}
		end
	end
end

-- (2) Run all positive tests
for test in io.popen("ls tests-positive", "r"):lines() do
	if test:find(filter, 1, true) then
		printHeader("TEST " .. test)
		local status = compiler("tests-positive/" .. test, "test:Test")
		if status ~= 0 then
			FAIL {name = test, expected = 0, got = status}
		else
			local generatedOkay = os.execute("lua output.lua > tests-positive/" .. test .. "/out.last")
			--if generatedOkay ~= 0 then
			--	FAIL {name = test, expected = status, got = status, reason = "runtime error"}
			--else
				--local correct = os.execute("diff -w tests-positive/" .. test ..  "/out.last tests-positive/" .. test .. "/out.correct")
				--if correct == 0 then
					PASS {name = test}
				--else
				--	FAIL {name = test, expected = status, got = status, reason = "wrong output"}
				--end
			--end
		end
	end
end

-- (3) Report
REPORT()
