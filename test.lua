-- Test script for the Lua smol compiler.
-- To run all tests,
--         lua test.lua

-- usage:
--         lua test.lua <query>
-- if <query> is blank, all tests are run.
-- if <query> begins with -, only negative tests are run.
-- if <query> begins with +, only positive tests are run.
-- if <query> contains text after an (optional) initial + or -, only tests whose
--     names contain the query string are run.

-- For example, to run all verification tests that the compiler should reject,
--         lua test.lua -verify

--------------------------------------------------------------------------------

-- ENVIRONMENT REQUIREMENTS

-- `ls` must be a utility available in the shell that lists file names in a
-- directory, one per line.

-- `gcc` must be a utility available in the shell that compiles C programs.
-- The `-std=c99` flag is specified with `-pedantic`.

--- `diff` must be a utility available in the shell that compares text files.

-- Searches the current directory for folders named `tests-positive` and
-- `tests-negative`.

-- `tests-positive` should contain one or more folders; each is a test-category.
-- Each test category should contain one or more folders; each is a test-case.
-- Each positive test-case should contain:
-- + `out.correct`, the text that the test case should generate on standard
--   output
-- + `test.smol`, a test file in the `test` package with main class `test:Test`.
-- + any additional `.smol` files.
-- Positive test-cases should compile and run successfully.

-- `tests-negative` should contain one or more folders; each is a test-category.
-- Each test category should contain one or more folders; each is a test-case.
-- Each negative test-case should contain:
-- + `test.smol`, a test file in the `test` package with main class `test:Test`.
-- + any additional `.smol` files.
-- Negative test-cases should be rejected by the compiler gracefully. They
-- should not create any executable or output.

--------------------------------------------------------------------------------

local filter = arg[1] or ""
local mode = filter:sub(1, 1)
if mode == "+" or mode == "-" then
	filter = filter:sub(2)
else
	mode = ""
end

local SEP = arg[2] or "/"
local remainingArguments = arg[3] or ""

--------------------------------------------------------------------------------

local function shell(command)
	local status = os.execute(command)
	return status == 0, status
end

local function path(elements)
	return table.concat(elements, SEP)
end

local function ls(directory)
	local contents = {}
	-- TODO: make this more portable and robust
	for line in io.popen("ls " .. directory, "r"):lines() do
		table.insert(contents, line)
	end
	return contents
end

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

-- Converts tabs to 4 spaces in a string that doesn't contain newlines
function string.spaces(s)
	assert(not s:find("\n"))
	local out = ""
	for i = 1, #s do
		if s:sub(i, i) ~= "\t" then
			out = out .. s:sub(i, i)
		else
			repeat
				out = out .. " "
			until #out % 4 == 0
		end
	end
	return out
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

local BEGIN_TIME = os.time()
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
	local elapsed = os.difftime(os.time(), BEGIN_TIME)
	print("Total time elapsed: " .. tostring(elapsed) .. " seconds")
	if #fails == 0 and #passes > 0 then
		print("Happy! :D")
		os.exit(0)
	else
		print("Sad. :(")
		os.exit(1)
	end
end

--------------------------------------------------------------------------------

local function compiler(directory, main)
	assert(type(directory) == "string")
	assert(type(main) == "string")

	local sources = {}
	for _, file in ipairs(ls(directory)) do
		if file:match "%.smol$" then
			table.insert(sources, path {directory, file})
		end
	end

	local command = table.concat {
		arg[-1] .. " " .. path {"src", "compiler.lua"},
		" --sources ", table.concat(sources, "    "),
		" --main ", main,
		" ", remainingArguments
	}

	local status = os.execute(command)
	while status > 255 do
		status = status / 256
	end
	return status
end

local positiveTests = {}
for _, category in ipairs(ls "tests-positive") do
	for _, test in ipairs(ls("tests-positive/" .. category)) do
		table.insert(positiveTests, path {category, test})
	end
end

local negativeTests = {}
for _, category in ipairs(ls "tests-negative") do
	for _, test in ipairs(ls("tests-negative/" .. category)) do
		table.insert(negativeTests, path {category, test})
	end
end

if mode ~= "+" then
	-- (1) Run all negative tests
	for _, test in ipairs(negativeTests) do
		if test:find(filter, 1, true) then
			printHeader("TEST " .. test)
			local status = compiler("tests-negative/" .. test, "test:Test")
			if status ~= 45 then
				FAIL {name = "- " .. test, expected = 45, got = status}
			else
				PASS {name = "- " .. test}
			end
		end
	end
end

if mode ~= "-" then
	-- (2) Run all positive tests
	for _, test in ipairs(positiveTests) do
		if test:find(filter, 1, true) then
			printHeader("TEST " .. test)
			local before = os.time()
			local status = compiler("tests-positive/" .. test, "test:Test")
			local elapsed = os.difftime(os.time(), before)
			print("ELAPSED:", elapsed)
			if status ~= 0 then
				FAIL {name = "+ " .. test, expected = 0, got = status}
			else
				local bin = "\"\"tests-positive" .. SEP .. test .. SEP .. "bin\"\""
				local flags = {
					"-g3",
					"-pedantic",
					"-std=c99",
					"-Werror",
					"-Wall",
					"-Wextra",
					"-Wconversion",
					-- Disable unhelpful warnings
					"-Wno-unused-parameter",
					"-Wno-unused-but-set-variable",
					"-Wno-unused-variable",
				}
				local compiles = shell("gcc " .. table.concat(flags, " ") .. " output.c -o " .. bin)
				if compiles then
					local outFile = path {"tests-positive", test, "out.last"}
					local runs = shell("" .. bin .. " > " .. outFile)
					if runs then
						local correctFile = path {"tests-positive", test, "out.correct"}
						local correct = shell("diff -w " .. correctFile .. " " .. outFile)
						if correct then
							PASS {name = "+ " .. test}
						else
							FAIL {name = "+ " .. test, expected = 0, got = 1, reason = "wrong output"}
						end
					else
						FAIL {name = "+ " .. test, expected = 0, got = 1, reason = "bin failed"}
					end
				else
					FAIL {name = "+ " .. test, expected = 0, got = 1, reason = "gcc rejected"}
				end
			end
		end
	end
end

-- (3) Report
REPORT()
