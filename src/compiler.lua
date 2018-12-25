-- A transpiler for Smol -> C.

local ARGV = arg

INVOCATION = table.concat {
	ARGV[-1],
	" ",
	ARGV[0],
	" ",
	table.concat(ARGV, " "),
	"\nsmol version 0??"
}

--------------------------------------------------------------------------------

-- Cache imported files
local _imported = {}
function import(name)
	if _imported[name] then
		return _imported[name]
	end
	local directory = ARGV[0]:gsub("[^/\\]+$", "")
	_imported[name] = dofile(directory .. name)
	return _imported[name]
end

local showLocation

local ansi = import "ansi.lua"
local trace = import "trace.lua"

-- DISPLAYS the concatenation of the input,
-- and terminates the program.
-- DOES NOT RETURN.
function quit(first, ...)
	local rest = {...}
	for i = 1, select("#", ...) do
		assert(rest[i] ~= nil, "missing arg " .. i + 1)
	end

	for i = 1, #rest do
		if type(rest[i]) == "number" then
			rest[i] = tostring(rest[i])
		elseif type(rest[i]) ~= "string" then
			assert(rest[i] ~= nil, "rest[i] ~= nil")
			rest[i] = showLocation(rest[i])
		end
	end
	rest = table.concat(rest)

	if not first:match("^[A-Z]+:\n$") then
		print(table.concat {ansi.red("ERROR"), ":\n", first, rest})
		os.exit(45)
	else
		print(table.concat {ansi.cyan(first), rest})
		os.exit(40)
	end
end

import "extend.lua"
import "types.lua"
import "def.lua"

--------------------------------------------------------------------------------

local LOCATION_MODE = "column"

-- RETURNS a string representing the location, respecting the command line
-- location mode
function showLocation(location)
	local from, to = location.from, location.to
	local source = location.file.lines
	assert(from and to and source)

	-- Compute human-readable description of location
	local contextLines = {}
	for line = math.max(1, from.line - 1), math.min(#source, to.line + 1) do
		local lineNum = tostring(line)
		local longestLineNumber = tostring(#source)
		local num = string.rep(" ", #longestLineNumber - #lineNum) .. lineNum
		table.insert(contextLines, "\t" .. num .. " | " .. source[line])
		local pointy = ""
		for i = 1, #source[line] do
			local after = (line == from.line and i >= from.column) or from.line < line
			local before = (line == to.line and i <= to.column) or line < to.line
			if after and before and source[line]:sub(1, i):find "%S" then
				pointy = pointy .. "^"
			else
				pointy = pointy .. " "
			end
		end
		if pointy:find "%S" then
			local align = string.rep(" ", #tostring(#source))
			table.insert(contextLines, "\t" .. align .. " | " .. ansi.red(pointy))
		end
	end
	local sourceContext = table.concat(contextLines, "\n")
	local cite = location.file.filename .. ":" .. from.line .. ":" .. from.column
	local location = "at " .. cite .. "\n" .. sourceContext .. "\n"

	-- Include indexes for computer consumption of error messages
	if LOCATION_MODE == "index" then
		location = table.concat {
			location,
			"@",
			location.file.filename,
			":",
			from.line,
			":",
			from.index,
			"::",
			to.line,
			":",
			to.index,
		}
	end
	return location
end

--------------------------------------------------------------------------------

local syntax = import "syntax.lua"
local calculateSemantics = import "semantics.lua"
local codegen = {
	c = import "codegen/genc.lua",
}
local verify = import "verify.lua"
local tokenization = import "tokenization.lua"

--------------------------------------------------------------------------------

local function quitUsage()
	quit(
		"USAGE:\n",
		"\tlua compiler.lua",
		" --sources <sequence of one-or-more .smol files>",
		" --main <mainpackage:Mainclass>\n",
		"\n",
		"\tFor example,\n\t\tlua compiler.lua --sources foo.smol --main main:Main\n",
		"\n",
		"\tOptional Flags:\n",
		"\t\t--nocolor\n\t\t\tDo NOT use ANSI escape codes to color output\n",
		"\t\t--color\n\t\t\tDO use ANSI escape codes to color output\n",
		"\t\t--location column\n\t\t\tThe default location description, for humans.\n",
		"\t\t--location index\n\t\t\tLocation description, for machines.\n"
	)
end

local commandMap = {}
local commandFlag = false
for i = 1, #ARGV do
	local flag = ARGV[i]:match("^%-%-(.*)$")
	if flag then
		if commandMap[flag] then
			quitUsage()
		end
		commandMap[flag] = {}
		commandFlag = flag
	elseif not commandFlag then
		quitUsage()
	else
		table.insert(commandMap[commandFlag], ARGV[i])
	end
end

if commandMap.color then
	ansi.enabled = true
elseif commandMap.nocolor then
	ansi.enabled = false
end

-- Check the command line arguments
if not commandMap.main or #commandMap.main ~= 1 then
	quitUsage()
elseif not commandMap.sources or #commandMap.sources == 0 then
	quitUsage()
end

if commandMap.location then
	LOCATION_MODE = commandMap.location[1]

	if LOCATION_MODE ~= "column" and LOCATION_MODE ~= "index" then
		quitUsage()
	end
end

local knownFlags = {
	color = true,
	nocolor = true,
	location = true,
	main = true,
	sources = true,
}

-- Check that only known command line flags are used
for key in pairs(commandMap) do
	if not knownFlags[key] then
		quitUsage()
	end
end

-- Main ------------------------------------------------------------------------

-- RETURNS the string prefix in common to all members of list of strings
local function commonPrefix(list)
	assert(#list >= 1)
	local out = list[1]
	for i = 2, #list do
		while list[i]:sub(1, #out) ~= out do
			-- Shorten
			out = out:sub(1, -2)
		end
	end
	return out
end

local commonRaw = commonPrefix(commandMap.sources)
local common = commonRaw:gsub("%.[a-zA-Z0-9]+$", ""):gsub("[a-zA-Z_0-9]+$", "")
local sourceFiles = {}
for _, source in ipairs(commandMap.sources) do
	table.insert(sourceFiles, {
		path = source,
		short = source:sub(#common + 1),
	})
end

table.insert(sourceFiles, {
	path = "<compiler-core>",
	short = "<compiler-core>",
	contents = [==[
package core;

class Out {
	foreign static println!(message String) Unit;
}

class ASCII {
	foreign static formatInt(value Int) String;
}

interface Showable {
	static showType() String;
	method show() String;
}

union Option[#T | #T is Eq] {
	var some #T;
	var none Unit;

	static makeSome(value #T) Option[#T]
	ensures return is some
	ensures return.some == value {
		return new(some = value);
	}

	static makeNone() Option[#T]
	ensures return is none {
		return new(none = unit);
	}

	method get() #T
	requires this is some
	ensures return == this.some {
		var out #T = this.some;
		assert out == this.some;
		return out;
	}
}

class Pair[#A, #B | #A is Eq, #B is Eq] is Eq {
	var left #A;
	var right #B;

	method getLeft() #A
	ensures return == this.left {
		return this.left;
	}

	method getRight() #B
	ensures return == this.right {
		return this.right;
	}

	static make(left #A, right #B) Pair[#A, #B]
	ensures return.getLeft() == left
	ensures return.getRight() == right {
		return new(left = left, right = right);
	}

	method eq(other Pair[#A, #B]) Boolean {
		return (this.left == other.left).and(this.right == other.right);
	}
}

interface Orderable {
	// RETURNS true when this is smaller than other in this ordering.
	method lessThan(other #Self) Boolean
	// ensures this.lessThan(this).not()
	// ensures forall (middle #Self) return when this.lessThan(middle).and( middle.lessThan(other)  )
	;
}

interface Eq {
	// RETURNS true when these elements are equal such that
	// (a == b) => f(a) == f(b)
	method eq(other #Self) Boolean;
}

class WInt is Eq {
	var value Int;

	method get() Int ensures return == this.value {
		return this.value;
	}

	static make(n Int) WInt ensures return.get() == n {
		var out WInt = new(value = n);
		assert out.value == n;
		assert out.get() == n;
		return out;
	}

	method eq(other WInt) Boolean {
		return this.value == other.value;
	}
}

]==]
})

-- Load and parse source files
local sourceParses = {}
for _, sourceFile in ipairs(sourceFiles) do
	local contents = sourceFile.contents
	if not contents then
		local file, err = io.open(sourceFile.path, "r")
		if not file then
			quit(
				"The compiler could not open source file `",
				sourceFile.path,
				"`"
			)
		end
		contents = file:read("*all")
		file:close()
		if not contents then
			quit(
				"The compiler could not read from the source file `",
				sourceFile.path,
				"`"
			)
		end
	end
	assert(contents)

	-- Lex contents
	local tokens = tokenization(contents, sourceFile.short)

	-- Parse contents
	table.insert(sourceParses, syntax.parseFile(tokens))
end

assert(#commandMap.main == 1)
local mainFunction = commandMap.main[1]

-- Get an intermediate representation of the program
local semantics = trace.run(
	calculateSemantics.semantics,
	sourceParses,
	mainFunction
)

-- Verify the assertions in the program statically hold
verify(semantics)

if semantics.main then
	-- Compile output in the given target
	-- TODO: read target
	local arguments = {out = "output.c"}
	local TARGET = "c"
	codegen[TARGET](semantics, arguments)
else
	print("Successfully verified " .. #sourceFiles .. " file(s)")
end
