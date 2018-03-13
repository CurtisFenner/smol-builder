-- A transpiler for Smol -> ???
-- Curtis Fenner, copyright (C) 2017

local ARGV = arg

INVOKATION = table.concat {
	ARGV[0],
	" ",
	table.concat(ARGV, " "),
	"\non ",
	os.date("!%c"),
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

-- DISPLAYS the concatenation of the input,
-- and terminates the program.
-- DOES NOT RETURN.
function quit(first, ...)
	local rest = {...}
	for i = 1, #rest do
		if type(rest[i]) == "number" then
			rest[i] = tostring(rest[i])
		elseif type(rest[i]) ~= "string" then
			if not rest[i].ends then
				print(...)
			end
			assertis(rest[i], "Location")
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

--------------------------------------------------------------------------------

local LOCATION_MODE = "column"

-- RETURNS a string representing the location, respecting the command line
-- location mode
function showLocation(location)
	assertis(location, "Location")

	local begins = location.begins
	local ends = location.ends

	if type(begins) == "string" or type(ends) == "string" then
		return "at " .. begins
	end

	local source = begins.sourceLines

	-- Compute human-readable description of location
	local context = {}
	for line = math.max(1, begins.line - 1), math.min(#source, ends.line + 1) do
		local num = string.rep(" ", #tostring(#source) - #tostring(line)) .. tostring(line) .. " "
		table.insert(context, "\t" .. num .. "| " .. source[line])
		local pointy = ""
		for i = 1, #source[line] do
			local after = (line == begins.line and i >= begins.column) or line > begins.line
			local before = (line == ends.line and i <= ends.column) or line < ends.line
			if after and before and source[line]:sub(1, i):find "%S" then
				pointy = pointy .. "^"
			else
				pointy = pointy .. " "
			end
		end
		if pointy:find "%S" then
			local align = string.rep(" ", #tostring(#source))
			table.insert(context, "\t" .. align .. " | " .. ansi.red(pointy))
		end
	end
	local sourceContext = table.concat(context, "\n")
	local cite = begins.filename .. ":" .. begins.line .. ":" .. begins.column
	local location = "at " .. cite .. "\n" .. sourceContext .. "\n"

	-- Include indexes for computer consumption of error messages
	if LOCATION_MODE == "index" then
		location = location .. "@" .. begins.filename .. ":" .. begins.line .. ":" .. begins.index .. "::" .. ends.line .. ":" .. ends.index
	end
	return location
end

--------------------------------------------------------------------------------

local profile = import "profile.lua"
local syntax = import "syntax.lua"
local calculateSemantics = import "semantics.lua"
local codegen = {
	c = import "codegen/genc.lua",
}
local verify = import "verify.lua"
local lexSmol = import "tokenization.lua"

--------------------------------------------------------------------------------

local function quitUsage()
	quit(
		"USAGE:\n",
		"\tlua compiler.lua",
		" --sources <sequence of one-or-more .smol files>",
		" --main <mainpackage:Mainclass>",
		"\n\n\tFor example, `lua compiler.lua --sources foo.smol --main main:Main`"
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

-- Check the command line arguments
if not commandMap.main or #commandMap.main ~= 1 then
	quitUsage()
elseif not commandMap.sources or #commandMap.sources == 0 then
	quitUsage()
end

if commandMap.location then
	-- TODO: assert that it is correct
	LOCATION_MODE = commandMap.location[1]
end

if commandMap.color then
	ansi.enabled = true
elseif commandMap.nocolor then
	ansi.enabled = false
end

-- Stream ----------------------------------------------------------------------

REGISTER_TYPE("Spot", choiceType(constantType "???", constantType "builtin", recordType {
	filename = "string",
	sourceLines = listType "string",
	line = "integer",
	column = "integer",
	index = "integer",
}))

REGISTER_TYPE("Location", recordType {
	begins = "Spot",
	ends = "Spot",
})

REGISTER_TYPE("Token", recordType {
	location = "Location",
	tag = "string",
	lexeme = "string",
})

-- Type Definitions ------------------------------------------------------------

REGISTER_TYPE("Semantics", recordType {
	classes = listType "ClassIR",
	interfaces = listType "InterfaceIR",
	builtins = listType(recordType {
		tag = constantType "builtin",
		name = "string",
		signatures = listType "Signature",
		type = "KeywordType+",
	}),
	unions = listType "UnionIR",
	functions = listType "FunctionIR",
	main = choiceType("string", constantType(false)),
})

REGISTER_TYPE("ClassIR", recordType {
	tag = constantType "class",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "InterfaceType+",
	signatures = listType "Signature",
	constraints = mapType("string", "InterfaceType+"),
	builtin = constantType(nil),
})

REGISTER_TYPE("UnionIR", recordType {
	tag = constantType "union",
	name = "string",
	fields = listType "VariableIR",
	generics = listType "TypeParameterIR",
	implements = listType "InterfaceType+",
	signatures = listType "Signature",
	constraints = mapType("string", "InterfaceType+"),
})

REGISTER_TYPE("InterfaceIR", recordType {
	tag = constantType "interface",
	name = "string",
	signatures = listType "Signature",
	generics = listType "TypeParameterIR",
})

REGISTER_TYPE("Definition", choiceType("ClassIR", "UnionIR", "InterfaceIR"))

REGISTER_TYPE("TypeParameterIR", recordType {
	name = "string",

	-- Type parameter name (e.g., "#Right")
	constraints = listType(recordType {
		interface = "InterfaceType+",
	}),
	location = "Location",
})

REGISTER_TYPE("FunctionIR", recordType {
	name = "string",
	parameters = listType "VariableIR",
	generics = listType "TypeParameterIR",
	returnTypes = listType "Type+",
	body = choiceType(constantType(false), "BlockSt"),
	signature = "Signature",
	definitionName = "string",
})

REGISTER_TYPE("Signature", recordType {
	name = "string",
	parameters = listType "VariableIR",
	returnTypes = listType "Type+",
	modifier = choiceType(constantType "static", constantType "method"),
	container = "string",
	foreign = "boolean",
	bang = "boolean",
	requiresAST = listType "ASTExpression",
	ensuresAST = listType "ASTExpression",
	logic = choiceType(constantType(false), mapType(
		"boolean",
		listType(listType(choiceType("boolean", constantType "*")))
	)),
	eval = choiceType(constantType(false), "function"),
})

REGISTER_TYPE("ASTExpression", recordType {
	tag = "string",

	-- TODO
})

REGISTER_TYPE("maybe", choiceType(constantType "yes", constantType "no", constantType "maybe"))

REGISTER_TYPE("StatementIR", intersectType("AbstractStatementIR", choiceType(
	-- Execution
	"AssignSt",
	"BlockSt",
	"BooleanLoadSt",
	"FieldSt",
	"GenericMethodCallSt",
	"GenericStaticCallSt",
	"IsASt",
	"LocalSt",
	"MatchSt",
	"MethodCallSt",
	"NewClassSt",
	"NewUnionSt",
	"IntLoadSt",
	"ReturnSt",
	"IfSt",
	"StaticCallSt",
	"StringLoadSt",
	"ThisSt",
	"UnitSt",
	"VariantSt",

	-- Verification
	"AssumeSt",
	"VerifySt",
	"ProofSt",
	"ForallSt",

	-- Nothing
	"NothingSt"
)))

REGISTER_TYPE("AbstractStatementIR", recordType {
	tag = "string",
	returns = "maybe",
})

EXTEND_TYPE("AssumeSt", "AbstractStatementIR", recordType {
	tag = constantType "assume",
	body = "nil",
	variable = "VariableIR",
	location = "Location",
})

EXTEND_TYPE("VerifySt", "AbstractStatementIR", recordType {
	tag = constantType "verify",
	body = "nil",
	variable = "VariableIR",
	checkLocation = "Location",
	conditionLocation = "Location",
	reason = "string",
})

-- Represents proof-only code (a block, but without codegen)
EXTEND_TYPE("ProofSt", "AbstractStatementIR", recordType {
	tag = constantType "proof",
	body = "StatementIR",
	returns = constantType "no",
})

EXTEND_TYPE("BlockSt", "AbstractStatementIR", recordType {
	tag = constantType "block",
	statements = listType "StatementIR",
})

EXTEND_TYPE("StringLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "string",
	destination = "VariableIR",
	string = "string",
	returns = constantType "no",
})

EXTEND_TYPE("LocalSt", "AbstractStatementIR", recordType {
	tag = constantType "local",
	variable = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NothingSt", "AbstractStatementIR", recordType {
	tag = constantType "nothing",
	returns = constantType "no",
})

EXTEND_TYPE("AssignSt", "AbstractStatementIR", recordType {
	tag = constantType "assign",
	source = "VariableIR",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("ReturnSt", "AbstractStatementIR", recordType {
	tag = constantType "return",
	sources = listType "VariableIR",
	returns = constantType "yes",
})

EXTEND_TYPE("IfSt", "AbstractStatementIR", recordType {
	tag = constantType "if",
	condition = "VariableIR",
	bodyThen = "StatementIR",
	bodyElse = "StatementIR",
})

EXTEND_TYPE("IntLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "int",
	number = "number",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NewClassSt", "AbstractStatementIR", recordType {
	tag = constantType "new-class",
	fields = mapType("string", "VariableIR"),
	type = "ConcreteType+",
	constraints = mapType("string", "ConstraintIR"),
	destination = "VariableIR",
	returns = constantType "no",
	memberDefinitions = mapType("string", "VariableIR"),
	location = "Location",
})

EXTEND_TYPE("NewUnionSt", "AbstractStatementIR", recordType {
	tag = constantType "new-union",
	type = "ConcreteType+",
	field = "string",
	value = "VariableIR",
	constraints = mapType("string", "ConstraintIR"),
	destination = "VariableIR",
	returns = constantType "no",
	variantDefinition = "VariableIR",
})

EXTEND_TYPE("StaticCallSt", "AbstractStatementIR", recordType {
	tag = constantType "static-call",
	constraints = mapType("string", "ConstraintIR"),
	baseType = "Type+",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	signature = "Signature",

	-- XXX: delete this
	staticName = "nil",
})

EXTEND_TYPE("MethodCallSt", "AbstractStatementIR", recordType {
	tag = constantType "method-call",
	baseInstance = "VariableIR",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	signature = "Signature",

	-- XXX: delete
	methodName = "nil",
})

EXTEND_TYPE("GenericMethodCallSt", "AbstractStatementIR", recordType {
	tag = constantType "generic-method-call",
	baseInstance = "VariableIR",
	constraint = "ConstraintIR",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	signature = "Signature",

	-- XXX: delete this
	methodName = "nil",
})

EXTEND_TYPE("GenericStaticCallSt", "AbstractStatementIR", recordType {
	tag = constantType "generic-static-call",
	constraint = "ConstraintIR",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	signature = "Signature",
	
	-- XXX: delete this
	staticName = "nil",
})

EXTEND_TYPE("BooleanLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "boolean",
	boolean = "boolean",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("FieldSt", "AbstractStatementIR", recordType {
	tag = constantType "field",
	name = "string",
	base = "VariableIR",
	destination = "VariableIR",
	returns = constantType "no",
	fieldDefinition = "VariableIR",
})

EXTEND_TYPE("ThisSt", "AbstractStatementIR", recordType {
	tag = constantType "this",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("UnitSt", "AbstractStatementIR", recordType {
	tag = constantType "unit",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("VariantSt", "AbstractStatementIR", recordType {
	tag = constantType "variant",
	destination = "VariableIR",
	base = "VariableIR",
	variant = "string",
	returns = constantType "no",
	variantDefinition = "VariableIR",
})

EXTEND_TYPE("MatchSt", "AbstractStatementIR", recordType {
	tag = constantType "match",
	base = "VariableIR",
	cases = listType(recordType {
		variant = "string",
		statement = "StatementIR",
	}),
})

EXTEND_TYPE("IsASt", "AbstractStatementIR", recordType {
	tag = constantType "isa",
	base = "VariableIR",
	destination = "VariableIR",
	returns = constantType "no",
	variant = "string",
})

EXTEND_TYPE("ForallSt", "AbstractStatementIR", recordType {
	tag = constantType "forall",
	destination = "VariableIR",
	quantified = "Type+",

	-- VariableIR => StatementIR, VariableIR
	instantiate = "function",
	location = "Location",
})

--------------------------------------------------------------------------------

REGISTER_TYPE("VariableIR", recordType {
	name = "string",
	type = "Type+",
	location = "Location",
	description = choiceType(constantType(false), "string"),
})

REGISTER_TYPE("ConstraintIR", choiceType(
	recordType {
		tag = constantType "this-constraint",
		instance = "VariableIR",
		interface = "InterfaceType+",
		name = "string",
	},
	recordType {
		tag = constantType "parameter-constraint",
		interface = "InterfaceType+",
		name = "string",
	},
	recordType {
		tag = constantType "concrete-constraint",
		interface = "InterfaceType+",
		concrete = "ConcreteType+",
		assignments = mapType("string", "ConstraintIR"),
	}
))

--------------------------------------------------------------------------------

REGISTER_TYPE("Type+", choiceType("ConcreteType+", "KeywordType+", "GenericType+", "SelfType+"))

REGISTER_TYPE("InterfaceType+", recordType {
	tag = constantType "interface-type",
	name = "string",
	arguments = listType "Type+",
	location = "Location",
})

REGISTER_TYPE("ConcreteType+", recordType {
	tag = constantType "concrete-type+",
	name = "string",
	arguments = listType "Type+",
	location = "Location",
})

REGISTER_TYPE("KeywordType+", recordType {
	tag = constantType "keyword-type+",
	name = "string",
	location = "Location",
})

REGISTER_TYPE("GenericType+", recordType {
	tag = constantType "generic+",

	-- e.g., "Foo" for `#Foo`
	name = "string",

	location = "Location",
})

REGISTER_TYPE("SelfType+", recordType {
	tag = constantType "self-type+",
	location = "Location",
})

-- Main ------------------------------------------------------------------------

-- RETURNS the string prefix in common to all members of list
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

class Array[#T] {
	foreign static make() Array[#T];
	foreign method get(index Int) #T;
	foreign method set(index Int, value #T) Array[#T];
	foreign method append(value #T) Array[#T];
	foreign method pop() Array[#T];
	foreign method size() Int;

	method swap(a Int, b Int) Array[#T] {
		return this.set(a, this.get(b)).set(b, this.get(a));
	}
}

class ASCII {
	foreign static formatInt(value Int) String;
}

class ArrayShower[#T | #T is Showable] {
	static inner(array Array[#T], index Int) String {
		if array.size() == index {
			return "";
		} elseif index == 0 {
			return array.get(0).show() ++ ArrayShower[#T].inner(array, 1);
		}
		return (", " ++ array.get(index).show()) ++ ArrayShower[#T].inner(array, index + 1);
	}

	static show(array Array[#T]) String {
		var inner String = ArrayShower[#T].inner(array, 0);
		return ("[" ++ inner) ++ "]";
	}
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
	method lessThan(other #Self) Boolean;
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

profile.open "parsing"

-- Load and parse source files
local sourceParses = {}
for _, sourceFile in ipairs(sourceFiles) do
	profile.open("parsing " .. sourceFile.path)
	profile.open("reading")
	local contents = sourceFile.contents
	if not contents then
		local file, err = io.open(sourceFile.path, "r")
		if not file then
			quit("The compiler could not open source file `", sourceFile.path, "`")
		end
		contents = file:read("*all")
		file:close()
		if not contents then
			quit("The compiler could not read from the source file `", sourceFile.path, "`")
		end
	end
	assert(contents)
	profile.close("reading")

	-- Lex contents
	profile.open("lexing")
	local tokens = lexSmol(contents, sourceFile.short)
	profile.close("lexing")

	-- Parse contents
	profile.open("parsing")
	table.insert(sourceParses, syntax.parseFile(tokens))
	profile.close("parsing")
	profile.close("parsing " .. sourceFile.path)
end

profile.close "parsing"

assert(#commandMap.main == 1)
local mainFunction = commandMap.main[1]

profile.open "semantics"
local semantics = calculateSemantics.semantics(sourceParses, mainFunction)
profile.close "semantics"

profile.open "verify"
verify(semantics)
profile.close "verify"

profile.open "codegen"
if semantics.main then
	-- TODO: read target
	local arguments = {out = "output.c"}
	local TARGET = "c"
	codegen[TARGET](semantics, arguments)
else
	print("Successfully compiled " .. #sourceFiles .. " file(s)")
end
profile.close "codegen"
