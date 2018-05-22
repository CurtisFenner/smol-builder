-- Curtis Fenner, copyright (C) 2017

local BUILTIN_NAME_MAP = {
	Int = true,
	String = true,
	Boolean = true,
	Unit = true,
	Never = true,
}

-- RETURNS a string
local function luaizeName(name)
	assert(not name:find "%.")
	return name:gsub(":", "_"):gsub("#", "hash")
end

-- RETURNS a string
local function staticFunctionName(longName)
	assert(longName, "string")
	assert(longName:find ":", "expected longName `" .. longName .. "` to have a `:`")
	return "smol_static_" .. luaizeName(longName)
end

-- RETURNS a string
local function methodFunctionName(longName)
	assertis(longName, "string")
	assert(longName:find ":")

	return "smol_method_" .. luaizeName(longName)
end

-- RETURNS a string
local function concreteConstraintFunctionName(definitionName, interfaceName)
	return "smol_concrete_constraint_" .. luaizeName(definitionName) .. "_for_" .. luaizeName(interfaceName)
end

-- RETURNS a string of smol representing the given type
local function showType(t)
	assertis(t, "Type+")

	if t.tag == "concrete-type+" then
		if #t.arguments == 0 then
			return t.name
		end
		local arguments = table.map(showType, t.arguments)
		return t.name .. "[" .. table.concat(arguments, ", ") .. "]"
	elseif t.tag == "keyword-type+" then
		return t.name
	elseif t.tag == "generic+" then
		return "#" .. t.name
	end
	error("unknown Type+ tag `" .. t.tag .. "`")
end

local C_THIS_LOCAL = "this"
local C_CONSTRAINT_PARAMETER_PREFIX = "cons"
local TAG_FIELD = "tag"

-- RETURNS a string representing a C identifier for a Smol variable or parameter
local function localName(name)
	assertis(name, "string")
	name = name:gsub(":", "_")

	return "smol_local_" .. name
end

-- RETURNS a string representing a C identifier for a Smol field
local function classFieldName(name)
	assert(not name:find(":"))

	return "smol_field_" .. name
end

-- RETURNS a string representing a C identifier for a Smol field
local function unionFieldName(name)
	assert(not name:find(":"))

	return "smol_case_" .. name
end

-- RETURNS a string representing a C type
local function cType(t, scope)
	assertis(t, "Type+")
	assertis(scope, mapType("string", "string"))

	if t.tag == "generic+" or t.tag == "self-type+" then
		return "void*"
	elseif t.tag == "concrete-type+" then
		return scope[t.name] .. "*"
	elseif t.tag == "keyword-type+" then
		return "smol_" .. t.name .. "*"
	end
	error "unknown"
end

-- RETURNS a string representing a tuple type
-- (even for 1 tuples, which may be inefficient, but is uniform)
local function cTypeTuple(ts, demandTuple, scope)
	assertis(ts, listType "Type+")
	assertis(demandTuple, "function")
	assert(#ts >= 1)
	assertis(scope, mapType("string", "string"))

	local shown = table.map(cType, ts, scope)
	return demandTuple(shown)
end

-- RETURNS a string
local function commented(message)
	return "// " .. message:gsub("\n", "\n// ")
end

-- RETURNS a string of C-code representing a literal to use as
-- the tag value for a union object
local function unionTagValue(union, variant)
	assertis(union, "UnionIR")
	assertis(variant, "string")

	for i, field in ipairs(union.fields) do
		if field.name == variant then
			return tostring(i)
		end
	end
	error("no variant")
end

-- RETURNS a string
local function cEncodedString(value)
	assertis(value, "string")

	local out = {}
	local safe = "[#_A-Za-z0-9 +-^*/:.,?!%%%[%]]"
	for i = 1, #value do
		if value:sub(i, i):match(safe) then
			table.insert(out, value:sub(i, i))
		else
			-- Convert to octal
			local digits = string.format("%o", value:byte(i))
			digits = string.rep("0", 3 - #digits) .. digits
			table.insert(out, "\\" .. digits)
		end
	end
	return "\"" .. table.concat(out) .. "\""
end

-- RETURNS a string
local function luaEncodedNumber(value)
	assertis(value, "number")

	return tostring(value)
end

local function indentedEmitter(emit)
	assertis(emit, "function")

	return function(line)
		return emit("\t" .. line)
	end
end

-- RETURNS a C type name
local function interfaceStructName(name)
	assertis(name, "string")
	assert(name:find(":"))

	return "smol_interface_" .. name:gsub(":", "_") .. "_T"
end

-- RETURNS a C type name
local function classStructName(name)
	assertis(name, "string")

	if BUILTIN_NAME_MAP[name] then
		return "smol_" .. name
	end
	assert(name:find(":"))

	return "smol_class_" .. name:gsub(":", "_") .. "_T"
end

-- RETURNS a C type name
local function unionStructName(name)
	assertis(name, "string")
	assert(name:find(":"))

	return "smol_union_" .. name:gsub(":", "_") .. "_T"
end

-- RETURNS a string representing a C type
local function cDefinitionType(definition)
	if definition.tag == "class" then
		return classStructName(definition.name) .. "*"
	elseif definition.tag == "union" then
		return unionStructName(definition.name) .. "*"
	elseif definition.tag == "builtin" then
		return "smol_" .. definition.name .. "*"
	end
	error("unknown definition tag `" .. definition.tag .. "`")
end

-- RETURNS a C struct field identifier
-- name must be a constraint "name", e.g., "2_3"
local function structConstraintField(name)
	assert(name:match("^#%d+_%d+$"))

	return "constraint_" .. name:sub(2)
end

-- RETURNS a string that is a Lua expression
local function cConstraint(constraint, semantics)
	assertis(constraint, "ConstraintIR")
	assertis(semantics, "Semantics")

	if constraint.tag == "parameter-constraint" then
		-- XXX
		return C_CONSTRAINT_PARAMETER_PREFIX .. "_" .. constraint.name:gsub("#", "")
	elseif constraint.tag == "concrete-constraint" then
		local func = concreteConstraintFunctionName(constraint.concrete.name, constraint.interface.name)
		local definition = table.findwith(semantics.compounds, "name", constraint.concrete.name)
		assertis(definition, recordType {generics = listType "TypeParameterIR"})

		local argumentValues = {}
		for i, generic in ipairs(definition.generics) do
			for j, c in ipairs(generic.constraints) do
				-- XXX
				local key = "#" .. i .. "_" .. j
				local assignment = constraint.assignments[key]
				table.insert(argumentValues, cConstraint(assignment, semantics))
			end
		end

		local arguments = table.concat(argumentValues, ", ")
		return func .. "(" .. arguments .. ")"
	elseif constraint.tag == "this-constraint" then
		return localName(constraint.instance.name) .. "->" .. structConstraintField(constraint.name)
	end
	error("unimplemented constraint tag `" .. constraint.tag .. "`")
end

-- RETURNS a string representing a interface struct field name
local function interfaceMember(name)
	return "i_" .. luaizeName(name)
end

-- REQUIRES that demandTuple has already been called; otherwise the referenced
-- tuple type doesn't exist
-- RETURNS a string that is a C type name
local function preTupleName(list)
	assert(list, listType "string")

	-- TODO: deal with 0-tuples
	local values = {}
	for _, element in ipairs(list) do
		table.insert(values, (element:gsub("%*", "_ptr")))
		assert(not element:find("%s"))
	end
	local name = "tuple" .. #list
	for i, value in ipairs(values) do
		name = name .. "_" .. i .. "_" .. value
	end

	return name
end

-- RETURNS a C function identifier
local function cWrapperName(signature, class, interface)
	return "wrapper_" .. luaizeName(class) .. "_" .. luaizeName(signature) .. "_is_" .. luaizeName(interface)
end

local counter = 0
local function UID()
	counter = counter + 1
	return counter
end

-- RETURNS nothing
-- Appends strings to code
local function generateStatement(statement, emit, structScope, semantics, demandTuple)
	assertis(statement, "StatementIR")
	assertis(structScope, mapType("string", "string"))
	assertis(demandTuple, "function")
	statement = freeze(statement)

	if statement.tag == "block" then
		for _, subStatement in ipairs(statement.statements) do
			generateStatement(subStatement, emit, structScope, semantics, demandTuple)
		end
		return
	end

	-- Emits a comment
	local function comment(message)
		emit("// " .. message)
	end

	-- Plain statements
	if statement.tag == "local" then
		comment("var " .. statement.variable.name .. " " .. showType(statement.variable.type) .. ";")
		emit(cType(statement.variable.type, structScope) .. " " .. localName(statement.variable.name) .. ";")
		return
	elseif statement.tag == "string" then
		comment(statement.destination.name .. " = " .. cEncodedString(statement.string) .. ";")
		local name = localName(statement.destination.name)
		emit(name .. " = ALLOCATE(smol_String);")
		emit(name .. "->length = " .. #statement.string .. ";")
		emit(name .. "->text = " .. cEncodedString(statement.string) .. ";")
		return
	elseif statement.tag == "int" then
		comment(statement.destination.name .. " = " .. statement.number .. ";")
		local name = localName(statement.destination.name)
		emit(name .. " = ALLOCATE(smol_Int);")
		emit(name .. "->value = " .. luaEncodedNumber(statement.number) .. ";")
		return
	elseif statement.tag == "boolean" then
		comment(statement.destination.name .. " = " .. tostring(statement.boolean) .. ";")
		local name = localName(statement.destination.name)
		emit(name .. " = ALLOCATE(smol_Boolean);")
		emit(name .. "->value = " .. (statement.boolean and 1 or 0) .. ";")
		return
	elseif statement.tag == "this" then
		comment(statement.destination.name .. " = this;")
		emit(localName(statement.destination.name) .. " = this;")
		return
	elseif statement.tag == "unit" then
		comment(statement.destination.name .. " = unit;")
		emit(localName(statement.destination.name) .. " = NULL;")
		return
	elseif statement.tag == "assign" then
		comment(statement.destination.name .. " = " .. statement.source.name .. ";")
		emit(localName(statement.destination.name) .. " = " .. localName(statement.source.name) .. ";")
		return
	elseif statement.tag == "new-class" then
		comment(statement.destination.name .. " = new(...);")

		-- Allocate a new instance
		local name = localName(statement.destination.name)
		local cT = cType(statement.destination.type, structScope)
		assert(cT:sub(-1) == "*")
		cT = cT:sub(1, -2)
		emit(name .. " = ALLOCATE(" .. cT .. ");")

		for key, value in spairs(statement.fields) do
			emit(name .. "->" .. classFieldName(key) .. " = " .. localName(value.name) .. ";")
		end
		for key, constraint in spairs(statement.constraints) do
			local constraintField = structConstraintField(key)
			emit(name .. "->" .. constraintField .. " = " .. cConstraint(constraint, semantics) .. ";")
		end
		return
	elseif statement.tag == "new-union" then
		comment(statement.destination.name .. " = new(" .. statement.field .. " = ...);")

		-- Allocate a new instance
		local destination = localName(statement.destination.name)
		local cT = cType(statement.destination.type, structScope)
		assert(cT:sub(-1) == "*")
		cT = cT:sub(1, -2)
		emit(destination .. " = ALLOCATE(" .. cT .. ");")

		local union = table.findwith(semantics.compounds, "name", statement.type.name)
		assert(union and union.tag == "union")

		-- Initialize the tag
		emit(destination .. "->" .. TAG_FIELD .. " = " .. unionTagValue(union, statement.field) .. ";")

		-- Initialize the value
		local value = localName(statement.value.name)
		emit(destination .. "->" .. unionFieldName(statement.field) .. " = " .. value .. ";")
		return
	elseif statement.tag == "return" then
		comment("return ...;")

		local types = {}
		for _, source in ipairs(statement.sources) do
			table.insert(types, cType(source.type, structScope))
		end
		local tuple = preTupleName(types)
		local values = table.map(function(v) return localName(v.name) end, statement.sources)
		emit("return " .. tuple .. "_make(" .. table.concat(values, ", ") .. ");")
		return
	elseif statement.tag == "if" then
		comment("if ... {")
		emit("if (" .. localName(statement.condition.name) .. "->value) {")
		generateStatement(statement.bodyThen, indentedEmitter(emit), structScope, semantics, demandTuple)
		emit("} else {")
		generateStatement(statement.bodyElse, indentedEmitter(emit), structScope, semantics, demandTuple)
		emit("}")
		return
	elseif statement.tag == "static-call" then
		comment("... = " .. statement.signature.longName .. "(...);")
		-- Collect value arguments
		local argumentNames = {}
		for _, argument in ipairs(statement.arguments) do
			table.insert(argumentNames, localName(argument.name))
		end

		-- Collect constraints
		-- XXX: right now, we're guaranteed these are in lexical order
		local keys = table.keys(statement.constraints)
		table.sort(keys)
		for _, key in ipairs(keys) do
			local constraint = statement.constraints[key]
			table.insert(argumentNames, cConstraint(constraint, semantics))
		end

		-- Emit code
		local invocation = staticFunctionName(statement.signature.longName)
		local arguments = table.concat(argumentNames, ", ")

		local definition = table.findwith(semantics.compounds, "name", statement.baseType.name)
		assert(definition)
		local signature = statement.signature

		local types = {}
		for _, r in ipairs(signature.returnTypes) do
			table.insert(types, cType(r, structScope))
		end
		local tuple = preTupleName(types)
		local tmp = "_tmp" .. UID()
		emit(tuple .. " " .. tmp .. " = " .. invocation .. "(" .. arguments .. ");")

		-- Assign each resulting tuple
		for i, destination in ipairs(statement.destinations) do
			local cast = "(" .. cType(destination.type, structScope) .. ")"
			emit(localName(destination.name) .. " = " .. cast .. tmp .. "._" .. i .. ";")
		end
		return
	elseif statement.tag == "method-call" then
		comment("... = " .. statement.signature.longName .. "(...);")

		-- Collect C arguments
		local argumentNames = {}

		-- Add the self argument
		table.insert(argumentNames, localName(statement.baseInstance.name))

		-- Add explicit value arguments
		for _, argument in ipairs(statement.arguments) do
			table.insert(argumentNames, localName(argument.name))
		end
		local arguments = table.concat(argumentNames, ", ")

		-- Get the signature
		local baseName = statement.baseInstance.type.name
		local compound = table.findwith(semantics.compounds, "name", baseName)
		local builtin = table.findwith(semantics.builtins, "name", baseName)
		local definition = compound or builtin
		assert(definition)
		local signature = statement.signature

		-- Get the C return-type of the function (which may not be the same
		-- as the definitions because of generics)
		local destinationTypes = {}
		for _, returnType in ipairs(signature.returnTypes) do
			table.insert(destinationTypes, cType(returnType, structScope))
		end

		local tmp = "tmp" .. UID()

		local tuple = preTupleName(destinationTypes)
		local invocation = methodFunctionName(signature.longName) .. "(" .. arguments .. ")"
		emit(tuple .. " " .. tmp .. " = " .. invocation .. ";")
		for i, destination in ipairs(statement.destinations) do
			emit(localName(destination.name) .. " = " .. tmp .. "._" .. i .. ";")
		end
		return
	elseif statement.tag == "field" then
		comment(statement.destination.name .. " = " .. statement.base.name .. "." .. statement.name .. ";")
		emit(localName(statement.destination.name) .. " = ")
		emit("\t" .. localName(statement.base.name) .. "->" .. classFieldName(statement.name) .. ";")
		return
	elseif statement.tag == "generic-static-call" then
		comment("... = " .. "... ." .. statement.signature.longName .. "(...);")

		-- Collect explicit arguments
		local argumentValues = {}
		for _, argument in ipairs(statement.arguments) do
			table.insert(argumentValues, localName(argument.name))
		end

		if #argumentValues < 1 then
			-- Closure calls must be given at least one argument
			table.insert(argumentValues, "NULL")
		end
		local arguments = table.concat(argumentValues, ", ")

		local interface = table.findwith(semantics.interfaces, "name", statement.constraint.interface.name)
		assert(interface)
		local signature = statement.signature

		local destinationTypes = {}
		for _, returnType in ipairs(signature.returnTypes) do
			table.insert(destinationTypes, cType(returnType, structScope))
		end
		local tuple = preTupleName(destinationTypes)

		local constraint = cConstraint(statement.constraint, semantics)
		local member = interfaceMember(statement.signature.memberName)
		local invocation = "CLOSURE_CALL(" .. constraint .. "->" .. member .. ", " .. arguments .. ")"
		local tmp = "tmp" .. UID()
		emit(tuple .. " " .. tmp .. " = " .. invocation .. ";")

		-- Assign from tmp
		for i, destination in ipairs(statement.destinations) do
			emit(localName(destination.name) .. " = " .. tmp .. "._" .. i .. ";")
		end
		return
	elseif statement.tag == "generic-method-call" then
		comment("... = " .. statement.signature.longName .. "(...);")
		local destinations = table.map(function(x) return localName(x.name) end, statement.destinations)

		-- Collect the arguments
		local argumentValues = {}

		-- The first argument is the implicit this
		table.insert(argumentValues, localName(statement.baseInstance.name))

		-- Add explicit arguments
		for _, argument in ipairs(statement.arguments) do
			table.insert(argumentValues, localName(argument.name))
		end

		local arguments = table.concat(argumentValues, ", ")

		local interface = table.findwith(semantics.interfaces, "name", statement.constraint.interface.name)
		assert(interface)
		local signature = statement.signature

		local tmp = "_tmp" .. UID()
		local outType = cTypeTuple(signature.returnTypes, demandTuple, structScope)
		emit(outType .. " " .. tmp .. " = CLOSURE_CALL(" .. cConstraint(statement.constraint, semantics) .. "->" .. interfaceMember(signature.memberName) .. ", " .. arguments .. ");")
		for i, destination in ipairs(statement.destinations) do
			emit(localName(destination.name) .. " = " .. tmp .. "._" .. i .. ";")
		end
		return
	elseif statement.tag == "match" then
		comment("match " .. statement.base.name .. " {")
		assert(#statement.cases >= 1)
		for i, case in ipairs(statement.cases) do
			if i > 1 then
				emit("else")
			end
			local id = tostring(i)
			comment("case ? " .. case.variant)
			emit("if (" .. localName(statement.base.name) .. "->" .. TAG_FIELD .. " == " .. id .. ") {")
			generateStatement(case.statement, indentedEmitter(emit), structScope, semantics, demandTuple)
			emit("}")
		end
		emit("else { assert(0); }")
		comment("}")
		return
	elseif statement.tag == "variant" then
		comment(statement.destination.name .. " = " .. statement.base.name .. "." .. statement.variant .. "; (union)")
		emit(localName(statement.destination.name) .. " = ")
		emit("\t" .. localName(statement.base.name) .. "->" .. unionFieldName(statement.variant) .. ";")
		return
	elseif statement.tag == "assume" then
		error "assume statements should be guarded by proof"
	elseif statement.tag == "verify" then
		error "verify statements should be guarded by proof"
	elseif statement.tag == "proof" then
		comment("proof")
		return
	elseif statement.tag == "isa" then
		comment(statement.destination.name .. " = " .. statement.base.name .. " isa " .. statement.variant)
		emit(localName(statement.destination.name) .. " = ALLOCATE(smol_Boolean);")
		local union = table.findwith(semantics.compounds, "name", statement.base.type.name)
		assert(union and union.tag == "union")

		-- Set value
		local tagValue = unionTagValue(union, statement.variant)
		local rhs = localName(statement.base.name) .. "->tag == " .. tagValue
		emit(localName(statement.destination.name) .. "->value = " .. rhs .. ";")
		return
	end

	comment(statement.tag .. " ????")
	print("unknown statement tag `" .. statement.tag .. "`")
end

-- RETURNS a C function identifier
local function cEqMethodName(kind, name)
	assert(kind == "class" or kind == "union")
	assertis(name, "string")

	return "smol_eq_" .. kind .. "_" .. name:gsub(":", "_")
end

return function(semantics, arguments)
	if not arguments.out then
		quit("out argument must be specified for C code generator")
	end

	-- Open the file
	local file = io.open(arguments.out, "wb")
	if not file then
		quit("Could not open file `" .. arguments.out .. "` for writing")
	end

	local code = {"// Generated by Smol Lua compiler", commented(INVOKATION), ""}
	table.insert(code, [[
#include "assert.h"
#include "stdint.h"
#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "inttypes.h"

#define ALLOCATE(T) ((T*)malloc(sizeof(T)))
#define ALLOCATE_ARRAY(size, T) ((T*)malloc(size * sizeof(T)))

#define PANIC(message) do { printf(message "\n"); exit(1); } while (0)

// NOTE: closures must take at least one argument
#define CLOSURE(returnType, ...)                \
	struct {                                    \
		void* data;                             \
		returnType (*func)(void*, __VA_ARGS__); \
	}

#define CLOSURE_CALL(closure, ...) (closure.func(closure.data, __VA_ARGS__))

typedef struct {
	void* instance;
	int (*eq)(void*, void*);
	void (*destruct)(void*);
} object_t;

]])

	local forwardSequence = {}
	table.insert(code, "// Forward type declarations")
	table.insert(code, forwardSequence)
	table.insert(code, "")
	local function forwardDeclareStruct(private, public)
		assertis(private, "string")
		assert(not private:find(";"))
		assertis(public, "string")

		table.insert(forwardSequence, "struct " .. private .. "; typedef struct " .. private .. " " .. public .. ";")
	end

	table.insert(code, "// Tuples")
	local tupleSequence = {}
	table.insert(code, tupleSequence)
	table.insert(code, "")

	-- RETURNS a string that is a C type
	local generatedTuples = {}
	local function demandTuple(list)
		assert(list, listType "string")

		-- TODO: deal with 0-tuples
		local name = preTupleName(list)
		if not generatedTuples[name] then
			generatedTuples[name] = true
			local sequence = {}
			-- Open struct impl
			table.insert(sequence, "struct _" .. name .. " {")
			local parameters = {}
			for i = 1, #list do
				table.insert(parameters, list[i] .. " _" .. i)
				table.insert(sequence, "\t" .. list[i] .. " _" .. i .. ";")
			end
			if #list == 0 then
				table.insert(sequence, "\tchar _;")
			end

			-- Close struct
			table.insert(sequence, "};")
			table.insert(sequence, "")

			table.insert(sequence, name .. " " .. name .. "_make(" .. table.concat(parameters, ", ") .. ") {")
			table.insert(sequence, "\t" .. name .. " out;")
			for i = 1, #list do
				table.insert(sequence, "\tout._" .. i .. " = _" .. i .. ";")
			end
			table.insert(sequence, "\treturn out;")
			table.insert(sequence, "}")
			table.insert(sequence, "")
			table.insert(tupleSequence, table.concat(sequence, "\n"))
			forwardDeclareStruct("_" .. name, name)
		end
		return name
	end

	table.insert(code, [[
struct _smol_Unit {
	void* nothing;
};

struct _smol_Boolean {
	int value;
};

struct _smol_String {
	size_t length;
	char* text;
};

struct _smol_Int {
	int64_t value;
};

////////////////////////////////////////////////////////////////////////////////
]])

	forwardDeclareStruct("_smol_Unit", "smol_Unit")
	forwardDeclareStruct("_smol_Boolean", "smol_Boolean")
	forwardDeclareStruct("_smol_Int", "smol_Int")
	forwardDeclareStruct("_smol_String", "smol_String")

	-- Build the struct scope map
	local structScope = {}
	for _, compound in ipairs(semantics.compounds) do
		assert(compound.tag == "class" or compound.tag == "union")
		if compound.tag == "class" then
			structScope[compound.name] = classStructName(compound.name)
		elseif compound.tag == "union" then
			structScope[compound.name] = unionStructName(compound.name)
		end
	end
	structScope = freeze(structScope)

	-- Generate a struct for each interface
	for _, interface in ipairs(semantics.interfaces) do
		table.insert(code, "// interface " .. interface.name)
		local structName = interfaceStructName(interface.name)
		table.insert(code, "struct _" .. structName .. " {")
		for _, signature in ipairs(interface.signatures) do
			local returns = cTypeTuple(signature.returnTypes, demandTuple, structScope)
			local name = interfaceMember(signature.memberName)
			local parameters = {}
			if signature.modifier == "method" then
				table.insert(parameters, "void* /*this*/")
			end
			for _, parameter in ipairs(signature.parameters) do
				table.insert(parameters, cType(parameter.type, structScope))
			end

			local prototype = #parameters == 0 and "void* /*ignore*/ " or table.concat(parameters, ", ")
			table.insert(code, "\tCLOSURE(" .. returns .. ", " .. prototype .. ") " .. name .. ";")
		end
		table.insert(code, "\tchar _;")
		table.insert(code, "};")
		forwardDeclareStruct("_" .. structName, structName)
		table.insert(code, "")
	end

	-- Generate a struct for each class
	for _, class in ipairs(semantics.compounds) do
		if class.tag == "class" then
			table.insert(code, "// class " .. class.name)
			local structName = classStructName(class.name)
			table.insert(code, "struct _" .. structName .. " {")

			-- Add a foreign field
			table.insert(code, "\tvoid* foreign;")

			-- Generate all value fields
			for _, field in ipairs(class.fields) do
				table.insert(code, "\t" .. cType(field.type, structScope) .. " " .. classFieldName(field.name) .. ";")
			end

			-- Generate all constraint fields
			for i, generic in ipairs(class.generics) do
				for j, constraint in ipairs(generic.constraints) do
					local t = interfaceStructName(constraint.interface.name) .. "*"
					-- XXX: constraint key
					local key = "#" .. i .. "_" .. j
					table.insert(code, "\t" .. t .. " " .. structConstraintField(key) .. ";")
				end
			end

			table.insert(code, "};")
			forwardDeclareStruct("_" .. structName, structName)
			table.insert(code, "")
		end
	end

	-- Generate a tagged union for each union
	for _, union in ipairs(semantics.compounds) do
		if union.tag == "union" then
			-- Open struct definition
			table.insert(code, "// union " .. union.name)
			local structName = unionStructName(union.name)

			-- TODO: Generate a union rather than a struct
			table.insert(code, "struct _" .. structName .. "{")

			-- Generate tag
			assert(#union.fields < 64)
			table.insert(code, "\tunsigned " .. TAG_FIELD .. ";")

			-- Generate all value fields
			for _, field in ipairs(union.fields) do
				table.insert(code, "\t" .. cType(field.type, structScope) .. " " .. unionFieldName(field.name) .. ";")
			end

			-- Generate all constraint fields
			for i, generic in ipairs(union.generics) do
				for j, constraint in ipairs(generic.constraints) do
					local t = interfaceStructName(constraint.interface.name) .. "*"
					-- XXX: constraint key
					local key = "#" .. i .. "_" .. j
					table.insert(code, "\t" .. t .. " " .. structConstraintField(key) .. ";")
				end
			end

			-- Close struct definition
			table.insert(code, "};")
			forwardDeclareStruct("_" .. structName, structName)
			table.insert(code, "")
		end
	end

	local prototypeSequence = {}
	table.insert(code, prototypeSequence)
	table.insert(code, "")
	-- Add a prototype string to up here
	local function genPrototype(prototype)
		assert(prototype:find(" ") and prototype:find(";"))
		table.insert(prototypeSequence, prototype)
	end

	-- Generate a constraint-building-function for each constraint
	for _, definition in ipairs(semantics.compounds) do
		for i, implement in ipairs(definition.implements) do
			local requirements = {}
			for key, constraint in spairs(definition.constraints) do
				table.insert(requirements, {name = key, constraint = constraint})
			end
			table.sort(requirements, function(a, b) return a.name < b.name end)
			local parameters = {}
			local parameterTypes = {}
			for j, p in ipairs(requirements) do
				local t = interfaceStructName(p.constraint.name) .. "*"
				table.insert(parameters, t .. " p" .. i .. "_" .. j)
				table.insert(parameterTypes, t)
			end

			local interface = table.findwith(semantics.interfaces, "name", implement.name)
			assert(interface)

			-- Generate the wrapper for each method part of the interface
			local wrapped = {}
			for _, signature in ipairs(interface.signatures) do
				table.insert(code, "// wrapper for impl")

				local implementingSignature = table.findwith(definition.signatures, "memberName", signature.memberName)

				-- Collect the constraints
				local constraints = {}
				for i, generic in ipairs(definition.generics) do
					for j, constraint in ipairs(generic.constraints) do
						table.insert(constraints, interfaceStructName(constraint.interface.name) .. "*")
					end
				end

				local dataTupleType = demandTuple(constraints) .. "*"

				-- Get the out type from the interface
				local wrapperName = cWrapperName(signature.memberName, definition.name, interface.name)
				wrapped[signature.memberName] = wrapperName
				local outType = cTypeTuple(signature.returnTypes, demandTuple, structScope)
				local cParameters = {"void* data_general"}

				-- Add implicit this parameter
				if signature.modifier == "method" then
					table.insert(cParameters, "void* " .. C_THIS_LOCAL)
				end

				-- Add explicit value parameters
				for _, parameter in ipairs(signature.parameters) do
					local t = cType(parameter.type, structScope)
					local name = localName(parameter.name)
					table.insert(cParameters, t .. " " .. name)
				end
				if #cParameters == 1 then
					table.insert(cParameters, "void* /*ignore*/ _")
				end

				-- Create prototype for wrapper
				local prototype = outType .. " " .. wrapperName .. "(" .. table.concat(cParameters, ", ") .. ")"
				table.insert(code, prototype .. " {")
				table.insert(code, "\t" .. dataTupleType .. " data = data_general;")

				-- Collect the value arguments for the implementation
				local arguments = {}
				if signature.modifier == "method" then
					-- TODO: explicitly cast to correct type
					local cast = "(void*)"
					table.insert(arguments, cast .. C_THIS_LOCAL)
				end

				for _, parameter in ipairs(signature.parameters) do
					table.insert(arguments, localName(parameter.name))
				end

				-- Collect the constraint arguments for the implementation
				if signature.modifier == "static" then
					-- Only static functions take parameters
					for i, constraint in ipairs(constraints) do
						table.insert(arguments, "data->_" .. i)
					end
				end

				local implName
				if signature.modifier == "static" then
					implName = staticFunctionName(implementingSignature.longName)
				else
					implName = methodFunctionName(implementingSignature.longName)
				end

				local invocation = implName .. "(" .. table.concat(arguments, ", ") .. ")"

				-- May need to convert tuple types
				local func = table.findwith(definition.signatures, "memberName", signature.memberName)
				local defOut = cTypeTuple(func.returnTypes, demandTuple, structScope)
				local intOut = cTypeTuple(signature.returnTypes, demandTuple, structScope)
				table.insert(code, "\t" .. defOut .. " concrete_out = " .. invocation .. ";")
				table.insert(code, "\t" .. intOut .. " out;")
				for i = 1, #signature.returnTypes do
					table.insert(code, "\tout._" .. i .. " = concrete_out._" .. i .. ";")
				end
				table.insert(code, "\treturn out;")
				table.insert(code, "}")
			end

			-- Generate the main function
			local functionName = concreteConstraintFunctionName(definition.name, implement.name)
			local outValueType = interfaceStructName(implement.name)
			table.insert(code, "// " .. definition.name .. " implements " .. implement.name)
			table.insert(code, outValueType .. "* " .. functionName .. "(" .. table.concat(parameters, ", ") .. ") {")
			local tuple = demandTuple(parameterTypes)
			table.insert(code, "\t" .. tuple .. "* closed = ALLOCATE(" .. tuple .. ");")
			for j = 1, #parameters do
				table.insert(code, "\tclosed->_" .. i .. " = p" .. i .. "_" .. j .. ";")
			end

			table.insert(code, "\t" .. outValueType .. "* out = ALLOCATE(" .. outValueType .. ");")
			for _, signature in ipairs(interface.signatures) do
				table.insert(code, "\tout->" .. interfaceMember(signature.memberName) .. ".data = closed;")
				local func = wrapped[signature.memberName]
				table.insert(code, "\tout->" .. interfaceMember(signature.memberName) .. ".func = " .. func .. ";")
			end

			table.insert(code, "\treturn out;")
			table.insert(code, "}")
			table.insert(code, "")
		end
	end

	-- Add separator before functions
	table.insert(code, string.rep("/", 80))
	table.insert(code, "")

	-- Generate the tuple types/prototypes for builtins
	local builtinFuncs = {}
	for _, builtin in ipairs(semantics.builtins) do
		for _, signature in ipairs(builtin.signatures) do
			-- Generate function header
			local cFunctionName
			local cParameters
			if signature.modifier == "static" then
				cFunctionName = staticFunctionName(signature.longName)
				cParameters = {}
			else
				assert(signature.modifier == "method")
				cFunctionName = methodFunctionName(signature.longName)
				cParameters = {"smol_" .. builtin.name .. "* " .. C_THIS_LOCAL}
			end

			-- Add value parameters
			for _, parameter in ipairs(signature.parameters) do
				table.insert(cParameters, cType(parameter.type, structScope) .. " " .. localName(parameter.name))
			end

			local outType = cTypeTuple(signature.returnTypes, demandTuple, structScope)
			local prototype = outType .. " " .. cFunctionName .. "(" .. table.concat(cParameters, ", ") .. ")"
			genPrototype(prototype .. ";")
		end
	end

	-- Generate the body for each method and static
	for _, func in ipairs(semantics.functions) do
		local fullName = func.definitionName .. "." .. func.name
		table.insert(code, "// " .. func.signature.modifier .. " " .. fullName)

		local definition = table.findwith(semantics.compounds, "name", func.definitionName)
		assert(definition)
		local thisType = cDefinitionType(definition)

		-- Generate function header
		local cFunctionName
		local cParameters
		if func.signature.modifier == "static" then
			cFunctionName = staticFunctionName(func.signature.longName)
			cParameters = {}
		else
			assert(func.signature.modifier == "method")
			cFunctionName = methodFunctionName(func.signature.longName)
			cParameters = {thisType .. " " .. C_THIS_LOCAL}
		end

		-- Add value parameters
		for _, parameter in ipairs(func.parameters) do
			table.insert(cParameters, cType(parameter.type, structScope) .. " " .. localName(parameter.name))
		end

		-- Add constraint parameters
		for i, generic in ipairs(func.generics) do
			for j, constraint in ipairs(generic.constraints) do
				local interface = constraint.interface
				assertis(interface, "InterfaceType+")

				local t = interfaceStructName(interface.name) .. "*"
				local identifier = C_CONSTRAINT_PARAMETER_PREFIX .. "_" .. i .. "_" .. j
				table.insert(cParameters, t .. " " .. identifier)
			end
		end
		local outType = cTypeTuple(func.returnTypes, demandTuple, structScope)
		local prototype = outType .. " " .. cFunctionName .. "(" .. table.concat(cParameters, ", ") .. ")"
		genPrototype(prototype .. ";")

		-- Generate function body
		if not func.signature.foreign then
			table.insert(code, prototype .. " {")
			local function emit(line)
				table.insert(code, "\t" .. line)
			end
			generateStatement(func.body, emit, structScope, semantics, demandTuple)

			-- Close function body
			if func.body.returns ~= "yes" then
				assert(#func.returnTypes == 1)
				assert(func.returnTypes[1].tag == "keyword-type+")
				assert(func.returnTypes[1].name == "Unit")

				table.insert(code, "\treturn (tuple1_1_smol_Unit_ptr){NULL};")
			end
			table.insert(code, "}")
		else
			table.insert(code, "// is foreign")
		end
		table.insert(code, "")
	end

	table.insert(code, [[
////////////////////////////////////////////////////////////////////////////////

// Boolean method and(Boolean) Boolean
tuple1_1_smol_Boolean_ptr smol_method_Boolean_and(smol_Boolean* this, smol_Boolean* other) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = this->value && other->value;
	return out;
}

// Boolean method or(Boolean) Boolean
tuple1_1_smol_Boolean_ptr smol_method_Boolean_or(smol_Boolean* this, smol_Boolean* other) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = this->value || other->value;
	return out;
}

// Boolean method not() Boolean
tuple1_1_smol_Boolean_ptr smol_method_Boolean_not(smol_Boolean* this) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = !this->value;
	return out;
}

// Boolean method implies(Boolean) Boolean
tuple1_1_smol_Boolean_ptr smol_method_Boolean_implies(smol_Boolean* this, smol_Boolean* other) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = !this->value || other->value;
	return out;
}

// Boolean method eq(Boolean) Boolean
tuple1_1_smol_Boolean_ptr smol_method_Boolean_eq(smol_Boolean* this, smol_Boolean* other) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = this->value == other->value;
	return out;
}

// Int method isPositive() Boolean
tuple1_1_smol_Boolean_ptr smol_method_Int_isPositive(smol_Int* this) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = this->value > 0;
	return out;
}

// Int method negate() Int
tuple1_1_smol_Int_ptr smol_method_Int_negate(smol_Int* this) {
	tuple1_1_smol_Int_ptr out;
	out._1 = ALLOCATE(smol_Int);
	out._1->value = -this->value;
	return out;
}

// Int method lessThan(Int) Boolean
tuple1_1_smol_Boolean_ptr smol_method_Int_lessThan(smol_Int* this, smol_Int* smol_local_one) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = this->value < smol_local_one->value;
	return out;
}

// Int method eq(Int) Boolean
tuple1_1_smol_Boolean_ptr smol_method_Int_eq(smol_Int* this, smol_Int* smol_local_other) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	out._1->value = this->value == smol_local_other->value;
	return out;
}

// Int method quotient(Int) Int
tuple1_1_smol_Int_ptr smol_method_Int_quotient(smol_Int* this, smol_Int* smol_local_other) {
	tuple1_1_smol_Int_ptr out;
	out._1 = ALLOCATE(smol_Int);
	out._1->value = this->value / smol_local_other->value;
	return out;
}

// Int method product(Int) Int
tuple1_1_smol_Int_ptr smol_method_Int_product(smol_Int* this, smol_Int* smol_local_other) {
	tuple1_1_smol_Int_ptr out;
	out._1 = ALLOCATE(smol_Int);
	out._1->value = this->value * smol_local_other->value;
	return out;
}

// Int method sum(Int) Int
tuple1_1_smol_Int_ptr smol_method_Int_sum(smol_Int* this, smol_Int* smol_local_other) {
	tuple1_1_smol_Int_ptr out;
	out._1 = ALLOCATE(smol_Int);
	out._1->value = this->value + smol_local_other->value;
	return out;
}

// Int method difference(Int) Int
tuple1_1_smol_Int_ptr smol_method_Int_difference(smol_Int* this, smol_Int* smol_local_other) {
	tuple1_1_smol_Int_ptr out;
	out._1 = ALLOCATE(smol_Int);
	out._1->value = this->value - smol_local_other->value;
	return out;
}

// String method concatenate(String) String
tuple1_1_smol_String_ptr smol_method_String_concatenate(smol_String* this, smol_String* other) {
	tuple1_1_smol_String_ptr out;
	out._1 = ALLOCATE(smol_String);
	out._1->length = this->length + other->length;
	out._1->text = ALLOCATE_ARRAY(out._1->length, char);
	for (size_t i = 0; i < this->length; i++) {
		out._1->text[i] = this->text[i];
	}
	for (size_t i = 0; i < other->length; i++) {
		out._1->text[i + this->length] = other->text[i];
	}
	return out;
}

// String method eq(String) Boolean
tuple1_1_smol_Boolean_ptr smol_method_String_eq(smol_String* this, smol_String* other) {
	tuple1_1_smol_Boolean_ptr out;
	out._1 = ALLOCATE(smol_Boolean);
	size_t length = this->length;
	if (length != other->length) {
		out._1->value = 0;
	} else {
		out._1->value = 0 == memcmp(this->text, other->text, length);
	}
	return out;
}

////////////////////////////////////////////////////////////////////////////////

// core:Out static println(String) Unit
tuple1_1_smol_Unit_ptr smol_static_core_Out_println(smol_String* message) {
	// TODO: allow nulls, etc.
	for (size_t i = 0; i < message->length; i++) {
		putchar(message->text[i]);
	}
	printf("\n");
	return (tuple1_1_smol_Unit_ptr){0};
}

// <Arrays>
typedef struct {
	size_t size;
	void** data;
} realarray;

// core:Array[#T] static make() Array[#T]
tuple1_1_smol_class_core_Array_T_ptr smol_static_core_Array_make() {
	realarray* real = ALLOCATE(realarray);
	real->size = 0;
	real->data = NULL;

	smol_class_core_Array_T* out = ALLOCATE(smol_class_core_Array_T);
	out->foreign = real;
	return (tuple1_1_smol_class_core_Array_T_ptr){out};
}

// core:Array[#T] method get(Int) #T
tuple1_1_void_ptr smol_method_core_Array_get(smol_class_core_Array_T* this, smol_Int* smol_local_index) {
	realarray* real = this->foreign;
	if (smol_local_index->value < 0) {
		PANIC("negative array index");
	} else if (smol_local_index->value >= (int)real->size) {
		PANIC("past end array index");
	}
	void* out = real->data[smol_local_index->value];
	return (tuple1_1_void_ptr){out};
}

// core:Array[#T] method set(Int, #T) Array[#T]
tuple1_1_smol_class_core_Array_T_ptr smol_method_core_Array_set(smol_class_core_Array_T* this, smol_Int* smol_local_index, void* smol_local_value) {
	realarray* old = this->foreign;
	if (smol_local_index->value < 0) {
		PANIC("negative array index");
	} else if (smol_local_index->value >= (int)old->size) {
		PANIC("past end array index");
	}

	realarray* prime = ALLOCATE(realarray);
	prime->size = old->size;
	prime->data = ALLOCATE_ARRAY(prime->size, void*);
	for (size_t i = 0; i < old->size; i++) {
		prime->data[i] = old->data[i];
	}

	// Update the value
	prime->data[smol_local_index->value] = smol_local_value;

	smol_class_core_Array_T* out = ALLOCATE(smol_class_core_Array_T);
	out->foreign = prime;

	return (tuple1_1_smol_class_core_Array_T_ptr){out};
}

// core:Array method append(#T) Array[#T]
tuple1_1_smol_class_core_Array_T_ptr smol_method_core_Array_append(smol_class_core_Array_T* this, void* smol_local_value) {
	realarray* old = this->foreign;
	realarray* prime = ALLOCATE(realarray);
	prime->size = old->size + 1;
	prime->data = ALLOCATE_ARRAY(prime->size, void*);
	for (size_t i = 0; i < old->size; i++) {
		prime->data[i] = old->data[i];
	}

	// Update the value
	prime->data[old->size] = smol_local_value;

	smol_class_core_Array_T* out = ALLOCATE(smol_class_core_Array_T);
	out->foreign = prime;

	return (tuple1_1_smol_class_core_Array_T_ptr){out};
}

// core:Array method pop() Array[#T]
tuple1_1_smol_class_core_Array_T_ptr smol_method_core_Array_pop(smol_class_core_Array_T* this) {
	realarray* old = this->foreign;
	realarray* prime = ALLOCATE(realarray);
	prime->size = old->size - 1;
	prime->data = ALLOCATE_ARRAY(prime->size, void*);
	for (size_t i = 0; i < old->size - 1; i++) {
		prime->data[i] = old->data[i];
	}

	smol_class_core_Array_T* out = ALLOCATE(smol_class_core_Array_T);
	out->foreign = prime;

	return (tuple1_1_smol_class_core_Array_T_ptr){out};
}

// core:Array method size() Int
tuple1_1_smol_Int_ptr smol_method_core_Array_size(smol_class_core_Array_T* this) {
	realarray* real = this->foreign;
	smol_Int* out = ALLOCATE(smol_Int);
	out->value = (int64_t)real->size;
	return (tuple1_1_smol_Int_ptr){out};
}

// core:ASCII static formatInt(Int) String
tuple1_1_smol_String_ptr smol_static_core_ASCII_formatInt(smol_Int* smol_local_value) {
	tuple1_1_smol_String_ptr out;
	out._1 = ALLOCATE(smol_String);
	out._1->text = ALLOCATE_ARRAY(32, char);
	out._1->length = (size_t)sprintf(out._1->text, "%" PRId64, smol_local_value->value);
	return out;
}

////////////////////////////////////////////////////////////////////////////////
]])

	demandTuple {"smol_String*"}
	demandTuple {"smol_class_core_Array_T*"}

	-- Generate the main function
	table.insert(code, "// Main " .. semantics.main)
	table.insert(code, "int main(int argv, char** argc) {")
	table.insert(code, "\t" .. staticFunctionName(semantics.main .. ":main") .. "();")
	table.insert(code, "\treturn 0;")
	table.insert(code, "}")

	-- Write the code to the output file
	for _, line in ipairs(code) do
		if type(line) == "string" then
			file:write(line .. "\n")
		else
			assertis(line, listType "string")
			for _, subline in ipairs(line) do
				file:write(subline .. "\n")
			end
		end
	end
	file:close()
end
