-- Curtis Fenner, copyright (C) 2017

-- RETURNS a string
local function luaizeName(name)
	return name:gsub(":", "_"):gsub("#", "hash")
end

-- RETURNS a string
local function staticFunctionName(name, definition)
	assert(definition:find("[A-Z]"))
	return "smol_static_" .. luaizeName(definition) .. "_" .. luaizeName(name)
end

-- RETURNS a string
local function methodFunctionName(name, definition)
	assertis(name, "string")
	assertis(definition, "string")
	assert(definition:match(":"))
	assert(definition:find("[A-Z]"))

	return "smol_method_" .. luaizeName(definition) .. "_" .. luaizeName(name)
end

-- RETURNS a string
local function concreteConstraintFunctionName(definitionName, interfaceName)
	return "smol_concrete_constraint_" .. luaizeName(definitionName) .. "_is_" .. luaizeName(interfaceName)
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

local LUA_THIS_LOCAL = "this"
local C_CONSTRAINT_PARAMETER_PREFIX = "cons"
local LUA_CONSTRAINTS_FIELD = "constraintField"

-- RETURNS a string representing a Lua identifier for a Smol variable or parameter
local function localName(name)
	assert(not name:find(":"))

	return "smol_local_" .. name
end

-- RETURNS a string representing a Lua identifier for a Smol field
local function classFieldName(name)
	assert(not name:find(":"))

	return "smol_field_" .. name
end

-- RETURNS a string representing a C type
local function cType(t, scope)
	assertis(t, "Type+")
	assertis(scope, mapType("string", "string"))

	if t.tag == "generic+" then
		return "void*"
	elseif t.tag == "concrete-type+" then
		return scope[t.name] .. "*"
	elseif t.tag == "keyword-type+" then
		return "smol_" .. t.name .. "*"
	end
	error "unknown"
end

-- RETURNS a string representing a tuple type
local function cTypeTuple(ts, demandTuple, scope)
	assertis(ts, listType "Type+")
	assertis(demandTuple, "function")
	assert(#ts >= 1)
	assertis(scope, mapType("string", "string"))
	if #ts == 1 then
		return cType(ts[1], scope)
	end
	local shown = table.map(cType, ts, scope)
	return demandTuple(shown)
end

-- RETURNS a string
local function commented(message)
	return "// " .. message:gsub("\n", "\n// ")
end

-- RETURNS a string
local function luaEncodedString(value)
	assertis(value, "string")

	local out = {}
	local safe = "[#_A-Za-z0-9 +-^*/:.,?!%%%[%]]"
	for i = 1, #value do
		if value:sub(i, i):match(safe) then
			table.insert(out, value:sub(i, i))
		else
			local digits = tostring(value:byte(i))
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
	assert(name:find(":"))

	return "smol_class_" .. name:gsub(":", "_") .. "_T"
end

-- RETURNS a string that is a Lua identifier
local function variableToLuaLocal(variable)
	assertis(variable, "VariableIR")

	return localName(variable.name)
end

-- RETURNS a string
local function variablesToLuaList(variables)
	assertis(variables, listType "VariableIR")

	local identifiers = table.map(variableToLuaLocal, variables)
	return table.concat(identifiers, ", ")
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
		local class = table.findwith(semantics.classes, "name", constraint.concrete.name)
		local union = table.findwith(semantics.unions, "name"< constraint.concrete.name)
		local definition = class or union
		assertis(definition, recordType {generics = listType "TypeParameterIR"})

		local argumentValues = {}
		for i, generic in ipairs(definition.generics) do
			for j, c in ipairs(generic.constraints) do
				-- XXX
				local assignment = constraint.assignments["#" .. i .. "_" .. j]
				table.insert(argumentValues, cConstraint(assignment, semantics))
			end
		end

		local arguments = table.concat(argumentValues, ", ")
		return func .. "(" .. arguments .. ")"
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
	end
	local name = "tuple" .. #list
	for i, value in ipairs(values) do
		name = name .. "_" .. i .. "_" .. value
	end
	return name
end

-- RETURNS a C function identifier
local function cWrapperName(signature, class, interface)
	return "wrapper_" .. luaizeName(signature) .. "_" .. signature .. "_is_" .. luaizeName(interface)
end

local counter = 0
local function UID()
	counter = counter + 1
	return counter
end

-- RETURNS nothing
-- Appends strings to code
local function generateStatement(statement, emit, structScope, semantics)
	assertis(statement, "StatementIR")
	assertis(structScope, mapType("string", "string"))

	if statement.tag == "block" then
		for _, subStatement in ipairs(statement.statements) do
			generateStatement(subStatement, emit, structScope, semantics)
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
		comment(statement.destination.name .. " = " .. luaEncodedString(statement.string) .. ";")
		local name = localName(statement.destination.name)
		emit(name .. " = ALLOCATE(smol_String);")
		emit(name .. "->length = " .. #statement.string .. ";")
		emit(name .. "->text = " .. luaEncodedString(statement.string) .. ";")
		return
	elseif statement.tag == "number" then
		comment(statement.destination.name .. " = " .. statement.number .. ";")
		local name = localName(statement.destination.name)
		emit(name .. " = ALLOCATE(smol_Number);")
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
	elseif statement.tag == "static-call" then
		comment("... = " .. showType(statement.baseType) .. "." .. statement.name .. "(...);")
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
		local destination = statement.destinations[1]
		local invocation = staticFunctionName(statement.name, statement.baseType.name)
		local arguments = table.concat(argumentNames, ", ")
		if #statement.destinations == 1 then
			emit(localName(destination.name) .. " = " .. invocation .. "(" .. arguments .. ");")
			return
		else
			assert(#statement.destinations >= 2)
			local destinationTypes = {}
			for _, destination in ipairs(statement.destinations) do
				table.insert(destinationTypes, cType(destination.type, structScope))
			end
			local class = table.findwith(semantics.classes, "name", statement.baseType.name)
			local union = table.findwith(semantics.unions, "name", statement.baseType.name)
			local definition = class or union
			assert(definition)
			local signature = table.findwith(definition.signatures, "name", statement.name)
			assert(signature)

			local types = {}
			for _, r in ipairs(signature.returnTypes) do
				table.insert(types, cType(r, structScope))
			end
			local tuple = preTupleName(types)
			local tmp = "_tmp" .. UID()
			emit(tuple .. " " .. tmp .. " = " .. invocation .. "(" .. arguments .. ");")

			-- Assign each resulting tuple
			for i, destination in ipairs(statement.destinations) do
				-- TODO: add explicit casts
				emit(localName(destination.name) .. " = " .. tmp .. "._" .. i .. ";")
			end
			return
		end
		
		-- local destinations = variablesToLuaList(statement.destinations)
		-- emit(destinations .. " = " .. staticFunctionName(statement.name, statement.baseType.name) .. "(")

		-- -- Collect constraint parameter map
		-- local constraints = {}
		-- for key, constraint in pairs(statement.constraints) do
		-- 	table.insert(constraints, "[" .. luaEncodedString(key) .. "] = " .. cConstraint(constraint))
		-- end

		-- -- Collect real arguments and constraint parameters
		-- local arguments = {}
		-- for _, argument in ipairs(statement.arguments) do
		-- 	table.insert(arguments, localName(argument.name))
		-- end
		-- local constraintsArgument = "{" .. table.concat(constraints, ", ") .. "}"
		-- table.insert(arguments, constraintsArgument)
		-- emit("\t" .. table.concat(arguments, ", "))

		-- emit(")")
		-- return
	elseif statement.tag == "assign" then
		comment(statement.destination.name .. " = " .. statement.source.name .. ";")
		emit(localName(statement.destination.name) .. " = " .. localName(statement.source.name) .. ";")
		return
	elseif statement.tag == "new" then
		comment(statement.destination.name .. " = new(...);")
		local name = localName(statement.destination.name)
		local cT = cType(statement.destination.type, structScope)
		if cT:sub(-1) == "*" then
			cT = cT:sub(1, -2)
		end
		emit(name .. " = ALLOCATE(" .. cT .. ");")
		
		for key, value in pairs(statement.fields) do
			emit(name .. "->" .. classFieldName(key) .. " = " .. localName(value.name) .. ";")
		end
		for key, constraint in pairs(statement.constraints) do
			local constraintField = "TODO"
			emit(name .. "->" .. constraintField .. " = " .. cConstraint(constraint, semantics) .. ";")
		end
		return
	elseif statement.tag == "return" then
		comment("return ...;")

		if #statement.sources == 1 then
			emit("return " .. localName(statement.sources[1].name) .. ";")
			return
		else
			local types = {}
			for _, source in ipairs(statement.sources) do
				table.insert(types, cType(source.type, structScope))
			end
			local tuple = preTupleName(types)
			local values = table.map(function(v) return localName(v.name) end, statement.sources)
			emit("return " .. tuple .. "_make(" .. table.concat(values, ", ") .. ");")
			return
		end
	elseif statement.tag == "if" then
		-- emit("if " .. localName(statement.condition.name) .. " then")
		-- generateStatement(statement.bodyThen, indentedEmitter(emit))
		-- emit("else")
		-- generateStatement(statement.bodyElse, indentedEmitter(emit))
		-- emit("end")
		-- return
	elseif statement.tag == "method-call" then
		-- local destinations = table.map(function(x) return localName(x.name) end, statement.destinations)
		-- destinations = table.concat(destinations, ", ")
		-- local method = methodFunctionName(statement.name, statement.baseInstance.type.name)
		-- emit(destinations .. " = " .. method .. "(")
		-- emit("\t" .. localName(statement.baseInstance.name))
		-- for _, argument in ipairs(statement.arguments) do
		-- 	emit("\t," .. localName(argument.name))
		-- end
		-- emit(")")
		-- return
	elseif statement.tag == "field" then
		comment(statement.destination.name .. " = " .. statement.base.name .. "." .. statement.name .. ";")
		emit(localName(statement.destination.name) .. " = ")
		emit("\t" .. localName(statement.base.name) .. "->" .. classFieldName(statement.name) .. ";")
		return
	elseif statement.tag == "generic-static-call" then
		-- local destinations = table.map(function(x) return localName(x.name) end, statement.destinations)
		-- destinations = table.concat(destinations, ", ")
		-- emit(destinations .. " = (" .. cConstraint(statement.constraint) .. ")." .. statement.staticName .. "(")
		-- for i, argument in ipairs(statement.arguments) do
		-- 	local comma = i == #statement.arguments and "" or ", "
		-- 	emit("\t" .. localName(argument.name) .. comma)
		-- end
		-- emit(")")
		-- return
	elseif statement.tag == "generic-method-call" then
		-- local destinations = table.map(function(x) return localName(x.name) end, statement.destinations)
		-- destinations = table.concat(destinations, ", ")
		-- emit(destinations .. " = (" .. cConstraint(statement.constraint) .. ")." .. statement.methodName .. "(")
		-- emit("\t" .. localName(statement.baseInstance.name))
		-- for _, argument in ipairs(statement.arguments) do
		-- 	emit("\t, " .. localName(argument.name))
		-- end
		-- emit(")")
		-- return
	end
	
	comment(statement.tag .. " ????")
	print("unknown statement tag `" .. statement.tag .. "`")
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
#include "stdio.h"
#include "stdlib.h"

#define ALLOCATE(T) ((T*)malloc(sizeof(T)))

// NOTE: closures must take at least one argument
#define CLOSURE(returnType, ...)                \
	struct {                                    \
		void* data;                             \
		returnType (*func)(void*, __VA_ARGS__); \
	}
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
			table.insert(sequence, "typedef struct _" .. name .. " {")
			local parameters = {}
			for i = 1, #list do
				table.insert(parameters, list[i] .. " _" .. i)
				table.insert(sequence, "\t" .. list[i] .. " _" .. i .. ";")
			end
			table.insert(sequence, "\tchar _;")
			table.insert(sequence, "} " .. name .. ";")
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
typedef struct _smol_Unit {
	void* nothing;
} smol_Unit;

typedef struct _smol_Boolean {
	int value;
} smol_Boolean;

typedef struct _smol_String {
	size_t length;
	char const* text;
} smol_String;

typedef struct _smol_Number {
	double value;
} smol_Number;

////////////////////////////////////////////////////////////////////////////////
]])

	forwardDeclareStruct("_smol_Unit", "smol_Unit")
	forwardDeclareStruct("_smol_Boolean", "smol_Boolean")
	forwardDeclareStruct("_smol_Number", "smol_Number")
	forwardDeclareStruct("_smol_String", "smol_String")

	-- Build the struct scope map
	local structScope = {}
	for _, class in ipairs(semantics.classes) do
		structScope[class.name] = classStructName(class.name)
	end	
	structScope = freeze(structScope)

	-- Generate a struct for each interface
	for _, interface in ipairs(semantics.interfaces) do
		table.insert(code, "// interface " .. interface.name)
		local structName = interfaceStructName(interface.name)
		table.insert(code, "typedef struct _" .. structName .. " {")
		for _, signature in ipairs(interface.signatures) do
			local returns = cTypeTuple(signature.returnTypes, demandTuple, structScope)
			local name = interfaceMember(signature.name)
			local parameters = {}
			if signature.modifier == "method" then
				table.insert(parameters, "void* /*this*/")
			end
			for _, parameter in ipairs(signature.parameters) do
				table.insert(parameters, cType(parameter.type))
			end

			local prototype = #parameters == 0 and "void* /*ignore*/ " or table.concat(parameters, ", ")
			table.insert(code, "\tCLOSURE(" .. returns .. ", " .. prototype .. ") " .. name .. ";")
		end
		table.insert(code, "\tchar _;")
		table.insert(code, "} " .. structName .. ";")
		forwardDeclareStruct("_" .. structName, structName)
		table.insert(code, "")
	end

table.insert(code, [[
void* smol_static_core_Out_println(smol_String* message) {
	// TODO: allow nulls, etc.
	for (size_t i = 0; i < message->length; i++) {
		putchar(message->text[i]);
	}
	return NULL;
}
]])

	-- Generate a struct for each class
	for _, class in ipairs(semantics.classes) do
		table.insert(code, "// class " .. class.name)
		local structName = classStructName(class.name)
		table.insert(code, "typedef struct _" .. structName .. " {")
		for _, field in ipairs(class.fields) do
			table.insert(code, "\t" .. cType(field.type, structScope) .. " " .. classFieldName(field.name) .. ";")
		end
		table.insert(code, "\tchar _;")
		table.insert(code, "} " .. structName .. ";")
		forwardDeclareStruct("_" .. structName, structName)
		table.insert(code, "")
	end

	-- TODO: generate a tagged union for each union

	local prototypeSequence = {}
	table.insert(code, prototypeSequence)
	table.insert(code, "")
	-- Add a prototype string to up here
	local function genPrototype(prototype)
		assert(prototype:find(" ") and prototype:find(";"))
		table.insert(prototypeSequence, prototype)
	end

	-- Generate a constraint-building-function for each constraint
	for _, definition in ipairs(table.concatted(semantics.classes, semantics.unions)) do
		for i, implement in ipairs(definition.implements) do
			local requirements = {}
			for key, constraint in pairs(definition.constraints) do
				table.insert(requirements, {name = key, constraint = constraint})
			end
			table.sort(requirements, function(a, b) return a.name < b.name end)
			local parameters = {}
			for _, p in ipairs(requirements) do
				table.insert(parameters, interfaceStructName(p.constraint.name) .. " p" .. i)
			end

			local interface = table.findwith(semantics.interfaces, "name", implement.name)
			assert(interface)

			-- Generate the wrapper for each method part of the interface
			local wrapped = {}
			for _, signature in ipairs(interface.signatures) do
				table.insert(code, "// for impl")

				-- Collect the constraints
				local constraints = {}
				for i, generic in ipairs(definition.generics) do
					for j, constraint in ipairs(definition.constraints) do
						table.insert(constraints, interfaceStructName(constraint.interface.name))
					end
				end

				local dataTupleType = demandTuple(constraints)
				if dataTupleType:sub(-1) ~= "*" then
					dataTupleType = dataTupleType .. "*"
				end

				-- Get the out type from the interface
				local wrapperName = cWrapperName(signature.name, definition.name, interface.name)
				wrapped[signature.name] = wrapperName
				local outType = cTypeTuple(signature.returnTypes, demandTuple, structScope)
				local cParameters = {"void* data_general"}

				-- Add implicit this parameter
				if signature.modifier == "method" then
					table.insert(cParameters, "void* this")
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
					-- TODO: add explicit cast
					table.insert(arguments, "this")
				end

				for _, parameter in ipairs(signature.parameters) do
					table.insert(arguments, localName(parameter.name))
				end

				-- Collect the constraint arguments for the implementation
				if signature.modifier == "static" then
					-- Only static functions take parameters
					if #constraints ~= 1 then
						for i, constraint in ipairs(constraints) do
							table.insert(arguments, "data->_" .. i)
						end
					else
						table.insert(arguments, "data")
					end
				end

				local implName
				if signature.modifier == "static" then
					implName = staticFunctionName(signature.name, definition.name)
				else
					implName = methodFunctionName(signature.name, definition.name)
				end

				-- TODO: convert out tuple types
				local invocation = implName .. "(" .. table.concat(arguments, ", ") .. ")"
				if #signature.returnTypes == 1 then
					-- Return the plain value
					table.insert(code, "\treturn " .. invocation .. ";")
				else
					-- May need to convert tuple types
					local func = table.findwith(definition.signatures, "name", signature.name)
					local defOut = cTypeTuple(func.returnTypes, demandTuple, structScope)
					local intOut = cTypeTuple(signature.returnTypes, demandTuple, structScope)
					table.insert(code, "\t" .. defOut .. " concrete_out = " .. invocation .. ";")
					table.insert(code, "\t" .. intOut .. " out;")
					for i = 1, #signature.returnTypes do
						table.insert(code, "\tout._" .. i .. " = concrete_out._" .. i .. ";")
					end
				end
				table.insert(code, "}")
			end

			-- Generate the main function
			local functionName = concreteConstraintFunctionName(definition.name, implement.name)
			local outType = interfaceStructName(implement.name)
			table.insert(code, "// " .. definition.name .. " implements " .. implement.name)
			table.insert(code, outType .. " " .. functionName .. "(" .. table.concat(parameters, ", ") .. ") {")
			local tuple = demandTuple(parameters)
			table.insert(code, "\t" .. tuple .. "* closed = ALLOCATE(" .. tuple .. ");")
			for i = 1, #parameters do
				table.insert(code, "\tclosed->_" .. i .. " = p" .. i)
			end

			table.insert(code, "\t" .. outType .. " out;")
			for _, signature in ipairs(interface.signatures) do
				table.insert(code, "\tout." .. interfaceMember(signature.name) .. ".data = closed;")
				local func = wrapped[signature.name]
				table.insert(code, "\tout." .. interfaceMember(signature.name) .. ".func = " .. func .. ";")
			end

			table.insert(code, "\treturn out;")
			table.insert(code, "}")
			table.insert(code, "")
		end
	end

	-- Add separator before functions
	table.insert(code, string.rep("/", 80))
	table.insert(code, "")

	-- Generate the body for each method and static
	for _, func in ipairs(semantics.functions) do
		local fullName = func.definitionName .. "." .. func.name
		table.insert(code, "// " .. func.signature.modifier .. " " .. fullName)
		if func.signature.foreign then
			table.insert(code, "// is foreign")
		else
			local thisType
			local definition = table.findwith(semantics.classes, "name", func.definitionName)
				or table.findwith(semantics.unions, "name", func.definitionName)
			assert(definition)
			if definition.tag == "class" then
				thisType = classStructName(definition.name) .. "*"
			elseif definition.tag == "union" then
				error "TODO"
			end
			assert(definition)

			-- Generate function header
			local cFunctionName
			local cParameters
			if func.signature.modifier == "static" then
				cFunctionName = staticFunctionName(func.name, func.definitionName)
				cParameters = {}
			else
				assert(func.signature.modifier == "method")
				cFunctionName = methodFunctionName(func.name, func.definitionName)
				cParameters = {thisType .. " " .. LUA_THIS_LOCAL}
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

					local t = interfaceStructName(interface.name)
					local identifier = C_CONSTRAINT_PARAMETER_PREFIX .. "_" .. i .. "_" .. j
					table.insert(cParameters, t .. " " .. identifier)
				end
			end
			local outType = cTypeTuple(func.returnTypes, demandTuple, structScope)
			local prototype = outType .. " " .. cFunctionName .. "(" .. table.concat(cParameters, ", ") .. ")"
			genPrototype(prototype .. ";")
			table.insert(code, prototype .. " {")

			-- Generate function body
			local function emit(line)
				table.insert(code, "\t" .. line)
			end
			generateStatement(func.body, emit, structScope, semantics)

			-- Close function body
			if func.body.returns ~= "yes" then
				table.insert(code, "\treturn NULL;")
			end
			table.insert(code, "}")
		end
		table.insert(code, "")
	end

	-- Generate the main function
	table.insert(code, "// Main " .. semantics.main)
	table.insert(code, "int main(int argv, char** argc) {")
	table.insert(code, "\t" .. staticFunctionName("main", semantics.main) .. "();")
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
