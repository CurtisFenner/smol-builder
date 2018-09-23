local common = import "common.lua"

local BUILTIN_NAME_MAP = {
	Int = true,
	String = true,
	Boolean = true,
	Unit = true,
	Never = true,
}

--------------------------------------------------------------------------------

local FOREIGN_IMPLEMENTATION = {}

FOREIGN_IMPLEMENTATION["core:ASCII.formatInt"] = [[
	smol_String_T* out1;
	out1 = ALLOCATE(smol_String_T);
	out1->text = ALLOCATE_ARRAY(32, char);
	out1->length = (size_t)sprintf(out1->text, "%" PRId64, smol_local_value->value);
]]

FOREIGN_IMPLEMENTATION["core:Out.println"] = [[
	for (size_t i = 0; i < smol_local_message->length; i++) {
		putchar(smol_local_message->text[i]);
	}
	printf("\n");
	smol_Unit_T* out1 = NULL;
]]

FOREIGN_IMPLEMENTATION["String:concatenate"] = [[
	smol_String_T* out1 = ALLOCATE(smol_String_T);
	out1->length = smol_local_left->length + smol_local_right->length;
	out1->text = ALLOCATE_ARRAY(out1->length, char);
	for (size_t i = 0; i < smol_local_left->length; i++) {
		out1->text[i] = smol_local_left->text[i];
	}
	for (size_t i = 0; i < smol_local_right->length; i++) {
		out1->text[i + smol_local_left->length] = smol_local_right->text[i];
	}
]]

FOREIGN_IMPLEMENTATION["String:eq"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	size_t length = smol_local_left->length;
	if (length != smol_local_right->length) {
		out1->value = 0;
	} else {
		out1->value = 0 == memcmp(smol_local_left->text, smol_local_right->text, length);
	}
]]

FOREIGN_IMPLEMENTATION["Boolean:implies"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = !smol_local_left->value || smol_local_right->value;
]]

FOREIGN_IMPLEMENTATION["Boolean:not"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = !smol_local_left->value;
]]

FOREIGN_IMPLEMENTATION["Boolean:eq"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = (!smol_local_left->value) == (!smol_local_right->value);
]]

FOREIGN_IMPLEMENTATION["Boolean:and"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = smol_local_left->value && smol_local_right->value;
]]

FOREIGN_IMPLEMENTATION["Boolean:or"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = smol_local_left->value || smol_local_right->value;
]]

FOREIGN_IMPLEMENTATION["Int:difference"] = [[
	smol_Int_T* out1 = ALLOCATE(smol_Int_T);
	out1->value = smol_local_this->value - smol_local_arg2->value;
]]

FOREIGN_IMPLEMENTATION["Int:sum"] = [[
	smol_Int_T* out1 = ALLOCATE(smol_Int_T);
	out1->value = smol_local_this->value + smol_local_arg2->value;
]]

FOREIGN_IMPLEMENTATION["Int:product"] = [[
	smol_Int_T* out1 = ALLOCATE(smol_Int_T);
	out1->value = smol_local_this->value * smol_local_arg2->value;
]]

FOREIGN_IMPLEMENTATION["Int:quotient"] = [[
	smol_Int_T* out1 = ALLOCATE(smol_Int_T);
	out1->value = smol_local_this->value / smol_local_arg2->value;
]]

FOREIGN_IMPLEMENTATION["Int:negate"] = [[
	smol_Int_T* out1 = ALLOCATE(smol_Int_T);
	out1->value = -smol_local_this->value;
]]

FOREIGN_IMPLEMENTATION["Int:lessThan"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = smol_local_this->value < smol_local_arg2->value;
]]

FOREIGN_IMPLEMENTATION["Int:eq"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = smol_local_this->value == smol_local_arg2->value;
]]

FOREIGN_IMPLEMENTATION["Int:isPositive"] = [[
	smol_Boolean_T* out1 = ALLOCATE(smol_Boolean_T);
	out1->value = 0 < smol_local_this->value;
]]

--------------------------------------------------------------------------------

-- Represents a source file
local Program = {}
Program.__index = Program

-- RETURNS a blank program
function Program.new(indent)
	local instance = {
		_chunks = {},
		_indent = indent or 0,
		_unique = {count = 0},
	}
	return setmetatable(instance, Program)
end

-- Appends a line of text to the end of this progra
-- RETURNS nothing
-- MODIFIES this
function Program:write(text)
	assert(type(text) == "string")
	table.insert(self._chunks, string.rep("\t", self._indent) .. text)
end

-- RETURNS a Program representing a chunk appended to the end of the file
-- MODIFIES this
function Program:section(indent)
	local c = Program.new(self._indent + (indent or 0))
	c._unique = self._unique
	table.insert(self._chunks, c)
	return c
end

-- RETURNS a unique string beginning with the given prefix
-- MODIFIES this
function Program:vendUnique(prefix)
	assert(type(prefix) == "string")

	self._unique.count = self._unique.count + 1
	return prefix .. (self._unique.count - 1)
end

-- RETURNS a string representing all of the lines of this program
function Program:serialize()
	local seq = {}
	for i = 1, #self._chunks do
		if type(self._chunks[i]) == "string" then
			seq[i] = self._chunks[i]
		else
			seq[i] = self._chunks[i]:serialize()
		end
	end
	return table.concat(seq, "\n")
end

--------------------------------------------------------------------------------

-- Represents a C source file
local CProgram = {}
CProgram.__index = CProgram

-- RETURNS a blank C program
function CProgram.new()
	local instance = {
		_program = Program.new(),
	}

	-- Initialize root information
	instance._tupleMap = {}
	instance._closureMap = {}
	instance._root = instance

	setmetatable(instance, CProgram)
	
	instance.preamble = instance:section()

	instance._forward = instance._program:section()
	instance._forward:write("// FORWARD DECLARATIONS")

	instance._definitions = instance._program:section()
	instance._definitions:write("// DECLARATION BODIES")

	instance._prototypes = instance._program:section()
	instance._prototypes:write("// FUNCTION PROTOTYPES")

	instance._functions = instance._program:section()
	instance._functions:write("// FUNCTION IMPLEMENTATIONS")

	return instance
end

-- RETURNS this program's text as a string
function CProgram:serialize()
	return self._program:serialize()
end

-- RETURNS a C type name (not a pointer)
function CProgram:getClosure(rt, pts)
	if self ~= self._root then
		return self._root:getClosure(rt, pts)
	end

	assertis(rt, "string")
	assertis(pts, listType "string")

	local parameters = {"void*", table.unpack(pts)}

	local fptr = rt .. " (*func)(" .. table.concat(parameters, ", ") .. ")"

	if self._closureMap[fptr] then
		return self._closureMap[fptr]
	end

	local name = "_closure_" .. #table.keys(self._closureMap) .. "_T"
	self._closureMap[fptr] = name

	self:defineStruct(name, {
		{name = "data", type = "void*"},

		-- XXX: fix this
		{name = fptr, type = ""},
	})
	return name
end

-- RETURNS nothing
-- MODIFIES this program
function CProgram:defineStruct(name, fields)
	if self ~= self._root then
		return self._root:defineStruct(name, fields)
	end

	assertis(fields, listType(recordType {
		name = "string",
		type = "string",
	}))
	assert(1 <= #fields)

	self._forward:write("typedef struct " .. name .. "_struct " .. name .. ";")
	self._definitions:write("struct " .. name .. "_struct {")
	for _, field in ipairs(fields) do
		self._definitions:write("\t" .. field.type .. " " .. field.name .. ";")
	end
	self._definitions:write("};")
	self._definitions:write("")
end

-- RETURNS a string representing a (one word) C type with fields 
-- _1, _2, ..., _{#fields}
-- of the given C types
-- REQUIRES at least one field is given
function CProgram:getTuple(fields)
	if self ~= self._root then
		return self._root:getTuple(fields)
	end

	assertis(fields, listType "string")
	assert(1 <= #fields, "cannot make a tuple for zero fields")

	local id = table.concat(fields, ", ")
	assert(not id:find("\n"))
	if self._tupleMap[id] then
		return self._tupleMap[id]
	end

	-- Generate a unique name
	local name = "_tuple_" .. #table.keys(self._tupleMap) .. "z" .. id:gsub("[^a-zA-Z0-9]+", "_") .. "z_T"
	self._tupleMap[id] = name

	-- Create forward declaration
	self._forward:write("// tuple (" .. id .. ")")
	self._forward:write("typedef struct " .. name .. "_struct " .. name .. ";")
	self._forward:write("")

	-- Give definition
	self._definitions:write("struct " .. name .. "_struct {")
	for i = 1, #fields do
		self._definitions:write("\t" .. fields[i] .. " _" .. i .. ";")
	end
	self._definitions:write("};")
	self._definitions:write("")

	return name
end

-- RETURNS a C program section
-- MODIFIES this
function CProgram:defineFunction(name, returns, parameters)
	if self ~= self._root then
		return self._root:defineFunction(name, returns, parameters)
	end

	assert(type(name) == "string")
	assert(type(returns) == "string")
	assertis(parameters, listType(recordType {
		type = "string",
		name = "string",
	}))

	local ps = {}
	for _, p in ipairs(parameters) do
		table.insert(ps, p.type .. " " .. p.name)
	end

	local prototype = returns .. " " .. name .. "(" .. table.concat(ps, ", ") .. ")"

	self._prototypes:write(prototype .. ";")

	local fn = self._functions:section(0)
	fn:write(prototype .. " {")
	local body = fn:section(1)
	fn:write("}")
	fn:write("")

	local out = {
		_program = body,
		_root = self._root,
	}

	return setmetatable(out, CProgram)
end

-- RETURNS a name, a C program section
-- MODIFIES this
function CProgram:defineLambda(hint, returns, parameters)
	assert(type(hint) == "string")
	local name = self._program:vendUnique("_lambda" .. hint)
	return name, self:defineFunction(name, returns, parameters)
end

-- RETURNS a subsection of this program
-- MODIFIES this
function CProgram:section(indent)
	local s = self._program:section(indent)

	local out = {
		_program = s,
		_root = self._root,
	}
	return setmetatable(out, CProgram)
end

-- RETURNS nothing
-- TODO: get rid of this function so that all writing is structure
function CProgram:write(text)
	self._program:write(text)
end

-- Appends a comment to the program
-- RETURNS nothing
-- MODIFIES this
function CProgram:comment(text)
	assert(not text:find "\r")
	for line in (text .. "\n"):gmatch "([^\n]*)\n" do
		self:write(line == "" and "//" or "// " .. line)
	end
end

-- Appends a variable declaration to the program
-- RETURNS nothing
-- MODIFIES this
function CProgram:declareVariable(name, t)
	assert(type(name) == "string" and not name:find "[*%s]")
	assert(type(t) == "string")

	self:write(t .. " " .. name .. ";")
end

-- Appends a variable declaration to the program
-- RETURNS the name of the variable used
-- MODIFIES this
function CProgram:declareTemporary(t, hint)
	local name = self._program:vendUnique("_tmpvar" .. (hint or ""))
	self:declareVariable(name, t)
	return name
end

-- Appends an assignment to the program
-- RETURNS nothing
-- MODIFIES this
function CProgram:assign(lhs, rhs)
	assert(type(lhs) == "string")
	assert(type(rhs) == "string", type(rhs))

	self:write(lhs .. " = " .. rhs .. ";")
end

-- Appends a return to the program
-- RETURNS nothing
-- MODIFIES this
function CProgram:returnValue(value)
	assert(type(value) == "string")

	self:write("return " .. value .. ";")
end

--------------------------------------------------------------------------------

-- RETURNS a string
local function luaizeName(name)
	return name:gsub("[:.]", "_"):gsub("#", "hash_")
end

-- RETURNS a string
local function staticFunctionName(longName)
	assert(longName, "string")
	assert(longName:find ":", "expected longName `" .. longName .. "` to have a `:`")
	return "smol_static_" .. luaizeName(longName)
end

local CONSTRAINT_PARAMETER = "cons"
local TAG_FIELD = "tag"
local TAG_TYPE = "uint32_t"

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

-- RETURNS a C type name
local function compoundStructName(name)
	assertis(name, "string")

	if BUILTIN_NAME_MAP[name] then
		return "smol_" .. name .. "_T"
	end
	assert(name:find(":"))

	return "smol_compound_" .. name:gsub(":", "_") .. "_T"
end

-- RETURNS a string
local function commented(message)
	return "// " .. message:gsub("\n", "\n// ")
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
local function cEncodedNumber(value)
	assertis(value, "number")

	return string.format("%d", value)
end

-- RETURNS a C type string for the given smol type
-- When noPointer, get the underlying struct type
-- Otherwise, a pointer to the underlying struct type
local function cType(t, noPointer)
	assertis(t, "TypeKind")

	if t.tag == "compound-type" then
		-- Note that it does not distinguish by type parameters
		local base = compoundStructName(t.packageName .. ":" .. t.definitionName)
		if noPointer then
			return base
		end
		return base .. "*"
	elseif t.tag == "generic-type" or t.tag == "self-type" then
		assert(not noPointer)
		return "void*"
	elseif t.tag == "keyword-type" then
		local base = compoundStructName(t.name)
		if noPointer then
			return base
		end
		return base .. "*"
	end
end

-- RETURNS a C type name
local function interfaceStructName(name)
	assertis(name, "string")
	assert(name:find(":"))

	return "smol_interface_" .. name:gsub(":", "_") .. "_T"
end

-- RETURNS a C identifier
local function vtableMemberName(name)
	assertis(name, "string")
	assert(not name:find("[:.]"))

	return "d_smol_" .. name
end

-- RETURNS a C type string
local function cVTableType(c)
	assertis(c, "ConstraintKind")

	if c.tag == "interface-constraint" then
		return interfaceStructName(c.packageName .. ":" .. c.definitionName)
	end
	error("TODO")
end

-- RETURNS name, type as strings
-- MODIFIES program
local function generateVTable(a, program, info)
	assertis(a, "VTableIR")
	assertis(program, "object")
	assertis(info, recordType {
		constraints = mapType("string", recordType {
			members = listType "Signature",
		}),
		parameterIndices = mapType("string", "integer"),
		functionSignatures = mapType("string", "Signature")
	})

	if a.tag == "parameter-vtable" then
		program:comment("<parameter-vtable>")
		local tmpType = cVTableType(a.interface)
		local tmp = program:declareTemporary(tmpType, "_vtable")
		local i = info.parameterIndices[a.name]
		program:assign(tmp, CONSTRAINT_PARAMETER .. "->_" .. i)
		program:comment("</parameter-vtable>")
		return tmp, tmpType
	elseif a.tag == "concrete-vtable" then
		program:comment("<concrete-vtable>")
		local tmpType = cVTableType(a.interface)
		local tmp = program:declareTemporary(tmpType, "_vtable")

		local fullName = a.interface.packageName .. ":" .. a.interface.definitionName
		for _, f in ipairs(info.constraints[fullName].members) do
			-- Get type parameters and return type
			local rts = table.map(cType, f.returnTypes)
			local rTuple = program:getTuple(rts)
			local pt = {}
			for _, p in ipairs(f.parameters) do
				table.insert(pt, cType(p.type))
			end

			-- The C argument types of the static implementation may differ
			-- from the interface: the interface may use generics where the
			-- implementation puts statics.
			-- As long as the representation of the arguments are the same, this
			-- is OK.
			-- NOTE: C guarantees that all pointers-to-structs have comptabile
			-- representations.
			local closureType = program:getClosure(rTuple, pt)

			-- Collect the arguments to store in the closure's state
			local neededVariables = {}
			local neededTypes = {}
			for _, a in ipairs(a.arguments) do
				local n, t = generateVTable(a, program, info)
				table.insert(neededVariables, n)
				table.insert(neededTypes, t)
			end

			local needed
			if #neededVariables == 0 then
				needed = "NULL"
			else
				local neededTuple = program:getTuple(neededTypes)
				local neededName = program:declareTemporary(neededTuple .. "*", "_closure_state")
				program:assign(neededName, "ALLOCATE(" .. neededTuple .. ")")
				for i, n in ipairs(neededVariables) do
					program:assign(neededName .. "->_" .. i, n)
				end
				needed = neededName
			end

			-- Generate wrapper parameters
			local wrapperParameters = {{name = "data", type = "void*"}}
			local arguments = {"data"}
			local concreteFunctionName = a.concrete.packageName .. ":" .. a.concrete.definitionName .. "." .. f.memberName
			local concreteSignature = info.functionSignatures[concreteFunctionName]
			assert(#pt == #concreteSignature.parameters)
			for i, p in ipairs(pt) do
				table.insert(wrapperParameters, {
					name = "a" .. i,
					type = p,
				})
				local cast = "(" .. cType(concreteSignature.parameters[i].type) .. ")"
				table.insert(arguments, cast .. "a" .. i)
			end

			-- Generate wrapper function
			local fptr = staticFunctionName(concreteFunctionName)
			local wrapperName, wrapperBody = program:defineLambda(fptr, rTuple, wrapperParameters)
			wrapperBody:comment("Wrapper for `" .. concreteFunctionName .. "` impl `" .. common.showConstraintKind(a.interface))
			wrapperBody:comment(common.showSignature(concreteSignature))
			wrapperBody:comment(common.showSignature(f))
			local rawTupleType = program:getTuple(table.map(cType, concreteSignature.returnTypes))
			wrapperBody:declareVariable("out", rawTupleType)
			wrapperBody:assign("out", fptr .. "(" .. table.concat(arguments, ", ") .. ")")
			wrapperBody:declareVariable("ret", program:getTuple(rts))
			for i, r in ipairs(rts) do
				wrapperBody:assign("ret._" .. i, "(" .. r .. ")out._" .. i)
			end
			wrapperBody:returnValue("ret")

			local closureName = program:declareTemporary(closureType, "_closure")
			program:assign(closureName .. ".data", needed)
			program:assign(closureName .. ".func", wrapperName)
			program:assign(tmp .. "." .. vtableMemberName(f.memberName), closureName)
		end
		program:comment("</concrete-vtable>")
		return tmp, tmpType
	end
	error("unknown VTableIR tag `" .. a.tag .. "`")
end

-- RETURNS nothing
-- MODIFIES program to include C statements executing the given statement
local function generateStatement(statement, program, info)
	assertis(statement, "StatementIR")
	assertis(program, "object")
	assertis(info, recordType {
		constraints = mapType("string", recordType {
			members = listType "Signature",
		}),
		unions = mapType("string", recordType {
			tags = mapType("string", "integer"),
		}),
	})

	program:comment(statement.tag)

	if statement.tag == "proof" then
		if statement.returns == "yes" then
			program:write("assert(0); // assert false;")
		else
			program:comment("skipping proof")
		end
		return
	elseif statement.tag == "sequence" then
		for _, s in ipairs(statement.statements) do
			generateStatement(s, program, info)
		end
		return
	elseif statement.tag == "string-load" then
		local lhs = localName(statement.destination.name)
		local rhs = "ALLOCATE(smol_String_T)"
		program:assign(lhs, rhs)
		program:assign(lhs .. "->length", tostring(#statement.string))
		program:assign(lhs .. "->text", cEncodedString(statement.string))
		return
	elseif statement.tag == "local" then
		program:declareVariable(localName(statement.variable.name), cType(statement.variable.type))
		return
	elseif statement.tag == "nothing" then
		program:comment("nothing statement")
		return
	elseif statement.tag == "assign" then
		program:assign(localName(statement.destination.name), localName(statement.source.name))
		return
	elseif statement.tag == "return" then
		local types = {}
		local values = {}
		for _, r in ipairs(statement.sources) do
			table.insert(types, cType(r.type))
			table.insert(values, localName(r.name))
		end
		local rhs = "(" .. program:getTuple(types) .. "){" .. table.concat(values, ", ") .. "}"
		program:returnValue(rhs)
		return
	elseif statement.tag == "if" then
		local condition = localName(statement.condition.name) .. "->value"
		program:write("if (" .. condition .. ") {")
		generateStatement(statement.bodyThen, program:section(1), info)
		program:write("} else {")
		generateStatement(statement.bodyElse, program:section(1), info)
		program:write("}")
		return
	elseif statement.tag == "int-load" then
		local lhs = localName(statement.destination.name)
		local rhs = "ALLOCATE(smol_Int_T)"
		program:assign(lhs, rhs)
		program:assign(lhs .. "->value", cEncodedNumber(statement.number))
		return
	elseif statement.tag == "new-class" then
		local lhs = localName(statement.destination.name)
		local rhs = "ALLOCATE(" .. cType(statement.destination.type, true) .. ")"
		program:assign(lhs, rhs)
		for key, source in pairs(statement.fields) do
			program:assign(lhs .. "->" .. classFieldName(key), localName(source.name))
		end
		return
	elseif statement.tag == "new-union" then
		local lhs = localName(statement.destination.name)
		local rhs = "ALLOCATE(" .. cType(statement.destination.type, true) .. ")"
		program:assign(lhs, rhs)

		local defName = statement.destination.type.packageName .. ":" .. statement.destination.type.definitionName
		local definition = info.unions[defName]
		assert(definition)
		local fieldID = cEncodedNumber(definition.tags[statement.field])
		program:assign(lhs .. "->" .. TAG_FIELD, fieldID)
		program:assign(lhs .. "->" .. unionFieldName(statement.field), localName(statement.value.name))
		return
	elseif statement.tag == "static-call" then
		-- Generate constraints argument
		local vtables = {}
		local vtableTypes = {}
		for _, a in ipairs(statement.constraintArguments) do
			local vName, vType = generateVTable(a, program, info)
			table.insert(vtables, vName)
			table.insert(vtableTypes, vType)
		end

		local cArguments = {}
		if #vtables == 0 then
			table.insert(cArguments, "NULL")
		else
			-- Create constraint argument
			local tupleType = program:getTuple(vtableTypes)
			local tupleValue = "(" .. tupleType .. "){" .. table.concat(vtables, ", ") .. "}"
			local constraintArgument = program:declareTemporary(tupleType)
			program:assign(constraintArgument, tupleValue)
			table.insert(cArguments, "&" .. constraintArgument)
		end

		-- Get static form of signature
		local staticSignature = info.functionSignatures[statement.signature.longName]

		-- Add regular value arguments
		for i, a in ipairs(statement.arguments) do
			-- An explicit cast is necessary if the signature statically takes
			-- generics
			local cast = "(" .. cType(staticSignature.parameters[i].type) .. ")"
			table.insert(cArguments, cast .. localName(a.name))
		end

		-- Invoke the function
		program:comment("static-call " .. common.showSignature(statement.signature))
		local tmpType = program:getTuple(table.map(cType, staticSignature.returnTypes))
		local tmp = program:declareTemporary(tmpType)
		local cName = staticFunctionName(statement.signature.longName)
		local invocation = cName .. "(" .. table.concat(cArguments, ", ") .. ")"
		program:assign(tmp, invocation)

		-- Write to destinations
		for i, d in ipairs(statement.destinations) do
			-- An explicit cast is necessary if the signature statically returns
			-- generics
			local cast = "(" .. cType(d.type) .. ")"
			program:assign(localName(d.name), cast .. tmp .. "._" .. i)
		end
		return
	elseif statement.tag == "dynamic-call" then
		local vName, vType = generateVTable(statement.constraint, program, info)

		-- Add regular value arguments
		local cArguments = {}
		for _, a in ipairs(statement.arguments) do
			table.insert(cArguments, localName(a.name))
		end

		if #cArguments == 0 then
			program:comment("Problematic 0 argument call!")
		end

		-- Invoke the function
		local tmpType = program:getTuple(table.map(cType, statement.signature.returnTypes))
		local tmp = program:declareTemporary(tmpType)
		local closure = vName .. "." .. vtableMemberName(statement.signature.memberName)
		table.insert(cArguments, 1, closure .. ".data")
		local invocation = closure .. ".func(" .. table.concat(cArguments, ", ") .. ")"
		program:assign(tmp, invocation)

		-- Write to destinations
		for i, d in ipairs(statement.destinations) do
			program:assign(localName(d.name), tmp .. "._" .. i)
		end
		return
	elseif statement.tag == "boolean" then
		local lhs = localName(statement.destination.name)
		local rhs = "ALLOCATE(smol_Boolean_T)"
		program:assign(lhs, rhs)
		program:assign(lhs .. "->value", statement.boolean and "1" or "0")
		return
	elseif statement.tag == "field" then
		local lhs = localName(statement.destination.name)
		local rhs = localName(statement.base.name) .. "->" .. classFieldName(statement.name)
		program:assign(lhs, rhs)
		return
	elseif statement.tag == "unit" then
		local lhs = localName(statement.destination.name)
		program:assign(lhs, "NULL")
		return
	elseif statement.tag == "isa" then
		local lhs = localName(statement.destination.name)
		local rhs = "ALLOCATE(smol_Boolean_T)"
		local union = info.unions[statement.base.type.packageName .. ":" .. statement.base.type.definitionName]
		local getTag = localName(statement.base.name) .. "->" .. TAG_FIELD
		local value = getTag .. " == " .. union.tags[statement.variant]
		program:assign(lhs, rhs)
		program:assign(lhs .. "->value", value)
		return
	elseif statement.tag == "variant" then
		local lhs = localName(statement.destination.name)
		local rhs = localName(statement.base.name) .. "->" .. unionFieldName(statement.variant)
		program:assign(lhs, rhs)
		return
	elseif statement.tag == "match" then
		local tagVar = program:declareTemporary(TAG_TYPE, "tag")
		local getTag = localName(statement.base.name) .. "->" .. TAG_FIELD
		program:assign(tagVar, getTag)
		local union = info.unions[statement.base.type.packageName .. ":" .. statement.base.type.definitionName]
		for i, case in ipairs(statement.cases) do
			local tagValue = union.tags[case.variant]
			if i ~= 1 then
				program:write("else")
			end
			program:write("if (" .. tagVar .. " == " .. tagValue .. ") {")
			local body = program:section(1)
			generateStatement(case.statement, body, info)
			program:write("}")
		end
		assert(#statement.cases ~= 0)
		program:write("else {")
		program:write("\tassert(0);")
		program:write("}")
		return
	end

	error("unknown statement tag `" .. statement.tag .. "`")
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

	local code = CProgram.new()
	code.preamble:comment("Generated by Smol Lua compiler")
	code.preamble:comment(INVOCATION)
	code.preamble:write("")

	code.preamble:write([[
#include "assert.h"
#include "stdint.h"
#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "inttypes.h"

#define ALLOCATE(T) ((T*)malloc(sizeof(T)))
#define ALLOCATE_ARRAY(size, T) ((T*)malloc(size * sizeof(T)))

#define PANIC(message) do { printf(message "\n"); exit(1); } while (0)

////////////////////////////////////////////////////////////////////////////////
]])

	code:defineStruct("smol_Unit_T", {
		{type = "void*", name = "nothing"},
	})

	code:defineStruct("smol_Boolean_T", {
		{type = "int", name = "value"},
	})

	code:defineStruct("smol_String_T", {
		{type = "size_t", name = "length"},
		{type = "char*", name = "text"},
	})

	code:defineStruct("smol_Int_T", {
		{type = "int64_t", name = "value"},
	})

	-- Maintain some global information needed to compile statements
	local globalInfo = {
		constraints = {},
		unions = {},
		functionSignatures = {},
	}

	-- Generate a vtable struct for each interface
	for _, interface in ipairs(semantics.interfaces) do
		table.insert(code, "// interface " .. interface.fullName)
		local structName = interfaceStructName(interface.fullName)
		local fields = {{type = "char", name = "_"}}
		local memberList = {}
		for _, func in pairs(interface._functionMap) do
			local signature = func.signature

			-- Get return types
			local rt = {}
			for _, r in ipairs(signature.returnTypes) do
				table.insert(rt, cType(r))
			end
			assert(1 <= #rt)

			-- Get parameter types, padding with "void*" to get at least one
			local pt = {}
			for _, p in ipairs(signature.parameters) do
				table.insert(pt, cType(p.type))
			end

			local fieldType = code:getClosure(code:getTuple(rt), pt)

			table.insert(memberList, signature)
			table.insert(fields, {
				name = vtableMemberName(signature.memberName),
				type = fieldType,
			})
		end

		table.sort(memberList, function(a, b)
			return a.memberName < b.memberName
		end)
		table.sort(fields, function(a, b)
			return a.name < b.name
		end)

		-- Save struct info
		globalInfo.constraints[interface.fullName] = {members = memberList}

		code:defineStruct(structName, fields)
	end

	-- Generate a struct for each class
	for _, class in ipairs(semantics.compounds) do
		if class.tag == "class-definition" then
			local structName = compoundStructName(class.fullName)
			local fields = {{type = "void*", name = "foreign"}}

			-- Generate all value fields
			for _, field in pairs(class._fieldMap) do
				table.insert(fields, {
					name = classFieldName(field.name),
					type = cType(field.type),
				})
			end

			code:defineStruct(structName, fields)
		end
	end

	-- Generate a tagged union for each union
	for _, union in ipairs(semantics.compounds) do
		if union.tag == "union-definition" then
			local structName = compoundStructName(union.fullName)
			globalInfo.unions[union.fullName] = {tags = {}}

			-- TODO: Generate a union rather than a struct
			local fields = {{type = TAG_TYPE, name = TAG_FIELD}}

			-- Generate tag
			assert(#table.keys(union._fieldMap) < 2 ^ 16, "TODO: Too many fields!")

			-- Generate all value fields
			local fieldList = {}
			for _, field in pairs(union._fieldMap) do
				table.insert(fieldList, field.name)
				table.insert(fields, {
					type = cType(field.type),
					name = unionFieldName(field.name),
				})
			end
			table.sort(fields, function(a, b)
				return a.name < b.name
			end)
			table.sort(fieldList)

			-- Save tag map
			for i, f in ipairs(fieldList) do
				globalInfo.unions[union.fullName].tags[f] = i
			end

			-- Create VTable struct
			code:defineStruct(structName, fields)
		end
	end

	-- Save the signatures of all functions
	for _, func in ipairs(semantics.functions) do
		globalInfo.functionSignatures[func.signature.longName] = func.signature
	end

	-- Generate the body for each method and static
	for _, func in ipairs(semantics.functions) do
		-- Generate function header
		local cFunctionName = staticFunctionName(func.signature.longName)
		local cParameters = {}

		-- Add constraint parameter(s)
		local vtableTypes = {}
		for _, constraintArgument in ipairs(func.constraintArguments) do
			local t = cVTableType(constraintArgument.constraint)
			table.insert(vtableTypes, t)
		end
		if #vtableTypes == 0 then
			-- Pad tuple to length 1
			table.insert(vtableTypes, "int")
		end

		table.insert(cParameters, {
			type = code:getTuple(vtableTypes) .. "*",
			name = CONSTRAINT_PARAMETER,
		})

		-- Add value parameters
		for _, parameter in ipairs(func.signature.parameters) do
			table.insert(cParameters, {
				type = cType(parameter.type),
				name = localName(parameter.name),
			})
		end

		-- Get the returns
		local cOutType = code:getTuple(table.map(cType, func.signature.returnTypes))

		-- Generate the function prototype
		local body = code:defineFunction(cFunctionName, cOutType, cParameters)
		body:comment(common.showSignature(func.signature))

		-- Generate function body
		if not func.signature.foreign then
			-- Get global information about the function
			local parameterIndices = {}
			for i, a in ipairs(func.constraintArguments) do
				parameterIndices[a.name] = i
			end
			local info = table.with(globalInfo, "parameterIndices", parameterIndices)

			-- Compile the function
			assert(func.body.returns == "yes")
			generateStatement(func.body, body, info)
		else
			-- Get body from table
			local impl = FOREIGN_IMPLEMENTATION[func.signature.longName]
			assert(impl, "no impl for foreign `" .. func.signature.longName .. "`")
			body:write("// Foreign function `" .. func.signature.longName .. "`\n" .. impl)

			-- Wrap for tuple type
			local cast = "(" .. cOutType .. ")"
			local rhs = "{"
			for i = 1, #func.signature.returnTypes do
				if i ~= 1 then
					rhs = rhs .. ", "
				end
				rhs = rhs .. "out" .. i
			end
			rhs = rhs .. "}"
			body:returnValue(cast .. rhs)
		end
	end

	-- Generate the main function
	local argc_argv = {
		{name = "argc", type = "int"},
		{name = "argv", type = "char**"},
	}
	local main = code:defineFunction("main", "int", argc_argv)
	main:write(staticFunctionName(semantics.main .. ":main") .. "(NULL);")
	main:returnValue("0")

	-- Write the code to the output file
	file:write(code:serialize())
	file:close()
end
