-- Curtis Fenner, copyright (C) 2017

-- RETURNS a string
local function luaizeName(name)
	return name:gsub(":", "_")
end

-- RETURNS a string
local function staticFunctionName(name, definition)
	return "smol_static_" .. luaizeName(definition) .. "_" .. luaizeName(name)
end

-- RETURNS a string
local function methodFunctionName(name, definition)
	assertis(name, "string")
	assertis(definition, "string")
	assert(definition:match(":"))

	return "smol_method_" .. luaizeName(definition) .. "_" .. luaizeName(name)
end

-- RETURNS a string
local function concreteConstraintFunctionName(definitionName, interfaceName)
	return "smol_concrete_constraint_" .. luaizeName(definitionName) .. "_"
end

-- RETURNS a string representing a Lua identifier for a Smol variable or parameter
local function localName(name)
	assert(not name:find(":"))

	return "smol_local_" .. name
end

-- RETURNS a string representing a Lua identifier for a Smol field
local function fieldName(name)
	assert(not name:find(":"))

	return "smol_field_" .. name
end

-- RETURNS a string
local function commented(message)
	return "-- " .. message:gsub("\n", "\n-- ")
end

-- RETURNS a string
local function luaEncodedString(value)
	local out = {}
	local safe = "[A-Za-z0-9 +-^*/:.,?!%%%[%]]"
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
	return tostring(value)
end

local function indentedEmitter(emit)
	return function(line)
		return emit("\t" .. line)
	end
end

-- RETURNS nothing
-- Appends strings to code
local function generateStatement(statement, emit)
	assertis(statement, "StatementIR")

	--print("#", statement.tag)

	if statement.tag == "block" then
		for _, subStatement in ipairs(statement.statements) do
			generateStatement(subStatement, emit)
		end
		return
	end

	-- Plain statements
	if statement.tag == "local" then
		emit("local " .. localName(statement.variable.name))
		return
	elseif statement.tag == "string" then
		emit(localName(statement.destination.name))
		emit("\t= " .. luaEncodedString(statement.string))
		return
	elseif statement.tag == "number" then
		emit(localName(statement.destination.name))
		emit("\t= " .. luaEncodedNumber(statement.number))
		return
	elseif statement.tag == "boolean" then
		emit(localName(statement.destination.name))
		emit("\t= " .. tostring(statement.boolean))
		return
	elseif statement.tag == "this" then
		emit(localName(statement.destination.name) .. " = this")
		return
	elseif statement.tag == "static-call" then
		local destinationNames = {}
		for _, destination in ipairs(statement.destinations) do
			table.insert(destinationNames, localName(destination.name))
		end
		local destinations = table.concat(destinationNames, ", ")
		emit(destinations .. " = " .. staticFunctionName(statement.name, statement.baseType.name) .. "(")

		-- Collect real arguments and constraint parameters
		local arguments = {}
		assert(#statement.constraints == 0, "TODO: constraints")
		for _, argument in ipairs(statement.arguments) do
			table.insert(arguments, localName(argument.name))
		end
		emit("\t" .. table.concat(arguments, ", "))

		emit(")")
		return
	elseif statement.tag == "assign" then
		emit(localName(statement.destination.name) .. " = " .. localName(statement.source.name))
		return
	elseif statement.tag == "new" then
		emit(localName(statement.destination.name) .. " = {")
		for key, value in pairs(statement.fields) do
			emit("\t" .. fieldName(key) .. " = " .. localName(value.name))
		end
		for key, constraint in pairs(statement.constraints) do
			error "TODO"
		end
		emit("}")
		return
	elseif statement.tag == "return" then
		local values = table.map(function(v) return localName(v.name) end, statement.sources)
		emit("return " .. table.concat(values, ", "))
		return
	elseif statement.tag == "method-call" then

		local destinations = table.map(function(x) return localName(x.name) end, statement.destinations)
		destinations = table.concat(destinations, ", ")
		local method = methodFunctionName(statement.name, statement.baseInstance.type.name)
		emit(destinations .. " = " .. method .. "(")
		emit("\t" .. localName(statement.baseInstance.name))
		for i, argument in ipairs(statement.arguments) do
			emit("\t," .. localName(statement.arguments[i].name))
		end
		emit(")")
		return
	elseif statement.tag == "field" then
		emit(localName(statement.destination.name) .. " = ")
		emit("\t" .. localName(statement.base.name) .. "." .. fieldName(statement.name))
		return
	end
	
	error("unknown statement tag `" .. statement.tag .. "`")
end

return function(semantics, arguments)
	if not arguments.out then
		quit("out argument must be specified for lua code generator")
	end

	-- Open the file
	local file = io.open(arguments.out, "wb")
	if not file then
		quit("Could not open file `" .. arguments.out .. "` for writing")
	end

	file:write [[
local function smol_static_core_Out_println(message)
	print(message)
end
	]]

	local code = {"-- Generated by Smol Lua compiler", commented(INVOKATION), ""}

	-- Generate a constraint-building-function for each constraint
	for _, definition in ipairs(table.concatted(semantics.classes, semantics.unions)) do
		for _, interface in ipairs(definition.implements) do
			table.insert(code, "function")
			table.insert(code, concreteConstraintFunctionName(definition.name, interface.name))
			table.insert(code, "(requirements)")
			table.insert(code, "\terror 'TODO'")
			table.insert(code, "end")
		end
	end

	-- Generate the body for each method and static
	for _, func in ipairs(semantics.functions) do
		table.insert(code, "-- " .. func.signature.modifier .. " " .. func.name)
		if func.signature.foreign then
			table.insert(code, "-- is foreign")
		else
			-- Generate function header
			table.insert(code, "function")
			local parameters
			if func.signature.modifier == "static" then
				table.insert(code, staticFunctionName(func.name, func.definitionName))
				parameters = {}
			else
				assert(func.signature.modifier == "method")
				table.insert(code, methodFunctionName(func.name, func.definitionName))
				parameters = {"this"}
			end

			for _, parameter in ipairs(func.parameters) do
				table.insert(parameters, localName(parameter.name))
			end

			assert(#func.generics == 0, "TODO: constraint parameters")
			table.insert(code, "(" .. table.concat(parameters, ", ") .. ")")

			-- Generate function body
			local function emit(line)
				table.insert(code, "\t" .. line)
			end
			generateStatement(func.body, emit)

			-- Close function body
			table.insert(code, "end")
		end
		table.insert(code, "")
	end

	-- Generate the main function
	table.insert(code, "-- Main " .. semantics.main)
	table.insert(code, staticFunctionName("main", semantics.main) .. "()")

	-- Write the code to the output file
	for _, line in ipairs(code) do
		file:write(line .. "\n")
	end
	file:close()
end
