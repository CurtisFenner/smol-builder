local Map = import "data/map.lua"

local Report = import "semantic-errors.lua"
local common = import "common.lua"

--------------------------------------------------------------------------------

-- Represents Smol classes and Smol unions.
local ValueObject = {}

function ValueObject.new(ast)
	assert(ast.tag == "class-definition" or ast.tag == "union-definition")

	local instance = {
		_ast = ast,
	}

	return setmetatable(instance, {__index = ValueObject})
end

--------------------------------------------------------------------------------

-- Represents Smol interfaces.
local InterfaceObject = {}

function InterfaceObject.new(ast)
	assert(ast.tag == "interface-definition")

	local instance = {
		_ast = ast,
	}

	return setmetatable(instance, {__index = InterfaceObject})
end

--------------------------------------------------------------------------------

-- Represents the subset of objects visible to a single source file.
local ObjectScope = {}

function ObjectScope.new(registry, ticket, packageName, packageLocation)
	assert(registry)
	assert(type(ticket) == "string")
	assert(type(packageName) == "string")
	assert(packageLocation)

	local instance = {
		_registry = registry,
		_ticket = ticket,
		_packageName = packageName,
		_packageLocation = packageLocation,
		_aliases = {},
	}

	return setmetatable(instance, {__index = ObjectScope})
end

function ObjectScope:_defineObject(name, location, object)
	assert(type(name) == "string")
	assert(location)
	assert(object)

	self._registry:defineObject(self._packageName, name, location, object)
	self:_setObjectAlias(name, location, self._packageName, name)
end

function ObjectScope:_setObjectAlias(alias, location, packageName, objectName)
	assert(type(alias) == "string")
	assert(location)
	assert(type(packageName) == "string")
	assert(type(objectName) == "string")

	if self._aliases[alias] then
		Report.OBJECT_DEFINED_TWICE {
			name = alias,
			firstLocation = self._aliases[alias].location,
			secondLocation = location,
		}
	end

	self._aliases[alias] = {
		packageName = packageName,
		objectName = objectName,
		location = location,
	}
end

function ObjectScope:getQualifiedObject(packageName, objectName, kind)
	assert(type(packageName) == "string")
	assert(type(objectName) == "string")
	assert(kind == "class" or kind == "union" or kind == "interface")
	
	error "TODO"
end

function ObjectScope:getUnqualifiedObject(objectName, kind)
	assert(type(objectName) == "string")
	assert(kind == "class" or kind == "union" or kind == "interface")

	error "TODO"
end

-- Registers all of the objects defined in this AST to this source scope and the
-- associated ObjectRegistry.
-- RETURNS nothing
function ObjectScope:initializeObjectList(ast)
	assert(ast.tag == "source")

	-- Records objects created in this package.
	for _, definition in ipairs(ast.definitions) do
		local name = definition.header.name.lexeme
		local location = definition.header.location
		if definition.tag == "class-definition" then
			self:_defineObject(name, location, ValueObject.new(definition))
		elseif definition.tag == "union-definition" then
			self:_defineObject(name, location, ValueObject.new(definition))
		elseif definition.tag == "interface-definition" then
			self:_defineObject(name, location, InterfaceObject.new(definition))
		else
			error("unhandled definition tag `" .. definition.tag .. "`")
		end
	end
end

function ObjectScope:_importPackage(package, location)
	assert(type(package) == "string")
	assert(location)

	error "TODO"
end

function ObjectScope:_importObject(package, objectName, location)
	assert(type(package) == "string")
	assert(type(objectName) == "string")
	assert(location)

	error "TODO"
end

function ObjectScope:_doImports(imports)
	for _, import in ipairs(imports) do
		if import.objectName then
			self:_importObject(import.packageName.lexeme, import.objectName.lexeme, import.location)
		else
			assert(type(import.packageName.lexeme) == "string")
			self:_importPackage(import.packageName.lexeme, import.location)
		end
	end
end

-- Sets up the local scope and compiles each object separately.
function ObjectScope:doWork(ast)
	-- Process all imports.
	self:_doImports(ast.imports)
end

--------------------------------------------------------------------------------

-- Represents all available objects in the program.
local ObjectRegistry = {}

function ObjectRegistry.new()
	local instance = {
		_definedPackages = {},
	}

	return setmetatable(instance, {__index = ObjectRegistry})
end

-- RETURNS an empty ObjectScope for the describe source.
-- MODIFIES this.
function ObjectRegistry:createScope(ticket, packageName, packageLocation)
	assert(type(ticket) == "string")
	assert(type(packageName) == "string")
	assert(packageLocation)

	if not self._definedPackages[packageName] then
		self._definedPackages[packageName] = {
			objects = {},
		}
	end
	return ObjectScope.new(self, ticket, packageName, packageLocation)
end

function ObjectRegistry:defineObject(packageName, objectName, location, object)
	assert(type(packageName) == "string")
	assert(type(objectName) == "string")
	assert(location)
	assert(object)

	-- The package should have been defined before objects are defined.
	local package = self._definedPackages[packageName]
	assert(package)
	if package.objects[objectName] then
		Report.OBJECT_DEFINED_TWICE {
			name = string.format("%s:%s", packageName, objectName),
			firstLocation = package.objects[objectName].location,
			secondLocation = location,
		}
	end

	package.objects[objectName] = {
		object = object,
		location = location,
	}
end

function ObjectRegistry:getObject(packageName, objectName, kind)
	assert(type(packageName) == "string")
	assert(type(objectName) == "string")
	assert(kind == "class" or kind == "union" or kind == "interface")
end

--------------------------------------------------------------------------------

-- RETURNS an IR-Program.
local function semantics(sourceASTs, main)
	assert(type(main) == "string")

	local registry = ObjectRegistry.new()

	-- Define the set of all available objects.
	local sourceScopes = {}
	for ticket, sourceAST in pairs(sourceASTs) do
		local package = sourceAST.package.name.lexeme
		assert(type(package) == "string")

		local scope = registry:createScope(ticket, package, sourceAST.package.location)
		scope:initializeObjectList(sourceAST)
		sourceScopes[ticket] = scope
	end

	-- Set up each source scope with its local objects.
	for ticket, scope in pairs(sourceScopes) do
		scope:doWork(sourceASTs[ticket])
	end

	return {}
end

--------------------------------------------------------------------------------

return {
	semantics = semantics,
}
