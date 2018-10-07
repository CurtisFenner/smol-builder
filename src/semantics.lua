-- Curtis Fenner, copyright (C) 2017

local Map = import "data/map.lua"

local Report = import "semantic-errors.lua"
local common = import "common.lua"

--------------------------------------------------------------------------------

local DefinitionASTUniverse = {}

-- RETURNS an empty definition AST universe
function DefinitionASTUniverse.new()
	local instance = {
		_objectsByPackage = {},
	}
	return setmetatable(instance, {__index = DefinitionASTUniverse})
end

-- RETURNS nothing
-- MODIFIES this
function DefinitionASTUniverse:createPackage(package)
	assert(type(package) == "string")
	self._objectsByPackage[package] = self._objectsByPackage[package] or {}
end

-- RETURNS nothing
-- REQUIRES the package has already been created
-- MODIFIES this
-- REPORTS a problem when this name has already been defined
function DefinitionASTUniverse:definitionAST(package, name, ast)
	assert(type(name) == "string")
	assert(self._objectsByPackage[package], "package not yet created")
	assert(type(ast.tag) == "string")

	if self._objectsByPackage[package][name] then
		Report.OBJECT_DEFINED_TWICE {
			fullName = package .. ":" .. name,
			firstLocation = self._objectsByPackage[package][name].location,
			secondLocation = ast.location,
		}
	end

	self._objectsByPackage[package][name] = {
		location = ast.location,
		ast = ast,
		fullName = package .. ":" .. name,
		view = false,
	}
end

-- RETURNS nothing
-- MODIFIES this to record a view associated with the given definition
function DefinitionASTUniverse:setSourceView(package, name, view)
	assert(self._objectsByPackage[package][name])
	assert(view)
	
	self._objectsByPackage[package][name].sourceView = view
end

-- RETURNS information about an object
-- REPORTS that the object with the given name doesn't exist if it doesn't
function DefinitionASTUniverse:lookupObject(package, name, useLocation)
	assert(type(package) == "string")
	assert(type(name) == "string")
	assert(useLocation)

	if not self._objectsByPackage[package] then
		Report.NO_SUCH_PACKAGE {
			package = package,
			location = useLocation,
		}
	elseif not self._objectsByPackage[package][name] then
		Report.NO_SUCH_OBJECT {
			name = package .. ":" .. name,
			location = useLocation,
		}
	end

	return self._objectsByPackage[package][name]
end

--------------------------------------------------------------------------------

local SourceScope = {}

-- RETURNS a new SourceScope
-- REQUIRES the package has been created in the given universe
function SourceScope.new(universe, package, packageLocation)
	assert(type(package) == "string")
	assert(packageLocation)

	local instance = {
		_package = package,
		_universe = universe,

		-- A mapping of name => information about a fully qualified object
		_scope = {},

		-- A set of packages that can be used in fully qualified names
		_packages = {[package] = packageLocation},
	}
	
	setmetatable(instance, {__index = SourceScope})

	assert(universe._objectsByPackage[package], "package not yet created")
	for name, information in pairs(universe._objectsByPackage[package]) do
		instance._scope[name] = {
			importLocation = information.location,
			importType = "definition",
			package = package,
			name = name,
		}
		universe:setSourceView(package, name, instance)
	end

	return instance
end

-- RETURNS nothing
-- MODIFIES this
-- REPORTS when a name has been imported/defined twice
function SourceScope:importObject(package, name, importLocation)
	assert(type(package) == "string")
	assert(type(name) == "string")
	assert(importLocation)

	if self._scope[name] then
		Report.NAME_IMPORTED_TWICE {
			name = name,
			firstLocation = self._scope[name].importLocation,
			secondLocation = importLocation,
		}
	end

	self._universe:lookupObject(package, name, importLocation)

	self._scope[name] = {
		importLocation = importLocation,
		importType = "import",
		package = package,
		name = name,
	}
end

-- RETURNS nothing
-- MODIFIES this
-- REPORTS when a package has been imported twice
function SourceScope:importPackage(package, importLocation)
	assert(type(package) == "string")
	assert(importLocation)

	if self._packages[package] then
		Report.PACKAGE_IMPORTED_TWICE {
			packageName = package,
			firstLocation = self._packages[package],
			secondLocation = importLocation,
		}
	end
	self._packages[package] = importLocation
end

-- RETURNS information about an object
function SourceScope:getObject(package, name, location)
	assert(package == false or type(package) == "string")
	assert(type(name) == "string")
	assert(location)

	if package then
		assert(type(package) == "string")
		if not self._packages[package] then
			Report.UNKNOWN_PACKAGE_USED {
				package = package,
				location = location,
			}
		end

		return self._universe:lookupObject(package, name, location)
	else
		local localInfo = self._scope[name]
		if not localInfo then
			Report.UNKNOWN_DEFINITION_USED {
				name = name,
				location = location,
			}
		end

		return self._universe:lookupObject(localInfo.package, name, location)
	end
end

-- RETURNS the name of this package
function SourceScope:getPackage()
	return self._package
end

--------------------------------------------------------------------------------

local TypeScope = {}

-- RETURNS a new TypeScope made from the current view
function TypeScope.fromSource(view)
	local instance = {
		_sourceView = view,
		_generics = {},

		-- The constraint to use for `#Self`.
		-- `false` indicates that `#Self` is illegal in this scope.
		_self = false,
	}

	return setmetatable(instance, {__index = TypeScope})
end

-- RETURNS nothing
-- MODIFIES this
function TypeScope:setSelf(interface)
	assert(type(interface.package) == "string")
	assert(type(interface.name) == "string")

	self._self = interface
end

-- RETURNS nothing
-- REQUIRES name is a valid generic name (ie, begings [A-Z] and is not "Self")
-- MODIFIES this
-- REPORTS when a generic is being re-defined
function TypeScope:defineGeneric(index, name, location)
	assert(type(index) == "number")
	assert(type(name) == "string")
	assert(name ~= "Self")
	assert(location)

	if self._generics[name] then
		Report.GENERIC_DEFINED_TWICE {
			name = name,
			firstLocation = self._generics[name].location,
			secondLocation = location,
		}
	end

	self._generics[name] = {
		index = index,
		location = location,
		constraints = {},
	}
end

-- RETURNS nothing
-- MODIFIES this
-- REPORTS when this generic name has not been defined
-- These constraints are TRUSTED and must be scanned again to produce errors!
function TypeScope:addGenericConstraint(name, plainConstraint, variableLocation)
	assert(type(name) == "string")
	assert(plainConstraint.tag == "constraint-plain-interface")
	assert(variableLocation)

	if not self._generics[name] then
		Report.UNKNOWN_GENERIC_USED {
			name = name,
			location = variableLocation,
		}
	end

	table.insert(self._generics[name].constraints, plainConstraint)
end

function TypeScope:_getObject(package, name, location)
	return self._sourceView:getObject(package, name, location)
end

-- RETURNS a new plain-constraint for the given object
-- REPORTS when types mentioned in this are not visible or have the wrong arity
-- NOTE: Does NOT report unsatisfied constraints
function TypeScope:astToPlainType(ast)
	if ast.tag == "keyword-generic" then
		if not self._self then
			Report.SELF_OUTSIDE_INTERFACE {
				location = ast.location,
			}
		end

		return {
			tag = "type-plain-self",
			interface = self._self,
		}
	elseif ast.tag == "type-keyword" then
		-- TODO: disallow Never, etc
		return {
			tag = "type-plain-keyword",
			name = ast.name,
		}
	elseif ast.tag == "generic" then
		if not self._generics[ast.name] then
			Report.UNKNOWN_GENERIC_USED {
				name = ast.name,
				location = ast.location,
			}
		end

		return {
			tag = "type-plain-generic",
			name = ast.name,
		}
	elseif ast.tag == "concrete-type" then
		local info = self:_getObject(ast.package, ast.base, ast.location)

		-- Check object type and arity
		local definitionAST = info.ast
		if definitionAST.tag ~= "union-definition" and definitionAST.tag ~= "class-definition" then
			Report.INTERFACE_USED_AS_TYPE {
				interface = definitionAST.fullName,
				location = ast.location,
			}
		elseif #definitionAST.generics.parameters ~= #ast.arguments then
			Report.WRONG_ARITY {
				name = info.fullName,
				definitionLocation = info.location,
				expectedArity = #definitionAST.generics.parameters,
				givenArity = #ast.arguments,
				location = ast.location,
			}
		end

		-- Recurse
		local arguments = {}
		for _, argument in ipairs(ast.arguments) do
			table.insert(arguments, self:astToPlainType(argument))
		end

		return {
			tag = "type-plain",
			object = {
				package = info.package,
				name = info.name,
			},
			arguments = arguments,
		}
	end

	error("unhandled type ast `" .. ast.tag .. "`")
end

-- RETURNS a new plain-constraint for the given object
-- REPORTS when types mentioned in this are not visible or have the wrong arity
-- NOTE: Does NOT report unsatisfied constraints
function TypeScope:astToPlainConstraint(ast)
	assert(ast.tag == "concrete-type")

	local info = self:_getObject(ast.package, ast.base, ast.location)

	-- Check object type and arity
	local definitionAST = info.ast
	if definitionAST.tag ~= "interface-definition" then
		Report.CONSTRAINTS_MUST_BE_INTERFACES {
			is = definitionAST.tag == "class-definition" and "class" or "union",
			typeShown = info.fullName,
			location = ast.location,
		}
	elseif #definitionAST.generics.parameters ~= #ast.arguments then
		Report.WRONG_ARITY {
			name = info.fullName,
			definitionLocation = info.location,
			expectedArity = #definitionAST.generics.parameters,
			givenArity = #ast.arguments,
			location = ast.location,
		}
	end

	-- Recurse
	local arguments = {}
	for _, a in ipairs(ast.arguments) do
		table.insert(arguments, self:astToPlainType(a))
	end

	return {
		tag = "constraint-plain-interface",
		object = {
			package = info.package,
			name = info.name,
		},
		arguments = arguments,
	}
end

--------------------------------------------------------------------------------

local function signatureSkeleton(typeScope, signatureAST)
	local parameters = {}
	for _, parameterAST in ipairs(signatureAST.parameters) do
		table.insert(parameters, {
			name = parameterAST.name.lexeme,
			typePlain = typeScope:astToPlainType(parameterAST.type),
			location = parameterAST.location,
		})
	end

	local returns = {}
	for _, returnAST in ipairs(signatureAST.returnTypes) do
		table.insert(returns, typeScope:astToPlainType(returnAST))
	end

	assert(type(signatureAST.modifier.lexeme) == "string")
	return {
		modifier = signatureAST.modifier.lexeme,
		parameters = parameters,
		returns = returns,
		requiresASTs = signatureAST.requires,
		ensuresAST = signatureAST.ensures,
		bang = signatureAST.bang,
		typeScope = typeScope,
	}
end

--------------------------------------------------------------------------------

local InterfaceSkeleton = {}

function InterfaceSkeleton.new(typeScope, ast)
	assert(ast.tag == "interface-definition")

	local instance = {
		tag = "interface-skeleton",
		_typeScope = typeScope,
		_methods = {},
		_statics = {},
	}

	local memberLocations = {}

	for _, signatureAST in ipairs(ast.signatures) do
		local name = signatureAST.name.lexeme
		assert(type(name) == "string")

		if memberLocations[name] then
			Report.MEMBER_DEFINED_TWICE {
				name = name,
				firstLocation = memberLocations[name],
				secondLocation = signatureAST.name.location,
			}
		end
		memberLocations[name] = signatureAST.name.location

		local signature = signatureSkeleton(typeScope, signatureAST)
		if signature.modifier == "method" then
			instance._methods[name] = signature
		else
			instance._methods[name] = signature
		end
	end

	return setmetatable(instance, {__index = InterfaceSkeleton})
end

--------------------------------------------------------------------------------

local UnionSkeleton = {}

function UnionSkeleton.new(typeScope, ast)
	assert(ast.tag == "union-definition")

	local instance = {
		tag = "union-skeleton",
		_typeScope = typeScope,
		_variants = {},
		_methods = {},
		_statics = {},
		_implements = {},
	}

	local memberLocations = {}

	for _, implements in ipairs(ast.implements) do
		table.insert(instance._implements, typeScope:astToPlainConstraint(implements))
	end

	for _, fieldAST in ipairs(ast.fields) do
		local name = fieldAST.name.lexeme

		if memberLocations[name] then
			Report.MEMBER_DEFINED_TWICE {
				name = name,
				firstLocation = memberLocations[name],
				secondLocation = fieldAST.name.location,
			}
		end
		memberLocations[name] = fieldAST.name.location

		local typePlain = typeScope:astToPlainType(fieldAST.type)
		instance._variants[name] = {
			location = fieldAST.location,
			typePlain = typePlain,
		}
	end

	for _, methodAST in ipairs(ast.methods) do
		local name = methodAST.signature.name.lexeme

		if memberLocations[name] then
			Report.MEMBER_DEFINED_TWICE {
				name = name,
				firstLocation = memberLocations[name],
				secondLocation = methodAST.signature.name.location,
			}
		end
		memberLocations[name] = methodAST.signature.name.location
	
		local body = false
		if not methodAST.foreign then
			body = methodAST.body
		end

		local signature = signatureSkeleton(typeScope, methodAST.signature)
		if signature.modifier == "method" then
			instance._methods[name] = {
				signature = signature,
				body = body,
			}
		else
			instance._statics[name] = {
				signature = signature,
				body = body,
			}
		end
	end

	return setmetatable(instance, {__index = UnionSkeleton})
end

--------------------------------------------------------------------------------

local ClassSkeleton = {}

function ClassSkeleton.new(typeScope, ast)
	assert(ast.tag == "class-definition")

	local instance = {
		tag = "class-skeleton",
		_typeScope = typeScope,
		_fields = {},
		_methods = {},
		_statics = {},
		_implements = {},
	}

	local memberLocations = {}

	for _, implements in ipairs(ast.implements) do
		table.insert(instance._implements, typeScope:astToPlainConstraint(implements))
	end

	for _, fieldAST in ipairs(ast.fields) do
		local name = fieldAST.name.lexeme

		if memberLocations[name] then
			Report.MEMBER_DEFINED_TWICE {
				name = name,
				firstLocation = memberLocations[name],
				secondLocation = fieldAST.name.location,
			}
		end
		memberLocations[name] = fieldAST.name.location

		local typePlain = typeScope:astToPlainType(fieldAST.type)
		instance._fields[name] = {
			location = fieldAST.location,
			typePlain = typePlain,
		}
	end

	for _, methodAST in ipairs(ast.methods) do
		local name = methodAST.signature.name.lexeme

		if memberLocations[name] then
			Report.MEMBER_DEFINED_TWICE {
				name = name,
				firstLocation = memberLocations[name],
				secondLocation = methodAST.signature.name.location,
			}
		end
		memberLocations[name] = methodAST.signature.name.location
	
		local body = false
		if not methodAST.foreign then
			body = methodAST.body
		end

		local signature = signatureSkeleton(typeScope, methodAST.signature)
		if signature.modifier == "method" then
			instance._methods[name] = {
				signature = signature,
				body = body,
			}
		else
			instance._statics[name] = {
				signature = signature,
				body = body,
			}
		end
	end

	return setmetatable(instance, {__index = ClassSkeleton})
end

--------------------------------------------------------------------------------

-- RETURNS a skeletal description of one class/union
local function skeletonStructure(view, ast)
	local group
	if ast.tag == "class-definition" then
		group = "class"
	elseif ast.tag == "union-definition" then
		group = "union"
	elseif ast.tag == "interface-definition" then
		group = "interface"
	end
	assert(group)

	local typeScope = TypeScope.fromSource(view)
	for i, parameter in ipairs(ast.generics.parameters) do
		typeScope:defineGeneric(i, parameter.name, parameter.location)
	end

	if group == "interface" then
		-- `#Self` is only allowed in interfaces
		typeScope:setSelf {
			package = view:getPackage(),
			name = ast.name,
		}
	end

	-- Record the required constraints
	for _, constraint in ipairs(ast.generics.constraints) do
		typeScope:addGenericConstraint(
			constraint.parameter.name,
			typeScope:astToPlainConstraint(constraint.constraint),
			constraint.parameter.location
		)
	end

	if group == "class" then
		return group, ClassSkeleton.new(typeScope, ast)
	elseif group == "union" then
		return group, UnionSkeleton.new(typeScope, ast)
	elseif group == "interface" then
		return group, InterfaceSkeleton.new(typeScope, ast)
	end
	error "unreachable"
end

--------------------------------------------------------------------------------

local ProgramSkeleton = {}

function ProgramSkeleton.new(sources)
	-- Collect the universe of definitions as ASTs
	local astUniverse = DefinitionASTUniverse.new()
	for _, source in ipairs(sources) do
		local packageName = source.package.name
		astUniverse:createPackage(packageName)

		for _, definition in ipairs(source.definitions) do
			astUniverse:definitionAST(packageName, definition.name, definition)
		end
	end

	local instance = {
		_objects = {
			class = {},
			union = {},
			interface = {},
		},
	}

	-- Compile each source
	for _, source in ipairs(sources) do
		-- Prepare this source's view into the universe
		local view = SourceScope.new(astUniverse, source.package.name, source.package.location)

		-- Bring all imports into scope
		for _, import in ipairs(source.imports) do
			if import.definition then
				-- Importing a particular object
				view:importObject(
					import.packageName,
					import.definition.name,
					import.location
				)
			else
				-- Allowing use of a package
				view:importPackage(import.packageName, import.location)
			end
		end

		-- Create each object
		for _, definition in ipairs(source.definitions) do
			local group, structure = skeletonStructure(view, definition)
			local packageName = view:getPackage()
			local definitionName = definition.name
			
			instance._objects[group][packageName] = instance._objects[group][packageName] or {}
			instance._objects[group][packageName][definitionName] = structure
		end
	end

	return setmetatable(instance, {__index = ProgramSkeleton})
end

-- RETURNS an IR program
local function semanticsBeta(sources, main)
	assert(type(main) == "string")

	local program = ProgramSkeleton.new(sources)

	error "TODO: Cook results."
end

return {
	semantics = semanticsBeta,
}
