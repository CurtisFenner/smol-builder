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
		package = package,
		name = name,
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
		Report.OBJECT_DEFINED_TWICE {
			fullName = name,
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

local function showPlainType(t)
	assert(type(t.tag) == "string")

	if t.tag == "type-self-plain" then
		return "#Self"
	elseif t.tag == "type-keyword-plain" then
		return t.name
	elseif t.tag == "type-generic-plain" then
		return "#" .. t.name
	elseif t.tag == "type-object-plain" then
		local prefix = t.object.package .. ":" .. t.object.object
		if #t.arguments == 0 then
			return prefix
		end
		local arguments = {}
		for _, argument in ipairs(t.arguments) do
			table.insert(arguments, showPlainType(argument))
		end
		return prefix .. "[" .. table.concat(arguments, ", ") .. "]"
	end

	error("unreachable")
end

local function showPlainConstraint(t)
	assert(type(t.tag) == "string")

	if t.tag == "constraint-interface-plain" then
		local prefix = t.object.package .. ":" .. t.object.object
		if #t.arguments == 0 then
			return prefix
		end
		local arguments = {}
		for _, argument in ipairs(t.arguments) do
			table.insert(arguments, showPlainType(argument))
		end
		return prefix .. "[" .. table.concat(arguments, ", ") .. "]"
	end

	error("unreachable")
end

-- RETURNS a plain type
-- REQUIRES all #Self and generics are present in the mapping
-- ENSURES return.location == t.location
local function substitutePlainType(mapping, t)
	assert(type(t.tag) == "string")

	if t.tag == "type-self-plain" then
		assert(mapping.Self)

		-- Substitute in the current location
		local obj = {}
		for k, v in pairs(mapping.Self) do
			obj[k] = v
		end
		obj.location = t.location
		return obj
	elseif t.tag == "type-keyword-plain" then
		return t
	elseif t.tag == "type-generic-plain" then
		assert(mapping[t.name])

		-- Substitute in the current location
		local obj = {}
		for k, v in pairs(mapping[t.name]) do
			obj[k] = v
		end
		obj.location = t.location
		return obj
	elseif t.tag == "type-object-plain" then
		local arguments = {}
		for _, argument in ipairs(t.arguments) do
			table.insert(arguments, substitutePlainType(mapping, argument))
		end

		return {
			tag = "type-object-plain",
			object = t.object,
			arguments = arguments,
			location = t.location,
		}
	end

	error("unhandled plain type tag `" .. t.tag .. "`")
end

-- RETURNS a plain constraint
local function substitutePlainConstraint(mapping, constraint)
	assert(type(constraint.tag) == "string", "constraint.tag is string")

	if constraint.tag == "constraint-interface-plain" then
		local arguments = {}
		for _, argument in ipairs(constraint.arguments) do
			table.insert(arguments, substitutePlainType(mapping, argument))
		end
		return {
			tag = "constraint-interface-plain",
			object = constraint.object,
			arguments = arguments,
			location = constraint.location,
		}
	end

	error("unhandled plain constraint tag `" .. constraint.tag .. "`")
end

local TypeScope = {}

-- RETURNS a new TypeScope made from the current view
function TypeScope.fromSource(view, objectDescription)
	assert(type(objectDescription) == "string")

	local instance = {
		_sourceView = view,
		_generics = {},
		_genericList = {},
		_objectDescription = objectDescription,

		-- The constraint to use for `#Self`.
		-- `false` indicates that `#Self` is illegal in this scope.
		_selfConstraint = false,
	}

	return setmetatable(instance, {__index = TypeScope})
end

-- RETURNS a list of plain generic type objects.
-- Use sparingly! This class can automatically substitute arguments.
function TypeScope:dumpPlainGenerics()
	local variables = {}
	for _, name in ipairs(self._genericList) do
		table.insert(variables, {
			tag = "type-generic-plain",
			name = name,
			location = self._generics[name].location,
		})
	end
	return variables
end

-- RETURNS nothing
-- MODIFIES this
function TypeScope:setSelfConstraint(constraint)
	assert(type(constraint.tag) == "string")
	assert(not self._selfConstraint, "self constraint has already been set")

	self._selfConstraint = constraint
end

-- RETURNS the plain type passed to :setSelf
-- REQUIRES that self has bene set
function TypeScope:getRawSelfConstraint()
	assert(self._selfConstraint, "self constraint has not been set")

	return self._selfConstraint
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
		location = location,
		constraints = {},
	}
	table.insert(self._genericList, name)
end

-- RETURNS nothing
-- MODIFIES this
-- REPORTS when this generic name has not been defined
-- These constraints are TRUSTED and must be scanned again to produce errors!
function TypeScope:addGenericConstraint(name, plainConstraint, variableLocation)
	assert(type(name) == "string")
	assert(plainConstraint.tag == "constraint-interface-plain")
	assert(variableLocation)

	if not self._generics[name] then
		Report.UNKNOWN_GENERIC_USED {
			name = name,
			location = variableLocation,
		}
	end

	table.insert(self._generics[name].constraints, plainConstraint)
end

-- RETURNS a function mapping plain types, for use by the containing skeleton
function TypeScope:makeConstraintSubstituter(arguments)
	assert(#arguments == #self._genericList)

	local mapping = {}
	for i, name in ipairs(self._genericList) do
		mapping[name] = arguments[i]
	end

	return function(t)
		return substitutePlainConstraint(mapping, t)
	end
end

-- RETURNS a list of the constraints required, given the arguments.
function TypeScope:getRequiredConstraints(arguments, selfType)
	assert(#arguments == #self._genericList)
	assert(selfType == false or selfType)

	local mapping = {}
	for i, name in ipairs(self._genericList) do
		mapping[name] = arguments[i]
	end
	mapping.Self = selfType

	local required = {}
	for i, name in ipairs(self._genericList) do
		for _, constraint in ipairs(self._generics[name].constraints) do
			assert(constraint.location)
			assert(arguments[i].location)
			table.insert(required, {
				of = arguments[i],
				constraint = substitutePlainConstraint(mapping, constraint),
				cause = self._objectDescription,
				component = "its " .. i .. "th type parameter `#" .. name .. "`",
				requiredLocation = constraint.location,
				neededLocation = arguments[i].location,
			})
		end
	end

	return required
end

function TypeScope:_getObject(package, name, location)
	return self._sourceView:getObject(package, name, location)
end

-- RETURNS a new plain-type for the given object
-- REPORTS when types mentioned in this are not visible or have the wrong arity
-- NOTE: Does NOT report unsatisfied constraints
function TypeScope:astToPlainType(ast)
	if ast.tag == "keyword-generic" then
		if not self._selfConstraint then
			Report.SELF_OUTSIDE_INTERFACE {
				location = ast.location,
			}
		end

		return {
			tag = "type-self-plain",
			location = ast.location,
		}
	elseif ast.tag == "type-keyword" then
		-- TODO: disallow Never, etc
		return {
			tag = "type-keyword-plain",
			name = ast.name,
			location = ast.location,
		}
	elseif ast.tag == "generic" then
		if not self._generics[ast.name] then
			Report.UNKNOWN_GENERIC_USED {
				name = ast.name,
				location = ast.location,
			}
		end

		return {
			tag = "type-generic-plain",
			name = ast.name,
			location = ast.location,
		}
	elseif ast.tag == "concrete-type" then
		local info = self:_getObject(ast.package, ast.base, ast.location)

		-- Check object type and arity
		local definitionAST = info.ast
		if definitionAST.tag ~= "union-definition" and definitionAST.tag ~= "class-definition" then
			Report.INTERFACE_USED_AS_TYPE {
				interface = info.fullName,
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
			tag = "type-object-plain",
			object = {
				package = info.package,
				object = info.name,
			},
			arguments = arguments,
			location = ast.location,
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
		tag = "constraint-interface-plain",
		object = {
			package = info.package,
			object = info.name,
		},
		arguments = arguments,
		location = ast.location,
	}
end

-- RETURNS true when `supplied` satisfies `required`
local function plainSatisfiesConstraint(supplied, required)
	assert(type(supplied.tag) == "string")
	assert(type(required.tag) == "string")

	return showPlainConstraint(supplied) == showPlainConstraint(required)
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
		anchorLocation = ast.name.location,
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

function InterfaceSkeleton:genericRequirements(plainArguments, selfType)
	assert(selfType)
	return self._typeScope:getRequiredConstraints(plainArguments, selfType)
end

--------------------------------------------------------------------------------

local UnionSkeleton = {}

function UnionSkeleton.new(typeScope, ast)
	assert(ast.tag == "union-definition")

	local instance = {
		tag = "union-skeleton",
		anchorLocation = ast.name.location,
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

function UnionSkeleton:genericRequirements(plainArguments)
	return self._typeScope:getRequiredConstraints(plainArguments, false)
end

--------------------------------------------------------------------------------

local ClassSkeleton = {}

function ClassSkeleton.new(typeScope, ast)
	assert(ast.tag == "class-definition")

	local instance = {
		tag = "class-skeleton",
		anchorLocation = ast.name.location,
		_typeScope = typeScope,
		_fields = {},
		_methods = {},
		_statics = {},
		_implements = {},
	}

	-- Record implements claims
	for _, implements in ipairs(ast.implements) do
		table.insert(instance._implements, typeScope:astToPlainConstraint(implements))
	end

	local memberLocations = {}

	-- Record fields
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

	-- Record methods and statics
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

-- RETURNS a list of records as [{
--     of = plain type, constraint = plain constraint
-- }]
function ClassSkeleton:genericRequirements(plainArguments)
	return self._typeScope:getRequiredConstraints(plainArguments, false)
end

-- RETURNS a list of plain constraints
function ClassSkeleton:implements(arguments)
	local substituter = self._typeScope:makeConstraintSubstituter(arguments)
	local list = {}
	for _, claim in ipairs(self._implements) do
		table.insert(list, substituter(claim))
	end
	return list
end

--------------------------------------------------------------------------------

-- RETURNS a skeletal description of one class/union
local function skeletonStructure(view, ast, objectDescription)
	local group
	if ast.tag == "class-definition" then
		group = "class"
	elseif ast.tag == "union-definition" then
		group = "union"
	elseif ast.tag == "interface-definition" then
		group = "interface"
	end
	assert(group)

	local typeScope = TypeScope.fromSource(view, ("%s `%s`"):format(group, objectDescription))
	for i, parameter in ipairs(ast.generics.parameters) do
		typeScope:defineGeneric(i, parameter.name, parameter.location)
	end

	if group == "interface" then
		-- `#Self` is only allowed in interfaces
		local plainConstraint = {
			tag = "constraint-interface-plain",
			object = {},
		}
		local arguments = {}
		for i, parameter in ipairs(ast.generics.parameters) do
			table.insert(arguments, {
				tag = "type-generic-plain",
				name = parameter.name,
				location = parameter.location,
			})
		end
		typeScope:setSelfConstraint {
			tag = "constraint-interface-plain",
			object = {
				package = view:getPackage(),
				object = ast.name.lexeme,
			},
			arguments = arguments,
			location = ast.name.location,
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
		return group, ClassSkeleton.new(typeScope, ast), typeScope
	elseif group == "union" then
		return group, UnionSkeleton.new(typeScope, ast), typeScope
	elseif group == "interface" then
		return group, InterfaceSkeleton.new(typeScope, ast), typeScope
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
			local objectName = definition.name.lexeme
			astUniverse:definitionAST(packageName, objectName, definition)
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
			local packageName = view:getPackage()
			local objectName = definition.name.lexeme
			local description = packageName .. ":" .. objectName
			local group, structure, extra = skeletonStructure(view, definition, description)

			local group = instance._objects[group]
			group[packageName] = group[packageName] or {}
			group[packageName][objectName] = {
				object = structure,
				extra = extra,
			}
		end
	end

	return setmetatable(instance, {__index = ProgramSkeleton})
end

-- REQUIRES the object exist
-- RETURNS the object's skeleton
function ProgramSkeleton:getObject(object)
	local packageName = object.package
	local objectName = object.object
	assert(packageName and objectName)

	if not self._objects.class[packageName] then
		self._objects.class[packageName] = {}
	end
	if not self._objects.union[packageName] then
		self._objects.union[packageName] = {}
	end
	if not self._objects.interface[packageName] then
		self._objects.interface[packageName] = {}
	end

	local class = self._objects.class[packageName][objectName]
	local union = self._objects.union[packageName][objectName]
	local interface = self._objects.interface[packageName][objectName]

	return (class or union or interface).object or error "no such object"
end

-- RETURNS a set of classes as {packageName => {objectName => {
--     object = class skeleton, extra = typeScope
-- }}
function ProgramSkeleton:getClasses()
	return self._objects.class
end

-- RETURNS a set of interfaces as {packageName => {objectName => {
--     object = interface skeleton, extra = typeScope
-- }}
function ProgramSkeleton:getInterfaces()
	return self._objects.interface
end

--------------------------------------------------------------------------------

local BlockScope = {}

-- RETURNS a new BlockScope
function BlockScope.new(skeleton, context)
	assert(skeleton, "skeleton")
	assert(context, "context")
	assert(context.newObject == false or context.newObject.objectName)
	assert(type(context.bang) == "boolean")

	local instance = {
		_skeleton = skeleton,
		_stack = {},

		-- The name of the object to use, or false if `new()` cannot be used
		_newObject = context.newObject,

		-- Whether or not ! actions can be used
		_bang = context.bang,
	}

	return setmetatable(instance, {__index = BlockScope})
end

-- RETURNS nothing
-- MODIFIES this
function BlockScope:defineVariable(name, location, type)
	assert(type(name) == "string")
	assert(location)
	assert(type.tag)

	if self._stack[name] then
		Report.VARIABLE_DEFINED_TWICE {
			name = name,
			first = self._stack[name].location,
			second = location,
		}
	end

	self._stack[name] = {
		location = location,
		type = type,
	}
end

REGISTER_TYPE("Type", choiceType(
	recordType {
		tag = constantType "type-keyword",
		name = "string",
	},
	recordType {
		tag = constantType "type-generic",
		name = "string",
	},
	recordType {
		tag = constantType "type-object",
		object = recordType {
			package = "string",
			object = "string",
		},
		arguments = listType "Type",
	},
	recordType {
		tag = constantType "type-self",
	}
))

-- RETURNS nothing
-- REPORTS when a problem is found
function BlockScope:checkTypeSatisfies(requirement, typeScope)
	assert(requirement.of and requirement.of.tag)
	assert(requirement.constraint and requirement.constraint.tag)
	assert(requirement.cause and requirement.component)
	assert(requirement.requiredLocation)
	assert(requirement.neededLocation)

	-- Extra information for the error message
	local trail = {}

	if requirement.of.tag == "type-generic-plain" then
		local satisfied = false
		-- TODO: remove private access
		local supplied = typeScope._generics[requirement.of.name]
		assert(supplied)
		for _, constraint in ipairs(supplied.constraints) do
			if plainSatisfiesConstraint(constraint, requirement.constraint) then
				return
			end
			table.insert(trail, "\t" .. showPlainConstraint(constraint))
		end
	elseif requirement.of.tag == "type-self-plain" then
		-- #Self implements only this interface
		local supplied = typeScope:getRawSelfConstraint()
		table.insert(trail, "\t" .. showPlainConstraint(supplied))
		if plainSatisfiesConstraint(supplied, requirement.constraint) then
			return
		end
	elseif requirement.of.tag == "type-object-plain" then
		local object = self._skeleton:getObject(requirement.of.object)
		assert(object.tag == "class-skeleton" or object.tag == "union-skeleton")
		
		local supplies = object:implements(requirement.of.arguments)
		for _, supplied in ipairs(supplies) do
			if plainSatisfiesConstraint(supplied, requirement.constraint) then
				return
			end
		end
	elseif requirement.of.tag == "type-keyword-plain" then
		-- TODO: Keywords only implement built-in constraints
	else
		error("unhandled type tag `" .. requirement.of.tag .. "`")
	end

	if #trail ~= 0 then
		table.insert(trail, 1, string.format(
			"\nThe type `%s` implements the following constraints:",
			showPlainType(requirement.of)
		))
	end

	Report.TYPE_MUST_IMPLEMENT_CONSTRAINT {
		cause = requirement.cause,
		component = requirement.component,
		constraint = showPlainConstraint(requirement.constraint),
		type = showPlainType(requirement.of),
		requiredLocation = requirement.requiredLocation,
		neededLocation = requirement.neededLocation,
		trail = table.concat(trail, "\n"),
	}
end

-- RETURNS a Type
-- REPORTS when the plain type is not valid (e.g., type arguments don't
-- satisfy the constraints required by the base type)
function BlockScope:upgradePlainType(plain, typeScope)
	assert(typeScope)

	if plain.tag == "type-self-plain" then
		return {
			tag = "type-self",
		}
	elseif plain.tag == "type-keyword-plain" then
		return {
			tag = "type-keyword",
			name = plain.name,
		}
	elseif plain.tag == "type-generic-plain" then
		return {
			tag = "type-generic",
			name = plain.name,
		}
	elseif plain.tag == "type-object-plain" then
		local arguments = {}
		for _, argumentPlain in ipairs(plain.arguments) do
			table.insert(arguments, self:upgradePlainType(argumentPlain, typeScope))
		end

		assert(plain.object.object and plain.object.package)
		local object = self._skeleton:getObject(plain.object)
		assert(object.tag == "class-skeleton" or object.tag == "union-skeleton")

		local requirements = object:genericRequirements(plain.arguments)
		for _, requirement in ipairs(requirements) do
			self:checkTypeSatisfies(requirement, typeScope)
		end

		return {
			tag = "type-object",
			object = plain.object,
			arguments = arguments,
		}
	end
	error("unhandled plain type tag `" .. plain.tag .. "`")
end

-- RETURNS a Constraint
-- REPORTS when the plain constraint is not valid (e.g., type arguments don't
-- satisfy the constraints required by the base interface)
function BlockScope:upgradePlainConstraint(plain, typeScope)
	assert(typeScope)

	if plain.tag == "constraint-interface-plain" then
		local arguments = {}
		for _, argumentPlain in ipairs(plain.arguments) do
			table.insert(arguments, self:upgradePlainType(argumentPlain, typeScope))
		end

		assert(plain.object.object and plain.object.package)
		local object = self._skeleton:getObject(plain.object)
		assert(object.tag == "interface-skeleton")

		local requirements = object:genericRequirements(plain.arguments, {
			tag = "type-self-plain",
			location = plain.location,
		})
		for _, requirement in ipairs(requirements) do
			self:checkTypeSatisfies(requirement, typeScope)
		end

		return {
			tag = "constraint-object",
			object = plain.object,
			arguments = arguments,
		}
	end

	error("unhanled plain constraint tag `" .. plain.tag .. "`")
end

--------------------------------------------------------------------------------

-- RETURNS a Statement
local function compileStatement(scope, ast)
	error "TODO"
end

-- RETURNS a Class, a list of functions
local function compileClass(skeleton, classInfo)
	assert(classInfo.object and classInfo.extra)
	local objectScope = BlockScope.new(skeleton, {
		newObject = false,
		bang = false,
	})

	local class = classInfo.object

	-- Check the implements and generic constraints are well-formed
	local genericContainer = classInfo.extra
	local generics = genericContainer:dumpPlainGenerics()
	local required1 = genericContainer:getRequiredConstraints(generics, false)
	for _, requirement in ipairs(required1) do
		-- TODO: avoid private access
		objectScope:upgradePlainConstraint(requirement.constraint, class._typeScope)
	end

	local implementsClaims = class:implements(generics)
	for _, claim in ipairs(implementsClaims) do
		-- TODO: avoid private access
		objectScope:upgradePlainConstraint(claim, class._typeScope)
	end

	return {"TODO"}, {}
end

-- RETURNS an Interface
local function compileInterface(skeleton, interface)
	assert(interface.object and interface.extra)
	assert(interface.object.anchorLocation)
	local objectScope = BlockScope.new(skeleton, {
		newObject = false,
		bang = false,
	})

	local genericContainer = interface.extra
	local generics = genericContainer:dumpPlainGenerics()
	local required = genericContainer:getRequiredConstraints(generics, {
		tag = "type-self-plain",
		location = interface.object.anchorLocation,
	})
	
	-- Check that the generic constraints are well-formed
	for _, requirement in ipairs(required) do
		objectScope:upgradePlainConstraint(requirement.constraint, interface.object._typeScope)
	end
end

-- RETURNS an IR program:
-- {
--     classes = [{
--         packageName = string,
--         objectName = string,
--         fields = { string => Type },
--     }],
--     unions = [{
--         packageName = string,
--         objectName = string,
--         variants = { string => Type }
--     }],
--     interfaces = [{
--         packageName = string,
--         objectName = string,
--         arguments = [{packageName = string, objectName = string}],
--         members = { string => plain signature }
--         PRE-CONDITIONS?
--         POST-CONDITIONS?
--     }],
--     functions = [{
--         packageName = string,
--         objectName = string,
--         memberName = string,
--         signature = plain signature,
--         constraints = [ ??? ],
--         body = statement,
--         PRE-CONDITIONS?
--         POST-CONDITIONS?
--     }]
--     main = {packageName, objectName, memberName = string}
-- }
-- Notes:
-- Classes and unions are "unboxed" and do not list their constraints. Instead,
-- constraints are passed to functions (possibly by closures for any "boxed"
-- values)
local function semanticsBeta(sources, main)
	assert(type(main) == "string")

	local skeleton = ProgramSkeleton.new(sources)

	local program = {}
	program.functions = {}

	program.classes = {}
	for packageName, classes in pairs(skeleton:getClasses()) do
		for className, class in pairs(classes) do
			local struct, functions = compileClass(skeleton, class)
			table.insert(program.classes, struct)
			for _, f in ipairs(functions) do
				table.insert(program.functions, f)
			end
		end
	end

	program.interfaces = {}
	for packageName, interfaces in pairs(skeleton:getInterfaces()) do
		for interfaceName, interface in pairs(interfaces) do
			local struct = compileInterface(skeleton, interface)
			table.insert(program.interfaces, struct)
		end
	end

	os.exit(2)
	error "TODO: Cook results."
end

return {
	semantics = semanticsBeta,
}
