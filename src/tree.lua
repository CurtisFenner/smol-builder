
-- Represents a method call. This can either become a static dispatch or
-- a dynamic dispatch, depending on whether or not the type of the base is
-- generic or concrete.
local MethodCallTree = {}

function MethodCallTree.new(base, access, location, ticket)
	local instance = {tag = "expr-method-call"}
	instance._base = base
	instance._methodName = access.methodName
	instance._bang = access.bang
	instance._arguments = access.arguments
	instance._ticket = ticket
	instance.location = location

	return setmetatable(instance, {__index = MethodCallTree})
end

function MethodCallTree.fromBinary(ast, ticket)
	local instance = {tag = "expr-method-call-binary"}
	instance._base = ast.left
	instance._methodName = error "TODO"
	instance._bang = false
	instance._arguments = {ast.right}
	instance._ticket = ticket
	instance.location = ast.location

	return setmetatable(instance, {__index = MethodCallTree})
end

-- RETURNS an IR statement, one or more variable names
function MethodCallTree:compileExpr()
	error "TODO"
end

--------------------------------------------------------------------------------

-- Represents a usage of a type.
local TypeTree = {}

function TypeTree.new(ast, ticket)
	local instance = {_ast = ast, _ticket = ticket}

	return setmetatable(instance, {__index = TypeTree})
end

--------------------------------------------------------------------------------

return {
	MethodCallTree = MethodCallTree,
	TypeTree = TypeTree,
}
