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
