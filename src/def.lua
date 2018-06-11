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
	compounds = listType(recordType {
		tag = choiceType(constantType("union-definition"), constantType("class-definition")),
		_fieldMap = mapType("string", recordType {
			name = "string",
			type = "TypeKind",
		}),
		constraintArguments = listType(recordType {
			name = "string",
			concerningIndex = "integer",
			constraintListIndex = "integer",
			constraint = "ConstraintKind",
		}),
		fullName = "string",
	}),
	interfaces = listType "InterfaceIR",
	functions = listType "FunctionIR",
	main = choiceType("string", constantType(false)),
})

REGISTER_TYPE("InterfaceIR", recordType {
	tag = constantType "interface-definition",
	fullName = "string",
	_functionMap = mapType("string", recordType {
		signature = "Signature",
	}),
	constraintArguments = listType(recordType {
		name = "string",
		concerningIndex = "integer",
		constraintListIndex = "integer",
		constraint = "ConstraintKind",
	}),
})

REGISTER_TYPE("FunctionIR", recordType {
	namespace = "string",
	name = "string",
	body = choiceType(constantType(false), "StatementIR"),
	signature = "Signature",
})

REGISTER_TYPE("Signature", recordType {
	-- TODO: Do we need memberName?
	memberName = "string",
	longName = "string",

	parameters = listType "VariableIR",
	returnTypes = listType "TypeKind",
	modifier = choiceType(constantType "static", constantType "method"),
	foreign = "boolean",
	bang = "boolean",
	requiresASTs = listType "ASTExpression",
	ensuresASTs = listType "ASTExpression",
	logic = choiceType(
		constantType(false),
		mapType("boolean", listType(listType(choiceType("boolean", constantType "*"))))
	),
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
	"SequenceSt",
	"BooleanLoadSt",
	"FieldSt",
	"DynamicCallSt",
	"StaticCallSt",
	"IsASt",
	"LocalSt",
	"MatchSt",
	"NewClassSt",
	"NewUnionSt",
	"IntLoadSt",
	"ReturnSt",
	"IfSt",
	"StringLoadSt",
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
	variable = "VariableIR",
})

EXTEND_TYPE("VerifySt", "AbstractStatementIR", recordType {
	tag = constantType "verify",
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

EXTEND_TYPE("SequenceSt", "AbstractStatementIR", recordType {
	tag = constantType "sequence",
	statements = listType "StatementIR",
})

EXTEND_TYPE("StringLoadSt", "AbstractStatementIR", recordType {
	tag = constantType "string-load",
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
	tag = constantType "int-load",
	number = "number",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NewClassSt", "AbstractStatementIR", recordType {
	tag = constantType "new-class",
	fields = mapType("string", "VariableIR"),
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("NewUnionSt", "AbstractStatementIR", recordType {
	tag = constantType "new-union",
	field = "string",
	value = "VariableIR",
	destination = "VariableIR",
	returns = constantType "no",
})

EXTEND_TYPE("StaticCallSt", "AbstractStatementIR", recordType {
	tag = constantType "static-call",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	constraintArguments = listType "VTableIR",
	returns = constantType "no",
	signature = "Signature",
})

EXTEND_TYPE("DynamicCallSt", "AbstractStatementIR", recordType {
	tag = constantType "dynamic-call",
	constraint = "VTableIR",
	arguments = listType "VariableIR",
	destinations = listType "VariableIR",
	returns = constantType "no",
	signature = "Signature",
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
})

EXTEND_TYPE("MatchSt", "AbstractStatementIR", recordType {
	tag = constantType "match",
	base = "VariableIR",
	cases = listType(recordType {
		variable = "VariableIR",
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
	quantified = "TypeKind",

	-- VariableIR => StatementIR, VariableIR
	instantiate = "function",
	location = "Location",
})

--------------------------------------------------------------------------------

REGISTER_TYPE("VariableIR", recordType {
	name = "string",
	type = "TypeKind",
})

REGISTER_TYPE("VTableIR", choiceType(
	recordType {
		tag = constantType "parameter-vtable",
		interface = "ConstraintKind",
		name = "string",
	},
	recordType {
		tag = constantType "concrete-vtable",
		interface = "ConstraintKind",
		concrete = "TypeKind",
		arguments = listType "VTableIR",
	}
))

--------------------------------------------------------------------------------

REGISTER_TYPE("Kind", choiceType("TypeKind", "ConstraintKind"))

REGISTER_TYPE("TypeKind", choiceType(
	"CompoundTypeKind",
	"SelfTypeKind",
	"GenericTypeKind",
	"KeywordTypeKind"
))

REGISTER_TYPE("CompoundTypeKind", recordType {
	tag = constantType "compound-type",
	role = constantType "type",
	packageName = "string",
	definitionName = "string",
	arguments = listType("TypeKind"),
})

REGISTER_TYPE("SelfTypeKind", recordType {
	tag = constantType "self-type",
	role = constantType "type",
})

REGISTER_TYPE("GenericTypeKind", recordType {
	tag = constantType "generic-type",
	role = constantType "type",
	name = "string",
})

REGISTER_TYPE("KeywordTypeKind", recordType {
	tag = constantType "keyword-type",
	role = constantType "type",
	name = "string",
})

REGISTER_TYPE("ConstraintKind", choiceType(
	"InterfaceConstraintKind",
	"KeywordConstraintKind"
))

REGISTER_TYPE("InterfaceConstraintKind", recordType {
	tag = constantType "interface-constraint",
	role = constantType "constraint",
	packageName = "string",
	definitionName = "string",
	arguments = listType("TypeKind"),
})

REGISTER_TYPE("KeywordConstraintKind", recordType {
	tag = constantType "keyword-constraint",
	role = constantType "constraint",
	name = "string",
})
