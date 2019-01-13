-- An intermediate language for compiling Smol to, combined with an interpreter.

REGISTER_TYPE("IR-identifier", intersectType("string", predicateType(function(x)
	return x:match "^[a-zA-Z][a-zA-Z0-9_]*$"
end)))

REGISTER_TYPE("IR-struct", recordType {
	fields = mapType("IR-identifier", "IR-type"),
})

REGISTER_TYPE("IR-function", recordType {
	arguments = listType(recordType {
		name = "IR-identifier",
		type = "IR-type",
	}),
	body = "IR-block",
})

REGISTER_TYPE("IR-Program", recordType {
	structs = mapType("IR-identifier", "IR-struct"),
	unions = mapType("IR-identifier", "IR-struct"),
	functions = mapType("IR-identifier", "IR-function"),
	main = "IR-identifier",
})

REGISTER_TYPE("IR-block", recordType {
	tag = constantType "block-ir",
	statements = listType "IR-Statement",
	returns = constantType "no",
})

REGISTER_TYPE("IR-type", choiceType(
	recordType {
		tag = constantType "ir-struct-type",
		name = "IR-identifier",
	},
	recordType {
		tag = constantType "ir-union-type",
		name = "IR-identifier",
	}
))

REGISTER_TYPE("IR-Statement", choiceType(
	"IR-block",
	recordType {
		tag = constantType "local-ir",

		-- Introduce the given name into the current scope.
		name = "IR-identifier",

		-- The type of the introduced variable.
		type = "IR-type",
	},
	recordType {
		tag = constantType "static-call-ir",

		-- The function name to statically dispatch to.
		procedure = "IR-identifier",

		-- The arguments to invoke the procedure with.
		arguments = "IR-identifier",

		-- The return-destinations of the function.
		destinations = listType "IR-identifier",
	},
	recordType {
		tag = constantType "allocate-struct-ir",

		-- The struct name to allocate.
		struct = "IR-identifier",

		-- A mapping of field name => variable holding initial value.
		fields = mapType("IR-identifier", "IR-identifier"),

		-- The destination to allocate into.
		destination = "IR-identifier",
	},
	recordType {tag = constantType}
))

--------------------------------------------------------------------------------

local function interpreter(program)
	
end
