REGISTER_TYPE("Spot", recordType {
	line = "integer",
	column = "integer",
	index = "integer",
})

REGISTER_TYPE("Location", recordType {
	file = recordType {
		filename = "string",
		lines = listType "string",
	},
	from = "Spot",
	to = "Spot",
})

REGISTER_TYPE("Token", recordType {
	location = "Location",
	tag = "string",
	lexeme = "string",
})

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

REGISTER_TYPE("TypePlain", choiceType(
	recordType {
		tag = constantType "type-keyword-plain",
		name = "string",
	},
	recordType {
		tag = constantType "type-self-plain",
	},
	recordType {
		tag = constantType "type-generic-plain",
		name = "string",
	},
	recordType {
		tag = constantType "type-object-plain",
		object = recordType {
			package = "string",
			object = "string",
		},
		arguments = listType "TypePlain",
	}
))

REGISTER_TYPE("maybe", choiceType(
	constantType "yes",
	constantType "no",
	constantType "maybe"
))

REGISTER_TYPE("Statement", choiceType(
	recordType {
		tag = constantType "sequence-statement",
		statements = listType "Statement",
		exits = "maybe",
	},
	recordType {
		tag = constantType "todo-statement",
	}
))
