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
