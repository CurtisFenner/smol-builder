local Report = {}

function Report.TYPE_DEFINED_TWICE(first, second)
	assertis(first.name, "string")
	assertis(second.name, "string")
	assert(first.name == second.name)

	local name = first.name

	quit(
		"The type `",
		name,
		"` was already defined ",
		first.location,
		"\nHowever, you are attempting to redefine it ",
		second.location
	)
end

function Report.GENERIC_DEFINED_TWICE(p)
	quit(
		"The generic variable `#",
		p.name,
		"` was already defined ",
		p.firstLocation,
		"\nHowever, you are attempting to redefine it ",
		p.secondLocation
	)
end

function Report.MEMBER_DEFINED_TWICE(p)
	quit(
		"The member `" .. p.name .. "` was already defined ",
		p.firstLocation,
		"\nHowever, you are attempting to redefine it ",
		p.secondLocation
	)
end

function Report.TYPE_BROUGHT_INTO_SCOPE_TWICE(p)
	quit(
		"The type `",
		p.name,
		"` was first brought into scope ",
		p.firstLocation,
		"\nHowever, you try to bring the name `",
		p.name,
		"` into scope again ",
		p.secondLocation
	)
end

function Report.UNKNOWN_TYPE_IMPORTED(p)
	p = freeze(p)
	quit(
		"A type called `",
		p.name,
		"` has not been defined.",
		"\nHowever, you are trying to import it ",
		p.location
	)
end

function Report.UNKNOWN_PACKAGE_USED(p)
	p = freeze(p)
	quit(
		"The package `",
		p.package,
		"` has not been imported.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.UNKNOWN_GENERIC_USED(p)
	quit(
		"A generic variable called `#" .. p.name .. "` has not been defined.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.UNKNOWN_TYPE_USED(p)
	quit(
		"No type called `" .. p.name .. "` has been defined.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.UNKNOWN_LOCAL_TYPE_USED(p)
	quit(
		"There is no type called `" .. p.name .. "` in scope.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.INTERFACE_REQUIRES_MEMBER(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"` ",
		p.implementsLocation,
		"\nHowever, `" .. p.class .. "` does not implement the required",
		" member `" .. p.memberName .. "` which is required by the interface `",
		p.interface,
		"` ",
		p.memberLocation
	)
end

function Report.WRONG_ARITY(p)
	assertis(p.definitionLocation, "Location")

	quit(
		"The type `",
		p.name,
		"` was defined ",
		p.definitionLocation,
		"to take exactly ",
		p.expectedArity,
		" type arguments.",
		"\nHowever, you provide ",
		p.givenArity,
		" ",
		p.location
	)
end

function Report.INTERFACE_REQUIRES_MODIFIER(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"`.",
		"\nThe interface `",
		p.interface,
		"` defines a ",
		p.interfaceModifier,
		" member called `",
		p.name,
		"` ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.name,
		"` to be a ",
		p.classModifier,
		" ",
		p.classLocation
	)
end

function Report.INTERFACE_PARAMETER_COUNT_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"`.",
		"\nThe interface `",
		p.interface,
		"` defines a member called `",
		p.name,
		"` with ",
		p.interfaceCount,
		" parameter(s) ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.name,
		"` with ",
		p.classCount,
		" parameter(s)",
		p.classLocation
	)
end

function Report.INTERFACE_PARAMETER_TYPE_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"`.",
		"\nThe interface `",
		p.interface,
		"` defines a member called `",
		p.name,
		"` with the ",
		string.ordinal(p.index),
		" parameter of type `",
		p.interfaceType,
		"` ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.name,
		"` with the ",
		string.ordinal(p.index),
		" parameter of type `",
		p.classType,
		"` ",
		p.classLocation
	)
end

function Report.INTERFACE_RETURN_COUNT_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"`.",
		"\nThe interface `",
		p.interface,
		"` defines a member called `",
		p.member,
		"` with ",
		p.interfaceCount,
		" return value(s) ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.member,
		"` with ",
		p.classCount,
		" return values(s) ",
		p.classLocation
	)
end

function Report.INTERFACE_RETURN_TYPE_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"`.",
		"\nThe interface `",
		p.interface,
		"` defines a member called `",
		p.member,
		"` with the ",
		string.ordinal(p.index),
		" return-value of type `",
		p.interfaceType,
		"` ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.member,
		"` with the ",
		string.ordinal(p.index),
		" return-value of type `",
		p.classType,
		"` ",
		p.classLocation
	)
end

function Report.CONSTRAINTS_MUST_BE_INTERFACES(p)
	quit(
		"Constraints must be interfaces.",
		"\nHowever, the ",
		p.is,
		" `",
		p.typeShown,
		"` is used as a constraint ",
		p.location
	)
end

function Report.TYPE_MUST_IMPLEMENT_CONSTRAINT(p)
	quit(
		"The type `",
		p.container,
		"` requires its ",
		string.ordinal(p.nth),
		" type-parameter to implement ",
		p.constraint,
		" ",
		p.cause,
		"\nHowever, the type `",
		p.type,
		"` does not implement the interface `",
		p.constraint,
		"` ",
		p.location
	)
end

function Report.VARIABLE_DEFINITION_COUNT_MISMATCH(p)
	quit(
		p.valueCount,
		" value(s) are provided but ",
		p.variableCount,
		" variable(s) are defined ",
		p.location
	)
end

function Report.VARIABLE_DEFINED_TWICE(p)
	quit(
		"The variable `",
		p.name,
		"` is first defined ",
		p.first,
		"While it is still in scope, you attempt to define another variable ",
		"with the same name `",
		p.name,
		"` ",
		p.second
	)
end

function Report.INTERFACE_USED_AS_VALUE(p)
	quit(
		"The definition for `",
		p.interface,
		"` is an interface,",
		" so you cannot use it as the type of a variable or value as you are ",
		p.location
	)
end

function Report.WRONG_VALUE_COUNT(p)
	quit(
		"The ",
		p.purpose,
		" needs ",
		p.expectedCount,
		" value(s),",
		" but was given ",
		p.givenCount,
		" ",
		p.location
	)
end

function Report.TYPES_DONT_MATCH(p)
	assertis(p.expectedType, "string")
	assertis(p.givenType, "string")
	assertis(p.location, "Location")
	assertis(p.purpose, "string")
	quit(
		"The ",
		p.purpose,
		" expects `",
		p.expectedType,
		"` as defined ",
		p.expectedLocation,
		"\nHowever, you pass a `",
		p.givenType,
		"` ",
		p.location
	)
end

function Report.EXPECTED_DIFFERENT_TYPE(p)
	assertis(p.expectedType, "string")
	assertis(p.givenType, "string")
	assertis(p.location, "Location")
	assertis(p.purpose, "string")
	quit(
		"The ",
		p.purpose,
		" expects `",
		p.expectedType,
		"` but was given `",
		p.givenType,
		"` ",
		p.location
	)
end

function Report.EQ_TYPE_MISMATCH(p)
	quit(
		"The operands of `==` must be of the same type.",
		"\nHowever, the left operand to `==` is of type `",
		p.leftType,
		"` while the right operand is of type `",
		p.rightType,
		"` ",
		p.location
	)
end

function Report.NO_SUCH_FIELD(p)
	quit(
		"The type `",
		p.container,
		"` does not have a field called `",
		p.name,
		"`",
		"\nHowever, you try to access `",
		p.name,
		"` ",
		p.location
	)
end

function Report.NO_SUCH_VARIANT(p)
	quit(
		"The type `",
		p.container,
		"` does not have a variant called `",
		p.name,
		"`",
		"\nHowever, you try to access variant `",
		p.name,
		"` ",
		p.location
	)
end

function Report.NO_SUCH_VARIABLE(p)
	quit("There is no variable named `", p.name, "` in scope ", p.location)
end

function Report.NO_SUCH_METHOD(p)
	quit(
		"The type `",
		p.type,
		"` does not have a ",
		p.modifier,
		" called `",
		p.name,
		"`.",
		"\nAvailable members include ",
		"\n\t",
		table.concat(p.alternatives, ", "),
		"\nHowever, you try to call `",
		p.type,
		".",
		p.name,
		"` ",
		p.location
	)
end

function Report.CONFLICTING_INTERFACES(p)
	quit(
		"The method `",
		p.method,
		"` is ambiguous ",
		p.location,
		"because `",
		p.method,
		"` is defined in both `",
		p.interfaceOne,
		"` and `",
		p.interfaceTwo,
		"`"
	)
end

function Report.TYPE_MUST_BE_CLASS(p)
	assertis(p.purpose, "string")
	assertis(p.givenType, "string")
	assertis(p.location, "Location")

	quit(
		"The ",
		p.purpose,
		" must be a class instance. However, it is a ",
		p.givenType,
		" ",
		p.location
	)
end

function Report.TYPE_MUST_BE_UNION(p)
	quit(
		"The ",
		p.purpose,
		" must be a union instance. However, you try to use a ",
		"`",
		p.givenType,
		"` ",
		p.location
	)
end

function Report.MISSING_VALUE(p)
	quit(
		"The ",
		p.purpose,
		" requires a value for field `",
		p.name,
		"`.",
		"\nHowever, it is missing ",
		p.location
	)
end

function Report.FUNCTION_DOESNT_RETURN(p)
	quit(
		"The ",
		p.modifier,
		" ",
		p.name,
		" does not always `return` ",
		p.returns,
		" as it says it does ",
		p.location
	)
end

function Report.BANG_MISMATCH(p)
	assert(p.given ~= p.expected)

	local expects
	local given
	if p.expected then
		expects = "a `!` " .. p.modifier .. " action"
		given = "without a `!`"
	else
		expects = "a pure (no `!`) " .. p.modifier
		given = "with a `!`"
	end

	quit(
		"The ",
		p.modifier,
		" ",
		p.fullName,
		" is defined to be ",
		expects,
		" ",
		p.signatureLocation,
		"\nHowever, you try to call it ",
		given,
		" ",
		p.location
	)
end

function Report.BANG_NOT_ALLOWED(p)
	quit(
		"A `!` action is not allowed in ",
		p.context,
		".",
		"\nHowever, you try to invoke one ",
		p.location
	)
end

function Report.NO_MAIN(p)
	quit("There is no class `" .. p.name .. "`.")
end

function Report.NO_MAIN_STATIC(p)
	quit("The class `" .. p.name .. "` is missing a `static main!()")
end

function Report.MAIN_MUST_NOT_BE_GENERIC(p)
	quit("The class `" .. p.name .. "` is generic, so it cannot be used as", " a main class.")
end

function Report.UNKNOWN_OPERATOR_USED(p)
	quit("You try to use the undefined operator `", p.operator, "` ", p.location)
end

function Report.THIS_USED_OUTSIDE_METHOD(p)
	quit("You try to use `this` in a non-method function ", p.location)
end

function Report.VARIANT_USED_TWICE(p)
	quit(
		"You use the variant `case ",
		p.variant,
		"` twice in a single match;",
		"\nYou use `case ",
		p.variant,
		"` first ",
		p.firstLocation,
		"\nYou use `case ",
		p.variant,
		"` a second time ",
		p.secondLocation
	)
end

function Report.INEXHAUSTIVE_MATCH(p)
	local clauses = {}
	for _, missing in ipairs(p.missingCases) do
		table.insert(clauses, "\t`case " .. missing .. "`")
	end
	quit(
		"In a match statement on a `",
		p.baseType,
		"` you are missing case clauses:\n",
		table.concat(clauses, "`\n"),
		"\n",
		p.location
	)
end

function Report.RETURN_USED_IN_IMPLEMENTATION(p)
	quit(
		"The `return` keyword can only be used as an expression in",
		" `ensures` clauses.",
		"\nHowever, you use `return` ",
		p.location
	)
end

function Report.QUANTIFIER_USED_IN_IMPLEMENTATION(p)
	quit(
		"The `", p.quantifier, "` quantifier can only be used in ",
		"`requires`, `ensures,` `assert` conditions.",
		"\nHowever, you use `", p.quantifier, "` ",
		p.location
	)
end

function Report.EVALUATION_ORDER(p)
	quit("The evaluation order of an expression is not defined ", p.location)
end

return Report
