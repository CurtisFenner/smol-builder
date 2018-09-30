local Report = {}

function Report.OBJECT_DEFINED_TWICE(p)
	assertis(p, recordType {
		fullName = "string",
		firstLocation = "Location",
		secondLocation = "Location",
	})

	quit(
		"A definition for `",
		p.fullName,
		"` was already made ",
		p.firstLocation,
		"\nHowever, you are attempting to redefine it ",
		p.secondLocation
	)
end

function Report.PACKAGE_IMPORTED_TWICE(p)
	quit(
		"The package `", p.packageName, "` was already imported ",
		p.firstLocation,
		"\nHowever, you try to import it again ",
		p.secondLocation
)
end

function Report.SELF_OUTSIDE_INTERFACE(p)
	quit(
		"A `#Self` type can only be used in an interface, but is mentioned ",
		p.location
	)
end

function Report.WRONG_ARITY(p)
	assertis(p.definitionLocation, "Location")

	quit(
		"The definition `",
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

function Report.INTERFACE_USED_AS_TYPE(p)
	quit(
		"The definition for `",
		p.interface,
		"` is an interface, so you cannot use it as a type as you are ",
		p.location
	)
end

function Report.UNKNOWN_DEFINITION_IMPORTED(p)
	quit(
		"A definition called `",
		p.name,
		"` has not been defined.",
		"\nHowever, you are trying to import it ",
		p.location
	)
end

function Report.NO_SUCH_OBJECT(p)
	quit(
		"No object called `",
		p.name,
		"` has been defined.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.NO_SUCH_PACKAGE(p)
	quit(
		"A package called `",
		p.package,
		"` has not been defined.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.UNKNOWN_PACKAGE_USED(p)
	quit(
		"The package `",
		p.package,
		"` has not been imported.",
		"\nHowever, you are trying to use it ",
		p.location
	)
end

function Report.UNKNOWN_DEFINITION_USED(p)
	quit(
		"No definition called `" .. p.name .. "` has been defined in scope.",
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

function Report.MEMBER_DEFINED_TWICE(p)
	quit(
		"The member `" .. p.name .. "` was already defined ",
		p.firstLocation,
		"\nHowever, you are attempting to redefine it ",
		p.secondLocation
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

function Report.INTERFACE_REQUIRES_MEMBER(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement the interface",
		" `",
		p.interface,
		"` ",
		p.implementsLocation,
		"\nHowever, `" .. p.class .. "` does not implement the required",
		" member `" .. p.memberName .. "` which is required by the interface `",
		p.interface,
		"` ",
		p.interfaceLocation
	)
end

function Report.INTERFACE_MODIFIER_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"` ",
		p.claimLocation,
		"\nThe interface `",
		p.interface,
		"` defines a ",
		p.interfaceModifier,
		" member called `",
		p.memberName,
		"` ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.memberName,
		"` to be a ",
		p.classModifier,
		" ",
		p.classLocation
	)
end

function Report.INTERFACE_BANG_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface `",
		p.interface,
		"` ",
		p.claimLocation,
		"\nHowever, `" .. p.class .. "` implements the ",
		p.modifier,
		"`" .. p.memberName .. "` ",
		not p.expectedBang and "with" or "without",
		" an action `!`, which disagrees with the interface."
	)
end

function Report.INTERFACE_COUNT_MISMATCH(p)
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
		p.modifier,
		" called `",
		p.memberName,
		"` with ",
		p.interfaceCount,
		" " .. p.thing .. "(s) ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.memberName,
		"` with ",
		p.classCount,
		" " .. p.thing .. "(s) ",
		p.classLocation
	)
end

function Report.INTERFACE_TYPE_MISMATCH(p)
	quit(
		"The class/union `",
		p.class,
		"` claims to implement interface",
		" `",
		p.interface,
		"` ",
		p.claimLocation,
		"\nThe interface `",
		p.interface,
		"` defines a ",
		p.modifier,
		" called `",
		p.memberName,
		"` with the ",
		string.ordinal(p.index),
		" " .. p.thing .. " of type `",
		p.interfaceType,
		"` ",
		p.interfaceLocation,
		"\nHowever, `",
		p.class,
		"` defines `",
		p.memberName,
		"` with the ",
		string.ordinal(p.index),
		" " .. p.thing .." of type `",
		p.classType,
		"` ",
		p.classLocation
	)
end

function Report.UNREACHABLE_STATEMENT(p)
	quit(
		"Statements following a `return` can never be reached.",
		"\nThis makes an unreachable point in your code ",
		p.location
	)
end

function Report.TYPE_MISMATCH(p)
	quit(
		"The " .. p.purpose,
		" expects a value of type `",
		p.expected,
		"` as defined ",
		p.expectedLocation,
		"\nHowever, the " .. p.purpose,
		" was `",
		p.given,
		"` ",
		p.givenLocation
	)
end

function Report.EVALUATION_ORDER(p)
	quit(
		"The evaluation order of an expressions.",
		"\nThe first is ",
		p.first,
		"\nThe second is ",
		p.second
	)
end

function Report.NO_SUCH_MEMBER(p)
	quit(
		"The type `",
		p.container,
		"` does not have a " .. p.memberType .. " called `",
		p.name,
		"`",
		"\nHowever, you try to use `",
		p.name,
		"` ",
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

function Report.NO_SUCH_VARIABLE(p)
	quit("There is no variable named `", p.name, "` in scope ", p.location)
end

function Report.NEW_IN_INTERFACE(p)
	quit(
		"Interfaces do not have constructors.\n",
		"However, you try to use `new()` ",
		p.location
	)
end

function Report.DUPLICATE_INITIALIZATION(p)
	if p.first == p.second then
		quit("The ", p.purpose, " is initialized twice ", p.location)
	end
	quit(
		"The ",
		p.purpose,
		" is initialized twice. The first initialization is ",
		p.first,
		"\nThe second initialization is ",
		p.second
	)
end

function Report.MISSING_INITIALIZATION(p)
	quit(
		"The ",
		p.purpose,
		" is never initialized ",
		p.location
	)
end

function Report.WRONG_VALUE_COUNT(p)
	quit(
		"Expected ",
		p.expectedCount,
		" ",
		p.purpose,
		" but got ",
		p.givenCount,
		" ",
		p.givenLocation
	)
end

function Report.TYPE_MUST_BE(p)
	quit(
		"The type `",
		p.givenType,
		"` cannot be used as ",
		p.purpose,
		" as it is ",
		p.givenLocation
	)
end

function Report.THIS_USED_OUTSIDE_METHOD(p)
	quit("You try to use `this` in a non-method function ", p.location)
end


function Report.CONFLICTING_INTERFACES(p)
	quit(
		"The call `",
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

--------------------------------------------------------------------------------

function Report.FUNCTION_DOESNT_RETURN(p)
	assertis(p, recordType {
		modifier = "string",
		name = "string",
		returns = "string",
		location = "Location",
	})

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

function Report.NO_MAIN(p)
	quit("There is no class `" .. p.name .. "`.")
end

function Report.NO_MAIN_STATIC(p)
	quit("The class `" .. p.name .. "` is missing a `static main!()")
end

function Report.MAIN_MUST_NOT_BE_GENERIC(p)
	quit(
		"The class `",
		p.name,
		"` is generic, so it cannot be used as",
		" a main class."
	)
end

function Report.UNKNOWN_OPERATOR_USED(p)
	quit(
		"You try to use the undefined operator `",
		p.operator,
		"` ",
		p.location
	)
end

function Report.VARIANT_USED_TWICE(p)
	assertis(p, recordType {
		variant = "string",
		firstLocation = "Location",
		secondLocation = "Location",
	})

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

function Report.CANNOT_USE_RETURN(p)
	quit("The `return` expression cannot be used ", p.location)
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
		"The `",
		p.quantifier,
		"` quantifier can only be used in ",
		"`requires`, `ensures,` `assert` conditions.",
		"\nHowever, you use `",
		p.quantifier,
		"` ",
		p.location
	)
end

function Report.RECURSIVE_REQUIRES(p)
	quit(
		"The preconditions of `",
		p.func,
		"` are recursive ",
		p.location
	)
end

return Report
