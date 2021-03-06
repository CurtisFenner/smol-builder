# The Smol Programming Language

This manual describes the current state of the Smol programming language.
The language and the compiler are not yet stable; all details are still subject
to change.

Smol is a statically-typed functional programming language that is equipped with
a static verification framework for checking functional correctness
properties at compile time.

## Program File Structure

A Smol program is made of one or more source files. These source files
conventionally have a `.smol` extension.

Each source file begins with a `package` declaration. A package is a word
made of ASCII letters and numbers, beginning with a
lowercase letter.
By convention, the package should reflect the source file's path and name;
however, this is unchecked, and two source files may have the same package name.

The `core` package is reserved for standard definitions. Programmers should not
write source files that declare themselves to be in `package core` because they
could conflict with internal or future names.

## Source File Syntax

Source files must be encoded in an ASCII-compatible encoding (such as UTF-8).
Non-ASCII bytes may appear only in comments and string literals.

Source files are interpretted as a sequence of tokens. A source file can be
split into tokens using simple rules on the ASCII bytes in the file.

### Tokens

The following words are reserved keywords:
* `case`
* `class`
* `do`
* `foreign`
* `if`
* `else`
* `elseif`
* `import`
* `interface`
* `is`
* `match`
* `method`
* `new`
* `package`
* `return`
* `static`
* `union`
* `var`
* `assert`
* `ensures`
* `forall`
* `requires`
* `when`
* `false`
* `this`
* `true`
* `unit`

The following words are reserved type keywords:

* `Boolean`
* `Int`
* `Never` Reserved, but currently unused.
* `String`
* `Unit`
* `#Self`

Smol source files are made of sequences of the following tokens:

* `[a-z][A-Za-z0-9]*` are variable, package, and field identifiers, except for
    the reserved keywords above
* `[A-Z][A-Za-z0-9]*` are type identifiers, except for the reserved type
    keywords above
* `#[A-Z][A-Za-z0-9]*` are type parameter identifiers, except for the reserved
    `#Self` keyword
* `[\n\r\t\v ]+` are whitespace, which are ignored except for separating tokens
* `//[^\n]*` are comments, which continue to the end of the line and are ignored
* `[0-9]+` are integer literals
* `,`, `;`, `|`, `!`, `.`, `(`, `)`, `[`, `]`, `{`, `}` are all one-character
    tokens
* `"` begins string literals. String literals continue until an unescaped `"` is
    reached. `\` escapes the next character, with `\0`, `\n`, `\r`, `\t`, `\\`,
    `\"`.
    A string literal cannot contain a literal newline (byte 10) or carriage
    return (byte 13).
* `[<=>%/*+-]+` are operators, excepting those containing `//`, which begins a
    comment as mentioned above

### Grammar
The grammar of Smol follows, with the following conventions:

* `lowercase` names are classes of tokens
* `Uppercase` names are abstract expressions
* `"quoted"` terms are literal tokens
* `x?` means 0 or 1 occurence of `x`
* `x*` means 0 or more occurences of `x`
* `x+` means 1 or more occurences of `x`
* `x,+` means 1 or more occurences of `x` separated by a literal `","`
* `x,*` means 0 or more occurences of `x` separated by a literal `","`

> IMPLEMENTATION NOTE:
> The grammar is simple to parse, and unambiguous. A PEG parser is suitable for
> parsing Smol.

	Source :=
		PackageDef
		Import*
		Definition+
	
	PackageDef :=
		"package" package_iden ";"
	
	Import :=
		| "import" package_iden ";"
		| "import" package_iden ":" type_iden ";"
	
	Definition :=
		| ClassDefinition
		| UnionDefinition
		| InterfaceDefinition
	
	ClassDefinition :=
		"foreign"?
		"class"
		type_iden
		Generics?
		Implements?
		"{"
		Field*
		FunctionDef*
		"}"
	
	UnionDefinition :=
		"union"
		type_iden
		Generics?
		Implements?
		Field*
		FunctionDef*
		"}"

	Implements :=
		"implements" Type,+

	Field :=
		"var" Variable ";"

	InterfaceDefinition :=
		"interface"
		type_iden
		Generics?
		"{"
		(Signature ";")*
		"}"

	Generics :=
		"["
		typeparam_iden,+
		("|" (typeparam_iden "is" Type),+)?
		"]"

	Type :=
		| "Boolean"
		| "Int"
		| "Never"
		| "String"
		| "Unit"
		| "#Self"
		| typeparam_iden
		| (package_iden ":")? type_iden ("[" Type,+ "]")?

	Signature :=
		"foreign"?
		("method" | "static")
		method_iden
		"!"?
		"("
		Variable,*
		")"
		Type,
		Requires*
		Ensures*
	
	Requires :=
		"requires" Expression ("when" Expression,+)?
	
	Ensures :=
		"ensures" Expression ("when" Expression,+)?

	Variable :=
		variable_iden Type

	FunctionDef :=
		Signature Block
	
	Block :=
		"{" Statement* "}"
	
	Statement :=
		| "var" Variable, "=" Expression ";"
		| "do" Expression ";"
		| IfSt
		| MatchSt
		| "assertion" Expression ";"
		| "return" Expression ";"
		| variable_iden,+ "=" Expression ";"

	IfSt :=
		"if" Expression Block
		("elseif" Expression Block)*
		("else" Block)?

	MatchSt :=
		"match"
		Expression
		"{"
		("case" variable_iden field_iden Block)+
		"}"

	Expression :=
		| ExpressionBase (operator ExpressionBase)? ("isa" variable_iden)?
		// "when" has higher precedence here than in ensures/requires/asserts
		| "forall" "(" Variable ")" Expression ("if" Expression,+)?

	ExpressionBase :=
		| "(" Expression ")"
		| variable_iden
		| ExpressionBase "." field_iden
		| ExpressionBase "." method_iden "!"? "(" Expression,* ")"
		| "this"
		| "true"
		| "false"
		| int_literal
		| string_literal
		| "return"
		| Type "." method_iden "!"? "(" Expression,* ")"
		| "new" "(" (field_iden "=" Expression),* ")"

## Types and Values

Smol is statically typed. There are several built-in types:

* `Unit`, which has one value, `unit`
* `Boolean`, which has two values, `true` and `false`
* `Int`, which has values corresponding to the integers:
  ..., `-3`, `-2`, `-1`, `0`, `1`, `2`, `3`, ...
* `String` which represents sequences of bytes such as `""` and `"Smol"`

There is no "any" type in Smol that encompasses all values
(like Java's `Object`).
There is no value in Smol that is of any type (like Java's `null`).

Smol does not have inheritance or subtyping.

In addition to the four built-in types, Smol has two kinds of type definitions:
`class` and `union`.

### Classes

`class` types correspond to records (product types) and have zero or more
*fields*.
Each field is given a name and a type. Each instance of a `class` type has a
value for each field. Class instances are created with `new`-expressions by
providing assigning a value to each field.

Smol has no special "constructor" members; `new`-expressions can be invoked in
any function in the class.

	class Pair {
		var myInt Int;
		var myString String;
		
		static make(n Int, s String) Pair {
			return new(myString = s, myInt = n);
		}

		method getInt() Int {
			return this.myInt;
		}
	}

### Unions

`union` types correspond to enums (sum types) and have one or more *variants*.
Each variant is given a name and a type.
Each instance of a `union` type has a *tag* specifying which variant the
instance is, and a value of that variant's type.

Variants are distinguished by their tag and not their type: a `union` may have
multiple variants with the same type. Union instances are created with `new`
by providing a value for exactly one variant.

	union Either {
		var success String;
		var errorCode Int;

		static makeSuccess() Either {
			return new(success = "Yay!");
		}

		static makeFailure() Either {
			return new(errorCode = 418);
		}

		method isSuccess() Boolean {
			return this is success;
		}
	}

### Parameterized Types (Generics)

`class` and `union` types may be parameterized by type parameters. Type
parameter tokens begin with `#`; for example, `#Foo` or `#T`.

Type parameters can be used anywhere that other types can be used,
including as function parameter types, function return types, field types, and
in static function invocations.

	class Pair[#Left, #Right] {
		var left #Left;
		var right #Right;

		static make(left #Left, right #Right) Pair[#Left, #Right] {
			return new(left = left, right = right);
		}

		method getLeft() #Left {
			return this.left;
		}

		method getRight() #Right {
			return this.right;
		}
	}

Parameterized types are allowed to be *recursive*:

	class Foo[#T] {
		var field core:Option[Foo[Foo[#T]]];
	}

> IMPLEMENTATION NOTE:
> As a result of the above kind of recursion, static template instantiation as
> in C++ is *not* sufficient to implement Smol generics. Instead, a function
> v-table must be used, in at least some circumstances.

### Constraints on Type Parameters: Interfaces

A type may `implement` an `interface`. An `interface` defines required
member functions for its implementers. These members can be both `method`
functions and `static` functions (which can be used even in the absence of an
instance of the type).

Interfaces may use the `#Self` type to refer to the implementer's type.
`#Self` corresponds to the type of `this` in `method` functions.

	interface Field {
		method sum(other #Self) #Self;
		method product(other #Self) #Self;

		// The additive identity
		static zero() #Self;

		// The multiplicative identity
		static one() #Self;

		// The additive inverse
		method negative() #Self;

		// The multiplicative inverse
		method reciprocal() #Self;
	}

	// A two-dimensional vector over an arbitrary field
	// #F will have all of the functions of Field available because
	// `#F is Field`.
	class V2[#F | #F is Field] {
		var x #F;
		var y #F;

		static make(x #F, y #F) {
			return new(x = x, y = y);
		}

		static zero() V2[#F] {
			// We can invoke the static members of a type parameter
			return new(
				x = #F.zero(),
				y = #F.zero()
			);
		}

		method sum(other V2[#F]) V2[#F] {
			// "+" here is another name for "sum"
			return new(
				x = this.x + other.x,
				y = this.y + other.y
			);
		}

		method scale(c #F) V2[#F] {
			return new(
				x = c * this.x,
				y = c * this.y,
				z = c * this.z
			);
		}

		method dot(other V2[#F]) #F {
			return (this.x * other.x) + (this.y * other.y);
		}
	}

Interfaces are *not* types; instead, they are used only to *constrain* type
parameters, allowing algorithms and data-structures that require something of
the types they contain or use.

### Values and Identity

All values in Smol are **immutable**. In particular, the values associated with
the fields of a `class` or `union` cannot change.

Instead, you can create a new value which has been modified from the previous
value.

In particular, this means "copying" a data structure in its entireity is never
necessary: if the fields of two class or union instances of the same type are
the same, then the values are the same.
Thus, there is no concept of object identity in Smol.

While values are immutable, *variables* may be modified to hold a different
value.

Since values in Smol are immutable and evaluation is *strict*, there can be no
cyclic data structures or reference cycles of any kind (The graph of references
is a directed acyclic graph).

> IMPLEMENTATION NOTE:
> Because there are no reference cycles, reference counting may be used as a
> precise garbage-collection strategy.

### Effects and Impurity

Most expressions in Smol are *pure*. This means that whenever any expression is
evaluated, nothing about the world changes. In particular, evaluating the same
expression twice will always produce the same result.

For example, the expression `a + b` is pure in most programming languages
because it depends only on the values of `a` and `b`.

While values in Smol can never be modified, external state *can* affect the
execution of a Smol program. Functions that can be affected by external state or
that can affect external state are marked with `!`.

A function with `!` after its name may invoke other `!` actions. A function
without this mark *cannot* invoke `!` actions.

For example, standard input and output functions are marked with `!`:

	static main!() Unit {
		do core:Out.println!("Hello, world!");
	}

## Semantics

A *function* in Smol has several components:

* A set of *parameters* which are assigned values at run-time
* A function body

The function body is a *block* of statements. A block of statements is executed
one at a time from the top to the bottom.

### `var` declaration statement

A `var` declaration statement declares at least one variable and assigns it an
initial value.

	var foo Int = 7;

A variable name cannot be used in a `var` declaration statement if a variable
(or function parameter) with that name is already in scope.

The scope of a variable begins in the next statement in its containing block and
ends at last statement of the variable's containing block.

Multiple variables may be defined at once in one `var` declaration statement.

	var num Int, name String = 1, "one";

### `do` statement

A `do` statement executes an expression.

	do core:Out.println!("Hello, world!");

The return value is discarded.

### `assert` statement

An `assert` statement asserts that a given boolean expression has value `true`
when it is reached. `assert` statements are not run at run-time. See the section
on Verification for more information.

### `return` statement

A `return` statement exits the currently executing function, assigning the
values to be returned.

	return 100;

The number and type of return values must match the function signature. Multiple
values can be returned in one `return` statement.

	return 1, "one";

### Assignment statement

Variables can be assigned new values with an assigment statement.

	num, name = 2, "two";

Multiple variables may be assigned in a single assignment statement. The
expression on the right-hand-side is evaluated before modifying any variables,
thus this can be used to "swap" the values of two variables of the same type:

	foo, bar = bar, foo;

Future references to the variable will use the newly assigned value.

### `if` statement

An `if` statement is a form of control flow. If the condition evaluates to
`true`, the first branch block is executed. If the condition evaluates to
`false`, the statement in the `else` or `elseif` branch is executed.

Only the *first* `if` or `elseif` branch with a condition evaluating to `true`
is taken.

	if 5 < 10 {
		do core:Out.println!("Five is less than ten.");
	} else {
		do core:Out.println!("Something is wrong!");
	}

### `match` statement

A `match` statement is a form of control flow. The tag of the matched expression
determines which branch is taken. As a convenience, the branch brings a variable
into scope and assigns it an initial value of the variant's value.

	do core:Out.println!("The optional value has:");
	match option {
		case nothing None {
			do core:Out.println!("Nothing at all!");
		}
		case something String {
			do core:Out.println!(something);
		}
	}

## Verification

Most programming languages have primitives which can *fail*. Those failures
are typically represented with runtime exceptions (aka panics, interrupts,
errors, or crashes).

Among programming languages, some of the most common runtime crashes are caused
by

* Null pointer dereference.
    Smol does not have any concept of "null" or "nil".
* Type downcast failure.
    Smol does not have any unsafe casts or inheritance.
* Array out of bounds.
    Smol does not have any unchecked array accesses.
* Unwrapping union variants at runtime.
    Smol does not have an unchecked way to unwrap unions.

Smol catches all of these common runtime errors *at compile time*.
In fact, during normal circumstances, no primitive component of Smol can fail at
runtime.

In order to accomplish this without mandating excessive (unreachable) error
handling code, Smol is equipped with a *verification framework*.

Smol checks precondition and postcondition *contracts* which allow
functions to state the conditions they require and the conditions that their
execution guarantees. These contracts are checked at compile time and have no
runtime cost.

For example, here are possible signatures for an array that allows only
in-bounds accesses:

	method get(i Int) #T
		requires this.inBounds(i);

	method set(i Int, value #T) Array[#T]
		requires this.inBounds(i)
		ensures return.get(i) == value
		ensures return.size() == this.size()
		ensures forall (j Int)
			this.get(i) == this.get(j) when this.inBounds(j), (i == j).not();

With these requirements in place, Smol will *statically* check the usage of
every `.get` and `.set`.

If Smol cannot statically prove that the preconditions hold, Smol points out the
problem and rejects the program.

### Satisfiability Modulo Theories (SMT)

The Smol verifier is implemented as an SMT solver.

The question the verification system asks is,

> In this point in the program, does condition `foo` necessarily hold?

This is equivalent to asking

> Is there a possible execution where `~foo` holds at this point in the program?

That is, this can be phrased as a *satisfiability problem*.

Smol uses an SMT solver, which is a boolean SAT solver combined with a "theory"
which allows Smol to understand more complicated expressions.

Smol uses a relatively simple theory of *equality with uninterpreted functions*.

> IMPLEMENTATION NOTE:
> The UF theory can be efficiently implemented, largely using union-find.

Smol also supports quantifiers through the `forall` construct. The expression
`forall (v T) p(v)` holds when it can be shown that `p(v)` holds for every
instance of type `T`.

Verification is not fast.
SAT solving in general is an NP-complete problem (and thus, slow).
Further, a precise SMT solver is in fact in general *undecidable*.

Because Smol attempts to be *sound*, it cannot be *complete*. This means that
there are (provably) correct programs which Smol will reject.

### Verification and Language Primitives

The verification framework understands control flow and its impact on the truth
of conditions:

	if foo {
		assert foo;
	} elseif bar {
		assert foo.not();
		assert bar
	} else {
		assert foo.not();
		assert bar.not();
	}

Variant fields of `union` instances can be retrieved whenever the tag is
statically known. The tag can be tested dynamically using `isa` or `match`:

	union Foo {
		var one Bar;
		var two Bar;
	}


	if foo isa one {
		// OK!
		foo.one.bar();
	} else {
		// OK! Smol understand exhaustivity
		foo.two.bar();

		// ERROR: foo is a two
		foo.one.bar();
	}

Matches must be exhaustive. However, variants which are not possible do not need
to be handled:

	union Three {
		a A;
		b B;
		c C;

		static handle(x Three) Unit
		requires (x isa c).not() {
			match x {
				case a is a {}
				case b is b {}
				// OK with no c case
			}
		}
	}

Smol applies *extensionality*, the fact that if two values are equal, functions
of them are equal:

	if a == b {
		assert a.foo() == b.foo();
	}

	if x.foo() == y.foo() {
		// ERROR! foo() may not be injective!
		assert x == y;
	} else {
		// OK! if x == y, then x.foo() MUST equal y.foo()
		assert (x == y).not();
	}

Assertions, preconditions, and postconditions are never executed at runtime, so
they cannot contain any `!` actions.

### Quantifiers

The `forall` quantifier evaluates to `true` only when the expression evaluates
to `true` for all instances of the given type. For example,

	forall (x Int) 0 < x

is `false` because `-1` is an `Int` and `0 < -1` is false.

However,

	forall (x Int) 0 < x if 10 < x

is `true` because *every* number bigger than `10` is also bigger than `0`.

"There exists" can be expressed by negating a `forall`. However, typically you
can construct a value to show that it exists.

## Failure and Unsoundness

Smol attempts to be *as sound* as possible. A *sound* analysis ensures that a
program that compiles will never

* crash at runtime
* violate at runtime any of the functional correctness propositions expressed in
    an `assert` or `requires` or `ensures`

However, Smol as designed is **not** entirely sound.

### Unchecked Runtime Errors

Some runtime edgecases are not handled by Smol for simplicity.
While these can typically be avoided by properly designing your program, Smol
cannot help you catch programs where these runtime crashes can occur.

#### Allocation
Smol currently assumes that all allocating operations succeed.

In the real world, `new` may fail because the program has exhausted all
available memory. A Smol program that exhausts its memory may stop or misbehave.

#### Stack Overflow
Smol currently assumes you have enough stack space to run your program.
Because Smol has no looping construct, it's not possible to bound the growth of
the stack. As a result, recursion may require an unpredictable amount of space.
A Smol program that exhausts its stack may stop or misbehave.

### Nonterminating Conditions

Smol assertions are *partial correctness specifications*. This means that

> *If and when* the program reaches this position, the condition holds.

When checking the condition, the compiler virtually "runs" the condition via
abstract interpretation, then determines whether or not it must evaluate to
`true`.
Because this is a partial correctness condition, if *evaluating the condition*
may never terminate, the condition may hold *vacuously*. In such a case, the
compiler will accept the buggy program.

Below is an example of such a program, which does `assert false;` at the
beginning of `main()`.

	class Test {
		static oracle(x Boolean) Boolean
		ensures x
		ensures return {
			if x.not() {
				return Test.oracle(x);
			}
			return x;
		}

		static main() Unit {
			// Assertions can only be total expressions
			assert Test.oracle(false);
			assert false;
		}
	}

Assertions *cannot* run at runtime. This is because running them would can
be prohibitively slow (for example, checking the transitivity of `<` would
require examining every triple of elements in a list that you're trying to
sort!) or in some cases impossible (for example, in the case of a
`forall (n Int) Foo.foo(n)`).

Thus, a sound analysis must check that all assertions *are guaranteed to halt*.
This can be checked easily for non-recursive functions, but recursive functions
must be analyzed or annotated further.

The current implementation does **not** attempt to check termination, which
leads to the above unsoundness.
