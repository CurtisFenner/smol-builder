# Satisfiability Modulo Theories

Satisfiability Modulo Theories (SMT) is a problem and problem-solving method for
determining whether or not a mathematical formula is (or is not) true.

SMT can be used to statically check hardware and software by proving the
design can never reach error states. SMT is popular for checking software
properties.

Smol contains its own SMT solver, implemented in Lua.

This document explains what SMT is and how the Smol SMT solver works.

## Theorem Proving

We can use an SMT solver to prove (verify) theorems.

The input is a Boolean **formula**. For example, the following:

	((a or ~b) and c) => (a or (b and c))

We want to know whether or not the above is always true: does `(a or ~b) and c`
necessarily imply `a or (b and c)`?

An **assignment** gives a value to each **variable**. For example, we have the
assignment

	a is TRUE
	b is FALSE
	c is TRUE

For this assignment, the formula has the value

	((TRUE or ~FALSE) and TRUE) => (TRUE or (FALSE and TRUE))
	TRUE => TRUE
	TRUE

We say that an assignment **satisfies** a formula when that formula evaluates to
TRUE under that assignment. A formula is **satisfiable** if there is *some*
assignment that satisfies the formula.

The job of an SMT solver is to either find such an assignment, or rule out its
existence.

If a statement is *true*, then its negation must always be *false*. That is,
to prove a statement, we must ask whether or not its negation is satisfiable.

For the above input, we ask whether or not the formula below is satisfiable:

	~[((a or ~b) and c) => (a or (b and c))]

## Conjunctive Normal Form and Satisfiability

Determining whether or not a boolean formula is satisfiable is typically
expressed in the **CNF-SAT** problem.

A formula is in **conjunctive normal form** (CNF) when it is expressed as a
**conjunction** (logical ands) of **disjunctions** (logical ors).

The first step of determining satisfiability is to convert the formula to CNF.

This can be done by applying Demorgan's Laws and other simplification rules.

	    x => y
	is equivalent to
	    ~x or y

	   ~(x and y)
	is equivalent to
	    ~x or ~y

	    ~(x or y)
	is equivalent to
	    ~x and ~y

	   x or (y and z)
	  is equivalent to
	(x or y) and (x or z)

Transforming the example formula above, we get

	~[((a or ~b) and c) => (a or (b and c))]
	~[~((a or ~b) and c) or (a or (b and c))]
	(a or ~b) and (c) and ~(a or (b and c))
	(a or ~b) and (c) and (~a) and ~(b and c)
	(a or ~b) and (c) and (~a) and (~b or ~c)

The parenthesized expressions are called **clauses**. Clauses are the
disjunction of **literals**, which is a variable or the negation of a variable.

The overall formula is turned into an `and` of clauses.

### Naive Satisfiability

A simple approach to determine whether or not a formula is satisfiable is to
enumerate all assignments and check if each one satisfies the formula.

There are 2<sup>n</sup> such assignments:

	a b c
	-----
	F F F
	F F T
	F T F
	F T T
	T F F
	T F T
	T T F
	T T T

This may be manageable for 3 variables; however, Smol often generates conditions
with hundreds or thousands of variables.

Suppose we can check one trillion assignments per second. The time required to
check 2<sup>80</sup> assignments is more than 30,000 years! We need to do
better.

> In fact, CNF-SAT is an NP-Complete problem. It is hypothesized that there is
> no better-than-exponential algorithm for CNF-SAT in general. *However*,
> typical input to an SMT solver are *not* general inputs, so we can do better.

### Backtracking

We can improve by employing *backtracking*. In this approach, we choose only one
variable at a time to add to the assignment. We can stop early if we find the
assignment we have chosen so far is futile.

	a b c | (a or ~b) and (c) and (~a) and (~b or ~c)
	------+---------------------------------------------------------
	T _ _ | TRUE and (c) and FALSE and (~b or ~c)     -- NO GOOD
	F _ _ | (~b) and (c) and TRUE and (~b or ~c)
	F T _ | FALSE and (c) and TRUE and (~c)           -- NO GOOD
	F F _ | TRUE and (c) and TRUE and TRUE
	F F T | TRUE and TRUE and TRUE and TRUE           -- SATISFIED!

If we get lucky with our choices, the formula will be satisfied (or ruled out)
quickly. However, most of the time we will have to assign *most* of the terms
before a contradiction is found, so this on its own does not significantly
improve solve time.

### Unit Propagation

A powerful tool for solving formulas is **unit propagation**. In order to
satisfy a CNF formula, all of its clauses must be satisfied. Thus, if there is
ever a clause with only one way to satisfy it, we should immediately pick that.

A clause has one way to satisfy it when it is made of a single literal, such as
`(~a)` or `(c)` in the above.

	a b c | (a or ~b) and (c) and (~a) and (~b or ~c)
	------+---------------------------------------------------------
	_ _ T | (a or ~b) and TRUE and (~a) and (~b)
	F _ T | (~b) and TRUE and TRUE and (~b)
	F F T | TRUE and TRUE and TRUE and TRUE           -- SATISFIED!

Unit propagation works well because as terms are simplified, more single-literal
clauses are made.

## Theories

Programs use more than just Booleans. We need to be able to reason about
functions and numbers and strings and lists. SMT does this by coordinating 
cooperation between a CNF-SAT solver and a *theory*.

An input problem may look like

	[x=y OR f(x,y)=1] and [f(x,y)!=f(y,y) or f(x,x)!=f(x,y)]

First, we transform the problem into CNF, and replace all "complex" expressions
with short names:

	[a or b] and [~c or ~d]

	a: x = y
	b: f(x,y) = 1
	c: f(x,y) = f(y,y)
	d: f(x,x) = f(x,y)

Next, we ask the CNF-SAT procedure to find a satisfaction.

	a b c d | [a or b] and [~c or ~d]
	--------+--------------------------------------------------------------
	T _ _ _ | TRUE and [~c or ~d]      -- Arbitrary choice (no unit clause)
	T _ F _ | TRUE and TRUE            -- Satisfied!

The CNF-SAT algorithm produced the following assignment:

	          x=y : TRUE
	f(x,y)=f(y,y) : FALSE

We now ask the *theory* whether or not it finds this assignment reasonable.

Because `x=y` it should be the case that `f(x,y) = f(y, y)`.

Yet the assignment says `f(x,y) != f(y,y)`. Figuring out this contradiction
is the job of the *theory*.

Because of this contradiction, the given assignment does not work to satisfy the
original formula.

Because CNF-SAT doesn't understand the *meaning* of the variables it is
assigning, it does not know about the implicit constraints. By asking the
theory, it *learns* additional constraints. In this case, it learns

Because `a` and `~c` contradiction each other, it learns that `~(a and ~c)`.
Equivanently, a new clause `(~a or c)` is added to the problem:

	a b c d | [a or b] and [~c or ~d]
	--------+--------------------------------------------------------------
	T _ _ _ | TRUE and [~c or ~d]      -- Arbitrary choice (no unit clause)
	T _ F _ | TRUE and TRUE            -- Satisfied!
	--------+--------------------------------------------------------------
	a b c d | [a or b] and [~c or ~d] and [~a or c]
	--------+--------------------------------------------------------------
	T _ F _ | TRUE and TRUE and FALSE  -- Backtrack
	T _ T _ | TRUE and [~d] and TRUE
	T _ T F | TRUE and TRUE and TRUE   -- Satisfied!

The theory will also reject `x=y and f(x,y)=f(y,y) and f(x,x)!=f(x,y)`. We can
easily get the clause `(~a or ~c or d)`. However, if the theory is *specific* it
can explain that just `(~a or d)` explains the problem. Smaller clauses rule out
far more assignments, so we hope the theory can give us this.

	a b c d | [a or b] and [~c or ~d]
	--------+--------------------------------------------------------------
	T _ _ _ | TRUE and [~c or ~d]      -- Arbitrary choice (no unit clause)
	T _ F _ | TRUE and TRUE            -- Satisfied!
	--------+--------------------------------------------------------------
	a b c d | [a or b] and [~c or ~d] and [~a or c]
	--------+--------------------------------------------------------------
	T _ F _ | TRUE and TRUE and FALSE  -- Backtrack
	T _ T _ | TRUE and [~d] and TRUE
	T _ T F | TRUE and TRUE and TRUE   -- Satisfied!
	--------+--------------------------------------------------------------
	a b c d | [a or b] and [~c or ~d] and [~a or c] and [~a or d]
	T _ T F | TRUE and TRUE and TRUE and FALSE -- Backtrack
	T _ T T | TRUE and FALSE and TRUE and TRUE -- Backtrack
	F _ _ _ | [b] and [~c or ~d] and TRUE and TRUE
	F T _ _ | TRUE and [~c or ~d] and TRUE and TRUE
	F T F _ | TRUE and TRUE and TRUE and TRUE

The resulting assignment is

	          x=y : FALSE
	     f(x,y)=1 : TRUE
	f(x,y)=f(y,y) : FALSE

The theory finds no problem with this assignment, and thus we find that the
formula has the above satisfying assignment.

Notice that of the 2<sup>4</sup>=16 possible assignments, we only needed to
backtrack 4 times!
