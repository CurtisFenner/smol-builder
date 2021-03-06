# The Smol Programming Language and Documentation

**[A full description of Smol can be found here.](docs/smol.md)**

I have been designing Smol since Spring of 2017.
My mission is to create a programming language that rigidly enforces the
conventions that I have found to be helpful
in designing maintainable software. These conventions include
* Statically checked functional correctness
* Explicitness
* Immutability
* Totally defined behavior

# The Smol Compiler, `smolc`

**`smolc`** is a highly-portable compiler for the toy programming language I
call Smol that emits standard-conforming ISO C99.
**Smol** is a pure, statically-typed, procedural programming language that
includes classes, interfaces, tagged unions, and generics.

Smol also includes a **verification framework** that allows assertions to be
checked *statically* with *zero runtime cost*. This analysis is mostly sound;
programs written in Smol do not reach error states.

## Hello world!

```java
// Every Smol file begins with a "package" declaration, which is a namespace.
package hello;

// You must explicitly import types defined in other files.
import core;

// This class called `HelloWorld` defines a static function called `main`,
// which is the entry point of this hello world program.
class HelloWorld {
	static main!() Unit {
		// Invoke a static action on the core:Out type.
		// The `!` indicates that the function is not pure.
		do core:Out.println!("Hello world!");

		// Statically checked assertions can be embedded in your code
		assert (1 + 2) == 3;
	}
}
```

## Installing the Smol compiler

These instructions explain what you need to run `smolc` and the compiler tests.

First, install Lua 5.1, Lua 5.2, or Lua 5.3. Lua may already be installed on
your machine!
`$ lua -v` will print the installed version.

Next, clone this repository.

```
$ git clone https://github.com/CurtisFenner/smol-builder.git
$ cd smol-builder
```

The compiler does not need to be built or prepared in any way and it does not
have any dependencies other than Lua 5.1/5.2/5.3.

## Using the Smol compiler

You can invoke the compiler directly by listing all .smol files that should be
compiled and indicating the main class:

```
$ lua src/compiler.lua --sources tests-positive/runtime/hello-world/test.smol --main test:Test
```

This produces a C99 `output.c` file in the current directory that you can
compile with your favorite C compiler:

```
$ gcc -std=c99 -pedantic output.c -o smol-hello-world
$ ./smol-hello-world
Hello world!
Hello
	world!
こんにちは世界
$
```

## Running the Smol compiler tests

The tests have a few extra dependencies:

* You need to have `ls` available in your path
    (Cygwin/MinGW will work on Windows)
* Your installation of Lua 5.1/5.2/5.3 must support `io.popen`
    (most installations of Lua support `io.popen` by default)
* You need a version of `gcc` installed in your path that supports pedantic C99

To run all the tests, run the following from the smol-builder directory:

```
$ lua test.lua
```

To only run certain tests, include a filter substring as the first argument to
the test script:

```
$ lua test.lua hello
```

**NOTE**: This produces C code and then compiles and executes that C code.
Compiler bugs are inevitable, exercise caution!

## VSCode Plugin

The VSCode extension can be found here:
https://marketplace.visualstudio.com/items?itemName=curtisfenner.smolcomp.

This extension provides syntax highlighting and red-underlining of errors.
Configure it by pointing it to the `src/compiler.lua` file in the cloned folder.

## Author

[Curtis Fenner](http://curtisfenner.com),
undergraduate at University of Michigan, 2014 - 2018.
