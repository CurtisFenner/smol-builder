# The Smol Compiler, `smolc`

`smolc` is a highly-portable compiler for the toy programming language I call
Smol that emits standard-conforming ISO C99.
Smol is a pure, statically-typed, procedural programming language that includes
classes, interfaces, tagged unions, and generics.

## Hello world!

```java
// Every Smol file begins with a "package" declaration, which is a namespace.
package test;

// You must explicitly import types defined in other files.
import core;

// This class called `Main` defines a static function called `main`,
// which is the entry point of this hello world program.
class Main {
	static main!() Unit {
		// Invoke a static action on the core:Out type.
		// The `!` indicates that the function is not pure.
		do core:Out.println!("Hello world!");
	}
}
```

## Installing the Smol compiler

These instructions explain what you need to run `smolc` and the compiler tests.

First, install Lua 5.1. Lua 5.2 and Lua 5.3 are **not** supported at this time.

Next, clone this repository.

```
$ git clone https://github.com/CurtisFenner/smol-builder.git
$ cd smol-builder
```

Change the current directory to the repository (so that `setup.bat` is in the
current directory). Run `setup.bat`, which generates `smolc.bat` and `smolc.sh`,
two scripts that can be added to the path. Right now, `smolc.bat` requires
`sh` be installed.

TODO: add `setup.sh`

The compiler does not need to be built or prepared in any way and it does not
have any dependencies other than Lua.

## Using the Smol compiler

You can invoke the compiler directly by listing all .smol files that should be
compiled and indicating the main class:

```
$ lua compiler.lua --sources tests-positive/hello-world/test.smol --main test:Test
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

You can also use the `smolc.bat` or the `smolc.sh` helper script to
automatically populate the list of smol files in a directory:

```
$ smolc tests-positive/hello-world test:Test
```

Add the smol-builder directory to your path so that you can use `smolc.sh` to
compile your Smol projects.

`smolc.bat` is another script that invokes `sh smolc.sh`.

## Running the Smol compiler tests

While the compiler itself is intended to be very portable, the tests are **not**
currently as portable.

You need to have `ls` available in your path (Cygwin/MinGW will work on Windows)
and your installation of Lua 5.1 must support `io.popen`
(most installations of Lua support `io.popen` by default).

You also must have a version of `gcc` installed that supports C99.

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
Compiler bugs are possible, exercise caution.

## VSCode Plugin

TODO

# The Smol Programming Language

I have been designing Smol since approximately Spring of 2017.
My mission is to create a programming language that rigidly enforces the
conventions that I have found to be helpful
in designing maintainable software. These conventions include
* Statically checked annotations (types)
* Explicitness
* Immutability
* Familiarity
* Totally defined behavior

Through the addition of preconditions and postconditions, I plan to entirely
eliminate runtime errors from Smol.

## Author

[Curtis Fenner](http://curtisfenner.com),
undergraduate at University of Michigan, 2014 - 2018.