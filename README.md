# MinHS2: A Minimal Haskell-like Language Interpreter

MinHS2 is an interpreter for a small, minimal functional language with Haskell-like syntax. It provides a lightweight environment for learning functional programming concepts, language implementation, and compiler theory.

Originally developed for educational purposes, MinHS2 demonstrates key concepts in programming language design and implementation, including lexical analysis, parsing, type checking, and interpretation.

## Overview

MinHS2 implements a functional language with the following features:
- Static type checking with type inference (Hindley-Milner type system)
- First-class functions and recursion
- Pattern matching with case expressions
- Algebraic data types (products and sums)
- Let and letrec bindings
- Basic integer arithmetic and boolean operations

## Getting Started

### Prerequisites

To build and run MinHS2, you need:
- GHC (Glasgow Haskell Compiler)
- Cabal or Stack build tools

### Building with Cabal

```bash
cabal build
```

### Building with Stack

```bash
stack build
```

### Building with Make

A Makefile is provided for convenience:

```bash
make        # Build with cabal
make stack  # Build with stack
make test   # Run tests with cabal
```

Run `make help` to see all available targets.

## Running MinHS2

After building, you can run the MinHS2 interpreter on a MinHS source file:

```bash
# Using Cabal
cabal run minhs-2 -- filename.mhs

# Using Stack
stack exec minhs-2 -- filename.mhs
```

### Examples

The `examples/` directory contains several MinHS programs that demonstrate various language features:

- `fibonacci.mhs` - Recursive Fibonacci sequence implementation
- `factorial.mhs` - Recursive factorial implementation
- `sum_product.mhs` - Demonstration of sum and product types

To run an example:

```bash
cabal run minhs-2 -- examples/fibonacci.mhs
```

### Command-line Options

MinHS2 supports several command-line options:

- `--dump STAGE`: Dumps the program state after a specific stage:
  - `parser`: After parsing
  - `parser-raw`: After parsing (raw output)
  - `type-infer`: After type inference
  - `evaluator`: After evaluation (default)
- `--no-colour`: Disables colored output

## Running Tests

The project includes a comprehensive test suite that can be run with:

```bash
# Using Cabal
./run_tests_cabal.sh

# Using Stack
./run_tests_stack.sh

# Using Make
make test
```

## Language Syntax

### Basic Syntax

MinHS programs consist of a series of bindings, with the main expression bound to `main`:

```
main = 42;
```

### Function Definitions

```
factorial n = if (n == 0) 
                then 1 
                else (n * (factorial (n - 1)));

main = factorial 5;
```

### Let Expressions

```
main = 
  let x = 10; 
  in x + 5;
```

### Recursive Functions

```
main = 
  recfun fib n = if (n <= 1) 
                  then n 
                  else (fib (n - 1)) + (fib (n - 2));
```

### Algebraic Data Types

MinHS supports product and sum types:

```
# Pair (product type)
main = Pair 1 2;

# Sum type
main = 
  let x = Inl 5;
  in case x of {
    Inl n -> n + 1;
    Inr m -> m - 1;
  };
```

## Project Structure

- `Main.hs`: Entry point for the interpreter
- `MinHS/`: Core modules for the MinHS language
  - `Syntax.hs`: Abstract syntax tree definitions
  - `Parse.hs`: Parser for MinHS language
  - `Evaluator.hs`: Interpreter for MinHS expressions
  - `TyInfer.hs`: Type inference and checking
  - `Pretty.hs`: Pretty printing for MinHS expressions and types
  - `Env.hs`: Environment handling for variables
  - `Subst.hs`: Substitution operations for type variables
  - `TCMonad.hs`: Monad for type checking operations
- `tests/`: Comprehensive test suite for the MinHS language
- `examples/`: Example MinHS programs demonstrating language features

## Documentation

Haddock documentation can be generated with:

```bash
make docs
```

## Recent Improvements

The project has recently undergone cleanup and improvements:
- Added comprehensive documentation using Haddock-style comments
- Created a proper build system with Makefile support
- Added CONTRIBUTING guidelines
- Added LICENSE (MIT)
- Added CHANGELOG to track project history
- Improved code organization and formatting
- Enhanced the cabal file with better metadata
- Added example programs demonstrating the language

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgements

Originally developed by Liam O'Connor at UNSW for teaching programming language concepts. 