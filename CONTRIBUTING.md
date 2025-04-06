# Contributing to MinHS2

Thank you for considering contributing to MinHS2! This document outlines the process for contributing to the project.

## Development Setup

1. Fork the repository
2. Clone your fork locally
3. Set up the development environment:

```bash
# With Cabal
cabal build

# With Stack
stack build
```

## Running Tests

Before submitting changes, make sure all tests pass:

```bash
# With Cabal
./run_tests_cabal.sh

# With Stack
./run_tests_stack.sh
```

## Pull Request Process

1. Create a branch for your feature or bugfix
2. Make your changes, ensuring all tests pass
3. Update documentation if necessary
4. Submit a pull request with a clear description of the changes
5. Reference any related issues in your pull request

## Coding Standards

- Follow the existing code style of the project
- Document new functions with Haddock-style comments
- Write tests for new functionality
- Keep commits focused and logical

## Adding New Features

When adding new features to the MinHS language:

1. Add appropriate syntax definitions in `MinHS/Syntax.hs`
2. Update the parser in `MinHS/Parse.hs`
3. Implement evaluation rules in `MinHS/Evaluator.hs`
4. Add type checking rules in `MinHS/TyInfer.hs`
5. Add test cases in the `tests/` directory

## Reporting Bugs

When reporting bugs, please include:

1. MinHS2 version
2. GHC version
3. Steps to reproduce
4. Expected vs. actual behavior
5. A minimal test case that demonstrates the issue 