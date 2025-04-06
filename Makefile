.PHONY: build clean test docs

# Default target is to build with cabal
build:
	cabal build

# Stack build
stack:
	stack build

# Run tests with cabal
test:
	./run_tests_cabal.sh

# Run tests with stack
stack-test:
	./run_tests_stack.sh

# Generate Haddock documentation
docs:
	cabal haddock --haddock-all

# Create a distribution package
dist:
	cabal sdist

# Clean up build artifacts
clean:
	cabal clean
	-rm -rf dist
	-rm -rf dist-newstyle
	-rm -rf .stack-work

# Helpful message for targets
help:
	@echo "Available targets:"
	@echo "  build       - Build with cabal (default)"
	@echo "  stack       - Build with stack"
	@echo "  test        - Run tests with cabal"
	@echo "  stack-test  - Run tests with stack"
	@echo "  docs        - Generate Haddock documentation"
	@echo "  dist        - Create a distribution package"
	@echo "  clean       - Clean up build artifacts"
	@echo "  help        - Show this help message" 