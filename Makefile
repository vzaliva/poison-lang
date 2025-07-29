.PHONY: all clean test poison-lang-spec lean-build lean-clean parser parser-clean 

all: poison-lang-spec lean-build parser 

parser:
	cd parser/tree-sitter-poison && tree-sitter generate && tree-sitter build 

poison-lang-spec:
	$(MAKE) -C poison-lang-spec || true

lean-build:
	lake build

lean-clean:
	lake clean


parser-clean:
	rm -rf parser/tree-sitter-poison/build \
	       parser/tree-sitter-poison/src/parser.c \
	       parser/tree-sitter-poison/src/scanner.c \
	       parser/tree-sitter-poison/src/parser.o \
	       parser/tree-sitter-poison/src/scanner.o \
	       parser/tree-sitter-poison/tree-sitter-poison.js \
	       parser/tree-sitter-poison/binding.gyp

parser-test: lean-build
	@echo "Running Poison language tests..."
	@for test in examples/*.poison; do \
		echo "\nTesting $$test:"; \
		lake exe poison-interpreter "$$test"; \
	done

test: lean-build
	lake exe poison-tests

clean: lean-clean parser-clean 
	-$(MAKE) -C poison-lang-spec clean || true

