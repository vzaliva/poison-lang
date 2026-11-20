GRAMMAR_DIR := tree-sitter-poison

TS ?= tree-sitter

# Generate the parser sources (src/) from grammar.js and compile them into the
# shared library that `tree-sitter parse` loads.
all:
	cd $(GRAMMAR_DIR) && $(TS) generate && $(TS) build

clean:
	rm -rf $(GRAMMAR_DIR)/src
	rm -f $(GRAMMAR_DIR)/*.so $(GRAMMAR_DIR)/*.dylib $(GRAMMAR_DIR)/*.wasm

.PHONY: all clean
