.PHONY: all clean test poison-lang-spec lean-build lean-clean parser parser-clean 

all: poison-lang-spec lean-build parser 

config.json:
	rm -f config.json
	@echo '{ "parser-directories": [ "'$(shell pwd)'/parser" ] }' > config.json

parser: config.json
	$(MAKE) -C parser

poison-lang-spec:
	$(MAKE) -C poison-lang-spec

lean-build:
	lake build

lean-clean:
	lake clean

parser-clean:
	$(MAKE) -C parser clean
	rm -f config.json

parser-test: lean-build
	@echo "Running Poison language tests..."
	@for test in examples/*.poison; do \
		echo "\nTesting $$test:"; \
		lake exe poison-interpreter "$$test"; \
	done

test: lean-build
	lake exe poison-tests

clean: lean-clean parser-clean 
	 $(MAKE) -C poison-lang-spec clean

