.PHONY: all clean test poison-lang-spec lean-build lean-clean

all: poison-lang-spec lean-build

poison-lang-spec:
	$(MAKE) -C poison-lang-spec

lean-build:
	lake build

lean-clean:
	lake clean

clean: lean-clean
	$(MAKE) -C poison-lang-spec clean

parser-test: lean-build
	@echo "Running Poison language tests..."
	@for test in examples/*.poison; do \
		echo "\nTesting $$test:"; \
		lake exe poison-interpreter "$$test"; \
	done

test: lean-build
	lake exe poison-tests

