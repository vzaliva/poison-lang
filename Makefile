.PHONY: all clean test poison-lang-spec doc lean-build lean-build-file lean-clean run run-verbose parser parser-clean cache cache-refresh distclean

all: poison-lang-spec lean-build parser doc

config.json:
	rm -f config.json
	@printf '%s\n' '{' \
 '  "parser-directories": [ "./parser" ],' \
  '  "theme": {' \
  '    "comment": "green",' \
  '    "keyword": "yellow",' \
  '    "atom": "blue",' \
  '    "symbol": "white",' \
  '    "paren": "orange",' \
  '    "base_type": "red",' \
  '    "operator": "black",' \
  '    "funcName": "red",' \
  '    "arg": "yellow"' \
  '  }' \
  '}' > config.json

parser: config.json
	$(MAKE) -C parser

poison-lang-spec:
	$(MAKE) -C poison-lang-spec

doc:
	$(MAKE) -C doc

# Download precompiled lean caches for mathlib/upstreams (idempotent)
# Uses sentinel file to avoid re-downloading if cache already exists
.lake/.cache-downloaded:
	@mkdir -p .lake
	@echo "Downloading Lean cache..."
	@lake exe cache get && touch .lake/.cache-downloaded

cache: .lake/.cache-downloaded

# Force a fresh cache (good after toolchain/mathlib bumps)
cache-refresh:
	lake clean
	rm -rf .lake
	mkdir -p .lake
	lake exe cache get!
	touch .lake/.cache-downloaded

lean-build: cache config.json
	lake build

# Build a single Lean file. FILE = module name (e.g. LeanProofs.FaultRobustness) or path (e.g. LeanProofs/FaultRobustness.lean)
# Example: make lean-build-file FILE=LeanProofs/FaultRobustness.lean
# Example: make lean-build-file FILE=LeanProofs.FaultRobustness
lean-build-file: cache config.json
	@if [ -z "$(FILE)" ]; then echo "Usage: make lean-build-file FILE=LeanProofs/FaultRobustness.lean"; exit 1; fi
	@MODULE=$$(echo "$(FILE)" | sed 's|/|.|g' | sed 's|\.lean$$||'); lake build $$MODULE

# Run a .poison file. POISON = path to .poison file.
# Example: make run POISON=examples/foo.poison
run: cache
	@if [ -z "$(POISON)" ]; then echo "Usage: make run POISON=path/to/file.poison"; exit 1; fi
	lake build poison-interpreter && lake exe poison-interpreter "$(POISON)"

# Run a .poison file with verbose output.
run-verbose: cache
	@if [ -z "$(POISON)" ]; then echo "Usage: make run-verbose POISON=path/to/file.poison"; exit 1; fi
	lake build poison-interpreter && lake exe poison-interpreter --verbose "$(POISON)"

lean-clean:
	lake clean

parser-clean:
	$(MAKE) -C parser clean
	rm -f config.json

test: cache parser
	lake build poison-interpreter
	chmod +x scripts/run_tests.sh
	echo "Running tests"
	rm -rf testResults
	./scripts/run_tests.sh

clean: lean-clean parser-clean
	$(MAKE) -C poison-lang-spec clean
	$(MAKE) -C doc clean

# If you really want to reset everything, including the lock file
distclean: clean
	rm -rf .lake
	rm -f lake-manifest.json
