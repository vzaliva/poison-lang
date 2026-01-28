.PHONY: all clean test poison-lang-spec lean-build lean-clean parser parser-clean cache cache-refresh distclean

all: poison-lang-spec lean-build parser 

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

lean-clean:
	lake clean

parser-clean:
	$(MAKE) -C parser clean
	rm -f config.json

test: cache parser   
	lake build poison-interpreter
	chmod +x run_tests.sh
	echo "Running tests"
	rm -rf testResults
	./run_tests.sh 

clean: lean-clean parser-clean 
	 $(MAKE) -C poison-lang-spec clean

# If you really want to reset everything, including the lock file
distclean: clean
	rm -rf .lake
	rm -f lake-manifest.json
