.PHONY: all clean test poison-lang-spec lean-build lean-clean parser parser-clean 

all: poison-lang-spec lean-build parser 

config.json:
	rm -f config.json
	@printf '%s\n' '{' \
  '  "parser-directories": [ "'$(shell pwd)'/parser" ],' \
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

lean-build:
	lake build

lean-clean:
	lake clean

parser-clean:
	$(MAKE) -C parser clean
	rm -f config.json

test: lean-build
	lake exe poison-tests
	chmod +x run_tests.sh
	./run_tests.sh 

clean: lean-clean parser-clean 
	 $(MAKE) -C poison-lang-spec clean

