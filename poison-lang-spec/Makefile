.PHONY: all clean poison-lang

all: poison-lang.pdf

poison-lang.tex: poison-lang.ott
	ott -i poison-lang.ott -o poison-lang.tex

poison-lang.pdf: poison-lang.tex
	latexmk -pdf poison-lang.tex

clean:
	latexmk -C poison-lang.tex
	rm -f poison-lang.tex

