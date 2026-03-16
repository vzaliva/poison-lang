.PHONY: all clean poison-lang

all: poison-lang.pdf

poison-lang.tex: poison-lang.ott poison-lang-custom.tex
	ott -i poison-lang.ott -o poison-lang.tex
	sed -i '/\\begin{verbatim}/,/\\end{verbatim}/d' poison-lang.tex

poison-lang.pdf: poison-lang.tex poison-lang-custom.tex
	latexmk -pdf poison-lang.tex

clean:
	-latexmk -C 
	-rm -f poison-lang.tex
