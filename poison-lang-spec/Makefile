.PHONY: all clean
.DELETE_ON_ERROR:

all: poison-lang.pdf

# `sed -i.bak` (with a suffix) is the form accepted by both GNU and BSD sed.
poison-lang.tex: poison-lang.ott poison-lang-custom.tex
	ott -i poison-lang.ott -o poison-lang.tex
	sed -i.bak '/\\begin{verbatim}/,/\\end{verbatim}/d' poison-lang.tex
	rm -f poison-lang.tex.bak

poison-lang.pdf: poison-lang.tex poison-lang-custom.tex
	latexmk -pdf poison-lang.tex

clean:
	-latexmk -C 
	-rm -f poison-lang.tex
