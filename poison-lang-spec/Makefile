.PHONY: all clean poison-lang

all: poison-lang.pdf

poison-lang.tex: poison-lang.ott
	ott -i poison-lang.ott -o poison-lang.tex
	sed -i '/\\begin{verbatim}/,/\\end{verbatim}/d' poison-lang.tex
	sed -i 's/\\\[#1\\\]}/\\[#1\\]\\vspace{0.6em}}/' poison-lang.tex

poison-lang.pdf: poison-lang.tex
	latexmk -pdf poison-lang.tex

clean:
	-latexmk -C 
	-rm -f poison-lang.tex
