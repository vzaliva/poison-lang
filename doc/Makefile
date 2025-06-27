all: poison-lang-description.pdf

poison-lang-description.pdf: poison-lang-description.tex
	latexmk -pdf poison-lang-description.tex

clean:
	latexmk -C poison-lang-description.tex
	rm -f poison-lang-description.bbl 