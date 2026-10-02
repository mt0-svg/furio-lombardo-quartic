main.pdf: main.tex refs.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

# Writes the table "From the paper to the proof" of ../STATEMENTS.md from the \lean and \computed macros of main.tex.
map: main.pdf
	./statement_map.sh

# Checks that the table of STATEMENTS.md is up to date.
check: main.pdf
	./statement_map.sh --check

clean:
	latexmk -C main.tex

.PHONY: map check clean
