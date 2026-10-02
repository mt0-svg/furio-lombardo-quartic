main.pdf: main.tex refs.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

# Writes the table "From the paper to the proof" of ../STATEMENTS.md from the \lean and \computed macros of main.tex.
map: main.pdf
	./statement_map.sh

# Reruns the checks printed in the introduction and compares with the recorded output, then checks that the
# table of STATEMENTS.md is up to date.
check: main.pdf
	gp -q small_checks.gp < /dev/null | diff - small_checks.out
	./statement_map.sh --check

clean:
	latexmk -C main.tex

.PHONY: map check clean
