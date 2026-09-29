main.pdf: main.tex refs.bib small_checks.gp small_checks.out ../FurioLombardo/Statement.lean
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

# Reruns the checks printed in the introduction and compares with the recorded output.
check:
	gp -q small_checks.gp < /dev/null | diff - small_checks.out

clean:
	latexmk -C main.tex

.PHONY: check clean
