COQMAKEFILE := Makefile.rocq

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

validate: all
	@if command -v coqchk >/dev/null 2>&1; then \
		coqchk -silent -o -Q . "" dls; \
	elif command -v rocqchk >/dev/null 2>&1; then \
		rocqchk -silent -o -Q . "" dls; \
	else \
		echo "no kernel checker (coqchk or rocqchk) found" >&2; exit 1; \
	fi

extracted: all
	ocamlc -c dls_extracted.mli dls_extracted.ml

tools: extracted
	ocamlc -I . dls_extracted.cmo tools/dls_cli.ml -o tools/dls
	ocamlc -I . dls_extracted.cmo tools/props.ml -o tools/props

test: tools
	./tools/props

js: tools
	js_of_ocaml tools/dls -o tools/dls.js

clean:
	rm -f *.vo *.vok *.vos *.glob *.aux .*.aux *.cmi *.cmo
	rm -f tools/*.cmi tools/*.cmo tools/dls tools/props tools/dls.js
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf .$(COQMAKEFILE).d

.PHONY: all validate extracted tools test js clean
