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

clean:
	rm -f *.vo *.vok *.vos *.glob *.aux .*.aux *.cmi *.cmo
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf .$(COQMAKEFILE).d

.PHONY: all validate extracted clean
