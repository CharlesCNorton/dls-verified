COQMAKEFILE := Makefile.rocq

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

validate: all
	@if command -v coqchk >/dev/null 2>&1; then \
		coqchk -silent -o -Q . "" dls; \
	else \
		rocq check -silent -o -Q . "" dls; \
	fi

extracted: all
	ocamlc -c dls_extracted.mli dls_extracted.ml

clean:
	rm -f *.vo *.vok *.vos *.glob *.aux .*.aux *.cmi *.cmo
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf .$(COQMAKEFILE).d

.PHONY: all validate extracted clean
