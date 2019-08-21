COQMODULE    := Paco
COQTHEORIES  := *.v

.PHONY: all theories clean doc

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-Q . $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

doc: Makefile.coq
	$(MAKE) -f Makefile.coq html
	cp index.html main.css html

install-doc: doc
	$(MAKE) -f Makefile.coq install-doc

%: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq
