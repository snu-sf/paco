COQMODULE    := Paco
COQTHEORIES  := $(wildcard *.v)
COQTHEORIES  := $(filter-out example_upto.v, $(COQTHEORIES))

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

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
