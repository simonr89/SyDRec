SRC := src
MODULES := $(SRC)/Morphisms.v $(SRC)/morphism_gen.ml $(SRC)/g_morphism.ml4 $(SRC)/morphism_plugin.mllib $(SRC)/Constructive.v $(SRC)/beta_exp.ml $(SRC)/g_beta.ml4 $(SRC)/beta_plugin.mllib
NAME := SyDRec
.PHONY: coq clean install

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile -R $(SRC) $(NAME) $(MODULES) -I $(SRC) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

install: Makefile.coq
	$(MAKE) -f Makefile.coq install
