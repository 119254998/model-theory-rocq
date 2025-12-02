build: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile:
	coq_makefile -f _CoqProject -o CoqMakefile

clean::
	if [ -e CoqMakefile ]; then $(MAKE) -f CoqMakefile cleanall; fi
	$(RM) $(wildcard CoqMakefile CoqMakefile.conf) 

-include CoqMakefile

.PHONY: build clean
