-include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

superclean: cleanall
	rm -f .Makefile.d Makefile.coq Makefile.coq.conf
