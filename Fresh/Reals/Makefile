VS:=Raxiom.v  Rconvenient.v  Rimpl.v
VOS:=$(VS:.v=.vo)

all:$(VOS)

%.vo %.glob: %.v
	coqc $*

clean:
	rm -f *.vo *.glob
