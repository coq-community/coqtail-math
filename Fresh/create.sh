#!/bin/sh

INHABITED_V=$(find Inhabited -name '*.v')
REALS_V="Reals/Raxiom.v Reals/Rconvenient.v Reals/IZR.v Reals/Repsilon.v Reals/Rseq.v Reals/Rapprox.v Reals/Rorder.v Reals/Rfun.v Reals/Rabs.v Reals/Rimpl.v Reals/Rrealize.v"
FILES="$INHABITED_V $REALS_V"

coq_makefile -R . Coqtail.Fresh $FILES -opt > Makefile
