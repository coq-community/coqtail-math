#!/bin/sh

INHABITED_V=$(find Inhabited -name '*.v')
REALS_V="Reals/Raxiom.v Reals/Rconvenient.v Reals/Rimpl.v"
FILES="$INHABITED_V $REALS_V"

coq_makefile -R . Coqtail.Fresh $FILES -opt > Makefile
