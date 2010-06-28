#!/bin/sh

DIRS="Arith Complex Hierarchy Modulo mytheories Reals Sets Subseq Topology"
GENERATED_MAKEFILE="Makefile"
SRC_V="$(find . -name '*.v' | grep -v Raxioms)"

coq_makefile -R . $DIRS $SRC_V -opt \
  | grep -v "^.cd [A-Za-z0-9]* ; ..MAKE. all" \
  | grep -v "^..cd [A-Za-z0-9]* ; ..MAKE. clean." \
  | sed 's/mkdir/mkdir -p/' \
  > $GENERATED_MAKEFILE

touch .depend

