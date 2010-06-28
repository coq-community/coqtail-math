#!/bin/sh

#DIRS="Arith Complex Hierarchy Modulo mytheories Reals Sets Subseq Topology"
DIRS="-I . -I Arith -I Complex -I Hierarchy -I Modulo -I mytheories/myReals -I Reals -I Sets -I Subseq -I Topology"
GENERATED_MAKEFILE="Makefile"
SRC_V="$(find . -name '*.v' | grep -v Raxioms)"

COQDOCOPTIONS="-g --coqlib http:\/\/coq.inria.fr\/library\/"

coq_makefile $DIRS $SRC_V -no-install -opt \
  | grep -v "^.cd [A-Za-z0-9]* ; ..MAKE. all" \
  | grep -v "^..cd [A-Za-z0-9]* ; ..MAKE. clean." \
  | sed 's/mkdir/mkdir -p/' \
  | sed "s/^COQDOCLIBS:=/COQDOCLIBS:= $COQDOCOPTIONS /" \
  | sed 's/\(..COQDOC. .*html.*\)$/\1\n\tsh alter_doc.sh html/' \
  > $GENERATED_MAKEFILE

touch .depend

