#!/bin/sh

GENERATED_LOCATION="graph/"
GENERATED_SCRIPT="Dependencies"
SRC_V="$(find . -name '*.v' | grep -v Raxioms)"

COQDEPLOCATION="~/svn/trunkcoq/bin/coqdep"
COQDEPOPTIONS="-dumpgraph" #boxes

echo "mkdir -p" $GENERATED_LOCATION ";" $COQDEPLOCATION "-R . Coqtail" \
 $COQDEPOPTIONS $SRC_V " > " $GENERATED_LOCATION"dumpedgraph.dot; \
 tred < " $GENERATED_LOCATION"dumpedgraph.dot > " $GENERATED_LOCATION"trimmedgraph.dot; \
 dot -Tpdf " $GENERATED_LOCATION"trimmedgraph.dot -o graph.pdf" > $GENERATED_SCRIPT

chmod +x $GENERATED_SCRIPT
