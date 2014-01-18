#!/bin/sh

# This script lists all the local files:
#  - whose name doesn't match $discard
#  - whose content matches $query
# 
# And for each of them, displays the concerned lines,
# highlighting the matched strings.
#
# If you run "todos.sh comments" it will also look for commented code

discard="\(^\.\/html\|\.git\|\.svn\|\.v\.d$\|\.vo$\|\.glob\|\.crashcoqide\|#$\)"
query='\(Admitted\)\|\(admit\)\|\(TODO\)'
opt="-i"

find | grep -v "$discard" |
  while read f
  do
    if [ -f "$f" ]
      then
      if [ "`grep "$query" $opt "$f" | wc -l`" -ne "0" ]
      then
        echo
        echo "\033[1m$f :\033[0m"
        grep --color "$query" $opt "$f"
      fi
    fi
  done

if [ "$1" = "comments" ]; then
    # This script looks for commented code, which is usually not desirable."
    find * | grep '\.v$' | while read f
    do
	(cat "$f" \
	    | awk '{printf("%s ", $0)}' \
	    | grep -o -P '\(\*([^\*]|((\*)(?!\))))*\*\)' \
	    | grep --color -P 'Definition.*:=|Lemma|Theorem|Proposition') \
	    && ( \
	    echo ; \
	    echo "    The above suspect pattern was found in $f." | grep --color "[^ ]*\.v" ; \
	    echo ; echo)
    done
fi