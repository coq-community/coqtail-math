#!/bin/sh

# This script lists all the local files:
#  - whose name doesn't match $discard
#  - whose content matches $query
# 
# And for each of them, displays the concerned lines,
# highlighting the matched strings.

discard="\(\.svn\|\.v\.d$\|\.vo$\|\.glob\|\.crashcoqide\|#$\)"
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
