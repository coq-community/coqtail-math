#!/bin/bash

# checking for files 

is_tracked () { git ls-files "$1" --error-unmatch >> /dev/null 2>&1; }
# is_tracked FILE && echo TRACKED || echo UNTRACKED

# echo "Diffing '_CoqProject' and actual .v files..."
(diff <(find * -name "*.v" | sort) <(cat _CoqProject | grep "\.v" | sort) \
    | grep '^[<>]' \
    | sed 's/^< \(.*\)$/\1: is not in _CoqProject (add to _CoqProject?)/' \
    | sed 's/^> \(.*\)$/\1: unfound but in (remove from _CoqProject?)/'
    ) \
	| tee >(wc -l | grep '^0$' | sed 's/^0$/"_CoqProject" appears to be configured correctly./') \
	| grep --color -E "^.*\.v|$"

# coqide configuration
rc="$HOME/.config/coq/coqiderc"
[ -f "$rc" ] && \
    ((grep "project_file_name = ._CoqProject." $rc && \
    grep "project_options = .appended to arguments." $rc) || \
    (echo "
To make coqide handle loadpath correctly:
- open coqide, go to Edit > Preferences > Project
- change default name to '_CoqProject'
- choose option 'appended to arguments'
")) | grep -v "="
