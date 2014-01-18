# First time usage

Run "./generate_makefile.sh" the first time to generate the Makefile
from the Make file. Then Makefile will update itself whenever Make is
modified.

Run "/help.sh" if you feel "make" is not compiling the right
things. It should also help you if coqide's loadpath is fucked up.

# Developer's todo list

Lemmas to prove:
- Mertens' Theorem for Complex numbers
- (expand this list to your wish)

Maintenance:
- Add a "public" README at the root directory
- Check for commented lemmas (and admits)
- Remove useless "Require"s
- Check for admits (run "./todos.sh").
- Check for commented code (run "./todos.sh comments")

# Loadpath problems

To make coqide handle loadpath correctly:

- open coqide, go to Edit > Preferences > Project
- change default name to 'Make'
- choose option 'appended to arguments'

# old configuration

How to launch Real library mytheories in Proofgeneral:
(setq coq-prog-args '("-R" "MY_PATH_TO_COQTAIL/coqtail/src/" "Coqtail"))

For Coqide:
coqide -R MY_PATH_TO_COQTAIL/coqtail/src/ Coqtail fichier.v
