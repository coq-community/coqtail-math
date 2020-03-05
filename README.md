# Requirements

`master` is developed with Coq 8.11.0, but the following tags point
to snapshots for different version of Coq, which should cover 8.5 to
8.11.

- tag `v8.6.1` for Coq 8.5pl3 and Coq 8.6.1
- tag `v8.7.2` for Coq 8.7.2
- tag `v8.8.2` for Coq 8.8.2
- tag `v8.9.1` for Coq 8.9.1
- tag `v8.10.2` for Coq 8.10.2
- tag `v8.11.0` for Coq 8.11.0

Use e.g. `git checkout v8.10.2` if you want to use Coq 8.10.2. Note
that those tags are for backward compatibility only, there is no
intention of maintaining them as branches: use master instead for
development.

# Compiling

Running `cd src; make` should suffice. It uses a `_CoqProject` file,
which should also allow you to use coqide and proofgeneral with no
further configuration.

# Developer's todo list

Big things:

- prove linear and non-linear theory of ℂ is decidable (using Groebner
  basis)

Lemmas to prove:

- Mertens' Theorem for Complex numbers
- (expand this list to your wish)

Maintenance:

- Add a "public" README at the root directory
- Check for commented lemmas (and admits)
- Remove useless "Require"s
- Check for admits (run "./todos.sh").
- Check for commented results (run "./todos.sh comments")
