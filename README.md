<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Coqtail

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/coqtail-math/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/coqtail-math/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



Coqtail is a library of mathematical theorems and tools proved inside
the Coq proof assistant. Results range mostly from arithmetic to real
and complex analysis.

## Meta

- Author(s):
  - Guillaume Allais
  - Sylvain Dailler
  - Hugo Férée
  - Jean-Marie Madiot
  - Pierre-Marie Pédrot
  - Amaury Pouly
- Coq-community maintainer(s):
  - Jean-Marie Madiot ([**@jmadiot**](https://github.com/jmadiot))
- License: [GNU Lesser General Public License v3.0 only](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies: none
- Coq namespace: `Coqtail`
- Related publication(s): none

## Building instructions

``` shell
git clone https://github.com/coq-community/coqtail-math
cd coqtail-math
make   # or make -j <number-of-cores-on-your-machine>
```

## Coqtail and Vim

Note that this project is distinct from [this other project named
Coqtail](https://github.com/whonore/Coqtail), which helps using Coq in Vim.

## Developer's todo list

Big things:

- prove linear and non-linear theory of ℂ is decidable (using Groebner basis)

Lemmas to prove:

- Mertens' Theorem for Complex numbers
- (expand this list to your wish)

Maintenance:

- Use `-Q` instead of `-R` and fix the resulting loadpath problems
- Check for commented lemmas (and admits)
- Remove useless `Require`s
- Check for admits (run `./todos.sh`).
- Check for commented results (run `./todos.sh comments`)
