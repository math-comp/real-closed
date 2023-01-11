<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Real closed fields

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/real-closed/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/real-closed/actions?query=workflow:"Docker%20CI"




This library contains definitions and theorems about real closed
fields, with a construction of the real closure and the algebraic
closure (including a proof of the fundamental theorem of
algebra). It also contains a proof of decidability of the first
order theory of real closed field, through quantifier elimination.

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Assia Mahboubi (initial)
- License: [CeCILL-B](CECILL-B)
- Compatible Coq versions: Coq 8.13 or later
- Additional dependencies:
  - [MathComp ssreflect 1.13 or later](https://math-comp.github.io)
  - [MathComp algebra 1.13 or later](https://math-comp.github.io)
  - [MathComp field 1.13 or later](https://math-comp.github.io)
  - [MathComp bigenough 1.0.0 or later](https://github.com/math-comp/bigenough)
- Coq namespace: `mathcomp.real_closed`
- Related publication(s):
  - [Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination](https://hal.inria.fr/inria-00593738v4) doi:[10.2168/LMCS-8(1:2)2012](https://doi.org/10.2168/LMCS-8(1:2)2012)
  - [Construction of real algebraic numbers in Coq](https://hal.inria.fr/hal-00671809v2) doi:[10.1007/978-3-642-32347-8_6](https://doi.org/10.1007/978-3-642-32347-8_6)

## Building and installation instructions

The easiest way to install the latest released version of Real closed fields
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-real-closed
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/real-closed.git
cd real-closed
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



## Documentation
The repository contains
- the decision procedure `rcf_sat` and its corectness lemma [`rcf_satP`](https://github.com/math-comp/real-closed/blob/3721886fffb13ea9c80824043f119ffed0c780f2/theories/qe_rcf.v#L991) for the first order theory of real closed fields through
[certified quantifier elimination](https://hal.inria.fr/inria-00593738v4)
- the definition `{realclosure F}` , a [construction of the real closure of an archimedean field](https://hal.inria.fr/hal-00671809v2), which is canonically a [`rcfType`](https://github.com/math-comp/math-comp/blob/c1ec9cd8e7e50f73159613c492aad4c6c40bc3aa/mathcomp/algebra/ssrnum.v#L63) when `F` is an archimedean field, and the characteristic theorems of section [`RealClosureTheory`](https://github.com/math-comp/real-closed/blob/3721886fffb13ea9c80824043f119ffed0c780f2/theories/realalg.v#L1477).
- the definition `complex R`,  a construction of the algebraic closure of a real closed field, which is canonically a [`numClosedFieldType`](https://github.com/math-comp/math-comp/blob/c1ec9cd8e7e50f73159613c492aad4c6c40bc3aa/mathcomp/algebra/ssrnum.v#L73) that additionally satisfies [`complexalg_algebraic`](https://github.com/math-comp/real-closed/blob/3721886fffb13ea9c80824043f119ffed0c780f2/theories/complex.v#L1324).

Except for the end-results listed above, one should not rely on anything.

The formalization is based on the [Mathematical Components](https://github.com/math-comp/math-comp)
library for the [Coq](https://coq.inria.fr) proof assistant.


## Development instructions

### With nix.

1. Install nix:
  - To install it on a single-user unix system where you have admin
    rights, just type:

    > sh <(curl https://nixos.org/nix/install)

    You should run this under your usual user account, not as
    root. The script will invoke `sudo` as needed.

    For other configurations (in particular if multiple users share
    the machine) or for nix uninstallation, go to the [appropriate
    section of the nix
    manual](https://nixos.org/nix/manual/#ch-installing-binary).

  - You need to **log out of your desktop session and log in again** before you proceed to step 2.

  - Step 1. only need to be done once on a same machine.

2. Open a new terminal. Navigate to the root of the Abel repository. Then type:
   > nix-shell

   - This will download and build the required packages, wait until
     you get a shell.
   - You need to type this command every time you open a new terminal.
   - You can call `nixEnv` after you start the nix shell to see your
     work environemnet (or call `nix-shell` with option `--arg
     print-env true`).

3. You are now in the correct work environment. You can do
   > make

   and do whatever you are accustomed to do with Coq.

4. In particular, you can edit files using `emacs` or `coqide`.

   - If you were already using emacs with proof general, make sure you
     empty your `coq-prog-name` variables and any other proof general
     options that used to be tied to a previous local installation of
     Coq.
   - If you do not have emacs installed, but want to use it, you can
     go back to step 2. and call `nix-shell` with the following option
     > nix-shell --arg withEmacs true

     in order to get a temporary installation of emacs and
     proof-general.  Make sure you add `(require 'proof-site)` to your
     `$HOME/.emacs`.
