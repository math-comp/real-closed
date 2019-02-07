[![Build Status](https://travis-ci.org/math-comp/real_closed.svg?branch=master)](https://travis-ci.org/math-comp/real-closed)

# Theorems for real closed fields
The repository contains
- the decision procedure `rcf_sat` and its corectness lemma [`rcf_satP`](https://github.com/math-comp/real-closed/blob/3721886fffb13ea9c80824043f119ffed0c780f2/theories/qe_rcf.v#L991) for the first order theory of real closed fields through
  [certified quantifier elimination](https://hal.inria.fr/inria-00593738v4)  
- the definition `{realclosure F}` , a [construction of the real closure of an archimedean field](https://hal.inria.fr/hal-00671809v2), which is canonically a [`rcfType`](https://github.com/math-comp/math-comp/blob/c1ec9cd8e7e50f73159613c492aad4c6c40bc3aa/mathcomp/algebra/ssrnum.v#L63) when `F` is an archimedean field, and the characteristic theorems of section [`RealClosureTheory`](https://github.com/math-comp/real-closed/blob/3721886fffb13ea9c80824043f119ffed0c780f2/theories/realalg.v#L1477).
- the definition `complex R`,  a construction of the algebraic closure of a real closed field, which is canonically a [`numClosedFieldType`](https://github.com/math-comp/math-comp/blob/c1ec9cd8e7e50f73159613c492aad4c6c40bc3aa/mathcomp/algebra/ssrnum.v#L73) that additionally satisfies [`complexalg_algebraic`](https://github.com/math-comp/real-closed/blob/3721886fffb13ea9c80824043f119ffed0c780f2/theories/complex.v#L1324).

Except for the end-results listed above, one should not rely on anything.

The formalization is based on the [Mathematical Components](https://github.com/math-comp/math-comp)
library for the [Coq](https://coq.inria.fr) proof assistant.

## Installation

With opam, using the package

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-real-closed
```

Or locally:

```
opam pin add coq-mathcomp-real-closed .
```

Or manually, assuming mathematical componenents is installed
```
make
make install
```
