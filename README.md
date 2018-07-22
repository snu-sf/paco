# Paco: Coq library for Parametric Coinduction

Paco is a Coq library for parametric coinduction.  For more information, please see:

- Chung-Kil Hur, Georg Neis, Derek Dreyer and Viktor Vafeiadis.  [The power of parameterization in
coinductive proof.](https://dl.acm.org/citation.cfm?doid=2429069.2429093).  POPL 2013.

The current version is v1.2.8, and it's compatible with Coq 8.6.1, 8.7.2, and 8.8.1.


## Installation

```bash
# from opam
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-paco

# from source
cd src; make; make install          # for library files
cd src; make doc; make install-doc  # for documentation
```
