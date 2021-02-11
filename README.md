# Paco: Coq library for Parametric Coinduction

[![Build Status](https://travis-ci.org/snu-sf/paco.svg?branch=master)](https://travis-ci.org/snu-sf/paco)
[![License](https://img.shields.io/badge/license-BSD3-blue.svg)](https://github.com/snu-sf/paco)

Paco is a Coq library for parametric coinduction.  For more information, please see:

- Chung-Kil Hur, Georg Neis, Derek Dreyer and Viktor Vafeiadis.  [The power of parameterization in coinductive proof](https://dl.acm.org/citation.cfm?doid=2429069.2429093).  POPL 2013.
- Yannick Zakowski, Paul He, Chung-Kil Hur and Steve Zdancewic.  [An equational theory for weak bisimulation via generalized parameterized coinduction](https://dl.acm.org/doi/10.1145/3372885.3373813).  CPP 2020.

Paco also supports upto techniques using "companion".  See:
- Damien Pous.  [Coinduction All the Way Up](https://dl.acm.org/citation.cfm?id=2934564).  LICS 2016.

Minki Cho refactored the implementation to speed up the compilation time.

The current version is v4.0.4, and it's compatible with Coq 8.9 - 8.13.


## Installation

```bash
# from opam
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-paco

# from source
cd src; make; make install          # for library files
cd src; make doc; make install-doc  # for documentation
```

## Examples

See [`/src/examples.v`](/src/examples.v) and [`/src/tutorial.v`](/src/tutorial.v) for examples.
