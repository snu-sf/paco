# Paco: Coq library for Parametric Coinduction

[![Build Status](https://travis-ci.org/snu-sf/paco.svg?branch=master)](https://travis-ci.org/snu-sf/paco)
[![License](https://img.shields.io/badge/license-BSD3-blue.svg)](https://github.com/snu-sf/paco)

Paco is a Coq library for parametric coinduction.  For more information, please see:

- Chung-Kil Hur, Georg Neis, Derek Dreyer and Viktor Vafeiadis.  [The power of parameterization in
coinductive proof](https://dl.acm.org/citation.cfm?doid=2429069.2429093).  POPL 2013.

The current version is v2.0.0, and it's compatible with Coq 8.6.1, 8.7.2, 8.8.1 and 8.9.0.


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
