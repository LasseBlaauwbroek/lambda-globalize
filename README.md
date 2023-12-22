# Globalization of Lambda Terms

This repository contains the reference implementation for the paper
> Hashing Modulo Context-Sensitive Alpha-Equivalence

The main implementation can be found in [lambdahash.ml](lambdahash.ml). Some
tests and simple benchmarks are available in [tests.ml](tests.ml).

## Installation

First, clone the repository:
```bash
git clone git@github.com:LasseBlaauwbroek/lambda-globalize.git
cd lambda-globalize
```

Make sure that you have an Opam switch available. You can create a local switch by running:
```bash
opam switch create . --empty
```

Then, install the dependencies:
```bash
opam install . --deps-only
```

Then, you can build the project and run the tests:
```bash
dune build
dune runtest
```
