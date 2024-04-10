# Globalization of Lambda Terms

This repository contains the reference implementation for the paper
> Hashing Modulo Context-Sensitive Alpha-Equivalence

## Getting Started

The code can be run either through the provided Docker container, or it can be
installed through the Opam package manager or the OCaml programming language.
The two sections below detail how to set up either environment (you only have to
follow one of them).

### Option 1: Docker

First, download the docker image. Then decompress and load it:

```bash
xz -d lambda-hash-docker.tar.xz
docker load -i lambda-hash-docker.tar
```

To start an interactive session with the image run
```bash
sudo docker run -it --rm lambda-hash:2.0
```

### Option 2: Opam

To install the software, you need to have Opam, GMP, MPF and Latex installed on
your system. For Ubuntu 22.04 these prerequisites can be installed as follows:

```bash
apt-get install opam libgmp-dev libmpfr-dev texlive texlive-latex-extra
```

Now, change to the directory of the `lambda-hash` source code and make sure that you
have an Opam switch available. If you'd like to isolate the build from the rest
of your system, you can create a local switch by running the following from the
root :

```bash
opam switch create . --empty
eval $(opam env)
```

Then, install the dependencies:
```bash
opam install . --deps-only --locked
```

(You can choose to omit `--locked` to allow more recent packages to be
installed, at the risk of breaking the build.)

### Basic Testing

To test that the software can be build, run the following commands. This should
finish within a minute without throwing errors.

```bash
dune build && dune runtest
```

## Step-by-step Instructions

After having followed the Getting Started instructions, first clean the build cache:

```bash
dune clean
```

The provided software implements several variants and permutations of the
algorithms described in the paper. These implementations are tested against the
examples provided in the paper, among others. Furthermore, the software includes
some implementations of other algorithms for comparison purposes. The algorithms
can be benchmarked for empirical validation of the claims made in the paper.

### List of claims

1. This repository contains a reference implementation of the globalization
   algorithms and its variants that are presented in the paper.
2. The correctness of the algorithms is validated with several tests. (Some
   tests are derived from examples in the paper.)
3. Benchmarks on various types of randomly generated terms verify the claimed
   O(n log n) runtime of the algorithms.
4. We use the globalization algorithm to assign equivalence classes to sub-terms
   modulo bisimilarity. Benchmarks show that this is competitive with Valmari's
   DFA minimization algorithm.
5. We implement Maziarz' hashing modulo (ordinary) alpha-equivalence algorithm,
   and show through benchmarks that our (optimized) algorithms processing time is
   competitive.

### Code organization:

The following source code files are important.

- [lambda.ml](lambda.ml): Definition of basic lambda terms.
- [lambdahash.ml](lambdahash.ml): Contains several implementations of the
  globalization algorithm described in Section 3 of the paper. It contains
  several implementations of algorithms and datastructures that can be
  mixed-and-matched to obtain different variations of the globalization
  algorithm:
  + Modules implementing the `globalize` function: `NaiveGlobalize` (Section
    3.1), `EfficientGlobalize1` (Section 3.2) and `EfficientGlobalize2`
    (Observation 3.16).
  + Modules for different hashing strategies: `GTerm`, `GDigest` (md5), `GInt`
    (OCamls native hashing strategy), `GTermConsed` (a hashconsed variant of
    `GTerm`).
  + Several implementations of term summaries (Definition 3.7):
    `ClosedZeroSizeModifier`, `LambdaSizeModifier`, `GTermSizeModifier`,
    `IntHashSizeModifier`, `StringHashSizeModifier`.

  To obtain a complete algorithm, these modules can be combined. For example,
  the following creates a globalization algorithm with plain g-terms that uses
  plain term-size as a term summary and combines that with the efficient
  globalization algorithm.
  
  ```ocaml
  module G = EfficientGlobalize1(LambdaImplementation(LambdaSizeModifier(GTerm)))
  ```
- [valmari.ml](valmari.ml): Valmari's DFA minimization algorithm for lambda terms.
- [tests.ml](tests.ml): Correctness tests.
- [lambdacount.ml](lambdacount.ml) and [generate.ml](generate.ml): Code to
  generate random lambda terms for benchmarking purposes.

### Running and inspecting tests:

To run the tests, execute `dune runtest`. The tests run on all permutations of
the globalization algorithm above. The code that executes the tests is in
[tests.ml](tests.ml). It firsts tests that the globalization algorithm produces
correct results for some of the examples in the paper. For example, the first
block of output is as follows:

```
Testing NaiveGlobalize(ClosedZeroSizeModifier(GTerm))
Testing: λ (λ 1) 0 at [↓↘], [↓↙↓]
Testing: λ (λ 0) (λ λ 0 2) (λ 0 1) at [↓↘], [↓↙↘↓] <--- Example 1.0.1
Testing: λ (λ 0) (λ λ 0 1) (λ 0 1) at [↓↘], [↓↙↘↓] <--- Example 1.0.3
Testing: λ (λ 0 1 (λ 1 2)) (λ λ 0 2 (λ 1 3)) at [↓↘↓↓↘↓], [↓↘↓↓↙], [↓↙↓↘↓], [↓↙↓↙] <--- Example 1.0.5
Testing: (λ (λ λ 0 1) (λ 0 1)) (λ (λ λ 0 1) (λ 0 1)) at [↙↓↘↓↙], [↙↓↙↓↓↙]
```

This test globalizes the given lambda term, and then checks that the hashes at
the give positions are equal or not equal.

As a second test, we use the globalization algorithm in combination with
hash-consing to assign equivalence classes to all nodes in a lambda-term. It is
checked that all variants of the globalization algorithm produce the same
equivalence classes and that they agree with the equivalence classes generated
by Valmari's DFA minimization algorithm. For example, the tests contain the
following output:

```
Testing minimization of λ (λ 1) 0
Valmari	 3λ (1λ [0]1) 2@ [0]0
NaiveGlobalize(ClosedZeroSizeModifier(GTermConsed))	 9λ (7λ [6]1) 8@ [6]0
NaiveGlobalize(LambdaSizeModifier(GTermConsed))	 9λ (7λ [6]1) 8@ [6]0
...
```

Here the algorithm processes the term `λ (λ 1) 0`. Each algorithm assigns an
integer to each node. Two nodes receive the same integer if they are bisimilar.
Note that algorithms do not have to agree on the integer they assign to an
equivalence class.

### Amending the tests

To test the correctness of `globalize` w.r.t. to positions in a new lambda-term,
you can follow the following template and add it to [tests.ml](tests.ml):

```
let%test "my new test" =
  let t = from_pure (Lam (App (Lam (Var 1), Var 0))) in
  let p1, p2 = [Down; Left; Down], [Down; Right] in
  info t [p1; p2];
  test (globalize t) p1 p2 && not @@ test t p1 p2
```

The first line defines the term to test (in this case `λ (λ 1) 0`. The second
line defines positions in the term, `[↓↘]` and `[↓↙↓]`. The third line prints
info about the term and paths to stdout. The last line asserts that the hashes
of the two positions are equal after globalization, but not before.

To add a test to the equivalence-class test, one can simply add another example
to the `all_terms` constant in [tests.ml](tests.ml).

### Running benchmarks

We include benchmarks that compare the running time of various algorithms on
synthetically generated terms. One can produce a plot of the benchmarks by
running

```bash
SIZE=9 dune build -j1 --no-buffer benchmark.pdf
```

This produces a pdf that can be found in `_build/default/benchmark.pdf`. If you
are in a docker image, and you wish to view the pdf, you can copy it to your
local machine. First get the docker id of the running container using `docker
ps`. Then, copy the pdf using

```bash
docker cp <docker-id>:/home/opam/lambdahash/_build/default/benchmark.pdf tmp-benchm.pdf
```

The environment variable `SIZE=n` specifies the maximum size `2^n` of
lambda-terms to benchmark. For the final plot, we set `SIZE=13`, but this may
several hours to complete. (Note: This plot has been requested to be added to
the final version of the paper by reviewers. As such, it is not part of the
submitted version of the paper, and we do not yet have a description the
explains the details of the plot.)
