FROM ocaml/opam:ubuntu-22.04-ocaml-5.1

RUN sudo apt-get --yes install libgmp-dev libmpfr-dev texlive texlive-latex-extra

COPY --chown=opam:opam lambda-globalize.opam lambdahash/

WORKDIR lambdahash

RUN opam install . --deps-only

COPY --chown=opam:opam . .

RUN eval $(opam env) && dune runtest && SIZE=8 dune build -j1 --no-buffer && dune clean