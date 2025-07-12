FROM ocaml/opam:debian

RUN sudo apt-get update
RUN sudo apt-get install -y libgmp-dev linux-libc-dev pkg-config
RUN sudo apt-get install -y git

RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam update
RUN opam install coq-ssprove
RUN opam install vscoq-language-server