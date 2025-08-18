FROM ocaml/opam:debian

RUN sudo apt-get update
RUN sudo apt-get install -y libgmp-dev linux-libc-dev pkg-config
RUN sudo apt-get install -y git

RUN opam repo add rocq-released https://rocq-prover.org/opam/released
RUN opam update
RUN opam pin add --no-action coq-ssprove https://github.com/SSProve/ssprove.git
RUN opam install coq-ssprove coq-mathcomp-algebra-tactics
RUN opam install vscoq-language-server
