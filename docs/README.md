# Documentation

The front page, [`../README.md`](../README.md), says what Logos is, how to build
and run it, and what its correctness theorem does and does not establish. Every
document here assumes it has been read.

| document | what it holds |
| --- | --- |
| [`smt-model-definitions.pdf`](smt-model-definitions.pdf) | the write-up: the SMT-LIB model semantics, the correctness specification and the checker. Built from [`smt-model-definitions.tex`](smt-model-definitions.tex) by `make -C docs`, and committed so it can be read without a LaTeX installation |
| [`smt-lib-conformance.md`](smt-lib-conformance.md) | where the model semantics is narrower than SMT-LIB and where it extends beyond the standard |
| [`parser.md`](parser.md) | the shared parser and generated CPC configuration, the commands and term syntax they accept, and how literals are read. The parser is unverified, and outside the correctness theorem |
| [`lean-native-proofs.md`](lean-native-proofs.md) | `logos-native` and the Lean-native proof format it reads: a secondary, experimental path that runs the same checks |
| [`modularity.md`](modularity.md) | how far the core checker is separated from the calculus it checks, what a checker for another calculus would have to supply, and what is left to do |

[`../install/README.md`](../install/README.md) sits with the scripts it
describes rather than here: it is how the `Cpc` and `CpcMini` packages are
compiled from the Eunoia definition of CPC, what is generated and what is left
alone.

[`misc/`](misc) keeps the superseded LaTeX source of the write-up.
