# Logos Checker

## A Verified Proof Checker for SMT Solvers

Logos is a verified proof checker for SMT written in Lean.
It is an executable checker whose soundness is proven in Lean against a correctness
specification, which depends on a complete definition of SMT-LIB semantics in Lean.
That definition, `Cpc/SmtModel.lean`, is an independent model semantics for SMT-LIB:
a standalone Lean formalization of the meaning of SMT-LIB terms that does not depend
on the checker and can be used on its own.
See [Correctness](#correctness) below for what that proof establishes and what it still assumes.

The semantics, the correctness specification and the checker are written up in
[docs/smt-model-definitions.pdf](docs/smt-model-definitions.pdf).

The calculus Logos checks is compiled from a definition written in *Eunoia*,
the logical framework of the proof checker Ethos
(https://github.com/cvc5/ethos), in which proof calculi are defined as
*signatures*. The Cooperating Proof Calculus (CPC) is one such signature — the
calculus in which cvc5 emits proofs, maintained at
https://github.com/cvc5/cvc5/blob/main/proofs/eo/cpc/Cpc.eo.

Logos has a fully functional CPC parser, meaning that it accepts the same syntax for proofs as Ethos
(see [docs/parser.md](docs/parser.md)).
However, Logos does not support arbitrary Eunoia signatures.
Instead,
the proof rules currently used by Logos are automatically generated from the current definition of CPC.
This compilation uses the Eunoia compiler `ethos-eoc`,
which lives in the Ethos repository and is documented at
https://github.com/cvc5/ethos/blob/main/tools/eoc/README.md.
The definition of Logos evolves and remains in sync with the definition of CPC
as further reasoning capabilities are added to cvc5.
See [Regenerating the calculus](#regenerating-the-calculus) for how to rerun that compilation.

## Building the Logos checker

```bash
scripts/build.sh logos
```

The build script uses the Lean version pinned in `lean-toolchain`. A direct
`lake build logos` is equivalent on supported hosts; the script additionally
falls back to the host C compiler and archiver on older Linux systems, where
Lean's bundled Clang cannot run against the host's glibc. The header of
`scripts/lean-toolchain-env.sh` describes that fallback and what to do when it
is not enough.

The checker executable is `logos`; it checks CPC proofs in s-expression syntax.
The first build of a CPC executable takes roughly 3.5 minutes currently. A
second executable, `logos-native`, reads an internal input format; see
[docs/lean-native-proofs.md](docs/lean-native-proofs.md).

`CpcMini` is a cut-down calculus used to develop and test the proofs; it has no
parser and no executable of its own.

To run the same checks as CI locally, use:

```bash
bash scripts/run-ci.sh
```

One of them, the `regeneration` group, recompiles the calculus and is skipped
until `install/get-eo-compiler.sh` has been run once. See
[Regenerating the calculus](#regenerating-the-calculus).

To build every CPC proof rule, use:

```bash
scripts/build-all-cpc-rules.sh
```

The script builds one rule target at a time by default to keep peak memory
bounded. On machines with more RAM, `--batch-size 2` (or a larger value) trades
memory for speed. `--all-at-once` enables the previous maximum-parallelism mode
and may exhaust memory.

**Be warned that building the entire proof development takes over two hours**, and
it is *not* part of CI: CI compiles only a small representative set of proof
targets (the `cpc-proofs` group of `scripts/run-ci.sh`). The current
workarounds:

- Build only what you are working on, one rule at a time:
  `lake build Cpc.Proofs.Rules.<Rule>`.
- `scripts/build-all-cpc-rules.sh` is resumable — Lake caches completed
  targets, so an interrupted run picks up where it left off.
- Run the same representative subset as CI locally with
  `bash scripts/run-ci.sh cpc-proofs`.
- `scripts/check-proof-hygiene.sh` (the `proof-hygiene` CI group) rejects
  `sorry`, `admit` and `axiom` textually without building anything, so an
  unproven rule cannot land silently even though CI does not build every proof.

A full build is still the only way to catch a rule whose proof broke, e.g.
because its statement changed after regenerating the calculus, so it should be
run (for instance overnight) before a release or after a regeneration.

To remove Lake build artifacts, use either of these equivalent commands:

```bash
scripts/clean-build.sh
lake clean
```

## Regenerating the calculus

The `Cpc` package is compiled from the Eunoia definition of CPC rather than
written by hand:

```bash
install/get-eo-compiler.sh                  # once: build the compiler
install/install-cpc.sh <cvc5>/.../Cpc.eo    # regenerate from a signature
scripts/build.sh Cpc                        # check the result
```

Any copy of `Cpc.eo` reachable on the machine can be passed, including one
being edited; no cvc5 *binary* or build is involved. Regenerating from the
version last compiled needs no cvc5 checkout at all:

```bash
install/install-cpc.sh --cached          # regenerate from that version
install/install-cpc.sh --cached --check  # ask whether it still matches
```

A plain run is of `Cpc` alone; `--all` adds `CpcMini`, the reduced package of
the same calculus, which follows the same signature. The `regeneration` CI
group is `--all --cached --check`, and fails when either package has drifted
from the signature it came from.

Regeneration rewrites the signature-wide modules of the package but preserves
the existing per-rule proofs under `Proofs/Rules/`. A rule newly added to CPC
appears as a `sorry` stub, and a rule whose statement changed keeps its old
proof and therefore fails to build — both are the intended signal that a proof
needs attention.

See [`install/README.md`](install/README.md) for more details.

## Using the Logos checker

The `logos` executable reads the s-expression (Eunoia) syntax emitted by
`cvc5 --dump-proofs --proof-format=cpc`:

```bash
lake exe logos test/regress/sexp/test-simple.cpc
```

After building, it can be run directly without invoking Lake:

```bash
./.lake/build/bin/logos test/regress/sexp/test-simple.cpc
```

The executable accepts exactly one proof path and reports one of three outcomes:

| output        | status | meaning                                                                     |
| ------------- | ------ | --------------------------------------------------------------------------- |
| `correct`     | 0      | the proof's assumptions are unsatisfiable, by `correct___logos_check_proof` |
| `incorrect`   | 1      | Logos does not accept the proof as a refutation                             |
| `incomplete`  | 2      | Logos accepts the proof, but it mentions something the specification of SMT-LIB semantics does not model, so the correctness theorem does not apply to it |

Parse and usage errors also exit with status 1. An `incomplete` run explains on
stderr which assumption or command took the proof outside the specified
fragment; see [Correctness](#correctness).

For example, a CPC proof may contain:

```
(declare-const x Int)
(declare-const y Int)
(assume @p0 (= y x))
(assume @p1 (not (= x y)))
(step @p2 :rule symm :premises (@p1))
(step @p3 :rule contra :premises (@p0 @p2))
```

The structure of the parser, the commands and term syntax it supports, and how it lexes
literals are described in [docs/parser.md](docs/parser.md).

Note that Logos has not (yet) been optimized for performance, so it is significantly slower
than performant proof checkers for SMT.

## Correctness

Logos is verified: its soundness is stated and proven in Lean against a specification of
SMT-LIB semantics, so a proof it accepts implies that the assumptions of that
proof are indeed unsatisfiable.
The specification is in two parts. First, the file `./Cpc/SmtModel.lean` formalizes a model semantics of SMT-LIB.
Second, the file `./Cpc/Spec.lean` defines a correspondence between Eunoia terms and SMT-LIB terms
and a definition of satisfiability for Eunoia terms.

The SMT-LIB formalization `./Cpc/SmtModel.lean` is self-contained: it defines the
model semantics of SMT-LIB without reference to the checker.
It includes several non-standard extensions of SMT-LIB (e.g. the theory of sets and the theory of sequences).
It additionally contains operators that are helpful in defining the semantics of existing operators.
This includes total versions of partial arithmetic operators.

The correctness proof for the checker lives in `Cpc/Proofs/Checker.lean`,
whose final theorem `correct___eo_is_refutation` states that
a successfully checked proof in Logos implies that the input assumptions to that proof are indeed unsatisfiable.
This theorem intentionally has two explicit assumptions that state that the given proof uses only terms that
have a corresponding SMT-LIB semantics.
That theorem is proven, as are the correctness proofs of the individual proof rules it relies on.
There are no `sorry`s in the soundness proof or its dependencies.

### From the theorem to the executable

`correct___eo_is_refutation` is stated about an assumption list `F`, a command
list, and two side conditions (`TranslatableAssumptionList F` and
`CmdListTranslationOk`, defined in `Cpc/Proofs/Assumptions.lean`, which restrict
the proof to terms the SMT-LIB formalization gives a meaning to). Its conclusion
is about `argListAssumes F`, the conjunction of that list. Three further
files connect that statement to what the executable actually runs, so that the
`correct` it prints is the theorem's conclusion rather than an informal argument
about it:

- `Cpc/Api.lean` is everything `logos` does with a proof file, as one function
  `Eo.logos_check_proof : String -> Except String Verdict`: parse the text, then
  run the three checks that stand for the theorem's hypotheses — the refutation
  check and the two side conditions.
- `Cpc/ApiChecks.lean` proves that each check gives the component it stands for.
  In particular it proves that folding the guarded assumption push over the
  parser's list builds the same state as `__eo_invoke_assume_list` on the
  corresponding `CArgList`, which is what lets the executable use a fold
  (constant stack) rather than a recursion over the list.
- `Cpc/ApiCorrect.lean` assembles those into `correct___logos_check_proof`,
  stated about the text of a proof file:

  ```lean
  theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
      (hParse : parseProof input = Except.ok (assums, cmds))
      (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
      eo_satisfiability (logos_assumption_term assums) false
  ```

  That is: if the parser reads the assumptions `assums` out of `input`, and
  `logos` prints `correct` for `input`, then their conjunction is unsatisfiable.
  `Main.lean` only reads the file, prints the verdict and picks an exit status.

The side conditions are not re-implemented for the executable to run: they are
the predicates of `Cpc/Proofs/Assumptions.lean`, and that file also derives the
`Decidable` instances that decide them, so the per-rule conditions the rule
proofs assume and the ones the executable checks are one definition, written
down once.

Note that the side conditions are *checked at run time*: computing them needs
the specification's `__eo_to_smt`, so the executable links the specification
layer, even though the checker itself never consults it (the proof rules remain
untyped syntactic manipulations, and the semantics is not used as an oracle).
A proof that Logos accepts but whose side conditions fail is reported as
`incomplete` rather than `correct` — `test/regress/sexp/test-declare-sort.cpc` is
one, since it declares a sort of arity 1 and the specification has no
counterpart for a sort constructor applied to a sort.

What is still outside the theorem: the s-expression reader and the parser
(`Logos/Sexp.lean`, `Logos/Parser.lean`, `Cpc/Parser.lean`) are unverified, so the
assumptions the theorem talks about are whatever they read out of the file, and Logos does not
compare them against an original input problem (`include` and `reference` are
ignored).

**Where the semantics is narrower than SMT-LIB.** On three standard theories the
model semantics admits a smaller class of models than SMT-LIB does: arrays are
almost-constant maps, `Real` is interpreted as the rationals, and uninterpreted
sorts are assumed infinite. Each is confined to quantified or nonlinear
reasoning — on the quantifier-free linear fragments the two agree — and on the
fragments it touches it makes `correct` claim slightly less than *unsatisfiable
in SMT-LIB*. Separately, the semantics extends SMT-LIB with sorts and operators
the standard does not define, sets and sequences among them, where conformance is
not a question that arises; and parametric datatypes are refused outright rather
than mismodeled. [docs/smt-lib-conformance.md](docs/smt-lib-conformance.md) has
all three kinds and what each costs.

The proof of the core checker is agnostic to the proof rules being used, i.e.
the core definition of Logos and its correctness does not depend on the particular rules of the calculus.
The proofs of correctness of each proof rule are contained in `Cpc/Proofs/Rules/`.
The dispatcher which case splits on these rules is in `Cpc/Proofs/RuleLemmas.lean`,
which is also auto-generated based on the calculus.

`scripts/cpc-loc-summary.py` reports the size of each of these pieces — the specification, the
checker, the parser and the correctness proof — in lines of code.

## The name

*Logos* (λόγος) is Greek for an account or a reasoned argument — what somebody
gives when asked to justify a claim rather than restate it. A proof is such an
account, and this checker decides whether one holds. The name is therefore the
thing the tool reads, and not a claim about how well it reads it.

## How this repository is maintained

This repository is part of the **Eunoia ecosystem** and follows its
[shared repository policy](https://github.com/ajreynol/kanon/blob/main/docs/policy.md).
It does not use that ecosystem's channels for AI-directed work: there is no
discussion file and no agent-facing maintenance page here, and anything another
project wants to say to Logos is carried by a person.

**Logos is written and maintained by people.** Everything that decides what a
`correct` verdict *means* — the SMT-LIB model semantics (`Cpc/SmtModel.lean`),
the correctness specification (`Cpc/Spec.lean`), the soundness theorem and the
checker it is about, and the Eunoia definition of the calculus — is written and
understood in full by its human maintainers. No claim Logos makes rests on a
definition no human maintainer has read.

**Two parts are AI generated, and nothing else is.** The per-rule proofs under
`Cpc/Proofs/Rules/` are checked by Lean against statements the maintainers
wrote, and `scripts/check-proof-hygiene.sh` rejects `sorry`, `admit` and
`axiom`, so how a proof was found does not affect what it establishes. The
parser (`Logos/Parser.lean`, `Cpc/Parser.lean`) carries no such guarantee and
none is claimed: it sits outside the correctness theorem, which speaks about the
assumptions the parser reports rather than about the text of the file, so
checking that those are the intended ones remains the user's obligation. See
[Correctness](#correctness).

The s-expression reader `Logos/Sexp.lean` is adapted from
[lean-smt](https://github.com/ufmg-smite/lean-smt), used under Apache 2.0; its
header keeps the upstream copyright notice and author list and records how the
file was modified.

Logos is under active development, and these policies are subject to change.
