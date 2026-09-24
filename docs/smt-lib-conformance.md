# Conformance to SMT-LIB

Logos's soundness theorem is stated against `Cpc/SmtModel.lean`, a formalization
of SMT-LIB semantics written independently of the checker. It parts company with
SMT-LIB in three ways, and they are different kinds of thing:

- **Narrowings.** On three standard theories — arrays, `Real`, and uninterpreted
  sorts — the semantics admits fewer models than SMT-LIB does. These change what
  `correct` claims, and are most of this page.
- **Extensions.** Sets and sequences are not in SMT-LIB at all, and neither are
  the auxiliary operators the semantics adds. Conformance is not defined for
  them, so nothing here is measured against the standard.
- **Refusals.** Parametric datatypes are rejected rather than interpreted, which
  costs coverage and nothing else.

**None of them is a gap in the proof.** The theorem is proven, and it says what
it says about the semantics it is stated against. What the narrowings record is
that the model class is slightly smaller than SMT-LIB's, so `correct` claims
slightly less than the words *these assumptions are unsatisfiable* are normally
taken to mean. Each is confined to quantified or nonlinear reasoning; on the
quantifier-free linear fragments the two agree.

## What `correct` means, exactly

Unsatisfiability in the specification is *false under every well-formed model*
(`smt_satisfiability` in `Cpc/SmtModel.lean`), where a model assigns each symbol
a value of the right SMT type (`model_wf`, in the same file), and the values
available at a type are the inhabitants of `SmtValue` at that type.

That value inductive is where the narrowing happens. Read on the standard
theories alone, every model of this semantics is an SMT-LIB model, and not every
SMT-LIB model is one of these — so

> SMT-LIB says unsatisfiable **⟹** Logos says unsatisfiable, and not the reverse.

The consequence worth stating plainly: a formula that is satisfiable in SMT-LIB
only by a model this semantics cannot express is treated here as
unsatisfiable. Nothing in the checker will notice, because the restriction is in
what a model *is*, not in what a term means, so no `incomplete` verdict fires.
The channel by which that could produce a wrong `correct` is a CPC rule that is
sound for this model class and unsound for SMT-LIB's: its Lean proof would go
through, and proofs using it would be accepted.

| narrowing | this semantics | SMT-LIB | where it bites |
| --- | --- | --- | --- |
| arrays are almost constant | a default plus finitely many overrides | the full function space | quantifiers over arrays or indices |
| `Real` is the rationals | ℚ | ℝ | nonlinear real arithmetic |
| uninterpreted sorts are infinite | one countably infinite domain per sort | any nonempty cardinality | quantified cardinality constraints |

## Arrays are almost-constant maps

An array value is `SmtMap`, which is `default T v` overridden at finitely many
points by `cons k v m` (`Cpc/SmtModelDefs.lean`). So every array in every model
is constant except at finitely many indices, where SMT-LIB's `ArraysEx`
interprets `(Array I E)` as the whole function space from `I` to `E`.

It bites where a formula forces an array that is not almost constant:

```smt2
(declare-const a (Array Int Int))
(assert (forall ((i Int)) (= (select a i) i)))
```

satisfiable in SMT-LIB by the identity, and false under every model here.

It does not bite on quantifier-free array formulas, where a satisfiable formula
has an almost-constant model — the same property array decision procedures are
built on.

## `Real` is interpreted as the rationals

`SmtValue.Rational` (`Cpc/SmtModelDefs.lean`) carries a `native_Rat`, which is
Lean's `Rat` (`Cpc/SmtEval.lean`), and it is the only numeric value at type
`Real`. The reals of every model are therefore exactly ℚ, and quantification
over `Real` ranges over ℚ.

It bites in nonlinear arithmetic, where a solution may be irrational:

```smt2
(declare-const x Real)
(assert (= (* x x) 2.0))
```

satisfiable in SMT-LIB, and false under every model here.

It does not bite on linear real arithmetic, where a satisfiable formula always
has a rational solution.

## Uninterpreted sorts are assumed infinite

A value of an uninterpreted sort is `UValue i n` for a natural `n`
(`Cpc/SmtModelDefs.lean`), and every such value has type `USort i`
(`__smtx_typeof` in `Cpc/SmtModel.lean`), so each uninterpreted sort is
interpreted as a countably infinite domain. SMT-LIB allows any nonempty
cardinality, finite included. The write-up states the assumption; nothing
enforces or checks it.

It bites on quantified cardinality constraints:

```smt2
(declare-sort U 0)
(declare-const x U) (declare-const y U) (declare-const z U)
(assert (forall ((a U) (b U) (c U)) (or (= a b) (= a c) (= b c))))
```

which bounds `U` at two elements: satisfiable in SMT-LIB, false under every model
here. Quantifier-free formulas are unaffected, since a satisfiable one always has
an infinite model.

## Extensions: what the standard does not define

Sets and sequences are cvc5 extensions rather than SMT-LIB theories, and the
standard `String` sort is modeled here as a sequence over a `Char` sort the
standard does not have. The semantics also carries auxiliary operators of its
own: total division and modulus, purification, and the difference witnesses for
arrays and sequences. **There is no SMT-LIB meaning for any of these to differ
from**, so the reference for them is CPC's meaning, not the standard's, and the
proofs of the rules that use them are what ties the two together.

Two facts about them are worth knowing anyway. Every set value is finite
(canonicity forces the map default to `false`, in `Cpc/SmtModel.lean`), which
the available set operators preserve; and out-of-bounds `seq.nth` is
underspecified through a model-dependent function, `@oob_seq_nth`, in the same
way SMT-LIB underspecifies partial standard operators.

## A coverage limit, not a semantic one: parametric datatypes

Parametric datatypes are refused, not mismodeled. Both the sort list and a `par`
body are rejected during parsing, in `Logos/Parser.lean`, with `parametric
datatype ... is not supported`, and the run exits 1 without a verdict. The generic parser can
read them, but CPC does not yet give them a representation to be read into;
[`parametric-datatypes.md`](parametric-datatypes.md) is the plan for doing so, which leaves the
model semantics as it is.

This costs coverage and nothing else: a proof over parametric datatypes is not
checked, rather than checked against the wrong meaning.

A parametric *sort* is refused later and more gently: `(declare-sort U 1)` parses,
and an application of it has no counterpart in the specification, so the side
conditions fail and the run reports `incomplete` rather than `correct`.
`test/regress/sexp/test-declare-sort.cpc` is that case.

## What is faithful, and is easy to assume otherwise

- **Division by zero, `mod` by zero and real division by zero** are
  underspecified exactly as SMT-LIB requires: each evaluates by applying a
  model-dependent function (`@div_by_zero`, `@mod_by_zero`, `@qdiv_by_zero`), so
  models disagreeing about `(div 1 0)` are all admitted, and nothing here fixes a
  value for it.
- **The character alphabet** is SMT-LIB's, code points `0` to `196607`
  (`native_char_valid`, `Cpc/SmtEval.lean`).
- **Uninterpreted functions** get the full function space, not the almost-constant
  restriction arrays carry.

## Where this is written down elsewhere

The write-up, [`smt-model-definitions.pdf`](smt-model-definitions.pdf), states the
same three kinds in its introduction and then each narrowing again at the
definition that introduces it — arrays under the type constructors and again
where maps are defined, the rational assumption where values are introduced, and
the cardinality assumption where uninterpreted sort values are. The parser's
refusal is in [`parser.md`](parser.md). This page is the list as it matters to
somebody running the checker; the write-up is where the definitions and their
reasoning are.
