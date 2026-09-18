# Modularity of the Logos checker

Logos is one checker for one calculus, CPC. But most of its soundness argument
is not about CPC: it is about a stack machine that pushes assumptions and proven
facts, and about the invariants that machine maintains. This page records how
far that separation has been taken, what a checker for a *different* calculus
would have to supply, and what is left to do.

Sizes below are rounded, and are not kept exact: they move with every change,
and nothing depends on the precise figure.

## The layers

Hand-written proof only. "Reusable" means a new calculus could take the file
essentially as-is.

| layer | files | Cpc | CpcMini | reusable? |
| --- | --- | ---: | ---: | --- |
| checker | `Proofs/{Checker,CheckerState,CheckerCore}.lean`, `Proofs/Invariants/Stability.lean`, `Proofs/RuleSupport/Contract.lean`, `Proofs/Assumptions.lean` | 4K | 4K | yes, except `Assumptions.lean` |
| common | `Proofs/{Common,CommonBoolOps,TermCompat}.lean` | 1K | 1K | mostly |
| translation | `Proofs/Translation*` | 33K | 5K | no — signature-specific |
| type preservation | `Proofs/TypePreservation*` | 18K | 6K | no — signature-specific |
| canonical models | `Proofs/Canonical*` | 10K | <1K | no — signature-specific |
| closedness / var-model | `Proofs/Closed*` | 32K | — | only with binder rules |
| rule support | `Proofs/RuleSupport/*` | 350K | <1K | no — rule-specific |
| rules | `Proofs/Rules/*` | 280K (591 files) | 1K (5 files) | no |

`Logos.lean`, `LogosTerm.lean`, `SmtEval.lean`, `SmtModel*.lean`,
`SmtValueOrder.lean`, `Spec.lean`, `Parser.lean`, `Proofs/RuleLemmas.lean` and
one stub per rule are emitted by `ethos-eoc` instead; see
[`../install/README.md`](../install/README.md).

**The proportions are the point.** The checker layer is under a quarter of
CpcMini's hand-written proof and well under one percent of Cpc's. It is in good
shape, and what a second checker would actually pay for is the *semantics*
layer.

### Module order

```
Proofs/Common.lean            core semantics predicates (eo_interprets, eo_has_bool_type)
Proofs/Assumptions.lean       input-problem + per-command side conditions
Proofs/RuleSupport/Contract.lean   the checker/rule contract
Proofs/CheckerState.lean      the state machine — no invariant is named here
Proofs/Invariants/Stability.lean   the one optional invariant
Proofs/CheckerCore.lean       the invariants, the bundle, the rule bridge
     ↑ (generated) Proofs/RuleLemmas.lean, Proofs/Rules/*.lean
Proofs/Checker.lean           preservation + correct___eo_is_refutation
```

`Proofs/CommonBoolOps.lean` and the rest of `Proofs/RuleSupport/` hang off
`Contract.lean` on the rule side, and are deliberately *not* in the checker's
transitive imports.

## What is already shared

`Proofs/Checker.lean` — the preservation theorems and
`correct___eo_is_refutation` — is **byte-identical between `Cpc` and `CpcMini`**
modulo the package name. It names no `CRule` constructor, no operator and no
calculus-specific invariant, and it uses three `Term` constructors: `Stuck`,
`Bool` and `Boolean`. `Proofs/CheckerState.lean` is byte-identical too, and
contains no occurrence of `Invariant`.

That this is real rather than aspirational is what `CpcMini` shows: it uses the
same `Checker.lean` verbatim while differing in rule set (5 rules against 591),
in signature, *and* in which invariants its rules need.

`scripts/check-proof-modularity.sh` keeps it that way. Every property it checks
had drifted at least once before it existed.

### The hazard that broke it before: generated arm numbers

`CheckerState.lean` had re-forked, and the interesting half of that divergence
was not sloppiness. Lean names the arms of a generated definition positionally —
`__smtx_model_eval.eq_9` — and **the numbering moves with the operator set**.
The `and` arm of `__smtx_model_eval` is `eq_9` in Cpc and `eq_7` in CpcMini;
`eq_9` in CpcMini is `imp`.

So a checker-layer proof that names an arm number is reusable only by accident.
It does not fail loudly when carried to another signature — it either fails to
rewrite or, in the bad case, rewrites with the *wrong* arm. That is what made
`CheckerState.lean` and `Proofs/Common.lean` fork in the first place: each
package wrote the proof against its own numbering, and the two texts stopped
being one text.

The fix is one line of discipline. The arms this layer needs are given names in
`Proofs/Common.lean` — `typeof_boolean_eq`, `typeof_none_eq`,
`model_eval_boolean_eq`, `model_eval_and_eq` — each proved by `rfl`, and the
numbers are used nowhere in the layer. A new checker should adopt the same rule
before its first proof, not after its second package.

## What a new checker supplies

### 1. Signature symbols

The checker layer hard-codes a small number of SMT-LIB symbols, and Eunoia does
not guarantee they exist.

- **`and`.** `stateAssumes` / `statePushes` / `stateProvens` fold the checker
  stack with it, and `argListAssumes` folds the input assumption list with it;
  the conclusion `eo_satisfiability (argListAssumes F) false` is a statement
  about that chain. `__eo_invoke_assume_list` itself does not name the operator:
  it walks the input problem as a `CArgList`.
- **`:right-assoc-nil true` on `and`, but only if the rules need it.** The core
  does not use the attribute at all — compiling CPC with `and` as a plain binary
  operator leaves `__eo_invoke_assume_list`, the refutation test and the SMT
  translation byte-identical. What the attribute buys is the `__eo_nil` arm for
  `and`, and that is reached only where a rule gathers `:list` premises with
  `and` through `__eo_mk_premise_list`. A calculus with binary `and` and no
  `and`-gathered premise lists is fine.
- **The Bool literals `true` / `false`.** `Term.Boolean` is a builtin so it
  always exists, but the checker fixes its meaning: `false` is the refutation
  target, and `true` is the unit of the assumption conjunction.

`not`, `=` and `imp` are **not** required. They are used only by rule proofs and
live in `Proofs/CommonBoolOps.lean`, outside the checker's transitive imports; a
signature declaring none of them can delete that module without touching
anything else. **The core of both packages depends on a single signature symbol,
`and`.**

### 2. The SMT semantics side

`__eo_to_smt` must send `and` to `SmtTerm.and` and `Bool` to `SmtType.Bool`. The
checker layer's entire SMT surface is `SmtTerm.and`, `SmtTerm.Boolean`,
`SmtType.Bool` and the `None` cases.

This is the seam where a mistake is silent: a signature that declared `and` but
translated it elsewhere would compile, would check proofs, and
`correct___eo_is_refutation` would be a statement about the wrong formula. So
`install/install-sig.sh` checks it — against what the compiler actually emitted
rather than against the signature text — and refuses to install without it.

### 3. The semantics layer

`Translation/`, `TypePreservation/`, `Canonical/`: proofs about the generated
`__eo_to_smt` and `__smtx_typeof` for *your* operators. This is the bulk of the
work, and it scales with how many SMT theories the calculus takes on.

Some of it turns out not to vary with the signature at all.
`Proofs/TypePreservation/{Datatypes,Nonvacuity,Predicates}.lean` and
`Proofs/Canonical/TypeDefaultBasic.lean` are identical between the two packages,
and the modularity check holds them that way — around seventeen hundred lines of
semantics proof that two calculi can share.

One file is invariant across *signatures* rather than merely across the two
packages: `SmtValueOrder.lean` is the same in Cpc as in a checker generated from
an entirely different signature, modulo the import lines. It is generated, so
that belongs to the compiler rather than to a shared library — and the compiler
prunes it for small signatures, which is the "fixed base, pruned as an
optimization" shape a shared SMT-LIB model would want.

### 4. `cmdTranslationOk`

`Proofs/Assumptions.lean`. Seed it from **CpcMini's** version, whose
`cmdTranslationOk` is generic and names no rule. Cpc's is a hand-maintained
specialization — see [What is left to do](#what-is-left-to-do).

### 5. Optionally, an extra invariant

If the rules need something of the proof state beyond "well-typed, translatable,
locally true", it goes through the slot in `Proofs/Invariants/Stability.lean`:
`checkerExtraInvariant`, `cmdExtraOk`, `CmdListExtraOk`, `extraAssumptionListOk`,
plus `invoke_cmd_preserves_extraInvariant_nonstuck`. `Checker.lean` is written
against those names and never mentions what they stand for. A calculus with no
extra invariant points `checkerExtraInvariant` at `fun _ _ => True`.

In CPC the slot holds variable stability, so that binder-sensitive rules
(`instantiate`, `skolemize`, `alpha_equiv`) can be given premise truth in a
variable-variant model. CpcMini defines it `True` and pays nothing.

**The slot is coupled to `RuleSupport/Contract.lean`.** Adding
`true_in_var_model` to `RulePremiseEvidence` is exactly what makes an extra
invariant load-bearing, so those two choices are made together, up front.

## What is left to do

**The semantics layer is the biggest lever, and everything else has bounded
returns.** It dwarfs the checker layer, and it is what a second consumer would
actually pay. Two directions: have `ethos-eoc` emit the translation and
type-preservation proofs alongside `__eo_to_smt`, since they are largely
mechanical case analyses over the operator set the compiler already enumerates;
and share the SMT-LIB half properly, since `SmtModel.lean` is a formalization of
*SMT-LIB* rather than of CPC, yet each package gets its own pruned copy.

The rest, roughly in order of value:

- **Make `cmdTranslationOk` per-rule and generated.** `Cpc/Proofs/Assumptions.lean`
  is a hand-maintained table naming individual CPC rules — the only hand-written
  non-rule file that mentions a rule, and it appears in the hypothesis of
  `correct___eo_is_refutation`. Emitting a per-rule stub the proof author
  strengthens, and generating the dispatch, would leave no hand-written file in
  the checker layer naming a rule. The masks cannot be inferred from the
  signature: the kind is discovered while proving the rule, so it has to be
  declared in the rule file.
- **Seed the checker layer rather than maintaining it per package.**
  `Checker.lean`, `CheckerState.lean`, `RuleSupport/Contract.lean` and a generic
  `Assumptions.lean` want the install-once, preserve-if-present treatment that
  `Proofs/Rules/*.lean` already gets from `install/install-sig.sh`. Today they
  are hand-maintained in each package, and they drifted badly before being
  unforked.
- **Push the var-model fields behind the extra-invariant slot.** `ContextualTruth`
  and `CmdStepFacts` hard-code a variable-model notion in *both* packages, so
  CpcMini — no binders, extra invariant `True` — still discharges a
  variable-model obligation on every push. Giving the slot an
  `extraContextualTruth` and an `extraPremiseEvidence`, `True` by default, would
  make `RuleSupport/Contract.lean` identical across the packages and stop a
  binder-free calculus paying for binder machinery. It changes `ContextualTruth`,
  which every rule proof sees, so it needs a full build to validate.
- **Unfork `Proofs/Common.lean`.** It is the last checker-layer file forked for
  no stated reason. Much of the divergence was the arm-numbering problem above
  and is now gone; what remains is genuine proof-text divergence plus Cpc's
  `TermCompat` import.
- **Split the monoliths.** `CheckerCore.lean` still holds four invariants, the
  bundle and the rule bridge in one file; splitting it per invariant would let a
  consumer replace the *translation* invariant, which matters if the
  specification is not "translate to SMT-LIB and interpret".
  `Closed/Support.lean` mixes generic closedness machinery with binder
  stability. `RuleSupport/` has four theory-level subdirectories and a large
  flat remainder that wants the same treatment.
- **Generalize the extra-invariant slot.** It is a single slot; a calculus
  needing two must conjoin them by hand. Cheap, and low value until somebody
  hits it.

**One trap worth knowing about.** `TypePreservation/Common.lean` differs between
the packages by exactly one import — Cpc pulls `TermCompat.lean`, CpcMini pulls
`CanonicalAssumptions.lean` — and neither is used by the body, which makes it
look like a five-second unfork. Cpc's is load-bearing *transitively*:
`TermCompat.lean` is where a `@[simp]` lemma lives that two other modules reach
only through this file. Naming `TermCompat` directly in those two changes which
definitions are exposed and breaks `simp` in `Translation/Apply.lean` under
Lean's `import all` visibility rules. It needs the module-visibility question
settled first, and a full build to validate.

## A note on mechanical file splitting

Several items above involve splitting large Lean files. Done programmatically, a
declaration scanner must handle multi-line `/-- … -/` docstrings, `@[attr]` on
the *same* line as the declaration, `set_option … in` prefixes, and dotted names
(`RulePremiseEvidence.instCoeFun` must not be conflated with
`RulePremiseEvidence`). Each of those, missed, produces a file that either fails
to parse or — worse — silently duplicates a declaration into both outputs.

Assert an exact line partition (`moved + kept + header + trailer == original`),
and afterwards diff every declaration body against the original. Both checks are
cheap and catch what the compiler will not.
