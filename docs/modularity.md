# Modularity of the Logos checker

Logos is one checker for one calculus, CPC. But most of its soundness argument
is not about CPC: it is about a stack machine that pushes assumptions and proven
facts, and about invariants that machine maintains. This document records how
far that separation has been taken, what a *second* consumer has to supply, and
what is left to do.

It has two audiences:

- Logos maintainers — the TODO list at the end.
- Anyone building a Logos-like checker for a different calculus (e.g.
  [eudaimonia](https://github.com/ajreynol/eudaimonia)) — the contract in
  [What a new checker supplies](#what-a-new-checker-supplies). Start from
  `CpcMini`, not `Cpc`.

## Current layering

Hand-written proof, in lines, after the split described below. "Reusable" means
a new calculus can take the file essentially as-is.

| layer | files | Cpc | CpcMini | reusable? |
| --- | --- | ---: | ---: | --- |
| checker | `Proofs/{Checker,CheckerState,CheckerCore}.lean`, `Proofs/Invariants/Stability.lean`, `Proofs/RuleSupport/Contract.lean`, `Proofs/Assumptions.lean` | 4,411 | 3,996 | yes, except `Assumptions.lean` |
| common | `Proofs/{Common,CommonBoolOps,TermCompat}.lean` | 1,422 | 836 | mostly |
| translation | `Proofs/Translation*` | 33,463 | 5,167 | no — signature-specific |
| type preservation | `Proofs/TypePreservation*` | 17,700 | 5,633 | no — signature-specific |
| canonical models | `Proofs/Canonical*` | 10,093 | 228 | no — signature-specific |
| closedness / var-model | `Proofs/Closed*` | 32,274 | 0 | only if you have binder rules |
| rule support | `Proofs/RuleSupport/*` | 352,795 | 259 | no — rule-specific |
| rules | `Proofs/Rules/*` | 279,000 (591 files) | 1,209 (5 files) | no |

Everything else — `Logos.lean`, `LogosTerm.lean`, `SmtEval.lean`,
`SmtModel*.lean`, `SmtValueOrder.lean`, `Spec.lean`, `Parser.lean`,
`Proofs/RuleLemmas.lean`, and one stub per rule — is emitted by `ethos-eoc`;
see `install/install-sig.sh`.

**Read that table before planning work.** The checker layer is 4.0K of
CpcMini's ~17.3K hand-written lines (23%), and 4.4K of Cpc's ~730K (0.6%). The
checker layer is now in good shape; the cost of a new checker is dominated by
the *semantics* layer. See TODO 5.

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
`Contract.lean` on the rule side and are deliberately *not* in the checker's
transitive imports.

## What a new checker inherits

`Proofs/Checker.lean` — the ~25 preservation theorems and
`correct___eo_is_refutation` — is **byte-identical between `Cpc` and `CpcMini`**
modulo the package name. It contains:

- zero references to any `CRule` constructor;
- zero references to the stability invariant, or to any other calculus-specific
  invariant;
- three `Term` constructors only: `Stuck`, `Bool`, `Boolean`.

`CheckerState.lean` contains zero occurrences of the string `Invariant`.

The evidence that this is real, not aspirational: `CpcMini` uses Cpc's
`Checker.lean` verbatim while differing in rule set (5 rules vs 591), in
signature, *and* in which invariants its rules require.

`Proofs/CheckerState.lean` is byte-identical too, as of the unforking described
in the next section.

### The hazard that broke it before: generated arm numbers

`CheckerState.lean` had re-forked, by 145 lines, and the interesting half of
that divergence was not sloppiness. Lean names the arms of a generated
definition positionally — `__smtx_model_eval.eq_9` — and **the numbering moves
with the operator set**. The `and` arm of `__smtx_model_eval` is `eq_9` in Cpc
and `eq_7` in CpcMini; `eq_9` in CpcMini is `imp`.

So a checker-layer proof that names an arm number is reusable only by accident.
It does not fail loudly when carried to another signature — it either fails to
rewrite, or, in the bad case, rewrites with the *wrong* arm. That is what made
`CheckerState.lean` and `Proofs/Common.lean` fork in the first place: each
package wrote the proof against its own numbering, and the two texts stopped
being one text.

The fix is one line of discipline: the three arms this layer needs are given
names in `Proofs/Common.lean` —

```lean
theorem typeof_boolean_eq   (b : Bool)                : __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool
theorem typeof_none_eq                                : __smtx_typeof SmtTerm.None = SmtType.None
theorem model_eval_boolean_eq (M : SmtModel) (b : Bool) : __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b
theorem model_eval_and_eq   (M : SmtModel) (a b : SmtTerm) : __smtx_model_eval M (SmtTerm.and a b) = ...
```

— each proved by `rfl`, and the numbers are used nowhere in the layer.
`scripts/check-proof-modularity.sh` keeps it that way (TODO 11). A new checker
should adopt the same rule before its first proof, not after its second package.

## What a new checker supplies

### 1. Signature symbols

The checker layer hard-codes a small number of SMT-LIB symbols. Eunoia does not
guarantee these exist; your signature must declare them.

- **`and`.** `stateAssumes` / `statePushes` / `stateProvens` fold the checker
  stack with it (`Proofs/CheckerState.lean`), and `argListAssumes` folds the
  input assumption list with it (`Proofs/Assumptions.lean`); the conclusion
  `eo_satisfiability (argListAssumes F) false` is a statement about that chain.
  `__eo_invoke_assume_list` itself does not name the operator: it walks the
  input problem as a `CArgList`.
- **`:right-assoc-nil true` on `and`, but only if your rules need it.** This
  document used to state the attribute as a flat requirement. It is not one.
  Compiling CPC with `and` declared as a plain binary operator leaves
  `__eo_invoke_assume_list`, the refutation test and the SMT translation
  **byte-identical**: the core does not use the attribute at all. What the
  attribute buys is the `__eo_nil` arm
  `| (Term.UOp UserOp.and), T => Term.Boolean true`, and that arm is reached
  only where a rule gathers `:list` premises with `and` through
  `__eo_mk_premise_list`. CPC has eleven such call sites; a calculus may have
  none, and one with binary `and` and no `and`-gathered premise lists is fine.
  (Measured on the eudaimonia side; see the cross-reference at the end.)
- **The Bool literals `true` / `false`.** `Term.Boolean` is a builtin `Term`
  constructor so it always exists, but the checker fixes its meaning: `false`
  is the refutation target (`__eo_state_is_refutation` is literally
  `check_proven false`), and `true` is the unit of the assumption conjunction.

`not`, `=` and `imp` are **not** required by the checker. They are used only by
rule proofs, and live in `Proofs/CommonBoolOps.lean`, outside the checker's
transitive imports. A signature declaring none of them can delete that module
without touching anything else.

`imp` was the last to go and was pure accident: `CheckerState.lean` carried five
`eo_interprets_imp_*` lemmas that **nothing in the checker used** — in Cpc they
were one-line forwarders to the `RuleProofs` versions in `Common.lean`, and in
CpcMini they had no users anywhere. Deleting them, and moving Cpc's originals
to `CommonBoolOps.lean`, left the core naming exactly one operator.

**The core of both packages now depends on a single signature symbol: `and`.**

`install/install-sig.sh` checks all of this against what the compiler emitted,
before it installs anything — see TODO 8.

### 2. The SMT semantics side

`__eo_to_smt` must send `and` to `SmtTerm.and` and `Bool` to `SmtType.Bool`.
The checker layer's entire SMT surface is `SmtTerm.and`, `SmtTerm.Boolean`,
`SmtType.Bool` and the `None` cases. A signature that declared `and` but
translated it to something else would compile, would check proofs, and
`correct___eo_is_refutation` would be a statement about the wrong formula.

This is the seam where a mistake is silent, so it is the one requirement whose
check earns its keep on its own: `install/install-sig.sh` greps the generated
`Spec.lean` for the `UserOp.and -> SmtTerm.and` arm and refuses to install
without it.

### 3. The semantics layer

`Translation/`, `TypePreservation/`, `Canonical/` — proofs about the generated
`__eo_to_smt` and `__smtx_typeof` for *your* operators. This is the bulk of the
work and it scales with how many SMT theories you take on: 228 lines of
`Canonical/` in CpcMini against 10,093 in Cpc.

### 4. `cmdTranslationOk`

`Proofs/Assumptions.lean`. Seed it from **CpcMini's** 64-line version, whose
`cmdTranslationOk` is generic (`| CCmd.step _ args _ => cArgListTranslationOk args`)
and names no rule. Cpc's 277-line version is a hand-maintained specialization —
see TODO 1.

### 5. Optionally, an extra invariant

If your rules need something of the proof state beyond "well-typed, translatable,
locally true", supply it through the slot in
`Proofs/Invariants/Stability.lean`:

```lean
abbrev checkerExtraInvariant (M : SmtModel) (s : CState) : Prop := ...
abbrev cmdExtraOk            (M : SmtModel) (c : CCmd)    : Prop := ...
abbrev CmdListExtraOk        (M : SmtModel) (cs : CCmdList) : Prop := ...
abbrev extraAssumptionListOk (M : SmtModel) (F : CArgList) : Prop := ...
```

plus `invoke_cmd_preserves_extraInvariant_nonstuck`. `Checker.lean` is written
against those four names and never mentions what they stand for. A calculus with
no extra invariant points `checkerExtraInvariant` at `fun _ _ => True`.

In CPC the slot holds variable stability, which exists so binder-sensitive rules
(`instantiate`, `skolemize`, `alpha_equiv`) can be given premise truth in a
variable-variant model via `RulePremiseEvidence.true_in_var_model`. CpcMini
defines `StableWhenTrueInAnyVarModel := True` and pays nothing.

**The slot is coupled to `RuleSupport/Contract.lean`.** Adding
`true_in_var_model` to `RulePremiseEvidence` is exactly what makes an extra
invariant load-bearing. Those two choices are made together, up front.

## TODO

Ordered by value to a second consumer.

### 1. Make `cmdTranslationOk` per-rule and generated

`Cpc/Proofs/Assumptions.lean` is a 277-line hand-maintained table naming 32
individual CPC rules. It is the **only** hand-written non-rule file that
mentions a rule, and it appears in the hypothesis of the top-level
`correct___eo_is_refutation`.

Have the rule stub template emit
`def cmd_step_<rule>_args_ok : CArgList → Prop := fun _ => True`, let the proof
author strengthen it in the rule file, and have `ethos-eoc` generate
`cmdTranslationOk` as a dispatch — exactly as it already generates
`cmd_step_proven_facts_of_invariants`. Then no hand-written file in the checker
layer names a rule.

The masks cannot be inferred from the signature: the kind
(`term`/`list`/`type`/`wfTerm`/`wfElem`) is discovered while proving the rule.
So it must be *declared* in the rule file, not derived.

Needs an eoc template change, and a `Decidable` instance per rule so
`Cpc/ApiChecks.lean` can keep discharging it with `decide`.

### 2. Promote the checker layer to eoc templates

`Checker.lean`, `CheckerState.lean`, `RuleSupport/Contract.lean` and a generic
`Assumptions.lean` should be *seeded* into a new package and then owned by it —
the install-once, preserve-if-present treatment that `Proofs/Rules/*.lean`
already gets in `install/install-sig.sh` (see the loop near line 723). Today
they are hand-maintained per package, and they drifted: before being unforked,
Cpc's and CpcMini's `Checker.lean` differed by 376 lines purely because CpcMini
did not need one invariant.

`Checker.lean` needs no parameterization beyond the package name — 25 `Term`
references, zero `CRule`, zero `UserOp`.

### 3. Split `CheckerCore.lean` per invariant

It still holds four invariants, the bundle, and the rule bridge in one file
(1,120 / 1,002 lines). Splitting into `Invariants/{Type,Translation,LocalTruth}.lean`
plus a bundle module would let a consumer replace the *translation* invariant —
relevant if your specification is not "translate to SMT-LIB and interpret".

Low risk: the same split was done for `Stability.lean` by computing the
declaration reference graph, and it had zero generic→invariant violations, so no
proof needed fixing.

### 4. Generalize the extra-invariant slot

`checkerExtraInvariant` is a single slot. A calculus needing two extra invariants
must conjoin them by hand. Making it a list, or documenting the conjunction
idiom, is cheap. Low value until someone hits it.

### 5. Make the semantics layer cheaper — the biggest lever

Cpc: semantics layer 93,530 lines against a 4,411-line checker layer. Whatever
else is done to the checker has bounded returns; **this** is what a new consumer
pays.

Two directions:

- Have `ethos-eoc` emit the translation and type-preservation proofs alongside
  `__eo_to_smt`. They are largely mechanical case analyses over the operator set,
  which is exactly what the compiler already enumerates.
- Share the SMT-LIB half properly. `SmtModel.lean` is a formalization of
  *SMT-LIB*, not of CPC, yet each package gets its own pruned copy (2,186 lines
  in Cpc, 743 in CpcMini). A real shared library with per-package pruning as an
  optimization would let two consumers share the theory proofs.

This is the item most worth coordinating with eudaimonia before they start: if
their signature differs substantially from CPC's, this is the cost they will
actually feel.

**A measured starting point.** Diffing every file the two packages share,
modulo the package name, the semantics layer is not uniformly per-calculus:

| file | Cpc | CpcMini | difference |
| --- | ---: | ---: | --- |
| `Proofs/TypePreservation/Datatypes.lean` | 1,334 | 1,334 | none |
| `Proofs/Canonical/TypeDefaultBasic.lean` | 228 | 228 | none |
| `Proofs/TypePreservation/Nonvacuity.lean` | 104 | 104 | one space of indentation |
| `Proofs/TypePreservation/Predicates.lean` | 21 | 21 | a `simp` lemma CpcMini did not use |
| `Proofs/TypePreservation/Common.lean` | 529 | 529 | one import line |
| `Proofs/TypePreservation/Model.lean` | 208 | 203 | 15 lines |

The first four are now identical and guarded by TODO 11 — about 1,690 lines of
hand-written semantics proof that two calculi can hold in common, which is the
first evidence that the "L (library)" category eudaimonia's roadmap asks for
reaches past the checker layer.

`TypePreservation/Common.lean` is worth a warning, because it looks like a
five-second fix and is not. The two copies differ by exactly one import: Cpc
pulls `Proofs/TermCompat.lean`, CpcMini pulls
`Proofs/TypePreservation/CanonicalAssumptions.lean`, and neither module exists
in the other package. Neither import is used by the 529-line body — but Cpc's
is load-bearing *transitively*: `TermCompat.lean` is where the `@[simp]` lemma
`native_Teq_self` lives, and `Translation/Special.lean` and
`TypePreservation/Full.lean` reach it only through this file. Naming
`TermCompat` directly in those two, which is the right fix on its face, changes
which definitions are exposed and breaks `simp` in `Translation/Apply.lean`
(17,003 lines) on Lean's `import all` visibility rules. Not attempted further;
it needs the module-visibility question settled first, and a full build to
validate.

### 6. Move calculus-independent material into `Logos/`

The `Logos` library is 1,152 lines (`Sexp.lean`, `Parser.lean`). Everything
reusable lives in per-package files instead, because `Term`, `CState` and
`CRule` are generated per package.

Two routes. **(a)** Keep per-package files but generate them from shared
templates — this is TODO 2, and is cheap. **(b)** Parameterize the proofs over
an abstract `Term` — expensive, because `CheckerCore.lean` also depends on the
translation layer and on `UserOp.and`. Recommend (a); do not start with (b).

**One file is already known to be invariant across *signatures*, not merely
across the two packages.** `Cpc/SmtValueOrder.lean` (157 lines) and the
`SmtValueOrder.lean` of eudaimonia's hello-world checker — a different
signature, compiled by a different invocation — differ only in the two import
lines that name the package. Every other cross-package measurement in this
document, and in eudaimonia's roadmap, compares two packages built from the
same signature; this one does not, which makes it the strongest evidence
available that a shared base is real rather than coincidental. It is generated,
so it belongs to TODO 5's second bullet rather than to `Logos/` as such — and
note that the compiler prunes it for small signatures (19 lines for a mini
package), which is exactly the "fixed base, pruning as an optimization" shape
the eudaimonia roadmap argues for.

### 7. Add a fast soundness check to CI — **done**

`Cpc.Proofs.Checker` and `Cpc.ApiCorrect` are deliberately excluded from CI
(`scripts/run-ci.sh`, "Expensive and not currently used in CI checks") because
they need all 591 rule files — roughly two hours. **Changes to `Checker.lean`
are therefore not verified by CI at all.**

`scripts/check-checker-soundness.sh` closes that gap, and now runs inside the
`cpc-proofs` group. It typechecks `Checker.lean` *and* `ApiCorrect.lean` against
the already-built `Proofs/CheckerCore` with the two generated bridge theorems
(`cmd_step_proven_facts_of_invariants`,
`cmd_step_pop_proven_facts_of_invariants`) stubbed by `sorry`. Whole thing runs
in **1.7 seconds** and catches everything except the rule proofs themselves.

Two details that make it trustworthy rather than decorative:

- it reads the two stubbed signatures *out of* `Proofs/RuleLemmas.lean` rather
  than hard-coding them, so a change to the compiler's template fails the check
  instead of silently testing the wrong statement;
- it ends with a canary — a declaration that must be rejected — so the harness
  cannot degrade into a no-op that always passes.

Verified against an injected error: replacing a hypothesis in one proof step of
`Checker.lean` makes it exit 1.

### 8. Check the signature contract explicitly — **done**

`install/install-sig.sh` checks the three requirements against **what the
compiler just emitted**, before anything is installed, and refuses naming what
is missing. It runs in both the `Cpc` and the `CpcMini` install, so the
`regeneration` CI group exercises it twice.

Checking the output rather than the signature text is the point: the name an
operator compiles to need not be its spelling, and `:right-assoc-nil` is
visible only in what it generates. The three checks are that `LogosTerm.lean`
declares `and`, that `Spec.lean` sends it to `SmtTerm.and`, and — conditionally
— that `Logos.lean` has an `__eo_nil` arm for `and` whenever it also calls
`__eo_mk_premise_list (Term.UOp UserOp.and)`.

The design is eudaimonia's, ported here; they implemented this item first and
in doing so found that the `:right-assoc-nil` half of the requirement as this
document stated it was too strong. See
[Signature symbols](#1-signature-symbols), which has been corrected.

Verified against an injected error: making the `and` test look for an operator
no signature declares makes `install-cpc.sh --cached --check` exit 1 with
"no operator `and`, which the soundness statement is about", and install
nothing.

### 9. Split `Closed/Support.lean`

7,917 lines in one file. The **checker layer** reaches it only through
`Invariants/Stability.lean`, which is the point — the rule side reaches it
directly, from `Closed/IsClosedRec.lean` and `RuleSupport/Support.lean`. It
mixes generic closedness machinery with binder/variable-model stability. A
calculus without binders pays nothing for it today, so this is low priority —
but it is a monolith and the natural next `Invariants/` tenant.

### 10. Organize `RuleSupport/`

352,795 lines across 172 files. Four theory-level subdirectories already hold
120,668 of them — `Cong/`, `Evaluate/`, `StrInReConsume/` and `Substitute/` —
and the remaining 232,127 lines sit flat at the top level in 118 files. So the
pattern exists and has not been carried through. Rule-specific, so off the
critical path for modularity, but it is the bulk of the repository.

### 11. Guard the properties this work established — **done**

`scripts/check-proof-modularity.sh`, CI group `proof-modularity`. Textual, no
toolchain, well under a second. Each invariant it checks had drifted at least
once:

- **six files are identical between `Cpc` and `CpcMini`** modulo the package
  name, and the check is table-driven so the set can grow:
  `Proofs/Checker.lean` (diverged by 376 lines before being unforked),
  `Proofs/CheckerState.lean` (145), and four semantics-layer files that turned
  out not to vary with the signature at all —
  `Proofs/TypePreservation/{Datatypes,Nonvacuity,Predicates}.lean` and
  `Proofs/Canonical/TypeDefaultBasic.lean`;
- `Checker.lean` names no `CRule` constructor, no `UserOp`, and no
  calculus-specific invariant;
- `Proofs/CheckerState.lean` contains no occurrence of `Invariant`;
- the checker layer names exactly one `UserOp`, namely `and`;
- **the checker layer names no generated arm by number** — no `.eq_<n>` on
  `__smtx_typeof` or `__smtx_model_eval`. See
  [the hazard](#the-hazard-that-broke-it-before-generated-arm-numbers); this is
  the invariant whose absence caused two of the forks above.

Both new checks were verified against an injected error: perturbing a shared
file, and adding an `.eq_1` to `CheckerCore.lean`, each make the script exit 1.

### 12. Cross-check the soundness proof against the Eudaimonia template

**Not yet — Eudaimonia is in active development.** Recorded so it is not lost.

Once Eudaimonia's `templates/pkg/Proofs/Checker.lean.in` carries content rather
than a description, the same identity check that keeps `Cpc` and `CpcMini` in
agreement should extend across the two repositories: the template and both
Logos packages should be one file modulo the calculus name. That is what would
make the template *the* soundness proof rather than a copy of it, and it is the
natural end state of TODO 2.

One thing blocks it, on the Eudaimonia side and deliberate. Re-checked
2026-09-18 at eudaimonia `f0b1a08`:

- `templates/pkg/Proofs/Checker.lean.in` is 81 lines whose theorem is a
  `sorry`, and `CheckerCore.lean.in` 163 lines that define every invariant as
  `True` and the obligation as a proposition with no constructor. Both are
  larger than they were and neither is proof, so there is still nothing to
  compare against.

**The second blocker is gone.** It was that `get-eo-compiler.sh` had
`DEV_MODE=1` and built the head of `ethosEoc3`, so a cross-repository check
would have compared against a moving target. Their generated checkers now pin
`8dc85c4d` — the ethos 0.2.4 release on `main`, 2026-09-11 — with `DEV_MODE=0`,
and following the tip is a per-run option rather than the default. What a
cross-repository check would compare is now fixed on both sides.

**What has changed is where to start.** `templates/pkg/Proofs/Assumptions.lean.in`
is no longer a stub: it is 122 real lines, seeded from CpcMini's generic
version, with `Decidable` instances and both `ApiChecks.lean` bridge lemmas
proven against it. So the first file to bring under a cross-repository identity
check is `Assumptions.lean`, not `Checker.lean` — it is available now, and it
is the file this document's TODO 1 wants to change, which makes agreement on it
worth establishing before either side moves.

Note also that the two repositories have drifted apart in *layout*, which a
textual check has to reconcile before it can compare anything: eudaimonia's
generated tree has `Proofs/Invariants/Extra.lean` and
`Proofs/RuleSupport/Support.lean` where this one has
`Proofs/Invariants/Stability.lean` and `Proofs/RuleSupport/Contract.lean`.
Theirs are the better names — the slot file should be named for the slot, not
for the CPC invariant that happens to occupy it — and renaming here is cheap
and is a prerequisite for TODO 2.

Until then the in-repo check (TODO 11) covers the property that matters most,
which is that Logos does not re-fork its own soundness proof.

### 13. Push the var-model fields behind the extra-invariant slot

**Ranks with TODO 1 and 2 by value; it is numbered last only to keep the
existing numbers stable, since eudaimonia's roadmap cites them.**

The claim in [Optionally, an extra invariant](#5-optionally-an-extra-invariant)
— that a calculus needing no extra invariant pays nothing — is true of
`Closed/` and false of the core. Two structures in the layer this document
calls reusable hard-code a variable-model notion:

- `Proofs/RuleSupport/Contract.lean:83`, `ContextualTruth`, the predicate
  `Proofs/Checker.lean` is stated against, carries a `true_in_var_model` field
  **in both packages**;
- `Proofs/CheckerCore.lean:1033`, `CmdStepFacts`, carries the same field, also
  in both;
- `model_agrees_on_globals` (`Contract.lean:41`) exists to state them.

So `CpcMini` — no binders, `checkerExtraInvariant := True` — still discharges a
variable-model obligation on every push. Only `RulePremiseEvidence` is
conditional, which is why `Contract.lean` still differs between the packages at
all: 48 lines under the package-name-normalizing diff
`scripts/check-proof-modularity.sh` uses, 34 of them only in Cpc. The field is
the only real one; the rest is declaration order, docstrings and `set_option`.

The fix is to give the slot a fifth and sixth name — an `extraContextualTruth`
and an `extraPremiseEvidence`, `True` by default, defined where
`checkerExtraInvariant` is — and point both structures at them. That would make
`RuleSupport/Contract.lean` byte-identical across the packages, retire the
"decide both up front" coupling warning in section 5, and stop a binder-free
calculus paying for binder machinery. It is the concrete form of TODO 3 and 4.

Not attempted here: it changes `ContextualTruth`, which every rule proof sees
through `StepRuleProperties`, so it needs the full two-hour build to validate
even though only seven files name `true_in_var_model`.

### 14. Unfork `Proofs/Common.lean`

555 lines against CpcMini's 528 and 263 of them differing. A large part of that
was the arm-numbering problem described
[above](#the-hazard-that-broke-it-before-generated-arm-numbers) — Cpc wrote
`__smtx_model_eval.eq_9` where CpcMini wrote `.eq_7` for the same arm — and
that half is now gone: both files name the arms instead, and TODO 11 keeps them
from regressing. What remains is genuine proof-text divergence plus Cpc's
`TermCompat` import. Worth a pass now that the mechanical obstacle is removed;
it is the last file of the checker layer that is forked for no stated reason.

## Cross-reference: the Eudaimonia roadmap

[eudaimonia](https://github.com/ajreynol/eudaimonia)'s `TODO.md`, *Modularizing
Logos — what is actually reusable*, measures the same tree independently and
reaches compatible conclusions. Two of its findings are worth importing here.

**Syntactic independence is not semantic independence.** Compilation
*configures the model*: `SmtModel.lean` is 743 lines in CpcMini and 2,186 in
Cpc, and `Spec.lean` 105 against 475. So a proof file that never names an
operator is still *stated about* an `SmtModel` that varies with the signature.
`Checker.lean` being byte-identical across the two packages therefore buys
**template** reuse, not library reuse — the two files are the same text about
two different types. That is exactly what TODO 2 proposes and what TODO 6(b)
would have to fix; the roadmap is right that stabilizing the SMT-LIB model as a
fixed base which signatures *extend* is the prerequisite for real sharing. It
matches TODO 5 here and should be sequenced first.

**`Term` has no per-operator constructors.** Operators live in the
`UserOp`/`UserOp1`/`UserOp2`/`UserOp3` enums and `Term` is uniform, so core
proofs never pattern-match an individual operator. Parameterizing `Term` over
the op enums with a small class supplying the required operators is therefore
much cheaper than abstracting the term algebra — and since the core is now down
to `and` alone, that class has one member. The roadmap's advice to try it on
`Proofs/Invariants/Stability.lean` first (one operator, self-contained) is
sound.

Two corrections to send back: the required-builtin list in the Eudaimonia
README (`and`, `imp`, `eq`, `not`, `Bool`, `true`, `false`) is stale — `eq` and
`not` were removed, and `imp` since — and the 108 differing lines it measures in
`Invariants/Stability.lean` are necessity rather than duplication: Cpc carries
the real `StableWhenTrueInAnyVarModel` machinery while CpcMini defines it
`True`.

### What came back, and what to send next (2026-08-30)

Both corrections above were accepted there and verified rather than taken on
trust. Two things arrived in return and are now acted on here:

- **The signature contract check**, which they implemented first and which is
  ported into `install/install-sig.sh` — TODO 8, now done. Their measurement
  also corrected this document: `:right-assoc-nil true` is a conditional
  requirement, not a flat one.
- **`Proofs/Assumptions.lean` seeded from CpcMini's generic version**, which is
  what makes it, rather than `Checker.lean`, the file to start TODO 12 on.

One correction to send back: `docs/logos-experience-report.md` records
`Cpc/Proofs/Checker.lean` as 1,063 lines. It is 901, and has been since the
modularization in `ea3c7002`. It is still open; it is restated with the rest
below.

And one finding they will want, because it is the kind of thing only visible
from inside a working development: **do not let a proof name a generated
equation-lemma arm by number.** The numbering is signature-dependent, it is how
two of this repository's forks started, and the template is the right place to
say so — see
[the hazard](#the-hazard-that-broke-it-before-generated-arm-numbers). Their
`templates/pkg/Proofs/` files carry exactly the kind of prose that should carry
it.

### eudaimonia-D12, and why the answer here is a triage rather than a verdict (2026-09-18)

They propose that `Proofs/Checker.lean` take the two rule-bridge theorems —
`cmd_step_proven_facts_of_invariants` and
`cmd_step_pop_proven_facts_of_invariants` — as parameters rather than as an
import of `Proofs/RuleLemmas.lean`, which would make
`correct___eo_is_refutation` conditional on the rule bridge. Their case is that
`scripts/check-checker-soundness.sh` already runs the experiment, and the
module structure should become what the script simulates.

**Their measurement is right, re-derived here at `be479120` rather than taken
on trust.** `Proofs/Checker.lean` is 901 lines and byte-identical across the
two packages modulo the package name; it takes exactly those two names from
`RuleLemmas` and nothing else; the call sites are lines 65, 148, 209 and 343;
4 of its 25 declarations name them directly and 15 of 25 need them
transitively. The 10 that do not are the `typeInvariant` and `shapeInvariant`
family together with the two `localTruthInvariant_of_*` lemmas.

**What the change costs past this file**, which the topic states and is worth
having in one place here. `correct___eo_is_refutation` is named by `Cpc/Api.lean`,
`Cpc/ApiChecks.lean`, `Cpc/ApiCorrect.lean`, `Cpc/Native.lean`,
`Cpc/Native/Correct.lean` and `Cpc/Proofs/Assumptions.lean`. `ApiCorrect.lean`
restates it about the text of a proof file, so the hypotheses thread outward to
`correct___logos_check_proof` and `correct___logos_state_is_refutation` — the
two statements the README's *Correctness* section makes to somebody running the
executable.

**One fact that changes the shape of the trade, and is not in the topic.**
Parameterizing does not put the *unconditional* theorem into CI. Applying the
two bridges still goes through `RuleLemmas.lean`, hence through all 591 rule
proofs, hence through the two-hour build, wherever that application is written
down. What moves is where the unproven boundary is drawn and what the top-level
statement says — not how much of the tree a push verifies. The conditional half
is already verified on every push, in 1.7 seconds, by the script the proposal
cites. That cuts both ways and it is theirs to weigh: it weakens *a consumer
would gain a soundness proof it can build* to *a consumer would gain a soundness
proof it can build, conditional on obligations it still cannot discharge*, and
it strengthens the argument that an import is the weaker way of saying what the
theorem has always meant, since nothing about coverage is being given up.

**Why there is no verdict here.** This is a change to what `correct` claims, and
the README reserves the soundness theorem and the specification of what a
`correct` verdict means to the human maintainers — explicitly not to an agent.
So this section records what was measured and what the change would reach; the
decision the topic asks for is a person's, and neither of the two artifacts its
*Settles when* names can be produced without one.

**Corrections queued for eudaimonia**, both line counts in their tree and
neither urgent:

- `docs/logos-experience-report.md` records `Proofs/Checker.lean` as 1,063
  lines in its summary table. It is 901, which is what the same document says
  in its own `Proofs/Checker.lean` section — so the table disagrees with the
  body rather than with us. First raised 2026-08-30 and still open.
- `docs/eoc-requests.md`, *Seed the checker layer as templates*, records
  `CheckerCore.lean` at 1,123 lines. It is 1,120 in `Cpc` and 1,002 in
  `CpcMini`, and has been since `43732cc5` removed five unused `imp` lemmas.
  This document carried the same stale number and has been corrected. The
  246-line divergence recorded beside it is not reproduced here: the
  package-name-normalizing diff `scripts/check-proof-modularity.sh` uses gives
  180 marked lines and a raw diff 188, so the measures differ rather than the
  trees — worth settling which is meant before either side quotes it again.

## A note on mechanical file splitting

Several TODOs above involve splitting large Lean files. When doing that
programmatically, a declaration scanner must handle: multi-line `/-- … -/`
docstrings, `@[attr]` on the *same* line as the declaration, `set_option … in`
prefixes, and dotted names (`RulePremiseEvidence.instCoeFun` must not be
conflated with `RulePremiseEvidence`). Each of those, missed, produces a file
that either fails to parse or — worse — silently duplicates a declaration into
both outputs.

Assert an exact line partition (`moved + kept + header + trailer == original`),
and afterwards diff every declaration body against the original. Both checks are
cheap and catch what the compiler will not.
