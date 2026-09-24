module

public import Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
import all Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# CPC rule `instantiate` — proof scaffold

The `instantiate` rule has one premise, a universally quantified formula, and one
argument, a list of instantiation terms:

```
premise:  (forall (x1 T1) ... (xn Tn) F)
arg:      ts = [t1, ..., tn]
conclude: F[x1 ↦ t1, ..., xn ↦ tn]
```

Operationally the conclusion is `__substitute_simul_rec false F xs ts nil`
(see `__eo_prog_instantiate`, `Cpc/Logos.lean:3775`).

The soundness obligation (`StepRuleProperties.facts_of_true`) is:

> if `(forall xs F)` interprets `true` in `M`, then `F[xs ↦ ts]` interprets `true` in `M`.

The proof factors into four pieces, in dependency order:

1. **`pushSubstModel`** — the model that assigns each bound variable `xᵢ:Tᵢ` the
   value of `tᵢ` evaluated in the *ambient* `M` (simultaneous substitution: the
   `tᵢ` see `M`, not the partially-extended model).

2. **`substitute_simul_eval`** (THE semantic crux, DONE) — evaluating the translation of
   the substituted body in `M` equals evaluating the translation of `F` in
   `pushSubstModel M xs ts`. This is the capture-avoiding substitution /
   coincidence lemma, proved by structural induction. See the doc comment on the
   lemma for the case breakdown and the `bvs`-generalisation it needs. The
   per-case machinery (`SubstFalseRel`, `substFalse_eval_var`, `substFalseRel_push`)
   already lives in `Cpc/Proofs/Closed/Substitute.lean`; what remains is the
   well-founded recursion tying them together (analogous to
   `smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt`).

3. **`instantiate_body_true`** (DONE) — from `forall xs F` true and the
   well-typedness of `ts`, the body is true under `pushSubstModel M xs ts`.
   The well-typedness of the actuals is exactly what the checker's
   `__is_instantiation xs ts = true` guard certifies: it requires
   `__eo_typeof tᵢ = Tᵢ` for each binder. `substActualsHaveSmtTypes_of_is_instantiation`
   reflects that guard into `SubstActualsHaveSmtTypes`, and
   `instantiate_body_true` calls the push-total body-truth bridge directly.
   `prog_instantiate_shape` exposes the guard from the checker.

4. **`prog_instantiate_shape`** (DONE) — a non-`Stuck` result forces the
   premise to be `forall xs F`, pins the conclusion to the substitution, AND
   exposes the `__is_instantiation xs ts = true` guard (the `__eo_requires`
   wrapper around `__substitute_simul_rec` collapses only when the guard holds).

Status (2026-06-29):
  * `prog_instantiate_shape`  — PROVEN (now also returns the `__is_instantiation`
    fact; previously this proof was broken because it ignored the guard wrapper).
  * `instantiate_body_true`   — PROVEN (via the `__is_instantiation` reflection).
  * `instantiate_sound`       — PROVEN, using `substitute_simul_eval`.
  * main theorem `hWf`        — PROVEN (premise is Bool-typed ⇒ translatable).
  * `substFalse_eval_gen_lt`  — general substitution-eval induction. PROVEN:
    variable / atom / `Stuck`; 9 unary heads (not, to_real, to_int, is_int, abs,
    uneg, int_pow2, int_log2, purify) via `substFalse_eval_unary_op`; 18 binary
    heads (and, or, imp, xor, eq, plus, neg, mult, lt, leq, gt, geq, div, mod,
    select, divisible, div_total, mod_total) via
    `substFalse_eval_binary_op` — div/mod use a `SubstFalseRel.globals`-
    aware congruence (their eval reads `native_div_by_zero_id` from the model).
    The special-head, generic application, and binder/quantifier cases are now
    proved. The quant case reduces, via
    `smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq`-style chain congruence
    (but a *different-body* variant: `toSmt (subst a)` vs `toSmt a`) threaded with
    `SubstituteSupport.substFalseRel_push` per binder (its `hNoCollide`
    discharged by `eo_to_smt_type_injective_of_field_wf_rec`), to the body IH.
    This is the reusable core of the crux.
  * `substitute_simul_eval`   — PROVEN via `substFalse_eval_gen_lt`
    plus the `SubstFalseRel M (pushSubstModel …) xs ts nil` base relation.
  * `substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck_lt`
    now lives in `Cpc.Proofs.RuleSupport.SubstitutePreservationSupport` and is
    the instantiate-facing staging theorem for merging the old type-preservation
    and SMT-translatability structural inductions. The instantiate-facing
    projection wrappers and old recursive engines have been removed from Lean's
    environment; callers use the combined theorem directly. The remaining
    generic application/operator-spine fallback holes now live in the combined
    theorem instead of through the retired standalone engines.

The main theorem then wires these together with the standard single-arg /
single-premise boilerplate (mirrors `BooleanElimSupport.cmd_step_and_elim_properties`).
-/

namespace InstantiateRule

/--
The checker's `__is_instantiation xs ts = true` guard exactly reflects the
predicate `SubstActualsHaveSmtTypes`: it certifies that `ts` matches `xs` in
length and that each actual `tᵢ` has EO type equal to the binder type `Tᵢ`.
Combined with elementwise translatability of `ts` and well-formedness of the
binder SMT types, this yields the well-typed-actuals record the substitution
soundness lemmas consume. -/
theorem substActualsHaveSmtTypes_of_is_instantiation
    {xs ts : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hIsInst : __is_instantiation xs ts = Term.Boolean true) :
    SubstActualsHaveSmtTypes xs ts := by
  induction hEnv generalizing ts with
  | nil => exact SubstActualsHaveSmtTypes.nil ts
  | cons hTail ih =>
      rename_i s T env tailVars
      cases ts with
      | Apply f ts' =>
          cases f with
          | Apply g t =>
              cases g with
              | __eo_List_cons =>
                  rcases hTs with ⟨hHeadTrans, hTailTrans⟩
                  have hReq :
                      __is_instantiation
                          (Term.Apply (Term.Apply Term.__eo_List_cons
                            (Term.Var (Term.String s) T)) env)
                          (Term.Apply (Term.Apply Term.__eo_List_cons t) ts') =
                        __eo_requires (__eo_typeof t) T
                          (__is_instantiation env ts') := rfl
                  rw [hReq] at hIsInst
                  have hNeStuck :
                      __eo_requires (__eo_typeof t) T
                          (__is_instantiation env ts') ≠ Term.Stuck := by
                    rw [hIsInst]; decide
                  have hTypeofT : __eo_typeof t = T :=
                    instantiate_eo_requires_arg_eq_of_ne_stuck hNeStuck
                  have hTailInst :
                      __is_instantiation env ts' = Term.Boolean true := by
                    rw [← instantiate_eo_requires_result_eq_of_ne_stuck hNeStuck]
                    exact hIsInst
                  have hMatch :
                      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T := by
                    rw [TranslationProofs.eo_to_smt_typeof_matches_translation t
                      hHeadTrans, hTypeofT]
                  exact SubstActualsHaveSmtTypes.cons
                    (hWf s T (List.Mem.head _))
                    hHeadTrans hMatch
                    (ih (fun s' T' hMem => hWf s' T' (List.Mem.tail _ hMem))
                      hTailTrans hTailInst)
              | _ => simp [EoListAllHaveSmtTranslation] at hTs
          | _ => simp [EoListAllHaveSmtTranslation] at hTs
      | __eo_List_nil =>
          have hStuck :
              __is_instantiation
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  Term.__eo_List_nil = Term.Stuck := rfl
          rw [hStuck] at hIsInst
          cases hIsInst
      | _ => simp [EoListAllHaveSmtTranslation] at hTs

/--
From `(forall xs F)` true in `M` and well-typed instantiation terms `ts`, the
body `F` is true under the substitution model `pushSubstModel M xs ts`. The
well-typedness of the actuals (`SubstActualsHaveSmtTypes`) is exactly what the
checker's `__is_instantiation` guard certifies; see
`substActualsHaveSmtTypes_of_is_instantiation`. -/
theorem instantiate_body_true
    (M : SmtModel) (hM : model_wf M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) = SmtValue.Boolean true :=
  instantiate_body_true_of_push_total_and_closedIn M hM xs F ts hPrem hWf
    (pushSubstModel_total_typed_of_smt_typed_actuals M hM hActuals)
    (SmtTermClosedIn.exists_env (__eo_to_smt F))

/--
A non-`Stuck` result of `__eo_prog_instantiate` forces the premise to be a
`forall` and pins the conclusion to the substituted body. -/
theorem prog_instantiate_shape
    (ts prem : Term)
    (hNe : __eo_prog_instantiate ts (Proof.pf prem) ≠ Term.Stuck) :
    ∃ xs F,
      prem = Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F ∧
      __is_instantiation xs ts = Term.Boolean true ∧
      __eo_prog_instantiate ts (Proof.pf prem) =
        __substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil := by
  cases prem with
  | Apply f F =>
      cases f with
      | Apply g xs =>
          cases g with
          | UOp op =>
              cases op with
              | «forall» =>
                  -- `__eo_prog_instantiate` wraps the substitution in a
                  -- `__is_instantiation` capture/type guard; a non-`Stuck`
                  -- result forces that guard, collapsing `requires` to the
                  -- substitution itself, and pins `__is_instantiation` to `true`.
                  have hProgEq :
                      __eo_prog_instantiate ts
                          (Proof.pf
                            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) =
                        __eo_requires (__is_instantiation xs ts) (Term.Boolean true)
                          (__substitute_simul_rec (Term.Boolean false) F xs ts
                            Term.__eo_List_nil) := by
                    cases ts <;> first | rfl | exact absurd rfl hNe
                  rw [hProgEq] at hNe
                  refine ⟨xs, F, rfl, ?_, ?_⟩
                  · exact instantiate_eo_requires_arg_eq_of_ne_stuck hNe
                  · rw [hProgEq]
                    exact instantiate_eo_requires_result_eq_of_ne_stuck hNe
              | _ => cases ts <;> exact absurd rfl hNe
          | _ => cases ts <;> exact absurd rfl hNe
      | _ => cases ts <;> exact absurd rfl hNe
  | _ => cases ts <;> exact absurd rfl hNe

/--
Soundness core: if the premise `(forall xs F)` is true in `M`, the conclusion
`F[xs ↦ ts]` is true in `M`. Combines `instantiate_body_true` and
`substitute_simul_eval`, plus the `Bool`-typedness of the result to package as
`eo_interprets`. -/
theorem instantiate_sound
    (M : SmtModel) (hM : model_wf M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hResBool : RuleProofs.eo_has_bool_type
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) :
    eo_interprets M
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) true := by
  -- chain: subst-eval ▸ body-true, then repackage with hResBool
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
        SmtValue.Boolean true := by
    have hFTrans : RuleProofs.eo_has_smt_translation F :=
      forall_body_has_smt_translation_of_has_smt_translation xs F hWf
    have hSubstTrans :
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) F xs ts
            Term.__eo_List_nil) :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type _ hResBool
    rw [substitute_simul_eval M hM F xs ts
      hFTrans hTs hActuals hSubstTrans]
    exact instantiate_body_true M hM xs F ts hPrem hWf hActuals
  have hTy :
      __smtx_typeof
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
        SmtType.Bool := hResBool
  exact smt_interprets.intro_true M _ hTy hEval

end InstantiateRule
