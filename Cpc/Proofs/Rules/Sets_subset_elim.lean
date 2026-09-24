module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm
open SetsMemberSupport
open SetsBasicRewritesSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def setsSubsetElimFormula (x y : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_subset x) y))
    (Term.Apply
      (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x) y))
      y)

private theorem prog_sets_subset_elim_eq_of_ne_stuck
    {x y : Term}
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck) :
    __eo_prog_sets_subset_elim x y = setsSubsetElimFormula x y := by
  cases x <;> cases y <;> simp [__eo_prog_sets_subset_elim, setsSubsetElimFormula]
    at hx hy ⊢

private theorem setsSubsetElim_eo_arg_types
    {x y : Term}
    (hTy : __eo_typeof (setsSubsetElimFormula x y) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T ∧
          T ≠ Term.Stuck := by
  -- The outer formula is (= (subset x y) rhs) with rhs = (= (union x y) y).
  have hTy' :
      __eo_typeof
        (SetsBasicRewritesSupport.mkEq
          (Term.Apply (Term.Apply Term.set_subset x) y)
          (Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x) y))
            y)) = Term.Bool := by
    simpa [setsSubsetElimFormula, SetsBasicRewritesSupport.mkEq] using hTy
  rcases eo_typeof_set_subset_eq_bool_info hTy' with ⟨T, hxTy, hyTy, _hRhsTy, hTNS⟩
  exact ⟨T, hxTy, hyTy, hTNS⟩

private theorem typed___eo_prog_sets_subset_elim_impl
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : __eo_typeof (__eo_prog_sets_subset_elim x y) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sets_subset_elim x y) := by
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hyNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hProgEq :
      __eo_prog_sets_subset_elim x y = setsSubsetElimFormula x y :=
    prog_sets_subset_elim_eq_of_ne_stuck hxNe hyNe
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hFormulaTy :
      __eo_typeof (setsSubsetElimFormula x y) = Term.Bool := by
    rw [hProgEq] at hTy
    exact hTy
  rcases setsSubsetElim_eo_arg_types (x := x) (y := y) hFormulaTy with
    ⟨T, hxTy, hyTy, _hTNS⟩
  have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hxTrans
    have hxSet :
        __smtx_typeof (__eo_to_smt x) =
          __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) := by
      rw [hxMatch, hxTy]
    rw [hxSet] at hxTrans
    intro hNone
    apply hxTrans
    simp [__eo_to_smt_type,
      __smtx_typeof_guard, native_ite, native_Teq, hNone]
  have hxSmtTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hxTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hxMatch
  have hySmtTy :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hyTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hyMatch
  rw [hProgEq]
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.set_subset (__eo_to_smt x) (__eo_to_smt y))
          (SmtTerm.eq
            (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y))
            (__eo_to_smt y))) = SmtType.Bool
  simp [typeof_eq_eq, typeof_set_subset_eq, typeof_set_union_eq,
    __smtx_typeof_sets_op_2, __smtx_typeof_sets_op_2_ret,
    __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
    hxSmtTy, hySmtTy]

private theorem facts___eo_prog_sets_subset_elim_impl
    (M : SmtModel) (hM : model_wf M)
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : __eo_typeof (__eo_prog_sets_subset_elim x y) = Term.Bool) :
    eo_interprets M (__eo_prog_sets_subset_elim x y) true := by
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_sets_subset_elim x y) :=
    typed___eo_prog_sets_subset_elim_impl x y hxTrans hyTrans hTy
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hyNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hProgEq :
      __eo_prog_sets_subset_elim x y = setsSubsetElimFormula x y :=
    prog_sets_subset_elim_eq_of_ne_stuck hxNe hyNe
  have hFormulaTy :
      __eo_typeof (setsSubsetElimFormula x y) = Term.Bool := by
    rw [hProgEq] at hTy
    exact hTy
  rcases setsSubsetElim_eo_arg_types (x := x) (y := y) hFormulaTy with
    ⟨T, hxTy, hyTy, _hTNS⟩
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hxTrans
    have hxSet :
        __smtx_typeof (__eo_to_smt x) =
          __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) := by
      rw [hxMatch, hxTy]
    rw [hxSet] at hxTrans
    intro hNone
    apply hxTrans
    simp [__eo_to_smt_type,
      __smtx_typeof_guard, native_ite, native_Teq, hNone]
  have hxSmtTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hxTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hxMatch
  have hySmtTy :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hyTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hyMatch
  have hxEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hxSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hxTrans)
  have hyEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hySmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hyTrans)
  rcases set_value_canonical (v := __smtx_model_eval M (__eo_to_smt x))
      (A := __eo_to_smt_type T) hxEvalTy with ⟨mx, hxVal⟩
  rcases set_value_canonical (v := __smtx_model_eval M (__eo_to_smt y))
      (A := __eo_to_smt_type T) hyEvalTy with ⟨my, hyVal⟩
  have hMxTy :
      __smtx_typeof_map_value mx = SmtType.Map (__eo_to_smt_type T) SmtType.Bool :=
    set_map_value_typed (by simpa [hxVal] using hxEvalTy)
  have hMyTy :
      __smtx_typeof_map_value my = SmtType.Map (__eo_to_smt_type T) SmtType.Bool :=
    set_map_value_typed (by simpa [hyVal] using hyEvalTy)
  have hXCanEval :
      value_canonical (__smtx_model_eval M (__eo_to_smt x)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM x hxTrans
  have hYCanEval :
      value_canonical (__smtx_model_eval M (__eo_to_smt y)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM y hyTrans
  have hXCanSet : value_canonical (SmtValue.Set mx) := by
    simpa [hxVal] using hXCanEval
  have hYCanSet : value_canonical (SmtValue.Set my) := by
    simpa [hyVal] using hYCanEval
  have hMxCan : __smtx_map_canonical mx = true := by
    have hParts := hXCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact hParts.1
  have hMyCan : __smtx_map_canonical my = true := by
    have hParts := hYCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact hParts.1
  have hMxDef : __smtx_map_get_default mx = SmtValue.Boolean false := by
    have hParts := hXCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact eq_of_native_veq_true hParts.2
  have hMyDef : __smtx_map_get_default my = SmtValue.Boolean false := by
    have hParts := hYCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact eq_of_native_veq_true hParts.2
  -- The core equivalence: subset evaluates as (= (inter x y) x);
  -- the rewrite gives (= (union x y) y); these coincide.
  have hVeqEq :
      native_veq (__smtx_set_inter (SmtValue.Set mx) (SmtValue.Set my))
          (SmtValue.Set mx) =
        native_veq (__smtx_set_union (SmtValue.Set mx) (SmtValue.Set my))
          (SmtValue.Set my) :=
    set_subset_inter_eq_union_veq hMxTy hMyTy hMxCan hMyCan hMxDef hMyDef
  let lhs := Term.Apply (Term.Apply Term.set_subset x) y
  let rhs :=
    Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x) y)) y
  have hProgBool' : RuleProofs.eo_has_bool_type (setsSubsetElimFormula x y) := by
    simpa [hProgEq] using hProgBool
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [setsSubsetElimFormula, lhs, rhs] using hProgBool'
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change
      __smtx_model_eval M (SmtTerm.set_subset (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval M
          (SmtTerm.eq
            (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y))
            (__eo_to_smt y))
    simp only [__smtx_model_eval, __smtx_model_eval_set_subset,
      __smtx_model_eval_set_inter, __smtx_model_eval_set_union,
      hxVal, hyVal]
    -- LHS: eq (inter mx my) mx ; RHS: eq (union mx my) my
    rw [show
        __smtx_model_eval_eq (__smtx_set_inter (SmtValue.Set mx) (SmtValue.Set my))
            (SmtValue.Set mx) =
          SmtValue.Boolean
            (native_veq (__smtx_set_inter (SmtValue.Set mx) (SmtValue.Set my))
              (SmtValue.Set mx)) by
        cases hI : __smtx_set_inter (SmtValue.Set mx) (SmtValue.Set my) <;>
          simp [__smtx_model_eval_eq, native_veq]]
    rw [show
        __smtx_model_eval_eq (__smtx_set_union (SmtValue.Set mx) (SmtValue.Set my))
            (SmtValue.Set my) =
          SmtValue.Boolean
            (native_veq (__smtx_set_union (SmtValue.Set mx) (SmtValue.Set my))
              (SmtValue.Set my)) by
        cases hU : __smtx_set_union (SmtValue.Set mx) (SmtValue.Set my) <;>
          simp [__smtx_model_eval_eq, native_veq]]
    rw [hVeqEq]
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))
  rw [hProgEq]
  simpa [setsSubsetElimFormula, lhs, rhs] using
    RuleProofs.eo_interprets_eq_of_rel M lhs rhs hEqBool hRel

public theorem cmd_step_sets_subset_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_subset_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_subset_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_subset_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_subset_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_sets_subset_elim a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_sets_subset_elim a1 a2) true
                    exact facts___eo_prog_sets_subset_elim_impl M hM a1 a2 hA1Trans
                      hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_sets_subset_elim_impl a1 a2 hA1Trans hA2Trans
                        hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
