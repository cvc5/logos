module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public import Cpc.Proofs.RuleSupport.SetsMemberSupport
import all Cpc.Proofs.RuleSupport.SetsMemberSupport
public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Choosing from a nonempty canonical set finds a true entry. -/
private theorem choose_mem_of_ne_empty
    (m : SmtMap) (A : SmtType)
    (hTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool)
    (hCan : __smtx_map_canonical m = true)
    (hDef : __smtx_map_get_default m = SmtValue.Boolean false)
    (hNe : m ≠ SmtMap.default A (SmtValue.Boolean false)) :
    __smtx_map_lookup m
      (native_eval_map_diff m (SmtMap.default A (SmtValue.Boolean false))) =
        SmtValue.Boolean true := by
  have hDiff := RuleProofs.map_diff_selects_model_eval_eq_false_of_default_eq
    m (SmtMap.default A (SmtValue.Boolean false)) A SmtType.Bool
    hTy (by simp [__smtx_typeof_map_value, __smtx_typeof_value])
    hCan (set_empty_map_canonical A) hDef (by decide)
    (by simp [__smtx_model_eval_eq, native_veq, hNe])
  rcases bool_value_canonical
    (SetsMemberSupport.set_map_lookup_bool (i := native_eval_map_diff m
      (SmtMap.default A (SmtValue.Boolean false))) hTy) with ⟨b, hb⟩
  rw [hb]
  rw [__smtx_map_lookup] at hDiff
  erw [hb] at hDiff
  cases b <;> simp_all [__smtx_model_eval_eq, native_veq]

private theorem choose_member_properties
    (M : SmtModel) (hM : model_wf M) (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.set_choose) a)) :
    StepRuleProperties M []
      (__eo_prog_sets_choose_member (Term.Apply (Term.UOp UserOp.set_choose) a)) := by
  have hNN : term_has_non_none_type
      (SmtTerm.map_diff (__eo_to_smt a)
        (SmtTerm.set_empty (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a))))) :=
    hTrans
  obtain ⟨A, hSetTy, hEmptyTy, hChooseTy⟩ : ∃ A,
      __smtx_typeof (__eo_to_smt a) = SmtType.Set A ∧
      __smtx_typeof (SmtTerm.set_empty A) = SmtType.Set A ∧
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) a)) = A := by
    rcases map_diff_args_of_non_none hNN with hMap | hSet
    · rcases hMap with ⟨A, B, hA, hE, _⟩
      rw [smtx_typeof_set_empty_term_eq] at hE
      simp only [__smtx_typeof_guard_wf, native_ite] at hE
      split at hE <;> contradiction
    · rcases hSet with ⟨A, hA, hE, hC⟩
      exact ⟨A, hA, by simpa [hA, __eo_to_smt_set_elem_type] using hE, hC⟩
  have haTrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSetTy]
    simp
  have hMatch : __eo_to_smt_type (__eo_typeof a) = SmtType.Set A :=
    (TranslationProofs.eo_to_smt_typeof_matches_translation a haTrans).symm.trans hSetTy
  let P := __eo_prog_sets_choose_member (Term.Apply (Term.UOp UserOp.set_choose) a)
  have hP : __eo_to_smt P =
      SmtTerm.or (SmtTerm.eq (__eo_to_smt a) (SmtTerm.set_empty A))
        (SmtTerm.or
          (SmtTerm.set_member
            (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty A)) (__eo_to_smt a))
          (SmtTerm.Boolean false)) := by
    simp [P, __eo_prog_sets_choose_member, __eo_mk_apply,
      __eo_to_smt, hMatch, __eo_to_smt_set_empty, hSetTy, __eo_to_smt_set_elem_type]
  have hBool : RuleProofs.eo_has_bool_type P := by
    unfold RuleProofs.eo_has_bool_type
    rw [hP]
    have hChoose : __smtx_typeof
        (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty A)) = A := by
      simpa [__eo_to_smt, hSetTy, __eo_to_smt_set_elem_type] using hChooseTy
    have hMember : __smtx_typeof
        (SmtTerm.set_member
          (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty A)) (__eo_to_smt a)) =
        SmtType.Bool := by
      change __smtx_typeof_set_member
        (__smtx_typeof (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty A)))
        (__smtx_typeof (__eo_to_smt a)) = SmtType.Bool
      rw [hChoose, hSetTy]
      simp [__smtx_typeof_set_member, native_ite, native_Teq]
    simp only [typeof_or_eq, typeof_eq_eq, RuleProofs.typeof_boolean_eq, hSetTy, hEmptyTy, hMember]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type P hBool⟩
  intro _
  apply smt_interprets.intro_true M _ hBool
  rw [hP]
  have hValTy : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
      SmtType.Set A := by
    simpa [hSetTy] using smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt a) haTrans
  rcases set_value_canonical hValTy with ⟨m, hm⟩
  have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
    set_map_value_typed (by simpa [hm] using hValTy)
  have hCan := RuleProofs.model_eval_eo_to_smt_canonical M hM a haTrans
  have hParts : __smtx_map_canonical m = true ∧
      native_veq (__smtx_map_get_default m) (SmtValue.Boolean false) = true := by
    simpa [hm, value_canonical, __smtx_value_canonical, SmtEval.native_and] using hCan
  have hmCan := hParts.1
  have hmDef := eq_of_native_veq_true hParts.2
  have hEvalEmpty : __smtx_model_eval M (SmtTerm.set_empty A) =
      SmtValue.Set (SmtMap.default A (SmtValue.Boolean false)) := by
    rw [__smtx_model_eval.eq_def]
  have hEvalChoose : __smtx_model_eval M
      (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty A)) =
      native_eval_map_diff m (SmtMap.default A (SmtValue.Boolean false)) := by
    rw [__smtx_model_eval.eq_def]
    simp only [hm, hEvalEmpty, __smtx_model_eval_map_diff]
    rfl
  rw [smtx_eval_or_term_eq, smtx_eval_eq_term_eq, smtx_eval_or_term_eq]
  have hMem : __smtx_model_eval M
      (SmtTerm.set_member
        (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty A)) (__eo_to_smt a)) =
      __smtx_map_lookup m
        (native_eval_map_diff m (SmtMap.default A (SmtValue.Boolean false))) := by
    rw [__smtx_model_eval.eq_def]
    simp only [hEvalChoose, hm, __smtx_model_eval_set_member, __smtx_map_select]
  rw [hm, hEvalEmpty, hMem]
  rcases bool_value_canonical
    (SetsMemberSupport.set_map_lookup_bool (i := native_eval_map_diff m
      (SmtMap.default A (SmtValue.Boolean false))) hmTy) with ⟨b, hb⟩
  by_cases hEmpty : m = SmtMap.default A (SmtValue.Boolean false)
  · rw [hb, hEmpty]
    cases b <;> simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval_or,
      __smtx_model_eval, native_or]
  · rw [choose_mem_of_ne_empty m A hmTy hmCan hmDef hEmpty]
    simp [__smtx_model_eval_eq, native_veq, hEmpty, __smtx_model_eval_or,
      __smtx_model_eval, native_or]

public theorem cmd_step_sets_choose_member_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_choose_member args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_choose_member args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_choose_member args premises) :=
by
  intro hCmdTrans _ hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons x args =>
    cases args with
    | cons _ _ => exact False.elim (hProg rfl)
    | nil =>
      cases premises with
      | cons _ _ => exact False.elim (hProg rfl)
      | nil =>
        have hTrans : RuleProofs.eo_has_smt_translation x := by
          simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
        change __eo_prog_sets_choose_member x ≠ Term.Stuck at hProg
        cases x <;> try simp [__eo_prog_sets_choose_member] at hProg
        next f a =>
          cases f <;> try simp at hProg
          next op =>
            by_cases hOp : op = UserOp.set_choose
            · subst op
              exact choose_member_properties M hM a hTrans
            · simp [hOp] at hProg
