module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo SmtEval Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private def insertTerm (x s : Term) : Term :=
  Term.Apply (Term.Apply Term.set_insert x) s

private def unionTerm (x s : Term) : Term :=
  Term.Apply (Term.Apply Term.set_union (Term.Apply Term.set_singleton x)) s

private def eqTerm (x s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (insertTerm x s)) (unionTerm x s)

private theorem insert_arg_types {A B : Term}
    (h : __eo_typeof_set_insert A B ≠ Term.Stuck) :
    ∃ T, A = T ∧ B = Term.Apply (Term.UOp UserOp.Set) T := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_insert] at h
  · cases B <;> simp [__eo_typeof_set_insert, hA] at h ⊢
    rename_i f T
    cases f <;> simp [__eo_typeof_set_insert, hA] at h ⊢
    rename_i op
    cases op <;> simp [__eo_typeof_set_insert, hA] at h ⊢
    have hReq : __eo_requires (__eo_eq A T) (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.Set) A) ≠ Term.Stuck := by
      simpa [__eo_typeof_set_insert, hA] using h
    exact support_eq_of_eo_eq_true A T
      (support_eo_requires_cond_eq_of_non_stuck hReq)

private theorem typed_insert_eq (x s : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hs : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (eqTerm x s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (eqTerm x s) := by
  have hEqTy : __eo_typeof_eq
      (__eo_typeof (insertTerm x s)) (__eo_typeof (unionTerm x s)) = Term.Bool := hTy
  have hInsertNS : __eo_typeof_set_insert (__eo_typeof x) (__eo_typeof s) ≠
      Term.Stuck := by
    intro h
    change __eo_typeof_eq
      (__eo_typeof_set_insert (__eo_typeof x) (__eo_typeof s)) _ = Term.Bool at hEqTy
    rw [h] at hEqTy
    simp [__eo_typeof_eq] at hEqTy
  rcases insert_arg_types hInsertNS with ⟨T, hxTy, hsTy⟩
  have hxSmt := TranslationProofs.eo_to_smt_typeof_matches_translation x hx
  have hsSmt := TranslationProofs.eo_to_smt_typeof_matches_translation s hs
  have hSetNN : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) ≠
      SmtType.None := by
    rw [← hsTy, ← hsSmt]
    exact hs
  have hSetTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
      SmtType.Set (__eo_to_smt_type T) := by
    cases hT : __eo_to_smt_type T <;>
      simp [TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
        native_ite, native_Teq, hT] at hSetNN ⊢
  have hsSet : __smtx_typeof (__eo_to_smt s) = SmtType.Set (__eo_to_smt_type T) := by
    rw [hsSmt, hsTy, hSetTy]
  have hWf := smt_term_set_type_wf_of_non_none (__eo_to_smt s) hs hsSet
  have hInsertTrans : RuleProofs.eo_has_smt_translation (insertTerm x s) := by
    change __smtx_typeof
      (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt x)) (__eo_to_smt s)) ≠
        SmtType.None
    rw [typeof_set_union_eq, smtx_typeof_set_singleton_term_eq, hxSmt, hxTy, hsSet]
    simp [__smtx_typeof_guard_wf, hWf, native_ite, __smtx_typeof_sets_op_2, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (insertTerm x s) (unionTerm x s) rfl hInsertTrans

public theorem cmd_step_sets_insert_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_insert_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_insert_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_insert_elim args premises) := by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons x args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons base args =>
      cases args with
      | cons _ _ => exact False.elim (hProg rfl)
      | nil =>
        cases premises with
        | cons _ _ => exact False.elim (hProg rfl)
        | nil =>
          change __eo_prog_sets_insert_elim x base ≠ Term.Stuck at hProg
          have hxNS : x ≠ Term.Stuck := by
            intro h; subst x; exact hProg rfl
          have hsNS : base ≠ Term.Stuck := by
            intro h; subst base; cases x <;> exact hProg rfl
          have hProgEq : __eo_prog_sets_insert_elim x base = eqTerm x base := by
            cases x <;> cases base <;>
              simp [__eo_prog_sets_insert_elim, eqTerm, insertTerm, unionTerm] at hxNS hsNS ⊢
          have hArgs : RuleProofs.eo_has_smt_translation x ∧
              RuleProofs.eo_has_smt_translation base ∧ True := by
            simpa [cmdTranslationOk, cArgListTranslationOk]
              using hCmdTrans
          change __eo_typeof (__eo_prog_sets_insert_elim x base) = Term.Bool at hResultTy
          rw [hProgEq] at hResultTy
          have hBool := typed_insert_eq x base hArgs.1 hArgs.2.1 hResultTy
          change StepRuleProperties M (premiseTermList s CIndexList.nil)
            (__eo_prog_sets_insert_elim x base)
          rw [hProgEq]
          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
          intro _
          exact RuleProofs.eo_interprets_eq_of_rel M (insertTerm x base) (unionTerm x base)
            hBool (RuleProofs.smt_value_rel_refl _)
