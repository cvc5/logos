module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_re_mult_eq_reglan_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ =>
      simp [__eo_typeof_re_mult] at h

private theorem eo_typeof_str_in_re_eq_types_of_ne_stuck (T R : Term)
    (h : __eo_typeof_str_in_re T R ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char ∧ R = Term.RegLan := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp opF =>
          cases opF <;> try (simp [__eo_typeof_str_in_re] at h)
          case Seq =>
            cases x with
            | UOp opX =>
                cases opX <;> try (simp at h)
                case Char =>
                  cases R with
                  | UOp opR =>
                      cases opR <;> simp at h ⊢
                  | _ => simp at h
            | _ => simp at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

private theorem smtx_model_eval_re_in_comp (ss : SmtSeq) (r : SmtRegLan)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hValid : native_string_valid (native_unpack_string ss) = true) :
    __smtx_model_eval_str_in_re (SmtValue.Seq ss)
        (__smtx_model_eval_re_comp (SmtValue.RegLan r)) =
      __smtx_model_eval_not
        (__smtx_model_eval_str_in_re (SmtValue.Seq ss) (SmtValue.RegLan r)) := by
  have hUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTy
  change SmtValue.Boolean
      (Smtm.native_str_in_re (native_unpack_seq ss) (native_re_comp r)) =
    __smtx_model_eval_not
      (SmtValue.Boolean (Smtm.native_str_in_re (native_unpack_seq ss) r))
  rw [hUnpack,
    ← RuleProofs.native_str_in_re_eq_model (native_unpack_string ss)
      (native_re_comp r),
    ← RuleProofs.native_str_in_re_eq_model (native_unpack_string ss) r]
  rw [RuleProofs.native_str_in_re_re_comp]
  simp [hValid, __smtx_model_eval_not, SmtEval.native_not]

private theorem typed___eo_prog_re_in_comp_impl
    (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char)
    (hA2Ty : __eo_typeof a2 = Term.RegLan) :
    RuleProofs.eo_has_bool_type (__eo_prog_re_in_comp a1 a2) := by
  let inner := Term.Apply (Term.Apply Term.str_in_re a1) a2
  let lhs := Term.Apply (Term.Apply Term.str_in_re a1) (Term.Apply Term.re_comp a2)
  let rhs := Term.Apply Term.not inner
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty] at hTyRaw
    exact hTyRaw
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
    rw [hA2Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hCompTy :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.re_comp a2)) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_comp (__eo_to_smt a2)) = SmtType.RegLan
    rw [typeof_re_comp_eq]
    simp [hA2SmtTy, native_ite, native_Teq]
  have hInnerTy : RuleProofs.eo_has_bool_type inner := by
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt a1) (__eo_to_smt a2)) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hA1SmtTy, hA2SmtTy, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt a1)
          (__eo_to_smt (Term.Apply Term.re_comp a2))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hA1SmtTy, hCompTy, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    unfold RuleProofs.eo_has_bool_type at hInnerTy
    change __smtx_typeof (SmtTerm.not (__eo_to_smt inner)) = SmtType.Bool
    rw [typeof_not_eq]
    simp [hInnerTy, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_in_comp a1 a2 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_re_in_comp a1 a2 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply Term.str_in_re a1) (Term.Apply Term.re_comp a2)))
            (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re a1) a2)) := by
      cases hA1 : a1 <;> cases hA2 : a2 <;> first
        | exact False.elim (hA1NotStuck hA1)
        | exact False.elim (hA2NotStuck hA2)
        | rfl
    simpa [lhs, rhs, inner] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_in_comp_impl
    (M : SmtModel) (hM : model_wf M) (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char)
    (hA2Ty : __eo_typeof a2 = Term.RegLan) :
    eo_interprets M (__eo_prog_re_in_comp a1 a2) true := by
  let inner := Term.Apply (Term.Apply Term.str_in_re a1) a2
  let lhs := Term.Apply (Term.Apply Term.str_in_re a1) (Term.Apply Term.re_comp a2)
  let rhs := Term.Apply Term.not inner
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_in_comp a1 a2 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_re_in_comp a1 a2 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply Term.str_in_re a1) (Term.Apply Term.re_comp a2)))
            (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re a1) a2)) := by
      cases hA1 : a1 <;> cases hA2 : a2 <;> first
        | exact False.elim (hA1NotStuck hA1)
        | exact False.elim (hA2NotStuck hA2)
        | rfl
    simpa [lhs, rhs, inner] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    rw [← hProg]
    exact typed___eo_prog_re_in_comp_impl a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty] at hTyRaw
    exact hTyRaw
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
    rw [hA2Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1) (by
        unfold term_has_non_none_type
        rw [hA1SmtTy]
        simp)
  have hA2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a2)) = SmtType.RegLan := by
    simpa [hA2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a2) (by
        unfold term_has_non_none_type
        rw [hA2SmtTy]
        simp)
  rcases seq_value_canonical hA1EvalTy with ⟨ss, hEval1⟩
  rcases reglan_value_canonical hA2EvalTy with ⟨r, hEval2⟩
  have hSSValid : native_string_valid (native_unpack_string ss) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simpa [hEval1, __smtx_typeof_value] using hA1EvalTy
  have hSSTy :
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hEval1, __smtx_typeof_value] using hA1EvalTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt a1)
          (SmtTerm.re_comp (__eo_to_smt a2))) =
      __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.str_in_re (__eo_to_smt a1) (__eo_to_smt a2)))
    simp [__smtx_model_eval, hEval1, hEval2]
    exact smtx_model_eval_re_in_comp ss r hSSTy hSSValid
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_re_in_comp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_comp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_in_comp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_comp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_in_comp args premises ≠ Term.Stuck :=
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
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    intro hStuck
                    subst a1
                    apply hProg
                    rfl
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    intro hStuck
                    subst a2
                    apply hProg
                    cases a1 <;> rfl
                  let inner := Term.Apply (Term.Apply Term.str_in_re a1) a2
                  let lhs := Term.Apply (Term.Apply Term.str_in_re a1) (Term.Apply Term.re_comp a2)
                  let rhs := Term.Apply Term.not inner
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.re_in_comp
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply (Term.Apply Term.eq lhs) rhs := by
                    have hProgEqRaw :
                        __eo_cmd_step_proven s CRule.re_in_comp
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                          Term.Apply
                            (Term.Apply Term.eq
                              (Term.Apply (Term.Apply Term.str_in_re a1)
                                (Term.Apply Term.re_comp a2)))
                            (Term.Apply Term.not
                              (Term.Apply (Term.Apply Term.str_in_re a1) a2)) := by
                      cases hA1 : a1 <;> cases hA2 : a2 <;> first
                        | exact False.elim (hA1NotStuck hA1)
                        | exact False.elim (hA2NotStuck hA2)
                        | rfl
                    simpa [lhs, rhs, inner] using hProgEqRaw
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                    Term.Bool at hResultTy
                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                  have hLhsTypes :
                      __eo_typeof a1 = Term.Apply Term.Seq Term.Char ∧
                        __eo_typeof (Term.Apply Term.re_comp a2) = Term.RegLan := by
                    change __eo_typeof_str_in_re (__eo_typeof a1)
                        (__eo_typeof (Term.Apply Term.re_comp a2)) ≠ Term.Stuck
                      at hLhsNotStuck
                    exact eo_typeof_str_in_re_eq_types_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof (Term.Apply Term.re_comp a2)) hLhsNotStuck
                  have hA2Ty : __eo_typeof a2 = Term.RegLan := by
                    have hCompNotStuck :
                        __eo_typeof_re_mult (__eo_typeof a2) ≠ Term.Stuck := by
                      change __eo_typeof (Term.Apply Term.re_comp a2) ≠ Term.Stuck
                      rw [hLhsTypes.2]
                      native_decide
                    exact eo_typeof_re_mult_eq_reglan_of_ne_stuck
                      (__eo_typeof a2) hCompNotStuck
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_re_in_comp a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_re_in_comp_impl a1 a2 hA1Trans hA2Trans
                        hLhsTypes.1 hA2Ty)⟩
                    intro _hTrue
                    exact facts___eo_prog_re_in_comp_impl M hM a1 a2 hA1Trans hA2Trans
                      hLhsTypes.1 hA2Ty
                  change StepRuleProperties M [] (__eo_prog_re_in_comp a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
