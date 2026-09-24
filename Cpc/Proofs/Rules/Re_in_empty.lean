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

/-- Derivatives of the empty language stay empty, so no value sequence matches it. -/
private theorem foldl_deriv_re_empty :
    ∀ xs : List SmtValue,
      xs.foldl (fun acc c => native_re_deriv c acc) SmtRegLan.empty = SmtRegLan.empty
  | [] => rfl
  | c :: cs => by
      simpa [native_re_deriv] using foldl_deriv_re_empty cs

private theorem native_str_in_re_re_none_false (xs : List SmtValue) :
    Smtm.native_str_in_re xs native_re_none = false := by
  simp [Smtm.native_str_in_re, native_re_none, foldl_deriv_re_empty,
    native_re_nullable]

private theorem smtx_model_eval_re_in_empty (ss : SmtSeq)
    (hValid : native_string_valid (native_unpack_string ss) = true) :
    __smtx_model_eval_str_in_re (SmtValue.Seq ss) (SmtValue.RegLan native_re_none) =
      SmtValue.Boolean false := by
  change SmtValue.Boolean
      (Smtm.native_str_in_re (native_unpack_seq ss) native_re_none) =
    SmtValue.Boolean false
  rw [native_str_in_re_re_none_false]

private theorem smtx_typeof_re_none :
    __smtx_typeof SmtTerm.re_none = SmtType.RegLan := by
  simp [__smtx_typeof]

private theorem eo_typeof_str_in_re_reglan_eq_seq_char_of_ne_stuck (T : Term)
    (h : __eo_typeof_str_in_re T Term.RegLan ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp at h ⊢
            | _ => simp at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

private theorem typed___eo_prog_re_in_empty_impl
    (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_re_in_empty a1) := by
  let lhs := Term.Apply (Term.Apply Term.str_in_re a1) Term.re_none
  let rhs := Term.Boolean false
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty] at hTyRaw
    exact hTyRaw
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt a1) SmtTerm.re_none) = SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hA1SmtTy, smtx_typeof_re_none, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
    simp [__smtx_typeof]
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
  have hProg :
      __eo_prog_re_in_empty a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_re_in_empty a1 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply Term.str_in_re a1) Term.re_none))
            (Term.Boolean false) := by
      cases hA1 : a1 <;> first | exact False.elim (hA1NotStuck hA1) | rfl
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_in_empty_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_re_in_empty a1) true := by
  let lhs := Term.Apply (Term.Apply Term.str_in_re a1) Term.re_none
  let rhs := Term.Boolean false
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hProg :
      __eo_prog_re_in_empty a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_re_in_empty a1 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply Term.str_in_re a1) Term.re_none))
            (Term.Boolean false) := by
      cases hA1 : a1 <;> first | exact False.elim (hA1NotStuck hA1) | rfl
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    rw [← hProg]
    exact typed___eo_prog_re_in_empty_impl a1 hA1Trans hA1Ty
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty] at hTyRaw
    exact hTyRaw
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1) (by
        unfold term_has_non_none_type
        rw [hA1SmtTy]
        simp)
  rcases seq_value_canonical hA1EvalTy with ⟨ss, hss⟩
  have hSSValid : native_string_valid (native_unpack_string ss) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simpa [hss, __smtx_typeof_value] using hA1EvalTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    have hLhsTranslate :
        __eo_to_smt lhs = SmtTerm.str_in_re (__eo_to_smt a1) SmtTerm.re_none := by
      rfl
    have hRhsTranslate : __eo_to_smt rhs = SmtTerm.Boolean false := by
      rfl
    rw [hLhsTranslate, hRhsTranslate]
    simp [__smtx_model_eval]
    change
      __smtx_model_eval_str_in_re (__smtx_model_eval M (__eo_to_smt a1))
          (SmtValue.RegLan native_re_none) =
        SmtValue.Boolean false
    rw [hss]
    exact smtx_model_eval_re_in_empty ss hSSValid
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_re_in_empty_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_in_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_empty args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_in_empty args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              have hA1NotStuck : a1 ≠ Term.Stuck := by
                intro hStuck
                subst a1
                apply hProg
                rfl
              let lhs := Term.Apply (Term.Apply Term.str_in_re a1) Term.re_none
              let rhs := Term.Boolean false
              have hProgEq :
                  __eo_cmd_step_proven s CRule.re_in_empty
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq lhs) rhs := by
                have hProgEqRaw :
                    __eo_cmd_step_proven s CRule.re_in_empty
                        (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                      Term.Apply
                        (Term.Apply Term.eq
                          (Term.Apply (Term.Apply Term.str_in_re a1) Term.re_none))
                        (Term.Boolean false) := by
                  cases hA1 : a1 <;> first | exact False.elim (hA1NotStuck hA1) | rfl
                simpa [lhs, rhs] using hProgEqRaw
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) = Term.Bool at hResultTy
              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
              have hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                change __eo_typeof_str_in_re (__eo_typeof a1) Term.RegLan ≠
                  Term.Stuck at hLhsNotStuck
                exact eo_typeof_str_in_re_reglan_eq_seq_char_of_ne_stuck
                  (__eo_typeof a1) hLhsNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_re_in_empty a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_re_in_empty_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_re_in_empty_impl M hM a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_re_in_empty a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
