module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev isDigitCode (s : Term) : Term :=
  Term.Apply Term.str_to_code s

private abbrev isDigitLower (s : Term) : Term :=
  Term.Apply (Term.Apply Term.leq (Term.Numeral 48)) (isDigitCode s)

private abbrev isDigitUpper (s : Term) : Term :=
  Term.Apply (Term.Apply Term.leq (isDigitCode s)) (Term.Numeral 57)

private abbrev isDigitBounds (s : Term) : Term :=
  Term.Apply (Term.Apply Term.and (isDigitLower s))
    (Term.Apply (Term.Apply Term.and (isDigitUpper s)) (Term.Boolean true))

private abbrev isDigitConclusion (s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_is_digit s))
    (isDigitBounds s)

private theorem eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_is_digit A ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char := by
  cases A <;> simp [__eo_typeof_str_is_digit] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  have hCharNN : __eo_to_smt_type Term.Char ≠ SmtType.None := by decide
  simpa [TranslationProofs.eo_to_smt_type_char] using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type Term.Char) (SmtType.Seq (__eo_to_smt_type Term.Char))
      hCharNN)

private theorem smtx_eval_str_is_digit_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_is_digit x) =
      __smtx_model_eval_str_is_digit (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem prog_str_is_digit_elim_eq_of_ne_stuck
    (s : Term) (hs : s ≠ Term.Stuck) :
    __eo_prog_str_is_digit_elim s = isDigitConclusion s := by
  cases hS : s <;> first
    | exact False.elim (hs hS)
    | rfl

private theorem typed___eo_prog_str_is_digit_elim_impl
    (s : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_is_digit_elim s) := by
  let lhs := Term.Apply Term.str_is_digit s
  let rhs := isDigitBounds s
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  have hCodeTy : __smtx_typeof (__eo_to_smt (isDigitCode s)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt s)) = SmtType.Int
    rw [typeof_str_to_code_eq]
    simp [hSSmtTy, native_ite, native_Teq]
  have hRawCodeTy :
      __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt s)) = SmtType.Int := by
    exact hCodeTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.str_is_digit (__eo_to_smt s)) = SmtType.Bool
    rw [typeof_str_is_digit_eq]
    simp [hSSmtTy, native_ite, native_Teq]
  have hLowerTy : __smtx_typeof (__eo_to_smt (isDigitLower s)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.leq (SmtTerm.Numeral 48)
        (SmtTerm.str_to_code (__eo_to_smt s))) = SmtType.Bool
    rw [typeof_leq_eq]
    simp [hRawCodeTy, __smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2_ret]
  have hUpperTy : __smtx_typeof (__eo_to_smt (isDigitUpper s)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s))
        (SmtTerm.Numeral 57)) = SmtType.Bool
    rw [typeof_leq_eq]
    simp [hRawCodeTy, __smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2_ret]
  have hRawUpperTy :
      __smtx_typeof
        (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s))
          (SmtTerm.Numeral 57)) = SmtType.Bool := by
    exact hUpperTy
  have hTrueTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  have hRawTrueTy : __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool := by
    simpa using hTrueTy
  have hRightAndTy :
      __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.and (isDigitUpper s)) (Term.Boolean true))) =
        SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.and
        (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s)) (SmtTerm.Numeral 57))
        (SmtTerm.Boolean true)) = SmtType.Bool
    rw [typeof_and_eq]
    simp [hRawUpperTy, hRawTrueTy, native_ite, native_Teq]
  have hRawLowerTy :
      __smtx_typeof
        (SmtTerm.leq (SmtTerm.Numeral 48)
          (SmtTerm.str_to_code (__eo_to_smt s))) = SmtType.Bool := by
    exact hLowerTy
  have hRawRightAndTy :
      __smtx_typeof
        (SmtTerm.and
          (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s))
            (SmtTerm.Numeral 57))
          (SmtTerm.Boolean true)) = SmtType.Bool := by
    exact hRightAndTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.and
        (SmtTerm.leq (SmtTerm.Numeral 48)
          (SmtTerm.str_to_code (__eo_to_smt s)))
        (SmtTerm.and
          (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s))
            (SmtTerm.Numeral 57))
          (SmtTerm.Boolean true))) = SmtType.Bool
    rw [typeof_and_eq]
    simp [hRawLowerTy, hRawRightAndTy, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hSNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  rw [prog_str_is_digit_elim_eq_of_ne_stuck s hSNotStuck]
  simpa [isDigitConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_is_digit_elim_impl
    (M : SmtModel) (hM : model_wf M) (s : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_str_is_digit_elim s) true := by
  let lhs := Term.Apply Term.str_is_digit s
  let rhs := isDigitBounds s
  have hSNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq :
      __eo_prog_str_is_digit_elim s =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [isDigitConclusion, lhs, rhs] using
      prog_str_is_digit_elim_eq_of_ne_stuck s hSNotStuck
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, lhs, rhs] using
      typed___eo_prog_str_is_digit_elim_impl s hSTrans hSTy
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M (SmtTerm.str_is_digit (__eo_to_smt s)) =
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.leq (SmtTerm.Numeral 48)
            (SmtTerm.str_to_code (__eo_to_smt s)))
          (SmtTerm.and
            (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s))
              (SmtTerm.Numeral 57))
            (SmtTerm.Boolean true)))
    rw [smtx_eval_str_is_digit_term_eq, smtx_eval_and_term_eq,
      smtx_eval_leq_term_eq, smtx_eval_and_term_eq, smtx_eval_leq_term_eq,
      smtx_eval_boolean_term_eq, smtx_eval_str_to_code_term_eq, hSEval]
    rw [show __smtx_model_eval M (SmtTerm.Numeral 48) = SmtValue.Numeral 48 by
      rw [__smtx_model_eval.eq_def]]
    rw [show __smtx_model_eval M (SmtTerm.Numeral 57) = SmtValue.Numeral 57 by
      rw [__smtx_model_eval.eq_def]]
    simp [__smtx_model_eval_str_is_digit, __smtx_model_eval_str_to_code,
      __smtx_model_eval_leq, __smtx_model_eval_and, native_and]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_is_digit_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_is_digit_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_is_digit_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_is_digit_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_is_digit_elim args premises ≠
      Term.Stuck :=
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
              have hA1NotStuck : a1 ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
              let lhs := Term.Apply Term.str_is_digit a1
              let rhs := isDigitBounds a1
              have hProgEq :
                  __eo_cmd_step_proven s CRule.str_is_digit_elim
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq lhs) rhs := by
                change __eo_prog_str_is_digit_elim a1 =
                  Term.Apply (Term.Apply Term.eq lhs) rhs
                simpa [isDigitConclusion, lhs, rhs] using
                  prog_str_is_digit_elim_eq_of_ne_stuck a1 hA1NotStuck
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                Term.Bool at hResultTy
              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
              have hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                change __eo_typeof_str_is_digit (__eo_typeof a1) ≠
                  Term.Stuck at hLhsNotStuck
                exact eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck
                  hLhsNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_str_is_digit_elim a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_str_is_digit_elim_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_str_is_digit_elim_impl M hM a1
                  hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_str_is_digit_elim a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
