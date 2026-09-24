module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_to_upper_str_to_upper_arg_seq_char_of_ne_stuck
    (T : Term)
    (h : __eo_typeof_str_to_lower (__eo_typeof_str_to_lower T) ≠ Term.Stuck) :
    T = Term.Apply Term.Seq (Term.UOp UserOp.Char) := by
  cases T <;> simp [__eo_typeof_str_to_lower] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases x <;> simp at h ⊢
        case UOp op2 =>
          cases op2 <;> simp at h ⊢

private theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)


private theorem smtx_eval_str_to_upper_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_to_upper x) =
      __smtx_model_eval_str_to_upper (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_char_to_upper_idem (c : native_Char) :
    impl_native_char_to_upper (impl_native_char_to_upper c) =
      impl_native_char_to_upper c := by
  by_cases h : (97 <= c && c <= 122) = true
  · have hr : 97 ≤ c ∧ c ≤ 122 := by simpa using h
    change (97 : Nat) ≤ c ∧ c ≤ (122 : Nat) at hr
    rcases hr with ⟨hlo, hhi⟩
    have hn : c - 32 < (97 : Nat) :=
      Nat.lt_of_le_of_lt (Nat.sub_le_sub_right hhi 32) (by decide)
    simp [impl_native_char_to_upper, h, Nat.not_le_of_gt hn]
  · simp [impl_native_char_to_upper, h]

private theorem native_str_to_upper_idem (s : native_String) :
    native_str_to_upper (native_str_to_upper s) = native_str_to_upper s := by
  unfold native_str_to_upper
  induction s with
  | nil => rfl
  | cons c cs ih =>
      simp [List.map, native_char_to_upper_idem c, ih]

private theorem map_native_ssm_char_of_value_char :
    ∀ s : native_String,
      List.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | c :: cs => by
      simp [Function.comp_def, impl_native_ssm_char_of_value]

private theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string, Smtm.native_unpack_pack_seq,
    map_native_ssm_char_of_value_char]

private theorem typed___eo_prog_str_to_upper_idem_impl
    (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq (Term.UOp UserOp.Char)) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_to_upper_idem x) := by
  let lhs := Term.Apply Term.str_to_upper (Term.Apply Term.str_to_upper x)
  let rhs := Term.Apply Term.str_to_upper x
  have hXSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char := by
    have := smtx_typeof_of_eo_seq x (Term.UOp UserOp.Char) hXTrans hXTy
    simpa using this
  have hLowerTy :
      __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt x)) =
        SmtType.Seq SmtType.Char := by
    rw [typeof_str_to_upper_eq, hXSmtTy]
    simp [native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_to_upper (SmtTerm.str_to_upper (__eo_to_smt x))) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_upper_eq, hLowerTy]
    simp [native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt x)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_upper_eq, hXSmtTy]
    simp [native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hXNotStuck : x ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProg :
      __eo_prog_str_to_upper_idem x = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_to_upper_idem x =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_to_upper
                (Term.Apply Term.str_to_upper x)))
            (Term.Apply Term.str_to_upper x) := by
      cases x <;> simp [__eo_prog_str_to_upper_idem] at hXNotStuck ⊢
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_to_upper_idem_impl
    (M : SmtModel) (hM : model_wf M) (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq (Term.UOp UserOp.Char)) :
    eo_interprets M (__eo_prog_str_to_upper_idem x) true := by
  let lhs := Term.Apply Term.str_to_upper (Term.Apply Term.str_to_upper x)
  let rhs := Term.Apply Term.str_to_upper x
  have hXNotStuck : x ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProg :
      __eo_prog_str_to_upper_idem x = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_to_upper_idem x =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_to_upper
                (Term.Apply Term.str_to_upper x)))
            (Term.Apply Term.str_to_upper x) := by
      cases x <;> simp [__eo_prog_str_to_upper_idem] at hXNotStuck ⊢
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_to_upper_idem_impl x hXTrans hXTy
  have hXSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char := by
    have := smtx_typeof_of_eo_seq x (Term.UOp UserOp.Char) hXTrans hXTy
    simpa using this
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq SmtType.Char := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_upper (SmtTerm.str_to_upper (__eo_to_smt x))) =
      __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt x))
    simp only [smtx_eval_str_to_upper_term_eq]
    rw [hXEval]
    simp [__smtx_model_eval_str_to_upper,
      native_unpack_string_pack_string, native_str_to_upper_idem]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_to_upper_idem_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_upper_idem args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_to_upper_idem args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_upper_idem args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_to_upper_idem args premises ≠
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
              have hA1NotStuck : a1 ≠ Term.Stuck := by
                intro hStuck
                subst a1
                apply hProg
                rfl
              let lhs :=
                Term.Apply Term.str_to_upper
                  (Term.Apply Term.str_to_upper a1)
              let rhs := Term.Apply Term.str_to_upper a1
              have hProgEq :
                  __eo_cmd_step_proven s CRule.str_to_upper_idem
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq lhs) rhs := by
                have hProgEqRaw :
                    __eo_cmd_step_proven s CRule.str_to_upper_idem
                        (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                      Term.Apply
                        (Term.Apply Term.eq
                          (Term.Apply Term.str_to_upper
                            (Term.Apply Term.str_to_upper a1)))
                        (Term.Apply Term.str_to_upper a1) := by
                  cases hA1 : a1 <;> first
                    | exact False.elim (hA1NotStuck hA1)
                    | rfl
                simpa [lhs, rhs] using hProgEqRaw
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                Term.Bool at hResultTy
              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
              have hA1Ty : __eo_typeof a1 =
                  Term.Apply Term.Seq (Term.UOp UserOp.Char) := by
                change __eo_typeof_str_to_lower
                    (__eo_typeof_str_to_lower (__eo_typeof a1)) ≠ Term.Stuck
                  at hLhsNotStuck
                exact eo_typeof_str_to_upper_str_to_upper_arg_seq_char_of_ne_stuck
                  (__eo_typeof a1) hLhsNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_str_to_upper_idem a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_str_to_upper_idem_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_str_to_upper_idem_impl M hM a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_str_to_upper_idem a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
