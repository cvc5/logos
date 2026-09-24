module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

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

private theorem smtx_eval_str_prefixof_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_prefixof x y) =
      __smtx_model_eval_str_prefixof
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_substr_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem typed___eo_prog_str_prefixof_elim_impl
    (s t : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_prefixof_elim s t) := by
  rcases hTy with ⟨T, hSTy, hTTy⟩
  let lhs := Term.Apply (Term.Apply Term.str_prefixof s) t
  let rhsSub :=
    Term.Apply
      (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0))
      (Term.Apply Term.str_len s)
  let rhs := Term.Apply (Term.Apply Term.eq s) rhsSub
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hLenTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int := by
    rw [typeof_str_len_eq]
    simp [hSSmtTy, __smtx_typeof_seq_op_1_ret]
  have hSubTy :
      __smtx_typeof (__eo_to_smt rhsSub) =
        SmtType.Seq (__eo_to_smt_type T) := by
    have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
      rw [__smtx_typeof.eq_def]
    change __smtx_typeof
      (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
        (SmtTerm.str_len (__eo_to_smt s))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hTSmtTy, hZeroTy, hLenTy, __smtx_typeof_str_substr]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_prefixof (__eo_to_smt s) (__eo_to_smt t)) =
      SmtType.Bool
    rw [typeof_str_prefixof_eq]
    simp [hSSmtTy, hTSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type s rhsSub
      (by rw [hSSmtTy, hSubTy]) (by rw [hSSmtTy]; simp)
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hSNotStuck : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProg :
      __eo_prog_str_prefixof_elim s t =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_prefixof_elim s t =
          Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_prefixof s) t))
            (Term.Apply (Term.Apply Term.eq s)
              (Term.Apply
                (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0))
                (Term.Apply Term.str_len s))) := by
      cases s <;> cases t <;>
        simp [__eo_prog_str_prefixof_elim] at hSNotStuck hTNotStuck ⊢
    simpa [lhs, rhs, rhsSub] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_prefixof_elim_impl
    (M : SmtModel) (s t : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_prefixof_elim s t) true := by
  rcases hTy with ⟨T, hSTy, hTTy⟩
  let lhs := Term.Apply (Term.Apply Term.str_prefixof s) t
  let rhsSub :=
    Term.Apply
      (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0))
      (Term.Apply Term.str_len s)
  let rhs := Term.Apply (Term.Apply Term.eq s) rhsSub
  have hSNotStuck : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProg :
      __eo_prog_str_prefixof_elim s t =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_prefixof_elim s t =
          Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_prefixof s) t))
            (Term.Apply (Term.Apply Term.eq s)
              (Term.Apply
                (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0))
                (Term.Apply Term.str_len s))) := by
      cases s <;> cases t <;>
        simp [__eo_prog_str_prefixof_elim] at hSNotStuck hTNotStuck ⊢
    simpa [lhs, rhs, rhsSub] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_prefixof_elim_impl s t hSTrans hTTrans
        ⟨T, hSTy, hTTy⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_prefixof (__eo_to_smt s) (__eo_to_smt t)) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt s)
          (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
            (SmtTerm.str_len (__eo_to_smt s))))
    rw [smtx_eval_str_prefixof_term_eq, smtx_eval_eq_term_eq,
      smtx_eval_str_substr_term_eq, smtx_eval_numeral_term_eq,
      smtx_eval_str_len_term_eq]
    simp [__smtx_model_eval_str_prefixof]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_prefixof_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_prefixof_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_prefixof_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_prefixof_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_prefixof_elim args premises ≠
      Term.Stuck :=
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
                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                      hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                      hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    exact RuleProofs.term_ne_stuck_of_has_smt_translation
                      a1 hA1Trans
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    exact RuleProofs.term_ne_stuck_of_has_smt_translation
                      a2 hA2Trans
                  let lhs := Term.Apply (Term.Apply Term.str_prefixof a1) a2
                  let rhsSub :=
                    Term.Apply
                      (Term.Apply (Term.Apply Term.str_substr a2) (Term.Numeral 0))
                      (Term.Apply Term.str_len a1)
                  let rhs := Term.Apply (Term.Apply Term.eq a1) rhsSub
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_prefixof_elim
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        Term.Apply (Term.Apply Term.eq lhs) rhs := by
                    have hProgEqRaw :
                        __eo_cmd_step_proven s CRule.str_prefixof_elim
                            (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                            CIndexList.nil =
                          Term.Apply
                            (Term.Apply Term.eq
                              (Term.Apply (Term.Apply Term.str_prefixof a1) a2))
                            (Term.Apply (Term.Apply Term.eq a1)
                              (Term.Apply
                                (Term.Apply
                                  (Term.Apply Term.str_substr a2)
                                  (Term.Numeral 0))
                                (Term.Apply Term.str_len a1))) := by
                      cases hA1 : a1 <;> cases hA2 : a2 <;> first
                        | exact False.elim (hA1NotStuck hA1)
                        | exact False.elim (hA2NotStuck hA2)
                        | rfl
                    simpa [lhs, rhs, rhsSub] using hProgEqRaw
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                    Term.Bool at hResultTy
                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                  have hArgsTy :
                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                        __eo_typeof a2 = Term.Apply Term.Seq T := by
                    change __eo_typeof_str_contains (__eo_typeof a1)
                        (__eo_typeof a2) ≠ Term.Stuck at hLhsNotStuck
                    exact eo_typeof_str_contains_args_of_ne_stuck
                      (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_prefixof_elim a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_str_prefixof_elim_impl a1 a2
                        hA1Trans hA2Trans hArgsTy)⟩
                    intro _hTrue
                    exact facts___eo_prog_str_prefixof_elim_impl M a1 a2
                      hA1Trans hA2Trans hArgsTy
                  change StepRuleProperties M [] (__eo_prog_str_prefixof_elim a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
