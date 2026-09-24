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

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_indexof_rec_nil
    (xs : List SmtValue) (i fuel : Nat)
    (hFuel : fuel ≠ 0) :
    native_seq_indexof_rec xs [] i fuel = Int.ofNat i := by
  cases fuel with
  | zero => exact False.elim (hFuel rfl)
  | succ fuel =>
      rw [Smtm.native_seq_indexof_rec.eq_def]
      simp [native_seq_prefix_eq]

private theorem native_seq_indexof_nil_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  unfold native_seq_indexof
  simp [native_seq_indexof_rec_nil]

private theorem native_seq_contains_nil (xs : List SmtValue) :
    native_seq_contains xs [] = true := by
  unfold native_seq_contains
  rw [native_seq_indexof_nil_zero]
  simp

private theorem list_eq_nil_of_native_seq_len_zero (xs : List SmtValue)
    (h : native_seq_len xs = 0) :
    xs = [] := by
  have hLenInt : (xs.length : Int) = 0 := by
    simpa [native_seq_len] using h
  have hLenNat : xs.length = 0 := by
    omega
  cases xs with
  | nil => rfl
  | cons _ _ => simp at hLenNat

private theorem prog_str_contains_emp_info
    (x y P : Term)
    (hProg : __eo_prog_str_contains_emp x y (Proof.pf P) ≠ Term.Stuck) :
    ∃ y0,
      P = Term.Apply
        (Term.Apply Term.eq (Term.Apply Term.str_len y0))
        (Term.Numeral 0) ∧
      y0 = y ∧
      __eo_prog_str_contains_emp x y (Proof.pf P) =
        Term.Apply
          (Term.Apply Term.eq
          (Term.Apply (Term.Apply Term.str_contains x) y))
          (Term.Boolean true) := by
  unfold __eo_prog_str_contains_emp at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hy :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_emp, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not]

private theorem typed___eo_prog_str_contains_emp_impl
    (x y P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_contains_emp x y (Proof.pf P) =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.str_contains x) y))
          (Term.Boolean true)) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_contains_emp x y (Proof.pf P)) := by
  let lhs := Term.Apply (Term.Apply Term.str_contains x) y
  let rhs := Term.Boolean true
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_str_contains_emp_impl
    (M : SmtModel) (hM : model_wf M) (x y P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hPrem :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq (Term.Apply Term.str_len y))
          (Term.Numeral 0)) true)
    (hProgEq :
      __eo_prog_str_contains_emp x y (Proof.pf P) =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.str_contains x) y))
          (Term.Boolean true)) :
    eo_interprets M (__eo_prog_str_contains_emp x y (Proof.pf P)) true := by
  let lhs := Term.Apply (Term.Apply Term.str_contains x) y
  let rhs := Term.Boolean true
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, lhs, rhs] using
      typed___eo_prog_str_contains_emp_impl x y P hXTrans hYTrans hXTy hYTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  have hYLenZero : native_seq_len (native_unpack_seq sy) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt y)) (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hYEval] at hEval
        rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
          rw [__smtx_model_eval.eq_def]] at hEval
        simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq]
          using hEval
  have hYNil : native_unpack_seq sy = [] :=
    list_eq_nil_of_native_seq_len_zero (native_unpack_seq sy) hYLenZero
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval M (SmtTerm.Boolean true)
    rw [smtx_eval_str_contains_term_eq, hXEval, hYEval]
    rw [show __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true by
      rw [__smtx_model_eval.eq_def]]
    simp [__smtx_model_eval_str_contains, hYNil, native_seq_contains_nil]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_emp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_emp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_contains_emp args premises ≠
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n premises =>
                  cases premises with
                  | nil =>
                      let P := __eo_state_proven_nth s n
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                      change __eo_typeof
                          (__eo_prog_str_contains_emp a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_contains_emp a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_contains_emp_info a1 a2 P hProgRule with
                        ⟨y0, hPremShape, hy0, hProgEq⟩
                      subst y0
                      let lhs := Term.Apply (Term.Apply Term.str_contains a1) a2
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs)
                          (__eo_typeof (Term.Boolean true)) = Term.Bool
                        at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs) (__eo_typeof (Term.Boolean true))
                          hResultTy).1
                      have hArgTypes :
                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                            __eo_typeof a2 = Term.Apply Term.Seq T := by
                        change __eo_typeof_str_contains (__eo_typeof a1)
                            (__eo_typeof a2) ≠ Term.Stuck at hLhsNotStuck
                        exact eo_typeof_str_contains_args_of_ne_stuck
                          (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                      rcases hArgTypes with ⟨T, hA1Ty, hA2Ty⟩
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPremRaw : eo_interprets M P true :=
                          hTrue P (by simp [P, premiseTermList])
                        have hPrem :
                            eo_interprets M
                              (Term.Apply
                                (Term.Apply Term.eq (Term.Apply Term.str_len a2))
                                (Term.Numeral 0)) true := by
                          simpa [hPremShape] using hPremRaw
                        change eo_interprets M
                          (__eo_prog_str_contains_emp a1 a2 (Proof.pf P)) true
                        exact facts___eo_prog_str_contains_emp_impl M hM a1 a2 P
                          hA1Trans hA2Trans hA1Ty hA2Ty hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_contains_emp_impl a1 a2 P
                            hA1Trans hA2Trans hA1Ty hA2Ty hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
