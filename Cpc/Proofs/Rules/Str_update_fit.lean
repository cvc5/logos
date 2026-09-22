module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev updateFitPremise (n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq n) (Term.Numeral 0)

private abbrev updateFitLengthPremise (t r : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len t)) (Term.Apply Term.str_len r)

private abbrev updateFitLhs (t n r : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r

private abbrev updateFitConclusion (t n r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (updateFitLhs t n r))
    r

private theorem eo_typeof_str_update_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_update A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Int ∧ C = Term.Apply Term.Seq T := by
  cases A <;> simp [__eo_typeof_str_update] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_update] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_update] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_update] at h ⊢
        case UOp opB =>
          cases opB <;> simp [__eo_typeof_str_update] at h ⊢
          case Int =>
            cases C <;>
              simp [__eo_typeof_str_update] at h ⊢
            case Apply g y =>
              cases g <;>
                simp [__eo_typeof_str_update] at h ⊢
              case UOp opC =>
                cases opC <;>
                  simp [__eo_typeof_str_update] at h ⊢
                case Seq =>
                  have hReqNe :
                      __eo_requires (__eo_eq x y) (Term.Boolean true)
                          (Term.Apply Term.Seq x) ≠ Term.Stuck := by
                    intro hReq
                    apply h
                    rw [hReq]
                  exact RuleProofs.eq_of_requires_eq_true_not_stuck x y
                    (Term.Apply Term.Seq x) hReqNe

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

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

private theorem smtx_eval_str_update_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_update x y n) =
      __smtx_model_eval_str_update
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem prog_str_update_fit_info
    (t n r P Q : Term)
    (hProg : __eo_prog_str_update_fit t n r (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck) :
    P = updateFitPremise n ∧ Q = updateFitLengthPremise t r ∧
      __eo_prog_str_update_fit t n r (Proof.pf P) (Proof.pf Q) =
        updateFitConclusion t n r := by
  unfold __eo_prog_str_update_fit at hProg
  split at hProg <;> try contradiction
  next hp hq =>
    cases hp
    cases hq
    rcases StrEqReplSupport.eqs_of_requires3_and_eq_true_not_stuck hProg with
      ⟨hn, ht, hr⟩
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp [__eo_prog_str_update_fit, __eo_requires, __eo_eq, __eo_and,
      SmtEval.native_ite, native_teq, native_and, SmtEval.native_not,
      updateFitConclusion, updateFitLhs]

private theorem typed___eo_prog_str_update_fit_impl
    (t n r P Q : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧ __eo_typeof r = Term.Apply Term.Seq T)
    (hProgEq : __eo_prog_str_update_fit t n r (Proof.pf P) (Proof.pf Q) = updateFitConclusion t n r) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_update_fit t n r (Proof.pf P) (Proof.pf Q)) := by
  rcases hTy with ⟨T, hTTy, hNTy, hRTy⟩
  have ht := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hn := smtx_typeof_of_eo_int n hNTrans hNTy
  have hr := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hu : __smtx_typeof (__eo_to_smt (updateFitLhs t n r)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n)
      (__eo_to_smt r)) = _
    rw [typeof_str_update_eq, ht, hn, hr]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (updateFitLhs t n r) r
    (hu.trans hr.symm) (by rw [hu]; simp)

private theorem facts___eo_prog_str_update_fit_impl
    (M : SmtModel) (hM : model_wf M) (t n r P Q : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (updateFitPremise n) true)
    (hLength : eo_interprets M (updateFitLengthPremise t r) true)
    (hProgEq :
      __eo_prog_str_update_fit t n r (Proof.pf P) (Proof.pf Q) =
        updateFitConclusion t n r) :
    eo_interprets M
      (__eo_prog_str_update_fit t n r (Proof.pf P) (Proof.pf Q)) true := by
  rcases hTy with ⟨T, hTTy, hNTy, hRTy⟩
  let lhs := updateFitLhs t n r
  let rhs := r
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, updateFitConclusion, lhs, rhs] using
      typed___eo_prog_str_update_fit_impl t n r P Q
        hTTrans hNTrans hRTrans ⟨T, hTTy, hNTy, hRTy⟩ hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hREvalTy with ⟨ss, hREval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hZero : ni = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
      change __smtx_model_eval M (SmtTerm.eq (__eo_to_smt n) (SmtTerm.Numeral 0)) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq, hNEval, smtx_eval_numeral_term_eq] at hEval
      simpa [__smtx_model_eval_eq, native_veq] using hEval
  have hLen : (native_unpack_seq ts).length = (native_unpack_seq ss).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLength
    cases hLength with
    | intro_true _ hEval =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t))
        (SmtTerm.str_len (__eo_to_smt r))) = SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
        smtx_eval_str_len_term_eq, hTEval, hREval] at hEval
      apply Int.ofNat.inj
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len,
        native_veq] using hEval
  have hElem : __smtx_elem_typeof_seq_value ts = __smtx_elem_typeof_seq_value ss := by
    have ht := elem_typeof_seq_value_of_typeof_seq_value
      (show __smtx_typeof_seq_value ts = SmtType.Seq (__eo_to_smt_type T) from
        by
          have h := hTEvalTy
          rw [hTEval] at h
          exact h)
    have hr := elem_typeof_seq_value_of_typeof_seq_value
      (show __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) from
        by
          have h := hREvalTy
          rw [hREval] at h
          exact h)
    exact ht.trans hr.symm
  have hUpdate : native_seq_update (native_unpack_seq ts) ni (native_unpack_seq ss) =
      native_unpack_seq ss := by
    subst ni
    simpa using native_seq_update_replace_middle [] (native_unpack_seq ts) []
      (native_unpack_seq ss) hLen

  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n) (__eo_to_smt r)) =
      __smtx_model_eval M (__eo_to_smt r)
    rw [smtx_eval_str_update_term_eq, hTEval, hNEval, hREval]
    simp [__smtx_model_eval_str_update, hUpdate, hElem,
      native_pack_unpack_seq]

  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_update_fit_properties
    (M : SmtModel) (hM : model_wf M)
    (r : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_fit args premises) ->
  AllHaveBoolType (premiseTermList r premises) ->
  __eo_typeof (__eo_cmd_step_proven r CRule.str_update_fit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList r premises)
    (__eo_cmd_step_proven r CRule.str_update_fit args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven r CRule.str_update_fit args premises ≠
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons nIdx premises =>
                      cases premises with
                      | nil =>
                          exact False.elim (hProg rfl)
                      | cons n2 premises =>
                          cases premises with
                          | nil =>
                              let P := __eo_state_proven_nth r nIdx
                              let Q := __eo_state_proven_nth r n2
                              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using
                                  hCmdTrans.1
                              have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using
                                  hCmdTrans.2.1
                              have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using
                                  hCmdTrans.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_update_fit a1 a2 a3 (Proof.pf P) (Proof.pf Q)) =
                                Term.Bool at hResultTy
                              have hProgRule :
                                  __eo_prog_str_update_fit a1 a2 a3 (Proof.pf P) (Proof.pf Q) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_update_fit_info a1 a2 a3 P Q hProgRule with
                                ⟨hPremShape, hLengthShape, hProgEq⟩
                              let lhs := updateFitLhs a1 a2 a3
                              let rhs := a3
                              rw [hProgEq] at hResultTy
                              change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                                Term.Bool at hResultTy
                              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                              have hArgTypes :
                                  ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                    __eo_typeof a2 = Term.Int ∧
                                    __eo_typeof a3 = Term.Apply Term.Seq T := by
                                change __eo_typeof_str_update (__eo_typeof a1)
                                    (__eo_typeof a2) (__eo_typeof a3) ≠
                                  Term.Stuck at hLhsNotStuck
                                exact eo_typeof_str_update_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a2)
                                  (__eo_typeof a3) hLhsNotStuck
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M (updateFitPremise a2) true := by
                                  simpa [hPremShape] using hPremRaw
                                have hLength : eo_interprets M (updateFitLengthPremise a1 a3) true := by
                                  have hQ := hTrue Q (by simp [Q, premiseTermList])
                                  simpa [hLengthShape] using hQ
                                exact facts___eo_prog_str_update_fit_impl
                                  M hM a1 a2 a3 P Q hA1Trans hA2Trans hA3Trans
                                  hArgTypes hPrem hLength hProgEq
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed___eo_prog_str_update_fit_impl
                                    a1 a2 a3 P Q hA1Trans hA2Trans hA3Trans
                                    hArgTypes hProgEq)
                          | cons _ _ =>
                              exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
