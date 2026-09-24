module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev replaceAllSelfPremise (t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.eq (Term.Apply Term.str_len t))
        (Term.Numeral 0)))
    (Term.Boolean false)

private abbrev replaceAllSelfLhs (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) t) s

private abbrev replaceAllSelfConclusion (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceAllSelfLhs t s)) s

private theorem eo_typeof_str_replace_self_args_of_ne_stuck
    (T U : Term)
    (h : __eo_typeof_str_replace T T U ≠ Term.Stuck) :
    ∃ V, T = Term.Apply Term.Seq V ∧ U = Term.Apply Term.Seq V := by
  cases T <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases U <;> simp at h ⊢
        case Apply g y =>
          cases g <;> simp at h ⊢
          case UOp opg =>
            cases opg <;> simp at h ⊢
            case Seq =>
              have hEq :=
                RuleProofs.eqs_of_requires_and_eq_true_not_stuck x x x y
                  (Term.Apply Term.Seq x) h
              exact hEq.2

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

private theorem smtx_eval_str_replace_all_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_all x y z) =
      __smtx_model_eval_str_replace_all
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_replace_all_aux_nil_cons
    (fuel : Nat) (p : SmtValue) (ps repl : List SmtValue) :
    native_seq_replace_all [] (p :: ps) repl = [] := by
  apply StrReplaceAllSupport.replace_all_eq_self_of_indexof_neg
  rw [native_seq_indexof_eq_rec]
  simp

private theorem native_seq_replace_all_self_of_nonempty
    (xs repl : List SmtValue)
    (hNonempty : xs ≠ []) :
    native_seq_replace_all xs xs repl = repl := by
  exact StrReplaceAllSupport.replace_all_self_of_nonempty xs repl hNonempty

private theorem prog_str_replace_all_self_info
    (t s P : Term)
    (hProg : __eo_prog_str_replace_all_self t s (Proof.pf P) ≠
      Term.Stuck) :
    ∃ t0,
      P = replaceAllSelfPremise t0 ∧
      t0 = t ∧
      __eo_prog_str_replace_all_self t s (Proof.pf P) =
        replaceAllSelfConclusion t s := by
  unfold __eo_prog_str_replace_all_self at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have ht :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_all_self, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      replaceAllSelfConclusion, replaceAllSelfLhs]

private theorem typed___eo_prog_str_replace_all_self_impl
    (t s P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_replace_all_self t s (Proof.pf P) =
        replaceAllSelfConclusion t s) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_all_self t s (Proof.pf P)) := by
  let lhs := replaceAllSelfLhs t s
  let rhs := s
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt t)
          (__eo_to_smt s)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_all_eq]
    simp [hTSmtTy, hSSmtTy, __smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hSSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [replaceAllSelfConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_replace_all_self_impl
    (M : SmtModel) (hM : model_wf M) (t s P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replaceAllSelfPremise t) true)
    (hProgEq :
      __eo_prog_str_replace_all_self t s (Proof.pf P) =
        replaceAllSelfConclusion t s) :
    eo_interprets M
      (__eo_prog_str_replace_all_self t s (Proof.pf P)) true := by
  let lhs := replaceAllSelfLhs t s
  let rhs := s
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, replaceAllSelfConclusion, lhs, rhs] using
      typed___eo_prog_str_replace_all_self_impl t s P
        hTTrans hSTrans hTTy hSTy hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hTLenNeZero :
      native_seq_len (native_unpack_seq ts) ≠ 0 := by
    intro hZero
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t))
                (SmtTerm.Numeral 0))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq,
          smtx_eval_str_len_term_eq, hTEval,
          smtx_eval_boolean_term_eq] at hEval
        rw [show __smtx_model_eval M (SmtTerm.Numeral 0) =
            SmtValue.Numeral 0 by
          rw [__smtx_model_eval.eq_def]] at hEval
        simp [__smtx_model_eval_str_len, __smtx_model_eval_eq,
          native_veq, hZero] at hEval
  have hTNonempty : native_unpack_seq ts ≠ [] := by
    intro hNil
    apply hTLenNeZero
    simp [native_seq_len, hNil]
  have hTSeqTy :
      __smtx_typeof_seq_value ts = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hTEval] using hTEvalTy
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hTElem : __smtx_elem_typeof_seq_value ts = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hPack :
      native_pack_seq (__smtx_elem_typeof_seq_value ts)
          (native_unpack_seq ss) =
        ss := by
    rw [hTElem, ← hSElem]
    exact native_pack_unpack_seq ss
  have hReplaceSelf :
      native_seq_replace_all (native_unpack_seq ts) (native_unpack_seq ts)
          (native_unpack_seq ss) =
        native_unpack_seq ss :=
    native_seq_replace_all_self_of_nonempty
      (native_unpack_seq ts) (native_unpack_seq ss) hTNonempty
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt t)
          (__eo_to_smt s)) =
      __smtx_model_eval M (__eo_to_smt s)
    rw [smtx_eval_str_replace_all_term_eq]
    rw [hTEval, hSEval]
    simp [__smtx_model_eval_str_replace_all, hReplaceSelf, hPack]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_all_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_all_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_all_self args premises ≠
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
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.2.1
                      change __eo_typeof
                          (__eo_prog_str_replace_all_self a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_replace_all_self a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_replace_all_self_info a1 a2 P hProgRule with
                        ⟨t0, hPremShape, ht0, hProgEq⟩
                      subst t0
                      let lhs := replaceAllSelfLhs a1 a2
                      let rhs := a2
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                        Term.Bool at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                      have hArgTypes :
                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                            __eo_typeof a2 = Term.Apply Term.Seq T := by
                        change __eo_typeof_str_replace (__eo_typeof a1)
                            (__eo_typeof a1) (__eo_typeof a2) ≠
                          Term.Stuck at hLhsNotStuck
                        exact eo_typeof_str_replace_self_args_of_ne_stuck
                          (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                      rcases hArgTypes with ⟨T, hA1Ty, hA2Ty⟩
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPremRaw : eo_interprets M P true :=
                          hTrue P (by simp [P, premiseTermList])
                        have hPrem :
                            eo_interprets M (replaceAllSelfPremise a1) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_replace_all_self_impl
                          M hM a1 a2 P hA1Trans hA2Trans hA1Ty hA2Ty
                          hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_replace_all_self_impl
                            a1 a2 P hA1Trans hA2Trans hA1Ty hA2Ty hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
