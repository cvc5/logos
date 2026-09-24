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

private abbrev replaceAllEmptyPremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len s))
    (Term.Numeral 0)

private abbrev replaceAllEmptyLhs (t s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) s) r

private abbrev replaceAllEmptyConclusion (t s r : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceAllEmptyLhs t s r)) t

private theorem eo_typeof_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_replace] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_replace] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_replace] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_replace] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_replace] at h ⊢
            case Seq =>
              cases C <;> simp [__eo_typeof_str_replace] at h ⊢
              case Apply k z =>
                cases k <;> simp [__eo_typeof_str_replace] at h ⊢
                case UOp opk =>
                  cases opk <;> simp [__eo_typeof_str_replace] at h ⊢
                  case Seq =>
                    have hEq :=
                      RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                        x x y z (Term.Apply Term.Seq x) h
                    rcases hEq with ⟨hy, hz⟩
                    subst y
                    subst z
                    simp

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

private theorem native_seq_replace_all_nil
    (xs repl : List SmtValue) :
    native_seq_replace_all xs [] repl = xs := by
  exact StrReplaceAllSupport.replace_all_nil_pat repl xs

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

private theorem prog_str_replace_all_empty_info
    (t s r P : Term)
    (hProg : __eo_prog_str_replace_all_empty t s r (Proof.pf P) ≠
      Term.Stuck) :
    ∃ s0,
      P = replaceAllEmptyPremise s0 ∧
      s0 = s ∧
      __eo_prog_str_replace_all_empty t s r (Proof.pf P) =
        replaceAllEmptyConclusion t s r := by
  unfold __eo_prog_str_replace_all_empty at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hs :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_all_empty, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      replaceAllEmptyConclusion, replaceAllEmptyLhs]

private theorem typed___eo_prog_str_replace_all_empty_impl
    (t s r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_replace_all_empty t s r (Proof.pf P) =
        replaceAllEmptyConclusion t s r) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_all_empty t s r (Proof.pf P)) := by
  rcases hTy with ⟨T, hTTy, hSTy, hRTy⟩
  let lhs := replaceAllEmptyLhs t s r
  let rhs := t
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt r)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_all_eq]
    simp [hTSmtTy, hSSmtTy, hRSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hTSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [replaceAllEmptyConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_replace_all_empty_impl
    (M : SmtModel) (hM : model_wf M) (t s r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replaceAllEmptyPremise s) true)
    (hProgEq :
      __eo_prog_str_replace_all_empty t s r (Proof.pf P) =
        replaceAllEmptyConclusion t s r) :
    eo_interprets M
      (__eo_prog_str_replace_all_empty t s r (Proof.pf P)) true := by
  rcases hTy with ⟨T, hTTy, hSTy, hRTy⟩
  let lhs := replaceAllEmptyLhs t s r
  let rhs := t
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, replaceAllEmptyConclusion, lhs, rhs] using
      typed___eo_prog_str_replace_all_empty_impl t s r P
        hTTrans hSTrans hRTrans ⟨T, hTTy, hSTy, hRTy⟩ hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
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
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  have hSLenZero : native_seq_len (native_unpack_seq ss) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s)) (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hSEval] at hEval
        rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
          rw [__smtx_model_eval.eq_def]] at hEval
        simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq]
          using hEval
  have hSNil : native_unpack_seq ss = [] :=
    list_eq_nil_of_native_seq_len_zero (native_unpack_seq ss) hSLenZero
  have hPack :
      native_pack_seq (__smtx_elem_typeof_seq_value ts)
          (native_unpack_seq ts) =
        ts :=
    native_pack_unpack_seq ts
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt r)) =
      __smtx_model_eval M (__eo_to_smt t)
    rw [smtx_eval_str_replace_all_term_eq, hTEval, hSEval, hREval]
    simp [__smtx_model_eval_str_replace_all, hSNil, native_seq_replace_all_nil,
      hPack]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_all_empty_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_all_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_empty args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_all_empty args premises ≠
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
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.2.2.1
                          change __eo_typeof
                              (__eo_prog_str_replace_all_empty a1 a2 a3 (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_replace_all_empty a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_replace_all_empty_info
                              a1 a2 a3 P hProgRule with
                            ⟨s0, hPremShape, hs0, hProgEq⟩
                          subst s0
                          let lhs := replaceAllEmptyLhs a1 a2 a3
                          let rhs := a1
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Apply Term.Seq T := by
                            change __eo_typeof_str_replace (__eo_typeof a1)
                                (__eo_typeof a2) (__eo_typeof a3) ≠
                              Term.Stuck at hLhsNotStuck
                            exact eo_typeof_str_replace_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a3) hLhsNotStuck
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M (replaceAllEmptyPremise a2) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_replace_all_empty_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hArgTypes hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_replace_all_empty_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hArgTypes hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
