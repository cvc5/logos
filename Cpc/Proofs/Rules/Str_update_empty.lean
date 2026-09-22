module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev updateEmptyPremise (t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len t)) (Term.Numeral 0)

private abbrev updateEmptyLhs (t n r : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r

private abbrev updateEmptyConclusion (t n r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (updateEmptyLhs t n r))
    t

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

private theorem prog_str_update_empty_info
    (t n r P : Term)
    (hProg : __eo_prog_str_update_empty t n r (Proof.pf P) ≠
      Term.Stuck) :
    ∃ t0,
      P = updateEmptyPremise t0 ∧
      t0 = t ∧
      __eo_prog_str_update_empty t n r (Proof.pf P) =
        updateEmptyConclusion t n r := by
  unfold __eo_prog_str_update_empty at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hn :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_update_empty, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      updateEmptyConclusion, updateEmptyLhs]

private theorem typed___eo_prog_str_update_empty_impl
    (t n r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧ __eo_typeof r = Term.Apply Term.Seq T)
    (hProgEq : __eo_prog_str_update_empty t n r (Proof.pf P) = updateEmptyConclusion t n r) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_update_empty t n r (Proof.pf P)) := by
  rcases hTy with ⟨T, hTTy, hNTy, hRTy⟩
  have ht := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hn := smtx_typeof_of_eo_int n hNTrans hNTy
  have hr := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hu : __smtx_typeof (__eo_to_smt (updateEmptyLhs t n r)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n)
      (__eo_to_smt r)) = _
    rw [typeof_str_update_eq, ht, hn, hr]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (updateEmptyLhs t n r) t
    (hu.trans ht.symm) (by rw [hu]; simp)

private theorem native_pack_unpack_seq : ∀ ss : SmtSeq,
    native_pack_seq (__smtx_elem_typeof_seq_value ss) (native_unpack_seq ss) = ss
  | .empty _ => rfl
  | .cons _ ss => by
    simp [native_pack_seq, native_unpack_seq, __smtx_elem_typeof_seq_value,
      native_pack_unpack_seq ss]

private theorem facts___eo_prog_str_update_empty_impl
    (M : SmtModel) (hM : model_wf M) (t n r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (updateEmptyPremise t) true)
    (hProgEq :
      __eo_prog_str_update_empty t n r (Proof.pf P) =
        updateEmptyConclusion t n r) :
    eo_interprets M
      (__eo_prog_str_update_empty t n r (Proof.pf P)) true := by
  rcases hTy with ⟨T, hTTy, hNTy, hRTy⟩
  let lhs := updateEmptyLhs t n r
  let rhs := t
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, updateEmptyConclusion, lhs, rhs] using
      typed___eo_prog_str_update_empty_impl t n r P
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
  have hEmpty : native_unpack_seq ts = [] := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t)) (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hTEval,
          smtx_eval_numeral_term_eq] at hEval
        have hLen : (native_unpack_seq ts).length = 0 := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        simpa using hLen
  have hUpdate : native_seq_update (native_unpack_seq ts) ni (native_unpack_seq ss) =
      native_unpack_seq ts := by
    rw [hEmpty]
    by_cases h : ni < 0
    · simp [native_seq_update, h]
    · simp [native_seq_update, h, Int.le_of_not_gt h]

  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n) (__eo_to_smt r)) =
      __smtx_model_eval M (__eo_to_smt t)
    rw [smtx_eval_str_update_term_eq, hTEval, hNEval, hREval]
    simp [__smtx_model_eval_str_update, hUpdate,
      native_pack_unpack_seq]

  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_update_empty_properties
    (M : SmtModel) (hM : model_wf M)
    (r : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_empty args premises) ->
  AllHaveBoolType (premiseTermList r premises) ->
  __eo_typeof (__eo_cmd_step_proven r CRule.str_update_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList r premises)
    (__eo_cmd_step_proven r CRule.str_update_empty args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven r CRule.str_update_empty args premises ≠
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
                          let P := __eo_state_proven_nth r nIdx
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
                              (__eo_prog_str_update_empty a1 a2 a3 (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_update_empty a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_update_empty_info a1 a2 a3 P hProgRule with
                            ⟨t0, hPremShape, ht0, hProgEq⟩
                          subst t0
                          let lhs := updateEmptyLhs a1 a2 a3
                          let rhs := a1
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
                                eo_interprets M (updateEmptyPremise a1) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_update_empty_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hArgTypes hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_update_empty_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hArgTypes hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
