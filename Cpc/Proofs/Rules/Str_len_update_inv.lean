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

private theorem eo_typeof_str_len_str_update_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_len (__eo_typeof_str_update A B C) ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Int ∧ C = Term.Apply Term.Seq T := by
  cases A <;> simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
        case UOp opB =>
          cases opB <;> simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
          case Int =>
            cases C <;>
              simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
            case Apply g y =>
              cases g <;>
                simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
              case UOp opC =>
                cases opC <;>
                  simp [__eo_typeof_str_update, __eo_typeof_str_len] at h ⊢
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
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_update x y z) =
      __smtx_model_eval_str_update
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_update_slice_length
    (xs ys : List SmtValue) (idx : Nat) (hIdxLe : idx ≤ xs.length) :
    (xs.take idx ++ ys.take (xs.length - idx) ++
      xs.drop (idx + ys.length)).length = xs.length := by
  simp only [List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left hIdxLe]
  by_cases hYs : ys.length ≤ xs.length - idx
  · rw [Nat.min_eq_right hYs]
    omega
  · have hRemLe : xs.length - idx ≤ ys.length := by
      omega
    have hDropZero : xs.length - (idx + ys.length) = 0 := by
      omega
    rw [Nat.min_eq_left hRemLe, hDropZero]
    omega

private theorem native_seq_update_length
    (xs ys : List SmtValue) (i : native_Int) :
    (native_seq_update xs i ys).length = xs.length := by
  unfold native_seq_update
  by_cases hNeg : i < 0
  · rw [show decide (i < 0) = true from decide_eq_true hNeg]
    rfl
  · rw [show decide (i < 0) = false from decide_eq_false hNeg]
    by_cases hHigh : Int.ofNat xs.length ≤ i
    · simp [hHigh]
      rw [show
          (if (↑xs.length : native_Int) ≤ i then xs
            else
              List.take (Int.toNat i) xs ++
                (List.take (xs.length - Int.toNat i) ys ++
                  List.drop (Int.toNat i + ys.length) xs)) = xs from
        if_pos hHigh]
    · simp [hHigh]
      have hNonneg : 0 ≤ i := int_nonneg_of_not_neg hNeg
      let idx := Int.toNat i
      have hCast : Int.ofNat idx = i := Int.toNat_of_nonneg hNonneg
      have hIdxLe : idx ≤ xs.length := by
        exact Int.ofNat_le.mp <| by
          calc
            (idx : Int) = i := hCast
            _ ≤ Int.ofNat xs.length := Int.le_of_lt (Int.lt_of_not_ge hHigh)
      rw [show
          (if (↑xs.length : native_Int) ≤ i then xs
            else
              List.take (Int.toNat i) xs ++
                (List.take (xs.length - Int.toNat i) ys ++
                  List.drop (Int.toNat i + ys.length) xs)) =
            List.take (Int.toNat i) xs ++
              (List.take (xs.length - Int.toNat i) ys ++
                List.drop (Int.toNat i + ys.length) xs) from
        if_neg hHigh]
      simpa [idx] using native_seq_update_slice_length xs ys idx hIdxLe

private theorem typed___eo_prog_str_len_update_inv_impl
    (t n r : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_len_update_inv t n r) := by
  let upd := Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r
  let lhs := Term.Apply Term.str_len upd
  let rhs := Term.Apply Term.str_len t
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hUpdTy :
      __smtx_typeof (__eo_to_smt upd) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n) (__eo_to_smt r)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_update_eq, hTSmtTy, hNSmtTy, hRSmtTy]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_len
          (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n) (__eo_to_smt r))) =
      SmtType.Int
    rw [typeof_str_len_eq]
    rw [show
        __smtx_typeof
            (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n)
              (__eo_to_smt r)) =
          SmtType.Seq (__eo_to_smt_type T) by
      change __smtx_typeof (__eo_to_smt upd) =
        SmtType.Seq (__eo_to_smt_type T)
      exact hUpdTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt t)) = SmtType.Int
    rw [typeof_str_len_eq, hTSmtTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hNNotStuck : n ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hRNotStuck : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProg :
      __eo_prog_str_len_update_inv t n r =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_len_update_inv t n r =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_len
                (Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r)))
            (Term.Apply Term.str_len t) := by
      cases ht : t <;> cases hn : n <;> cases hr : r <;> first
        | exact False.elim (hTNotStuck ht)
        | exact False.elim (hNNotStuck hn)
        | exact False.elim (hRNotStuck hr)
        | rfl
    simpa [lhs, rhs, upd] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_len_update_inv_impl
    (M : SmtModel) (hM : model_wf M) (t n r : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_len_update_inv t n r) true := by
  let upd := Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r
  let lhs := Term.Apply Term.str_len upd
  let rhs := Term.Apply Term.str_len t
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hNNotStuck : n ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hRNotStuck : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProg :
      __eo_prog_str_len_update_inv t n r =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_len_update_inv t n r =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_len
                (Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r)))
            (Term.Apply Term.str_len t) := by
      cases ht : t <;> cases hn : n <;> cases hr : r <;> first
        | exact False.elim (hTNotStuck ht)
        | exact False.elim (hNNotStuck hn)
        | exact False.elim (hRNotStuck hr)
        | rfl
    simpa [lhs, rhs, upd] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_len_update_inv_impl t n r hTTrans hNTrans hRTrans
        hTTy hNTy hRTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases int_value_canonical hNEvalTy with ⟨i, hNEval⟩
  rcases seq_value_canonical hREvalTy with ⟨sr, hREval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_len
          (SmtTerm.str_update (__eo_to_smt t) (__eo_to_smt n) (__eo_to_smt r))) =
      __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t))
    rw [smtx_eval_str_len_term_eq, smtx_eval_str_update_term_eq,
      smtx_eval_str_len_term_eq]
    rw [hTEval, hNEval, hREval]
    simp [__smtx_model_eval_str_update, __smtx_model_eval_str_len,
      native_seq_len, Smtm.native_unpack_pack_seq, native_seq_update_length]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_len_update_inv_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_update_inv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_len_update_inv args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_update_inv args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_len_update_inv args premises ≠
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
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
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
                      have hA3NotStuck : a3 ≠ Term.Stuck := by
                        intro hStuck
                        subst a3
                        apply hProg
                        cases a1 <;> cases a2 <;> rfl
                      let upd :=
                        Term.Apply (Term.Apply (Term.Apply Term.str_update a1) a2) a3
                      let lhs := Term.Apply Term.str_len upd
                      let rhs := Term.Apply Term.str_len a1
                      have hProgEq :
                          __eo_cmd_step_proven s CRule.str_len_update_inv
                            (CArgList.cons a1
                              (CArgList.cons a2
                                (CArgList.cons a3 CArgList.nil)))
                            CIndexList.nil =
                            Term.Apply (Term.Apply Term.eq lhs) rhs := by
                        have hProgEqRaw :
                            __eo_cmd_step_proven s CRule.str_len_update_inv
                              (CArgList.cons a1
                                (CArgList.cons a2
                                  (CArgList.cons a3 CArgList.nil)))
                              CIndexList.nil =
                              Term.Apply
                                (Term.Apply Term.eq
                                  (Term.Apply Term.str_len
                                    (Term.Apply
                                      (Term.Apply
                                        (Term.Apply Term.str_update a1) a2)
                                      a3)))
                                (Term.Apply Term.str_len a1) := by
                          cases hA1 : a1 <;> cases hA2 : a2 <;>
                            cases hA3 : a3 <;> first
                            | exact False.elim (hA1NotStuck hA1)
                            | exact False.elim (hA2NotStuck hA2)
                            | exact False.elim (hA3NotStuck hA3)
                            | rfl
                        simpa [lhs, rhs, upd] using hProgEqRaw
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
                        change __eo_typeof_str_len
                            (__eo_typeof_str_update (__eo_typeof a1)
                              (__eo_typeof a2) (__eo_typeof a3)) ≠ Term.Stuck
                          at hLhsNotStuck
                        exact eo_typeof_str_len_str_update_args_of_ne_stuck
                          (__eo_typeof a1) (__eo_typeof a2) (__eo_typeof a3)
                          hLhsNotStuck
                      rcases hArgTypes with ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                      have hProps :
                          StepRuleProperties M (premiseTermList s CIndexList.nil)
                            (__eo_prog_str_len_update_inv a1 a2 a3) := by
                        refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_len_update_inv_impl a1 a2 a3
                            hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty)⟩
                        intro _hTrue
                        exact facts___eo_prog_str_len_update_inv_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty
                      change StepRuleProperties M []
                        (__eo_prog_str_len_update_inv a1 a2 a3)
                      simpa [premiseTermList] using hProps
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
