module

public import Cpc.Proofs.RuleSupport.ReLoopElimSupport
import all Cpc.Proofs.RuleSupport.ReLoopElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReLoopNegProof

private abbrev mkGtEq (x y : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y))
    (Term.Boolean true)

private abbrev lhs (n m r : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.re_loop n m) r

private abbrev rhs : Term :=
  Term.UOp UserOp.re_none

private abbrev concl (n m r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs n m r)) rhs

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not, SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

private theorem eo_and_eq_true {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  unfold __eo_and at h
  split at h
  · rename_i b1 b2
    simp only [Term.Boolean.injEq, SmtEval.native_and, Bool.and_eq_true] at h
    exact ⟨by rw [h.1], by rw [h.2]⟩
  · rename_i w1 n1 w2 n2
    simp only [__eo_requires, native_ite] at h
    split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

private theorem eval_smt_numeral (M : SmtModel) (n : Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_2]

private theorem prog_form (n m r P : Term)
    (hNe : __eo_prog_re_loop_neg n m r (Proof.pf P) ≠ Term.Stuck) :
    P = mkGtEq n m ∧
      __eo_prog_re_loop_neg n m r (Proof.pf P) = concl n m r := by
  unfold __eo_prog_re_loop_neg at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i heqP
    injection heqP with hP
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    obtain ⟨hN, hM⟩ := eo_and_eq_true hReqArg
    have hnEq := eo_eq_eq_true hN
    have hmEq := eo_eq_eq_true hM
    rw [hnEq, hmEq] at hP
    exact ⟨hP, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem gt_neg_one_true_num_nonneg (t : Term)
    (h : __eo_gt t (Term.Numeral (-1 : native_Int)) = Term.Boolean true) :
    ∃ n : Int, t = Term.Numeral n ∧ native_zleq 0 n = true := by
  cases t with
  | Numeral n =>
      have hLt : (-1 : Int) < n := by
        simpa [__eo_gt, native_zlt] using h
      have hLe : (0 : Int) ≤ n := by omega
      exact ⟨n, rfl, by simpa [native_zleq] using hLe⟩
  | Rational q =>
      simp [__eo_gt] at h
  | Binary w n =>
      simp [__eo_gt, __eo_requires, native_ite, native_teq] at h
  | _ =>
      simp [__eo_gt] at h

private theorem eo_typeof_re_loop_eq_reglan_inv
    (Tn n Tm m Tr : Term)
    (h : __eo_typeof_re_loop Tn n Tm m Tr = Term.UOp UserOp.RegLan) :
    ∃ lo hi : Int,
      n = Term.Numeral lo ∧
      m = Term.Numeral hi ∧
      native_zleq 0 lo = true ∧
      native_zleq 0 hi = true ∧
      Tr = Term.UOp UserOp.RegLan := by
  have hNe : __eo_typeof_re_loop Tn n Tm m Tr ≠ Term.Stuck := by
    rw [h]
    native_decide
  unfold __eo_typeof_re_loop at h hNe
  split at h
  · cases h
  · cases h
  · rename_i hTn hTm hTr
    have hOuterNe :
        __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_requires (__eo_gt m (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.UOp UserOp.RegLan)) ≠ Term.Stuck := by
      simpa using hNe
    have hNReq : __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hOuterNe
    have hInnerEq := eo_requires_eq_result_of_ne_stuck _ _ _ hOuterNe
    have hInnerNe :
        __eo_requires (__eo_gt m (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.UOp UserOp.RegLan) ≠ Term.Stuck := by
      intro hStuck
      rw [hInnerEq, hStuck] at h
      cases h
    have hMReq : __eo_gt m (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hInnerNe
    rcases gt_neg_one_true_num_nonneg n hNReq with ⟨lo, hn, hlo⟩
    rcases gt_neg_one_true_num_nonneg m hMReq with ⟨hi, hm, hhi⟩
    exact ⟨lo, hi, hn, hm, hlo, hhi, rfl⟩
  · cases h

private theorem typed_concl
    (r : Term) (lo hi : Int)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hLo : native_zleq 0 lo = true)
    (hHi : native_zleq 0 hi = true) :
    RuleProofs.eo_has_bool_type (concl (Term.Numeral lo) (Term.Numeral hi) r) := by
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs (Term.Numeral lo) (Term.Numeral hi) r)) =
        SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_loop (SmtTerm.Numeral lo) (SmtTerm.Numeral hi) (__eo_to_smt r)) =
      SmtType.RegLan
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop, hRTy, hLo, hHi, native_ite]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
    rw [__smtx_typeof.eq_def] <;> simp only
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhs (Term.Numeral lo) (Term.Numeral hi) r) rhs
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; decide)

private theorem zlt_of_gt_premise
    (M : SmtModel) (n m : Term) (lo hi : Int)
    (hn : n = Term.Numeral lo) (hm : m = Term.Numeral hi)
    (hPrem : eo_interprets M (mkGtEq n m) true) :
    native_zlt hi lo = true := by
  have hRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n) m) (Term.Boolean true) hPrem
  have hGtEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n) m)) =
        SmtValue.Boolean (native_zlt hi lo) := by
    subst n
    subst m
    change __smtx_model_eval M
        (SmtTerm.gt (SmtTerm.Numeral lo) (SmtTerm.Numeral hi)) =
      SmtValue.Boolean (native_zlt hi lo)
    simp [__smtx_model_eval, eval_smt_numeral, __smtx_model_eval_gt,
      __smtx_model_eval_lt]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    rw [__smtx_model_eval.eq_1]
  rw [hGtEval, hTrueEval] at hRel
  have hEq :
      SmtValue.Boolean (native_zlt hi lo) = SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hRel
  simpa using hEq

private theorem facts
    (M : SmtModel) (hM : model_wf M) (r : Term)
    (lo hi : Int)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hLo : native_zleq 0 lo = true)
    (hHi : native_zleq 0 hi = true)
    (hPrem : eo_interprets M (mkGtEq (Term.Numeral lo) (Term.Numeral hi)) true) :
    eo_interprets M (concl (Term.Numeral lo) (Term.Numeral hi) r) true := by
  have hBool := typed_concl r lo hi hRTy hLo hHi
  have hRNN : term_has_non_none_type (__eo_to_smt r) := by
    unfold term_has_non_none_type
    rw [hRTy]
    intro h
    cases h
  have hREvalTy := type_preservation M hM (__eo_to_smt r) hRNN
  rw [hRTy] at hREvalTy
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hGt : native_zlt hi lo = true :=
    zlt_of_gt_premise M (Term.Numeral lo) (Term.Numeral hi) lo hi rfl rfl hPrem
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt (lhs (Term.Numeral lo) (Term.Numeral hi) r)) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M
        (SmtTerm.re_loop (SmtTerm.Numeral lo) (SmtTerm.Numeral hi) (__eo_to_smt r)) =
      SmtValue.RegLan native_re_none
    simp only [__smtx_model_eval]
    rw [hREval]
    simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_ite, hGt]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_def] <;> simp only
  exact RuleProofs.eo_interprets_eq_of_rel M
      (lhs (Term.Numeral lo) (Term.Numeral hi) r) rhs hBool <| by
    rw [hLhsEval, hRhsEval]
    change SmtValue.Boolean (native_re_ext_eq native_re_none native_re_none) =
      SmtValue.Boolean true
    congr
    simp

end ReLoopNegProof

public theorem cmd_step_re_loop_neg_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_loop_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_loop_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_loop_neg args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_loop_neg args premises ≠ Term.Stuck :=
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
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n1 premises =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
                          show StepRuleProperties M [__eo_state_proven_nth s n1]
                            (__eo_prog_re_loop_neg a1 a2 a3
                              (Proof.pf (__eo_state_proven_nth s n1)))
                          generalize hP : __eo_state_proven_nth s n1 = P
                          have hProgNe :
                              __eo_prog_re_loop_neg a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck := by
                            rw [← hP]
                            change __eo_cmd_step_proven s CRule.re_loop_neg
                                (CArgList.cons a1
                                  (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                                (CIndexList.cons n1 CIndexList.nil) ≠ Term.Stuck
                            exact hProg
                          obtain ⟨hPremShape, hProgEq⟩ :=
                            ReLoopNegProof.prog_form a1 a2 a3 P hProgNe
                          have hResultTyProg :
                              __eo_typeof
                                  (__eo_prog_re_loop_neg a1 a2 a3 (Proof.pf P)) =
                                Term.Bool := by
                            rw [← hP]
                            change __eo_typeof
                                (__eo_cmd_step_proven s CRule.re_loop_neg
                                  (CArgList.cons a1
                                    (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                                  (CIndexList.cons n1 CIndexList.nil)) = Term.Bool
                            exact hResultTy
                          have hConclTy :
                              __eo_typeof (ReLoopNegProof.concl a1 a2 a3) =
                                Term.Bool := by
                            rw [hProgEq] at hResultTyProg
                            exact hResultTyProg
                          have hLhsTy :
                              __eo_typeof (ReLoopNegProof.lhs a1 a2 a3) =
                                Term.UOp UserOp.RegLan := by
                            change __eo_typeof_eq
                                (__eo_typeof (ReLoopNegProof.lhs a1 a2 a3))
                                (__eo_typeof ReLoopNegProof.rhs) =
                              Term.Bool at hConclTy
                            have hTyEq :=
                              support_eo_typeof_eq_bool_operands_eq
                                (__eo_typeof (ReLoopNegProof.lhs a1 a2 a3))
                                (__eo_typeof ReLoopNegProof.rhs) hConclTy
                            simpa [ReLoopNegProof.rhs] using hTyEq
                          have hLoopInv :
                              ∃ lo hi : Int,
                                a1 = Term.Numeral lo ∧
                                a2 = Term.Numeral hi ∧
                                native_zleq 0 lo = true ∧
                                native_zleq 0 hi = true ∧
                                __eo_typeof a3 = Term.UOp UserOp.RegLan := by
                            change __eo_typeof_re_loop (__eo_typeof a1) a1
                                (__eo_typeof a2) a2 (__eo_typeof a3) =
                              Term.UOp UserOp.RegLan at hLhsTy
                            exact ReLoopNegProof.eo_typeof_re_loop_eq_reglan_inv
                              (__eo_typeof a1) a1 (__eo_typeof a2) a2
                              (__eo_typeof a3) hLhsTy
                          rcases hLoopInv with
                            ⟨lo, hi, hA1, hA2, hLo, hHi, hA3Ty⟩
                          have hA3SmtTy :
                              __smtx_typeof (__eo_to_smt a3) = SmtType.RegLan := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a3) =
                                  __eo_to_smt_type (__eo_typeof a3) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a3 hA3Trans
                            rw [hA3Ty] at hTyRaw
                            exact hTyRaw
                          subst a1
                          subst a2
                          have hBool :=
                            ReLoopNegProof.typed_concl a3 lo hi hA3SmtTy hLo hHi
                          rw [hProgEq]
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            hBool⟩
                          intro hEv
                          have hPrem :
                              eo_interprets M
                                (ReLoopNegProof.mkGtEq
                                  (Term.Numeral lo) (Term.Numeral hi)) true := by
                            have h := hEv.true_here P (by simp)
                            rwa [hPremShape] at h
                          exact ReLoopNegProof.facts M hM a3 lo hi hA3SmtTy hLo hHi hPrem
