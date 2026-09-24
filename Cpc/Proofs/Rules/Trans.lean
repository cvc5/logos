module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Lemma about `eo_requires_not_stuck`. -/
theorem eo_requires_not_stuck (x1 x2 x3 : Term) :
  __eo_requires x1 x2 x3 ≠ Term.Stuck ->
  x1 = x2 ∧ x1 ≠ Term.Stuck ∧ x3 ≠ Term.Stuck := by
  intro hReq
  by_cases hEq : x1 = x2
  · by_cases hStuck : x1 = Term.Stuck
    · have hX2Stuck : x2 = Term.Stuck := by simpa [hEq] using hStuck
      exact False.elim <| hReq (by
        simp [__eo_requires, native_teq, hEq, hX2Stuck, native_ite, native_not,
          SmtEval.native_not])
    · refine ⟨hEq, hStuck, ?_⟩
      intro hX3
      exact hReq (by
        simp [__eo_requires, native_teq, hEq, hX3, native_ite, native_not,
          SmtEval.native_not])
  · exact False.elim <| hReq (by
      simp [__eo_requires, native_teq, hEq, native_ite])

/-- Derives `eo_requires_eq` from `eq_not_stuck`. -/
theorem eo_requires_eq_of_eq_not_stuck (x1 x2 x3 : Term) :
  x1 = x2 ->
  x1 ≠ Term.Stuck ->
  __eo_requires x1 x2 x3 = x3 := by
  intro hEq hNotStuck
  subst x2
  cases x1 <;> simp [__eo_requires, native_teq, native_ite, native_not,
    SmtEval.native_not] at hNotStuck ⊢

/-- Lemma about `mk_trans_step_eq`. -/
theorem mk_trans_step_eq (t1 t2 t3 t4 tail : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4))
        tail) =
    __eo_requires t2 t3 (__mk_trans t1 t4 tail) := by
  intro _ _
  simp [__mk_trans]

/-- Lemma about `mk_trans_base_eq`. -/
theorem mk_trans_base_eq (t1 t2 : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 (Term.Boolean true) =
    Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2 := by
  intro _ _
  simp [__mk_trans]

/-- Derives `term_ne_stuck` from `smt_type_not_none`. -/
theorem term_ne_stuck_of_smt_type_not_none (t : Term) :
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
  t ≠ Term.Stuck := by
  exact RuleProofs.term_ne_stuck_of_has_smt_translation t

/-- Derives `mk_trans_shape` from `not_stuck`. -/
private theorem mk_trans_shape_of_not_stuck (t1 t2 tail : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 tail ≠ Term.Stuck ->
  tail = Term.Boolean true ∨
    ∃ t3 t4 tail',
      tail =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4))
          tail' := by
  intro hT1 hT2 hProg
  cases tail with
  | Apply f tail' =>
      cases f with
      | Apply g eq34 =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  cases eq34 with
                  | Apply g2 t4 =>
                      cases g2 with
                      | Apply g3 t3 =>
                          cases g3 with
                          | UOp op2 =>
                              cases op2 with
                              | eq =>
                                  exact Or.inr ⟨t3, t4, tail', rfl⟩
                              | _ =>
                                  exact False.elim (hProg (by simp [__mk_trans]))
                          | _ =>
                              exact False.elim (hProg (by simp [__mk_trans]))
                      | _ =>
                          exact False.elim (hProg (by simp [__mk_trans]))
                  | _ =>
                      exact False.elim (hProg (by simp [__mk_trans]))
              | _ =>
                  exact False.elim (hProg (by simp [__mk_trans]))
          | _ =>
              exact False.elim (hProg (by simp [__mk_trans]))
      | _ =>
          exact False.elim (hProg (by simp [__mk_trans]))
  | Boolean b =>
      cases b with
      | false =>
          exact False.elim (hProg (by simp [__mk_trans]))
      | true =>
          exact Or.inl rfl
  | _ =>
      exact False.elim (hProg (by simp [__mk_trans]))

/-- Lemma about `sizeOf_lt_trans_tail`. -/
private theorem sizeOf_lt_trans_tail (t3 t4 tail : Term) :
  sizeOf tail <
    sizeOf
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4))
        tail) := by
  simp
  omega

/-- Transitivity lemma for `typed_mk`. -/
private theorem typed_mk_trans (M : SmtModel) (t1 t2 tail : Term) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
        tail) true ->
    __mk_trans t1 t2 tail ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__mk_trans t1 t2 tail) := by
  intro hChainTrue hProg
  let eq12 := Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2
  have hEq12True : eo_interprets M eq12 true := by
    simpa [eq12] using RuleProofs.eo_interprets_and_left M eq12 tail hChainTrue
  rcases RuleProofs.eo_eq_operands_same_smt_type M t1 t2 hEq12True with ⟨hTy12, hT1Ty⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t1 hT1Ty
  have hT2Ty : __smtx_typeof (__eo_to_smt t2) ≠ SmtType.None := by
    rwa [← hTy12]
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t2 hT2Ty
  rcases mk_trans_shape_of_not_stuck t1 t2 tail hT1NotStuck hT2NotStuck hProg with hTail
  cases hTail with
  | inl hBase =>
      subst hBase
      rw [mk_trans_base_eq t1 t2 hT1NotStuck hT2NotStuck]
      exact RuleProofs.eo_has_bool_type_eq_of_true M t1 t2 hEq12True
  | inr hStep =>
      rcases hStep with ⟨t3, t4, tail', hTail⟩
      subst hTail
      let eq34 := Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4
      have hTailTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) eq34) tail') true := by
        simpa [eq12, eq34] using
          RuleProofs.eo_interprets_and_right M eq12
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) eq34) tail') hChainTrue
      have hEq34True : eo_interprets M eq34 true := by
        simpa [eq34] using
          RuleProofs.eo_interprets_and_left M eq34 tail' hTailTrue
      have hRestTrue : eo_interprets M tail' true := by
        simpa [eq34] using
          RuleProofs.eo_interprets_and_right M eq34 tail' hTailTrue
      have hReqNotStuck :
          __eo_requires t2 t3 (__mk_trans t1 t4 tail') ≠ Term.Stuck := by
        rw [← mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
        exact hProg
      rcases eo_requires_not_stuck t2 t3 (__mk_trans t1 t4 tail') hReqNotStuck with
        ⟨h23, _hT2NotStuck, hRecNotStuck⟩
      have hEq24True :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t2) t4) true := by
        simpa [eq34, h23] using hEq34True
      have hEq14True :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4) true :=
        RuleProofs.eo_interprets_eq_trans M t1 t2 t4 hEq12True hEq24True
      have hCompressedTrue :
          eo_interprets M
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4))
              tail') true :=
        RuleProofs.eo_interprets_and_intro M
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4) tail'
          hEq14True hRestTrue
      rw [mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
      rw [eo_requires_eq_of_eq_not_stuck t2 t3 (__mk_trans t1 t4 tail') h23 hT2NotStuck]
      exact typed_mk_trans M t1 t4 tail' hCompressedTrue hRecNotStuck
termination_by sizeOf tail
decreasing_by
  simpa [hTail] using sizeOf_lt_trans_tail t3 t4 tail'

/-- Derives `typed_mk_trans` from `bool_chain`. -/
private theorem typed_mk_trans_of_bool_chain (t1 t2 tail : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
        tail) ->
    __mk_trans t1 t2 tail ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__mk_trans t1 t2 tail) := by
  intro hChainBool hProg
  let eq12 := Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2
  have hEq12Bool : RuleProofs.eo_has_bool_type eq12 := by
    simpa [eq12] using RuleProofs.eo_has_bool_type_and_left eq12 tail hChainBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t1 t2 hEq12Bool with
    ⟨hTy12, hT1Ty⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t1 hT1Ty
  have hT2Ty : __smtx_typeof (__eo_to_smt t2) ≠ SmtType.None := by
    rwa [← hTy12]
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t2 hT2Ty
  rcases mk_trans_shape_of_not_stuck t1 t2 tail hT1NotStuck hT2NotStuck hProg with hTail
  cases hTail with
  | inl hBase =>
      subst hBase
      rw [mk_trans_base_eq t1 t2 hT1NotStuck hT2NotStuck]
      exact hEq12Bool
  | inr hStep =>
      rcases hStep with ⟨t3, t4, tail', hTail⟩
      subst hTail
      let eq34 := Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4
      have hTailBool :
          RuleProofs.eo_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) eq34) tail') := by
        simpa [eq12, eq34] using
          RuleProofs.eo_has_bool_type_and_right eq12
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) eq34) tail') hChainBool
      have hEq34Bool : RuleProofs.eo_has_bool_type eq34 := by
        simpa [eq34] using
          RuleProofs.eo_has_bool_type_and_left eq34 tail' hTailBool
      have hRestBool : RuleProofs.eo_has_bool_type tail' := by
        simpa [eq34] using
          RuleProofs.eo_has_bool_type_and_right eq34 tail' hTailBool
      have hReqNotStuck :
          __eo_requires t2 t3 (__mk_trans t1 t4 tail') ≠ Term.Stuck := by
        rw [← mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
        exact hProg
      rcases eo_requires_not_stuck t2 t3 (__mk_trans t1 t4 tail') hReqNotStuck with
        ⟨h23, _hT2NotStuck, hRecNotStuck⟩
      have hEq24Bool :
          RuleProofs.eo_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t2) t4) := by
        simpa [eq34, h23] using hEq34Bool
      have hEq14Bool :
          RuleProofs.eo_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4) :=
        RuleProofs.eo_has_bool_type_eq_of_bool_chain t1 t2 t4 hEq12Bool hEq24Bool
      have hCompressedBool :
          RuleProofs.eo_has_bool_type
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4))
              tail') :=
        RuleProofs.eo_has_bool_type_and_of_bool_args
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4) tail' hEq14Bool hRestBool
      rw [mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
      rw [eo_requires_eq_of_eq_not_stuck t2 t3 (__mk_trans t1 t4 tail') h23 hT2NotStuck]
      exact typed_mk_trans_of_bool_chain t1 t4 tail' hCompressedBool hRecNotStuck
termination_by sizeOf tail
decreasing_by
  simpa [hTail] using sizeOf_lt_trans_tail t3 t4 tail'

/-- Transitivity lemma for `correct_mk`. -/
private theorem correct_mk_trans (M : SmtModel) (t1 t2 tail : Term) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
        tail) true ->
    __mk_trans t1 t2 tail ≠ Term.Stuck ->
    eo_interprets M (__mk_trans t1 t2 tail) true := by
  intro hChainTrue hProg
  let eq12 := Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2
  have hEq12True : eo_interprets M eq12 true := by
    simpa [eq12] using RuleProofs.eo_interprets_and_left M eq12 tail hChainTrue
  rcases RuleProofs.eo_eq_operands_same_smt_type M t1 t2 hEq12True with ⟨hTy12, hT1Ty⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t1 hT1Ty
  have hT2Ty : __smtx_typeof (__eo_to_smt t2) ≠ SmtType.None := by
    rwa [← hTy12]
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t2 hT2Ty
  rcases mk_trans_shape_of_not_stuck t1 t2 tail hT1NotStuck hT2NotStuck hProg with hTail
  cases hTail with
  | inl hBase =>
      subst hBase
      rw [mk_trans_base_eq t1 t2 hT1NotStuck hT2NotStuck]
      exact hEq12True
  | inr hStep =>
      rcases hStep with ⟨t3, t4, tail', hTail⟩
      subst hTail
      let eq34 := Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4
      have hTailTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) eq34) tail') true := by
        simpa [eq12, eq34] using
          RuleProofs.eo_interprets_and_right M eq12
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) eq34) tail') hChainTrue
      have hEq34True : eo_interprets M eq34 true := by
        simpa [eq34] using
          RuleProofs.eo_interprets_and_left M eq34 tail' hTailTrue
      have hRestTrue : eo_interprets M tail' true := by
        simpa [eq34] using
          RuleProofs.eo_interprets_and_right M eq34 tail' hTailTrue
      have hReqNotStuck :
          __eo_requires t2 t3 (__mk_trans t1 t4 tail') ≠ Term.Stuck := by
        rw [← mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
        exact hProg
      rcases eo_requires_not_stuck t2 t3 (__mk_trans t1 t4 tail') hReqNotStuck with
        ⟨h23, _hT2NotStuck, hRecNotStuck⟩
      have hEq24True :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t2) t4) true := by
        simpa [eq34, h23] using hEq34True
      have hEq14True :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4) true :=
        RuleProofs.eo_interprets_eq_trans M t1 t2 t4 hEq12True hEq24True
      have hCompressedTrue :
          eo_interprets M
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4))
              tail') true :=
        RuleProofs.eo_interprets_and_intro M
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t4) tail'
          hEq14True hRestTrue
      rw [mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
      rw [eo_requires_eq_of_eq_not_stuck t2 t3 (__mk_trans t1 t4 tail') h23 hT2NotStuck]
      exact correct_mk_trans M t1 t4 tail' hCompressedTrue hRecNotStuck
termination_by sizeOf tail
decreasing_by
  simpa [hTail] using sizeOf_lt_trans_tail t3 t4 tail'

/-- Shows that the EO program for `trans_impl` is well typed. -/
theorem typed___eo_prog_trans_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_trans (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) :=
by
  intro hX1Bool hProg
  cases x1 with
  | Apply f tail =>
      cases f with
      | Apply g eq12 =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  cases eq12 with
                  | Apply g2 t2 =>
                      cases g2 with
                      | Apply g3 t1 =>
                          cases g3 with
                          | UOp op2 =>
                              cases op2 with
                              | eq =>
                                  simpa [__eo_prog_trans] using
                                    typed_mk_trans_of_bool_chain t1 t2 tail hX1Bool hProg
                              | _ =>
                                  exact False.elim (hProg (by simp [__eo_prog_trans]))
                          | _ =>
                              exact False.elim (hProg (by simp [__eo_prog_trans]))
                      | _ =>
                          exact False.elim (hProg (by simp [__eo_prog_trans]))
                  | _ =>
                      exact False.elim (hProg (by simp [__eo_prog_trans]))
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_trans]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_trans]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_trans]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_trans]))

/-- Proves correctness of the EO program for `trans_impl`. -/
theorem correct___eo_prog_trans_impl
    (M : SmtModel) (_hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) ->
  eo_interprets M (__eo_prog_trans (Proof.pf x1)) true :=
by
  intro hX1True hTy
  have hProg : __eo_prog_trans (Proof.pf x1) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type (__eo_prog_trans (Proof.pf x1)) hTy
  cases x1 with
  | Apply f tail =>
      cases f with
      | Apply g eq12 =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  cases eq12 with
                  | Apply g2 t2 =>
                      cases g2 with
                      | Apply g3 t1 =>
                          cases g3 with
                          | UOp op2 =>
                              cases op2 with
                              | eq =>
                                  simpa [__eo_prog_trans] using
                                    correct_mk_trans M t1 t2 tail hX1True hProg
                              | _ =>
                                  exact False.elim (hProg (by simp [__eo_prog_trans]))
                          | _ =>
                              exact False.elim (hProg (by simp [__eo_prog_trans]))
                      | _ =>
                          exact False.elim (hProg (by simp [__eo_prog_trans]))
                  | _ =>
                      exact False.elim (hProg (by simp [__eo_prog_trans]))
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_trans]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_trans]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_trans]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_trans]))

/-- Derives the checker facts exposed by the EO program for `trans_impl`. -/
theorem facts___eo_prog_trans_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_trans (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_trans (Proof.pf x1)) true :=
by
  intro hXTrue hProg
  let hXBool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hXTrue
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) :=
    typed___eo_prog_trans_impl x1 hXBool hProg
  exact correct___eo_prog_trans_impl M hM x1 hXTrue hBool

/-- Packages the properties required for the `trans` checker step. -/
public theorem cmd_step_trans_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.trans args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.trans args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.trans args premises) :=
by
  intro _hCmdTrans hPremises hResultTy
  have hProg : __eo_cmd_step_proven s CRule.trans args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      have hProgTrans :
          __eo_prog_trans (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
            Term.Stuck := by
        change __eo_cmd_step_proven s CRule.trans CArgList.nil premises ≠ Term.Stuck at hProg
        change __eo_prog_trans (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
          Term.Stuck
        exact hProg
      refine ⟨?_, ?_⟩
      · intro hTrue
        change eo_interprets M
          (__eo_prog_trans (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
        rw [mk_premise_list_and_eq_premiseAndFormulaList]
        exact facts___eo_prog_trans_impl M hM (premiseAndFormulaList (premiseTermList s premises))
          (premiseAndFormulaList_true_of_all_true M (premiseTermList s premises) hTrue.true_here)
          (by
            rw [mk_premise_list_and_eq_premiseAndFormulaList] at hProgTrans
            exact hProgTrans)
      · change RuleProofs.eo_has_smt_translation
          (__eo_prog_trans (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
        apply RuleProofs.eo_has_smt_translation_of_has_bool_type
        rw [mk_premise_list_and_eq_premiseAndFormulaList]
        exact typed___eo_prog_trans_impl (premiseAndFormulaList (premiseTermList s premises))
          (premiseAndFormulaList_has_bool_type (premiseTermList s premises) hPremises)
          (by
            rw [mk_premise_list_and_eq_premiseAndFormulaList] at hProgTrans
            exact hProgTrans)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
