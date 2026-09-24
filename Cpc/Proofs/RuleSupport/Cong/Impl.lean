module

public import Cpc.Proofs.RuleSupport.Cong.TrueSpine
import all Cpc.Proofs.RuleSupport.Cong.TrueSpine

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

private theorem congStableSpine_eq_true
    (M : SmtModel) (hM : model_wf M) (t rhs : Term) :
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    CongStableSpine M t rhs ->
    eo_interprets M (mkEq t rhs) true := by
  intro hEqBool hSpine
  by_cases hForall :
      ∃ xs body,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body
  · rcases hForall with ⟨xs, body, rfl⟩
    have hTrans :
        RuleProofs.eo_has_smt_translation
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) := by
      have hLeftNN :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
          rhs hEqBool).2
      simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
    have hBinderTypesWf : QuantifierBinderTypesWf xs :=
      quantifierBinderTypesWf_of_forall_translation xs body hTrans
    exact congStableSpine_quantifier_eq_true
      M hM UserOp.forall xs body rhs (Or.inl rfl)
      hBinderTypesWf hEqBool hSpine
  · by_cases hExists :
        ∃ xs body,
          t = Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body
    · rcases hExists with ⟨xs, body, rfl⟩
      have hTrans :
          RuleProofs.eo_has_smt_translation
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) := by
        have hLeftNN :=
          (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)
            rhs hEqBool).2
        simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
      have hBinderTypesWf : QuantifierBinderTypesWf xs :=
        quantifierBinderTypesWf_of_exists_translation xs body hTrans
      exact congStableSpine_quantifier_eq_true
        M hM UserOp.exists xs body rhs (Or.inr rfl)
        hBinderTypesWf hEqBool hSpine
    · exact congTrueSpine_eq_true M hM t rhs
        ⟨(fun xs body h => hForall ⟨xs, body, h⟩),
          (fun xs body h => hExists ⟨xs, body, h⟩)⟩ hEqBool
        (congTrueSpine_of_congStableSpine M hM hSpine)

/--
Rebase a stable congruence spine across a model with the same globals.

The public spelling keeps downstream rules from depending on the private
`mkEq` name hidden inside the spine constructors.
-/
theorem congStableSpine_rebase_of_globals
    {M N : SmtModel} :
    model_agrees_on_globals M N ->
    ∀ {t rhs : Term},
      CongStableSpine M t rhs ->
      CongStableSpine N t rhs :=
  congStableSpine_rebase

/-- Interpret a stable congruence spine as a true public equality term. -/
theorem eqTerm_true_of_congStableSpine
    (M : SmtModel) (hM : model_wf M) (t rhs : Term) :
    RuleProofs.eo_has_bool_type (eqTerm t rhs) ->
    CongStableSpine M t rhs ->
    eo_interprets M (eqTerm t rhs) true := by
  intro hEqBool hSpine
  simpa [eqTerm] using
    congStableSpine_eq_true M hM t rhs
      (by simpa [eqTerm] using hEqBool) hSpine

/--
A stable congruence spine gives an equality fact that is stable under variable
model changes.
-/
theorem stableInAnyVarModel_eqTerm_of_congStableSpine
    (M : SmtModel) (t rhs : Term)
    (hEqBool : RuleProofs.eo_has_bool_type (eqTerm t rhs))
    (hSpine : CongStableSpine M t rhs) :
    StableInAnyVarModel M (eqTerm t rhs) := by
  intro N hN hAgree
  simpa [eqTerm] using
    congStableSpine_eq_true N hN t rhs
      (by simpa [eqTerm] using hEqBool)
      (congStableSpine_rebase hAgree hSpine)

private theorem mk_nary_cong_rhs_congTypeSpine_of_list :
    ∀ (ps : List Term) (t : Term),
      RuleProofs.eo_has_smt_translation t ->
      AllHaveBoolType ps ->
      __mk_nary_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongTypeSpine t (__mk_nary_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
          __eo_l_1___mk_nary_cong_rhs] at hProg ⊢
      all_goals exact CongTypeSpine.refl _
  | cons p ps ih =>
      intro t hTrans hBool hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply fn argTail =>
                        cases fn with
                        | Apply f s₁ =>
                            have hHeadBool :
                                RuleProofs.eo_has_bool_type (mkEq lhs tail) := by
                              simpa [premiseAndFormulaList, mkEq] using
                                hBool (mkEq lhs tail) (by simp [mkEq])
                            have hRestBool : AllHaveBoolType ps := by
                              intro q hq
                              exact hBool q (by simp [hq])
                            have hCond :
                                __eo_eq s₁ lhs = Term.Boolean true := by
                              cases hEq : __eo_eq s₁ lhs <;>
                                simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                                  __eo_l_1___mk_nary_cong_rhs, __eo_ite, hEq,
                                  native_teq, native_ite] at hProg
                              case Boolean b =>
                                cases b with
                                | false =>
                                    simp  at hProg
                                | true =>
                                    rfl
                            have hStepEq :=
                              mk_nary_cong_rhs_step_eq_of_eo_eq_true
                                f s₁ argTail lhs tail (premiseAndFormulaList ps)
                                hCond
                            have hMkApplyNN :
                                __eo_mk_apply (Term.Apply f tail)
                                    (__mk_nary_cong_rhs argTail
                                      (premiseAndFormulaList ps)) ≠
                                  Term.Stuck := by
                              rw [← hStepEq]
                              exact hProg
                            have hRecNN :
                                __mk_nary_cong_rhs argTail
                                    (premiseAndFormulaList ps) ≠
                                  Term.Stuck :=
                              eo_mk_apply_right_ne_stuck_of_ne_stuck
                                (Term.Apply f tail)
                                (__mk_nary_cong_rhs argTail
                                  (premiseAndFormulaList ps))
                                hMkApplyNN
                            have hArgTailTrans :
                                RuleProofs.eo_has_smt_translation argTail :=
                              eo_apply_apply_arg_has_translation_of_has_translation
                                f s₁ argTail hTrans
                            have hRec :=
                              ih argTail hArgTailTrans hRestBool hRecNN
                            have hRecBool :
                                RuleProofs.eo_has_bool_type
                                  (mkEq argTail
                                    (__mk_nary_cong_rhs argTail
                                      (premiseAndFormulaList ps))) :=
                              congTypeSpine_eq_has_bool_type argTail
                                (__mk_nary_cong_rhs argTail
                                  (premiseAndFormulaList ps))
                                hArgTailTrans hRec
                            have hLhs : lhs = s₁ :=
                              eq_of_eo_eq_true s₁ lhs hCond
                            subst lhs
                            change CongTypeSpine
                              (Term.Apply (Term.Apply f s₁) argTail)
                              (__mk_nary_cong_rhs
                                (Term.Apply (Term.Apply f s₁) argTail)
                                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                                  (mkEq s₁ tail)) (premiseAndFormulaList ps)))
                            rw [hStepEq]
                            rw [eo_mk_apply_eq_of_ne_stuck
                              (Term.Apply f tail)
                              (__mk_nary_cong_rhs argTail
                                (premiseAndFormulaList ps))
                              (by simp) hRecNN]
                            exact CongTypeSpine.app
                              (CongTypeSpine.app (CongTypeSpine.refl f)
                                hHeadBool)
                              hRecBool
                        | _ =>
                            exact False.elim (hProg (by
                              simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                                __eo_l_1___mk_nary_cong_rhs]))
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                            __eo_l_1___mk_nary_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                          __eo_l_1___mk_nary_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                        __eo_l_1___mk_nary_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                    __eo_l_1___mk_nary_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                __eo_l_1___mk_nary_cong_rhs]))

private theorem mk_nary_cong_rhs_congStableSpine_of_list
    (M : SmtModel) (hM : model_wf M) :
    ∀ (ps : List Term) (t : Term),
      RulePremiseEvidence M ps ->
      RuleProofs.eo_has_smt_translation t ->
      __mk_nary_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongStableSpine M t (__mk_nary_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
          __eo_l_1___mk_nary_cong_rhs] at hProg ⊢
      all_goals exact CongStableSpine.refl _
  | cons p ps ih =>
      intro t hEvidence hTrans hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply fn argTail =>
                        cases fn with
                        | Apply f s₁ =>
                            have hHeadStable :
                                StableInAnyVarModel M (mkEq lhs tail) := by
                              intro N hN hAgree
                              exact hEvidence.true_in_var_model N hN hAgree
                                (mkEq lhs tail) (by simp [mkEq])
                            have hRestEvidence :
                                RulePremiseEvidence M ps := by
                              refine ⟨?_, ?_⟩
                              · intro q hq
                                exact hEvidence q (by simp [hq])
                              · intro N hN hAgree q hq
                                exact hEvidence.true_in_var_model N hN hAgree
                                  q (by simp [hq])
                            have hRestBool : AllHaveBoolType ps := by
                              intro q hq
                              exact RuleProofs.eo_has_bool_type_of_interprets_true
                                M q (hRestEvidence.true_here q hq)
                            have hCond :
                                __eo_eq s₁ lhs = Term.Boolean true := by
                              cases hEq : __eo_eq s₁ lhs <;>
                                simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                                  __eo_l_1___mk_nary_cong_rhs, __eo_ite, hEq,
                                  native_teq, native_ite] at hProg
                              case Boolean b =>
                                cases b with
                                | false =>
                                    simp at hProg
                                | true =>
                                    rfl
                            have hStepEq :=
                              mk_nary_cong_rhs_step_eq_of_eo_eq_true
                                f s₁ argTail lhs tail (premiseAndFormulaList ps)
                                hCond
                            have hMkApplyNN :
                                __eo_mk_apply (Term.Apply f tail)
                                    (__mk_nary_cong_rhs argTail
                                      (premiseAndFormulaList ps)) ≠
                                  Term.Stuck := by
                              rw [← hStepEq]
                              exact hProg
                            have hRecNN :
                                __mk_nary_cong_rhs argTail
                                    (premiseAndFormulaList ps) ≠
                                  Term.Stuck :=
                              eo_mk_apply_right_ne_stuck_of_ne_stuck
                                (Term.Apply f tail)
                                (__mk_nary_cong_rhs argTail
                                  (premiseAndFormulaList ps))
                                hMkApplyNN
                            have hArgTailTrans :
                                RuleProofs.eo_has_smt_translation argTail :=
                              eo_apply_apply_arg_has_translation_of_has_translation
                                f s₁ argTail hTrans
                            have hRec :=
                              ih argTail hRestEvidence hArgTailTrans hRecNN
                            have hRecType :=
                              mk_nary_cong_rhs_congTypeSpine_of_list ps
                                argTail hArgTailTrans hRestBool hRecNN
                            have hRecBool :
                                RuleProofs.eo_has_bool_type
                                  (mkEq argTail
                                    (__mk_nary_cong_rhs argTail
                                      (premiseAndFormulaList ps))) :=
                              congTypeSpine_eq_has_bool_type argTail
                                (__mk_nary_cong_rhs argTail
                                  (premiseAndFormulaList ps))
                                hArgTailTrans hRecType
                            have hRecStable :
                                StableInAnyVarModel M
                                  (mkEq argTail
                                    (__mk_nary_cong_rhs argTail
                                      (premiseAndFormulaList ps))) := by
                              intro N hN hAgree
                              exact congStableSpine_eq_true N hN argTail
                                (__mk_nary_cong_rhs argTail
                                  (premiseAndFormulaList ps))
                                hRecBool (congStableSpine_rebase hAgree hRec)
                            have hLhs : lhs = s₁ :=
                              eq_of_eo_eq_true s₁ lhs hCond
                            subst lhs
                            change CongStableSpine M
                              (Term.Apply (Term.Apply f s₁) argTail)
                              (__mk_nary_cong_rhs
                                (Term.Apply (Term.Apply f s₁) argTail)
                                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                                  (mkEq s₁ tail)) (premiseAndFormulaList ps)))
                            rw [hStepEq]
                            rw [eo_mk_apply_eq_of_ne_stuck
                              (Term.Apply f tail)
                              (__mk_nary_cong_rhs argTail
                                (premiseAndFormulaList ps))
                              (by simp) hRecNN]
                            exact CongStableSpine.app
                              (CongStableSpine.app (CongStableSpine.refl f)
                                hHeadStable)
                              hRecStable
                        | _ =>
                            exact False.elim (hProg (by
                              simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                                __eo_l_1___mk_nary_cong_rhs]))
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                            __eo_l_1___mk_nary_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                          __eo_l_1___mk_nary_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                        __eo_l_1___mk_nary_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                    __eo_l_1___mk_nary_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                __eo_l_1___mk_nary_cong_rhs]))

private inductive TypedListShape : Term -> Prop where
  | nil (T : Term) :
      TypedListShape (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T)
  | cons (x xs : Term) :
      TypedListShape xs ->
      TypedListShape
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs)

private inductive PairwiseListTypeSpine : Term -> Term -> Prop where
  | refl (xs : Term) : PairwiseListTypeSpine xs xs
  | cons {x y xs ys : Term} :
      RuleProofs.eo_has_bool_type (mkEq x y) ->
      PairwiseListTypeSpine xs ys ->
      PairwiseListTypeSpine
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs)
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) y) ys)

private inductive PairwiseListTrueSpine (M : SmtModel) : Term -> Term -> Prop where
  | refl (xs : Term) : PairwiseListTrueSpine M xs xs
  | cons {x y xs ys : Term} :
      eo_interprets M (mkEq x y) true ->
      PairwiseListTrueSpine M xs ys ->
      PairwiseListTrueSpine M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs)
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) y) ys)

private theorem typedListShape_of_typed_list_elem_type_non_none :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      TypedListShape xs := by
  intro xs hNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            exact TypedListShape.nil tail
          all_goals
            exact False.elim (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                have hTailNN :
                    __eo_to_smt_typed_list_elem_type tail ≠ SmtType.None := by
                  intro hTail
                  apply hNN
                  cases hHead : __smtx_typeof (__eo_to_smt head) <;>
                    simp [__eo_to_smt_typed_list_elem_type, hHead, hTail,
                      native_ite, native_Teq]
                exact TypedListShape.cons head tail
                  (typedListShape_of_typed_list_elem_type_non_none tail hTailNN)
              all_goals
                exact False.elim
                  (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs => xs

private theorem typedListShape_of_distinct_translation (xs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) ->
    TypedListShape xs := by
  intro hTrans
  have hElemNN :
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hElemNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.None
    simp [hElemNone, native_ite, native_Teq, TranslationProofs.smtx_typeof_none]
  exact typedListShape_of_typed_list_elem_type_non_none xs hElemNN

private theorem mk_nary_cong_rhs_pairwiseListTypeSpine_of_list :
    ∀ (ps : List Term) (xs : Term),
      TypedListShape xs ->
      AllHaveBoolType ps ->
      __mk_nary_cong_rhs xs (premiseAndFormulaList ps) ≠ Term.Stuck ->
      PairwiseListTypeSpine xs
        (__mk_nary_cong_rhs xs (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro xs _ _ _
      cases xs <;>
        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
          __eo_l_1___mk_nary_cong_rhs]
      all_goals exact PairwiseListTypeSpine.refl _
  | cons p ps ih =>
      intro xs hShape hBool hProg
      cases hShape with
      | nil T =>
          exact False.elim (hProg (by
            cases p <;>
              simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                __eo_l_1___mk_nary_cong_rhs]))
      | cons s₁ tail hTailShape =>
          cases p with
          | Apply pf rhsHead =>
              cases pf with
              | Apply pg lhs =>
                  cases pg with
                  | UOp op =>
                      cases op
                      case eq =>
                        have hHeadBool :
                            RuleProofs.eo_has_bool_type (mkEq lhs rhsHead) := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hBool (mkEq lhs rhsHead) (by simp [mkEq])
                        have hRestBool : AllHaveBoolType ps := by
                          intro q hq
                          exact hBool q (by simp [hq])
                        have hCond :
                            __eo_eq s₁ lhs = Term.Boolean true := by
                          cases hEq : __eo_eq s₁ lhs <;>
                            simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                              __eo_l_1___mk_nary_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp  at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_nary_cong_rhs_step_eq_of_eo_eq_true
                            (Term.UOp UserOp._at__at_TypedList_cons)
                            s₁ tail lhs rhsHead (premiseAndFormulaList ps)
                            hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (Term.Apply
                                  (Term.UOp UserOp._at__at_TypedList_cons)
                                  rhsHead)
                                (__mk_nary_cong_rhs tail
                                  (premiseAndFormulaList ps)) ≠ Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_nary_cong_rhs tail
                                (premiseAndFormulaList ps) ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (Term.Apply
                              (Term.UOp UserOp._at__at_TypedList_cons)
                              rhsHead)
                            (__mk_nary_cong_rhs tail
                              (premiseAndFormulaList ps))
                            hMkApplyNN
                        have hRec :=
                          ih tail hTailShape hRestBool hRecNN
                        have hLhs : lhs = s₁ :=
                          eq_of_eo_eq_true s₁ lhs hCond
                        subst lhs
                        change PairwiseListTypeSpine
                          (Term.Apply
                            (Term.Apply
                              (Term.UOp UserOp._at__at_TypedList_cons) s₁)
                            tail)
                          (__mk_nary_cong_rhs
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at__at_TypedList_cons) s₁)
                              tail)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.and)
                                (mkEq s₁ rhsHead))
                              (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons)
                            rhsHead)
                          (__mk_nary_cong_rhs tail
                            (premiseAndFormulaList ps))
                          (by simp) hRecNN]
                        exact PairwiseListTypeSpine.cons hHeadBool hRec
                      all_goals
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                            __eo_l_1___mk_nary_cong_rhs]))
                  | _ =>
                      exact False.elim (hProg (by
                        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                          __eo_l_1___mk_nary_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                      __eo_l_1___mk_nary_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                  __eo_l_1___mk_nary_cong_rhs]))

private theorem mk_nary_cong_rhs_pairwiseListTrueSpine_of_list
    (M : SmtModel) :
    ∀ (ps : List Term) (xs : Term),
      TypedListShape xs ->
      AllInterpretedTrue M ps ->
      __mk_nary_cong_rhs xs (premiseAndFormulaList ps) ≠ Term.Stuck ->
      PairwiseListTrueSpine M xs
        (__mk_nary_cong_rhs xs (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro xs _ _ _
      cases xs <;>
        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
          __eo_l_1___mk_nary_cong_rhs]
      all_goals exact PairwiseListTrueSpine.refl _
  | cons p ps ih =>
      intro xs hShape hTrue hProg
      cases hShape with
      | nil T =>
          exact False.elim (hProg (by
            cases p <;>
              simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                __eo_l_1___mk_nary_cong_rhs]))
      | cons s₁ tail hTailShape =>
          cases p with
          | Apply pf rhsHead =>
              cases pf with
              | Apply pg lhs =>
                  cases pg with
                  | UOp op =>
                      cases op
                      case eq =>
                        have hHeadTrue :
                            eo_interprets M (mkEq lhs rhsHead) true := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hTrue (mkEq lhs rhsHead) (by simp [mkEq])
                        have hRestTrue : AllInterpretedTrue M ps := by
                          intro q hq
                          exact hTrue q (by simp [hq])
                        have hCond :
                            __eo_eq s₁ lhs = Term.Boolean true := by
                          cases hEq : __eo_eq s₁ lhs <;>
                            simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                              __eo_l_1___mk_nary_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp  at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_nary_cong_rhs_step_eq_of_eo_eq_true
                            (Term.UOp UserOp._at__at_TypedList_cons)
                            s₁ tail lhs rhsHead (premiseAndFormulaList ps)
                            hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (Term.Apply
                                  (Term.UOp UserOp._at__at_TypedList_cons)
                                  rhsHead)
                                (__mk_nary_cong_rhs tail
                                  (premiseAndFormulaList ps)) ≠ Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_nary_cong_rhs tail
                                (premiseAndFormulaList ps) ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (Term.Apply
                              (Term.UOp UserOp._at__at_TypedList_cons)
                              rhsHead)
                            (__mk_nary_cong_rhs tail
                              (premiseAndFormulaList ps))
                            hMkApplyNN
                        have hRec :=
                          ih tail hTailShape hRestTrue hRecNN
                        have hLhs : lhs = s₁ :=
                          eq_of_eo_eq_true s₁ lhs hCond
                        subst lhs
                        change PairwiseListTrueSpine M
                          (Term.Apply
                            (Term.Apply
                              (Term.UOp UserOp._at__at_TypedList_cons) s₁)
                            tail)
                          (__mk_nary_cong_rhs
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at__at_TypedList_cons) s₁)
                              tail)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.and)
                                (mkEq s₁ rhsHead))
                              (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons)
                            rhsHead)
                          (__mk_nary_cong_rhs tail
                            (premiseAndFormulaList ps))
                          (by simp) hRecNN]
                        exact PairwiseListTrueSpine.cons hHeadTrue hRec
                      all_goals
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                            __eo_l_1___mk_nary_cong_rhs]))
                  | _ =>
                      exact False.elim (hProg (by
                        simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                          __eo_l_1___mk_nary_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                      __eo_l_1___mk_nary_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                simp [premiseAndFormulaList, __mk_nary_cong_rhs,
                  __eo_l_1___mk_nary_cong_rhs]))

private theorem typed_list_elem_type_cons_non_none
    (x xs : Term) :
    __eo_to_smt_typed_list_elem_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_typed_list_elem_type xs ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
  intro hNN
  cases hx : __smtx_typeof (__eo_to_smt x) <;>
    cases hxs : __eo_to_smt_typed_list_elem_type xs <;>
    simp [__eo_to_smt_typed_list_elem_type, hx, hxs, native_ite, native_Teq]
      at hNN ⊢
  all_goals exact hNN

private theorem smtx_typeof_distinct_pairs_of_elem_type :
    ∀ (s : SmtTerm) (xs : Term),
      __smtx_typeof s = __eo_to_smt_typed_list_elem_type xs ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt_distinct_pairs s xs) = SmtType.Bool := by
  intro s xs hS hElemNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
            rw [__smtx_typeof.eq_1]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_elem_type_cons_non_none head tail hElemNN with
                  ⟨hHeadTail, hHeadNN, hTailNN⟩
                have hSElem :
                    __smtx_typeof s = __smtx_typeof (__eo_to_smt head) := by
                  have hConsElem :
                      __eo_to_smt_typed_list_elem_type
                          (Term.Apply
                            (Term.Apply
                              (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) =
                        __smtx_typeof (__eo_to_smt head) := by
                    change
                      native_ite
                          (native_Teq (__smtx_typeof (__eo_to_smt head))
                            (__eo_to_smt_typed_list_elem_type tail))
                          (__smtx_typeof (__eo_to_smt head)) SmtType.None =
                        __smtx_typeof (__eo_to_smt head)
                    rw [hHeadTail]
                    cases hHeadTy : __smtx_typeof (__eo_to_smt head) <;>
                      simp [hHeadTy, native_ite, native_Teq] at hHeadNN ⊢
                  rw [hS, hConsElem]
                have hEqBool :
                    __smtx_typeof
                      (SmtTerm.eq s (__eo_to_smt head)) = SmtType.Bool := by
                  rw [typeof_eq_eq]
                  exact (RuleProofs.smtx_typeof_eq_bool_iff
                    (__smtx_typeof s)
                    (__smtx_typeof (__eo_to_smt head))).mpr
                    ⟨hSElem, by rw [hSElem]; exact hHeadNN⟩
                have hNotBool :
                    __smtx_typeof
                      (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head))) =
                        SmtType.Bool := by
                  rw [typeof_not_eq, hEqBool]
                  rfl
                have hRec :
                    __smtx_typeof
                      (__eo_to_smt_distinct_pairs s tail) = SmtType.Bool :=
                  smtx_typeof_distinct_pairs_of_elem_type s tail
                    (hSElem.trans hHeadTail)
                    hTailNN
                change
                  __smtx_typeof
                    (SmtTerm.and
                      (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                      (__eo_to_smt_distinct_pairs s tail)) = SmtType.Bool
                rw [typeof_and_eq, hNotBool, hRec]
                rfl
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by s xs _ _ => xs

private theorem smtx_typeof_distinct_of_elem_type_non_none :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool := by
  intro xs hElemNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
            rw [__smtx_typeof.eq_1]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_elem_type_cons_non_none head tail hElemNN with
                  ⟨hHeadTail, _hHeadNN, hTailNN⟩
                have hPairs :
                    __smtx_typeof
                      (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail) =
                        SmtType.Bool :=
                  smtx_typeof_distinct_pairs_of_elem_type
                    (__eo_to_smt head) tail hHeadTail hTailNN
                have hTailDistinct :
                    __smtx_typeof (__eo_to_smt_distinct tail) =
                      SmtType.Bool :=
                  smtx_typeof_distinct_of_elem_type_non_none tail hTailNN
                change
                  __smtx_typeof
                    (SmtTerm.and
                      (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                      (__eo_to_smt_distinct tail)) = SmtType.Bool
                rw [typeof_and_eq, hPairs, hTailDistinct]
                rfl
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs _ => xs

private theorem distinct_has_translation_of_elem_type_non_none
    (xs : Term) :
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) := by
  intro hElemNN
  unfold RuleProofs.eo_has_smt_translation
  change
    __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) ≠ SmtType.None
  have hGuard :
      native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None =
        false := by
    cases hElem : __eo_to_smt_typed_list_elem_type xs <;>
      simp [hElem] at hElemNN ⊢
    all_goals rfl
  rw [hGuard]
  simp [native_ite]
  rw [smtx_typeof_distinct_of_elem_type_non_none xs hElemNN]
  simp

private theorem pairwiseListTypeSpine_elem_type_eq :
    ∀ {xs ys : Term},
      PairwiseListTypeSpine xs ys ->
      __eo_to_smt_typed_list_elem_type xs =
        __eo_to_smt_typed_list_elem_type ys := by
  intro xs ys hSpine
  induction hSpine with
  | refl xs =>
      rfl
  | cons hHead _ ih =>
      have hHeadTy :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          _ _ hHead).1
      change
        native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt _))
              (__eo_to_smt_typed_list_elem_type _))
            (__smtx_typeof (__eo_to_smt _)) SmtType.None =
          native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt _))
              (__eo_to_smt_typed_list_elem_type _))
            (__smtx_typeof (__eo_to_smt _)) SmtType.None
      rw [hHeadTy, ih]

private theorem pairwiseListTypeSpine_distinct_has_translation
    {xs ys : Term} :
    PairwiseListTypeSpine xs ys ->
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) ->
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) ys) := by
  intro hSpine hTrans
  have hElemNN :
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hElemNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.None
    simp [hElemNone, native_ite, native_Teq, TranslationProofs.smtx_typeof_none]
  have hElemEq := pairwiseListTypeSpine_elem_type_eq hSpine
  exact distinct_has_translation_of_elem_type_non_none ys
    (by rw [← hElemEq]; exact hElemNN)

private theorem distinct_has_bool_type_of_translation (xs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.UOp UserOp.distinct) xs) := by
  intro hTrans
  have hElemNN :
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hElemNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.None
    simp [hElemNone, native_ite, native_Teq, TranslationProofs.smtx_typeof_none]
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.Bool
  have hGuard :
      native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None =
        false := by
    cases hElem : __eo_to_smt_typed_list_elem_type xs <;>
      simp [hElem] at hElemNN ⊢
    all_goals rfl
  rw [hGuard]
  simp [native_ite]
  exact smtx_typeof_distinct_of_elem_type_non_none xs hElemNN

private theorem eo_to_smt_distinct_eq_of_translation (xs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) ->
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) =
      __eo_to_smt_distinct xs := by
  intro hTrans
  have hElemNN :
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hElemNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.None
    simp [hElemNone, native_ite, native_Teq, TranslationProofs.smtx_typeof_none]
  change
    native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
      __eo_to_smt_distinct xs
  have hGuard :
      native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None =
        false := by
    cases hElem : __eo_to_smt_typed_list_elem_type xs <;>
      simp [hElem] at hElemNN ⊢
    all_goals rfl
  rw [hGuard]
  simp [native_ite]

private theorem smt_value_rel_model_eval_not_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_not a) (__smtx_model_eval_not b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq] at hRel ⊢
  case Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp  at hRel ⊢

private theorem smt_value_rel_model_eval_and_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_and a b) (__smtx_model_eval_and c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_and, native_veq] at hAC hBD ⊢
  case Boolean.Boolean.Boolean.Boolean a₁ b₁ c₁ d₁ =>
    cases a₁ <;> cases b₁ <;> cases c₁ <;> cases d₁ <;>
      simp  at hAC hBD ⊢

/-- SMT Boolean negation is congruent with respect to `smt_value_rel`. -/
theorem smt_value_rel_not_congr
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_not a) (__smtx_model_eval_not b) :=
  smt_value_rel_model_eval_not_of_rel a b

/-- SMT Boolean conjunction is congruent with respect to `smt_value_rel`. -/
theorem smt_value_rel_and_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_and a b) (__smtx_model_eval_and c d) :=
  smt_value_rel_model_eval_and_of_rel a b c d

/-- SMT Boolean disjunction is congruent with respect to `smt_value_rel`. -/
theorem smt_value_rel_or_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_or a b) (__smtx_model_eval_or c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq] at hAC hBD ⊢
  case Boolean.Boolean.Boolean.Boolean a₁ b₁ c₁ d₁ =>
    cases a₁ <;> cases b₁ <;> cases c₁ <;> cases d₁ <;>
      simp at hAC hBD ⊢

/-- SMT Boolean implication is congruent with respect to `smt_value_rel`. -/
theorem smt_value_rel_imp_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_imp a b) (__smtx_model_eval_imp c d) := by
  intro hAC hBD
  unfold __smtx_model_eval_imp
  exact smt_value_rel_or_congr
    (__smtx_model_eval_not a) b (__smtx_model_eval_not c) d
    (smt_value_rel_not_congr a c hAC) hBD

/-- SMT Boolean exclusive-or is congruent with respect to `smt_value_rel`. -/
theorem smt_value_rel_xor_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_xor a b) (__smtx_model_eval_xor c d) := by
  intro hAC hBD
  unfold __smtx_model_eval_xor
  exact smt_value_rel_not_congr
    (__smtx_model_eval_eq a b) (__smtx_model_eval_eq c d)
    (smt_value_rel_eq_congr a b c d hAC hBD)

/-- SMT if-then-else is congruent with respect to `smt_value_rel`. -/
theorem smt_value_rel_ite_congr
    (c c' t t' e e' : SmtValue) :
    RuleProofs.smt_value_rel c c' ->
    RuleProofs.smt_value_rel t t' ->
    RuleProofs.smt_value_rel e e' ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_ite c t e) (__smtx_model_eval_ite c' t' e') := by
  intro hCond hThen hElse
  unfold RuleProofs.smt_value_rel at hCond hThen hElse ⊢
  cases c <;> cases c' <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_ite, native_veq]
      at hCond hThen hElse ⊢
  case Boolean.Boolean b b' =>
    cases b <;> cases b' <;>
      simp at hCond hThen hElse ⊢
    · exact hElse
    · exact hThen

private theorem distinct_pairs_rel_same_tail
    (M : SmtModel) (x y : Term) :
    eo_interprets M (mkEq x y) true ->
    ∀ xs,
      TypedListShape xs ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt_distinct_pairs (__eo_to_smt x) xs))
        (__smtx_model_eval M (__eo_to_smt_distinct_pairs (__eo_to_smt y) xs)) := by
  intro hXY xs hShape
  induction hShape with
  | nil T =>
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.Boolean true))
        (__smtx_model_eval M (SmtTerm.Boolean true))
      exact RuleProofs.smt_value_rel_refl _
  | cons a tail hTailShape ih =>
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.not (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt a)))
            (__eo_to_smt_distinct_pairs (__eo_to_smt x) tail)))
        (__smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.not (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt a)))
            (__eo_to_smt_distinct_pairs (__eo_to_smt y) tail)))
      rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_9]
      apply smt_value_rel_model_eval_and_of_rel
      · rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_7,
          smtx_model_eval_eq_term_eq, smtx_model_eval_eq_term_eq]
        apply smt_value_rel_model_eval_not_of_rel
        exact smt_value_rel_model_eval_eq_congr
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt a))
          (RuleProofs.eo_interprets_eq_rel M x y hXY)
          (RuleProofs.smt_value_rel_refl _)
      · exact ih

private theorem pairwiseListTrueSpine_distinct_pairs_rel
    (M : SmtModel) (x y : Term) :
    eo_interprets M (mkEq x y) true ->
    ∀ {xs ys : Term},
      TypedListShape xs ->
      PairwiseListTrueSpine M xs ys ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt_distinct_pairs (__eo_to_smt x) xs))
        (__smtx_model_eval M (__eo_to_smt_distinct_pairs (__eo_to_smt y) ys)) := by
  intro hXY xs ys hShape hSpine
  induction hSpine generalizing x y with
  | refl xs =>
      exact distinct_pairs_rel_same_tail M x y hXY xs hShape
  | cons hHead hTail ih =>
      cases hShape with
      | cons a tail hTailShape =>
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (SmtTerm.and
                (SmtTerm.not (SmtTerm.eq (__eo_to_smt x) _))
                _))
            (__smtx_model_eval M
              (SmtTerm.and
                (SmtTerm.not (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt _)))
                (__eo_to_smt_distinct_pairs (__eo_to_smt y) _)))
          rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_9]
          apply smt_value_rel_model_eval_and_of_rel
          · rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_7,
              smtx_model_eval_eq_term_eq, smtx_model_eval_eq_term_eq]
            apply smt_value_rel_model_eval_not_of_rel
            exact smt_value_rel_model_eval_eq_congr
              _ _ _ _
              (RuleProofs.eo_interprets_eq_rel M x y hXY)
              (RuleProofs.eo_interprets_eq_rel M _ _ hHead)
          · exact ih x y hXY hTailShape

private theorem pairwiseListTrueSpine_distinct_rel
    (M : SmtModel) :
    ∀ {xs ys : Term},
      TypedListShape xs ->
      PairwiseListTrueSpine M xs ys ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt_distinct xs))
        (__smtx_model_eval M (__eo_to_smt_distinct ys)) := by
  intro xs ys hShape hSpine
  induction hSpine with
  | refl xs =>
      exact RuleProofs.smt_value_rel_refl _
  | cons hHead hTail ih =>
      cases hShape with
      | cons a tail hTailShape =>
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (SmtTerm.and
                (__eo_to_smt_distinct_pairs (__eo_to_smt _) _)
                (__eo_to_smt_distinct _)))
            (__smtx_model_eval M
              (SmtTerm.and
                (__eo_to_smt_distinct_pairs (__eo_to_smt _) _)
                (__eo_to_smt_distinct _)))
          rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_9]
          apply smt_value_rel_model_eval_and_of_rel
          · exact pairwiseListTrueSpine_distinct_pairs_rel M _ _
              hHead hTailShape hTail
          · exact ih hTailShape

/-- Typing for the generated EO implementation of `cong` over a premise list. -/
theorem typed___eo_prog_cong_impl (t : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  AllHaveBoolType premises ->
  __eo_prog_cong t (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  __eo_typeof (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) =
    Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) := by
  intro hTrans hPremisesBool hProg hProgType
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_cong_rhs t (premiseAndFormulaList premises.reverse)
  have hProgEq :=
    eo_prog_cong_pf_eq_of_ne_stuck t (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠ Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (premiseAndFormulaList premises.reverse)) ≠
        Term.Stuck
    rw [← eo_list_rev_and_premiseAndFormulaList premises]
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongTypeSpine t rhs := by
    simpa [rhs] using
      mk_cong_rhs_congTypeSpine_of_list premises.reverse t
        (all_have_bool_type_reverse premises hPremisesBool) hRhsNN
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) :=
    congTypeSpine_eq_has_bool_type t rhs hTrans hSpine
  rw [hProgEq]
  rw [eo_list_rev_and_premiseAndFormulaList]
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqBool

private theorem congEvidenceSpine_eq_true
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term) (t rhs : Term) :
  RulePremiseEvidence M premises ->
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    CongEvidenceSpine M premises t rhs ->
    eo_interprets M (mkEq t rhs) true := by
  intro hEvidence hEqBool hSpine
  by_cases hForall :
      ∃ xs body,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body
  · rcases hForall with ⟨xs, body, rfl⟩
    have hTrans :
        RuleProofs.eo_has_smt_translation
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) := by
      have hLeftNN :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
          rhs hEqBool).2
      simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
    have hBinderTypesWf : QuantifierBinderTypesWf xs :=
      quantifierBinderTypesWf_of_forall_translation xs body hTrans
    exact congEvidenceSpine_quantifier_eq_true
      M hM premises UserOp.forall xs body rhs (Or.inl rfl)
      hEvidence hBinderTypesWf hEqBool hSpine
  · by_cases hExists :
        ∃ xs body,
          t = Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body
    · rcases hExists with ⟨xs, body, rfl⟩
      have hTrans :
          RuleProofs.eo_has_smt_translation
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) := by
        have hLeftNN :=
          (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)
            rhs hEqBool).2
        simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
      have hBinderTypesWf : QuantifierBinderTypesWf xs :=
        quantifierBinderTypesWf_of_exists_translation xs body hTrans
      exact congEvidenceSpine_quantifier_eq_true
        M hM premises UserOp.exists xs body rhs (Or.inr rfl)
        hEvidence hBinderTypesWf hEqBool hSpine
    · exact congTrueSpine_eq_true M hM t rhs
        ⟨(fun xs body h => hForall ⟨xs, body, h⟩),
          (fun xs body h => hExists ⟨xs, body, h⟩)⟩ hEqBool
        (congTrueSpine_of_congEvidenceSpine M premises hEvidence hSpine)

/-- Correctness for the generated EO implementation of `cong` over a premise list. -/
theorem facts___eo_prog_cong_impl
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  RulePremiseEvidence M premises ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) ->
  __eo_prog_cong t (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  eo_interprets M
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hTrans hEvidence hProgBool hProg
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_cong_rhs t (premiseAndFormulaList premises.reverse)
  have hProgEq :=
    eo_prog_cong_pf_eq_of_ne_stuck t (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠ Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (premiseAndFormulaList premises.reverse)) ≠
        Term.Stuck
    rw [← eo_list_rev_and_premiseAndFormulaList premises]
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hEvidenceRev :
      RulePremiseEvidence M premises.reverse := by
    refine ⟨?_, ?_⟩
    · exact all_interpreted_true_reverse M premises hEvidence.true_here
    · intro N hN hAgree q hq
      exact hEvidence.true_in_var_model N hN hAgree
        q (by simpa using List.mem_reverse.mp hq)
  have hSpine :
      CongEvidenceSpine M premises.reverse t rhs := by
    simpa [rhs] using
      mk_cong_rhs_congEvidenceSpine_of_list M premises.reverse t
        hEvidenceRev.true_here hRhsNN
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) := by
    have hProgBool' := hProgBool
    rw [hProgEq] at hProgBool'
    rw [eo_list_rev_and_premiseAndFormulaList] at hProgBool'
    change RuleProofs.eo_has_bool_type
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
      at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
      (by simp) hRhsNN] at hProgBool'
    exact hProgBool'
  have hEqTrue : eo_interprets M (mkEq t rhs) true :=
    congEvidenceSpine_eq_true M hM premises.reverse t rhs
      hEvidenceRev hEqBool hSpine
  rw [hProgEq]
  rw [eo_list_rev_and_premiseAndFormulaList]
  change eo_interprets M
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs) true
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqTrue

/-- Typing for the generated EO implementation of `nary_cong` over a premise list. -/
theorem typed___eo_prog_nary_cong_impl (t : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  AllHaveBoolType premises ->
  __eo_prog_nary_cong t (Proof.pf (premiseAndFormulaList premises)) ≠
    Term.Stuck ->
  __eo_typeof (__eo_prog_nary_cong t
    (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_nary_cong t (Proof.pf (premiseAndFormulaList premises))) := by
  intro hTrans hPremisesBool hProg _hProgType
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_nary_cong_rhs t (premiseAndFormulaList premises)
  have hProgEq :=
    eo_prog_nary_cong_pf_eq_of_ne_stuck t
      (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠
        Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_nary_cong_rhs t (premiseAndFormulaList premises)) ≠
        Term.Stuck
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongTypeSpine t rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_congTypeSpine_of_list premises t
        hTrans hPremisesBool hRhsNN
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) :=
    congTypeSpine_eq_has_bool_type t rhs hTrans hSpine
  rw [hProgEq]
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqBool

/-- Correctness for the generated EO implementation of `nary_cong` over a premise list. -/
theorem facts___eo_prog_nary_cong_impl
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  RulePremiseEvidence M premises ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_nary_cong t (Proof.pf (premiseAndFormulaList premises))) ->
  __eo_prog_nary_cong t (Proof.pf (premiseAndFormulaList premises)) ≠
    Term.Stuck ->
  eo_interprets M
    (__eo_prog_nary_cong t (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hTrans hEvidence hProgBool hProg
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_nary_cong_rhs t (premiseAndFormulaList premises)
  have hProgEq :=
    eo_prog_nary_cong_pf_eq_of_ne_stuck t
      (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠
        Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_nary_cong_rhs t (premiseAndFormulaList premises)) ≠
        Term.Stuck
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongStableSpine M t rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_congStableSpine_of_list M hM premises t
        hEvidence hTrans hRhsNN
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) := by
    have hProgBool' := hProgBool
    rw [hProgEq] at hProgBool'
    change RuleProofs.eo_has_bool_type
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
      at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
      (by simp) hRhsNN] at hProgBool'
    exact hProgBool'
  have hEqTrue : eo_interprets M (mkEq t rhs) true :=
    congStableSpine_eq_true M hM t rhs hEqBool hSpine
  rw [hProgEq]
  change eo_interprets M
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs) true
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqTrue

/-- Typing for the `distinct`-shaped core of `pairwise_cong`. -/
theorem typed___eo_prog_pairwise_cong_distinct_impl
    (xs : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.UOp UserOp.distinct) xs) ->
  AllHaveBoolType premises ->
  __eo_prog_pairwise_cong (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  __eo_typeof (__eo_prog_pairwise_cong
    (Term.Apply (Term.UOp UserOp.distinct) xs)
    (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_pairwise_cong (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Proof.pf (premiseAndFormulaList premises))) := by
  intro hTrans hPremisesBool hProg _hProgType
  let rhs := __mk_nary_cong_rhs xs (premiseAndFormulaList premises)
  have hOuterNN :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (__eo_mk_apply (Term.UOp UserOp.distinct) rhs) ≠
        Term.Stuck := by
    change
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (__eo_mk_apply (Term.UOp UserOp.distinct)
            (__mk_nary_cong_rhs xs (premiseAndFormulaList premises))) ≠
        Term.Stuck at hProg
    exact hProg
  have hRightApplyNN :
      __eo_mk_apply (Term.UOp UserOp.distinct) rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (__eo_mk_apply (Term.UOp UserOp.distinct) rhs) hOuterNN
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.distinct) rhs hRightApplyNN
  have hShape : TypedListShape xs :=
    typedListShape_of_distinct_translation xs hTrans
  have hSpine :
      PairwiseListTypeSpine xs rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_pairwiseListTypeSpine_of_list premises xs
        hShape hPremisesBool hRhsNN
  have hRightTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.distinct) rhs) :=
    pairwiseListTypeSpine_distinct_has_translation hSpine hTrans
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.UOp UserOp.distinct) xs) :=
    distinct_has_bool_type_of_translation xs hTrans
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.UOp UserOp.distinct) rhs) :=
    distinct_has_bool_type_of_translation rhs hRightTrans
  have hSameTy :
      __smtx_typeof (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.distinct) xs)) =
        __smtx_typeof (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.distinct) rhs)) := by
    unfold RuleProofs.eo_has_bool_type at hLeftBool hRightBool
    rw [hLeftBool, hRightBool]
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (mkEq (Term.Apply (Term.UOp UserOp.distinct) xs)
          (Term.Apply (Term.UOp UserOp.distinct) rhs)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Term.Apply (Term.UOp UserOp.distinct) rhs)
      hSameTy hTrans
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (__eo_mk_apply (Term.UOp UserOp.distinct) rhs))
  rw [eo_mk_apply_eq_of_ne_stuck (Term.UOp UserOp.distinct) rhs
    (by simp) hRhsNN]
  rw [eo_mk_apply_eq_of_ne_stuck
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.distinct) xs))
    (Term.Apply (Term.UOp UserOp.distinct) rhs) (by simp) (by simp)]
  exact hEqBool

/-- Correctness for the `distinct`-shaped core of `pairwise_cong`. -/
theorem facts___eo_prog_pairwise_cong_distinct_impl
    (M : SmtModel) (hM : model_wf M)
    (xs : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.UOp UserOp.distinct) xs) ->
  AllInterpretedTrue M premises ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_pairwise_cong (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Proof.pf (premiseAndFormulaList premises))) ->
  __eo_prog_pairwise_cong (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  eo_interprets M
    (__eo_prog_pairwise_cong (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hTrans hPremisesTrue hProgBool hProg
  let rhs := __mk_nary_cong_rhs xs (premiseAndFormulaList premises)
  have hOuterNN :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (__eo_mk_apply (Term.UOp UserOp.distinct) rhs) ≠
        Term.Stuck := by
    change
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (__eo_mk_apply (Term.UOp UserOp.distinct)
            (__mk_nary_cong_rhs xs (premiseAndFormulaList premises))) ≠
        Term.Stuck at hProg
    exact hProg
  have hRightApplyNN :
      __eo_mk_apply (Term.UOp UserOp.distinct) rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (__eo_mk_apply (Term.UOp UserOp.distinct) rhs) hOuterNN
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.distinct) rhs hRightApplyNN
  have hShape : TypedListShape xs :=
    typedListShape_of_distinct_translation xs hTrans
  have hPremisesBool : AllHaveBoolType premises := by
    intro p hp
    exact RuleProofs.eo_has_bool_type_of_interprets_true M p
      (hPremisesTrue p hp)
  have hTypeSpine :
      PairwiseListTypeSpine xs rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_pairwiseListTypeSpine_of_list premises xs
        hShape hPremisesBool hRhsNN
  have hTrueSpine :
      PairwiseListTrueSpine M xs rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_pairwiseListTrueSpine_of_list M premises xs
        hShape hPremisesTrue hRhsNN
  have hRightTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.distinct) rhs) :=
    pairwiseListTypeSpine_distinct_has_translation hTypeSpine hTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (mkEq (Term.Apply (Term.UOp UserOp.distinct) xs)
          (Term.Apply (Term.UOp UserOp.distinct) rhs)) := by
    have hProgBool' := hProgBool
    change RuleProofs.eo_has_bool_type
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (__eo_mk_apply (Term.UOp UserOp.distinct) rhs)) at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck (Term.UOp UserOp.distinct) rhs
      (by simp) hRhsNN] at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Apply (Term.UOp UserOp.distinct) rhs) (by simp) (by simp)]
      at hProgBool'
    exact hProgBool'
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.distinct) xs)))
        (__smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.distinct) rhs))) := by
    rw [eo_to_smt_distinct_eq_of_translation xs hTrans,
      eo_to_smt_distinct_eq_of_translation rhs hRightTrans]
    exact pairwiseListTrueSpine_distinct_rel M hShape hTrueSpine
  have hEqTrue :
      eo_interprets M
        (mkEq (Term.Apply (Term.UOp UserOp.distinct) xs)
          (Term.Apply (Term.UOp UserOp.distinct) rhs)) true :=
    RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.UOp UserOp.distinct) xs)
      (Term.Apply (Term.UOp UserOp.distinct) rhs)
      hEqBool hRel
  change eo_interprets M
    (__eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (__eo_mk_apply (Term.UOp UserOp.distinct) rhs)) true
  rw [eo_mk_apply_eq_of_ne_stuck (Term.UOp UserOp.distinct) rhs
    (by simp) hRhsNN]
  rw [eo_mk_apply_eq_of_ne_stuck
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.distinct) xs))
    (Term.Apply (Term.UOp UserOp.distinct) rhs) (by simp) (by simp)]
  exact hEqTrue

/-- Typing for the application-shaped core of `pairwise_cong`.

This is the ordinary congruence path, used when the argument itself has an SMT
translation. Operators such as `distinct` need a separate list-aware path. -/
theorem typed___eo_prog_pairwise_cong_apply_impl
    (f xs : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation (Term.Apply f xs) ->
  RuleProofs.eo_has_smt_translation xs ->
  AllHaveBoolType premises ->
  __eo_prog_pairwise_cong (Term.Apply f xs)
      (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  __eo_typeof (__eo_prog_pairwise_cong (Term.Apply f xs)
    (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_pairwise_cong (Term.Apply f xs)
      (Proof.pf (premiseAndFormulaList premises))) := by
  intro hTrans hXsTrans hPremisesBool hProg _hProgType
  let rhs := __mk_nary_cong_rhs xs (premiseAndFormulaList premises)
  have hOuterNN :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
          (__eo_mk_apply f rhs) ≠ Term.Stuck := by
    change
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
          (__eo_mk_apply f
            (__mk_nary_cong_rhs xs (premiseAndFormulaList premises))) ≠
        Term.Stuck at hProg
    exact hProg
  have hRightApplyNN :
      __eo_mk_apply f rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
      (__eo_mk_apply f rhs) hOuterNN
  have hFNN : f ≠ Term.Stuck :=
    eo_mk_apply_left_ne_stuck_of_ne_stuck f rhs hRightApplyNN
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck f rhs hRightApplyNN
  have hArgSpine :
      CongTypeSpine xs rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_congTypeSpine_of_list premises xs
        hXsTrans hPremisesBool hRhsNN
  have hArgEqBool : RuleProofs.eo_has_bool_type (mkEq xs rhs) :=
    congTypeSpine_eq_has_bool_type xs rhs hXsTrans hArgSpine
  have hSpine :
      CongTypeSpine (Term.Apply f xs) (Term.Apply f rhs) :=
    CongTypeSpine.app (CongTypeSpine.refl f) hArgEqBool
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (mkEq (Term.Apply f xs) (Term.Apply f rhs)) :=
    congTypeSpine_eq_has_bool_type (Term.Apply f xs)
      (Term.Apply f rhs) hTrans hSpine
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
      (__eo_mk_apply f rhs))
  rw [eo_mk_apply_eq_of_ne_stuck f rhs hFNN hRhsNN]
  rw [eo_mk_apply_eq_of_ne_stuck
    (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
    (Term.Apply f rhs) (by simp) (by simp)]
  exact hEqBool

/-- Correctness for the application-shaped core of `pairwise_cong`.

This is the ordinary congruence path, used when the argument itself has an SMT
translation. Operators such as `distinct` need a separate list-aware path. -/
theorem facts___eo_prog_pairwise_cong_apply_impl
    (M : SmtModel) (hM : model_wf M)
    (f xs : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation (Term.Apply f xs) ->
  RuleProofs.eo_has_smt_translation xs ->
  RulePremiseEvidence M premises ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_pairwise_cong (Term.Apply f xs)
      (Proof.pf (premiseAndFormulaList premises))) ->
  __eo_prog_pairwise_cong (Term.Apply f xs)
      (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  eo_interprets M
    (__eo_prog_pairwise_cong (Term.Apply f xs)
      (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hTrans hXsTrans hEvidence hProgBool hProg
  let rhs := __mk_nary_cong_rhs xs (premiseAndFormulaList premises)
  have hOuterNN :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
          (__eo_mk_apply f rhs) ≠ Term.Stuck := by
    change
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
          (__eo_mk_apply f
            (__mk_nary_cong_rhs xs (premiseAndFormulaList premises))) ≠
        Term.Stuck at hProg
    exact hProg
  have hRightApplyNN :
      __eo_mk_apply f rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
      (__eo_mk_apply f rhs) hOuterNN
  have hFNN : f ≠ Term.Stuck :=
    eo_mk_apply_left_ne_stuck_of_ne_stuck f rhs hRightApplyNN
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck f rhs hRightApplyNN
  have hArgSpine :
      CongStableSpine M xs rhs := by
    simpa [rhs] using
      mk_nary_cong_rhs_congStableSpine_of_list M hM premises xs
        hEvidence hXsTrans hRhsNN
  have hArgBoolSpine :
      CongTypeSpine xs rhs := by
    have hPremisesBool : AllHaveBoolType premises := by
      intro p hp
      exact RuleProofs.eo_has_bool_type_of_interprets_true M p
        (hEvidence p hp)
    simpa [rhs] using
      mk_nary_cong_rhs_congTypeSpine_of_list premises xs
        hXsTrans hPremisesBool hRhsNN
  have hArgEqBool : RuleProofs.eo_has_bool_type (mkEq xs rhs) :=
    congTypeSpine_eq_has_bool_type xs rhs hXsTrans hArgBoolSpine
  have hArgStable : StableInAnyVarModel M (mkEq xs rhs) := by
    intro N hN hAgree
    exact congStableSpine_eq_true N hN xs rhs hArgEqBool
      (congStableSpine_rebase hAgree hArgSpine)
  have hSpine :
      CongStableSpine M (Term.Apply f xs) (Term.Apply f rhs) :=
    CongStableSpine.app (CongStableSpine.refl f) hArgStable
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (mkEq (Term.Apply f xs) (Term.Apply f rhs)) := by
    have hProgBool' := hProgBool
    change RuleProofs.eo_has_bool_type
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
        (__eo_mk_apply f rhs)) at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck f rhs hFNN hRhsNN] at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
      (Term.Apply f rhs) (by simp) (by simp)] at hProgBool'
    exact hProgBool'
  have hEqTrue :
      eo_interprets M (mkEq (Term.Apply f xs) (Term.Apply f rhs)) true :=
    congStableSpine_eq_true M hM (Term.Apply f xs) (Term.Apply f rhs)
      hEqBool hSpine
  change eo_interprets M
    (__eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
      (__eo_mk_apply f rhs)) true
  rw [eo_mk_apply_eq_of_ne_stuck f rhs hFNN hRhsNN]
  rw [eo_mk_apply_eq_of_ne_stuck
    (Term.Apply (Term.UOp UserOp.eq) (Term.Apply f xs))
    (Term.Apply f rhs) (by simp) (by simp)]
  exact hEqTrue

theorem smt_value_rel_model_eval_apply_of_rel
    (M : SmtModel) (hM : model_wf M)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval M g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval M y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply M (__smtx_model_eval M g) (__smtx_model_eval M y)) :=
  smt_value_rel_model_eval_apply_of_rel_core M hM f g x y
    hAppNN hFy hXy hFRel hXRel

/--
Generic SMT application preserves `smt_value_rel` across two models that agree
on globals.

This is the cross-model form needed by substitution/equality rules: the function
and argument values may be obtained from different variable assignments, while
uninterpreted-function lookup is kept aligned by global agreement.
-/
theorem smt_value_rel_model_eval_apply_of_rel_across_models
    (M N : SmtModel) (hM : model_wf M) (hN : model_wf N)
    (hGlobals : model_agrees_on_globals M N)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval N g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval N y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply N (__smtx_model_eval N g) (__smtx_model_eval N y)) := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, _B, hHead, hX, hA, _hB⟩
  have hFNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    exact smt_type_ne_none_of_apply_head hHead
  have hGNN : term_has_non_none_type g := by
    unfold term_has_non_none_type
    rw [← hFy]
    exact hFNN
  have hXNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hX]
    exact hA
  have hYNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [← hXy]
    exact hXNN
  have hFPres :
      __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
    smt_model_eval_preserves_type_of_non_none M hM f hFNN
  have hGPres :
      __smtx_typeof_value (__smtx_model_eval N g) = __smtx_typeof g :=
    smt_model_eval_preserves_type_of_non_none N hN g hGNN
  have hXPres :
      __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
    smt_model_eval_preserves_type_of_non_none M hM x hXNN
  have hYPres :
      __smtx_typeof_value (__smtx_model_eval N y) = __smtx_typeof y :=
    smt_model_eval_preserves_type_of_non_none N hN y hYNN
  have hFNeReg : __smtx_typeof f ≠ SmtType.RegLan :=
    smt_type_ne_reglan_of_apply_head hHead
  have hANeReg : A ≠ SmtType.RegLan :=
    Smtm.smt_term_fun_like_arg_ne_reglan_of_non_none
      f hFNN hHead
  have hFEq : __smtx_model_eval M f = __smtx_model_eval N g :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      hFPres (by simpa [hFy] using hGPres) hFNeReg hFRel
  have hXEq : __smtx_model_eval M x = __smtx_model_eval N y :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      (by simpa [hX] using hXPres)
      (by
        rw [← hXy, hX] at hYPres
        exact hYPres)
      hANeReg hXRel
  rw [hFEq, hXEq]
  rw [smtx_model_eval_apply_eq_of_globals hGlobals]
  exact RuleProofs.smt_value_rel_refl _

end CongSupport

namespace Smtm

private theorem reglan_rel_model_ext {r r' : SmtRegLan}
    (h : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan r')) :
    ∀ s : native_String, native_string_valid s = true ->
      Smtm.native_str_in_re (impl_native_string_to_values s) r =
        Smtm.native_str_in_re (impl_native_string_to_values s) r' := by
  have hb : native_re_ext_eq r r' = true := by
    have h' : SmtValue.Boolean (native_re_ext_eq r r') =
        SmtValue.Boolean true := h
    simpa using h'
  intro s hs
  by_cases hAll : ∀ str : native_String, native_string_valid str = true ->
      Smtm.native_str_in_re (impl_native_string_to_values str) r =
        Smtm.native_str_in_re (impl_native_string_to_values str) r'
  · exact hAll s hs
  · rw [dif_neg hAll] at hb
    cases hb

private theorem reglan_rel_of_model_ext {r r' : SmtRegLan}
    (h : ∀ s : native_String, native_string_valid s = true ->
      Smtm.native_str_in_re (impl_native_string_to_values s) r =
        Smtm.native_str_in_re (impl_native_string_to_values s) r') :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan r') := by
  show SmtValue.Boolean (native_re_ext_eq r r') = SmtValue.Boolean true
  rw [dif_pos h]

end Smtm

namespace CongSupport

/-! ### Value-level congruence for regular-expression operators

Public lemmas for the rel-coincidence development: rel-related values are
either equal or a pair of extensionally equal `RegLan` values, and every
regex-consuming evaluation operator respects that relation.
-/

/-- Case split for `smt_value_rel`: related values are equal unless both are
`RegLan` values (which are then extensionally equal). -/
theorem smt_value_rel_cases {a b : SmtValue}
    (h : RuleProofs.smt_value_rel a b) :
    a = b ∨ ∃ r r', a = SmtValue.RegLan r ∧ b = SmtValue.RegLan r' := by
  unfold RuleProofs.smt_value_rel at h
  unfold __smtx_model_eval_eq at h
  split at h
  · rename_i r1 r2
    exact Or.inr ⟨r1, r2, rfl, rfl⟩
  · left
    have hveq : native_veq a b = true := by
      simpa using h
    simpa [native_veq] using hveq

/-- Rel-related `RegLan` values agree on membership of valid strings. -/
theorem reglan_valid_ext_of_rel {r r' : SmtRegLan}
    (h : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan r')) :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r = RuleProofs.native_str_in_re s r' := by
  intro s hs
  simpa only [← RuleProofs.native_str_in_re_eq_model] using
    Smtm.reglan_rel_model_ext h s hs

/-- Rel-related `RegLan` values agree on membership of all strings, valid or
not (invalid strings are never members). -/
theorem reglan_ext_of_rel {r r' : SmtRegLan}
    (h : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan r')) :
    ∀ s : native_String,
      RuleProofs.native_str_in_re s r = RuleProofs.native_str_in_re s r' :=
  native_str_in_re_ext_of_valid_ext (reglan_valid_ext_of_rel h)

/-- Converse: agreement on valid strings makes `RegLan` values rel-related. -/
theorem smt_value_rel_reglan_of_valid_ext {r r' : SmtRegLan}
    (h : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r = RuleProofs.native_str_in_re s r') :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan r') := by
  exact Smtm.reglan_rel_of_model_ext (by
    intro s hs
    simpa only [← RuleProofs.native_str_in_re_eq_model] using h s hs)

private theorem valid_ext_refl (r : SmtRegLan) :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r = RuleProofs.native_str_in_re s r :=
  fun _ _ => rfl

private theorem native_re_union_valid_ext_congr
    {r1 r1' r2 r2' : SmtRegLan}
    (h1 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r1 = RuleProofs.native_str_in_re s r1')
    (h2 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r2 = RuleProofs.native_str_in_re s r2') :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s (native_re_union r1 r2) =
        RuleProofs.native_str_in_re s (native_re_union r1' r2') := by
  intro s hs
  change native_str_in_re s (native_re_union r1 r2) =
    native_str_in_re s (native_re_union r1' r2')
  have h1' : native_str_in_re s r1 = native_str_in_re s r1' := by
    simpa [native_str_in_re, RuleProofs.native_str_in_re,
      native_list_in_re] using h1 s hs
  have h2' : native_str_in_re s r2 = native_str_in_re s r2' := by
    simpa [native_str_in_re, RuleProofs.native_str_in_re,
      native_list_in_re] using h2 s hs
  rw [native_str_in_re_re_union, native_str_in_re_re_union, h1', h2']

private theorem native_re_inter_valid_ext_congr
    {r1 r1' r2 r2' : SmtRegLan}
    (h1 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r1 = RuleProofs.native_str_in_re s r1')
    (h2 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r2 = RuleProofs.native_str_in_re s r2') :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s (native_re_inter r1 r2) =
        RuleProofs.native_str_in_re s (native_re_inter r1' r2') := by
  intro s hs
  rw [RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_inter, h1 s hs, h2 s hs]

private theorem native_re_diff_valid_ext_congr
    {r1 r1' r2 r2' : SmtRegLan}
    (h1 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r1 = RuleProofs.native_str_in_re s r1')
    (h2 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r2 = RuleProofs.native_str_in_re s r2') :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s (native_re_diff r1 r2) =
        RuleProofs.native_str_in_re s (native_re_diff r1' r2') := by
  intro s hs
  change native_str_in_re s (native_re_diff r1 r2) =
    native_str_in_re s (native_re_diff r1' r2')
  have h1' : native_str_in_re s r1 = native_str_in_re s r1' := by
    simpa [native_str_in_re, RuleProofs.native_str_in_re,
      native_list_in_re] using h1 s hs
  have h2' : native_str_in_re s r2 = native_str_in_re s r2' := by
    simpa [native_str_in_re, RuleProofs.native_str_in_re,
      native_list_in_re] using h2 s hs
  rw [native_str_in_re_re_diff, native_str_in_re_re_diff, h1', h2']

private theorem native_re_comp_valid_ext_congr
    {r r' : SmtRegLan}
    (h : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r = RuleProofs.native_str_in_re s r') :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s (native_re_comp r) =
        RuleProofs.native_str_in_re s (native_re_comp r') := by
  intro s hs
  rw [RuleProofs.native_str_in_re_re_comp,
    RuleProofs.native_str_in_re_re_comp, h s hs]

private theorem native_re_concat_valid_ext_congr
    {r1 r1' r2 r2' : SmtRegLan}
    (h1 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r1 = RuleProofs.native_str_in_re s r1')
    (h2 : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r2 = RuleProofs.native_str_in_re s r2') :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s (native_re_concat r1 r2) =
        RuleProofs.native_str_in_re s (native_re_concat r1' r2') :=
  fun s _ => native_str_in_re_re_concat_congr s r1 r1' r2 r2' h1 h2

private theorem native_re_mult_valid_ext_congr
    {r r' : SmtRegLan}
    (h : ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s r = RuleProofs.native_str_in_re s r') :
    ∀ s : native_String, native_string_valid s = true ->
      RuleProofs.native_str_in_re s (native_re_mult r) =
        RuleProofs.native_str_in_re s (native_re_mult r') :=
  fun s _ => native_str_in_re_re_mult_congr s r r' h

/-- Binary regex constructors respect `smt_value_rel`. -/
theorem smt_value_rel_re_union_congr {a b c d : SmtValue}
    (hAC : RuleProofs.smt_value_rel a c) (hBD : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_union a b)
      (__smtx_model_eval_re_union c d) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r1, r1', rfl, rfl⟩
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · exact RuleProofs.smt_value_rel_refl _
    · cases a with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_union_valid_ext_congr (valid_ext_refl r0)
              (reglan_valid_ext_of_rel hBD))
      | _ => exact RuleProofs.smt_value_rel_refl _
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · cases b with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_union_valid_ext_congr
              (reglan_valid_ext_of_rel hAC) (valid_ext_refl r0))
      | _ => exact RuleProofs.smt_value_rel_refl _
    · exact smt_value_rel_reglan_of_valid_ext
        (native_re_union_valid_ext_congr
          (reglan_valid_ext_of_rel hAC) (reglan_valid_ext_of_rel hBD))

theorem smt_value_rel_re_inter_congr {a b c d : SmtValue}
    (hAC : RuleProofs.smt_value_rel a c) (hBD : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_inter a b)
      (__smtx_model_eval_re_inter c d) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r1, r1', rfl, rfl⟩
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · exact RuleProofs.smt_value_rel_refl _
    · cases a with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_inter_valid_ext_congr (valid_ext_refl r0)
              (reglan_valid_ext_of_rel hBD))
      | _ => exact RuleProofs.smt_value_rel_refl _
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · cases b with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_inter_valid_ext_congr
              (reglan_valid_ext_of_rel hAC) (valid_ext_refl r0))
      | _ => exact RuleProofs.smt_value_rel_refl _
    · exact smt_value_rel_reglan_of_valid_ext
        (native_re_inter_valid_ext_congr
          (reglan_valid_ext_of_rel hAC) (reglan_valid_ext_of_rel hBD))

theorem smt_value_rel_re_concat_congr {a b c d : SmtValue}
    (hAC : RuleProofs.smt_value_rel a c) (hBD : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_concat a b)
      (__smtx_model_eval_re_concat c d) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r1, r1', rfl, rfl⟩
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · exact RuleProofs.smt_value_rel_refl _
    · cases a with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_concat_valid_ext_congr (valid_ext_refl r0)
              (reglan_valid_ext_of_rel hBD))
      | _ => exact RuleProofs.smt_value_rel_refl _
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · cases b with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_concat_valid_ext_congr
              (reglan_valid_ext_of_rel hAC) (valid_ext_refl r0))
      | _ => exact RuleProofs.smt_value_rel_refl _
    · exact smt_value_rel_reglan_of_valid_ext
        (native_re_concat_valid_ext_congr
          (reglan_valid_ext_of_rel hAC) (reglan_valid_ext_of_rel hBD))

theorem smt_value_rel_re_diff_congr {a b c d : SmtValue}
    (hAC : RuleProofs.smt_value_rel a c) (hBD : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_diff a b)
      (__smtx_model_eval_re_diff c d) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r1, r1', rfl, rfl⟩
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · exact RuleProofs.smt_value_rel_refl _
    · cases a with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_diff_valid_ext_congr (valid_ext_refl r0)
              (reglan_valid_ext_of_rel hBD))
      | _ => exact RuleProofs.smt_value_rel_refl _
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · cases b with
      | RegLan r0 =>
          exact smt_value_rel_reglan_of_valid_ext
            (native_re_diff_valid_ext_congr
              (reglan_valid_ext_of_rel hAC) (valid_ext_refl r0))
      | _ => exact RuleProofs.smt_value_rel_refl _
    · exact smt_value_rel_reglan_of_valid_ext
        (native_re_diff_valid_ext_congr
          (reglan_valid_ext_of_rel hAC) (reglan_valid_ext_of_rel hBD))

/-- Unary regex constructors respect `smt_value_rel`. -/
theorem smt_value_rel_re_mult_congr {a c : SmtValue}
    (hAC : RuleProofs.smt_value_rel a c) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_mult a)
      (__smtx_model_eval_re_mult c) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r, r', rfl, rfl⟩
  · exact RuleProofs.smt_value_rel_refl _
  · exact smt_value_rel_reglan_of_valid_ext
      (native_re_mult_valid_ext_congr (reglan_valid_ext_of_rel hAC))

theorem smt_value_rel_re_comp_congr {a c : SmtValue}
    (hAC : RuleProofs.smt_value_rel a c) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_comp a)
      (__smtx_model_eval_re_comp c) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r, r', rfl, rfl⟩
  · exact RuleProofs.smt_value_rel_refl _
  · exact smt_value_rel_reglan_of_valid_ext
      (native_re_comp_valid_ext_congr (reglan_valid_ext_of_rel hAC))

/-- `str.in_re` respects `smt_value_rel`. -/
theorem smt_value_rel_str_in_re_congr {a b c d : SmtValue}
    (hATy : __smtx_typeof_value a = SmtType.Seq SmtType.Char)
    (hAC : RuleProofs.smt_value_rel a c) (hBD : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_str_in_re a b)
      (__smtx_model_eval_str_in_re c d) := by
  rcases smt_value_rel_cases hAC with rfl | ⟨r1, r1', rfl, rfl⟩
  · rcases smt_value_rel_cases hBD with rfl | ⟨r2, r2', rfl, rfl⟩
    · exact RuleProofs.smt_value_rel_refl _
    · cases a with
      | Seq s1 =>
          have hAll := reglan_ext_of_rel hBD
          have hS1Ty :
              __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
            simpa [__smtx_typeof_value] using hATy
          have hUnpack :=
            native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS1Ty
          have hEq :
              __smtx_model_eval_str_in_re (SmtValue.Seq s1) (SmtValue.RegLan r2) =
                __smtx_model_eval_str_in_re (SmtValue.Seq s1)
                  (SmtValue.RegLan r2') := by
            show SmtValue.Boolean
                (Smtm.native_str_in_re (native_unpack_seq s1) r2) =
              SmtValue.Boolean
                (Smtm.native_str_in_re (native_unpack_seq s1) r2')
            rw [hUnpack, ← RuleProofs.native_str_in_re_eq_model,
              ← RuleProofs.native_str_in_re_eq_model,
              hAll (native_unpack_string s1)]
          rw [hEq]
          exact RuleProofs.smt_value_rel_refl _
      | _ => exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.smt_value_rel_refl _

/-- `str.replace_re` respects `smt_value_rel`. -/
theorem smt_value_rel_str_replace_re_congr {a1 a2 a3 b1 b2 b3 : SmtValue}
    (hA1Ty : __smtx_typeof_value a1 = SmtType.Seq SmtType.Char)
    (hA3Ty : __smtx_typeof_value a3 = SmtType.Seq SmtType.Char)
    (h1 : RuleProofs.smt_value_rel a1 b1)
    (h2 : RuleProofs.smt_value_rel a2 b2)
    (h3 : RuleProofs.smt_value_rel a3 b3) :
    RuleProofs.smt_value_rel (__smtx_model_eval_str_replace_re a1 a2 a3)
      (__smtx_model_eval_str_replace_re b1 b2 b3) := by
  rcases smt_value_rel_cases h1 with rfl | ⟨r1, r1', rfl, rfl⟩
  · cases a1 with
    | Seq s1 =>
        have hS1Ty :
            __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
          simpa [__smtx_typeof_value] using hA1Ty
        have hS1Unpack :=
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS1Ty
        have hS1Valid :=
          native_unpack_string_valid_of_typeof_seq_char hS1Ty
        rcases smt_value_rel_cases h2 with rfl | ⟨r2, r2', rfl, rfl⟩
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · exact RuleProofs.smt_value_rel_refl _
          · cases a2 with
            | RegLan r0 => exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · cases a3 with
            | Seq s3 =>
                have hS3Ty :
                    __smtx_typeof_seq_value s3 = SmtType.Seq SmtType.Char := by
                  simpa [__smtx_typeof_value] using hA3Ty
                have hS3Unpack :=
                  native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS3Ty
                have hEq :
                    __smtx_model_eval_str_replace_re (SmtValue.Seq s1)
                        (SmtValue.RegLan r2) (SmtValue.Seq s3) =
                      __smtx_model_eval_str_replace_re (SmtValue.Seq s1)
                        (SmtValue.RegLan r2') (SmtValue.Seq s3) := by
                  show SmtValue.Seq (native_pack_seq
                      (__smtx_elem_typeof_seq_value s1)
                      (native_str_replace_re (native_unpack_seq s1) r2
                        (native_unpack_seq s3))) =
                    SmtValue.Seq (native_pack_seq
                      (__smtx_elem_typeof_seq_value s1)
                      (native_str_replace_re (native_unpack_seq s1) r2'
                        (native_unpack_seq s3)))
                  rw [hS1Unpack, hS3Unpack,
                    native_str_replace_re_congr (native_unpack_string s1)
                      r2 r2' (native_unpack_string s3) hS1Valid
                      (reglan_valid_ext_of_rel h2)]
                rw [hEq]
                exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
          · exact RuleProofs.smt_value_rel_refl _
    | _ => exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.smt_value_rel_refl _

/-- `str.replace_re_all` respects `smt_value_rel`. -/
theorem smt_value_rel_str_replace_re_all_congr {a1 a2 a3 b1 b2 b3 : SmtValue}
    (hA1Ty : __smtx_typeof_value a1 = SmtType.Seq SmtType.Char)
    (hA3Ty : __smtx_typeof_value a3 = SmtType.Seq SmtType.Char)
    (h1 : RuleProofs.smt_value_rel a1 b1)
    (h2 : RuleProofs.smt_value_rel a2 b2)
    (h3 : RuleProofs.smt_value_rel a3 b3) :
    RuleProofs.smt_value_rel (__smtx_model_eval_str_replace_re_all a1 a2 a3)
      (__smtx_model_eval_str_replace_re_all b1 b2 b3) := by
  rcases smt_value_rel_cases h1 with rfl | ⟨r1, r1', rfl, rfl⟩
  · cases a1 with
    | Seq s1 =>
        have hS1Ty :
            __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
          simpa [__smtx_typeof_value] using hA1Ty
        have hS1Unpack :=
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS1Ty
        have hS1Valid :=
          native_unpack_string_valid_of_typeof_seq_char hS1Ty
        rcases smt_value_rel_cases h2 with rfl | ⟨r2, r2', rfl, rfl⟩
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · exact RuleProofs.smt_value_rel_refl _
          · cases a2 with
            | RegLan r0 => exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · cases a3 with
            | Seq s3 =>
                have hS3Ty :
                    __smtx_typeof_seq_value s3 = SmtType.Seq SmtType.Char := by
                  simpa [__smtx_typeof_value] using hA3Ty
                have hS3Unpack :=
                  native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS3Ty
                have hEq :
                    __smtx_model_eval_str_replace_re_all (SmtValue.Seq s1)
                        (SmtValue.RegLan r2) (SmtValue.Seq s3) =
                      __smtx_model_eval_str_replace_re_all (SmtValue.Seq s1)
                        (SmtValue.RegLan r2') (SmtValue.Seq s3) := by
                  show SmtValue.Seq (native_pack_seq
                      (__smtx_elem_typeof_seq_value s1)
                      (native_str_replace_re_all (native_unpack_seq s1) r2
                        (native_unpack_seq s3))) =
                    SmtValue.Seq (native_pack_seq
                      (__smtx_elem_typeof_seq_value s1)
                      (native_str_replace_re_all (native_unpack_seq s1) r2'
                        (native_unpack_seq s3)))
                  rw [hS1Unpack, hS3Unpack,
                    native_str_replace_re_all_congr
                      (native_unpack_string s1) r2 r2'
                      (native_unpack_string s3) hS1Valid
                      (reglan_valid_ext_of_rel h2)]
                rw [hEq]
                exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
          · exact RuleProofs.smt_value_rel_refl _
    | _ => exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.smt_value_rel_refl _

/-- `str.indexof_re` respects `smt_value_rel`. -/
theorem smt_value_rel_str_indexof_re_congr {a1 a2 a3 b1 b2 b3 : SmtValue}
    (hA1Ty : __smtx_typeof_value a1 = SmtType.Seq SmtType.Char)
    (h1 : RuleProofs.smt_value_rel a1 b1)
    (h2 : RuleProofs.smt_value_rel a2 b2)
    (h3 : RuleProofs.smt_value_rel a3 b3) :
    RuleProofs.smt_value_rel (__smtx_model_eval_str_indexof_re a1 a2 a3)
      (__smtx_model_eval_str_indexof_re b1 b2 b3) := by
  rcases smt_value_rel_cases h1 with rfl | ⟨r1, r1', rfl, rfl⟩
  · cases a1 with
    | Seq s1 =>
        have hS1Ty :
            __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
          simpa [__smtx_typeof_value] using hA1Ty
        have hS1Unpack :=
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS1Ty
        have hS1Valid :=
          native_unpack_string_valid_of_typeof_seq_char hS1Ty
        rcases smt_value_rel_cases h2 with rfl | ⟨r2, r2', rfl, rfl⟩
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · exact RuleProofs.smt_value_rel_refl _
          · cases a2 with
            | RegLan r0 => exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · cases a3 with
            | Numeral i =>
                have hEq :
                    __smtx_model_eval_str_indexof_re (SmtValue.Seq s1)
                        (SmtValue.RegLan r2) (SmtValue.Numeral i) =
                      __smtx_model_eval_str_indexof_re (SmtValue.Seq s1)
                        (SmtValue.RegLan r2') (SmtValue.Numeral i) := by
                  show SmtValue.Numeral
                      (native_str_indexof_re (native_unpack_seq s1) r2 i) =
                    SmtValue.Numeral
                      (native_str_indexof_re (native_unpack_seq s1) r2' i)
                  rw [hS1Unpack,
                    native_str_indexof_re_congr (native_unpack_string s1)
                      r2 r2' i hS1Valid (reglan_valid_ext_of_rel h2)]
                rw [hEq]
                exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
          · exact RuleProofs.smt_value_rel_refl _
    | _ => exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.smt_value_rel_refl _

/-- `str.indexof_re_split` respects `smt_value_rel`. -/
theorem smt_value_rel_str_indexof_re_split_congr {a1 a2 a3 b1 b2 b3 : SmtValue}
    (hA1Ty : __smtx_typeof_value a1 = SmtType.Seq SmtType.Char)
    (h1 : RuleProofs.smt_value_rel a1 b1)
    (h2 : RuleProofs.smt_value_rel a2 b2)
    (h3 : RuleProofs.smt_value_rel a3 b3) :
    RuleProofs.smt_value_rel (__smtx_model_eval_str_indexof_re_split a1 a2 a3)
      (__smtx_model_eval_str_indexof_re_split b1 b2 b3) := by
  rcases smt_value_rel_cases h1 with rfl | ⟨r1, r1', rfl, rfl⟩
  · cases a1 with
    | Seq s1 =>
        have hS1Ty :
            __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
          simpa [__smtx_typeof_value] using hA1Ty
        have hS1Unpack :=
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hS1Ty
        have hS1Valid :=
          native_unpack_string_valid_of_typeof_seq_char hS1Ty
        rcases smt_value_rel_cases h2 with rfl | ⟨r2, r2', rfl, rfl⟩
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · exact RuleProofs.smt_value_rel_refl _
          · cases a2 with
            | RegLan r0 =>
                have hEq :
                    __smtx_model_eval_str_indexof_re_split (SmtValue.Seq s1)
                        (SmtValue.RegLan r0) (SmtValue.RegLan r3) =
                      __smtx_model_eval_str_indexof_re_split (SmtValue.Seq s1)
                        (SmtValue.RegLan r0) (SmtValue.RegLan r3') := by
                  show SmtValue.Numeral
                      (native_str_indexof_re_split (native_unpack_seq s1)
                        r0 r3) =
                    SmtValue.Numeral
                      (native_str_indexof_re_split (native_unpack_seq s1)
                        r0 r3')
                  rw [hS1Unpack, native_str_indexof_re_split_congr
                    (native_unpack_string s1) r0 r0 r3 r3'
                    (valid_ext_refl r0) (reglan_valid_ext_of_rel h3)]
                rw [hEq]
                exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
        · rcases smt_value_rel_cases h3 with rfl | ⟨r3, r3', rfl, rfl⟩
          · cases a3 with
            | RegLan r0 =>
                have hEq :
                    __smtx_model_eval_str_indexof_re_split (SmtValue.Seq s1)
                        (SmtValue.RegLan r2) (SmtValue.RegLan r0) =
                      __smtx_model_eval_str_indexof_re_split (SmtValue.Seq s1)
                        (SmtValue.RegLan r2') (SmtValue.RegLan r0) := by
                  show SmtValue.Numeral
                      (native_str_indexof_re_split (native_unpack_seq s1)
                        r2 r0) =
                    SmtValue.Numeral
                      (native_str_indexof_re_split (native_unpack_seq s1)
                        r2' r0)
                  rw [hS1Unpack, native_str_indexof_re_split_congr
                    (native_unpack_string s1) r2 r2' r0 r0
                    (reglan_valid_ext_of_rel h2) (valid_ext_refl r0)]
                rw [hEq]
                exact RuleProofs.smt_value_rel_refl _
            | _ => exact RuleProofs.smt_value_rel_refl _
          · have hEq :
                __smtx_model_eval_str_indexof_re_split (SmtValue.Seq s1)
                    (SmtValue.RegLan r2) (SmtValue.RegLan r3) =
                  __smtx_model_eval_str_indexof_re_split (SmtValue.Seq s1)
                    (SmtValue.RegLan r2') (SmtValue.RegLan r3') := by
              show SmtValue.Numeral
                  (native_str_indexof_re_split (native_unpack_seq s1)
                    r2 r3) =
                SmtValue.Numeral
                  (native_str_indexof_re_split (native_unpack_seq s1)
                    r2' r3')
              rw [hS1Unpack, native_str_indexof_re_split_congr
                (native_unpack_string s1) r2 r2' r3 r3'
                (reglan_valid_ext_of_rel h2) (reglan_valid_ext_of_rel h3)]
            rw [hEq]
            exact RuleProofs.smt_value_rel_refl _
    | _ => exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.smt_value_rel_refl _


end CongSupport
