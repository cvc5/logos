module

public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x :=
  RuleProofs.eq_of_eo_eq_true x y h

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x :=
  RuleProofs.eq_of_requires_eq_true_not_stuck x y B

private theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 :=
  RuleProofs.eqs_of_requires_and_eq_true_not_stuck x1 y1 x2 y2 B

private theorem array_index_eq_of_eq
    (I1 E1 I2 E2 : Term)
    (h :
      Term.Apply (Term.Apply Term.Array I1) E1 =
        Term.Apply (Term.Apply Term.Array I2) E2) :
    I1 = I2 := by
  have h' := congrArg
    (fun t =>
      match t with
      | Term.Apply (Term.Apply Term.Array I) _ => I
      | _ => Term.Stuck) h
  simpa using h'

private theorem array_value_eq_of_eq
    (I1 E1 I2 E2 : Term)
    (h :
      Term.Apply (Term.Apply Term.Array I1) E1 =
        Term.Apply (Term.Apply Term.Array I2) E2) :
    E1 = E2 := by
  have h' := congrArg
    (fun t =>
      match t with
      | Term.Apply (Term.Apply Term.Array _) E => E
      | _ => Term.Stuck) h
  simpa using h'

private theorem prog_array_store_swap_eq
    (t1 i1 j1 e1 f1 i2 j2 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck)
    (hI1NotStuck : i1 ≠ Term.Stuck)
    (hJ1NotStuck : j1 ≠ Term.Stuck)
    (hE1NotStuck : e1 ≠ Term.Stuck)
    (hF1NotStuck : f1 ≠ Term.Stuck) :
    __eo_prog_array_store_swap t1 i1 j1 e1 f1
      (Proof.pf
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.eq i2) j2))
          (Term.Boolean false))) =
      __eo_requires (__eo_and (__eo_eq i1 i2) (__eo_eq j1 j2)) (Term.Boolean true)
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.store
                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1) f1))
          (Term.Apply
            (Term.Apply
              (Term.Apply Term.store
                (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1)) i1) e1)) := by
  by_cases hT : t1 = Term.Stuck
  · contradiction
  · by_cases hI : i1 = Term.Stuck
    · contradiction
    · by_cases hJ : j1 = Term.Stuck
      · contradiction
      · by_cases hE : e1 = Term.Stuck
        · contradiction
        · by_cases hF : f1 = Term.Stuck
          · contradiction
          · simp [__eo_prog_array_store_swap]

private theorem typeof_args_of_prog_array_store_swap_bool
    (t1 i1 j1 e1 f1 p1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hI1Trans : RuleProofs.eo_has_smt_translation i1)
    (hJ1Trans : RuleProofs.eo_has_smt_translation j1)
    (hE1Trans : RuleProofs.eo_has_smt_translation e1)
    (hF1Trans : RuleProofs.eo_has_smt_translation f1)
    (h : __eo_typeof (__eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1)) = Term.Bool) :
    __eo_typeof t1 = Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1) ∧
      __eo_typeof j1 = __eo_typeof i1 ∧
      __eo_typeof e1 = __eo_typeof f1 := by
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hF1NotStuck : f1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f1 hF1Trans
  have hProg :
      __eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool h
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases pLhs with
                  | Apply f2 j2 =>
                      cases f2 with
                      | Apply g2 i2 =>
                          cases g2 with
                          | UOp op2 =>
                              cases op2 with
                              | eq =>
                                  cases pRhs with
                                  | Boolean b =>
                                      cases b with
                                      | false =>
                                          rw [prog_array_store_swap_eq
                                                t1 i1 j1 e1 f1 i2 j2
                                                hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck hF1NotStuck]
                                            at hProg h
                                          let lhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply Term.store
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                                j1) f1
                                          let rhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply Term.store
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1))
                                                i1) e1
                                          let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                          have hAlign :
                                              i2 = i1 ∧ j2 = j1 :=
                                            eqs_of_requires_and_eq_true_not_stuck
                                              i1 j1 i2 j2 body hProg
                                          have hi2 : i2 = i1 := hAlign.1
                                          have hj2 : j2 = j1 := hAlign.2
                                          subst i2
                                          subst j2
                                          simp [__eo_requires, __eo_and, __eo_eq,
                                            native_ite, native_teq, native_not,
                                            SmtEval.native_not] at h
                                          have hTypesNotStuck :=
                                            RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                              (__eo_typeof lhs) (__eo_typeof rhs) h
                                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                            hTypesNotStuck.1
                                          have hRhsNotStuck : __eo_typeof rhs ≠ Term.Stuck :=
                                            hTypesNotStuck.2
                                          have hInnerITy :
                                              __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1) =
                                                Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof f1) := by
                                            change __eo_typeof_store
                                                (__eo_typeof
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                                (__eo_typeof j1) (__eo_typeof f1) ≠ Term.Stuck at hLhsNotStuck
                                            exact RuleProofs.eo_typeof_store_not_stuck_implies_array
                                              (__eo_typeof
                                                (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                              (__eo_typeof j1) (__eo_typeof f1) hLhsNotStuck
                                          have hInnerINotStuck :
                                              __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1) ≠
                                                Term.Stuck := by
                                            rw [hInnerITy]
                                            simp
                                          have hInnerJTy :
                                              __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1) =
                                                Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1) := by
                                            change __eo_typeof_store
                                                (__eo_typeof
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1))
                                                (__eo_typeof i1) (__eo_typeof e1) ≠ Term.Stuck at hRhsNotStuck
                                            exact RuleProofs.eo_typeof_store_not_stuck_implies_array
                                              (__eo_typeof
                                                (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1))
                                              (__eo_typeof i1) (__eo_typeof e1) hRhsNotStuck
                                          have hInnerJNotStuck :
                                              __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1) ≠
                                                Term.Stuck := by
                                            rw [hInnerJTy]
                                            simp
                                          have hT1TyIE :
                                              __eo_typeof t1 =
                                                Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1) := by
                                            change __eo_typeof_store (__eo_typeof t1) (__eo_typeof i1)
                                                (__eo_typeof e1) ≠ Term.Stuck at hInnerINotStuck
                                            exact RuleProofs.eo_typeof_store_not_stuck_implies_array
                                              (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof e1)
                                              hInnerINotStuck
                                          have hT1TyJF :
                                              __eo_typeof t1 =
                                                Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof f1) := by
                                            change __eo_typeof_store (__eo_typeof t1) (__eo_typeof j1)
                                                (__eo_typeof f1) ≠ Term.Stuck at hInnerJNotStuck
                                            exact RuleProofs.eo_typeof_store_not_stuck_implies_array
                                              (__eo_typeof t1) (__eo_typeof j1) (__eo_typeof f1)
                                              hInnerJNotStuck
                                          have hArrayEq :
                                              Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1) =
                                                Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof f1) :=
                                            hT1TyIE.symm.trans hT1TyJF
                                          have hIJ : __eo_typeof i1 = __eo_typeof j1 :=
                                            array_index_eq_of_eq
                                              (__eo_typeof i1) (__eo_typeof e1)
                                              (__eo_typeof j1) (__eo_typeof f1) hArrayEq
                                          have hEF : __eo_typeof e1 = __eo_typeof f1 :=
                                            array_value_eq_of_eq
                                              (__eo_typeof i1) (__eo_typeof e1)
                                              (__eo_typeof j1) (__eo_typeof f1) hArrayEq
                                          have hT1Ty :
                                              __eo_typeof t1 =
                                                Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1) := by
                                            simpa [hEF] using hT1TyIE
                                          exact ⟨hT1Ty, hIJ.symm, hEF⟩
                                      | true =>
                                          have : False := by
                                            simp [__eo_prog_array_store_swap
                                              ] at hProg
                                          exact False.elim this
                                  | _ =>
                                      have : False := by
                                        simp [__eo_prog_array_store_swap
                                          ] at hProg
                                      exact False.elim this
                              | _ =>
                                  have : False := by
                                    simp [__eo_prog_array_store_swap
                                      ] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_store_swap
                                  ] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_store_swap
                              ] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_store_swap
                          ] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_store_swap
                      ] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_store_swap
                  ] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_store_swap
              ] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_store_swap
          ] at hProg
      exact False.elim this

private theorem typed___eo_prog_array_store_swap_impl
    (t1 i1 j1 e1 f1 p1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  RuleProofs.eo_has_smt_translation f1 ->
  __eo_typeof (__eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1)) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1)) := by
  intro hT1Trans hI1Trans hJ1Trans hE1Trans hF1Trans hResultTy
  rcases typeof_args_of_prog_array_store_swap_bool
      t1 i1 j1 e1 f1 p1
      hT1Trans hI1Trans hJ1Trans hE1Trans hF1Trans hResultTy with
    ⟨hT1Ty, hJI, hEF⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hF1NotStuck : f1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f1 hF1Trans
  have hSmtT1Raw :
      __smtx_typeof (__eo_to_smt t1) =
        __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1)) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hT1TyNonNone :
      __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1)) ≠
        SmtType.None := by
    rw [← hSmtT1Raw]
    exact hT1Trans
  have hSmtT1 :
      __smtx_typeof (__eo_to_smt t1) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    exact hSmtT1Raw.trans
      (RuleProofs.eo_to_smt_type_array_of_non_none
        (__eo_typeof i1) (__eo_typeof f1) hT1TyNonNone)
  have hSmtI1 :
      __smtx_typeof (__eo_to_smt i1) = __eo_to_smt_type (__eo_typeof i1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation i1 hI1Trans
  have hSmtJ1 :
      __smtx_typeof (__eo_to_smt j1) = __eo_to_smt_type (__eo_typeof i1) := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation j1 hJ1Trans, hJI]
  have hSmtE1 :
      __smtx_typeof (__eo_to_smt e1) = __eo_to_smt_type (__eo_typeof f1) := by
    exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      e1 (__eo_typeof f1) (__eo_to_smt e1) rfl hE1Trans hEF
  have hSmtF1 :
      __smtx_typeof (__eo_to_smt f1) = __eo_to_smt_type (__eo_typeof f1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation f1 hF1Trans
  have hInnerITy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hSmtT1, hSmtI1, hSmtE1]
  have hInnerJTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hSmtT1, hSmtJ1, hSmtF1]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.store
                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1) f1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hInnerITy, hSmtJ1, hSmtF1]
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.store
                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1)) i1) e1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hInnerJTy, hSmtI1, hSmtE1]
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply
            (Term.Apply Term.store
              (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1) f1) := by
    simp [RuleProofs.eo_has_smt_translation, hLhsTy]
  have hProg :
      __eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases pLhs with
                  | Apply f2 j2 =>
                      cases f2 with
                      | Apply g2 i2 =>
                          cases g2 with
                          | UOp op2 =>
                              cases op2 with
                              | eq =>
                                  cases pRhs with
                                  | Boolean b =>
                                      cases b with
                                      | false =>
                                          let lhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply Term.store
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                                j1) f1
                                          let rhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply Term.store
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1))
                                                i1) e1
                                          let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                          have hProgEq :=
                                            prog_array_store_swap_eq
                                              t1 i1 j1 e1 f1 i2 j2
                                              hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck hF1NotStuck
                                          rw [hProgEq] at hProg
                                          have hAlign :
                                              i2 = i1 ∧ j2 = j1 :=
                                            eqs_of_requires_and_eq_true_not_stuck
                                              i1 j1 i2 j2 body hProg
                                          have hi2 : i2 = i1 := hAlign.1
                                          have hj2 : j2 = j1 := hAlign.2
                                          subst i2
                                          subst j2
                                          rw [prog_array_store_swap_eq
                                                t1 i1 j1 e1 f1 i1 j1
                                                hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck hF1NotStuck]
                                          simp [__eo_requires, __eo_and, __eo_eq, native_ite,
                                            native_teq, native_not, SmtEval.native_not]
                                          exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                            lhs rhs
                                            (by rw [hLhsTy, hRhsTy]) hLhsTrans
                                      | true =>
                                          have : False := by
                                            simp [__eo_prog_array_store_swap] at hProg
                                          exact False.elim this
                                  | _ =>
                                      have : False := by
                                        simp [__eo_prog_array_store_swap] at hProg
                                      exact False.elim this
                              | _ =>
                                  have : False := by
                                    simp [__eo_prog_array_store_swap] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_store_swap] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_store_swap] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_store_swap] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_store_swap] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_store_swap] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_store_swap] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_store_swap] at hProg
      exact False.elim this

private theorem facts___eo_prog_array_store_swap_impl
    (M : SmtModel) (hM : model_wf M) (t1 i1 j1 e1 f1 p1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  RuleProofs.eo_has_smt_translation f1 ->
  eo_interprets M p1 true ->
  __eo_typeof (__eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1)) = Term.Bool ->
  eo_interprets M (__eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1)) true := by
  intro hT1Trans hI1Trans hJ1Trans hE1Trans hF1Trans hP1True hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1)) :=
    typed___eo_prog_array_store_swap_impl
      t1 i1 j1 e1 f1 p1
      hT1Trans hI1Trans hJ1Trans hE1Trans hF1Trans hResultTy
  have hT1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt t1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM t1 hT1Trans
  have hI1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt i1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM i1 hI1Trans
  have hJ1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt j1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM j1 hJ1Trans
  have hE1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt e1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM e1 hE1Trans
  have hF1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt f1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM f1 hF1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hF1NotStuck : f1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f1 hF1Trans
  have hProg :
      __eo_prog_array_store_swap t1 i1 j1 e1 f1 (Proof.pf p1) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _
      hProgBool
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases pLhs with
                  | Apply f2 j2 =>
                      cases f2 with
                      | Apply g2 i2 =>
                          cases g2 with
                          | UOp op2 =>
                              cases op2 with
                              | eq =>
                                  cases pRhs with
                                  | Boolean b =>
                                      cases b with
                                      | false =>
                                          have hProgEq :=
                                            prog_array_store_swap_eq
                                              t1 i1 j1 e1 f1 i2 j2
                                              hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck hF1NotStuck
                                          rw [hProgEq] at hProg
                                          let lhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply Term.store
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                                j1) f1
                                          let rhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply Term.store
                                                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1))
                                                i1) e1
                                          let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                          have hAlign :
                                              i2 = i1 ∧ j2 = j1 :=
                                            eqs_of_requires_and_eq_true_not_stuck
                                              i1 j1 i2 j2 body hProg
                                          have hi2 : i2 = i1 := hAlign.1
                                          have hj2 : j2 = j1 := hAlign.2
                                          subst i2
                                          subst j2
                                          have hij :
                                              native_veq
                                                (__smtx_model_eval M (__eo_to_smt i1))
                                                (__smtx_model_eval M (__eo_to_smt j1)) = false := by
                                            exact RuleProofs.native_veq_false_of_model_eval_eq_false
                                              (RuleProofs.model_eval_eq_false_of_eq_false_eq_true M i1 j1 hP1True)
                                          have hBodyBool :
                                              RuleProofs.eo_has_bool_type body := by
                                            rw [hProgEq] at hProgBool
                                            have hsimpa := hProgBool
                                            try simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq, native_not, SmtEval.native_not] at hsimpa ⊢
                                            exact hsimpa
                                          rw [hProgEq]
                                          simp [__eo_requires, __eo_and, __eo_eq,
                                            native_ite, native_teq, native_not, SmtEval.native_not]
                                          exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBodyBool <| by
                                            simpa [lhs, rhs, RuleProofs.eo_to_smt_store_eq, __smtx_model_eval] using
                                              (RuleProofs.smt_value_rel_store_swap_of_native_veq_false
                                                (__smtx_model_eval M (__eo_to_smt t1))
                                                (__smtx_model_eval M (__eo_to_smt i1))
                                                (__smtx_model_eval M (__eo_to_smt j1))
                                                (__smtx_model_eval M (__eo_to_smt e1))
                                                (__smtx_model_eval M (__eo_to_smt f1))
                                                hT1Can hI1Can hJ1Can hE1Can hF1Can
                                                hij)
                                      | true =>
                                          have : False := by
                                            simp [__eo_prog_array_store_swap] at hProg
                                          exact False.elim this
                                  | _ =>
                                      have : False := by
                                        simp [__eo_prog_array_store_swap] at hProg
                                      exact False.elim this
                              | _ =>
                                  have : False := by
                                    simp [__eo_prog_array_store_swap] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_store_swap] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_store_swap] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_store_swap] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_store_swap] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_store_swap] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_store_swap] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_store_swap] at hProg
      exact False.elim this

public theorem cmd_step_array_store_swap_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_store_swap args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.array_store_swap args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_store_swap args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.array_store_swap args premises ≠ Term.Stuck :=
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons a5 args =>
                      cases args with
                      | nil =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons n1 premises =>
                              cases premises with
                              | nil =>
                                  let T1 := a1
                                  let I1 := a2
                                  let J1 := a3
                                  let E1 := a4
                                  let F1 := a5
                                  let P1 := __eo_state_proven_nth s n1
                                  have hTranses :
                                      RuleProofs.eo_has_smt_translation T1 ∧
                                        RuleProofs.eo_has_smt_translation I1 ∧
                                        RuleProofs.eo_has_smt_translation J1 ∧
                                        RuleProofs.eo_has_smt_translation E1 ∧
                                        RuleProofs.eo_has_smt_translation F1 := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                                  change __eo_typeof
                                      (__eo_prog_array_store_swap T1 I1 J1 E1 F1 (Proof.pf P1)) =
                                    Term.Bool at hResultTy
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    change eo_interprets M
                                        (__eo_prog_array_store_swap T1 I1 J1 E1 F1 (Proof.pf P1))
                                        true
                                    exact facts___eo_prog_array_store_swap_impl M hM
                                      T1 I1 J1 E1 F1 P1
                                      hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2.1
                                      hTranses.2.2.2.2
                                      (hTrue P1 (by simp [P1, premiseTermList]))
                                      hResultTy
                                  · change RuleProofs.eo_has_smt_translation
                                      (__eo_prog_array_store_swap T1 I1 J1 E1 F1 (Proof.pf P1))
                                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                      (__eo_prog_array_store_swap T1 I1 J1 E1 F1 (Proof.pf P1))
                                      (typed___eo_prog_array_store_swap_impl
                                        T1 I1 J1 E1 F1 P1
                                        hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2.1
                                        hTranses.2.2.2.2
                                        hResultTy)
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
