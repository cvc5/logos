module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_bv_commutative_comp_eq_of_ne_stuck (x1 y1 : Term) :
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_bv_commutative_comp x1 y1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1))
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y1) x1) := by
  intro hX1 hY1
  cases x1 <;> cases y1 <;> simp [__eo_prog_bv_commutative_comp] at hX1 hY1 ⊢

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  -- v4.33 `simp` unfolds `__eo_eq` under `decide` and desyncs the
  -- `Decidable` instance, so derive the guard by contradiction instead.
  have hEq : __eo_eq x y = Term.Boolean true := by
    apply Classical.byContradiction
    intro hne
    apply hProg
    simp [__eo_requires, native_ite, native_teq, hne]
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at hEq
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at hEq
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using hEq
      simpa [native_teq] using hDec

private theorem requires_eq_true_stuck_of_ne (x y B : Term) :
    x ≠ y ->
    __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck := by
  intro hNe
  by_cases hReq :
      __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck
  · exact hReq
  · have hEq : y = x := eq_of_requires_eq_true_not_stuck x y B hReq
    exact False.elim (hNe hEq.symm)

private theorem typeof_args_of_prog_bv_commutative_comp_bool (x1 y1 : Term) :
    __eo_typeof (__eo_prog_bv_commutative_comp x1 y1) = Term.Bool ->
    ∃ w, __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hY1 : y1 = Term.Stuck
    · subst y1
      cases x1 <;> simp [__eo_prog_bv_commutative_comp] at hX1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_commutative_comp_eq_of_ne_stuck x1 y1 hX1 hY1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvcomp (__eo_typeof x1) (__eo_typeof y1))
          (__eo_typeof_bvcomp (__eo_typeof y1) (__eo_typeof x1)) =
        Term.Bool at hTy
      cases hXTy : __eo_typeof x1 with
      | Apply fx wx =>
          cases fx with
          | UOp opx =>
              cases opx
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · cases hYTy : __eo_typeof y1 with
                | Apply fy wy =>
                    cases fy with
                    | UOp opy =>
                        cases opy
                        · exfalso
                          simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, hXTy, hYTy] using hTy
                        · exfalso
                          simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, hXTy, hYTy] using hTy
                        · by_cases hEq : wx = wy
                          · subst wy
                            exact ⟨wx, by simpa [hXTy], by simpa [hYTy], by
                              intro hW
                              subst wx
                              simp [__eo_typeof_eq, __eo_typeof_bvcomp,
                                __eo_requires, __eo_eq, native_ite,
                                native_teq, native_not, hXTy, hYTy] at hTy⟩
                          · exfalso
                            have hLeftStuck :
                                __eo_typeof_bvcomp
                                    (Term.Apply (Term.UOp UserOp.BitVec) wx)
                                    (Term.Apply (Term.UOp UserOp.BitVec) wy) =
                                  Term.Stuck := by
                              simpa [__eo_typeof_bvcomp] using
                                requires_eq_true_stuck_of_ne
                                  wx wy
                                  (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
                                  hEq
                            have hOuterBool :
                                __eo_typeof_eq
                                    (__eo_typeof_bvcomp
                                      (Term.Apply (Term.UOp UserOp.BitVec) wx)
                                      (Term.Apply (Term.UOp UserOp.BitVec) wy))
                                    (__eo_typeof_bvcomp
                                      (Term.Apply (Term.UOp UserOp.BitVec) wy)
                                      (Term.Apply (Term.UOp UserOp.BitVec) wx)) =
                                  Term.Bool := by
                              simpa [__eo_typeof_bvcomp, hXTy, hYTy] using hTy
                            rw [hLeftStuck] at hOuterBool
                            simp [__eo_typeof_eq] at hOuterBool
                        all_goals
                          exfalso
                          simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, hXTy, hYTy] using hTy
                    | _ =>
                        exfalso
                        simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                          __eo_requires, __eo_eq, native_ite, native_teq,
                          native_not, hXTy, hYTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                      __eo_requires, __eo_eq, native_ite, native_teq,
                      native_not, hXTy, hYTy] using hTy
              all_goals
                exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvcomp,
                  __eo_requires, __eo_eq, native_ite, native_teq,
                  native_not, hXTy] using hTy
          | _ =>
              simp [__eo_typeof_eq, __eo_typeof_bvcomp,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hXTy] at hTy
      | _ =>
          simp [__eo_typeof_eq, __eo_typeof_bvcomp,
            __eo_requires, __eo_eq, native_ite, native_teq, native_not,
            hXTy] at hTy

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat n) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hX1Trans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

private theorem eo_has_bvcomp_type_same
    (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_commutative_comp x1 y1) = Term.Bool ->
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)) =
      SmtType.BitVec 1 := by
  intro hX1Trans hY1Trans hResultTy
  rcases typeof_args_of_prog_bv_commutative_comp_bool x1 y1 hResultTy with
    ⟨w, hX1Type, hY1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, _hNonneg, hX1SmtTy⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y1 (Term.Numeral n) hY1Trans
      (by simpa using hY1Type) with
    ⟨m, hM, _hMNonneg, hY1SmtTy⟩
  cases hM
  change __smtx_typeof (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt y1)) =
    SmtType.BitVec 1
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hX1SmtTy, hY1SmtTy, native_nateq, native_ite]

private theorem eo_has_bvcomp_type_swap
    (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_commutative_comp x1 y1) = Term.Bool ->
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y1) x1)) =
      SmtType.BitVec 1 := by
  intro hX1Trans hY1Trans hResultTy
  rcases typeof_args_of_prog_bv_commutative_comp_bool x1 y1 hResultTy with
    ⟨w, hX1Type, hY1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, _hNonneg, hX1SmtTy⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y1 (Term.Numeral n) hY1Trans
      (by simpa using hY1Type) with
    ⟨m, hM, _hMNonneg, hY1SmtTy⟩
  cases hM
  change __smtx_typeof (SmtTerm.bvcomp (__eo_to_smt y1) (__eo_to_smt x1)) =
    SmtType.BitVec 1
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hX1SmtTy, hY1SmtTy, native_nateq, native_ite]

private theorem typed___eo_prog_bv_commutative_comp_impl (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_commutative_comp x1 y1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_commutative_comp x1 y1) := by
  intro hX1Trans hY1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hCompSame :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)) =
        SmtType.BitVec 1 :=
    eo_has_bvcomp_type_same x1 y1 hX1Trans hY1Trans hResultTy
  have hCompSwap :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y1) x1)) =
        SmtType.BitVec 1 :=
    eo_has_bvcomp_type_swap x1 y1 hX1Trans hY1Trans hResultTy
  rw [prog_bv_commutative_comp_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y1) x1)
    (by rw [hCompSame, hCompSwap])
    (by rw [hCompSame]; simp)

private theorem native_veq_false_symm_local {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    native_veq v2 v1 = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

private theorem smtx_model_eval_eq_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

private theorem smtx_model_eval_eq_false_symm_local
    {v1 v2 : SmtValue} :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false ->
    __smtx_model_eval_eq v2 v1 = SmtValue.Boolean false := by
  intro hEq
  by_cases hReg :
      ∃ r1 r2, v1 = SmtValue.RegLan r1 ∧ v2 = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    change SmtValue.Boolean (native_re_ext_eq r2 r1) = SmtValue.Boolean false
    change SmtValue.Boolean (native_re_ext_eq r1 r2) = SmtValue.Boolean false at hEq
    simp at hEq ⊢
    rcases hEq with ⟨s, hs, hNe⟩
    exact ⟨s, hs, fun h => hNe h.symm⟩
  · cases v1 <;> cases v2 <;>
      simp [__smtx_model_eval_eq] at hEq hReg ⊢
    all_goals
      exact native_veq_false_symm_local hEq

private theorem smtx_model_eval_bvcomp_comm (v1 v2 : SmtValue) :
    __smtx_model_eval_bvcomp v1 v2 = __smtx_model_eval_bvcomp v2 v1 := by
  unfold __smtx_model_eval_bvcomp
  rcases smtx_model_eval_eq_boolean v1 v2 with ⟨b, hEq⟩
  cases b with
  | false =>
      have hEqSymm := smtx_model_eval_eq_false_symm_local hEq
      rw [hEq, hEqSymm]
  | true =>
      have hEqSymm :
          __smtx_model_eval_eq v2 v1 = SmtValue.Boolean true :=
        RuleProofs.smt_value_rel_symm v1 v2 hEq
      rw [hEq, hEqSymm]

private theorem eval_bvcomp_comm
    (M : SmtModel) (hM : model_wf M) (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_commutative_comp x1 y1) = Term.Bool ->
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)) =
      __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y1) x1)) := by
  intro _hX1Trans _hY1Trans _hResultTy
  change __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt y1)) =
    __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt y1) (__eo_to_smt x1))
  rw [show __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt y1)) =
      __smtx_model_eval_bvcomp
        (__smtx_model_eval M (__eo_to_smt x1))
        (__smtx_model_eval M (__eo_to_smt y1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [show __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt y1) (__eo_to_smt x1)) =
      __smtx_model_eval_bvcomp
        (__smtx_model_eval M (__eo_to_smt y1))
        (__smtx_model_eval M (__eo_to_smt x1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  exact smtx_model_eval_bvcomp_comm
    (__smtx_model_eval M (__eo_to_smt x1))
    (__smtx_model_eval M (__eo_to_smt y1))

private theorem facts___eo_prog_bv_commutative_comp_impl
    (M : SmtModel) (hM : model_wf M) (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_commutative_comp x1 y1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_commutative_comp x1 y1) true := by
  intro hX1Trans hY1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_commutative_comp x1 y1) :=
    typed___eo_prog_bv_commutative_comp_impl x1 y1 hX1Trans hY1Trans hResultTy
  rw [prog_bv_commutative_comp_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_commutative_comp_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck] using
      hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y1) x1)))
    rw [eval_bvcomp_comm M hM x1 y1 hX1Trans hY1Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_commutative_comp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_commutative_comp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_commutative_comp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_commutative_comp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_commutative_comp args premises ≠ Term.Stuck :=
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
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_bv_commutative_comp a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_commutative_comp a1 a2) true
                    exact facts___eo_prog_bv_commutative_comp_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_commutative_comp_impl a1 a2 hA1Trans
                        hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
