module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_bv_comp_eliminate_eq_of_ne_stuck (x1 y1 : Term) :
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_bv_comp_eliminate x1 y1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) := by
  intro hX1 hY1
  cases x1 <;> cases y1 <;> simp [__eo_prog_bv_comp_eliminate] at hX1 hY1 ⊢

private theorem typeof_args_of_prog_bv_comp_eliminate_bool (x1 y1 : Term) :
    __eo_typeof (__eo_prog_bv_comp_eliminate x1 y1) = Term.Bool ->
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
      cases x1 <;> simp [__eo_prog_bv_comp_eliminate] at hX1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_comp_eliminate_eq_of_ne_stuck x1 y1 hX1 hY1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvcomp (__eo_typeof x1) (__eo_typeof y1))
          (__eo_typeof
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
        Term.Bool at hTy
      have hLeftNN :
          __eo_typeof_bvcomp (__eo_typeof x1) (__eo_typeof y1) ≠ Term.Stuck :=
        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
          (__eo_typeof_bvcomp (__eo_typeof x1) (__eo_typeof y1))
          (__eo_typeof
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))))
          hTy).1
      cases hXTy : __eo_typeof x1 with
      | Apply fx wx =>
          cases fx with
          | UOp opx =>
              cases opx
              · exfalso
                exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy])
              · exfalso
                exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy])
              · cases hYTy : __eo_typeof y1 with
                | Apply fy wy =>
                    cases fy with
                    | UOp opy =>
                        cases opy
                        · exfalso
                          exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy, hYTy])
                        · exfalso
                          exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy, hYTy])
                        · have hReqNN :
                              __eo_requires (__eo_eq wx wy) (Term.Boolean true)
                                  (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) ≠
                                Term.Stuck := by
                            simpa [__eo_typeof_bvcomp, hXTy, hYTy] using hLeftNN
                          have hEq : wy = wx :=
                            RuleProofs.eq_of_requires_eq_true_not_stuck wx wy
                              (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
                              hReqNN
                          subst wy
                          exact ⟨wx, by simpa [hXTy], by simpa [hYTy], by
                            intro hW
                            subst wx
                            simp [__eo_typeof_bvcomp, __eo_requires, __eo_eq,
                              native_ite, native_teq, native_not, hXTy, hYTy] at hLeftNN⟩
                        all_goals
                          exfalso
                          exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy, hYTy])
                    | _ =>
                        exfalso
                        exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy, hYTy])
                | _ =>
                    exfalso
                    exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy, hYTy])
              all_goals
                exfalso
                exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy])
          | _ =>
              exfalso
              exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy])
      | _ =>
          exfalso
          exact hLeftNN (by simp [__eo_typeof_bvcomp, hXTy])

private theorem smt_bitvec_type_of_eo_bitvec_type
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec n := by
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
    · exact ⟨native_int_to_nat n, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

private theorem smt_type_eq_of_same_eo_bitvec_type
    (x1 y1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    __eo_typeof y1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    __smtx_typeof (__eo_to_smt y1) = __smtx_typeof (__eo_to_smt x1) := by
  intro hX1Trans hY1Trans hX1Type hY1Type
  have hX1SmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  have hY1SmtType :
      __smtx_typeof (__eo_to_smt y1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt y1) rfl
      hY1Trans hY1Type
  rw [hY1SmtType, hX1SmtType]

private theorem smt_typeof_bv_one_one :
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1))) =
      SmtType.BitVec 1 := by
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 1)) =
    SmtType.BitVec 1
  have hNN :
      __smtx_typeof (SmtTerm.Binary 1 (native_mod_total 1 (native_int_pow2 1))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq (native_mod_total 1 (native_int_pow2 1))
            (native_mod_total (native_mod_total 1 (native_int_pow2 1))
              (native_int_pow2 1)) =
          true :=
      native_mod_total_canonical 1 1
    have hNonneg : native_zleq 0 1 = true := by
      native_decide
    simp [SmtEval.native_and, native_ite, hMod, hNonneg]
  exact TranslationProofs.smtx_typeof_binary_of_non_none 1 (native_mod_total 1 (native_int_pow2 1)) hNN

private theorem smt_typeof_bv_zero_one :
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) =
      SmtType.BitVec 1 := by
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)) =
    SmtType.BitVec 1
  have hNN :
      __smtx_typeof (SmtTerm.Binary 1 (native_mod_total 0 (native_int_pow2 1))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq (native_mod_total 0 (native_int_pow2 1))
            (native_mod_total (native_mod_total 0 (native_int_pow2 1))
              (native_int_pow2 1)) =
          true :=
      native_mod_total_canonical 1 0
    have hNonneg : native_zleq 0 1 = true := by
      native_decide
    simp [SmtEval.native_and, native_ite, hMod, hNonneg]
  exact TranslationProofs.smtx_typeof_binary_of_non_none 1 (native_mod_total 0 (native_int_pow2 1)) hNN

private theorem smt_typeof_bvcomp_same
    (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_comp_eliminate x1 y1) = Term.Bool ->
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)) =
      SmtType.BitVec 1 := by
  intro hX1Trans hY1Trans hResultTy
  rcases typeof_args_of_prog_bv_comp_eliminate_bool x1 y1 hResultTy with
    ⟨w, hX1Type, hY1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type x1 w hX1Trans hX1Type with
    ⟨n, hX1SmtTy⟩
  have hSameTy :=
    smt_type_eq_of_same_eo_bitvec_type x1 y1 w hX1Trans hY1Trans hX1Type hY1Type
  change __smtx_typeof (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt y1)) =
    SmtType.BitVec 1
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hSameTy, hX1SmtTy]
  simp [__smtx_typeof_bv_op_2_ret, native_nateq, native_ite]

private theorem smt_typeof_comp_eliminate_rhs
    (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_comp_eliminate x1 y1) = Term.Bool ->
    __smtx_typeof
      (__eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
      SmtType.BitVec 1 := by
  intro hX1Trans hY1Trans hResultTy
  rcases typeof_args_of_prog_bv_comp_eliminate_bool x1 y1 hResultTy with
    ⟨w, hX1Type, hY1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type x1 w hX1Trans hX1Type with
    ⟨n, hX1SmtTy⟩
  have hSameTy :=
    smt_type_eq_of_same_eo_bitvec_type x1 y1 w hX1Trans hY1Trans hX1Type hY1Type
  have hEqType :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt y1)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    rw [hSameTy, hX1SmtTy]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_Teq, native_ite]
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt y1))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
    SmtType.BitVec 1
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hEqType, smt_typeof_bv_one_one,
    smt_typeof_bv_zero_one, native_Teq, native_ite]

private theorem typed___eo_prog_bv_comp_eliminate_impl (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_comp_eliminate x1 y1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_comp_eliminate x1 y1) := by
  intro hX1Trans hY1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  rw [prog_bv_comp_eliminate_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))
    (by
      rw [smt_typeof_bvcomp_same x1 y1 hX1Trans hY1Trans hResultTy,
        smt_typeof_comp_eliminate_rhs x1 y1 hX1Trans hY1Trans hResultTy])
    (by
      rw [smt_typeof_bvcomp_same x1 y1 hX1Trans hY1Trans hResultTy]
      simp)

private theorem eval_bv_const
    (M : SmtModel) (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtValue.Binary n (native_mod_total k (native_int_pow2 n)) := by
  intro hNonneg
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtValue.Binary n (native_mod_total k (native_int_pow2 n))
  simp [native_ite, hNonneg]

private theorem eval_bv_one_one (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1))) =
      SmtValue.Binary 1 1 := by
  have hNonneg : native_zleq 0 1 = true := by
    native_decide
  have hEval := eval_bv_const M 1 1 hNonneg
  have hMod : native_mod_total 1 (native_int_pow2 1) = 1 := by
    native_decide
  simpa [hMod] using hEval

private theorem eval_bv_zero_one (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) =
      SmtValue.Binary 1 0 := by
  have hNonneg : native_zleq 0 1 = true := by
    native_decide
  have hEval := eval_bv_const M 0 1 hNonneg
  have hMod : native_mod_total 0 (native_int_pow2 1) = 0 := by
    native_decide
  simpa [hMod] using hEval

private theorem eval_bvcomp_eliminate
    (M : SmtModel) (x1 y1 : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) := by
  change __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt y1)) =
    __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt y1))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))))
  rw [show __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt y1)) =
      __smtx_model_eval_bvcomp
        (__smtx_model_eval M (__eo_to_smt x1))
        (__smtx_model_eval M (__eo_to_smt y1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [show __smtx_model_eval M
        (SmtTerm.ite (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt y1))
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
      __smtx_model_eval_ite
        (__smtx_model_eval M (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt y1)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [show __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt y1)) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt x1))
        (__smtx_model_eval M (__eo_to_smt y1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [eval_bv_one_one M, eval_bv_zero_one M]
  simp [__smtx_model_eval_bvcomp]

private theorem facts___eo_prog_bv_comp_eliminate_impl
    (M : SmtModel) (hM : model_wf M) (x1 y1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    RuleProofs.eo_has_smt_translation y1 ->
    __eo_typeof (__eo_prog_bv_comp_eliminate x1 y1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_comp_eliminate x1 y1) true := by
  intro hX1Trans hY1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_comp_eliminate x1 y1) :=
    typed___eo_prog_bv_comp_eliminate_impl x1 y1 hX1Trans hY1Trans hResultTy
  rw [prog_bv_comp_eliminate_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_comp_eliminate_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck] using
      hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x1) y1)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) y1))
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))))
    rw [eval_bvcomp_eliminate M x1 y1]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_comp_eliminate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_comp_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_comp_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_comp_eliminate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_comp_eliminate args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_bv_comp_eliminate a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_comp_eliminate a1 a2) true
                    exact facts___eo_prog_bv_comp_eliminate_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_comp_eliminate_impl a1 a2 hA1Trans
                        hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
