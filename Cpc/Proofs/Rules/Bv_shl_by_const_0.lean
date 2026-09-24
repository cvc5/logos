module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_bv_shl_by_const_0_eq_of_ne_stuck (x1 sz1 : Term) :
    x1 ≠ Term.Stuck ->
    sz1 ≠ Term.Stuck ->
    __eo_prog_bv_shl_by_const_0 x1 sz1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x1)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv sz1) (Term.Numeral 0)))) x1 := by
  intro hX1 hSz1
  cases x1 <;> cases sz1 <;> simp [__eo_prog_bv_shl_by_const_0] at hX1 hSz1 ⊢

private theorem typeof_args_of_prog_bv_shl_by_const_0_bool (x1 sz1 : Term) :
    __eo_typeof (__eo_prog_bv_shl_by_const_0 x1 sz1) = Term.Bool ->
    ∃ w, __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      sz1 = w ∧ w ≠ Term.Stuck := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hSz1 : sz1 = Term.Stuck
    · subst sz1
      cases x1 <;> simp [__eo_prog_bv_shl_by_const_0] at hX1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_shl_by_const_0_eq_of_ne_stuck x1 sz1 hX1 hSz1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvand
            (__eo_typeof x1)
            (__eo_typeof_int_to_bv (__eo_typeof sz1) sz1 (Term.UOp UserOp.Int)))
          (__eo_typeof x1) =
        Term.Bool at hTy
      cases hXTy : __eo_typeof x1 with
      | Apply f w =>
          cases f with
          | UOp op =>
              cases op
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · cases hSzTy : __eo_typeof sz1 with
                | UOp nop =>
                    cases nop
                    · have hEq : sz1 = w :=
                        bv_width_eq_of_typeof_bvand_at_bv_right_bool w sz1 hSz1 hSzTy
                          (by simpa [hXTy] using hTy)
                      have hWNotStuck : w ≠ Term.Stuck := by
                        intro hW
                        exact hSz1 (hEq.trans hW)
                      exact ⟨w, by simpa [hXTy], hEq, hWNotStuck⟩
                    all_goals
                      exfalso
                      simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                        hXTy, hSzTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                      hXTy, hSzTy] using hTy
              all_goals
                exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
          | _ =>
              simp [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hXTy] at hTy
      | _ =>
          simp [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
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

private theorem smt_typeof_bv_zero
    (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)) =
    SmtType.BitVec (native_int_to_nat n)
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary n (native_mod_total 0 (native_int_pow2 n))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total 0 (native_int_pow2 n))
            (native_mod_total
              (native_mod_total 0 (native_int_pow2 n))
              (native_int_pow2 n)) =
          true :=
      native_mod_total_canonical n 0
    simp [SmtEval.native_and, hNonneg, hMod, native_ite]
  simpa [native_ite, hNonneg] using
    TranslationProofs.smtx_typeof_binary_of_non_none n
      (native_mod_total 0 (native_int_pow2 n)) hNN

private theorem smt_typeof_bvshl_const_zero_eq_self
    (x1 sz1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_shl_by_const_0 x1 sz1) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv sz1) (Term.Numeral 0)))) =
      __smtx_typeof (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_shl_by_const_0_bool x1 sz1 hResultTy with
    ⟨w, hX1Type, hSz1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, hNonneg, hX1SmtTy⟩
  subst w
  subst sz1
  have hZeroTy := smt_typeof_bv_zero n hNonneg
  change __smtx_typeof
      (SmtTerm.bvshl (__eo_to_smt x1)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))) =
    __smtx_typeof (__eo_to_smt x1)
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hX1SmtTy, hZeroTy, native_nateq, native_ite]

private theorem typed___eo_prog_bv_shl_by_const_0_impl (x1 sz1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_shl_by_const_0 x1 sz1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_shl_by_const_0 x1 sz1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_bv_shl_by_const_0_bool x1 sz1 hResultTy with
    ⟨w, hX1Type, hSz1, hW⟩
  subst sz1
  rw [prog_bv_shl_by_const_0_eq_of_ne_stuck x1 w hX1NotStuck hW]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x1)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)))
    x1
    (smt_typeof_bvshl_const_zero_eq_self x1 w hX1Trans (by simpa using hResultTy))
    (by
      rw [smt_typeof_bvshl_const_zero_eq_self x1 w hX1Trans (by simpa using hResultTy)]
      rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
        ⟨n, hWidth, _hNonneg, hX1SmtTy⟩
      subst w
      rw [hX1SmtTy]
      simp)

private theorem eval_bvshl_const_zero_self
    (M : SmtModel) (hM : model_wf M) (x1 sz1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_shl_by_const_0 x1 sz1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv sz1) (Term.Numeral 0)))) =
      __smtx_model_eval M (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_shl_by_const_0_bool x1 sz1 hResultTy with
    ⟨w, hX1Type, hSz1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, hNonneg, hX1SmtTy⟩
  subst w
  subst sz1
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hX1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX1⟩
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) =
        SmtValue.Binary n (native_mod_total 0 (native_int_pow2 n)) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)) =
      SmtValue.Binary n (native_mod_total 0 (native_int_pow2 n))
    simp [native_ite, hNonneg]
  have hPayloadCanon :
      native_zeq payload
          (native_mod_total payload
            (native_int_pow2 (native_nat_to_int (native_int_to_nat n)))) =
        true :=
    bitvec_payload_canonical (by simpa [hEvalX1] using hEvalTy)
  have hPayloadMod :
      native_mod_total payload
          (native_int_pow2 (native_nat_to_int (native_int_to_nat n))) =
        payload := by
    have hPayloadEq :
        payload =
          native_mod_total payload
            (native_int_pow2 (native_nat_to_int (native_int_to_nat n))) := by
      simpa [SmtEval.native_zeq] using hPayloadCanon
    exact hPayloadEq.symm
  change __smtx_model_eval M
      (SmtTerm.bvshl (__eo_to_smt x1)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))) =
    __smtx_model_eval M (__eo_to_smt x1)
  rw [show __smtx_model_eval M
        (SmtTerm.bvshl (__eo_to_smt x1)
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))) =
      __smtx_model_eval_bvshl
        (__smtx_model_eval M (__eo_to_smt x1))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hEvalX1, hZeroEval]
  have hPowZero : native_int_pow2 0 = 1 := by
    simp [native_int_pow2, native_zexp_total]
  have hPayloadModInt :
      payload % native_int_pow2 (native_nat_to_int (native_int_to_nat n)) = payload := by
    simpa [SmtEval.native_mod_total] using hPayloadMod
  simp [__smtx_model_eval_bvshl, SmtEval.native_zmult,
    SmtEval.native_mod_total, hPowZero, hPayloadMod, hPayloadModInt]

private theorem facts___eo_prog_bv_shl_by_const_0_impl
    (M : SmtModel) (hM : model_wf M) (x1 sz1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_shl_by_const_0 x1 sz1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_shl_by_const_0 x1 sz1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_bv_shl_by_const_0_bool x1 sz1 hResultTy with
    ⟨w, _hX1Type, hSz1, hW⟩
  subst sz1
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_shl_by_const_0 x1 w) :=
    typed___eo_prog_bv_shl_by_const_0_impl x1 w hX1Trans (by simpa using hResultTy)
  rw [prog_bv_shl_by_const_0_eq_of_ne_stuck x1 w hX1NotStuck hW]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_shl_by_const_0_eq_of_ne_stuck x1 w hX1NotStuck hW] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)))))
      (__smtx_model_eval M (__eo_to_smt x1))
    rw [eval_bvshl_const_zero_self M hM x1 w hX1Trans (by simpa using hResultTy)]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt x1))

public theorem cmd_step_bv_shl_by_const_0_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_shl_by_const_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_shl_by_const_0 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_shl_by_const_0 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_shl_by_const_0 args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_bv_shl_by_const_0 a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_shl_by_const_0 a1 a2) true
                    exact facts___eo_prog_bv_shl_by_const_0_impl M hM a1 a2
                      hA1Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_shl_by_const_0_impl a1 a2 hA1Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
