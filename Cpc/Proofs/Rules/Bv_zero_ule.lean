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

private theorem prog_bv_zero_ule_eq_of_ne_stuck (x1 n1 : Term) :
    x1 ≠ Term.Stuck ->
    n1 ≠ Term.Stuck ->
    __eo_prog_bv_zero_ule x1 n1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) x1))
        (Term.Boolean true) := by
  intro hX1 hN1
  cases x1 <;> cases n1 <;> simp [__eo_prog_bv_zero_ule] at hX1 hN1 ⊢

private theorem typeof_args_of_prog_bv_zero_ule_bool (x1 n1 : Term) :
    __eo_typeof (__eo_prog_bv_zero_ule x1 n1) = Term.Bool ->
    ∃ w, __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      n1 = w ∧ w ≠ Term.Stuck := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hN1 : n1 = Term.Stuck
    · subst n1
      cases x1 <;> simp [__eo_prog_bv_zero_ule] at hX1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_zero_ule_eq_of_ne_stuck x1 n1 hX1 hN1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvult
            (__eo_typeof_int_to_bv (__eo_typeof n1) n1 (Term.UOp UserOp.Int))
            (__eo_typeof x1))
          Term.Bool = Term.Bool at hTy
      cases hXTy : __eo_typeof x1 with
      | Apply f w =>
          cases f with
          | UOp op =>
              cases op
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · cases hNTy : __eo_typeof n1 with
                | UOp nop =>
                    cases nop
                    · have hEq : w = n1 :=
                        bv_width_eq_of_typeof_bvult_at_bv_left_bool n1 w hN1 hNTy
                          (by simpa [hXTy] using hTy)
                      subst w
                      exact ⟨n1, by simpa [hXTy], rfl, hN1⟩
                    all_goals
                      exfalso
                      simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                        hXTy, hNTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                      hXTy, hNTy] using hTy
              all_goals
                exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
          | _ =>
              simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hXTy] at hTy
      | _ =>
          simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
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

private theorem eo_has_bool_type_bvule_zero
    (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_ule x1 n1) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) x1) := by
  intro hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_zero_ule_bool x1 n1 hResultTy with
    ⟨w, hX1Type, hN1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, hNonneg, hSmtTy⟩
  subst w
  subst n1
  have hZeroTy := smt_typeof_bv_zero n hNonneg
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof
      (SmtTerm.bvule
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
        (__eo_to_smt x1)) =
    SmtType.Bool
  rw [__smtx_typeof.eq_57]
  simp [__smtx_typeof_bv_op_2_ret, hSmtTy, hZeroTy, native_nateq, native_ite]

private theorem typed___eo_prog_bv_zero_ule_impl (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_ule x1 n1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_zero_ule x1 n1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_bv_zero_ule_bool x1 n1 hResultTy with
    ⟨w, _hX1Type, hN1, hW⟩
  subst n1
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) x1) :=
    eo_has_bool_type_bvule_zero x1 w hX1Trans (by simpa using hResultTy)
  rw [prog_bv_zero_ule_eq_of_ne_stuck x1 w hX1NotStuck hW]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) x1)
    (Term.Boolean true)
    (hInnerBool.trans RuleProofs.eo_has_bool_type_true.symm)
    (by
      rw [hInnerBool]
      decide)

private theorem eval_bvule_zero_true
    (M : SmtModel) (hM : model_wf M) (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_ule x1 n1) = Term.Bool ->
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) x1)) =
      SmtValue.Boolean true := by
  intro hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_zero_ule_bool x1 n1 hResultTy with
    ⟨w, hX1Type, hN1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, hNonneg, hSmtTy⟩
  subst w
  subst n1
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX1⟩
  have hWidth : native_zleq 0 (native_nat_to_int (native_int_to_nat n)) = true :=
    bitvec_width_nonneg (by simpa [hEvalX1] using hEvalTy)
  have hPayloadCanon :
      native_zeq payload
        (native_mod_total payload (native_int_pow2 (native_nat_to_int (native_int_to_nat n)))) =
        true :=
    bitvec_payload_canonical (by simpa [hEvalX1] using hEvalTy)
  have hPayloadNonneg :
      0 <= payload :=
    (bitvec_payload_range_of_canonical hWidth hPayloadCanon).1
  have hnNonneg : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) =
        SmtValue.Binary n (native_mod_total 0 (native_int_pow2 n)) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)) =
      SmtValue.Binary n (native_mod_total 0 (native_int_pow2 n))
    simp [native_ite, hNonneg]
  change __smtx_model_eval M
      (SmtTerm.bvule
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
        (__eo_to_smt x1)) =
    SmtValue.Boolean true
  rw [__smtx_model_eval.eq_57, hZeroEval, hEvalX1]
  by_cases hPayloadZero : payload = 0
  · subst payload
    simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
      __smtx_model_eval_bvugt, __smtx_model_eval_eq, __smtx_model_eval_or,
      native_zlt, SmtEval.native_zlt, native_veq, native_or,
      SmtEval.native_mod_total, hWidthEq]
  · have hPayloadPos : 0 < payload :=
      by
        rcases Int.lt_or_gt_of_ne hPayloadZero with hNeg | hPos
        · exact False.elim ((Int.not_lt_of_ge hPayloadNonneg) hNeg)
        · exact hPos
    simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
      __smtx_model_eval_bvugt, __smtx_model_eval_eq, __smtx_model_eval_or,
      native_zlt, SmtEval.native_zlt, native_veq, native_or,
      SmtEval.native_mod_total, hPayloadPos]

private theorem facts___eo_prog_bv_zero_ule_impl
    (M : SmtModel) (hM : model_wf M) (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_ule x1 n1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_zero_ule x1 n1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_bv_zero_ule_bool x1 n1 hResultTy with
    ⟨w, _hX1Type, hN1, hW⟩
  subst n1
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_zero_ule x1 w) :=
    typed___eo_prog_bv_zero_ule_impl x1 w hX1Trans (by simpa using hResultTy)
  rw [prog_bv_zero_ule_eq_of_ne_stuck x1 w hX1NotStuck hW]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_zero_ule_eq_of_ne_stuck x1 w hX1NotStuck hW] using hProgBool
  · have hTrueEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
          SmtValue.Boolean true := by
      change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
      rw [__smtx_model_eval.eq_1]
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) x1)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true)))
    rw [eval_bvule_zero_true M hM x1 w hX1Trans (by simpa using hResultTy), hTrueEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

public theorem cmd_step_bv_zero_ule_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_ule args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_zero_ule args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_ule args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_zero_ule args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_bv_zero_ule a1 a2) = Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_zero_ule a1 a2) true
                    exact facts___eo_prog_bv_zero_ule_impl M hM a1 a2 hA1Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_zero_ule_impl a1 a2 hA1Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
