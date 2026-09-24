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

private theorem prog_bv_udiv_one_eq_of_ne_stuck (x1 n1 : Term) :
    x1 ≠ Term.Stuck ->
    n1 ≠ Term.Stuck ->
    __eo_prog_bv_udiv_one x1 n1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x1)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 1)))) x1 := by
  intro hX1 hN1
  cases x1 <;> cases n1 <;> simp [__eo_prog_bv_udiv_one] at hX1 hN1 ⊢

private theorem typeof_args_of_prog_bv_udiv_one_bool (x1 n1 : Term) :
    __eo_typeof (__eo_prog_bv_udiv_one x1 n1) = Term.Bool ->
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
      cases x1 <;> simp [__eo_prog_bv_udiv_one] at hX1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_udiv_one_eq_of_ne_stuck x1 n1 hX1 hN1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvand (__eo_typeof x1)
            (__eo_typeof_int_to_bv (__eo_typeof n1) n1 (Term.UOp UserOp.Int)))
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
              · cases hNTy : __eo_typeof n1 with
                | UOp nop =>
                    cases nop
                    · have hEq : n1 = w :=
                        bv_width_eq_of_typeof_bvand_at_bv_right_bool w n1 hN1 hNTy
                          (by simpa [hXTy] using hTy)
                      have hW : w ≠ Term.Stuck := by
                        intro hW
                        exact hN1 (by rw [hEq, hW])
                      exact ⟨w, by simpa [hXTy], hEq, hW⟩
                    all_goals
                      exfalso
                      simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                        hXTy, hNTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                      hXTy, hNTy] using hTy
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

private theorem smt_typeof_bv_const
    (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtType.BitVec (native_int_to_nat n)
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary n (native_mod_total k (native_int_pow2 n))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total k (native_int_pow2 n))
            (native_mod_total
              (native_mod_total k (native_int_pow2 n))
              (native_int_pow2 n)) =
          true :=
      native_mod_total_canonical n k
    simp [SmtEval.native_and, hNonneg, hMod, native_ite]
  simpa [native_ite, hNonneg] using
    TranslationProofs.smtx_typeof_binary_of_non_none n
      (native_mod_total k (native_int_pow2 n)) hNN

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

private theorem native_int_pow2_one_lt_of_pos
    {w : native_Int} (hw : 0 < w) :
    1 < native_int_pow2 w := by
  have hwNonneg : 0 <= w := Int.le_of_lt hw
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hwNonneg
  have hwNatNe : Int.toNat w ≠ 0 := by
    intro hZero
    have hwle : w <= 0 := Int.toNat_eq_zero.mp hZero
    exact (Int.not_le_of_gt hw) hwle
  have hNat : 1 < (2 : Nat) ^ Int.toNat w :=
    Nat.one_lt_pow hwNatNe (by decide : 1 < (2 : Nat))
  rw [native_int_pow2, native_zexp_total]
  simp [hnot]
  exact_mod_cast hNat

private theorem smt_typeof_bvudiv_one_eq_self
    (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_udiv_one x1 n1) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 1)))) =
      __smtx_typeof (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_udiv_one_bool x1 n1 hResultTy with
    ⟨w, hX1Type, hN1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, hNonneg, hX1SmtTy⟩
  subst w
  subst n1
  have hOneTy := smt_typeof_bv_const 1 n hNonneg
  change __smtx_typeof
      (SmtTerm.bvudiv (__eo_to_smt x1)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 1)))) =
    __smtx_typeof (__eo_to_smt x1)
  have hLhsTy :
      __smtx_typeof
          (SmtTerm.bvudiv (__eo_to_smt x1)
            (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 1)))) =
        SmtType.BitVec (native_int_to_nat n) := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2, hX1SmtTy, hOneTy, native_nateq, native_ite]
  rw [hLhsTy, hX1SmtTy]

private theorem typed___eo_prog_bv_udiv_one_impl (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_udiv_one x1 n1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_udiv_one x1 n1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_bv_udiv_one_bool x1 n1 hResultTy with
    ⟨w, _hX1Type, hN1, hW⟩
  subst n1
  rw [prog_bv_udiv_one_eq_of_ne_stuck x1 w hX1NotStuck hW]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x1)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 1)))
    x1
    (smt_typeof_bvudiv_one_eq_self x1 w hX1Trans (by simpa using hResultTy))
    (by
      rw [smt_typeof_bvudiv_one_eq_self x1 w hX1Trans (by simpa using hResultTy)]
      exact hX1Trans)

private theorem eval_bvudiv_one_eq_self
    (M : SmtModel) (hM : model_wf M) (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_udiv_one x1 n1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 1)))) =
      __smtx_model_eval M (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_udiv_one_bool x1 n1 hResultTy with
    ⟨w, hX1Type, hN1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨n, hW, hNonneg, hX1SmtTy⟩
  subst w
  subst n1
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hX1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX1⟩
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hnNonneg : 0 <= n := by
      simpa [SmtEval.native_zleq] using hNonneg
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  rw [hWidthEq] at hEvalX1
  have hEvalTyN :
      __smtx_typeof_value (SmtValue.Binary n payload) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hEvalX1] using hEvalTy
  have hPayloadCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 n)) = true := by
    have hCanon := bitvec_payload_canonical hEvalTyN
    simpa [hWidthEq] using hCanon
  have hOneEval := eval_bv_const M 1 n hNonneg
  change __smtx_model_eval M
      (SmtTerm.bvudiv (__eo_to_smt x1)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 1)))) =
    __smtx_model_eval M (__eo_to_smt x1)
  rw [show __smtx_model_eval M
        (SmtTerm.bvudiv (__eo_to_smt x1)
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 1)))) =
      __smtx_model_eval_bvudiv
        (__smtx_model_eval M (__eo_to_smt x1))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 1)))) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hEvalX1, hOneEval]
  by_cases hnZero : n = 0
  · subst n
    have hWidth0 := bitvec_width_nonneg hEvalTyN
    have hRange0 := bitvec_payload_range_of_canonical hWidth0 hPayloadCanon
    have hPayloadZero : payload = 0 := by
      have hlt : payload < 1 := by
        simpa [native_int_pow2, native_zexp_total, Smtm.native_nat_to_int,
          SmtEval.native_int_to_nat] using hRange0.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange0.1
    rw [hPayloadZero]
    simp [__smtx_model_eval_bvudiv, native_binary_max, SmtEval.native_mod_total,
      SmtEval.native_zeq, native_ite, native_zplus, native_zneg,
      native_int_pow2, native_zexp_total, SmtEval.native_div_total]
  · have hnPos : 0 < n := by
      have hnNonneg : 0 <= n := by
        simpa [SmtEval.native_zleq] using hNonneg
      rcases Int.lt_or_eq_of_le hnNonneg with hlt | heq
      · exact hlt
      · exact False.elim (hnZero heq.symm)
    have hOneMod :
        native_mod_total 1 (native_int_pow2 n) = 1 := by
      have hPowGt := native_int_pow2_one_lt_of_pos hnPos
      simpa [SmtEval.native_mod_total] using
        Int.emod_eq_of_lt (by decide : (0 : Int) <= 1) hPowGt
    have hPayloadMod :
        native_mod_total payload (native_int_pow2 n) = payload := by
      have hPayloadEq :
          payload = native_mod_total payload (native_int_pow2 n) := by
        simpa [SmtEval.native_zeq] using hPayloadCanon
      exact hPayloadEq.symm
    have hOneModInt : (1 : Int) % native_int_pow2 n = 1 := by
      simpa [SmtEval.native_mod_total] using hOneMod
    have hPayloadModInt : payload % native_int_pow2 n = payload := by
      simpa [SmtEval.native_mod_total] using hPayloadMod
    simp [__smtx_model_eval_bvudiv, hOneMod, hOneModInt, hPayloadMod,
      hPayloadModInt, SmtEval.native_div_total, SmtEval.native_mod_total,
      SmtEval.native_zeq, native_ite]

private theorem facts___eo_prog_bv_udiv_one_impl
    (M : SmtModel) (hM : model_wf M) (x1 n1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_udiv_one x1 n1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_udiv_one x1 n1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_bv_udiv_one_bool x1 n1 hResultTy with
    ⟨w, _hX1Type, hN1, hW⟩
  subst n1
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_udiv_one x1 w) :=
    typed___eo_prog_bv_udiv_one_impl x1 w hX1Trans (by simpa using hResultTy)
  rw [prog_bv_udiv_one_eq_of_ne_stuck x1 w hX1NotStuck hW]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_udiv_one_eq_of_ne_stuck x1 w hX1NotStuck hW] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 1)))))
      (__smtx_model_eval M (__eo_to_smt x1))
    rw [eval_bvudiv_one_eq_self M hM x1 w hX1Trans (by simpa using hResultTy)]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x1))

public theorem cmd_step_bv_udiv_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_udiv_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_udiv_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_udiv_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_udiv_one args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_bv_udiv_one a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_udiv_one a1 a2) true
                    exact facts___eo_prog_bv_udiv_one_impl M hM a1 a2
                      hA1Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_udiv_one_impl a1 a2 hA1Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
