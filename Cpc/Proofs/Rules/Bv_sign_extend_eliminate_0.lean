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
set_option maxHeartbeats 10000000

private theorem prog_bv_sign_extend_eliminate_0_eq_of_ne_stuck (x1 : Term) :
    x1 ≠ Term.Stuck ->
    __eo_prog_bv_sign_extend_eliminate_0 x1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)) x1)) x1 := by
  intro hX1
  cases x1 <;> simp [__eo_prog_bv_sign_extend_eliminate_0] at hX1 ⊢

private theorem typeof_arg_of_prog_bv_sign_extend_eliminate_0_bool (x1 : Term) :
    __eo_typeof (__eo_prog_bv_sign_extend_eliminate_0 x1) = Term.Bool ->
    ∃ w, __eo_typeof x1 =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bv_sign_extend_eliminate_0_eq_of_ne_stuck x1 hX1] at hTy
    change __eo_typeof_eq
        (__eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral 0)
          (__eo_typeof x1))
        (__eo_typeof x1) = Term.Bool at hTy
    cases hT : __eo_typeof x1 with
    | Apply f w =>
        cases f with
        | UOp op =>
            cases op <;>
              simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
                __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
                native_teq, native_not, hT] at hTy ⊢
            · cases w <;>
                simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
                  __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
                  native_teq, native_not, hT] at hTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
              __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
              native_teq, native_not, hT] at hTy
    | _ =>
        simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
          __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
          native_teq, native_not, hT] at hTy

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 : Term) (w : native_Int) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    native_zleq 0 w = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat w) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
      (__eo_to_smt x1) rfl hX1Trans hX1Type
  cases hNonneg : native_zleq 0 w <;>
    simp [__eo_to_smt_type, hNonneg] at hSmtType
  · exact False.elim (hX1Trans hSmtType)
  · exact ⟨rfl, hSmtType⟩

private theorem smt_type_sign_extend_zero_eq
    (x1 : Term) (w : native_Int) :
    __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat w) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)) x1)) =
      __smtx_typeof (__eo_to_smt x1) := by
  intro hX1SmtTy
  have hWidthRound :
      native_int_to_nat
          (native_zplus 0 (native_nat_to_int (native_int_to_nat w))) =
        native_int_to_nat w := by
    by_cases hw : 0 ≤ w
    · have hCast : native_nat_to_int (native_int_to_nat w) = w := by
        simpa [native_int_to_nat, native_nat_to_int] using
          Int.toNat_of_nonneg hw
      simp [SmtEval.native_zplus, hCast]
    · have hwlt : w < 0 := Int.lt_of_not_ge hw
      have hWZero : native_int_to_nat w = 0 := by
        simpa [native_int_to_nat] using
          Int.toNat_eq_zero.mpr (Int.le_of_lt hwlt)
      rw [hWZero]
      simp [SmtEval.native_zplus, native_int_to_nat, native_nat_to_int]
  change __smtx_typeof (SmtTerm.sign_extend (SmtTerm.Numeral 0) (__eo_to_smt x1)) =
    __smtx_typeof (__eo_to_smt x1)
  rw [typeof_sign_extend_eq, hX1SmtTy]
  simp [__smtx_typeof_sign_extend, native_ite, SmtEval.native_zleq,
    hWidthRound]

private theorem eo_has_bool_type_sign_extend_zero_eq_self
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sign_extend_eliminate_0 x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)) x1)) x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_sign_extend_eliminate_0_bool x1 hResultTy with
    ⟨w, hX1Type⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨_hWNonneg, hX1SmtTy⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)) x1) x1
    (smt_type_sign_extend_zero_eq x1 w hX1SmtTy)
    (by
      rw [smt_type_sign_extend_zero_eq x1 w hX1SmtTy, hX1SmtTy]
      simp)

private theorem typed___eo_prog_bv_sign_extend_eliminate_0_impl (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sign_extend_eliminate_0 x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_sign_extend_eliminate_0 x1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rw [prog_bv_sign_extend_eliminate_0_eq_of_ne_stuck x1 hX1NotStuck]
  exact eo_has_bool_type_sign_extend_zero_eq_self x1 hX1Trans hResultTy

private theorem native_int_pow2_succ_pred
    {w : native_Int} (hwpos : 0 < w) :
    native_int_pow2 w = 2 * native_int_pow2 (w - 1) := by
  have hw0 : 0 <= w := Int.le_of_lt hwpos
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw0
  have hnotP : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
  have hNat : w.toNat = (w - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_one]
    rw [Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hwp0]
    omega
  rw [native_int_pow2, native_int_pow2, native_zexp_total,
    native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

private theorem native_int_pow2_pos_of_nonneg
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem native_binary_uts_mod_self_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    native_mod_total (native_binary_uts w n) (native_int_pow2 w) = n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let q := native_div_total n p
    let r := native_mod_total n p
    have hpPos : 0 < p := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      exact native_int_pow2_pos_of_nonneg hwp0
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow : native_int_pow2 w = 2 * p := by
      simpa [p] using native_int_pow2_succ_pred (w := w) hwpos
    have hqNonneg : 0 <= q :=
      Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
    have hqLt2 : q < 2 := by
      have hlt : n < 2 * p := by
        simpa [hPow] using hRange.2
      exact Int.ediv_lt_of_lt_mul hpPos hlt
    have hqCases : q = 0 ∨ q = 1 := by
      by_cases hq0 : q = 0
      · exact Or.inl hq0
      · have hqPos : 0 < q := by
          rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
          · exact hlt
          · exact False.elim (hq0 heq.symm)
        have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
        have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
        exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
    have hDivMod : p * q + r = n := by
      simpa [q, r, p, native_div_total, native_mod_total] using
        Int.mul_ediv_add_emod n p
    have hRRange : 0 <= r ∧ r < p := by
      constructor
      · simpa [r, native_mod_total] using
          Int.emod_nonneg n (Int.ne_of_gt hpPos)
      · simpa [r, native_mod_total] using
          Int.emod_lt_of_pos n hpPos
    have hRMod : native_mod_total r p = r := by
      simpa [native_mod_total] using
        Int.emod_eq_of_lt hRRange.1 hRRange.2
    rcases hqCases with hq | hq
    · have hnEq : n = r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hUts : native_binary_uts w n = n := by
        rw [native_binary_uts]
        change native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n) = n
        rw [hnEq]
        change native_zplus (native_zmult 2 (native_mod_total r p))
            (native_zneg r) = r
        rw [hRMod]
        simp [native_zplus, native_zmult, native_zneg]
        rw [Int.two_mul]
        calc
          r + r + -r = r + (r + -r) := by rw [Int.add_assoc]
          _ = r + 0 := by rw [Int.add_right_neg]
          _ = r := by rw [Int.add_zero]
      have hPayloadMod : native_mod_total n (native_int_pow2 w) = n := by
        have hEq : n = native_mod_total n (native_int_pow2 w) := by
          simpa [native_zeq] using hCanon
        exact hEq.symm
      rw [hUts, hPayloadMod]
    · have hnEq : n = p + r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hPAddMod : native_mod_total (p + r) p = r := by
        have hRModInt : r % p = r := by
          simpa [native_mod_total] using hRMod
        have hPModInt : p % p = 0 :=
          Int.emod_eq_zero_of_dvd ⟨1, by simp⟩
        change (p + r) % p = r
        rw [Int.add_emod, hPModInt, hRModInt]
        simpa using hRModInt
      have hUts : native_binary_uts w n = r - p := by
        rw [native_binary_uts]
        change native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n) = r - p
        rw [hnEq]
        change native_zplus (native_zmult 2 (native_mod_total (p + r) p))
            (native_zneg (p + r)) = r - p
        rw [hPAddMod]
        simp [native_zplus, native_zmult, native_zneg]
        rw [Int.two_mul, Int.neg_add]
        change r + r + (-p + -r) = r + -p
        calc
          r + r + (-p + -r) = r + (r + (-p + -r)) := by rw [Int.add_assoc]
          _ = r + (r + (-r + -p)) := by rw [Int.add_comm (-p) (-r)]
          _ = r + ((r + -r) + -p) := by
            exact congrArg (fun t => r + t) (Int.add_assoc r (-r) (-p)).symm
          _ = r + (0 + -p) := by rw [Int.add_right_neg]
          _ = r + -p := by rw [Int.zero_add]
      have hMod :
          native_mod_total (r - p) (2 * p) = p + r := by
        have hTargetRange : 0 <= p + r ∧ p + r < 2 * p := by
          constructor
          · exact Int.add_nonneg (Int.le_of_lt hpPos) hRRange.1
          · have hAddLt : p + r < p + p :=
              Int.add_lt_add_left hRRange.2 p
            simpa [Int.two_mul] using hAddLt
        have hTargetMod : (p + r) % (2 * p) = p + r := by
          exact Int.emod_eq_of_lt hTargetRange.1 hTargetRange.2
        have hCong : (r - p) % (2 * p) = (p + r) % (2 * p) := by
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
          have hSub : (r - p) - (p + r) = -(2 * p) := by
            simp [Int.sub_eq_add_neg, Int.neg_add, Int.two_mul, Int.add_assoc,
              Int.add_comm, Int.add_left_comm]
            rw [Int.add_right_neg, Int.add_zero]
          rw [hSub]
          exact Int.emod_eq_zero_of_dvd ⟨-1, by simp⟩
        change (r - p) % (2 * p) = p + r
        exact hCong.trans hTargetMod
      rw [hUts, hPow, hMod]
      exact hnEq.symm
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    simp [native_binary_uts, native_mod_total, native_int_pow2,
      native_zexp_total, native_zplus, native_zmult, native_zneg]

private theorem eval_sign_extend_zero_self
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sign_extend_eliminate_0 x1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)) x1)) =
      __smtx_model_eval M (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_sign_extend_eliminate_0_bool x1 hResultTy with
    ⟨w, hX1Type⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨_hWNonneg, hX1SmtTy⟩
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hX1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX1⟩
  change __smtx_model_eval M
      (SmtTerm.sign_extend (SmtTerm.Numeral 0) (__eo_to_smt x1)) =
    __smtx_model_eval M (__eo_to_smt x1)
  rw [show __smtx_model_eval M
        (SmtTerm.sign_extend (SmtTerm.Numeral 0) (__eo_to_smt x1)) =
      __smtx_model_eval_sign_extend
        (__smtx_model_eval M (SmtTerm.Numeral 0))
        (__smtx_model_eval M (__eo_to_smt x1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hEvalX1]
  have hWidthNonneg :
      native_zleq 0 (native_nat_to_int (native_int_to_nat w)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  have hPayloadCanon :
      native_zeq payload
          (native_mod_total payload
            (native_int_pow2 (native_nat_to_int (native_int_to_nat w)))) =
        true := by
    have hTy :
        __smtx_typeof_value
            (SmtValue.Binary (native_nat_to_int (native_int_to_nat w)) payload) =
          SmtType.BitVec (native_int_to_nat w) := by
      simpa [hEvalX1] using hEvalTy
    exact bitvec_payload_canonical hTy
  have hUtsMod :
      native_mod_total
          (native_binary_uts (native_nat_to_int (native_int_to_nat w)) payload)
          (native_int_pow2 (native_nat_to_int (native_int_to_nat w))) =
        payload :=
    native_binary_uts_mod_self_of_canonical hWidthNonneg hPayloadCanon
  simp [__smtx_model_eval_sign_extend, SmtEval.native_zplus, hUtsMod]

private theorem facts___eo_prog_bv_sign_extend_eliminate_0_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sign_extend_eliminate_0 x1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_sign_extend_eliminate_0 x1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_sign_extend_eliminate_0 x1) :=
    typed___eo_prog_bv_sign_extend_eliminate_0_impl x1 hX1Trans hResultTy
  rw [prog_bv_sign_extend_eliminate_0_eq_of_ne_stuck x1 hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_sign_extend_eliminate_0_eq_of_ne_stuck x1 hX1NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)) x1)))
      (__smtx_model_eval M (__eo_to_smt x1))
    rw [eval_sign_extend_zero_self M hM x1 hX1Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x1))

public theorem cmd_step_bv_sign_extend_eliminate_0_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_eliminate_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_sign_extend_eliminate_0 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_eliminate_0 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_sign_extend_eliminate_0 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              change __eo_typeof (__eo_prog_bv_sign_extend_eliminate_0 a1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bv_sign_extend_eliminate_0 a1) true
                exact facts___eo_prog_bv_sign_extend_eliminate_0_impl M hM a1
                  hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bv_sign_extend_eliminate_0_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
