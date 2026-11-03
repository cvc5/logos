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

private def bvNotNeqPrem (x : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.gt)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (Term.Numeral 0)))
    (Term.Boolean true)

private def bvNotNeqTerm (x : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq) x)
        (Term.Apply (Term.UOp UserOp.bvnot) x)))
    (Term.Boolean false)

private theorem prog_bv_not_neq_eq_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_prog_bv_not_neq x (Proof.pf (bvNotNeqPrem x)) =
      bvNotNeqTerm x := by
  intro hX
  cases x <;>
    simp [__eo_prog_bv_not_neq, bvNotNeqPrem, bvNotNeqTerm,
      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
      SmtEval.native_not] at hX ⊢

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

private theorem eo_typeof_eq_right_stuck (T : Term) :
    __eo_typeof_eq T Term.Stuck = Term.Stuck := by
  cases T <;> rfl

private theorem bv_not_neq_shape_of_ne_stuck (x P : Term) :
    __eo_prog_bv_not_neq x (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ ∃ px, P = bvNotNeqPrem px := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_not_neq.eq_1 (Proof.pf P))
  refine ⟨hXNe, ?_⟩
  by_cases hShape : ∃ px, P = bvNotNeqPrem px
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_not_neq.eq_3 x (Proof.pf P) hXNe (by
        intro px hP
        cases hP
        exact hShape ⟨px, rfl⟩)))

private theorem typeof_bvnot_ne_stuck_inv :
    (A : Term) ->
    __eo_typeof_bvnot A ≠ Term.Stuck ->
    ∃ m, A = Term.Apply (Term.UOp UserOp.BitVec) m
  | A, hNe => by
      cases A <;> try simp [__eo_typeof_bvnot] at hNe
      case Apply f a =>
        cases f <;> try simp [__eo_typeof_bvnot] at hNe
        case UOp op =>
          cases op <;> try simp [__eo_typeof_bvnot] at hNe
          case BitVec =>
            exact ⟨a, rfl⟩

private theorem typeof_arg_of_bv_not_neq_term_bool (x : Term) :
    __eo_typeof (bvNotNeqTerm x) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof x)
        (__eo_typeof_bvnot (__eo_typeof x)))
      Term.Bool =
    Term.Bool at hTy
  have hInner :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof_bvnot (__eo_typeof x)) =
        Term.Bool :=
    support_eo_typeof_eq_bool_operands_eq _ _ hTy
  have hInnerNe :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof_bvnot (__eo_typeof x)) ≠
        Term.Stuck := by
    intro h
    rw [h] at hInner
    simp [__eo_typeof_eq] at hInner
  have hNotNe : __eo_typeof_bvnot (__eo_typeof x) ≠ Term.Stuck := by
    intro h
    apply hInnerNe
    rw [h]
    exact eo_typeof_eq_right_stuck (__eo_typeof x)
  rcases typeof_bvnot_ne_stuck_inv _ hNotNe with ⟨w, hXTy⟩
  exact ⟨w, hXTy⟩

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x) rfl
      hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem smt_typeof_bvnot
    (a : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvnot a) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro ha
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, ha]

private theorem smt_typeof_boolean (b : Bool) :
    __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem eo_has_bool_type_eq_self_bvnot
    (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvNotNeqTerm x) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq) x)
        (Term.Apply (Term.UOp UserOp.bvnot) x)) := by
  intro hXTrans hResultTy
  rcases typeof_arg_of_bv_not_neq_term_bool x hResultTy with ⟨w, hXType⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨n, _hW, _hNonneg, hXSmtTy⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x
    (Term.Apply (Term.UOp UserOp.bvnot) x)
    (by
      change __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x))
      rw [hXSmtTy, smt_typeof_bvnot _ n hXSmtTy])
    (by
      rw [hXSmtTy]
      intro h
      cases h)

private theorem typed_bv_not_neq_term
    (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvNotNeqTerm x) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvNotNeqTerm x) := by
  intro hXTrans hResultTy
  have hInnerBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.Apply (Term.UOp UserOp.bvnot) x)) :=
    eo_has_bool_type_eq_self_bvnot x hXTrans hResultTy
  unfold bvNotNeqTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq) x)
      (Term.Apply (Term.UOp UserOp.bvnot) x))
    (Term.Boolean false)
    (by
      rw [hInnerBool]
      simpa using (smt_typeof_boolean false).symm)
    (by
      rw [hInnerBool]
      decide)

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem bool_of_true_eval
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t true ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = true := by
  intro hTrue hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue
  cases hTrue with
  | intro_true _ hEvalTrue =>
      rw [hEval] at hEvalTrue
      cases b <;> simp at hEvalTrue ⊢

private theorem eval_bvsize_eq (M : SmtModel) (x : Term) (n : native_Int)
    (hNonneg : native_zleq 0 n = true)
    (hXSmt : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral (native_nat_to_int (native_int_to_nat n)) := by
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) =
    SmtValue.Numeral (native_nat_to_int (native_int_to_nat n))
  have hSize : __eo_to_smt_bv_size (SmtType.BitVec (native_int_to_nat n)) =
      native_nat_to_int (native_int_to_nat n) := rfl
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat n)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  rw [hXSmt, hSize]
  simp [native_ite, hNN]
  simp [__smtx_model_eval, __smtx_model_eval__at_purify]

private theorem bv_not_neq_prem_width_pos
    (M : SmtModel) (x : Term) (n : native_Int) :
    eo_interprets M (bvNotNeqPrem x) true ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    native_zlt 0 n = true := by
  intro hPrem hNonneg hXSmt
  have hnNonneg : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  have hEvalSize := eval_bvsize_eq M x n hNonneg hXSmt
  have hEvalPrem :
      __smtx_model_eval M (__eo_to_smt (bvNotNeqPrem x)) =
        SmtValue.Boolean (native_zlt 0 n) := by
    unfold bvNotNeqPrem
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.gt
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (SmtTerm.Numeral 0))
          (SmtTerm.Boolean true)) =
      SmtValue.Boolean (native_zlt 0 n)
    rw [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq, hEvalSize,
      smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt,
      __smtx_model_eval_eq, native_zlt, SmtEval.native_zlt, native_veq,
      hWidthEq]
  exact bool_of_true_eval hPrem hEvalPrem

private theorem int_not_eq (P a : Int) :
    P + -(a + 1) = P - 1 - a := by
  omega

private theorem native_binary_not_eq_pow_sub_one
    (w n : native_Int) :
    native_binary_not w n = native_int_pow2 w - 1 - n := by
  have h := int_not_eq (native_int_pow2 w) n
  simpa [native_binary_not, native_zplus, native_zneg] using h

private theorem int_sub_lo (P a : Int) (h : a < P) :
    0 <= P - 1 - a := by
  omega

private theorem int_sub_hi (P a : Int) (h : 0 <= a) :
    P - 1 - a < P := by
  omega

private theorem int_complement_fixed_double {P a : Int}
    (h : a = P - 1 - a) :
    2 * a = P - 1 := by
  omega

private theorem int_double_ne_double_sub_one (a k : Int) :
    2 * a ≠ 2 * k - 1 := by
  intro h
  omega

private theorem native_binary_not_mod_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    native_mod_total (native_binary_not w n) (native_int_pow2 w) =
      native_int_pow2 w - 1 - n := by
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  rw [native_binary_not_eq_pow_sub_one]
  let P := native_int_pow2 w
  have hnLo : 0 <= n := hRange.1
  have hnHi : n < P := by
    simpa [P] using hRange.2
  have hLo : 0 <= P - 1 - n := by
    exact int_sub_lo P n hnHi
  have hHi : P - 1 - n < P := by
    exact int_sub_hi P n hnLo
  simpa [P, SmtEval.native_mod_total] using
    Int.emod_eq_of_lt hLo hHi

private theorem native_int_pow2_even_of_pos
    {w : native_Int} (hw : 0 < w) :
    ∃ k : native_Int, native_int_pow2 w = 2 * k := by
  have hwNonneg : 0 <= w := Int.le_of_lt hw
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hwNonneg
  have hwNatNe : Int.toNat w ≠ 0 := by
    intro hZero
    have hwle : w <= 0 := Int.toNat_eq_zero.mp hZero
    exact (Int.not_le_of_gt hw) hwle
  cases hNat : Int.toNat w with
  | zero =>
      exact False.elim (hwNatNe hNat)
  | succ k =>
      refine ⟨(2 : Int) ^ k, ?_⟩
      rw [native_int_pow2, native_zexp_total]
      simp [hnot, hNat]
      exact (Int.pow_succ (2 : Int) k).trans
        (Int.mul_comm ((2 : Int) ^ k) 2)

private theorem payload_ne_complement_of_pos
    {w payload : native_Int} :
    0 < w ->
    payload ≠ native_int_pow2 w - 1 - payload := by
  intro hw hEq
  rcases native_int_pow2_even_of_pos hw with ⟨k, hPow⟩
  let P := native_int_pow2 w
  have hEqP : payload = P - 1 - payload := by
    simpa [P] using hEq
  have hDouble : 2 * payload = P - 1 := by
    exact int_complement_fixed_double hEqP
  have hPowP : P = 2 * k := by
    simpa [P] using hPow
  rw [hPowP] at hDouble
  exact (int_double_ne_double_sub_one payload k) hDouble

private theorem eval_eq_self_bvnot_false
    (M : SmtModel) (hM : model_wf M) (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvNotNeqPrem x) true ->
    __eo_typeof (bvNotNeqTerm x) = Term.Bool ->
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.Apply (Term.UOp UserOp.bvnot) x))) =
      SmtValue.Boolean false := by
  intro hXTrans hPrem hResultTy
  rcases typeof_arg_of_bv_not_neq_term_bool x hResultTy with ⟨w, hXType⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨i, _hW, hNonneg, hXSmtTy⟩
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat i) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hiNonneg : 0 <= i := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hWidthEq : native_nat_to_int (native_int_to_nat i) = i := by
    have hInt : (Int.ofNat (Int.toNat i) : Int) = i :=
      Int.toNat_of_nonneg hiNonneg
    simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  rw [hWidthEq] at hEvalX
  have hEvalTyI :
      __smtx_typeof_value (SmtValue.Binary i payload) =
        SmtType.BitVec (native_int_to_nat i) := by
    simpa [hEvalX] using hEvalTy
  have hPayloadCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 i)) = true := by
    have hCanon := bitvec_payload_canonical hEvalTyI
    simpa using hCanon
  have hWidthPosBool := bv_not_neq_prem_width_pos M x i hPrem hNonneg hXSmtTy
  have hiPos : 0 < i := by
    simpa [SmtEval.native_zlt] using hWidthPosBool
  have hNotMod :
      native_mod_total (native_binary_not i payload) (native_int_pow2 i) =
        native_int_pow2 i - 1 - payload :=
    native_binary_not_mod_of_canonical
      (w := i) (n := payload) (bitvec_width_nonneg hEvalTyI) hPayloadCanon
  have hNoEq : ¬ payload = native_int_pow2 i - 1 - payload :=
    payload_ne_complement_of_pos hiPos
  change __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt x) (SmtTerm.bvnot (__eo_to_smt x))) =
    SmtValue.Boolean false
  rw [smtx_eval_eq_term_eq, smtx_eval_bvnot_term_eq, hEvalX]
  simp [__smtx_model_eval_bvnot, __smtx_model_eval_eq, native_veq,
    hNotMod, hNoEq]

private theorem facts_bv_not_neq_term
    (M : SmtModel) (hM : model_wf M) (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvNotNeqPrem x) true ->
    __eo_typeof (bvNotNeqTerm x) = Term.Bool ->
    eo_interprets M (bvNotNeqTerm x) true := by
  intro hXTrans hPrem hResultTy
  have hTermBool := typed_bv_not_neq_term x hXTrans hResultTy
  unfold bvNotNeqTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvNotNeqTerm] using hTermBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp UserOp.bvnot) x))))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean false)))
    rw [eval_eq_self_bvnot_false M hM x hXTrans hPrem hResultTy]
    change RuleProofs.smt_value_rel (SmtValue.Boolean false)
      (__smtx_model_eval M (SmtTerm.Boolean false))
    rw [smtx_eval_boolean_term_eq]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_not_neq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_not_neq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_not_neq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_not_neq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_not_neq args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
                  let P1 := __eo_state_proven_nth s n1
                  change
                    StepRuleProperties M [P1]
                      (__eo_prog_bv_not_neq a1 (Proof.pf P1))
                  have hProgLocal :
                      __eo_prog_bv_not_neq a1 (Proof.pf P1) ≠ Term.Stuck := by
                    exact hProg
                  rcases bv_not_neq_shape_of_ne_stuck a1 P1 hProgLocal with
                    ⟨hA1Ne, px, hP1⟩
                  have hReqNe : __eo_requires (__eo_eq a1 px) (Term.Boolean true)
                        (bvNotNeqTerm a1) ≠ Term.Stuck := by
                    have h := hProgLocal
                    rw [hP1] at h
                    unfold bvNotNeqPrem at h
                    rw [__eo_prog_bv_not_neq.eq_2 a1 px hA1Ne] at h
                    simpa [bvNotNeqPrem, bvNotNeqTerm] using h
                  have hPx : px = a1 :=
                    eq_of_requires_eq_true_not_stuck a1 px (bvNotNeqTerm a1) hReqNe
                  subst px
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hResultTyCanonical :
                      __eo_typeof (bvNotNeqTerm a1) = Term.Bool := by
                    have hResultTyLocal := hResultTy
                    change __eo_typeof
                        (__eo_prog_bv_not_neq a1
                          (Proof.pf (__eo_state_proven_nth s n1))) =
                      Term.Bool at hResultTyLocal
                    simpa [P1, hP1, prog_bv_not_neq_eq_of_ne_stuck
                      a1 hA1Ne] using hResultTyLocal
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hPrem :
                        eo_interprets M (bvNotNeqPrem a1) true := by
                      simpa [hP1] using hTrue.true_here P1 (by simp)
                    change eo_interprets M
                      (__eo_prog_bv_not_neq a1 (Proof.pf P1)) true
                    rw [hP1, prog_bv_not_neq_eq_of_ne_stuck a1 hA1Ne]
                    exact facts_bv_not_neq_term M hM a1 hA1Trans hPrem
                      hResultTyCanonical
                  · rw [hP1, prog_bv_not_neq_eq_of_ne_stuck a1 hA1Ne]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed_bv_not_neq_term a1 hA1Trans hResultTyCanonical)
