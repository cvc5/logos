module

public import Cpc.Proofs.RuleSupport.BvSaddoElimSupport
import all Cpc.Proofs.RuleSupport.BvSaddoElimSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

public section

/-! Support for the `bv_ssubo_eliminate` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def bvSsuboDiff (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x) y

def bvSsuboRhs (x y nm : Term) : Term :=
  bvSaddoOr
    (bvSaddoBranch (bvSdivSign nm x)
      (bvSaddoBitEq nm y bvSaddoZeroBit)
      (bvSaddoBitEq nm (bvSsuboDiff x y) bvSaddoZeroBit))
    (bvSaddoOr
      (bvSaddoBranch (bvSaddoBitEq nm x bvSaddoZeroBit)
        (bvSdivSign nm y) (bvSdivSign nm (bvSsuboDiff x y)))
      (Term.Boolean false))

def bvSsuboLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) x) y

def bvSsuboTerm (x y nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSsuboLhs x y))
    (bvSsuboRhs x y nm)

private theorem typeof_or_bool_args_ssubo (A B : Term) :
    __eo_typeof_or A B = Term.Bool -> A = Term.Bool ∧ B = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_or_bool_args A B h

private theorem typeof_bvSaddoAnd_inv_ssubo {a b : Term} :
    __eo_typeof (bvSaddoAnd a b) = Term.Bool ->
    __eo_typeof a = Term.Bool ∧ __eo_typeof b = Term.Bool := by
  intro h
  exact typeof_or_bool_args_ssubo _ _ (by have hsimpa := h; (try simp [bvSaddoAnd] at hsimpa ⊢); exact hsimpa)

private theorem typeof_bvSaddoOr_inv_ssubo {a b : Term} :
    __eo_typeof (bvSaddoOr a b) = Term.Bool ->
    __eo_typeof a = Term.Bool ∧ __eo_typeof b = Term.Bool := by
  intro h
  exact typeof_or_bool_args_ssubo _ _ (by have hsimpa := h; (try simp [bvSaddoOr] at hsimpa ⊢); exact hsimpa)

private theorem bv_ssubo_rhs_x_sign_bool {x y nm : Term} :
    __eo_typeof (bvSsuboRhs x y nm) = Term.Bool ->
    __eo_typeof (bvSdivSign nm x) = Term.Bool := by
  intro h
  have hOuter := typeof_bvSaddoOr_inv_ssubo h
  have hBranch := typeof_bvSaddoAnd_inv_ssubo hOuter.1
  have hSigns := typeof_bvSaddoAnd_inv_ssubo hBranch.1
  exact hSigns.1

private theorem bv_ssubo_context (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSsuboTerm x y nm) = Term.Bool ->
    ∃ w n : native_Int,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      nm = Term.Numeral n ∧
      native_zleq 0 w = true ∧ native_zleq 0 n = true ∧
      native_zlt n w = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hYTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof x) (__eo_typeof y))
      (__eo_typeof (bvSsuboRhs x y nm)) = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases typeof_bvult_args_of_ne_stuck hOps.1 with
    ⟨widthTerm, hXTy, hYTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x widthTerm
      hXTrans hXTy with ⟨w, hWidth, hw0, hXSmtTy⟩
  subst widthTerm
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) := by
    have hsimpa :=
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        y (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
        (__eo_to_smt y) rfl hYTrans hYTy)
    try simp [__eo_to_smt_type, hw0] at hsimpa ⊢
    exact hsimpa
  have hLhsTy :
      __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  rw [hLhsTy] at hTypeEq
  have hRhsTy : __eo_typeof (bvSsuboRhs x y nm) = Term.Bool := hTypeEq.symm
  have hSignTy := bv_ssubo_rhs_x_sign_bool hRhsTy
  have hExtractNe : __eo_typeof (bvSdivExtract nm x) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hSignTy; (try simp [bvSdivSign] at hsimpa ⊢); exact hsimpa)).1
  rcases bv_extract_context_of_non_stuck x nm nm hXTrans
      (by have hsimpa := hExtractNe; (try simp [bvSdivExtract] at hsimpa ⊢); exact hsimpa) with
    ⟨w', nHi, nLo, hXTy', hNmHi, hNmLo, hw'0, hn0, hnW,
      _hOne0, hXSmtTy'⟩
  have hWNat : native_int_to_nat w' = native_int_to_nat w := by
    rw [hXSmtTy] at hXSmtTy'
    exact (SmtType.BitVec.inj hXSmtTy').symm
  have hW' : w' = w :=
    nonneg_int_eq_of_toNat_eq w' w hw'0 hw0 hWNat
  subst w'
  have hN : nLo = nHi := by
    rw [hNmHi] at hNmLo
    injection hNmLo with h
    exact h.symm
  subst nLo
  exact ⟨w, nHi, hXTy, hYTy, hNmHi, hw0, hn0, hnW,
    hXSmtTy, hYSmtTy⟩

private theorem eo_has_bool_type_or_ssubo (a b : Term) :
    RuleProofs.eo_has_bool_type a -> RuleProofs.eo_has_bool_type b ->
    RuleProofs.eo_has_bool_type (bvSaddoOr a b) := by
  intro ha hb
  unfold RuleProofs.eo_has_bool_type at ha hb ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [ha, hb, native_ite]

private theorem typed_bv_ssubo_term (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSsuboTerm x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSsuboTerm x y nm) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_ssubo_context x y nm hXTrans hYTrans hResultTy with
    ⟨w, n, _hXTy, _hYTy, rfl, hw0, hn0, hnW, hXSmtTy, hYSmtTy⟩
  let W := native_int_to_nat w
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  have hDiffTy :
      __smtx_typeof (__eo_to_smt (bvSsuboDiff x y)) = SmtType.BitVec W := by
    change __smtx_typeof
      (SmtTerm.bvsub (__eo_to_smt x) (__eo_to_smt y)) = _
    exact smt_typeof_bvbin_same SmtTerm.bvsub
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hXSmtTyW hYSmtTyW
  have hOneIndex : native_zplus (native_zplus n 1) (native_zneg n) = 1 := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg]
    rw [Int.add_comm n 1]
    exact Int.add_neg_cancel_right 1 n
  have hOneWidth :
      native_zlt 0 (native_zplus (native_zplus n 1) (native_zneg n)) =
        true := by rw [hOneIndex]; decide
  have extractTy (z : Term)
      (hz : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
      __smtx_typeof (__eo_to_smt (bvSdivExtract (Term.Numeral n) z)) =
        SmtType.BitVec 1 := by
    have h := smt_typeof_extract_of_context z w n n
      (by simpa [W] using hz) hw0 hn0 hnW hOneWidth
    have hsimpa := h
    try simp [bvSdivExtract, hOneIndex, native_int_to_nat, SmtEval.native_int_to_nat] at hsimpa ⊢
    exact hsimpa
  have hExtractXTy := extractTy x hXSmtTyW
  have hExtractYTy := extractTy y hYSmtTyW
  have hExtractDiffTy := extractTy (bvSsuboDiff x y) hDiffTy
  have hOneTy :
      __smtx_typeof (__eo_to_smt bvSdivBitOne) = SmtType.BitVec 1 := by
    simpa [bvSdivBitOne, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 1 1 (by decide)
  have hZeroTy :
      __smtx_typeof (__eo_to_smt bvSaddoZeroBit) = SmtType.BitVec 1 := by
    simpa [bvSaddoZeroBit, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 0 1 (by decide)
  have eqBitTy (z bit : Term)
      (hz : __smtx_typeof (__eo_to_smt
        (bvSdivExtract (Term.Numeral n) z)) = SmtType.BitVec 1)
      (hb : __smtx_typeof (__eo_to_smt bit) = SmtType.BitVec 1) :
      RuleProofs.eo_has_bool_type
        (bvSaddoBitEq (Term.Numeral n) z bit) := by
    unfold bvSaddoBitEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hz.trans hb.symm) (by rw [hz]; intro h; cases h)
  have hXOne := eqBitTy x bvSdivBitOne hExtractXTy hOneTy
  have hYOne := eqBitTy y bvSdivBitOne hExtractYTy hOneTy
  have hDiffOne := eqBitTy (bvSsuboDiff x y) bvSdivBitOne
    hExtractDiffTy hOneTy
  have hXZero := eqBitTy x bvSaddoZeroBit hExtractXTy hZeroTy
  have hYZero := eqBitTy y bvSaddoZeroBit hExtractYTy hZeroTy
  have hDiffZero := eqBitTy (bvSsuboDiff x y) bvSaddoZeroBit
    hExtractDiffTy hZeroTy
  have hTrue := RuleProofs.eo_has_bool_type_true
  have branchTy (a b c : Term)
      (ha : RuleProofs.eo_has_bool_type a)
      (hb : RuleProofs.eo_has_bool_type b)
      (hc : RuleProofs.eo_has_bool_type c) :
      RuleProofs.eo_has_bool_type (bvSaddoBranch a b c) := by
    unfold bvSaddoBranch bvSaddoAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ ha
        (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hb hTrue))
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hc hTrue)
  have hFirst := branchTy _ _ _
    (by simpa [bvSaddoBitEq, bvSdivSign] using hXOne)
    hYZero hDiffZero
  have hSecond := branchTy _ _ _ hXZero
    (by simpa [bvSaddoBitEq, bvSdivSign] using hYOne)
    (by simpa [bvSaddoBitEq, bvSdivSign] using hDiffOne)
  have hRhsBool : RuleProofs.eo_has_bool_type
      (bvSsuboRhs x y (Term.Numeral n)) := by
    unfold bvSsuboRhs
    exact eo_has_bool_type_or_ssubo _ _ hFirst
      (eo_has_bool_type_or_ssubo _ _ hSecond (by rfl))
  have hLhsBool : RuleProofs.eo_has_bool_type (bvSsuboLhs x y) := by
    change __smtx_typeof
      (SmtTerm.bvssubo (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2_ret, hXSmtTyW, hYSmtTyW,
      native_nateq, native_ite]
  unfold bvSsuboTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm) (by rw [hLhsBool]; intro h; cases h)

-- Semantic support follows below.

def bvSsuboFormula (sx sy sd : Bool) : Bool :=
  (sx && !sy && !sd) || (!sx && sy && sd)

theorem eval_bvneg_canonical_ssubo (W B : Nat) :
    __smtx_model_eval_bvneg
        (SmtValue.Binary (native_nat_to_int W) (B : Int)) =
      SmtValue.Binary (native_nat_to_int W)
        (((-(BitVec.ofInt W (B : Int))).toNat : Nat) : Int) := by
  let b := BitVec.ofInt W (B : Int)
  have hPow : native_int_pow2 (native_nat_to_int W) = (2 ^ W : Int) :=
    native_int_pow2_nat W
  have hNegNat :
      (-b).toNat = ((-(B : Int)) % (2 ^ W : Int)).toNat := by
    rw [← BitVec.ofInt_neg]
    exact BitVec.toNat_ofInt (-(B : Int))
  have hModNonneg : 0 ≤ (-(B : Int)) % (2 ^ W : Int) := by
    have hp : (0 : Int) < (2 ^ W : Nat) := by
      exact_mod_cast Nat.two_pow_pos W
    exact Int.emod_nonneg _ (Int.ne_of_gt hp)
  have hMod :
      native_mod_total (-(B : Int))
          (native_int_pow2 (native_nat_to_int W)) =
        ((-b).toNat : Int) := by
    rw [hPow]
    change (-(B : Int)) % (2 ^ W : Int) = ((-b).toNat : Int)
    rw [← Int.toNat_of_nonneg hModNonneg, ← hNegNat]
  change SmtValue.Binary (native_nat_to_int W)
      (native_mod_total (-(B : Int))
        (native_int_pow2 (native_nat_to_int W))) = _
  rw [hMod]

theorem bvsub_value_eq_bitvec_sub
    (W A B : Nat) (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval_bvsub
        (SmtValue.Binary (native_nat_to_int W) (A : Int))
        (SmtValue.Binary (native_nat_to_int W) (B : Int)) =
      SmtValue.Binary (native_nat_to_int W)
        (((BitVec.ofInt W (A : Int) -
          BitVec.ofInt W (B : Int)).toNat : Nat) : Int) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  let nb := (-b).toNat
  have haNat : a.toNat = A := by
    simpa [a] using ofInt_toNat_canonical W (A : Int)
      (Int.natCast_nonneg A) (by exact_mod_cast hA)
  have hAddNat : (a + -b).toNat = (A + nb) % 2 ^ W := by
    rw [BitVec.toNat_add, haNat]
  have hMod :
      native_mod_total ((A : Int) + (nb : Int))
          (native_int_pow2 (native_nat_to_int W)) =
        (((A + nb) % 2 ^ W : Nat) : Int) := by
    rw [native_int_pow2_nat]
    have hCast : (A : Int) + (nb : Int) = ((A + nb : Nat) : Int) := by
      norm_cast
    rw [hCast]
    unfold native_mod_total
    exact (Int.natCast_emod (A + nb) (2 ^ W)).symm
  unfold __smtx_model_eval_bvsub
  rw [eval_bvneg_canonical_ssubo W B]
  change SmtValue.Binary (native_nat_to_int W)
      (native_mod_total ((A : Int) + (nb : Int))
        (native_int_pow2 (native_nat_to_int W))) = _
  rw [hMod]
  congr 2
  rw [BitVec.sub_eq_add_neg, hAddNat]

theorem bvsge_zero_value_eq_not_msb
    (W A : Nat) (hW : 0 < W) (hA : A < 2 ^ W) :
    __smtx_model_eval_bvsge
        (SmtValue.Binary (native_nat_to_int W) (A : Int))
        (SmtValue.Binary (native_nat_to_int W) 0) =
      SmtValue.Boolean (!(BitVec.ofInt W (A : Int)).msb) := by
  have hPred :
      native_zplus (native_nat_to_int W) (native_zneg 1) =
        native_nat_to_int (W - 1) := by
    have hOneLe : 1 ≤ W := hW
    change (W : Int) + -(1 : Int) = ((W - 1 : Nat) : Int)
    rw [Int.ofNat_sub hOneLe]
    rfl
  have hIndex :
      __smtx_model_eval__
          (SmtValue.Numeral (native_nat_to_int W)) (SmtValue.Numeral 1) =
        SmtValue.Numeral (native_nat_to_int (W - 1)) := by
    simp [__smtx_model_eval__, hPred]
  have hExtractA := extract_bit_binary_eval
    (native_nat_to_int W) (A : Int) (W - 1) (Int.natCast_nonneg A)
  have hExtractZero := extract_bit_binary_eval
    (native_nat_to_int W) 0 (W - 1) (by omega)
  unfold __smtx_model_eval_bvsge __smtx_model_eval_bvsgt
  simp only [__smtx_bv_sizeof_value, hIndex]
  rw [hExtractA, hExtractZero]
  rw [bitvec_msb_of_canonical W A hA]
  simp [__smtx_model_eval_bvugt, __smtx_model_eval_eq,
    __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, native_veq, native_not, native_and,
    native_or, native_zlt, bv1]
  by_cases hA0 : A = 0
  · subst A
    simp
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA0
    simp [hA0, hApos]

theorem bvnego_value_eq_negOverflow
    (W B : Nat) (hW : 0 < W) (hB : B < 2 ^ W) :
    __smtx_model_eval_bvnego
        (SmtValue.Binary (native_nat_to_int W) (B : Int)) =
      SmtValue.Boolean (BitVec.negOverflow (BitVec.ofInt W (B : Int))) := by
  let b := BitVec.ofInt W (B : Int)
  have hPred :
      native_zplus (native_nat_to_int W) (native_zneg 1) =
        native_nat_to_int (W - 1) := by
    have hOneLe : 1 ≤ W := hW
    change (W : Int) + -(1 : Int) = ((W - 1 : Nat) : Int)
    rw [Int.ofNat_sub hOneLe]
    rfl
  have hbNat : b.toNat = B := by
    simpa [b] using ofInt_toNat_canonical W (B : Int)
      (Int.natCast_nonneg B) (by exact_mod_cast hB)
  have hEq : b = BitVec.intMin W ↔ B = 2 ^ (W - 1) := by
    constructor
    · intro h
      rw [← hbNat, h, BitVec.toNat_intMin_of_pos hW]
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [hbNat, BitVec.toNat_intMin_of_pos hW, h]
  change SmtValue.Boolean
      (native_zeq (B : Int)
        (native_int_pow2
          (native_zplus (native_nat_to_int W) (native_zneg 1)))) =
    SmtValue.Boolean (BitVec.negOverflow b)
  rw [hPred, native_int_pow2_nat]
  rw [BitVec.negOverflow_eq]
  simp only [hW, decide_true, Bool.true_and, native_zeq]
  congr 2
  exact propext ((Int.ofNat_inj).trans hEq.symm)

theorem bvsaddo_neg_value_eq_ssubOverflow
    (W A B : Nat) (hW : 0 < W)
    (hA : A < 2 ^ W) (hB : B < 2 ^ W)
    (hNo : BitVec.negOverflow (BitVec.ofInt W (B : Int)) = false) :
    __smtx_model_eval_bvsaddo
        (SmtValue.Binary (native_nat_to_int W) (A : Int))
        (SmtValue.Binary (native_nat_to_int W)
          (((-(BitVec.ofInt W (B : Int))).toNat : Nat) : Int)) =
      SmtValue.Boolean
        (BitVec.ssubOverflow (BitVec.ofInt W (A : Int))
          (BitVec.ofInt W (B : Int))) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  let nb := (-b).toNat
  have hNb : nb < 2 ^ W := (-b).isLt
  have hNbVec : BitVec.ofInt W (nb : Int) = -b := by
    change BitVec.ofNat W nb = -b
    simpa [nb] using BitVec.ofNat_toNat W (-b)
  have hNo' : ¬ BitVec.negOverflow b := by
    intro ht
    have hf : BitVec.negOverflow b = false := hNo
    rw [hf] at ht
    contradiction
  have hOverflow : BitVec.saddOverflow a (-b) = BitVec.ssubOverflow a b := by
    simp only [BitVec.saddOverflow, BitVec.ssubOverflow,
      BitVec.toInt_neg_of_not_negOverflow hNo']
    rw [Int.sub_eq_add_neg]
  rw [show (-(BitVec.ofInt W (B : Int))).toNat = nb by rfl]
  rw [bvsaddo_value_eq_saddOverflow W A nb hW hA hNb]
  simpa [a, b, hNbVec] using hOverflow

theorem ssubOverflow_of_negOverflow
    (W A B : Nat) (hW : 0 < W)
    (hNeg : BitVec.negOverflow (BitVec.ofInt W (B : Int)) = true) :
    Bool.not (BitVec.ofInt W (A : Int)).msb =
      BitVec.ssubOverflow (BitVec.ofInt W (A : Int))
        (BitVec.ofInt W (B : Int)) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  have hbMin : b = BitVec.intMin W := by
    have h := hNeg
    change BitVec.negOverflow b = true at h
    rw [BitVec.negOverflow_eq] at h
    simpa [hW, beq_iff_eq] using h
  have hbInt : b.toInt = -(2 ^ (W - 1) : Int) := by
    rw [hbMin, BitVec.toInt_intMin_of_pos hW]
  have haLo := BitVec.le_toInt a
  have haHi := BitVec.toInt_lt (x := a)
  change Bool.not a.msb = BitVec.ssubOverflow a b
  by_cases haNeg : a.toInt < 0
  · have hUpper : ¬a.toInt - b.toInt ≥ (2 ^ (W - 1) : Int) := by
      rw [hbInt]
      omega
    have hLower : ¬a.toInt - b.toInt < -(2 ^ (W - 1) : Int) := by
      rw [hbInt]
      omega
    simp [BitVec.msb_eq_toInt, BitVec.ssubOverflow, haNeg, hUpper, hLower]
  · have hUpper : a.toInt - b.toInt ≥ (2 ^ (W - 1) : Int) := by
      rw [hbInt]
      omega
    have hLower : ¬a.toInt - b.toInt < -(2 ^ (W - 1) : Int) := by
      rw [hbInt]
      omega
    simp [BitVec.msb_eq_toInt, BitVec.ssubOverflow, haNeg, hUpper, hLower]

theorem bvssubo_value_eq_ssubOverflow
    (W A B : Nat) (hW : 0 < W)
    (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval_bvssubo
        (SmtValue.Binary (native_nat_to_int W) (A : Int))
        (SmtValue.Binary (native_nat_to_int W) (B : Int)) =
      SmtValue.Boolean
        (BitVec.ssubOverflow (BitVec.ofInt W (A : Int))
          (BitVec.ofInt W (B : Int))) := by
  let b := BitVec.ofInt W (B : Int)
  have hNeg := bvnego_value_eq_negOverflow W B hW hB
  unfold __smtx_model_eval_bvssubo
  rw [hNeg]
  by_cases hb : BitVec.negOverflow b = true
  · rw [show BitVec.negOverflow (BitVec.ofInt W (B : Int)) = true by
      simpa [b] using hb]
    simp only [__smtx_model_eval_ite, __smtx_bv_sizeof_value]
    rw [bvsge_zero_value_eq_not_msb W A hW hA]
    rw [ssubOverflow_of_negOverflow W A B hW (by simpa [b] using hb)]
  · have hbFalse : BitVec.negOverflow b = false := by
      cases h : BitVec.negOverflow b
      · rfl
      · exact False.elim (hb h)
    rw [show BitVec.negOverflow (BitVec.ofInt W (B : Int)) = false by
      simpa [b] using hbFalse]
    simp only [__smtx_model_eval_ite]
    rw [eval_bvneg_canonical_ssubo W B]
    rw [bvsaddo_neg_value_eq_ssubOverflow W A B hW hA hB
      (by simpa [b] using hbFalse)]

theorem eval_bvSsuboDiff
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int))
    (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval M (__eo_to_smt (bvSsuboDiff x y)) =
      SmtValue.Binary (native_nat_to_int W)
        (((BitVec.ofInt W (A : Int) -
          BitVec.ofInt W (B : Int)).toNat : Nat) : Int) := by
  change __smtx_model_eval M
      (SmtTerm.bvsub (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [hx, hy]
  exact bvsub_value_eq_bitvec_sub W A B hA hB

theorem eval_bvSsuboRhs
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int))
    (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvSsuboRhs x y
            (Term.Numeral (native_nat_to_int (W - 1))))) =
      SmtValue.Boolean
        (bvSsuboFormula (A.testBit (W - 1)) (B.testBit (W - 1))
          ((BitVec.ofInt W (A : Int) -
            BitVec.ofInt W (B : Int)).toNat.testBit (W - 1))) := by
  let D := (BitVec.ofInt W (A : Int) -
    BitVec.ofInt W (B : Int)).toNat
  have hDiff := eval_bvSsuboDiff M x y W A B hx hy hA hB
  have hXBit := eval_extract_bit_term M x (native_nat_to_int W) (A : Int)
    (W - 1) hx (Int.natCast_nonneg A)
  have hYBit := eval_extract_bit_term M y (native_nat_to_int W) (B : Int)
    (W - 1) hy (Int.natCast_nonneg B)
  have hDiffBit := eval_extract_bit_term M (bvSsuboDiff x y)
    (native_nat_to_int W) (D : Int) (W - 1)
    (by simpa [D] using hDiff) (Int.natCast_nonneg D)
  let nm := Term.Numeral (native_nat_to_int (W - 1))
  have hXOne :
      __smtx_model_eval M (__eo_to_smt (bvSdivSign nm x)) =
        SmtValue.Boolean (A.testBit (W - 1)) := by
    simpa [bvSdivSign, bvSaddoBitEq] using
      eval_bvSaddoBitEq_one M nm x (A.testBit (W - 1))
        (by simpa [nm, bvSdivExtract] using hXBit)
  have hYOne :
      __smtx_model_eval M (__eo_to_smt (bvSdivSign nm y)) =
        SmtValue.Boolean (B.testBit (W - 1)) := by
    simpa [bvSdivSign, bvSaddoBitEq] using
      eval_bvSaddoBitEq_one M nm y (B.testBit (W - 1))
        (by simpa [nm, bvSdivExtract] using hYBit)
  have hDiffOne :
      __smtx_model_eval M
          (__eo_to_smt (bvSdivSign nm (bvSsuboDiff x y))) =
        SmtValue.Boolean (D.testBit (W - 1)) := by
    simpa [bvSdivSign, bvSaddoBitEq] using
      eval_bvSaddoBitEq_one M nm (bvSsuboDiff x y)
        (D.testBit (W - 1))
        (by simpa [nm, bvSdivExtract] using hDiffBit)
  have hXZero := eval_bvSaddoBitEq_zero M nm x (A.testBit (W - 1))
    (by simpa [nm, bvSdivExtract] using hXBit)
  have hYZero := eval_bvSaddoBitEq_zero M nm y (B.testBit (W - 1))
    (by simpa [nm, bvSdivExtract] using hYBit)
  have hDiffZero := eval_bvSaddoBitEq_zero M nm (bvSsuboDiff x y)
    (D.testBit (W - 1))
    (by simpa [nm, bvSdivExtract] using hDiffBit)
  have hFirst := eval_bvSaddoBranch M
    (bvSdivSign nm x)
    (bvSaddoBitEq nm y bvSaddoZeroBit)
    (bvSaddoBitEq nm (bvSsuboDiff x y) bvSaddoZeroBit)
    (A.testBit (W - 1)) (!(B.testBit (W - 1)))
    (!(D.testBit (W - 1))) hXOne hYZero hDiffZero
  have hSecond := eval_bvSaddoBranch M
    (bvSaddoBitEq nm x bvSaddoZeroBit)
    (bvSdivSign nm y) (bvSdivSign nm (bvSsuboDiff x y))
    (!(A.testBit (W - 1))) (B.testBit (W - 1))
    (D.testBit (W - 1)) hXZero hYOne hDiffOne
  have hFalse :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by rfl
  have hRight := eval_bvSaddoOr M
    (bvSaddoBranch (bvSaddoBitEq nm x bvSaddoZeroBit)
      (bvSdivSign nm y) (bvSdivSign nm (bvSsuboDiff x y)))
    (Term.Boolean false)
    ((!A.testBit (W - 1)) && B.testBit (W - 1) &&
      D.testBit (W - 1)) false hSecond hFalse
  have hOuter := eval_bvSaddoOr M
    (bvSaddoBranch (bvSdivSign nm x)
      (bvSaddoBitEq nm y bvSaddoZeroBit)
      (bvSaddoBitEq nm (bvSsuboDiff x y) bvSaddoZeroBit))
    (bvSaddoOr
      (bvSaddoBranch (bvSaddoBitEq nm x bvSaddoZeroBit)
        (bvSdivSign nm y) (bvSdivSign nm (bvSsuboDiff x y)))
      (Term.Boolean false))
    (A.testBit (W - 1) && !B.testBit (W - 1) &&
      !D.testBit (W - 1))
    (((!A.testBit (W - 1)) && B.testBit (W - 1) &&
      D.testBit (W - 1)) || false) hFirst hRight
  simpa [bvSsuboRhs, bvSsuboFormula, nm, D] using hOuter

private theorem bvSsuboFormula_eq_sign_circuit (sx sy sd : Bool) :
    bvSsuboFormula sx sy sd =
      ((!sx && sy && sd) || (sx && !sy && !sd)) := by
  cases sx <;> cases sy <;> cases sd <;> native_decide

theorem bvSsuboFormula_eq_ssubOverflow
    (W A B : Nat) (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    bvSsuboFormula (A.testBit (W - 1)) (B.testBit (W - 1))
        ((BitVec.ofInt W (A : Int) -
          BitVec.ofInt W (B : Int)).toNat.testBit (W - 1)) =
      BitVec.ssubOverflow (BitVec.ofInt W (A : Int))
        (BitVec.ofInt W (B : Int)) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  have hDiffMsb : (a - b).msb = (a - b).toNat.testBit (W - 1) := by
    rw [BitVec.msb_eq_getLsbD_last, ← BitVec.testBit_toNat]
  rw [BitVec.ssubOverflow_eq,
    bitvec_msb_of_canonical W A hA,
    bitvec_msb_of_canonical W B hB]
  change bvSsuboFormula (A.testBit (W - 1)) (B.testBit (W - 1))
      ((a - b).toNat.testBit (W - 1)) = _
  rw [hDiffMsb]
  exact bvSsuboFormula_eq_sign_circuit _ _ _

theorem eval_bvSsuboLhs
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hW : 0 < W)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int))
    (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval M (__eo_to_smt (bvSsuboLhs x y)) =
      SmtValue.Boolean
        (bvSsuboFormula (A.testBit (W - 1)) (B.testBit (W - 1))
          ((BitVec.ofInt W (A : Int) -
            BitVec.ofInt W (B : Int)).toNat.testBit (W - 1))) := by
  change __smtx_model_eval M
      (SmtTerm.bvssubo (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [hx, hy]
  rw [bvssubo_value_eq_ssubOverflow W A B hW hA hB]
  rw [bvSsuboFormula_eq_ssubOverflow W A B hA hB]

private theorem facts_bv_ssubo_term
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSsuboTerm x y nm) = Term.Bool ->
    eo_interprets M (bvSsuboTerm x y nm) true := by
  intro hXTrans hYTrans hPrem hResultTy
  rcases bv_ssubo_context x y nm hXTrans hYTrans hResultTy with
    ⟨w, n, _hXTy, _hYTy, rfl, hw0, hn0, hnW,
      hXSmtTy, hYSmtTy⟩
  have hIndex : n = w - 1 :=
    bv_sdiv_index_eq_of_premise M x w n hPrem hw0 hXSmtTy
  let W := native_int_to_nat w
  have hRound : native_nat_to_int W = w :=
    native_nat_to_int_int_to_nat_eq w hw0
  have hnNonneg : 0 ≤ n := by
    simpa [SmtEval.native_zleq] using hn0
  have hnLtW : n < w := by
    simpa [SmtEval.native_zlt] using hnW
  have hwPos : 0 < w := Int.lt_of_le_of_lt hnNonneg hnLtW
  have hW : 0 < W := by
    rw [← hRound] at hwPos
    have hwPos' : (0 : Int) < (W : Int) := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hwPos
    exact_mod_cast hwPos'
  have hOneLe : 1 ≤ W := hW
  have hIndexNat : n = native_nat_to_int (W - 1) := by
    rw [hIndex, ← hRound]
    change (W : Int) - 1 = ((W - 1 : Nat) : Int)
    rw [Int.ofNat_sub hOneLe]
    rfl
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  rcases bitvec_eval_nat_payload M hM x W hXSmtTyW with
    ⟨A, hXEval, hABound⟩
  rcases bitvec_eval_nat_payload M hM y W hYSmtTyW with
    ⟨B, hYEval, hBBound⟩
  have hLhsEval := eval_bvSsuboLhs M x y W A B hW
    hXEval hYEval hABound hBBound
  have hRhsEval := eval_bvSsuboRhs M x y W A B
    hXEval hYEval hABound hBBound
  have hBool := typed_bv_ssubo_term x y (Term.Numeral n)
    hXTrans hYTrans hResultTy
  unfold bvSsuboTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSsuboTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvSsuboLhs x y)))
      (__smtx_model_eval M
        (__eo_to_smt (bvSsuboRhs x y (Term.Numeral n))))
    rw [hLhsEval]
    simpa [hIndexNat] using
      (show RuleProofs.smt_value_rel
          (SmtValue.Boolean
            (bvSsuboFormula (A.testBit (W - 1)) (B.testBit (W - 1))
              ((BitVec.ofInt W (A : Int) -
                BitVec.ofInt W (B : Int)).toNat.testBit (W - 1))))
          (__smtx_model_eval M
            (__eo_to_smt
              (bvSsuboRhs x y
                (Term.Numeral (native_nat_to_int (W - 1)))))) from by
        rw [hRhsEval]
        exact RuleProofs.smt_value_rel_refl _)

def bvSsuboProgram (x y nm : Term) : Term :=
  __eo_prog_bv_ssubo_eliminate x y nm (Proof.pf (bvSdivPrem x nm))

private theorem bv_ssubo_program_eq_term_of_ne_stuck
    (x y nm : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> nm ≠ Term.Stuck ->
    bvSsuboProgram x y nm = bvSsuboTerm x y nm := by
  intro hXNe hYNe hNmNe
  unfold bvSsuboProgram bvSdivPrem
  rw [__eo_prog_bv_ssubo_eliminate.eq_4 x y nm nm x
    hXNe hYNe hNmNe]
  simp [bvSsuboTerm, bvSsuboLhs, bvSsuboRhs, bvSsuboDiff,
    bvSaddoBranch, bvSaddoAnd, bvSaddoOr, bvSaddoBitEq,
    bvSaddoZeroBit, bvSdivSign, bvSdivExtract, bvSdivBitOne,
    __eo_requires, __eo_and, __eo_eq, __eo_mk_apply,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hXNe, hNmNe]

theorem bv_ssubo_program_eq_term_of_type_bool (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSsuboProgram x y nm) = Term.Bool ->
    bvSsuboProgram x y nm = bvSsuboTerm x y nm := by
  intro hXTrans hYTrans hNmTrans _hTy
  exact bv_ssubo_program_eq_term_of_ne_stuck x y nm
    (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans)

theorem bv_ssubo_eliminate_shape_of_ne_stuck (x y nm P : Term) :
    __eo_prog_bv_ssubo_eliminate x y nm (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ nm ≠ Term.Stuck ∧
      ∃ pnm px, P = bvSdivPrem px pnm := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_ssubo_eliminate.eq_1 y nm (Proof.pf P))
  have hYNe : y ≠ Term.Stuck := by
    intro hY
    subst y
    exact hProg
      (__eo_prog_bv_ssubo_eliminate.eq_2 x nm (Proof.pf P) hXNe)
  have hNmNe : nm ≠ Term.Stuck := by
    intro hNm
    subst nm
    exact hProg
      (__eo_prog_bv_ssubo_eliminate.eq_3 x y (Proof.pf P) hXNe hYNe)
  refine ⟨hXNe, hYNe, hNmNe, ?_⟩
  by_cases hShape : ∃ pnm px, P = bvSdivPrem px pnm
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_ssubo_eliminate.eq_5 x y nm (Proof.pf P)
        hXNe hYNe hNmNe (by
          intro pnm px hP
          cases hP
          exact hShape ⟨pnm, px, rfl⟩)))

theorem typed_bv_ssubo_program (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSsuboProgram x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSsuboProgram x y nm) := by
  intro hXTrans hYTrans hNmTrans hResultTy
  have hEq := bv_ssubo_program_eq_term_of_type_bool x y nm
    hXTrans hYTrans hNmTrans hResultTy
  have hTermTy : __eo_typeof (bvSsuboTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_ssubo_term x y nm hXTrans hYTrans hTermTy

theorem facts_bv_ssubo_program
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSsuboProgram x y nm) = Term.Bool ->
    eo_interprets M (bvSsuboProgram x y nm) true := by
  intro hXTrans hYTrans hNmTrans hPrem hResultTy
  have hEq := bv_ssubo_program_eq_term_of_type_bool x y nm
    hXTrans hYTrans hNmTrans hResultTy
  have hTermTy : __eo_typeof (bvSsuboTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_ssubo_term M hM x y nm
    hXTrans hYTrans hPrem hTermTy
