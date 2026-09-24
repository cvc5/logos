module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

inductive BvBitwiseElimKind where
  | nand
  | nor
  | xnor
  deriving DecidableEq

def BvBitwiseElimKind.lhsOp : BvBitwiseElimKind -> UserOp
  | .nand => UserOp.bvnand
  | .nor => UserOp.bvnor
  | .xnor => UserOp.bvxnor

def BvBitwiseElimKind.innerOp : BvBitwiseElimKind -> UserOp
  | .nand => UserOp.bvand
  | .nor => UserOp.bvor
  | .xnor => UserOp.bvxor

def bvBitwiseElimLhs (k : BvBitwiseElimKind) (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp k.lhsOp) x) y

def bvBitwiseElimRhs (k : BvBitwiseElimKind) (x y : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot)
    (Term.Apply (Term.Apply (Term.UOp k.innerOp) x)
      (Term.Apply (Term.Apply (Term.UOp k.innerOp) y)
        (__eo_nil (Term.UOp k.innerOp) (__eo_typeof x))))

def bvBitwiseElimTerm (k : BvBitwiseElimKind) (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvBitwiseElimLhs k x y))
    (bvBitwiseElimRhs k x y)

private theorem eo_typeof_bvand_arg_types_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ u,
      A = Term.Apply (Term.UOp UserOp.BitVec) u ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) u := by
  cases A <;> cases B <;> simp [__eo_typeof_bvand] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvand] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvand] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvand] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

theorem bv_bitwise_elim_args_type_of_bool
    (k : BvBitwiseElimKind) (x y : Term) :
    __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hLeftNN :
      __eo_typeof (bvBitwiseElimLhs k x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvBitwiseElimLhs k x y))
        (__eo_typeof (bvBitwiseElimRhs k x y))
        (by
          cases k <;>
            simpa [bvBitwiseElimTerm, bvBitwiseElimLhs, bvBitwiseElimRhs, __eo_nil, __eo_typeof, __eo_typeof_eq]
              using hTy)
    exact hOperands.1
  have hBvAndNN :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    cases k <;>
      exact hLeftNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hBvAndNN with
    ⟨w, hXTy, hYTy⟩
  refine ⟨w, hXTy, hYTy, ?_⟩
  intro hW
  subst w
  simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not, hXTy, hYTy] at hBvAndNN

theorem bv_bitwise_elim_nil_ne
    (k : BvBitwiseElimKind) (x y : Term) :
    __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool ->
    __eo_nil (Term.UOp k.innerOp) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy
  have hRightNN :
      __eo_typeof (bvBitwiseElimRhs k x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvBitwiseElimLhs k x y))
        (__eo_typeof (bvBitwiseElimRhs k x y))
        (by
          cases k <;>
            simpa [bvBitwiseElimTerm, bvBitwiseElimLhs, bvBitwiseElimRhs, __eo_nil, __eo_typeof, __eo_typeof_eq]
              using hTy)
    exact hOperands.2
  intro hNil
  apply hRightNN
  cases k with
  | nand =>
      have hNil' :
          __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x) = Term.Stuck := by
        simpa [BvBitwiseElimKind.innerOp] using hNil
      change __eo_typeof
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) y)
                (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x))))) =
        Term.Stuck
      rw [hNil']
      change __eo_typeof_bvnot
          (__eo_typeof_bvand (__eo_typeof x)
            (__eo_typeof_bvand (__eo_typeof y) Term.Stuck)) =
        Term.Stuck
      simp [__eo_typeof_bvnot, __eo_typeof_bvand]
  | nor =>
      have hNil' :
          __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x) = Term.Stuck := by
        simpa [BvBitwiseElimKind.innerOp] using hNil
      change __eo_typeof
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) y)
                (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x))))) =
        Term.Stuck
      rw [hNil']
      change __eo_typeof_bvnot
          (__eo_typeof_bvand (__eo_typeof x)
            (__eo_typeof_bvand (__eo_typeof y) Term.Stuck)) =
        Term.Stuck
      simp [__eo_typeof_bvnot, __eo_typeof_bvand]
  | xnor =>
      have hNil' :
          __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) = Term.Stuck := by
        simpa [BvBitwiseElimKind.innerOp] using hNil
      change __eo_typeof
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
                (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))))) =
        Term.Stuck
      rw [hNil']
      change __eo_typeof_bvnot
          (__eo_typeof_bvand (__eo_typeof x)
            (__eo_typeof_bvand (__eo_typeof y) Term.Stuck)) =
        Term.Stuck
      simp [__eo_typeof_bvnot, __eo_typeof_bvand]

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
    cases hNonneg : native_zleq 0 n <;>
      simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem bitvec_toInt_emod_pow (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2 ^ w
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)

private theorem native_mod_pow2_eq_bitvec_toNat (w : Nat) (n : Int) :
    native_mod_total n (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n).toNat : Int) := by
  rw [native_int_pow2_nat]
  change n % (2 ^ w : Int) = ((BitVec.ofInt w n).toNat : Int)
  rw [BitVec.toNat_ofInt]
  have hpow : 0 < (2 ^ w : Int) := by exact_mod_cast Nat.two_pow_pos w
  exact (Int.toNat_of_nonneg (Int.emod_nonneg n (Int.ne_of_gt hpow))).symm

private theorem native_binary_and_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 &&& BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_and, native_piand, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_and, native_piand, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 &&& BitVec.ofInt (Nat.succ w) n2)

private theorem native_binary_or_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_or (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 ||| BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_or, impl_native_pior, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_or, impl_native_pior, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 ||| BitVec.ofInt (Nat.succ w) n2)

private theorem native_binary_xor_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 ^^^ BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_xor, impl_native_pixor, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_xor, impl_native_pixor, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 ^^^ BitVec.ofInt (Nat.succ w) n2)

private theorem native_pow2_minus_one_mod_self_nat (w : Nat) :
    native_mod_total
        (native_int_pow2 (native_nat_to_int w) - 1)
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 := by
  rw [native_int_pow2_nat]
  have hPowPos : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hLower : 0 <= (2 ^ w : Int) - 1 := by
    omega
  have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
    omega
  simpa [native_mod_total] using Int.emod_eq_of_lt hLower hUpper

private theorem bitvec_ofInt_allOnes (w : Nat) :
    BitVec.ofInt w (native_int_pow2 (native_nat_to_int w) - 1) =
      BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes, native_int_pow2_nat]
  have hPowPos : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hLower : 0 <= (2 ^ w : Int) - 1 := by
    omega
  have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
    omega
  change (((2 ^ w : Int) - 1) % (2 ^ w : Int)).toNat = 2 ^ w - 1
  rw [Int.emod_eq_of_lt hLower hUpper]
  have hToNat :
      (((2 ^ w : Int) - 1).toNat : Int) = (2 ^ w : Int) - 1 :=
    Int.toNat_of_nonneg hLower
  have hRhs :
      ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
    Int.ofNat_sub Nat.one_le_two_pow
  exact Int.ofNat.inj (hToNat.trans hRhs.symm)

private theorem native_binary_and_right_allOnes_mod_nat
    (w : Nat) (n id : Int) :
    BitVec.ofInt w id = BitVec.allOnes w ->
    native_mod_total (native_binary_and (native_nat_to_int w) n id)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  intro hId
  rw [native_binary_and_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  rw [hId, BitVec.and_allOnes]

private theorem native_binary_or_right_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_or (native_nat_to_int w) n 0)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_or_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  simp

private theorem native_binary_xor_right_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n 0)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_xor_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  simp

private theorem bvAnd_nil_eq_allOnes_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvand) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvand) ty =
      Term.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1) := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · have hMod :
        native_mod_total
            (native_binary_not (native_nat_to_int w) 0)
            (native_int_pow2 (native_nat_to_int w)) =
          native_int_pow2 (native_nat_to_int w) - 1 := by
      simpa [native_binary_not, native_zplus, native_zneg, native_int_pow2, native_mod_total, native_nat_to_int, native_pow2_minus_one_mod_self_nat] using
        native_pow2_minus_one_mod_self_nat w
    have hBoundProp : native_nat_to_int w <= 4294967296 := by
      simpa [native_zleq] using hBound
    have hWidthNonneg : 0 <= native_nat_to_int w := by
      simp [native_nat_to_int]
    have hToBin :
        __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
          Term.Binary (native_nat_to_int w) 0 := by
      simp [__eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
        hBoundProp, hWidthNonneg, native_mod_total]
    change __eo_not
        (__eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0)) =
      Term.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1)
    rw [hToBin]
    simp [__eo_not, hMod]
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvand, __eo_to_bin, hBoundFalse,
        native_ite, native_zleq, __eo_not]
    exact False.elim (hNe hStuck)

private theorem bvZero_to_bin_eq_of_bound (w : Nat) :
    native_zleq (native_nat_to_int w) 4294967296 = true ->
    __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hBound
  have hBoundProp : native_nat_to_int w <= 4294967296 := by
    simpa [native_zleq] using hBound
  have hWidthNonneg : 0 <= native_nat_to_int w := by
    simp [native_nat_to_int]
  simp [__eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
    hBoundProp, hWidthNonneg, native_mod_total]

private theorem bvOr_nil_eq_zero_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvor) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvor) ty =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · change
      __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Binary (native_nat_to_int w) 0
    exact bvZero_to_bin_eq_of_bound w hBound
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvor, __eo_to_bin, hBoundFalse,
        native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem bvXor_nil_eq_zero_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvxor) ty =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · change
      __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Binary (native_nat_to_int w) 0
    exact bvZero_to_bin_eq_of_bound w hBound
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvxor, __eo_to_bin, hBoundFalse,
        native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem smt_typeof_binary_allOnes (w : Nat) :
    __smtx_typeof
      (SmtTerm.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1)) =
      SmtType.BitVec w := by
  have hMod := native_pow2_minus_one_mod_self_nat w
  have hMod' :
      native_mod_total (native_int_pow2 (↑w) - 1) (native_int_pow2 (↑w)) =
        native_int_pow2 (↑w) - 1 := by
    simpa [native_nat_to_int] using hMod
  simp [__smtx_typeof, SmtEval.native_and, native_ite, native_zleq,
    native_zeq, hMod', native_nat_to_int,
    SmtEval.native_int_to_nat, native_int_to_nat]

private theorem smt_typeof_binary_zero (w : Nat) :
    __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) =
      SmtType.BitVec w := by
  simp [__smtx_typeof, SmtEval.native_and, native_ite, native_zleq,
    native_zeq, native_nat_to_int, native_mod_total, SmtEval.native_int_to_nat,
    native_int_to_nat]

theorem bvand_generated_nil_eq_allOnes
    (w : Nat) :
    __eo_nil (Term.UOp UserOp.bvand)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvand)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w))) =
      Term.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1) := by
  intro hNe
  exact bvAnd_nil_eq_allOnes_of_type w (by
    simp [__eo_to_smt_type, native_ite, SmtEval.native_zleq, native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat]) hNe

theorem bvor_generated_nil_eq_zero
    (w : Nat) :
    __eo_nil (Term.UOp UserOp.bvor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w))) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hNe
  exact bvOr_nil_eq_zero_of_type w (by
    simp [__eo_to_smt_type, native_ite, SmtEval.native_zleq, native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat]) hNe

theorem bvxor_generated_nil_eq_zero
    (w : Nat) :
    __eo_nil (Term.UOp UserOp.bvxor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvxor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w))) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hNe
  exact bvXor_nil_eq_zero_of_type w (by
    simp [__eo_to_smt_type, native_ite, SmtEval.native_zleq, native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat]) hNe

theorem bvand_generated_nil_smt_type
    (w : Nat) (hNe : __eo_nil (Term.UOp UserOp.bvand)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))))) = SmtType.BitVec w := by
  rw [bvand_generated_nil_eq_allOnes w hNe]
  exact smt_typeof_binary_allOnes w

theorem bvor_generated_nil_smt_type
    (w : Nat) (hNe : __eo_nil (Term.UOp UserOp.bvor)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))))) = SmtType.BitVec w := by
  rw [bvor_generated_nil_eq_zero w hNe]
  exact smt_typeof_binary_zero w

theorem bvxor_generated_nil_smt_type
    (w : Nat) (hNe : __eo_nil (Term.UOp UserOp.bvxor)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))))) = SmtType.BitVec w := by
  rw [bvxor_generated_nil_eq_zero w hNe]
  exact smt_typeof_binary_zero w

theorem bvand_generated_nil_marker
    (w : Nat) (hNe : __eo_nil (Term.UOp UserOp.bvand)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.bvand)
      (__eo_nil (Term.UOp UserOp.bvand)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))) = Term.Boolean true := by
  rw [bvand_generated_nil_eq_allOnes w hNe]
  simp [__eo_is_list_nil, __eo_is_list_nil_bvand, __eo_to_z, __eo_not,
    __eo_is_eq, native_binary_not, native_zplus, native_zneg,
    native_mod_total, native_and, native_not, SmtEval.native_not,
    native_teq]

theorem bvor_generated_nil_marker
    (w : Nat) (hNe : __eo_nil (Term.UOp UserOp.bvor)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.bvor)
      (__eo_nil (Term.UOp UserOp.bvor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))) = Term.Boolean true := by
  rw [bvor_generated_nil_eq_zero w hNe]
  simp [__eo_is_list_nil, __eo_is_list_nil_bvor, __eo_to_z, __eo_is_eq,
    native_and, native_not, SmtEval.native_not, native_teq]

theorem bvxor_generated_nil_marker
    (w : Nat) (hNe : __eo_nil (Term.UOp UserOp.bvxor)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.bvxor)
      (__eo_nil (Term.UOp UserOp.bvxor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))) = Term.Boolean true := by
  rw [bvxor_generated_nil_eq_zero w hNe]
  simp [__eo_is_list_nil, __eo_is_list_nil_bvxor, __eo_to_z, __eo_is_eq,
    native_and, native_not, SmtEval.native_not, native_teq]

private theorem smt_typeof_nil
    (k : BvBitwiseElimKind) (x : Term) (w : Nat) :
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp k.innerOp) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (__eo_nil (Term.UOp k.innerOp) (__eo_typeof x))) =
      SmtType.BitVec w := by
  intro hTy hNilNe
  cases k with
  | nand =>
      have hEq := bvAnd_nil_eq_allOnes_of_type w hTy hNilNe
      change __smtx_typeof
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x))) =
        SmtType.BitVec w
      rw [hEq]
      exact smt_typeof_binary_allOnes w
  | nor =>
      have hEq := bvOr_nil_eq_zero_of_type w hTy hNilNe
      change __smtx_typeof
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x))) =
        SmtType.BitVec w
      rw [hEq]
      exact smt_typeof_binary_zero w
  | xnor =>
      have hEq := bvXor_nil_eq_zero_of_type w hTy hNilNe
      change __smtx_typeof
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
        SmtType.BitVec w
      rw [hEq]
      exact smt_typeof_binary_zero w

private theorem smt_eval_nil
    (M : SmtModel) (k : BvBitwiseElimKind) (x : Term) (w : Nat) :
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp k.innerOp) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp k.innerOp) (__eo_typeof x))) =
      match k with
      | .nand =>
          SmtValue.Binary (native_nat_to_int w)
            (native_int_pow2 (native_nat_to_int w) - 1)
      | .nor => SmtValue.Binary (native_nat_to_int w) 0
      | .xnor => SmtValue.Binary (native_nat_to_int w) 0 := by
  intro hTy hNilNe
  cases k with
  | nand =>
      have hEq := bvAnd_nil_eq_allOnes_of_type w hTy hNilNe
      change __smtx_model_eval M
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x))) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)
      rw [hEq]
      change __smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_int_pow2 (native_nat_to_int w) - 1)) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)
      rw [__smtx_model_eval.eq_def] <;> simp only
  | nor =>
      have hEq := bvOr_nil_eq_zero_of_type w hTy hNilNe
      change __smtx_model_eval M
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x))) =
        SmtValue.Binary (native_nat_to_int w) 0
      rw [hEq]
      change __smtx_model_eval M (SmtTerm.Binary (native_nat_to_int w) 0) =
        SmtValue.Binary (native_nat_to_int w) 0
      rw [__smtx_model_eval.eq_def] <;> simp only
  | xnor =>
      have hEq := bvXor_nil_eq_zero_of_type w hTy hNilNe
      change __smtx_model_eval M
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
        SmtValue.Binary (native_nat_to_int w) 0
      rw [hEq]
      change __smtx_model_eval M (SmtTerm.Binary (native_nat_to_int w) 0) =
        SmtValue.Binary (native_nat_to_int w) 0
      rw [__smtx_model_eval.eq_def] <;> simp only

private theorem bitwise_context
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool ->
    ∃ w : Nat,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ∧
      __eo_nil (Term.UOp k.innerOp) (__eo_typeof x) ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  rcases bv_bitwise_elim_args_type_of_bool k x y hResultTy with
    ⟨wTerm, hXTy, hYTy, _hWTerm⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x wTerm hXTrans hXTy with
    ⟨n, hWTerm, hNonneg, hXSmtTy⟩
  subst wTerm
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (native_int_to_nat n) := by
    rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n) hYTrans
        (by simpa using hYTy) with
      ⟨m, hM, _hMNonneg, hYSmtTy⟩
    cases hM
    exact hYSmtTy
  have hXTypeSmt :
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec (native_int_to_nat n) := by
    rw [hXTy]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  exact ⟨native_int_to_nat n, hXSmtTy, hYSmtTy, hXTypeSmt,
    bv_bitwise_elim_nil_ne k x y hResultTy⟩

private theorem smtx_typeof_bvand_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvand x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvxor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvxor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvnand_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnand x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvnor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvxnor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvxnor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_lhs
    (k : BvBitwiseElimKind) (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (bvBitwiseElimLhs k x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy
  cases k with
  | nand =>
    change __smtx_typeof (SmtTerm.bvnand (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.BitVec w
    rw [smtx_typeof_bvnand_term_eq]
    simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_ite, native_nateq]
  | nor =>
    change __smtx_typeof (SmtTerm.bvnor (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.BitVec w
    rw [smtx_typeof_bvnor_term_eq]
    simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_ite, native_nateq]
  | xnor =>
    change __smtx_typeof (SmtTerm.bvxnor (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.BitVec w
    rw [smtx_typeof_bvxnor_term_eq]
    simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_ite, native_nateq]

private theorem smt_typeof_rhs
    (k : BvBitwiseElimKind) (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp k.innerOp) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvBitwiseElimRhs k x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hXTypeSmt hNilNe
  have hNilTy := smt_typeof_nil k x w hXTypeSmt hNilNe
  cases k with
  | nand =>
    have hNilTy' :
        __smtx_typeof
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x))) =
          SmtType.BitVec w := by
      simpa [BvBitwiseElimKind.innerOp] using hNilTy
    change __smtx_typeof
        (SmtTerm.bvnot
          (SmtTerm.bvand (__eo_to_smt x)
            (SmtTerm.bvand (__eo_to_smt y)
              (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x)))))) =
      SmtType.BitVec w
    rw [smtx_typeof_bvnot_term_eq, smtx_typeof_bvand_term_eq,
      smtx_typeof_bvand_term_eq]
    simp [__smtx_typeof_bv_op_1, __smtx_typeof_bv_op_2, hXTy, hYTy,
      hNilTy', native_ite, native_nateq]
  | nor =>
    have hNilTy' :
        __smtx_typeof
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x))) =
          SmtType.BitVec w := by
      simpa [BvBitwiseElimKind.innerOp] using hNilTy
    change __smtx_typeof
        (SmtTerm.bvnot
          (SmtTerm.bvor (__eo_to_smt x)
            (SmtTerm.bvor (__eo_to_smt y)
              (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x)))))) =
      SmtType.BitVec w
    rw [smtx_typeof_bvnot_term_eq, smtx_typeof_bvor_term_eq,
      smtx_typeof_bvor_term_eq]
    simp [__smtx_typeof_bv_op_1, __smtx_typeof_bv_op_2, hXTy, hYTy,
      hNilTy', native_ite, native_nateq]
  | xnor =>
    have hNilTy' :
        __smtx_typeof
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
          SmtType.BitVec w := by
      simpa [BvBitwiseElimKind.innerOp] using hNilTy
    change __smtx_typeof
        (SmtTerm.bvnot
          (SmtTerm.bvxor (__eo_to_smt x)
            (SmtTerm.bvxor (__eo_to_smt y)
              (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))) =
      SmtType.BitVec w
    rw [smtx_typeof_bvnot_term_eq, smtx_typeof_bvxor_term_eq,
      smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_1, __smtx_typeof_bv_op_2, hXTy, hYTy,
      hNilTy', native_ite, native_nateq]

theorem typed_bv_bitwise_elim_term
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvBitwiseElimTerm k x y) := by
  intro hXTrans hYTrans hResultTy
  rcases bitwise_context k x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hNilNe⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvBitwiseElimLhs k x y) (bvBitwiseElimRhs k x y)
    (by
      rw [smt_typeof_lhs k x y w hXTy hYTy,
        smt_typeof_rhs k x y w hXTy hYTy hXTypeSmt hNilNe])
    (by
      rw [smt_typeof_lhs k x y w hXTy hYTy]
      simp)

private theorem smt_eval_binary_of_smt_type_bitvec
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (w : native_Nat) :
    __smtx_typeof t = SmtType.BitVec w ->
    ∃ n, __smtx_model_eval M t =
      SmtValue.Binary (native_nat_to_int w) n ∧
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.BitVec w := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  rcases bitvec_value_canonical hValTy with ⟨n, hEval⟩
  have hCan :
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical (by simpa [hEval] using hValTy)
  exact ⟨n, hEval, hCan⟩

private theorem smt_eval_inner_identity
    (k : BvBitwiseElimKind) (w : Nat) (ny : Int) :
    native_zeq ny
        (native_mod_total ny (native_int_pow2 (native_nat_to_int w))) =
      true ->
    (match k with
    | .nand =>
        __smtx_model_eval_bvand
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w)
            (native_int_pow2 (native_nat_to_int w) - 1))
    | .nor =>
        __smtx_model_eval_bvor
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w) 0)
    | .xnor =>
        __smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w) 0)) =
      SmtValue.Binary (native_nat_to_int w) ny := by
  intro hCan
  have hModEq :
      native_mod_total ny (native_int_pow2 (native_nat_to_int w)) = ny := by
    have hEq :
        ny =
          native_mod_total ny (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hCan
    exact hEq.symm
  cases k <;> simp [__smtx_model_eval_bvand, __smtx_model_eval_bvor,
    __smtx_model_eval_bvxor]
  · rw [native_binary_and_right_allOnes_mod_nat w ny
      (native_int_pow2 (native_nat_to_int w) - 1)
      (bitvec_ofInt_allOnes w), hModEq]
  · rw [native_binary_or_right_zero_mod_nat w ny, hModEq]
  · rw [native_binary_xor_right_zero_mod_nat w ny, hModEq]

private theorem smtx_eval_bvand_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvand x y) =
      __smtx_model_eval_bvand (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvor x y) =
      __smtx_model_eval_bvor (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvxor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvxor x y) =
      __smtx_model_eval_bvxor (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvnand_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvnand x y) =
      __smtx_model_eval_bvnand (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvnor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvnor x y) =
      __smtx_model_eval_bvnor (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvxnor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvxnor x y) =
      __smtx_model_eval_bvxnor (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_bitwise_elim
    (M : SmtModel) (hM : model_wf M)
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvBitwiseElimLhs k x y)) =
      __smtx_model_eval M (__eo_to_smt (bvBitwiseElimRhs k x y)) := by
  intro hXTrans hYTrans hResultTy
  rcases bitwise_context k x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hNilNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, _hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, hYCan⟩
  have hNilEval := smt_eval_nil M k x w hXTypeSmt hNilNe
  cases k with
  | nand =>
      have hNilEval' :
          __smtx_model_eval M
              (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x))) =
            SmtValue.Binary (native_nat_to_int w)
              (native_int_pow2 (native_nat_to_int w) - 1) := by
        simpa [BvBitwiseElimKind.innerOp] using hNilEval
      change __smtx_model_eval M (SmtTerm.bvnand (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval M
          (SmtTerm.bvnot
            (SmtTerm.bvand (__eo_to_smt x)
              (SmtTerm.bvand (__eo_to_smt y)
                (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x)))))
          )
      rw [smtx_eval_bvnand_term_eq, smtx_eval_bvnot_term_eq,
        smtx_eval_bvand_term_eq, smtx_eval_bvand_term_eq]
      simp [__smtx_model_eval_bvnand, hXEval, hYEval, hNilEval']
      have hInner := smt_eval_inner_identity BvBitwiseElimKind.nand w ny hYCan
      change __smtx_model_eval_bvand
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w)
            (native_int_pow2 (native_nat_to_int w) - 1)) =
        SmtValue.Binary (native_nat_to_int w) ny at hInner
      rw [hInner]
  | nor =>
      have hNilEval' :
          __smtx_model_eval M
              (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x))) =
            SmtValue.Binary (native_nat_to_int w) 0 := by
        simpa [BvBitwiseElimKind.innerOp] using hNilEval
      change __smtx_model_eval M (SmtTerm.bvnor (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval M
          (SmtTerm.bvnot
            (SmtTerm.bvor (__eo_to_smt x)
              (SmtTerm.bvor (__eo_to_smt y)
                (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x)))))
          )
      rw [smtx_eval_bvnor_term_eq, smtx_eval_bvnot_term_eq,
        smtx_eval_bvor_term_eq, smtx_eval_bvor_term_eq]
      simp [__smtx_model_eval_bvnor, hXEval, hYEval, hNilEval']
      have hInner := smt_eval_inner_identity BvBitwiseElimKind.nor w ny hYCan
      change __smtx_model_eval_bvor
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w) 0) =
        SmtValue.Binary (native_nat_to_int w) ny at hInner
      rw [hInner]
  | xnor =>
      have hNilEval' :
          __smtx_model_eval M
              (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
            SmtValue.Binary (native_nat_to_int w) 0 := by
        simpa [BvBitwiseElimKind.innerOp] using hNilEval
      change __smtx_model_eval M (SmtTerm.bvxnor (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval M
          (SmtTerm.bvnot
            (SmtTerm.bvxor (__eo_to_smt x)
              (SmtTerm.bvxor (__eo_to_smt y)
                (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))
          )
      rw [smtx_eval_bvxnor_term_eq, smtx_eval_bvnot_term_eq,
        smtx_eval_bvxor_term_eq, smtx_eval_bvxor_term_eq]
      simp [__smtx_model_eval_bvxnor, hXEval, hYEval, hNilEval']
      have hInner := smt_eval_inner_identity BvBitwiseElimKind.xnor w ny hYCan
      change __smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w) 0) =
        SmtValue.Binary (native_nat_to_int w) ny at hInner
      rw [hInner]

theorem facts_bv_bitwise_elim_term
    (M : SmtModel) (hM : model_wf M)
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool ->
    eo_interprets M (bvBitwiseElimTerm k x y) true := by
  intro hXTrans hYTrans hResultTy
  have hBool :=
    typed_bv_bitwise_elim_term k x y hXTrans hYTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvBitwiseElimLhs k x y)))
      (__smtx_model_eval M (__eo_to_smt (bvBitwiseElimRhs k x y)))
    rw [eval_bv_bitwise_elim M hM k x y hXTrans hYTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvBitwiseElimProgram (k : BvBitwiseElimKind) (x y : Term) : Term :=
  match k with
  | .nand => __eo_prog_bv_nand_eliminate x y
  | .nor => __eo_prog_bv_nor_eliminate x y
  | .xnor => __eo_prog_bv_xnor_eliminate x y

private def bvBitwiseElimProgramSkeleton
    (k : BvBitwiseElimKind) (x y : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (bvBitwiseElimLhs k x y))
    (__eo_mk_apply (Term.UOp UserOp.bvnot)
      (__eo_mk_apply (Term.Apply (Term.UOp k.innerOp) x)
        (__eo_mk_apply (Term.Apply (Term.UOp k.innerOp) y)
          (__eo_nil (Term.UOp k.innerOp) (__eo_typeof x)))))

private theorem bvBitwiseElimProgram_eq_skeleton_of_ne_stuck
    (k : BvBitwiseElimKind) (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    bvBitwiseElimProgram k x y =
      bvBitwiseElimProgramSkeleton k x y := by
  intro hXNe hYNe
  cases k <;> cases x <;> cases y <;>
    simp [bvBitwiseElimProgram, bvBitwiseElimProgramSkeleton,
      __eo_prog_bv_nand_eliminate, __eo_prog_bv_nor_eliminate,
      __eo_prog_bv_xnor_eliminate, bvBitwiseElimLhs,
      BvBitwiseElimKind.lhsOp, BvBitwiseElimKind.innerOp] at hXNe hYNe ⊢

theorem bvBitwiseElimProgram_eq_term_of_type_bool
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimProgram k x y) = Term.Bool ->
    bvBitwiseElimProgram k x y = bvBitwiseElimTerm k x y := by
  intro hXTrans hYTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hSkeleton :=
    bvBitwiseElimProgram_eq_skeleton_of_ne_stuck k x y hXNe hYNe
  cases k with
  | nand =>
      by_cases hNil :
          __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof x) = Term.Stuck
      · have hProgStuck :
            bvBitwiseElimProgram BvBitwiseElimKind.nand x y = Term.Stuck := by
          rw [hSkeleton]
          simp [bvBitwiseElimProgramSkeleton, BvBitwiseElimKind.innerOp,
            __eo_mk_apply, hNil]
        rw [hProgStuck] at hTy
        have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hBad hTy)
      · rw [hSkeleton]
        simp [bvBitwiseElimProgramSkeleton, bvBitwiseElimTerm,
          bvBitwiseElimLhs, bvBitwiseElimRhs, BvBitwiseElimKind.lhsOp,
          BvBitwiseElimKind.innerOp, __eo_mk_apply, hNil]
  | nor =>
      by_cases hNil :
          __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof x) = Term.Stuck
      · have hProgStuck :
            bvBitwiseElimProgram BvBitwiseElimKind.nor x y = Term.Stuck := by
          rw [hSkeleton]
          simp [bvBitwiseElimProgramSkeleton, BvBitwiseElimKind.innerOp,
            __eo_mk_apply, hNil]
        rw [hProgStuck] at hTy
        have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hBad hTy)
      · rw [hSkeleton]
        simp [bvBitwiseElimProgramSkeleton, bvBitwiseElimTerm,
          bvBitwiseElimLhs, bvBitwiseElimRhs, BvBitwiseElimKind.lhsOp,
          BvBitwiseElimKind.innerOp, __eo_mk_apply, hNil]
  | xnor =>
      by_cases hNil :
          __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) = Term.Stuck
      · have hProgStuck :
            bvBitwiseElimProgram BvBitwiseElimKind.xnor x y = Term.Stuck := by
          rw [hSkeleton]
          simp [bvBitwiseElimProgramSkeleton, BvBitwiseElimKind.innerOp,
            __eo_mk_apply, hNil]
        rw [hProgStuck] at hTy
        have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hBad hTy)
      · rw [hSkeleton]
        simp [bvBitwiseElimProgramSkeleton, bvBitwiseElimTerm,
          bvBitwiseElimLhs, bvBitwiseElimRhs, BvBitwiseElimKind.lhsOp,
          BvBitwiseElimKind.innerOp, __eo_mk_apply, hNil]

theorem typed_bv_bitwise_elim_program
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimProgram k x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvBitwiseElimProgram k x y) := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvBitwiseElimProgram_eq_term_of_type_bool k x y hXTrans hYTrans hResultTy
  have hTermTy :
      __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_bitwise_elim_term k x y hXTrans hYTrans hTermTy

theorem facts_bv_bitwise_elim_program
    (M : SmtModel) (hM : model_wf M)
    (k : BvBitwiseElimKind) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvBitwiseElimProgram k x y) = Term.Bool ->
    eo_interprets M (bvBitwiseElimProgram k x y) true := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvBitwiseElimProgram_eq_term_of_type_bool k x y hXTrans hYTrans hResultTy
  have hTermTy :
      __eo_typeof (bvBitwiseElimTerm k x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_bitwise_elim_term M hM k x y hXTrans hYTrans hTermTy
