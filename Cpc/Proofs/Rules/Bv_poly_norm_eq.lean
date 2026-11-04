module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
  __eo_requires x y z ≠ Term.Stuck ->
  x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    have hNe : native_teq x y = false := by
      simp [native_teq, hxy]
    simp [__eo_requires, hNe, native_ite] at hReq

private theorem eo_requires_body_ne_stuck_of_ne_stuck
    {x y z : Term} :
  __eo_requires x y z ≠ Term.Stuck ->
  z ≠ Term.Stuck := by
  intro hReq
  have hxy : x = y := eo_requires_arg_eq_of_ne_stuck hReq
  by_cases hxSt : x = Term.Stuck
  · subst x
    subst y
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at hReq
  · intro hz
    subst z
    have hReqSt : __eo_requires x y Term.Stuck = Term.Stuck := by
      simp [__eo_requires, hxy, native_teq, native_ite, native_not,
        SmtEval.native_not]
    exact hReq hReqSt

private theorem eo_and_true
    {x y : Term} :
  __eo_and x y = Term.Boolean true ->
  x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

private theorem eo_eq_true_eq
    {x y : Term} :
  __eo_eq x y = Term.Boolean true ->
  x = y := by
  intro h
  by_cases hxSt : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  by_cases hySt : y = Term.Stuck
  · subst y
    simp [__eo_eq] at h
  have hyx : y = x := by
    simpa [__eo_eq, hxSt, hySt, native_teq] using h
  exact hyx.symm

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem nat_coprime_two_of_mod_eq_one (n : Nat) (h : n % 2 = 1) :
    Nat.Coprime 2 n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [Nat.gcd_rec]
  rw [h]
  rfl

private theorem int_toNat_mod_two_of_nonneg {c : Int}
    (hc : 0 <= c) (hOdd : c % 2 = 1) :
    c.toNat % 2 = 1 := by
  have h := Int.toNat_emod (x := c) (y := 2) hc (by decide : 0 <= (2 : Int))
  rw [hOdd] at h
  exact h.symm

private theorem odd_mul_mod_pow2_eq_zero_imp_zero
    (w : Nat) {c x : Int}
    (hc0 : 0 <= c) (hx0 : 0 <= x)
    (hxLt : x < native_int_pow2 (native_nat_to_int w))
    (hcOdd : c % 2 = 1)
    (hMul : (c * x) % native_int_pow2 (native_nat_to_int w) = 0) :
    x = 0 := by
  let mNat : Nat := 2 ^ w
  have hDvdInt : (mNat : Int) ∣ c * x := by
    have hDvd := Int.dvd_of_emod_eq_zero hMul
    simpa [mNat, native_int_pow2_nat] using hDvd
  have hDvdNatMul : mNat ∣ c.toNat * x.toNat := by
    rw [← Int.ofNat_dvd]
    have hCast : ((c.toNat * x.toNat : Nat) : Int) = c * x := by
      simp [Int.toNat_of_nonneg hc0, Int.toNat_of_nonneg hx0]
    simpa [hCast] using hDvdInt
  have hcNatOdd : c.toNat % 2 = 1 := int_toNat_mod_two_of_nonneg hc0 hcOdd
  have hCop2 : Nat.Coprime 2 c.toNat := nat_coprime_two_of_mod_eq_one c.toNat hcNatOdd
  have hCop : Nat.Coprime mNat c.toNat := Nat.Coprime.pow_left w hCop2
  have hDvdXNat : mNat ∣ x.toNat := hCop.dvd_of_dvd_mul_left hDvdNatMul
  have hxNatLt : x.toNat < mNat := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hx0]
    simpa [mNat, native_int_pow2_nat] using hxLt
  have hxNatZero : x.toNat = 0 := Nat.eq_zero_of_dvd_of_lt hDvdXNat hxNatLt
  rw [← Int.toNat_of_nonneg hx0, hxNatZero]
  rfl

private theorem bvsub_payload_zero_iff_eq
    (w : Nat) {n1 n2 : Int}
    (h1lo : 0 <= n1) (h1hi : n1 < native_int_pow2 (native_nat_to_int w))
    (h2lo : 0 <= n2) (h2hi : n2 < native_int_pow2 (native_nat_to_int w)) :
    native_mod_total (native_zplus n1
      (native_mod_total (native_zneg n2) (native_int_pow2 (native_nat_to_int w))))
      (native_int_pow2 (native_nat_to_int w)) = 0 ↔ n1 = n2 := by
  let m := native_int_pow2 (native_nat_to_int w)
  have hReduce : (n1 + ((-n2) % m)) % m = (n1 - n2) % m := by
    calc
      (n1 + ((-n2) % m)) % m = (((-n2) % m) + n1) % m := by rw [Int.add_comm]
      _ = ((-n2) + n1) % m := Int.emod_add_emod (-n2) m n1
      _ = (n1 + -n2) % m := by rw [Int.add_comm]
      _ = (n1 - n2) % m := by rfl
  have hEqMod : (n1 % m = n2 % m ↔ (n1 - n2) % m = 0) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero
  have h1mod : n1 % m = n1 := by simpa [m] using Int.emod_eq_of_lt h1lo h1hi
  have h2mod : n2 % m = n2 := by simpa [m] using Int.emod_eq_of_lt h2lo h2hi
  rw [h1mod, h2mod] at hEqMod
  change (n1 + ((-n2) % m)) % m = 0 ↔ n1 = n2
  rw [hReduce]
  exact hEqMod.symm

private theorem native_veq_binary_same_width_eq_of_iff
    {w n1 n2 m1 m2 : native_Int}
    (hiff : (n1 = n2 ↔ m1 = m2)) :
    native_veq (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      native_veq (SmtValue.Binary w m1) (SmtValue.Binary w m2) := by
  by_cases hn : n1 = n2
  · have hm : m1 = m2 := hiff.mp hn
    subst n2
    subst m2
    simp [native_veq]
  · have hm : m1 ≠ m2 := by
      intro h
      exact hn (hiff.mpr h)
    simp [native_veq, hn, hm]

private theorem binary_literal_of_to_z_bitvec_type
    {t : Term} {w : native_Nat} {n : native_Int}
    (hToZ : __eo_to_z t = Term.Numeral n)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    t = Term.Binary (native_nat_to_int w) n := by
  cases t <;> try simp [__eo_to_z] at hToZ
  case Numeral z =>
      rw [show __eo_to_smt (Term.Numeral z) = SmtTerm.Numeral z by rfl] at hTy
      rw [__smtx_typeof.eq_2] at hTy
      cases hTy
  case Rational q =>
      rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl] at hTy
      rw [__smtx_typeof.eq_3] at hTy
      cases hTy
  case String s =>
      rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl] at hTy
      rw [__smtx_typeof.eq_4] at hTy
      cases hValid : native_string_valid s <;>
        simp [native_ite, hValid] at hTy
  case Binary bw payload =>
      subst payload
      have hTyBin : __smtx_typeof (SmtTerm.Binary bw n) = SmtType.BitVec w := by
        rw [show __eo_to_smt (Term.Binary bw n) = SmtTerm.Binary bw n by rfl] at hTy
        exact hTy
      have hNN : __smtx_typeof (SmtTerm.Binary bw n) ≠ SmtType.None := by
        rw [hTyBin]
        simp
      have hCanon := TranslationProofs.smtx_typeof_binary_of_non_none bw n hNN
      have hWidthInfo := TranslationProofs.smtx_binary_well_formed_of_non_none bw n hNN
      have hWidthNat : native_int_to_nat bw = w := by
        rw [hTyBin] at hCanon
        cases hCanon
        rfl
      have hBwNonneg : 0 <= bw := by
        simpa [SmtEval.native_zleq] using hWidthInfo.1
      have hBw : bw = native_nat_to_int w := by
        have hInt : (Int.ofNat (Int.toNat bw) : Int) = bw :=
          Int.toNat_of_nonneg hBwNonneg
        simp [native_int_to_nat, SmtEval.native_int_to_nat] at hWidthNat
        simp [hWidthNat] at hInt
        exact hInt.symm
      subst bw
      rfl

private theorem odd_to_z_of_zmod_to_z
    {t : Term}
    (hOdd : __eo_zmod (__eo_to_z t) (Term.Numeral 2) = Term.Numeral 1) :
    ∃ n : native_Int, __eo_to_z t = Term.Numeral n ∧ n % 2 = 1 := by
  cases hz : __eo_to_z t
  all_goals
    rw [hz] at hOdd
    simp [__eo_zmod, native_ite, SmtEval.native_zeq] at hOdd
  case Numeral z =>
    exact ⟨z, rfl, by simpa [SmtEval.native_mod_total] using hOdd⟩

private theorem binary_literal_odd_of_zmod_to_z_bitvec_type
    {t : Term} {w : native_Nat}
    (hOdd : __eo_zmod (__eo_to_z t) (Term.Numeral 2) = Term.Numeral 1)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : native_Int, t = Term.Binary (native_nat_to_int w) n ∧ n % 2 = 1 := by
  rcases odd_to_z_of_zmod_to_z hOdd with ⟨n, hToZ, hnOdd⟩
  exact ⟨n, binary_literal_of_to_z_bitvec_type hToZ hTy, hnOdd⟩

private theorem binary_literal_range_of_bitvec_type
    {w : native_Nat} {n : native_Int}
    (hTy :
      __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) n) =
        SmtType.BitVec w) :
    0 <= n ∧ n < native_int_pow2 (native_nat_to_int w) := by
  have hNN : __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) n) ≠ SmtType.None := by
    rw [hTy]
    simp
  have hWF :=
    TranslationProofs.smtx_binary_well_formed_of_non_none
      (native_nat_to_int w) n hNN
  exact Smtm.bitvec_payload_range_of_canonical hWF.1 hWF.2

private theorem model_eval_bitvec_payload
    (M : SmtModel) (hM : model_wf M) (t : Term) (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary (native_nat_to_int w) n ∧
      0 <= n ∧ n < native_int_pow2 (native_nat_to_int w) := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.BitVec w := by
    simpa [hTy] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNN
  rcases Smtm.bitvec_value_canonical hEvalTy with ⟨n, hv⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    exact Smtm.bitvec_width_nonneg (by simpa [hv] using hEvalTy)
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true := by
    exact Smtm.bitvec_payload_canonical (by simpa [hv] using hEvalTy)
  have hRange := Smtm.bitvec_payload_range_of_canonical hWidth hMod
  exact ⟨n, hv, hRange⟩

private theorem bvmul_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x) =
      SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x) by rfl] at hTy
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvmul)
      (show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_49]) hNN with ⟨w', hy, hx⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_49]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hy, hx, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hy, hx⟩

private theorem bvsub_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x) =
      SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x) by rfl] at hTy
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvsub)
      (show __smtx_typeof (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_52]) hNN with ⟨w', hy, hx⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show __smtx_typeof (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_52]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hy, hx, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hy, hx⟩

private theorem bvmul_info_of_non_none (y x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) ≠
      SmtType.None ->
    ∃ w : native_Nat,
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
        SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hNN0
  have hNN : term_has_non_none_type (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x) =
      SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x) by rfl]
    exact hNN0
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvmul)
      (show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_49]) hNN with ⟨w, hy, hx⟩
  have hResSmt :
      __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [__smtx_typeof.eq_49]
    simp [__smtx_typeof_bv_op_2, hy, hx, native_ite, native_nateq,
      SmtEval.native_nateq]
  have hRes :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x) =
      SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x) by rfl]
    exact hResSmt
  exact ⟨w, hRes, hy, hx⟩

private theorem prog_bv_poly_norm_eq_eq_arg_of_typeof_bool_shape
    (xb1 xb2 yb1 yb2 cx xb1p xb2p one cy yb1p yb2p one2 : Term) :
  __eo_typeof
      (__eo_prog_bv_poly_norm_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2))))) =
      Term.Bool ->
  __eo_prog_bv_poly_norm_eq
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))
      (Proof.pf
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2)))) =
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2)) := by
  intro hTy
  have hProg :
      __eo_prog_bv_poly_norm_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2)))) ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  let guardSame :=
    __eo_and
      (__eo_and (__eo_and (__eo_and (__eo_eq xb1 xb1p) (__eo_eq xb2 xb2p))
        (__eo_eq yb1 yb1p)) (__eo_eq yb2 yb2p))
      (__eo_eq one one2)
  let restOne :=
    __eo_requires (__eo_to_z one) (Term.Numeral 1)
      (__eo_requires (__eo_zmod (__eo_to_z cx) (Term.Numeral 2)) (Term.Numeral 1)
        (__eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))))
  have hOuter : __eo_requires guardSame (Term.Boolean true) restOne ≠ Term.Stuck := by
    simpa [guardSame, restOne, __eo_and, __eo_eq, __eo_prog_bv_poly_norm_eq, __eo_requires, __eo_to_z, __eo_zmod] using hProg
  have hGuardSame : guardSame = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hOuter
  have hRestOne : restOne ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hOuter
  have hParts0 := eo_and_true hGuardSame
  have hOneSame : one = one2 := eo_eq_true_eq hParts0.2
  have hParts1 := eo_and_true hParts0.1
  have hy2 : yb2 = yb2p := eo_eq_true_eq hParts1.2
  have hParts2 := eo_and_true hParts1.1
  have hy1 : yb1 = yb1p := eo_eq_true_eq hParts2.2
  have hParts3 := eo_and_true hParts2.1
  have hx1 : xb1 = xb1p := eo_eq_true_eq hParts3.1
  have hx2 : xb2 = xb2p := eo_eq_true_eq hParts3.2
  subst one2
  subst yb2p
  subst yb1p
  subst xb1p
  subst xb2p
  have hOne : __eo_to_z one = Term.Numeral 1 :=
    eo_requires_arg_eq_of_ne_stuck hRestOne
  have hRestCx :
      __eo_requires (__eo_zmod (__eo_to_z cx) (Term.Numeral 2)) (Term.Numeral 1)
        (__eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestOne
  have hCxOdd : __eo_zmod (__eo_to_z cx) (Term.Numeral 2) = Term.Numeral 1 :=
    eo_requires_arg_eq_of_ne_stuck hRestCx
  have hRestCy :
      __eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2)) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestCx
  have hCyOdd : __eo_zmod (__eo_to_z cy) (Term.Numeral 2) = Term.Numeral 1 :=
    eo_requires_arg_eq_of_ne_stuck hRestCy
  simp [__eo_prog_bv_poly_norm_eq, __eo_requires, guardSame, hGuardSame, hOne, hCxOdd,
    hCyOdd, native_teq, native_ite, native_not, SmtEval.native_not]

private theorem prog_bv_poly_norm_eq_eq_arg_of_typeof_bool
    (a1 prem : Term) :
  __eo_typeof (__eo_prog_bv_poly_norm_eq a1 (Proof.pf prem)) = Term.Bool ->
  __eo_prog_bv_poly_norm_eq a1 (Proof.pf prem) = a1 := by
  intro hTy
  have hProg : __eo_prog_bv_poly_norm_eq a1 (Proof.pf prem) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f right =>
      cases f with
      | Apply eqHead left =>
          cases eqHead with
          | UOp op =>
              cases op <;> (try (exfalso; apply hProg; rfl))
              case eq =>
                cases left with
                | Apply lf xb2 =>
                    cases lf with
                    | Apply eqHead2 xb1 =>
                        cases eqHead2 with
                        | UOp op2 =>
                            cases op2 <;> (try (exfalso; apply hProg; rfl))
                            case eq =>
                              cases right with
                              | Apply rf yb2 =>
                                  cases rf with
                                  | Apply eqHead3 yb1 =>
                                      cases eqHead3 with
                                      | UOp op3 =>
                                          cases op3 <;> (try (exfalso; apply hProg; rfl))
                                          case eq =>
                                            cases prem with
                                            | Apply pf pright =>
                                                cases pf with
                                                | Apply peqHead pleft =>
                                                    cases peqHead with
                                                    | UOp pop =>
                                                        cases pop <;> (try (exfalso; apply hProg; rfl))
                                                        case eq =>
                                                          cases pleft with
                                                          | Apply plf plarg =>
                                                              cases plf with
                                                              | Apply pmulHead cx =>
                                                                  cases pmulHead with
                                                                  | UOp pmulOp =>
                                                                      cases pmulOp <;> (try (exfalso; apply hProg; rfl))
                                                                      case bvmul =>
                                                                        cases plarg with
                                                                        | Apply pxf one =>
                                                                            cases pxf with
                                                                            | Apply pxHead xdiff =>
                                                                                cases pxHead with
                                                                                | UOp pxOp =>
                                                                                    cases pxOp <;> (try (exfalso; apply hProg; rfl))
                                                                                    case bvmul =>
                                                                                      cases xdiff with
                                                                                      | Apply xsf xb2p =>
                                                                                          cases xsf with
                                                                                          | Apply xsubHead xb1p =>
                                                                                              cases xsubHead with
                                                                                              | UOp xsubOp =>
                                                                                                  cases xsubOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                  case bvsub =>
                                                                                                    cases pright with
                                                                                                    | Apply prf prarg =>
                                                                                                        cases prf with
                                                                                                        | Apply prmulHead cy =>
                                                                                                            cases prmulHead with
                                                                                                            | UOp prmulOp =>
                                                                                                                cases prmulOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                                case bvmul =>
                                                                                                                  cases prarg with
                                                                                                                  | Apply pyf one2 =>
                                                                                                                      cases pyf with
                                                                                                                      | Apply pyHead ydiff =>
                                                                                                                          cases pyHead with
                                                                                                                          | UOp pyOp =>
                                                                                                                              cases pyOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                                              case bvmul =>
                                                                                                                                cases ydiff with
                                                                                                                                | Apply ysf yb2p =>
                                                                                                                                    cases ysf with
                                                                                                                                    | Apply ysubHead yb1p =>
                                                                                                                                        cases ysubHead with
                                                                                                                                        | UOp ysubOp =>
                                                                                                                                            cases ysubOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                                                            case bvsub =>
                                                                                                                                              exact
                                                                                                                                                prog_bv_poly_norm_eq_eq_arg_of_typeof_bool_shape
                                                                                                                                                  xb1 xb2 yb1 yb2 cx xb1p xb2p one cy yb1p yb2p one2 hTy
                                                                                                                                        | _ => exact False.elim (hProg (by rfl))
                                                                                                                                    | _ => exact False.elim (hProg (by rfl))
                                                                                                                                | _ => exact False.elim (hProg (by rfl))
                                                                                                                          | _ => exact False.elim (hProg (by rfl))
                                                                                                                      | _ => exact False.elim (hProg (by rfl))
                                                                                                                  | _ => exact False.elim (hProg (by rfl))
                                                                                                            | _ => exact False.elim (hProg (by rfl))
                                                                                                        | _ => exact False.elim (hProg (by rfl))
                                                                                                    | _ => exact False.elim (hProg (by rfl))
                                                                                              | _ => exact False.elim (hProg (by rfl))
                                                                                          | _ => exact False.elim (hProg (by rfl))
                                                                                      | _ => exact False.elim (hProg (by rfl))
                                                                                | _ => exact False.elim (hProg (by rfl))
                                                                            | _ => exact False.elim (hProg (by rfl))
                                                                        | _ => exact False.elim (hProg (by rfl))
                                                                  | _ => exact False.elim (hProg (by rfl))
                                                              | _ => exact False.elim (hProg (by rfl))
                                                          | _ => exact False.elim (hProg (by rfl))
                                                    | _ => exact False.elim (hProg (by rfl))
                                                | _ => exact False.elim (hProg (by rfl))
                                            | _ => exact False.elim (hProg (by rfl))
                                      | _ => exact False.elim (hProg (by rfl))
                                  | _ => exact False.elim (hProg (by rfl))
                              | _ => exact False.elim (hProg (by rfl))
                        | _ => exact False.elim (hProg (by rfl))
                    | _ => exact False.elim (hProg (by rfl))
                | _ => exact False.elim (hProg (by rfl))
          | _ => exact False.elim (hProg (by rfl))
      | _ => exact False.elim (hProg (by rfl))
  | _ => exact False.elim (hProg (by rfl))

theorem typed___eo_prog_bv_poly_norm_eq_impl
    (a1 prem : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_bv_poly_norm_eq a1 (Proof.pf prem)) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_bv_poly_norm_eq a1 (Proof.pf prem)) := by
  intro hA1Trans hResultTy
  have hProgEq :
      __eo_prog_bv_poly_norm_eq a1 (Proof.pf prem) = a1 :=
    prog_bv_poly_norm_eq_eq_arg_of_typeof_bool a1 prem hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem facts___eo_prog_bv_poly_norm_eq_impl_shape
    (M : SmtModel) (hM : model_wf M)
    (xb1 xb2 yb1 yb2 cx xb1p xb2p one cy yb1p yb2p one2 : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2)) ->
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2))) ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2))) true ->
  __eo_typeof
      (__eo_prog_bv_poly_norm_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2))))) =
    Term.Bool ->
  eo_interprets M
      (__eo_prog_bv_poly_norm_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2))))) true := by
  intro hA1Trans hPremBool hPremTrue hResultTy
  have hProgEq :=
    prog_bv_poly_norm_eq_eq_arg_of_typeof_bool_shape
      xb1 xb2 yb1 yb2 cx xb1p xb2p one cy yb1p yb2p one2 hResultTy
  have hProg :
      __eo_prog_bv_poly_norm_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1p) xb2p)) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1p) yb2p)) one2)))) ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  let guardSame :=
    __eo_and
      (__eo_and (__eo_and (__eo_and (__eo_eq xb1 xb1p) (__eo_eq xb2 xb2p))
        (__eo_eq yb1 yb1p)) (__eo_eq yb2 yb2p))
      (__eo_eq one one2)
  let restOne :=
    __eo_requires (__eo_to_z one) (Term.Numeral 1)
      (__eo_requires (__eo_zmod (__eo_to_z cx) (Term.Numeral 2)) (Term.Numeral 1)
        (__eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))))
  have hOuter : __eo_requires guardSame (Term.Boolean true) restOne ≠ Term.Stuck := by
    simpa [guardSame, restOne, __eo_and, __eo_eq, __eo_prog_bv_poly_norm_eq, __eo_requires, __eo_to_z, __eo_zmod] using hProg
  have hGuardSame : guardSame = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hOuter
  have hRestOne : restOne ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hOuter
  have hParts0 := eo_and_true hGuardSame
  have hOneSame : one = one2 := eo_eq_true_eq hParts0.2
  have hParts1 := eo_and_true hParts0.1
  have hy2 : yb2 = yb2p := eo_eq_true_eq hParts1.2
  have hParts2 := eo_and_true hParts1.1
  have hy1 : yb1 = yb1p := eo_eq_true_eq hParts2.2
  have hParts3 := eo_and_true hParts2.1
  have hx1 : xb1 = xb1p := eo_eq_true_eq hParts3.1
  have hx2 : xb2 = xb2p := eo_eq_true_eq hParts3.2
  subst one2
  subst yb2p
  subst yb1p
  subst xb1p
  subst xb2p
  have hOne : __eo_to_z one = Term.Numeral 1 :=
    eo_requires_arg_eq_of_ne_stuck hRestOne
  have hRestCx :
      __eo_requires (__eo_zmod (__eo_to_z cx) (Term.Numeral 2)) (Term.Numeral 1)
        (__eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2))) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestOne
  have hCxOdd : __eo_zmod (__eo_to_z cx) (Term.Numeral 2) = Term.Numeral 1 :=
    eo_requires_arg_eq_of_ne_stuck hRestCx
  have hRestCy :
      __eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2)) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestCx
  have hCyOdd : __eo_zmod (__eo_to_z cy) (Term.Numeral 2) = Term.Numeral 1 :=
    eo_requires_arg_eq_of_ne_stuck hRestCy
  let eqX := Term.Apply (Term.Apply (Term.UOp UserOp.eq) xb1) xb2
  let eqY := Term.Apply (Term.Apply (Term.UOp UserOp.eq) yb1) yb2
  let diffX := Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) xb1) xb2
  let diffY := Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) yb1) yb2
  let innerX := Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) diffX) one
  let innerY := Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) diffY) one
  let lhs := Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cx) innerX
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) cy) innerY
  have hPremEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
    simpa [lhs, rhs, innerX, innerY, diffX, diffY] using hPremBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type lhs rhs hPremEqBool with
    ⟨hLhsRhsTy, hLhsNN⟩
  rcases bvmul_info_of_non_none cx innerX (by simpa [lhs] using hLhsNN) with
    ⟨w, hLhsTy, hCxTy, hInnerXTy⟩
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.BitVec w := by
    rw [← hLhsRhsTy]
    exact hLhsTy
  rcases bvmul_args_of_bitvec_type cy innerY w hRhsTy with ⟨hCyTy, hInnerYTy⟩
  rcases bvmul_args_of_bitvec_type diffX one w hInnerXTy with ⟨hDiffXTy, hOneTy⟩
  rcases bvmul_args_of_bitvec_type diffY one w hInnerYTy with ⟨hDiffYTy, _hOneTy2⟩
  rcases bvsub_args_of_bitvec_type xb1 xb2 w hDiffXTy with ⟨hXb1Ty, hXb2Ty⟩
  rcases bvsub_args_of_bitvec_type yb1 yb2 w hDiffYTy with ⟨hYb1Ty, hYb2Ty⟩
  have hOneLit : one = Term.Binary (native_nat_to_int w) 1 :=
    binary_literal_of_to_z_bitvec_type hOne hOneTy
  rcases binary_literal_odd_of_zmod_to_z_bitvec_type hCxOdd hCxTy with
    ⟨ncx, hCxLit, hNcxOdd⟩
  rcases binary_literal_odd_of_zmod_to_z_bitvec_type hCyOdd hCyTy with
    ⟨ncy, hCyLit, hNcyOdd⟩
  have hCxTyBin :
      __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) ncx) = SmtType.BitVec w := by
    rw [hCxLit] at hCxTy
    exact hCxTy
  have hCyTyBin :
      __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) ncy) = SmtType.BitVec w := by
    rw [hCyLit, __eo_to_smt] at hCyTy
    simpa using hCyTy
  have hCxRange := binary_literal_range_of_bitvec_type hCxTyBin
  have hCyRange := binary_literal_range_of_bitvec_type hCyTyBin
  have hCxEval :
      __smtx_model_eval M (__eo_to_smt cx) = SmtValue.Binary (native_nat_to_int w) ncx := by
    rw [hCxLit]
    rw [show __eo_to_smt (Term.Binary (native_nat_to_int w) ncx) =
      SmtTerm.Binary (native_nat_to_int w) ncx by rfl]
    rw [__smtx_model_eval.eq_5]
  have hCyEval :
      __smtx_model_eval M (__eo_to_smt cy) = SmtValue.Binary (native_nat_to_int w) ncy := by
    rw [hCyLit]
    rw [show __eo_to_smt (Term.Binary (native_nat_to_int w) ncy) =
      SmtTerm.Binary (native_nat_to_int w) ncy by rfl]
    rw [__smtx_model_eval.eq_5]
  have hOneEval :
      __smtx_model_eval M (__eo_to_smt one) = SmtValue.Binary (native_nat_to_int w) 1 := by
    rw [hOneLit]
    rw [show __eo_to_smt (Term.Binary (native_nat_to_int w) 1) =
      SmtTerm.Binary (native_nat_to_int w) 1 by rfl]
    rw [__smtx_model_eval.eq_5]
  rcases model_eval_bitvec_payload M hM xb1 w hXb1Ty with ⟨nxb1, hXb1Eval, hXb1Range⟩
  rcases model_eval_bitvec_payload M hM xb2 w hXb2Ty with ⟨nxb2, hXb2Eval, hXb2Range⟩
  rcases model_eval_bitvec_payload M hM yb1 w hYb1Ty with ⟨nyb1, hYb1Eval, hYb1Range⟩
  rcases model_eval_bitvec_payload M hM yb2 w hYb2Ty with ⟨nyb2, hYb2Eval, hYb2Range⟩
  rcases model_eval_bitvec_payload M hM diffX w hDiffXTy with ⟨ndx, hDiffXEval, hDxRange⟩
  rcases model_eval_bitvec_payload M hM diffY w hDiffYTy with ⟨ndy, hDiffYEval, hDyRange⟩
  have hDiffXCalc :
      __smtx_model_eval M (__eo_to_smt diffX) =
        SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zplus nxb1
            (native_mod_total (native_zneg nxb2)
              (native_int_pow2 (native_nat_to_int w))))
            (native_int_pow2 (native_nat_to_int w))) := by
    rw [show __eo_to_smt diffX =
      SmtTerm.bvsub (__eo_to_smt xb1) (__eo_to_smt xb2) by rfl]
    rw [__smtx_model_eval.eq_52, hXb1Eval, hXb2Eval]
    rfl
  have hDiffYCalc :
      __smtx_model_eval M (__eo_to_smt diffY) =
        SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zplus nyb1
            (native_mod_total (native_zneg nyb2)
              (native_int_pow2 (native_nat_to_int w))))
            (native_int_pow2 (native_nat_to_int w))) := by
    rw [show __eo_to_smt diffY =
      SmtTerm.bvsub (__eo_to_smt yb1) (__eo_to_smt yb2) by rfl]
    rw [__smtx_model_eval.eq_52, hYb1Eval, hYb2Eval]
    rfl
  have hDxPayload :
      ndx =
        native_mod_total (native_zplus nxb1
          (native_mod_total (native_zneg nxb2)
            (native_int_pow2 (native_nat_to_int w))))
          (native_int_pow2 (native_nat_to_int w)) := by
    rw [hDiffXEval] at hDiffXCalc
    injection hDiffXCalc with _ hPayload
  have hDyPayload :
      ndy =
        native_mod_total (native_zplus nyb1
          (native_mod_total (native_zneg nyb2)
            (native_int_pow2 (native_nat_to_int w))))
          (native_int_pow2 (native_nat_to_int w)) := by
    rw [hDiffYEval] at hDiffYCalc
    injection hDiffYCalc with _ hPayload
  have hDxZeroIff : ndx = 0 ↔ nxb1 = nxb2 := by
    rw [hDxPayload]
    exact bvsub_payload_zero_iff_eq w
      hXb1Range.1 hXb1Range.2 hXb2Range.1 hXb2Range.2
  have hDyZeroIff : ndy = 0 ↔ nyb1 = nyb2 := by
    rw [hDyPayload]
    exact bvsub_payload_zero_iff_eq w
      hYb1Range.1 hYb1Range.2 hYb2Range.1 hYb2Range.2
  have hInnerXEval :
      __smtx_model_eval M (__eo_to_smt innerX) =
        SmtValue.Binary (native_nat_to_int w) ndx := by
    have hMul :
        __smtx_model_eval M (__eo_to_smt innerX) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total (native_zmult ndx 1)
              (native_int_pow2 (native_nat_to_int w))) := by
      rw [show __eo_to_smt innerX =
        SmtTerm.bvmul (__eo_to_smt diffX) (__eo_to_smt one) by rfl]
      rw [__smtx_model_eval.eq_49, hDiffXEval, hOneEval]
      rfl
    have hOneMul :
        native_mod_total (native_zmult ndx 1) (native_int_pow2 (native_nat_to_int w)) =
          ndx := by
      simpa [SmtEval.native_zmult, SmtEval.native_mod_total] using
        Int.emod_eq_of_lt hDxRange.1 hDxRange.2
    rw [hMul, hOneMul]
  have hInnerYEval :
      __smtx_model_eval M (__eo_to_smt innerY) =
        SmtValue.Binary (native_nat_to_int w) ndy := by
    have hMul :
        __smtx_model_eval M (__eo_to_smt innerY) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total (native_zmult ndy 1)
              (native_int_pow2 (native_nat_to_int w))) := by
      rw [show __eo_to_smt innerY =
        SmtTerm.bvmul (__eo_to_smt diffY) (__eo_to_smt one) by rfl]
      rw [__smtx_model_eval.eq_49, hDiffYEval, hOneEval]
      rfl
    have hOneMul :
        native_mod_total (native_zmult ndy 1) (native_int_pow2 (native_nat_to_int w)) =
          ndy := by
      simpa [SmtEval.native_zmult, SmtEval.native_mod_total] using
        Int.emod_eq_of_lt hDyRange.1 hDyRange.2
    rw [hMul, hOneMul]
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt lhs) =
        SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zmult ncx ndx)
            (native_int_pow2 (native_nat_to_int w))) := by
    rw [show __eo_to_smt lhs =
      SmtTerm.bvmul (__eo_to_smt cx) (__eo_to_smt innerX) by rfl]
    rw [__smtx_model_eval.eq_49, hCxEval, hInnerXEval]
    rfl
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zmult ncy ndy)
            (native_int_pow2 (native_nat_to_int w))) := by
    rw [show __eo_to_smt rhs =
      SmtTerm.bvmul (__eo_to_smt cy) (__eo_to_smt innerY) by rfl]
    rw [__smtx_model_eval.eq_49, hCyEval, hInnerYEval]
    rfl
  have hPremRel := RuleProofs.eo_interprets_eq_rel M lhs rhs (by simpa [lhs, rhs] using hPremTrue)
  rw [hLhsEval, hRhsEval] at hPremRel
  have hProdValEq :
      SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zmult ncx ndx)
            (native_int_pow2 (native_nat_to_int w))) =
        SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zmult ncy ndy)
            (native_int_pow2 (native_nat_to_int w))) := by
    exact (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBin, _hReg⟩
      cases hBin)).mp hPremRel
  have hProdEq :
      native_mod_total (native_zmult ncx ndx) (native_int_pow2 (native_nat_to_int w)) =
        native_mod_total (native_zmult ncy ndy) (native_int_pow2 (native_nat_to_int w)) := by
    injection hProdValEq with _ hPayload
  have hZeroY_of_X : ndx = 0 -> ndy = 0 := by
    intro hdx0
    have hLeftZero :
        native_mod_total (native_zmult ncx ndx)
          (native_int_pow2 (native_nat_to_int w)) = 0 := by
      rw [hdx0]
      simp [SmtEval.native_zmult, SmtEval.native_mod_total]
    have hRightZero :
        native_mod_total (native_zmult ncy ndy)
          (native_int_pow2 (native_nat_to_int w)) = 0 := by
      rw [← hProdEq]
      exact hLeftZero
    exact odd_mul_mod_pow2_eq_zero_imp_zero w hCyRange.1 hDyRange.1 hDyRange.2
      hNcyOdd hRightZero
  have hZeroX_of_Y : ndy = 0 -> ndx = 0 := by
    intro hdy0
    have hRightZero :
        native_mod_total (native_zmult ncy ndy)
          (native_int_pow2 (native_nat_to_int w)) = 0 := by
      rw [hdy0]
      simp [SmtEval.native_zmult, SmtEval.native_mod_total]
    have hLeftZero :
        native_mod_total (native_zmult ncx ndx)
          (native_int_pow2 (native_nat_to_int w)) = 0 := by
      rw [hProdEq]
      exact hRightZero
    exact odd_mul_mod_pow2_eq_zero_imp_zero w hCxRange.1 hDxRange.1 hDxRange.2
      hNcxOdd hLeftZero
  have hEqIff : nxb1 = nxb2 ↔ nyb1 = nyb2 := by
    constructor
    · intro hxEq
      exact hDyZeroIff.mp (hZeroY_of_X (hDxZeroIff.mpr hxEq))
    · intro hyEq
      exact hDxZeroIff.mp (hZeroX_of_Y (hDyZeroIff.mpr hyEq))
  have hEqXEval :
      __smtx_model_eval M (__eo_to_smt eqX) =
        SmtValue.Boolean
          (native_veq (SmtValue.Binary (native_nat_to_int w) nxb1)
            (SmtValue.Binary (native_nat_to_int w) nxb2)) := by
    rw [show __eo_to_smt eqX =
      SmtTerm.eq (__eo_to_smt xb1) (__eo_to_smt xb2) by rfl]
    rw [smtx_eval_eq_term_eq, hXb1Eval, hXb2Eval]
    rfl
  have hEqYEval :
      __smtx_model_eval M (__eo_to_smt eqY) =
        SmtValue.Boolean
          (native_veq (SmtValue.Binary (native_nat_to_int w) nyb1)
            (SmtValue.Binary (native_nat_to_int w) nyb2)) := by
    rw [show __eo_to_smt eqY =
      SmtTerm.eq (__eo_to_smt yb1) (__eo_to_smt yb2) by rfl]
    rw [smtx_eval_eq_term_eq, hYb1Eval, hYb2Eval]
    rfl
  have hEqBool :
      native_veq (SmtValue.Binary (native_nat_to_int w) nxb1)
          (SmtValue.Binary (native_nat_to_int w) nxb2) =
        native_veq (SmtValue.Binary (native_nat_to_int w) nyb1)
          (SmtValue.Binary (native_nat_to_int w) nyb2) :=
    native_veq_binary_same_width_eq_of_iff hEqIff
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt eqX))
        (__smtx_model_eval M (__eo_to_smt eqY)) := by
    rw [hEqXEval, hEqYEval]
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hEqBool]
    cases native_veq (SmtValue.Binary (native_nat_to_int w) nyb1)
        (SmtValue.Binary (native_nat_to_int w) nyb2) <;>
      simp [__smtx_model_eval_eq, native_veq]
  have hOutBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) eqX) eqY) := by
    have hProgBool :=
      typed___eo_prog_bv_poly_norm_eq_impl
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) eqX) eqY)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs)
        (by simpa [eqX, eqY] using hA1Trans)
        (by simpa [eqX, eqY, lhs, rhs, innerX, innerY, diffX, diffY] using hResultTy)
    simpa [hProgEq, eqX, eqY, lhs, rhs, innerX, innerY, diffX, diffY] using hProgBool
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M eqX eqY hOutBool hRel

private theorem facts___eo_prog_bv_poly_norm_eq_impl
    (M : SmtModel) (hM : model_wf M) (a1 prem : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  RuleProofs.eo_has_bool_type prem ->
  eo_interprets M prem true ->
  __eo_typeof (__eo_prog_bv_poly_norm_eq a1 (Proof.pf prem)) = Term.Bool ->
  eo_interprets M (__eo_prog_bv_poly_norm_eq a1 (Proof.pf prem)) true := by
  intro hA1Trans hPremBool hPremTrue hResultTy
  have hProg : __eo_prog_bv_poly_norm_eq a1 (Proof.pf prem) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases a1 with
  | Apply f right =>
      cases f with
      | Apply eqHead left =>
          cases eqHead with
          | UOp op =>
              cases op <;> (try (exfalso; apply hProg; rfl))
              case eq =>
                cases left with
                | Apply lf xb2 =>
                    cases lf with
                    | Apply eqHead2 xb1 =>
                        cases eqHead2 with
                        | UOp op2 =>
                            cases op2 <;> (try (exfalso; apply hProg; rfl))
                            case eq =>
                              cases right with
                              | Apply rf yb2 =>
                                  cases rf with
                                  | Apply eqHead3 yb1 =>
                                      cases eqHead3 with
                                      | UOp op3 =>
                                          cases op3 <;> (try (exfalso; apply hProg; rfl))
                                          case eq =>
                                            cases prem with
                                            | Apply pf pright =>
                                                cases pf with
                                                | Apply peqHead pleft =>
                                                    cases peqHead with
                                                    | UOp pop =>
                                                        cases pop <;> (try (exfalso; apply hProg; rfl))
                                                        case eq =>
                                                          cases pleft with
                                                          | Apply plf plarg =>
                                                              cases plf with
                                                              | Apply pmulHead cx =>
                                                                  cases pmulHead with
                                                                  | UOp pmulOp =>
                                                                      cases pmulOp <;> (try (exfalso; apply hProg; rfl))
                                                                      case bvmul =>
                                                                        cases plarg with
                                                                        | Apply pxf one =>
                                                                            cases pxf with
                                                                            | Apply pxHead xdiff =>
                                                                                cases pxHead with
                                                                                | UOp pxOp =>
                                                                                    cases pxOp <;> (try (exfalso; apply hProg; rfl))
                                                                                    case bvmul =>
                                                                                      cases xdiff with
                                                                                      | Apply xsf xb2p =>
                                                                                          cases xsf with
                                                                                          | Apply xsubHead xb1p =>
                                                                                              cases xsubHead with
                                                                                              | UOp xsubOp =>
                                                                                                  cases xsubOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                  case bvsub =>
                                                                                                    cases pright with
                                                                                                    | Apply prf prarg =>
                                                                                                        cases prf with
                                                                                                        | Apply prmulHead cy =>
                                                                                                            cases prmulHead with
                                                                                                            | UOp prmulOp =>
                                                                                                                cases prmulOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                                case bvmul =>
                                                                                                                  cases prarg with
                                                                                                                  | Apply pyf one2 =>
                                                                                                                      cases pyf with
                                                                                                                      | Apply pyHead ydiff =>
                                                                                                                          cases pyHead with
                                                                                                                          | UOp pyOp =>
                                                                                                                              cases pyOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                                              case bvmul =>
                                                                                                                                cases ydiff with
                                                                                                                                | Apply ysf yb2p =>
                                                                                                                                    cases ysf with
                                                                                                                                    | Apply ysubHead yb1p =>
                                                                                                                                        cases ysubHead with
                                                                                                                                        | UOp ysubOp =>
                                                                                                                                            cases ysubOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                                                            case bvsub =>
                                                                                                                                              exact
                                                                                                                                                facts___eo_prog_bv_poly_norm_eq_impl_shape
                                                                                                                                                  M hM xb1 xb2 yb1 yb2 cx xb1p xb2p one cy yb1p yb2p one2
                                                                                                                                                  hA1Trans hPremBool hPremTrue hResultTy
                                                                                                                                        | _ => exact False.elim (hProg (by rfl))
                                                                                                                                    | _ => exact False.elim (hProg (by rfl))
                                                                                                                                | _ => exact False.elim (hProg (by rfl))
                                                                                                                          | _ => exact False.elim (hProg (by rfl))
                                                                                                                      | _ => exact False.elim (hProg (by rfl))
                                                                                                                  | _ => exact False.elim (hProg (by rfl))
                                                                                                            | _ => exact False.elim (hProg (by rfl))
                                                                                                        | _ => exact False.elim (hProg (by rfl))
                                                                                                    | _ => exact False.elim (hProg (by rfl))
                                                                                              | _ => exact False.elim (hProg (by rfl))
                                                                                          | _ => exact False.elim (hProg (by rfl))
                                                                                      | _ => exact False.elim (hProg (by rfl))
                                                                                | _ => exact False.elim (hProg (by rfl))
                                                                            | _ => exact False.elim (hProg (by rfl))
                                                                        | _ => exact False.elim (hProg (by rfl))
                                                                  | _ => exact False.elim (hProg (by rfl))
                                                              | _ => exact False.elim (hProg (by rfl))
                                                          | _ => exact False.elim (hProg (by rfl))
                                                    | _ => exact False.elim (hProg (by rfl))
                                                | _ => exact False.elim (hProg (by rfl))
                                            | _ => exact False.elim (hProg (by rfl))
                                      | _ => exact False.elim (hProg (by rfl))
                                  | _ => exact False.elim (hProg (by rfl))
                              | _ => exact False.elim (hProg (by rfl))
                        | _ => exact False.elim (hProg (by rfl))
                    | _ => exact False.elim (hProg (by rfl))
                | _ => exact False.elim (hProg (by rfl))
          | _ => exact False.elim (hProg (by rfl))
      | _ => exact False.elim (hProg (by rfl))
  | _ => exact False.elim (hProg (by rfl))

public theorem cmd_step_bv_poly_norm_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_poly_norm_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_poly_norm_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_poly_norm_eq args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_poly_norm_eq args premises ≠ Term.Stuck :=
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let A1 := a1
                  let P := __eo_state_proven_nth s n1
                  have hArgsTrans :
                      cArgListTranslationOk (CArgList.cons A1 CArgList.nil) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans
                  have hPremBool : RuleProofs.eo_has_bool_type P :=
                    hPremisesBool P (by simp [P, premiseTermList])
                  change
                    __eo_typeof (__eo_prog_bv_poly_norm_eq A1 (Proof.pf P)) =
                      Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hPremTrue : eo_interprets M P true :=
                      hTrue P (by simp [P, premiseTermList])
                    change eo_interprets M (__eo_prog_bv_poly_norm_eq A1 (Proof.pf P)) true
                    exact facts___eo_prog_bv_poly_norm_eq_impl
                      M hM A1 P hA1Trans hPremBool hPremTrue hResultTy
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_bv_poly_norm_eq A1 (Proof.pf P))
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_bv_poly_norm_eq A1 (Proof.pf P))
                      (typed___eo_prog_bv_poly_norm_eq_impl
                        A1 P hA1Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
