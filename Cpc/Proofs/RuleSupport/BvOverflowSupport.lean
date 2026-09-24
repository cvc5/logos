module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

theorem typeof_extract_bit_of_bv
    (b : Term) (w start : Nat)
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hstart : start < w) :
    __eo_typeof
        (Term.Apply
          (Term.UOp2 UserOp2.extract
            (Term.Numeral (native_nat_to_int start))
            (Term.Numeral (native_nat_to_int start))) b) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  change
    __eo_typeof_extract (Term.UOp UserOp.Int)
      (Term.Numeral (native_nat_to_int start))
      (Term.UOp UserOp.Int)
      (Term.Numeral (native_nat_to_int start))
      (__eo_typeof b) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  rw [hbTy]
  change
    __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_requires
        (__eo_gt (Term.Numeral (native_nat_to_int start))
          (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true)
        (__eo_requires
          (__eo_gt (Term.Numeral (native_nat_to_int w))
            (Term.Numeral (native_nat_to_int start)))
          (Term.Boolean true)
          (__eo_requires
            (__eo_gt
              (__eo_add
                (__eo_add (Term.Numeral (native_nat_to_int start))
                  (__eo_neg (Term.Numeral (native_nat_to_int start))))
                (Term.Numeral 1))
              (Term.Numeral 0))
            (Term.Boolean true)
            (__eo_add
              (__eo_add (Term.Numeral (native_nat_to_int start))
                (__eo_neg (Term.Numeral (native_nat_to_int start))))
              (Term.Numeral 1))))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  have hStartNonneg :
      native_zlt (native_nat_to_int start) (-1 : native_Int) = false := by
    simp only [native_zlt, native_nat_to_int]
    refine decide_eq_false ?_
    show ¬ ((start : Int) < -1)
    omega
  have hStartGtNeg :
      __eo_gt (Term.Numeral (native_nat_to_int start))
        (Term.Numeral (-1 : native_Int)) = Term.Boolean true := by
    have hs0 : (0 : Int) ≤ (start : Int) := Int.natCast_nonneg start
    have hlt : (-1 : Int) < (start : Int) := by omega
    simp [__eo_gt, native_zlt, native_nat_to_int, hlt]
  have hWStart :
      __eo_gt (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int start)) = Term.Boolean true := by
    have hlt : (start : Int) < (w : Int) := by exact_mod_cast hstart
    simp [__eo_gt, native_zlt, native_nat_to_int, hlt]
  have hWidth :
      __eo_add
        (__eo_add (Term.Numeral (native_nat_to_int start))
          (__eo_neg (Term.Numeral (native_nat_to_int start))))
        (Term.Numeral 1) = Term.Numeral 1 := by
    have hEq : (↑start + -↑start + 1 : Int) = 1 := by omega
    simp [__eo_add, __eo_neg, native_zplus, native_zneg, native_nat_to_int, hEq]
  rw [hStartGtNeg, hWStart, hWidth]
  native_decide

theorem nil_bvand_bit :
    __eo_nil (Term.UOp UserOp.bvand)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) =
      Term.Binary 1 1 := by
  native_decide

theorem nil_bvor_bit :
    __eo_nil (Term.UOp UserOp.bvor)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) =
      Term.Binary 1 0 := by
  native_decide

def bv1 (b : Bool) : SmtValue :=
  SmtValue.Binary 1 (if b then (1 : Int) else 0)

theorem native_int_pow2_nat (k : Nat) :
    native_int_pow2 (native_nat_to_int k) = (2 ^ k : Int) := by
  have hnot : ¬ ((k : Int) < 0) :=
    Int.not_lt_of_ge (Int.natCast_nonneg k)
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, hnot]

theorem extract_bit_binary_eval
    (w pa : Int) (i : Nat) (hpa0 : 0 <= pa) :
    __smtx_model_eval_extract (SmtValue.Numeral (native_nat_to_int i))
        (SmtValue.Numeral (native_nat_to_int i)) (SmtValue.Binary w pa) =
      bv1 ((Int.toNat pa).testBit i) := by
  simp [__smtx_model_eval_extract, native_binary_extract, native_zplus,
    native_zneg, native_nat_to_int]
  have hWidth : (↑i + 1 + -↑i : Int) = 1 := by omega
  rw [hWidth]
  change SmtValue.Binary 1 (native_mod_total (pa / native_int_pow2 (↑i)) (native_int_pow2 1)) =
    bv1 (pa.toNat.testBit i)
  have hpowi : native_int_pow2 (↑i) = (2 ^ i : Int) := by
    simpa [native_nat_to_int] using native_int_pow2_nat i
  have hpow1 : native_int_pow2 1 = (2 : Int) := by
    native_decide
  rw [hpowi, hpow1]
  have hpa : ((Int.toNat pa : Nat) : Int) = pa := by
    simpa using (Int.toNat_of_nonneg hpa0)
  have hdiv : pa / (2 ^ i : Int) = ((Int.toNat pa / 2 ^ i : Nat) : Int) := by
    rw [← hpa]
    exact (Int.natCast_ediv (Int.toNat pa) (2 ^ i)).symm
  have hmod : native_mod_total (pa / (2 ^ i : Int)) 2 =
      ((Int.toNat pa / 2 ^ i % 2 : Nat) : Int) := by
    unfold native_mod_total
    rw [hdiv]
    exact (Int.natCast_emod (Int.toNat pa / 2 ^ i) 2).symm
  rw [hmod]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hbit : (Int.toNat pa / 2 ^ i % 2 = 1)
  · simp [bv1, hbit]
  · have hzero : Int.toNat pa / 2 ^ i % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (Int.toNat pa / 2 ^ i) with h0 | h1
      · exact h0
      · exact False.elim (hbit h1)
    simp [bv1, hbit, hzero]

theorem bv1_and (x y : Bool) :
    __smtx_model_eval_bvand (bv1 x) (bv1 y) = bv1 (x && y) := by
  cases x <;> cases y <;> native_decide

theorem bv1_or (x y : Bool) :
    __smtx_model_eval_bvor (bv1 x) (bv1 y) = bv1 (x || y) := by
  cases x <;> cases y <;> native_decide

theorem bv1_eq_one (x : Bool) :
    __smtx_model_eval_eq (bv1 x) (SmtValue.Binary 1 1) = SmtValue.Boolean x := by
  cases x <;> simp [bv1, __smtx_model_eval_eq, native_veq]

theorem smtx_eval_bvand_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvand x y) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_bvor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvor x y) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.concat x y) =
      __smtx_model_eval_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_bvmul_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvmul x y) =
      __smtx_model_eval_bvmul
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_bvumulo_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvumulo x y) =
      __smtx_model_eval_bvumulo
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem native_mod_nat_of_lt {n m : Nat} (_hm : 0 < m) (h : n < m) :
    native_mod_total (n : Int) (m : Int) = (n : Int) := by
  unfold native_mod_total
  exact Int.emod_eq_of_lt (Int.natCast_nonneg n) (by exact_mod_cast h)

theorem concat_zero_right_value
    (w A : Nat) (haBound : A < 2 ^ w) :
    __smtx_model_eval_concat
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary 0 0) =
    SmtValue.Binary (native_nat_to_int w) (A : Int) := by
  change
    SmtValue.Binary (native_zplus (native_nat_to_int w) 0)
      (native_mod_total
        (native_binary_concat (native_nat_to_int w) (A : Int) 0 0)
        (native_int_pow2 (native_zplus (native_nat_to_int w) 0))) =
    SmtValue.Binary (native_nat_to_int w) (A : Int)
  have hWidth : native_zplus (native_nat_to_int w) 0 = native_nat_to_int w := by
    simp [native_zplus, native_nat_to_int]
  rw [hWidth]
  unfold native_binary_concat
  simp [native_zplus, native_zmult]
  have hpow0 : native_int_pow2 0 = (1 : Int) := by native_decide
  rw [hpow0]
  simp
  have hmod :
      native_mod_total (A : Int) (native_int_pow2 (native_nat_to_int w)) =
        (A : Int) := by
    rw [native_int_pow2_nat w]
    exact native_mod_nat_of_lt (Nat.two_pow_pos w) haBound
  rw [hmod]

theorem concat_zero_left_value
    (w A : Nat) (haBound : A < 2 ^ w) :
    __smtx_model_eval_concat
      (SmtValue.Binary 1 0)
      (SmtValue.Binary (native_nat_to_int w) (A : Int)) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
  change
    SmtValue.Binary (native_zplus 1 (native_nat_to_int w))
      (native_mod_total
        (native_binary_concat 1 0 (native_nat_to_int w) (A : Int))
        (native_int_pow2 (native_zplus 1 (native_nat_to_int w)))) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int)
  have hWidth : native_zplus 1 (native_nat_to_int w) = native_nat_to_int (w + 1) := by
    have hEq : (1 : Int) + (w : Int) = ((w + 1 : Nat) : Int) := by omega
    simpa [native_zplus, native_nat_to_int] using hEq
  rw [hWidth]
  unfold native_binary_concat
  simp [native_zplus, native_zmult]
  have hAHi : A < 2 ^ (w + 1) := by
    have hle : 2 ^ w ≤ 2 ^ (w + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_of_lt_of_le haBound hle
  have hmod :
      native_mod_total (A : Int) (native_int_pow2 (native_nat_to_int (w + 1))) =
        (A : Int) := by
    rw [native_int_pow2_nat (w + 1)]
    exact native_mod_nat_of_lt (Nat.two_pow_pos (w + 1)) hAHi
  rw [hmod]

theorem eval_extract_bit_term
    (M : SmtModel) (t : Term) (w payload : Int) (i : Nat)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w payload)
    (hPayload0 : 0 ≤ payload) :
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.UOp2 UserOp2.extract
            (Term.Numeral (native_nat_to_int i))
            (Term.Numeral (native_nat_to_int i))) t)) =
      bv1 (payload.toNat.testBit i) := by
  show __smtx_model_eval M
      (SmtTerm.extract (SmtTerm.Numeral (native_nat_to_int i))
        (SmtTerm.Numeral (native_nat_to_int i)) (__eo_to_smt t)) =
      bv1 (payload.toNat.testBit i)
  rw [smtx_eval_extract_term_eq, hEval]
  simp [__smtx_model_eval]
  exact extract_bit_binary_eval w payload i hPayload0

theorem eval_bvand_term
    (M : SmtModel) (x y : Term) (bx byv : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = bv1 byv) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y)) =
      bv1 (bx && byv) := by
  show __smtx_model_eval M (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)) =
      bv1 (bx && byv)
  rw [smtx_eval_bvand_term_eq]
  rw [hx, hy]
  exact bv1_and bx byv

theorem eval_bvor_term
    (M : SmtModel) (x y : Term) (bx byv : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = bv1 byv) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y)) =
      bv1 (bx || byv) := by
  show __smtx_model_eval M (SmtTerm.bvor (__eo_to_smt x) (__eo_to_smt y)) =
      bv1 (bx || byv)
  rw [smtx_eval_bvor_term_eq]
  rw [hx, hy]
  exact bv1_or bx byv

theorem eval_concat_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)) =
      __smtx_model_eval_concat vx vy := by
  show __smtx_model_eval M (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_concat vx vy
  rw [smtx_eval_concat_term_eq]
  rw [hx, hy]

theorem eval_bvmul_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y)) =
      __smtx_model_eval_bvmul vx vy := by
  show __smtx_model_eval M (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_bvmul vx vy
  rw [smtx_eval_bvmul_term_eq]
  rw [hx, hy]

theorem eval_bvumulo_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x) y)) =
      __smtx_model_eval_bvumulo vx vy := by
  show __smtx_model_eval M (SmtTerm.bvumulo (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_bvumulo vx vy
  rw [smtx_eval_bvumulo_term_eq]
  rw [hx, hy]

theorem eval_zero_extend_one_term
    (M : SmtModel) (a : Term) (w A : Nat)
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (haBound : A < 2 ^ w) :
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.concat) (Term.Binary 1 0))
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
            (Term.Binary 0 0)))) =
      SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
  have hZero0 : __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
      SmtValue.Binary 0 0 := by
    change __smtx_model_eval M (SmtTerm.Binary 0 0) = SmtValue.Binary 0 0
    simp only [__smtx_model_eval]
  have hInner :=
    eval_concat_term M a (Term.Binary 0 0)
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary 0 0) haEval hZero0
  have hInner' :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
            (Term.Binary 0 0))) =
        SmtValue.Binary (native_nat_to_int w) (A : Int) := by
    rw [hInner]
    exact concat_zero_right_value w A haBound
  have hZero1 : __smtx_model_eval M (__eo_to_smt (Term.Binary 1 0)) =
      SmtValue.Binary 1 0 := by
    change __smtx_model_eval M (SmtTerm.Binary 1 0) = SmtValue.Binary 1 0
    simp only [__smtx_model_eval]
  have hOuter :=
    eval_concat_term M (Term.Binary 1 0)
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
        (Term.Binary 0 0))
      (SmtValue.Binary 1 0)
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      hZero1 hInner'
  rw [hOuter]
  exact concat_zero_left_value w A haBound

def zeroExtendOneTerm (a : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat) (Term.Binary 1 0))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) (Term.Binary 0 0))

theorem typeof_zero_extend_one_term
    (a : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (zeroExtendOneTerm a) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1))) := by
  dsimp [zeroExtendOneTerm]
  change
    __eo_typeof_concat (__eo_typeof (Term.Binary 1 0))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
          (Term.Binary 0 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  change
    __eo_typeof_concat
      (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_len (Term.Binary 1 0)))
      (__eo_typeof_concat (__eo_typeof a) (__eo_typeof (Term.Binary 0 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  rw [haTy]
  change
    __eo_typeof_concat
      (__eo_mk_apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
      (__eo_typeof_concat
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))
        (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_len (Term.Binary 0 0)))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  change
    __eo_typeof_concat
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
      (__eo_typeof_concat
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  change
    __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_add (Term.Numeral 1)
        (__eo_add (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  have hAddInner :
      __eo_add (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Numeral (native_nat_to_int w) := by
    simp [__eo_add, native_zplus, native_nat_to_int]
  have hAddOuter :
      __eo_add (Term.Numeral 1) (Term.Numeral (native_nat_to_int w)) =
        Term.Numeral (native_nat_to_int (w + 1)) := by
    have hEq : (1 : Int) + (w : Int) = ((w + 1 : Nat) : Int) := by omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  rw [hAddInner, hAddOuter]
  rfl

theorem typeof_bvmul_same_bitvec
    (x y : Term) (w : Nat)
    (hxTy : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hyTy : __eo_typeof y =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  rw [hxTy, hyTy]
  change
    __eo_requires
      (__eo_eq (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int w)))
      (Term.Boolean true)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  simp [__eo_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

theorem typeof_binary_bitvec_nat
    (w : Nat) (n : Int) :
    __eo_typeof (Term.Binary (native_nat_to_int w) n) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_len (Term.Binary (native_nat_to_int w) n)) =
    Term.Apply (Term.UOp UserOp.BitVec)
      (Term.Numeral (native_nat_to_int w))
  rfl

theorem eval_eq_bv1_one_term
    (M : SmtModel) (x : Term) (bx : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
        (Term.Binary 1 1))) =
      SmtValue.Boolean bx := by
  show __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1)) =
      SmtValue.Boolean bx
  rw [smtx_eval_eq_term_eq, hx]
  simp [__smtx_model_eval]
  exact bv1_eq_one bx

theorem bvmul_high_bit_value (w A B : Nat) :
    __smtx_model_eval_extract
      (SmtValue.Numeral (native_nat_to_int w))
      (SmtValue.Numeral (native_nat_to_int w))
      (__smtx_model_eval_bvmul
        (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
        (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))) =
    bv1 ((A * B).testBit w) := by
  have hpow : native_int_pow2 (native_nat_to_int (w + 1)) =
      (2 ^ (w + 1) : Int) := native_int_pow2_nat (w + 1)
  have hmulPayload :
      native_mod_total (native_zmult (A : Int) (B : Int))
          (native_int_pow2 (native_nat_to_int (w + 1))) =
        ((A * B) % 2 ^ (w + 1) : Nat) := by
    unfold native_mod_total native_zmult
    change ((A : Int) * (B : Int)) %
        native_int_pow2 (native_nat_to_int (w + 1)) =
      ((A * B) % 2 ^ (w + 1) : Nat)
    rw [hpow]
    have hcastMul : ((A : Int) * (B : Int)) = ((A * B : Nat) : Int) := by
      norm_cast
    rw [hcastMul]
    exact (Int.natCast_emod (A * B) (2 ^ (w + 1))).symm
  change
    __smtx_model_eval_extract (SmtValue.Numeral (native_nat_to_int w))
      (SmtValue.Numeral (native_nat_to_int w))
      (SmtValue.Binary (native_nat_to_int (w + 1))
        (native_mod_total (native_zmult (A : Int) (B : Int))
          (native_int_pow2 (native_nat_to_int (w + 1))))) =
    bv1 ((A * B).testBit w)
  rw [hmulPayload]
  rw [extract_bit_binary_eval (native_nat_to_int (w + 1))
    (((A * B) % 2 ^ (w + 1) : Nat) : Int) w (Int.natCast_nonneg _)]
  congr 1
  rw [Int.toNat_natCast]
  have htb := Nat.testBit_mod_two_pow (A * B) (w + 1) w
  simpa using htb

theorem bvmul_one_right_value
    (w B : Nat) (hbBound : B < 2 ^ w) :
    __smtx_model_eval_bvmul
      (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
      (SmtValue.Binary (native_nat_to_int (w + 1)) 1) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) := by
  change
    SmtValue.Binary (native_nat_to_int (w + 1))
      (native_mod_total (native_zmult (B : Int) 1)
        (native_int_pow2 (native_nat_to_int (w + 1)))) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int)
  simp [native_zmult]
  have hbHi : B < 2 ^ (w + 1) := by
    have hle : 2 ^ w ≤ 2 ^ (w + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_of_lt_of_le hbBound hle
  have hmod :
      native_mod_total (B : Int) (native_int_pow2 (native_nat_to_int (w + 1))) =
        (B : Int) := by
    rw [native_int_pow2_nat (w + 1)]
    exact native_mod_nat_of_lt (Nat.two_pow_pos (w + 1)) hbHi
  rw [hmod]

theorem bvumulo_value (w A B : Nat) :
    __smtx_model_eval_bvumulo
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary (native_nat_to_int w) (B : Int)) =
    SmtValue.Boolean (decide (2 ^ w ≤ A * B)) := by
  change
    SmtValue.Boolean
      (native_zleq (native_int_pow2 (native_nat_to_int w))
        (native_zmult (A : Int) (B : Int))) =
    SmtValue.Boolean (decide (2 ^ w ≤ A * B))
  congr 1
  rw [native_int_pow2_nat w]
  change decide ((2 ^ w : Int) ≤ (A : Int) * (B : Int)) =
    decide (2 ^ w ≤ A * B)
  have hMul : (A : Int) * (B : Int) = ((A * B : Nat) : Int) := by
    norm_cast
  rw [hMul]
  have hiff :
      ((2 ^ w : Int) ≤ ((A * B : Nat) : Int)) ↔ 2 ^ w ≤ A * B := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  by_cases h : 2 ^ w ≤ A * B
  · have hI : (2 ^ w : Int) ≤ ((A * B : Nat) : Int) := hiff.2 h
    rw [decide_eq_true hI, decide_eq_true h]
  · have hI : ¬ (2 ^ w : Int) ≤ ((A * B : Nat) : Int) := by
      intro hi
      exact h (hiff.1 hi)
    rw [decide_eq_false hI, decide_eq_false h]

theorem nil_bvmul_bitvec_succ_of_ne_stuck
    (w : Nat)
    (hNe :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int (w + 1)))) ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1)))) =
      Term.Binary (native_nat_to_int (w + 1)) 1 := by
  change __eo_to_bin (Term.Numeral (native_nat_to_int (w + 1))) (Term.Numeral 1) =
      Term.Binary (native_nat_to_int (w + 1)) 1
  change
    (native_ite (native_zleq (native_nat_to_int (w + 1)) 4294967296)
        (__eo_mk_binary (native_nat_to_int (w + 1)) 1) Term.Stuck) =
      Term.Binary (native_nat_to_int (w + 1)) 1
  cases hBound : native_zleq (native_nat_to_int (w + 1)) 4294967296
  · exfalso
    apply hNe
    change
      native_ite (native_zleq (native_nat_to_int (w + 1)) 4294967296)
          (__eo_mk_binary (native_nat_to_int (w + 1)) 1) Term.Stuck =
        Term.Stuck
    rw [hBound]
    rfl
  · simp [native_ite, hBound]
    have hNonneg : native_zleq 0 (native_nat_to_int (w + 1)) = true := by
      exact decide_eq_true (Int.natCast_nonneg (w + 1))
    simp [__eo_mk_binary, native_ite, hNonneg]
    have hmod : native_mod_total (1 : native_Int)
        (native_int_pow2 (native_nat_to_int (w + 1))) = 1 := by
      unfold native_mod_total
      have hpowGt1 : (1 : Int) < native_int_pow2 (native_nat_to_int (w + 1)) := by
        rw [native_int_pow2_nat (w + 1)]
        have hle : 2 ^ 1 ≤ 2 ^ (w + 1) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        exact_mod_cast hle
      exact Int.emod_eq_of_lt (by decide) hpowGt1
    rw [hmod]

theorem term_apply_ne_stuck0 (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

theorem eo_mk_apply_of_ne_stuck0
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

def intRangeList : Nat -> Nat -> Term
  | _start, 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)
  | start, Nat.succ len =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral (native_nat_to_int start)))
        (intRangeList (start + 1) len)

def intZeroList : Nat -> Term
  | 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)
  | Nat.succ k =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (intZeroList k)

theorem intZeroList_ne_stuck :
    ∀ k : Nat, intZeroList k ≠ Term.Stuck := by
  intro k
  induction k with
  | zero =>
      intro h
      cases h
  | succ k ih =>
      intro h
      cases h

theorem intRangeList_ne_stuck :
    ∀ start len : Nat, intRangeList start len ≠ Term.Stuck := by
  intro start len
  induction len generalizing start with
  | zero =>
      intro h
      cases h
  | succ len ih =>
      intro h
      cases h

theorem intZeroList_repeat_rec_eq :
    ∀ k : Nat,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) k =
        intZeroList k := by
  intro k
  induction k with
  | zero =>
      change
        __eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_typeof (Term.Numeral 0)) =
          intZeroList 0
      rfl
  | succ k ih =>
      change
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) k) =
          intZeroList (Nat.succ k)
      rw [ih]
      exact eo_mk_apply_of_ne_stuck0 (term_apply_ne_stuck0 _ _)
        (intZeroList_ne_stuck k)

theorem iota_rec_range_eq :
    ∀ len start : Nat,
      __iota_rec (intZeroList len) (Term.Numeral (native_nat_to_int start)) =
        intRangeList start len := by
  intro len
  induction len with
  | zero =>
      intro start
      rfl
  | succ len ih =>
      intro start
      change
        __eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (native_nat_to_int start)))
          (__iota_rec (intZeroList len)
            (__eo_add (Term.Numeral (native_nat_to_int start))
              (Term.Numeral 1))) =
        intRangeList start (Nat.succ len)
      have hAdd :
          __eo_add (Term.Numeral (native_nat_to_int start)) (Term.Numeral 1) =
            Term.Numeral (native_nat_to_int (start + 1)) := by
        simp [__eo_add, native_zplus, native_nat_to_int]
      rw [hAdd, ih (start + 1)]
      exact eo_mk_apply_of_ne_stuck0 (term_apply_ne_stuck0 _ _)
        (intRangeList_ne_stuck (start + 1) len)

def scanRec (w a b : Nat) : Nat -> Nat -> Bool -> Bool -> Bool
  | _start, 0, _uppc, res => res
  | start, len + 1, uppc, res =>
      (b.testBit start && uppc) ||
        scanRec w a b (start + 1) len
          (a.testBit (w - 1 - start) || uppc) res

def highPair (w a b : Nat) : Prop :=
  ∃ i : Nat, 1 ≤ i ∧ i < w ∧ b.testBit i = true ∧ 2 ^ (w - i) ≤ a

theorem pow_two_mul (a b : Nat) : 2 ^ a * 2 ^ b = 2 ^ (a + b) := by
  rw [← Nat.pow_add]

theorem highPair_overflow {w a b : Nat}
    (h : highPair w a b) : 2 ^ w ≤ a * b := by
  rcases h with ⟨i, h1, hiw, hbit, ha⟩
  have hb : 2 ^ i ≤ b := Nat.ge_two_pow_of_testBit hbit
  have hmul : 2 ^ (w - i) * 2 ^ i ≤ a * b := Nat.mul_le_mul ha hb
  have hsum : w - i + i = w := by omega
  have hp : 2 ^ (w - i) * 2 ^ i = 2 ^ w := by
    rw [pow_two_mul, hsum]
  simpa [hp] using hmul

theorem bit_w_of_range {w n : Nat}
    (hlo : 2 ^ w ≤ n) (hhi : n < 2 ^ (w + 1)) : n.testBit w = true := by
  exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hlo hhi

theorem large_product_highPair {w a b : Nat}
    (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w)
    (hLarge : 2 ^ (w + 1) ≤ a * b) : highPair w a b := by
  have hbNe : b ≠ 0 := by
    intro hb0
    subst b
    simp at hLarge
  let i := b.log2
  have hbLog := (Nat.log2_eq_iff (n := b) (k := i) hbNe).mp rfl
  have hbLow : 2 ^ i ≤ b := hbLog.1
  have hbHigh : b < 2 ^ (i + 1) := hbLog.2
  have hiw : i < w := by
    have hlogLt : b.log2 < w := (Nat.log2_lt hbNe).mpr hbBound
    simpa [i] using hlogLt
  have hi1 : 1 ≤ i := by
    apply Decidable.by_contra
    intro hnot
    have hi0 : i = 0 := by omega
    have hbLt2 : b < 2 := by
      simpa [hi0] using hbHigh
    have hbPos : 0 < b := Nat.pos_of_ne_zero hbNe
    have hbEq1 : b = 1 := by omega
    have hprod : a * b = a := by simp [hbEq1]
    have h2w_le : 2 ^ w ≤ 2 ^ (w + 1) := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hlt : a * b < 2 ^ (w + 1) := by
      rw [hprod]
      exact Nat.lt_of_lt_of_le haBound h2w_le
    exact Nat.not_le_of_gt hlt hLarge
  have haNeed : 2 ^ (w - i) ≤ a := by
    apply Decidable.by_contra
    intro hnot
    have haLt : a < 2 ^ (w - i) := Nat.lt_of_not_le hnot
    have hbPos : 0 < b := Nat.pos_of_ne_zero hbNe
    have hpowPos : 0 < 2 ^ (w - i) := Nat.two_pow_pos _
    have h1 : a * b < 2 ^ (w - i) * b :=
      Nat.mul_lt_mul_of_pos_right haLt hbPos
    have h2 : 2 ^ (w - i) * b < 2 ^ (w - i) * 2 ^ (i + 1) :=
      Nat.mul_lt_mul_of_pos_left hbHigh hpowPos
    have hltMul : a * b < 2 ^ (w - i) * 2 ^ (i + 1) := Nat.lt_trans h1 h2
    have hsum : w - i + (i + 1) = w + 1 := by omega
    have hp : 2 ^ (w - i) * 2 ^ (i + 1) = 2 ^ (w + 1) := by
      rw [pow_two_mul, hsum]
    rw [hp] at hltMul
    exact Nat.not_le_of_gt hltMul hLarge
  exact ⟨i, hi1, hiw, Nat.testBit_log2 hbNe, haNeed⟩

theorem bit_or_highPair_of_overflow {w a b : Nat}
    (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w)
    (hov : 2 ^ w ≤ a * b) :
    (a * b).testBit w = true ∨ highPair w a b := by
  by_cases hbit : (a * b).testBit w = true
  · exact Or.inl hbit
  · right
    have hLarge : 2 ^ (w + 1) ≤ a * b := by
      apply Decidable.by_contra
      intro hnot
      have hlt : a * b < 2 ^ (w + 1) := Nat.lt_of_not_le hnot
      have htrue : (a * b).testBit w = true := bit_w_of_range hov hlt
      exact hbit htrue
    exact large_product_highPair haBound hbBound hLarge

theorem bit_or_highPair_iff_overflow {w a b : Nat}
    (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w) :
    ((a * b).testBit w = true ∨ highPair w a b) ↔ 2 ^ w ≤ a * b := by
  constructor
  · intro h
    cases h with
    | inl hbit => exact Nat.ge_two_pow_of_testBit hbit
    | inr hp => exact highPair_overflow hp
  · exact bit_or_highPair_of_overflow haBound hbBound

def scanPair (w a b : Nat) : Nat -> Nat -> Bool -> Bool
  | _start, 0, _uppc => false
  | start, len + 1, uppc =>
      (b.testBit start && uppc) ||
        scanPair w a b (start + 1) len (a.testBit (w - 1 - start) || uppc)

theorem uppc_step (a k : Nat) :
    (a.testBit k || decide (2 ^ (k + 1) ≤ a)) = decide (2 ^ k ≤ a) := by
  by_cases hlow : 2 ^ k ≤ a
  · have hr : decide (2 ^ k ≤ a) = true := by simp [hlow]
    by_cases hbit : a.testBit k = true
    · simp [hbit, hr]
    · have hhi : 2 ^ (k + 1) ≤ a := by
        apply Decidable.by_contra
        intro hnot
        have hlt : a < 2 ^ (k + 1) := Nat.lt_of_not_le hnot
        have htrue : a.testBit k = true :=
          Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hlow hlt
        exact hbit htrue
      simp [hbit, hhi, hr]
  · have hr : decide (2 ^ k ≤ a) = false := by simp [hlow]
    have hbit : a.testBit k = false := by
      by_cases h : a.testBit k = true
      · have hle := Nat.ge_two_pow_of_testBit h
        exact False.elim (hlow hle)
      · exact Bool.eq_false_iff.2 h
    have hhiNot : ¬ 2 ^ (k + 1) ≤ a := by
      intro hhi
      have hlePow : 2 ^ k ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact hlow (Nat.le_trans hlePow hhi)
    simp [hbit, hhiNot, hr]

theorem scanPair_iff_highPair_aux (w a b : Nat) :
    ∀ start len : Nat,
      start + len = w ->
      (scanPair w a b start len (decide (2 ^ (w - start) ≤ a)) = true ↔
        ∃ i : Nat, start ≤ i ∧ i < w ∧ b.testBit i = true ∧ 2 ^ (w - i) ≤ a) := by
  intro start len
  induction len generalizing start with
  | zero =>
      intro hsum
      constructor
      · intro h
        simp [scanPair] at h
      · intro h
        rcases h with ⟨i, hsi, hiw, _⟩
        omega
  | succ len ih =>
      intro hsum
      simp [scanPair]
      have hws : w - start = w - 1 - start + 1 := by omega
      rw [hws]
      rw [uppc_step a (w - 1 - start)]
      have hpowIdx : w - (start + 1) = w - 1 - start := by omega
      rw [← hpowIdx]
      have htail := ih (start + 1) (by omega)
      rw [htail]
      constructor
      · intro h
        cases h with
        | inl hhead =>
            exact ⟨start, by omega, by omega, hhead.1, by
              simpa [hws, hpowIdx] using hhead.2⟩
        | inr htailEx =>
            rcases htailEx with ⟨i, hsi, hiw, hbi, hai⟩
            exact ⟨i, by omega, hiw, hbi, hai⟩
      · intro h
        rcases h with ⟨i, hsi, hiw, hbi, hai⟩
        by_cases his : i = start
        · subst i
          left
          exact ⟨hbi, by simpa [hws, hpowIdx] using hai⟩
        · right
          exact ⟨i, by omega, hiw, hbi, hai⟩

theorem scanPair_iff_highPair {w a b : Nat}
    (hw : 1 ≤ w) (haBound : a < 2 ^ w) :
    scanPair w a b 1 (w - 1) (a.testBit (w - 1)) = true ↔ highPair w a b := by
  have hinit : a.testBit (w - 1) = decide (2 ^ (w - 1) ≤ a) := by
    have hk : w - 1 + 1 = w := Nat.sub_add_cancel hw
    rw [← uppc_step a (w - 1)]
    have htooHigh : ¬ 2 ^ ((w - 1) + 1) ≤ a := by
      intro h
      rw [hk] at h
      exact Nat.not_le_of_gt haBound h
    simp [htooHigh]
  rw [hinit]
  have hsum : 1 + (w - 1) = w := by omega
  have haux := scanPair_iff_highPair_aux w a b 1 (w - 1) hsum
  simpa [highPair] using haux

theorem scanRec_eq_or_scanPair (w a b start len : Nat)
    (up rs : Bool) :
    scanRec w a b start len up rs = (rs || scanPair w a b start len up) := by
  induction len generalizing start up with
  | zero =>
      simp [scanRec, scanPair]
  | succ len ih =>
      simp [scanRec, scanPair, ih]
      let tail :=
        scanPair w a b (start + 1) len
          (a.testBit (w - 1 - start) || up)
      cases b.testBit start <;> cases up <;> cases rs <;> cases tail <;> rfl

theorem scanRec_iff_overflow {w a b : Nat}
    (hw : 1 ≤ w) (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w) :
    scanRec w a b 1 (w - 1) (a.testBit (w - 1)) ((a * b).testBit w) = true ↔
      2 ^ w ≤ a * b := by
  rw [scanRec_eq_or_scanPair]
  constructor
  · intro h
    have hor : (a * b).testBit w = true ∨
        scanPair w a b 1 (w - 1) (a.testBit (w - 1)) = true := by
      simpa using h
    exact (bit_or_highPair_iff_overflow haBound hbBound).1 <|
      hor.imp id (fun hscan => (scanPair_iff_highPair hw haBound).1 hscan)
  · intro hov
    have hor := (bit_or_highPair_iff_overflow haBound hbBound).2 hov
    cases hor with
    | inl hbit =>
        simp [hbit]
    | inr hp =>
        have hscan := (scanPair_iff_highPair hw haBound).2 hp
        simp [hscan]

theorem term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

theorem term_uop_ne_stuck (op : UserOp) :
    Term.UOp op ≠ Term.Stuck := by
  intro h
  cases h

theorem term_binary_ne_stuck (w n : Int) :
    Term.Binary w n ≠ Term.Stuck := by
  intro h
  cases h

theorem term_numeral_ne_stuck (n : Int) :
    Term.Numeral n ≠ Term.Stuck := by
  intro h
  cases h

theorem eo_to_smt_stuck :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

theorem eval_stuck (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt Term.Stuck) = SmtValue.NotValue := by
  rw [eo_to_smt_stuck]
  change __smtx_model_eval M SmtTerm.None = SmtValue.NotValue
  simp only [__smtx_model_eval]

theorem term_ne_stuck_of_eval_bv1
    (M : SmtModel) (t : Term) (b : Bool)
    (h : __smtx_model_eval M (__eo_to_smt t) = bv1 b) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  rw [eval_stuck] at h
  cases b <;> cases h

theorem term_ne_stuck_of_eval_binary
    (M : SmtModel) (t : Term) (w n : Int)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w n) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  rw [eval_stuck] at h
  cases h

theorem eval_binary (M : SmtModel) (w n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Binary w n)) =
      SmtValue.Binary w n := by
  change __smtx_model_eval M (SmtTerm.Binary w n) = SmtValue.Binary w n
  simp only [__smtx_model_eval]

theorem eo_mk_apply_of_ne_stuck
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem index_term_eq (w start : Nat) (hstart : start < w) :
    __eo_add
        (__eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)))
        (__eo_neg (Term.Numeral (native_nat_to_int start))) =
      Term.Numeral (native_nat_to_int (w - 1 - start)) := by
  have hEq : ((w : Int) + -1 + -(start : Int) :
      Int) = (w - 1 - start : Nat) := by
    omega
  simp [__eo_add, __eo_neg, native_zplus, native_zneg, native_nat_to_int, hEq]

theorem eo_requires_left_ne_stuck_of_ne_stuck
    {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h

theorem eo_bitvec_type_of_smt_type
    (t : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hTrans : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  have hEoTy : __eo_to_smt_type (__eo_typeof t) = SmtType.BitVec w := by
    rw [← hMatch, hTy]
  exact TranslationProofs.eo_to_smt_type_eq_bitvec hEoTy

theorem bitvec_eval_nat_payload
    (M : SmtModel) (hM : model_wf M) (t : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : Nat,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) (n : Int) ∧
      n < 2 ^ w := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hEvalTy := type_preservation M hM (__eo_to_smt t) hNN
  rw [hTy] at hEvalTy
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEval⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true :=
    bitvec_width_nonneg (by simpa [hEval] using hEvalTy)
  have hCanon :
      native_zeq payload
        (native_mod_total payload (native_int_pow2 (native_nat_to_int w))) =
        true :=
    bitvec_payload_canonical (by simpa [hEval] using hEvalTy)
  have hRange := bitvec_payload_range_of_canonical hWidth hCanon
  let n : Nat := Int.toNat payload
  have hPayloadNat : ((n : Nat) : Int) = payload := by
    simpa [n] using Int.toNat_of_nonneg hRange.1
  have hEvalNat :
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) (n : Int) := by
    rw [hEval, hPayloadNat]
  have hBound : n < 2 ^ w := by
    have hLt : (n : Int) < (2 ^ w : Int) := by
      rw [hPayloadNat]
      simpa [native_int_pow2_nat w] using hRange.2
    exact_mod_cast hLt
  exact ⟨n, hEvalNat, hBound⟩
