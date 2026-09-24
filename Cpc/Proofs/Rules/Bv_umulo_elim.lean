module

public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

theorem umulo_indices_eq
    (w : Nat) (hw : 1 ≤ w) :
    __eo_requires
      (__eo_is_neg
        (__eo_add
          (__eo_add (Term.Numeral 1)
            (__eo_add (Term.Numeral (native_nat_to_int w))
              (Term.Numeral (-1 : native_Int))))
          (Term.Numeral (-1 : native_Int))))
      (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (__eo_add
            (__eo_add (Term.Numeral 1)
              (__eo_add (Term.Numeral (native_nat_to_int w))
                (Term.Numeral (-1 : native_Int))))
            (Term.Numeral (-1 : native_Int))))
        (Term.Numeral 1)) =
      intRangeList 1 (w - 1) := by
  have hSub :
      __eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
    have hEq : ((w : Int) + (-1 : Int) : Int) = ((w - 1 : Nat) : Int) := by
      omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  have hLen :
      __eo_add
          (__eo_add (Term.Numeral 1)
            (Term.Numeral (native_nat_to_int (w - 1))))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
    have hEq : ((1 : Int) + (w - 1 : Nat) + (-1 : Int) : Int) =
        ((w - 1 : Nat) : Int) := by omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  rw [hSub, hLen]
  have hNotNeg :
      __eo_is_neg (Term.Numeral (native_nat_to_int (w - 1))) =
        Term.Boolean false := by
    have hNonneg : ¬ (((w - 1 : Nat) : Int) < 0) :=
      Int.not_lt_of_ge (Int.natCast_nonneg (w - 1))
    simp [__eo_is_neg, native_zlt, native_nat_to_int, hNonneg]
  have hRepeat :
      __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (Term.Numeral (native_nat_to_int (w - 1))) =
        intZeroList (w - 1) := by
    change
      native_ite
        (native_zlt (native_nat_to_int (w - 1)) (0 : native_Int))
        Term.Stuck
        (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (native_int_to_nat (native_nat_to_int (w - 1)))) =
        intZeroList (w - 1)
    have hNegFalse :
        native_zlt (native_nat_to_int (w - 1)) (0 : native_Int) = false := by
      simp only [native_zlt, native_nat_to_int]
      refine decide_eq_false ?_
      show ¬ (((w - 1 : Nat) : Int) < 0)
      omega
    have hToNat :
        native_int_to_nat (native_nat_to_int (w - 1)) = w - 1 := by
      simp [native_int_to_nat, native_nat_to_int]
    rw [hNegFalse, hToNat]
    simp [native_ite]
    exact intZeroList_repeat_rec_eq (w - 1)
  have hIota :
      __iota_rec (intZeroList (w - 1)) (Term.Numeral 1) =
        intRangeList 1 (w - 1) := by
    simpa [native_nat_to_int] using iota_rec_range_eq (w - 1) 1
  rw [hNotNeg, hRepeat, hIota]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

def mulHighBitTerm (a b : Term) : Term :=
  let wTerm := __bv_bitwidth (__eo_typeof a)
  let aExt := zeroExtendOneTerm a
  let bExt := zeroExtendOneTerm b
  __eo_mk_apply (Term.UOp2 UserOp2.extract wTerm wTerm)
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt)
        (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt))))

theorem eval_mul_high_bit_term
    (M : SmtModel) (a b : Term) (w A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (haBound : A < 2 ^ w) (hbBound : B < 2 ^ w)
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (mulHighBitTerm a b)) =
      bv1 ((A * B).testBit w) := by
  let aExt := zeroExtendOneTerm a
  let bExt := zeroExtendOneTerm b
  have haExtEval :
      __smtx_model_eval M (__eo_to_smt aExt) =
        SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
    simpa [aExt, zeroExtendOneTerm] using
      eval_zero_extend_one_term M a w A haEval haBound
  have hbExtEval :
      __smtx_model_eval M (__eo_to_smt bExt) =
        SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) := by
    simpa [bExt, zeroExtendOneTerm] using
      eval_zero_extend_one_term M b w B hbEval hbBound
  have haExtTy :
      __eo_typeof aExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    simpa [aExt] using typeof_zero_extend_one_term a w haTy
  let nilMul := __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)
  have hNilNe' : nilMul ≠ Term.Stuck := by
    simpa [nilMul, aExt] using hNilNe
  have hNilEq :
      nilMul = Term.Binary (native_nat_to_int (w + 1)) 1 := by
    dsimp [nilMul]
    rw [haExtTy]
    exact nil_bvmul_bitvec_succ_of_ne_stuck w (by
      simpa [nilMul, haExtTy] using hNilNe')
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nilMul) =
        SmtValue.Binary (native_nat_to_int (w + 1)) 1 := by
    rw [hNilEq]
    change __smtx_model_eval M
      (SmtTerm.Binary (native_nat_to_int (w + 1)) 1) =
      SmtValue.Binary (native_nat_to_int (w + 1)) 1
    simp only [__smtx_model_eval]
  let bTimesOne := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul
  have hbTimesOneEq :
      bTimesOne = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul := by
    dsimp [bTimesOne]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilEq]; exact term_binary_ne_stuck _ _)
  have hbTimesOneEval :
      __smtx_model_eval M (__eo_to_smt bTimesOne) =
        SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) := by
    rw [hbTimesOneEq]
    have hMul :=
      eval_bvmul_term M bExt nilMul
        (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
        (SmtValue.Binary (native_nat_to_int (w + 1)) 1)
        hbExtEval hNilEval
    rw [hMul]
    exact bvmul_one_right_value w B hbBound
  have hbTimesOneNe : bTimesOne ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M bTimesOne (native_nat_to_int (w + 1))
      (B : Int) hbTimesOneEval
  let product := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne
  have hProductEq :
      product = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne := by
    dsimp [product]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hbTimesOneNe
  have hProductEval :
      __smtx_model_eval M (__eo_to_smt product) =
        __smtx_model_eval_bvmul
          (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
          (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int)) := by
    rw [hProductEq]
    exact eval_bvmul_term M aExt bTimesOne
      (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
      (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
      haExtEval hbTimesOneEval
  have hProductNe : product ≠ Term.Stuck := by
    rw [hProductEq]
    exact term_apply_ne_stuck _ _
  have hExtractEq :
      __eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product =
      Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product := by
    exact eo_mk_apply_of_ne_stuck (by intro h; cases h) hProductNe
  have hEvalExtract :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
              (Term.Numeral (native_nat_to_int w))) product)) =
        bv1 ((A * B).testBit w) := by
    show __smtx_model_eval M
        (SmtTerm.extract (SmtTerm.Numeral (native_nat_to_int w))
          (SmtTerm.Numeral (native_nat_to_int w)) (__eo_to_smt product)) =
        bv1 ((A * B).testBit w)
    rw [smtx_eval_extract_term_eq, hProductEval]
    simp [__smtx_model_eval]
    exact bvmul_high_bit_value w A B
  have hWidth :
      __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
    rw [haTy]
    rfl
  dsimp [mulHighBitTerm, zeroExtendOneTerm]
  rw [hWidth]
  change
    __smtx_model_eval M
      (__eo_to_smt
        (__eo_mk_apply
          (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
            (Term.Numeral (native_nat_to_int w))) product)) =
      bv1 ((A * B).testBit w)
  rw [hExtractEq]
  exact hEvalExtract

theorem typeof_mul_high_bit_term
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __eo_typeof (mulHighBitTerm a b) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  let aExt := zeroExtendOneTerm a
  let bExt := zeroExtendOneTerm b
  have haExtTy :
      __eo_typeof aExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    simpa [aExt] using typeof_zero_extend_one_term a w haTy
  have hbExtTy :
      __eo_typeof bExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    simpa [bExt] using typeof_zero_extend_one_term b w hbTy
  let nilMul := __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)
  have hNilNe' : nilMul ≠ Term.Stuck := by
    simpa [nilMul, aExt] using hNilNe
  have hNilEq :
      nilMul = Term.Binary (native_nat_to_int (w + 1)) 1 := by
    dsimp [nilMul]
    rw [haExtTy]
    exact nil_bvmul_bitvec_succ_of_ne_stuck w (by
      simpa [nilMul, haExtTy] using hNilNe')
  have hNilTy :
      __eo_typeof nilMul =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    rw [hNilEq]
    exact typeof_binary_bitvec_nat (w + 1) 1
  let bTimesOne := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul
  have hbTimesOneEq :
      bTimesOne = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul := by
    dsimp [bTimesOne]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilEq]; exact term_binary_ne_stuck _ _)
  have hbTimesOneTy :
      __eo_typeof bTimesOne =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    rw [hbTimesOneEq]
    exact typeof_bvmul_same_bitvec bExt nilMul (w + 1) hbExtTy hNilTy
  let product := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne
  have hProductEq :
      product = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne := by
    dsimp [product]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by
        intro h
        have hTyStuck : __eo_typeof bTimesOne = __eo_typeof Term.Stuck := by
          rw [h]
        rw [hbTimesOneTy] at hTyStuck
        change Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) = Term.Stuck at hTyStuck
        cases hTyStuck)
  have hProductTy :
      __eo_typeof product =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    rw [hProductEq]
    exact typeof_bvmul_same_bitvec aExt bTimesOne (w + 1) haExtTy hbTimesOneTy
  have hWidth :
      __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
    rw [haTy]
    rfl
  dsimp [mulHighBitTerm, zeroExtendOneTerm]
  rw [hWidth]
  change
    __eo_typeof
      (__eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  have hExtractEq :
      __eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product =
      Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product := by
    exact eo_mk_apply_of_ne_stuck (by intro h; cases h)
      (by rw [hProductEq]; exact term_apply_ne_stuck _ _)
  rw [hExtractEq]
  exact typeof_extract_bit_of_bv product (w + 1) w hProductTy (by omega)

def mulHighOrTerm (a b : Term) : Term :=
  let hi := mulHighBitTerm a b
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvor) hi)
    (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof hi))

theorem mulHighBitTerm_stuck_of_nil_bvmul_stuck
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNil :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) = Term.Stuck) :
    mulHighBitTerm a b = Term.Stuck := by
  dsimp [mulHighBitTerm]
  rw [haTy]
  simp [__bv_bitwidth, hNil, __eo_mk_apply]

theorem mulHighOrTerm_stuck_of_high_stuck
    (a b : Term) (hHi : mulHighBitTerm a b = Term.Stuck) :
    mulHighOrTerm a b = Term.Stuck := by
  dsimp [mulHighOrTerm]
  rw [hHi]
  simp [__eo_mk_apply]

theorem eval_mul_high_or_term
    (M : SmtModel) (a b : Term) (w A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (haBound : A < 2 ^ w) (hbBound : B < 2 ^ w)
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (mulHighOrTerm a b)) =
      bv1 ((A * B).testBit w) := by
  let hi := mulHighBitTerm a b
  have hHiEval :
      __smtx_model_eval M (__eo_to_smt hi) =
        bv1 ((A * B).testBit w) := by
    simpa [hi] using
      eval_mul_high_bit_term M a b w A B haTy haEval hbEval
        haBound hbBound hNilNe
  have hHiTy :
      __eo_typeof hi =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [hi] using typeof_mul_high_bit_term a b w haTy hbTy hNilNe
  let nilOr := __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof hi)
  have hNilOrEq : nilOr = Term.Binary 1 0 := by
    dsimp [nilOr]
    rw [hHiTy, nil_bvor_bit]
  have hNilOrEval :
      __smtx_model_eval M (__eo_to_smt nilOr) = bv1 false := by
    rw [hNilOrEq]
    simpa [bv1] using eval_binary M 1 0
  let bvorHi := __eo_mk_apply (Term.UOp UserOp.bvor) hi
  have hBvorHiEq :
      bvorHi = Term.Apply (Term.UOp UserOp.bvor) hi := by
    dsimp [bvorHi]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
      (term_ne_stuck_of_eval_bv1 M hi _ hHiEval)
  have hTermEq :
      __eo_mk_apply bvorHi nilOr =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvor) hi) nilOr := by
    rw [hBvorHiEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilOrEq]; exact term_binary_ne_stuck _ _)
  dsimp [mulHighOrTerm]
  change
    __smtx_model_eval M
      (__eo_to_smt (__eo_mk_apply bvorHi nilOr)) =
      bv1 ((A * B).testBit w)
  rw [hTermEq]
  have hEval := eval_bvor_term M hi nilOr ((A * B).testBit w) false
    hHiEval hNilOrEval
  simpa using hEval

def bvUmuloExpanded (a b : Term) : Term :=
  let wTerm := __bv_bitwidth (__eo_typeof a)
  let topIdx := __eo_add wTerm (Term.Numeral (-1 : native_Int))
  let len :=
    __eo_add (__eo_add (Term.Numeral 1) topIdx)
      (Term.Numeral (-1 : native_Int))
  __eo_ite (__eo_eq wTerm (Term.Numeral 1)) (Term.Boolean false)
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__bv_umulo_elim_rec a b
          (__eo_mk_apply (Term.UOp2 UserOp2.extract topIdx topIdx) a)
          (mulHighOrTerm a b)
          (__eo_requires (__eo_is_neg len) (Term.Boolean false)
            (__iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0) len)
              (Term.Numeral 1)))
          wTerm))
      (Term.Binary 1 1))


theorem umulo_rec_nil_eq
    {a b uppc res n : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck)
    (hu : uppc ≠ Term.Stuck) (hr : res ≠ Term.Stuck)
    (hn : n ≠ Term.Stuck) :
    __bv_umulo_elim_rec a b uppc res
      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)) n = res := by
  simp [__bv_umulo_elim_rec, ha, hb, hu, hr, hn]

theorem umulo_rec_cons_eq
    {a b uppc res i ns n : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck)
    (hu : uppc ≠ Term.Stuck) (hr : res ≠ Term.Stuck)
    (hn : n ≠ Term.Stuck) :
    __bv_umulo_elim_rec a b uppc res
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) i) ns) n =
      (let _v0 := (__eo_add (__eo_add n (Term.Numeral (-1 : native_Int)))
          (__eo_neg i))
       let _v1 := (__eo_mk_apply (Term.UOp2 UserOp2.extract _v0 _v0) a)
       let _v2 := (Term.Apply (Term.UOp2 UserOp2.extract i i) b)
       (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.bvor)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) _v2)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) uppc)
                (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof _v2)))))
          (__bv_umulo_elim_rec a b
            (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvor) _v1)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) uppc)
                (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof _v1))))
            res ns n))) := by
  simp [__bv_umulo_elim_rec, ha, hb, hu, hr, hn]

theorem umulo_rec_list_stuck_eq
    (a b uppc res n : Term) :
    __bv_umulo_elim_rec a b uppc res Term.Stuck n = Term.Stuck := by
  by_cases ha : a = Term.Stuck
  · subst a
    exact __bv_umulo_elim_rec.eq_1 b uppc res Term.Stuck n
  by_cases hb : b = Term.Stuck
  · subst b
    exact __bv_umulo_elim_rec.eq_2 a uppc res Term.Stuck n ha
  by_cases hu : uppc = Term.Stuck
  · subst uppc
    exact __bv_umulo_elim_rec.eq_3 a b res Term.Stuck n ha hb
  by_cases hr : res = Term.Stuck
  · subst res
    exact __bv_umulo_elim_rec.eq_4 a b uppc Term.Stuck n ha hb hu
  by_cases hn : n = Term.Stuck
  · subst n
    exact __bv_umulo_elim_rec.eq_5 a b uppc res Term.Stuck ha hb hu hr
  exact __bv_umulo_elim_rec.eq_8 a b uppc res Term.Stuck n ha hb hu hr
    (by intro h; cases h)
    (by intro i ns h; cases h)
    hn

theorem umulo_rec_res_stuck_eq
    (a b uppc ns n : Term) :
    __bv_umulo_elim_rec a b uppc Term.Stuck ns n = Term.Stuck := by
  by_cases ha : a = Term.Stuck
  · subst a
    exact __bv_umulo_elim_rec.eq_1 b uppc Term.Stuck ns n
  by_cases hb : b = Term.Stuck
  · subst b
    exact __bv_umulo_elim_rec.eq_2 a uppc Term.Stuck ns n ha
  by_cases hu : uppc = Term.Stuck
  · subst uppc
    exact __bv_umulo_elim_rec.eq_3 a b Term.Stuck ns n ha hb
  exact __bv_umulo_elim_rec.eq_4 a b uppc ns n ha hb hu

theorem umulo_rec_eval
    (M : SmtModel) (a b uppc res : Term)
    (w A B start len : Nat) (up rs : Bool)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (hupEval : __smtx_model_eval M (__eo_to_smt uppc) = bv1 up)
    (hrsEval : __smtx_model_eval M (__eo_to_smt res) = bv1 rs)
    (hbound : start + len ≤ w) :
    __smtx_model_eval M
      (__eo_to_smt
        (__bv_umulo_elim_rec a b uppc res (intRangeList start len)
          (Term.Numeral (native_nat_to_int w)))) =
      bv1 (scanRec w A B start len up rs) := by
  have haNe : a ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M a (native_nat_to_int w) (A : Int) haEval
  have hbNe : b ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M b (native_nat_to_int w) (B : Int) hbEval
  have hrNe : res ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M res rs hrsEval
  induction len generalizing start uppc up with
  | zero =>
      have huNe : uppc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M uppc up hupEval
      change
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_umulo_elim_rec a b uppc res
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
                (Term.UOp UserOp.Int))
              (Term.Numeral (native_nat_to_int w)))) =
          bv1 (scanRec w A B start 0 up rs)
      rw [umulo_rec_nil_eq haNe hbNe huNe hrNe (term_numeral_ne_stuck _)]
      simpa [intRangeList, scanRec] using hrsEval
  | succ len ih =>
      have huNe : uppc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M uppc up hupEval
      have hstartLt : start < w := by omega
      have htailBound : start + 1 + len ≤ w := by omega
      have hIdx := index_term_eq w start hstartLt
      change
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_umulo_elim_rec a b uppc res
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral (native_nat_to_int start)))
                (intRangeList (start + 1) len))
              (Term.Numeral (native_nat_to_int w)))) =
          bv1 (scanRec w A B start (Nat.succ len) up rs)
      rw [umulo_rec_cons_eq haNe hbNe huNe hrNe (term_numeral_ne_stuck _)]
      rw [hIdx]
      let hiTerm := Term.Numeral (native_nat_to_int (w - 1 - start))
      let iTerm := Term.Numeral (native_nat_to_int start)
      let v1 := Term.Apply (Term.UOp2 UserOp2.extract hiTerm hiTerm) a
      let v2 := Term.Apply (Term.UOp2 UserOp2.extract iTerm iTerm) b
      have hv1MkEq :
          __eo_mk_apply (Term.UOp2 UserOp2.extract hiTerm hiTerm) a = v1 := by
        dsimp [v1]
        exact eo_mk_apply_of_ne_stuck (by intro h; cases h) haNe
      have hv1Eval :
          __smtx_model_eval M (__eo_to_smt v1) =
            bv1 (A.testBit (w - 1 - start)) := by
        simpa [v1, hiTerm] using
          eval_extract_bit_term M a (native_nat_to_int w) (A : Int)
            (w - 1 - start) haEval (Int.natCast_nonneg A)
      have hv2Eval :
          __smtx_model_eval M (__eo_to_smt v2) =
            bv1 (B.testBit start) := by
        simpa [v2, iTerm] using
          eval_extract_bit_term M b (native_nat_to_int w) (B : Int)
            start hbEval (Int.natCast_nonneg B)
      have hv1Ty :
          __eo_typeof v1 =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [v1, hiTerm] using
          typeof_extract_bit_of_bv a w (w - 1 - start) haTy (by omega)
      have hv2Ty :
          __eo_typeof v2 =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [v2, iTerm] using
          typeof_extract_bit_of_bv b w start hbTy hstartLt
      let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof v2)
      have hnilAndEq : nilAnd = Term.Binary 1 1 := by
        dsimp [nilAnd]
        rw [hv2Ty, nil_bvand_bit]
      have hnilAndEval :
          __smtx_model_eval M (__eo_to_smt nilAnd) = bv1 true := by
        rw [hnilAndEq]
        simpa [bv1] using eval_binary M 1 1
      let upAnd := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) uppc) nilAnd
      have hupAndEq :
          upAnd = Term.Apply (Term.Apply (Term.UOp UserOp.bvand) uppc) nilAnd := by
        dsimp [upAnd]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (by rw [hnilAndEq]; exact term_binary_ne_stuck 1 1)
      have hupAndEval :
          __smtx_model_eval M (__eo_to_smt upAnd) = bv1 up := by
        rw [hupAndEq]
        have h := eval_bvand_term M uppc nilAnd up true hupEval hnilAndEval
        simpa using h
      let headAnd := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) v2) upAnd
      have hheadAndEq :
          headAnd = Term.Apply (Term.Apply (Term.UOp UserOp.bvand) v2) upAnd := by
        dsimp [headAnd]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_eval_bv1 M upAnd up hupAndEval)
      have hheadAndEval :
          __smtx_model_eval M (__eo_to_smt headAnd) =
            bv1 (B.testBit start && up) := by
        rw [hheadAndEq]
        exact eval_bvand_term M v2 upAnd (B.testBit start) up
          hv2Eval hupAndEval
      let nilOr := __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof v1)
      have hnilOrEq : nilOr = Term.Binary 1 0 := by
        dsimp [nilOr]
        rw [hv1Ty, nil_bvor_bit]
      have hnilOrEval :
          __smtx_model_eval M (__eo_to_smt nilOr) = bv1 false := by
        rw [hnilOrEq]
        simpa [bv1] using eval_binary M 1 0
      let upOrTail := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) uppc) nilOr
      have hupOrTailEq :
          upOrTail = Term.Apply (Term.Apply (Term.UOp UserOp.bvor) uppc) nilOr := by
        dsimp [upOrTail]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (by rw [hnilOrEq]; exact term_binary_ne_stuck 1 0)
      have hupOrTailEval :
          __smtx_model_eval M (__eo_to_smt upOrTail) = bv1 up := by
        rw [hupOrTailEq]
        have h := eval_bvor_term M uppc nilOr up false hupEval hnilOrEval
        simpa using h
      let newUppc := __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvor) v1) upOrTail
      have hBvorV1Eq :
          __eo_mk_apply (Term.UOp UserOp.bvor) v1 =
            Term.Apply (Term.UOp UserOp.bvor) v1 := by
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_apply_ne_stuck _ _)
      have hnewUppcEq :
          newUppc =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) v1) upOrTail := by
        dsimp [newUppc]
        rw [hBvorV1Eq]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_eval_bv1 M upOrTail up hupOrTailEval)
      have hnewUppcEval :
          __smtx_model_eval M (__eo_to_smt newUppc) =
            bv1 (A.testBit (w - 1 - start) || up) := by
        rw [hnewUppcEq]
        exact eval_bvor_term M v1 upOrTail
          (A.testBit (w - 1 - start)) up hv1Eval hupOrTailEval
      have htailEval :=
        ih newUppc (start + 1)
          (A.testBit (w - 1 - start) || up)
          hnewUppcEval htailBound
      let tail :=
        __bv_umulo_elim_rec a b newUppc res
          (intRangeList (start + 1) len)
          (Term.Numeral (native_nat_to_int w))
      have htailEval' :
          __smtx_model_eval M (__eo_to_smt tail) =
            bv1
              (scanRec w A B (start + 1) len
                (A.testBit (w - 1 - start) || up) rs) := by
        simpa [tail] using htailEval
      have htailNe : tail ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M tail _ htailEval'
      let headOr := __eo_mk_apply (Term.UOp UserOp.bvor) headAnd
      have hheadOrEq :
          headOr = Term.Apply (Term.UOp UserOp.bvor) headAnd := by
        dsimp [headOr]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_ne_stuck_of_eval_bv1 M headAnd _ hheadAndEval)
      have hresultEq :
          __eo_mk_apply headOr tail =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) tail := by
        rw [hheadOrEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) htailNe
      have hresultEqDirect :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) tail =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) tail := by
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) htailNe
      have hFinal := eval_bvor_term M headAnd tail
        (B.testBit start && up)
        (scanRec w A B (start + 1) len
          (A.testBit (w - 1 - start) || up) rs)
        hheadAndEval htailEval'
      simpa [scanRec, hiTerm, iTerm, v1, v2, nilAnd, upAnd, headAnd,
        nilOr, upOrTail, newUppc, tail, headOr, hv1MkEq, hheadOrEq,
        hresultEq, hresultEqDirect] using hFinal

theorem eval_bv_umulo_expanded
    (M : SmtModel) (a b : Term) (w A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (haBound : A < 2 ^ w) (hbBound : B < 2 ^ w)
    (hw : 1 ≤ w)
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (bvUmuloExpanded a b)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) := by
  have hWidth :
      __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
    rw [haTy]
    rfl
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) =
        SmtValue.Boolean (decide (2 ^ w ≤ A * B)) := by
    have h := eval_bvumulo_term M a b
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary (native_nat_to_int w) (B : Int))
      haEval hbEval
    rw [h]
    exact bvumulo_value w A B
  by_cases hw1 : w = 1
  · subst w
    have hNoOverflow : ¬ 2 ^ 1 ≤ A * B := by
      intro hov
      have hA : A ≤ 1 := by omega
      have hB : B ≤ 1 := by omega
      have hA01 : A = 0 ∨ A = 1 := by omega
      have hB01 : B = 0 ∨ B = 1 := by omega
      have hProd : A * B ≤ 1 := by
        rcases hA01 with rfl | rfl <;> rcases hB01 with rfl | rfl <;> omega
      change (2 : Nat) ≤ A * B at hov
      omega
    dsimp [bvUmuloExpanded]
    rw [hWidth]
    change
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_ite
            (__eo_eq (Term.Numeral (native_nat_to_int 1)) (Term.Numeral 1))
            (Term.Boolean false)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.eq)
                (__bv_umulo_elim_rec a b
                  (__eo_mk_apply
                    (Term.UOp2 UserOp2.extract
                      (__eo_add (Term.Numeral (native_nat_to_int 1))
                        (Term.Numeral (-1 : native_Int)))
                      (__eo_add (Term.Numeral (native_nat_to_int 1))
                        (Term.Numeral (-1 : native_Int)))) a)
                  (mulHighOrTerm a b)
                  (__eo_requires
                    (__eo_is_neg
                      (__eo_add
                        (__eo_add (Term.Numeral 1)
                          (__eo_add (Term.Numeral (native_nat_to_int 1))
                            (Term.Numeral (-1 : native_Int))))
                        (Term.Numeral (-1 : native_Int))))
                    (Term.Boolean false)
                    (__iota_rec
                      (__eo_list_repeat
                        (Term.UOp UserOp._at__at_TypedList_cons)
                        (Term.Numeral 0)
                        (__eo_add
                          (__eo_add (Term.Numeral 1)
                            (__eo_add (Term.Numeral (native_nat_to_int 1))
                              (Term.Numeral (-1 : native_Int))))
                          (Term.Numeral (-1 : native_Int))))
                      (Term.Numeral 1)))
                  (Term.Numeral (native_nat_to_int 1))))
              (Term.Binary 1 1)))) =
        __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b))
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int 1)) (Term.Numeral 1) =
          Term.Boolean true := by
      native_decide
    rw [hCond]
    simp [__eo_ite, native_ite, native_teq]
    rw [hOrigEval]
    simp [hNoOverflow, __smtx_model_eval]
  · have hTop :
        __eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
      have hEq : ((w : Int) + (-1 : Int) : Int) = ((w - 1 : Nat) : Int) := by
        omega
      simp [__eo_add, native_zplus, native_nat_to_int, hEq]
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int w)) (Term.Numeral 1) =
          Term.Boolean false := by
      have hne : (w : Int) ≠ 1 := by omega
      have hne' : ¬ (1 : Int) = (w : Int) := by omega
      simp [__eo_eq, native_teq, native_nat_to_int, hne, hne']
    let uppc :=
      __eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int (w - 1)))
          (Term.Numeral (native_nat_to_int (w - 1)))) a
    have haNe : a ≠ Term.Stuck :=
      term_ne_stuck_of_eval_binary M a (native_nat_to_int w) (A : Int) haEval
    have hUppcEq :
        uppc =
          Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int (w - 1)))
              (Term.Numeral (native_nat_to_int (w - 1)))) a := by
      dsimp [uppc]
      exact eo_mk_apply_of_ne_stuck (by intro h; cases h) haNe
    have hUppcEval :
        __smtx_model_eval M (__eo_to_smt uppc) =
          bv1 (A.testBit (w - 1)) := by
      rw [hUppcEq]
      simpa using
        eval_extract_bit_term M a (native_nat_to_int w) (A : Int)
          (w - 1) haEval (Int.natCast_nonneg A)
    have hResEval :
        __smtx_model_eval M (__eo_to_smt (mulHighOrTerm a b)) =
          bv1 ((A * B).testBit w) := by
      exact eval_mul_high_or_term M a b w A B haTy hbTy haEval hbEval
        haBound hbBound hNilNe
    have hIndices := umulo_indices_eq w hw
    have hIndices' :
        __eo_requires
          (__eo_is_neg
            (__eo_add
              (__eo_add (Term.Numeral 1)
                (Term.Numeral (native_nat_to_int (w - 1))))
              (Term.Numeral (-1 : native_Int))))
          (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0)
              (__eo_add
                (__eo_add (Term.Numeral 1)
                  (Term.Numeral (native_nat_to_int (w - 1))))
                (Term.Numeral (-1 : native_Int))))
            (Term.Numeral 1)) =
          intRangeList 1 (w - 1) := by
      simpa [hTop] using hIndices
    have hRecEval :
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
              (intRangeList 1 (w - 1))
              (Term.Numeral (native_nat_to_int w)))) =
          bv1
            (scanRec w A B 1 (w - 1) (A.testBit (w - 1))
              ((A * B).testBit w)) := by
      exact umulo_rec_eval M a b uppc (mulHighOrTerm a b)
        w A B 1 (w - 1) (A.testBit (w - 1)) ((A * B).testBit w)
        haTy hbTy haEval hbEval hUppcEval hResEval (by omega)
    have hEqEval :
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
                  (intRangeList 1 (w - 1))
                  (Term.Numeral (native_nat_to_int w))))
              (Term.Binary 1 1))) =
          SmtValue.Boolean
            (scanRec w A B 1 (w - 1) (A.testBit (w - 1))
              ((A * B).testBit w)) := by
      exact eval_eq_bv1_one_term M
        (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
          (intRangeList 1 (w - 1))
          (Term.Numeral (native_nat_to_int w)))
        (scanRec w A B 1 (w - 1) (A.testBit (w - 1))
          ((A * B).testBit w)) hRecEval
    have hScanBool :
        scanRec w A B 1 (w - 1) (A.testBit (w - 1))
            ((A * B).testBit w) =
          decide (2 ^ w ≤ A * B) := by
      have hiff := scanRec_iff_overflow (w := w) (a := A) (b := B)
        hw haBound hbBound
      by_cases hscan :
          scanRec w A B 1 (w - 1) (A.testBit (w - 1))
            ((A * B).testBit w) = true
      · have hov : 2 ^ w ≤ A * B := hiff.1 hscan
        simp [hscan, hov]
      · have hnOv : ¬ 2 ^ w ≤ A * B := by
          intro hov
          exact hscan (hiff.2 hov)
        have hscanFalse :
          scanRec w A B 1 (w - 1) (A.testBit (w - 1))
            ((A * B).testBit w) = false := Bool.eq_false_iff.2 hscan
        simp [hscanFalse, hnOv]
    dsimp [bvUmuloExpanded]
    rw [hWidth, hTop, hCond]
    simp [__eo_ite, native_ite, native_teq]
    rw [hIndices']
    change
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.eq)
              (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
                (intRangeList 1 (w - 1))
                (Term.Numeral (native_nat_to_int w))))
            (Term.Binary 1 1))) =
        __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b))
    have hRecNe :
        __bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
          (intRangeList 1 (w - 1))
          (Term.Numeral (native_nat_to_int w)) ≠ Term.Stuck :=
      term_ne_stuck_of_eval_bv1 M _ _ hRecEval
    have hEqHead :
        __eo_mk_apply (Term.UOp UserOp.eq)
          (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
            (intRangeList 1 (w - 1))
            (Term.Numeral (native_nat_to_int w))) =
        Term.Apply (Term.UOp UserOp.eq)
          (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
            (intRangeList 1 (w - 1))
            (Term.Numeral (native_nat_to_int w))) := by
      exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.eq) hRecNe
    rw [hEqHead]
    have hEqTerm :
        __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
              (intRangeList 1 (w - 1))
              (Term.Numeral (native_nat_to_int w))))
          (Term.Binary 1 1) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
              (intRangeList 1 (w - 1))
              (Term.Numeral (native_nat_to_int w))))
          (Term.Binary 1 1) := by
      exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
        (term_binary_ne_stuck 1 1)
    rw [hEqTerm, hEqEval, hOrigEval, hScanBool]

theorem bvUmuloExpanded_width_pos
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNe : bvUmuloExpanded a b ≠ Term.Stuck) :
    1 ≤ w := by
  by_cases hw0 : w = 0
  · subst w
    exfalso
    apply hNe
    dsimp [bvUmuloExpanded]
    rw [haTy]
    simp [__bv_bitwidth, __eo_eq, __eo_add, __eo_is_neg, __eo_requires,
      __eo_ite, __eo_mk_apply, __bv_umulo_elim_rec, native_ite,
      native_teq, native_not, SmtEval.native_not, native_zplus,
      native_zlt, native_nat_to_int, umulo_rec_list_stuck_eq]
  · omega

theorem nil_bvmul_ne_of_bvUmuloExpanded_ne
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNe : bvUmuloExpanded a b ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
      (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck := by
  have hw : 1 ≤ w := bvUmuloExpanded_width_pos a b w haTy hNe
  by_cases hw1 : w = 1
  · subst w
    intro hNil
    have hTy :
        __eo_typeof (zeroExtendOneTerm a) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int 2)) := by
      simpa [native_nat_to_int] using typeof_zero_extend_one_term a 1 haTy
    rw [hTy] at hNil
    have hNilOk :
        __eo_nil (Term.UOp UserOp.bvmul)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int 2))) =
          Term.Binary (native_nat_to_int 2) 1 := by
      native_decide
    rw [hNilOk] at hNil
    cases hNil
  · intro hNil
    apply hNe
    have hHiStuck : mulHighBitTerm a b = Term.Stuck :=
      mulHighBitTerm_stuck_of_nil_bvmul_stuck a b w haTy hNil
    have hResStuck : mulHighOrTerm a b = Term.Stuck :=
      mulHighOrTerm_stuck_of_high_stuck a b hHiStuck
    have hWidth :
        __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
      rw [haTy]
      rfl
    have hTop :
        __eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
      have hEq : ((w : Int) + (-1 : Int) : Int) = ((w - 1 : Nat) : Int) := by
        omega
      simp [__eo_add, native_zplus, native_nat_to_int, hEq]
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int w)) (Term.Numeral 1) =
          Term.Boolean false := by
      have hne : (w : Int) ≠ 1 := by omega
      have hne' : ¬ (1 : Int) = (w : Int) := by omega
      simp [__eo_eq, native_teq, native_nat_to_int, hne, hne']
    dsimp [bvUmuloExpanded]
    rw [hWidth, hTop, hCond, hResStuck]
    simp [__eo_ite, __eo_mk_apply, native_ite, native_teq,
      umulo_rec_res_stuck_eq]


theorem bv_umulo_elim_shape_of_ne_stuck (A : Term) :
    __eo_prog_bv_umulo_elim A ≠ Term.Stuck ->
    ∃ a b c,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) c := by
  intro h
  by_cases hShape :
      ∃ a b c,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) c
  · exact hShape
  · have hStuck : __eo_prog_bv_umulo_elim A = Term.Stuck := by
      rw [__eo_prog_bv_umulo_elim.eq_2]
      intro a b c hEq
      exact hShape ⟨a, b, c, hEq⟩
    exact False.elim (h hStuck)

theorem bvumulo_typeof_args_of_non_none
    {a b : Term}
    (hNN : term_has_non_none_type
      (SmtTerm.bvumulo (__eo_to_smt a) (__eo_to_smt b))) :
    ∃ w,
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w := by
  apply bv_binop_ret_args_of_non_none
    (op := SmtTerm.bvumulo) (ret := SmtType.Bool)
  · rw [__smtx_typeof.eq_def] <;> simp only
  · exact hNN

public theorem cmd_step_bv_umulo_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_umulo_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_umulo_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_umulo_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_umulo_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_bv_umulo_elim A)
              change __eo_typeof (__eo_prog_bv_umulo_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_bv_umulo_elim A ≠ Term.Stuck := by
                change __eo_prog_bv_umulo_elim A ≠ Term.Stuck at hProgNe
                exact hProgNe
              rcases bv_umulo_elim_shape_of_ne_stuck A hProgNe' with
                ⟨a, b, rhs, hShape⟩
              subst A
              let lhs := Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b
              let expanded := bvUmuloExpanded a b
              let orig := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_umulo_elim, expanded, orig, lhs,
                  bvUmuloExpanded, mulHighOrTerm, mulHighBitTerm,
                  zeroExtendOneTerm] using hProgNe'
              have hExpandedEq : expanded = rhs :=
                support_eo_requires_cond_eq_of_non_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_umulo_elim
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
                    orig := by
                rw [__eo_prog_bv_umulo_elim.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig, lhs] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    lhs rhs hOrigBool with
                ⟨_hSameTy, hLhsNN⟩
              have hBvumuloNN :
                  term_has_non_none_type
                    (SmtTerm.bvumulo (__eo_to_smt a) (__eo_to_smt b)) := by
                unfold term_has_non_none_type
                exact hLhsNN
              rcases bvumulo_typeof_args_of_non_none hBvumuloNN with
                ⟨w, haSmtTy, hbSmtTy⟩
              have haEoTy := eo_bitvec_type_of_smt_type a w haSmtTy
              have hbEoTy := eo_bitvec_type_of_smt_type b w hbSmtTy
              rcases bitvec_eval_nat_payload M hM a w haSmtTy with
                ⟨av, haEval, haBound⟩
              rcases bitvec_eval_nat_payload M hM b w hbSmtTy with
                ⟨bv, hbEval, hbBound⟩
              have hw : 1 ≤ w :=
                bvUmuloExpanded_width_pos a b w haEoTy hExpandedNe
              have hNilNe :
                  __eo_nil (Term.UOp UserOp.bvmul)
                    (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck :=
                nil_bvmul_ne_of_bvUmuloExpanded_ne a b w haEoTy hExpandedNe
              have hExpandedEval :
                  __smtx_model_eval M (__eo_to_smt expanded) =
                    __smtx_model_eval M (__eo_to_smt lhs) := by
                simpa [expanded, lhs] using
                  eval_bv_umulo_expanded M a b w av bv haEoTy hbEoTy
                    haEval hbEval haBound hbBound hw hNilNe
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt lhs)) := by
                rw [hExpandedEval]
                exact RuleProofs.smt_value_rel_refl _
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt lhs))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_bv_umulo_elim orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M lhs rhs hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
