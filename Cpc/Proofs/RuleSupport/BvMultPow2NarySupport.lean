module

public import Cpc.Proofs.RuleSupport.BvMultPow2Support
import all Cpc.Proofs.RuleSupport.BvMultPow2Support
public import Cpc.Proofs.RuleSupport.BvMultPow2PosSupport
import all Cpc.Proofs.RuleSupport.BvMultPow2PosSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.BvXorOnesSupport
import all Cpc.Proofs.RuleSupport.BvXorOnesSupport

public section

/-! Support for the n-ary multiplication-by-a-power-of-two rewrite. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvMultPow2NarySupport

abbrev op : Term := Term.UOp UserOp.bvmul

private def mul (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private theorem smtx_typeof_bvmul_term_eq_nary
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvmul x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private def baseList (xs ys z : Term) : Term :=
  __eo_list_concat_rec xs (mul z ys)

def base (xs ys z : Term) : Term :=
  __eo_list_singleton_elim op (baseList xs ys z)

private def lhs (xs ys z size n : Term) : Term :=
  __eo_list_concat_rec xs
    (mul z (mul (bvMultPow2Const size n) ys))

def term (xs ys z size n exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (lhs xs ys z size n))
    (bvMultPow2Rhs (base xs ys z) exponent u)

def simpleLhs (xs ys z size n : Term) : Term :=
  mul (base xs ys z) (bvMultPow2Const size n)

def simpleTerm (xs ys z size n exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (simpleLhs xs ys z size n))
    (bvMultPow2Rhs (base xs ys z) exponent u)

def posTerm (xs ys z size n exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (lhs xs ys z size n))
    (BvMultPow2PosSupport.bvMultPow2PosRhs
      (base xs ys z) exponent u)

def simplePosTerm (xs ys z size n exponent u : Term) : Term :=
  BvMultPow2PosSupport.bvMultPow2PosDirectTerm
    (base xs ys z) size n exponent u

private def guardedBase (xs ys z : Term) : Term :=
  __eo_list_singleton_elim op
    (__eo_list_concat op xs (mul z ys))

private def guardedLhs (xs ys z size n : Term) : Term :=
  __eo_list_concat op xs
    (mul z (mul (bvMultPow2Const size n) ys))

private def guardedNegBase (xs ys z : Term) : Term :=
  __eo_mk_apply (Term.UOp UserOp.bvneg) (guardedBase xs ys z)

private def guardedExtract (xs ys z u : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract u (Term.Numeral 0))
    (guardedNegBase xs ys z)

private def guardedRhs (xs ys z exponent u : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.concat)
      (guardedExtract xs ys z u))
    (bvMultPow2Zeros exponent)

private def skeleton
    (xs ys z size n exponent u : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys z size n))
    (guardedRhs xs ys z exponent u)

def program
    (xs ys z size n exponent u P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_mult_pow2_2 xs ys z size n exponent u
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private theorem list_concat_parts_of_ne_stuck (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have hA := support_eo_requires_cond_eq_of_non_stuck hReq
  have hTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hReq
  exact ⟨hA, support_eo_requires_cond_eq_of_non_stuck hTail⟩

private theorem list_concat_reduce (f a b : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f b = Term.Boolean true ->
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  intro hA hB
  simp [__eo_list_concat, hA, hB, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem guarded_lhs_lists
    (xs ys z size n : Term) :
    guardedLhs xs ys z size n ≠ Term.Stuck ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true := by
  intro hLhs
  have hParts := list_concat_parts_of_ne_stuck op xs
    (mul z (mul (bvMultPow2Const size n) ys))
    (by simpa [guardedLhs] using hLhs)
  have hInner := eo_is_list_tail_true_of_cons_self op z
    (mul (bvMultPow2Const size n) ys) hParts.2
  have hYs := eo_is_list_tail_true_of_cons_self op
    (bvMultPow2Const size n) ys hInner
  exact ⟨hParts.1, hYs⟩

private theorem guarded_lhs_eq_lhs
    (xs ys z size n : Term) :
    guardedLhs xs ys z size n ≠ Term.Stuck ->
    guardedLhs xs ys z size n = lhs xs ys z size n := by
  intro hLhs
  have hParts := list_concat_parts_of_ne_stuck op xs
    (mul z (mul (bvMultPow2Const size n) ys))
    (by simpa [guardedLhs] using hLhs)
  exact list_concat_reduce op xs
    (mul z (mul (bvMultPow2Const size n) ys)) hParts.1 hParts.2

private theorem guarded_base_eq_base
    (xs ys z : Term) :
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    guardedBase xs ys z = base xs ys z := by
  intro hXs hYs
  have hZYs : __eo_is_list op (mul z ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op z ys (by decide) hYs
  unfold guardedBase base
  rw [show __eo_list_concat op xs (mul z ys) =
      __eo_list_concat_rec xs (mul z ys) from
    list_concat_reduce op xs (mul z ys) hXs hZYs]
  rfl

private theorem premise_shape
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> z ≠ Term.Stuck ->
    size ≠ Term.Stuck -> n ≠ Term.Stuck -> exponent ≠ Term.Stuck ->
    u ≠ Term.Stuck ->
    program xs ys z size n exponent u P1 P2 P3 ≠ Term.Stuck ->
    ∃ sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3,
      P1 = bvMultPow2IspowPrem sizeRef1 nRef1 ∧
      P2 = bvMultPow2ExponentPrem sizeRef2 nRef2 exponentRef ∧
      P3 = bvMultPow2UpperPremRefs sizeRef3 sizeRef4 nRef3 uRef := by
  intro hXs hYs hZ hSize hN hExponent hU hProg
  by_cases hShape :
      ∃ sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3,
        P1 = bvMultPow2IspowPrem sizeRef1 nRef1 ∧
        P2 = bvMultPow2ExponentPrem sizeRef2 nRef2 exponentRef ∧
        P3 = bvMultPow2UpperPremRefs sizeRef3 sizeRef4 nRef3 uRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_mult_pow2_2.eq_9 xs ys z size n exponent u
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hXs hYs hZ hSize hN hExponent hU (by
        intro sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef
          sizeRef3 sizeRef4 nRef3 hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨sizeRef1, nRef1, exponentRef, sizeRef2, nRef2, uRef,
            sizeRef3, sizeRef4, nRef3, rfl, rfl, rfl⟩)

private theorem program_canonical
    (xs ys z size n exponent u : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> z ≠ Term.Stuck ->
    size ≠ Term.Stuck -> n ≠ Term.Stuck -> exponent ≠ Term.Stuck ->
    u ≠ Term.Stuck ->
    program xs ys z size n exponent u
        (bvMultPow2IspowPrem size n)
        (bvMultPow2ExponentPrem size n exponent)
        (bvMultPow2UpperPrem size n u) =
      skeleton xs ys z size n exponent u := by
  intro hXs hYs hZ hSize hN hExponent hU
  unfold program bvMultPow2IspowPrem bvMultPow2ExponentPrem
    bvMultPow2UpperPrem bvMultPow2Diff
  rw [__eo_prog_bv_mult_pow2_2.eq_8 xs ys z size n exponent u
    size n exponent size n u size size n
    hXs hYs hZ hSize hN hExponent hU]
  simp [skeleton, guardedLhs, guardedRhs, guardedExtract, guardedNegBase,
    guardedBase, mul, op, bvMultPow2Const, bvMultPow2Zeros, __eo_requires,
    __eo_and, __eo_eq, native_ite, native_teq, native_not, native_and,
    hXs, hYs, hZ, hSize, hN, hExponent, hU]

private theorem program_normalize
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    program xs ys z size n exponent u P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvMultPow2IspowPrem size n ∧
      P2 = bvMultPow2ExponentPrem size n exponent ∧
      P3 = bvMultPow2UpperPrem size n u ∧
      program xs ys z size n exponent u P1 P2 P3 =
        skeleton xs ys z size n exponent u := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hSize := RuleProofs.term_ne_stuck_of_has_smt_translation size hSizeTrans
  have hN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hExponent :=
    RuleProofs.term_ne_stuck_of_has_smt_translation exponent hExponentTrans
  have hU := RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
  rcases premise_shape xs ys z size n exponent u P1 P2 P3
      hXs hYs hZ hSize hN hExponent hU hProg with
    ⟨sizeRef1, nRef1, exponentRef, sizeRef2, nRef2, uRef,
      sizeRef3, sizeRef4, nRef3, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold program bvMultPow2IspowPrem bvMultPow2ExponentPrem
    bvMultPow2UpperPremRefs bvMultPow2Diff at hReq
  rw [__eo_prog_bv_mult_pow2_2.eq_8 xs ys z size n exponent u
    sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3
    hXs hYs hZ hSize hN hExponent hU] at hReq
  rcases bv_mult_pow2_guard_refs
      (size := size) (n := n) (exponent := exponent) (u := u)
      (sizeRef1 := sizeRef1) (nRef1 := nRef1)
      (exponentRef := exponentRef) (sizeRef2 := sizeRef2)
      (nRef2 := nRef2) (uRef := uRef) (sizeRef3 := sizeRef3)
      (sizeRef4 := sizeRef4) (nRef3 := nRef3)
      (by simpa [bvMultPow2Guard] using hReq) with
    ⟨hSize1, hN1, hExponentRef, hSize2, hN2, hURef,
      hSize3, hSize4, hN3⟩
  subst sizeRef1
  subst nRef1
  subst exponentRef
  subst sizeRef2
  subst nRef2
  subst uRef
  subst sizeRef3
  subst sizeRef4
  subst nRef3
  refine ⟨hP1, hP2, ?_, ?_⟩
  · simpa [bvMultPow2UpperPrem, bvMultPow2UpperPremRefs] using hP3
  · rw [hP1, hP2, hP3]
    simpa [bvMultPow2UpperPrem, bvMultPow2UpperPremRefs] using
      (program_canonical xs ys z size n exponent u
        hXs hYs hZ hSize hN hExponent hU)

theorem program_eq_term_of_type_bool
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (program xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    P1 = bvMultPow2IspowPrem size n ∧
      P2 = bvMultPow2ExponentPrem size n exponent ∧
      P3 = bvMultPow2UpperPrem size n u ∧
      program xs ys z size n exponent u P1 P2 P3 =
        term xs ys z size n exponent u := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases program_normalize xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProg with
    ⟨hP1, hP2, hP3, hSkeleton⟩
  have hSkeletonTy :
      __eo_typeof (skeleton xs ys z size n exponent u) = Term.Bool := by
    rw [← hSkeleton]
    exact hTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLists := guarded_lhs_lists xs ys z size n hLhsNe
  have hLhsEq := guarded_lhs_eq_lhs xs ys z size n hLhsNe
  have hBaseEq := guarded_base_eq_base xs ys z hLists.1 hLists.2
  have hOuterConcatFunNe :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
  have hExtractNe :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOuterConcatFunNe
  have hNegNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hExtractNe
  refine ⟨hP1, hP2, hP3, ?_⟩
  calc
    program xs ys z size n exponent u P1 P2 P3 =
        skeleton xs ys z size n exponent u := hSkeleton
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (guardedLhs xs ys z size n))
          (guardedRhs xs ys z exponent u) := by
      unfold skeleton
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
    _ = term xs ys z size n exponent u := by
      unfold guardedRhs at hRhsNe ⊢
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hOuterConcatFunNe]
      unfold guardedExtract at hExtractNe ⊢
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hExtractNe]
      unfold guardedNegBase at hNegNe ⊢
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hNegNe]
      unfold term bvMultPow2Rhs bvExtractTerm
      rw [hLhsEq, hBaseEq]

theorem program_lists_of_type_bool
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (program xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases program_normalize xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProg with
    ⟨_hP1, _hP2, _hP3, hSkeleton⟩
  have hSkeletonTy :
      __eo_typeof (skeleton xs ys z size n exponent u) = Term.Bool := by
    rw [← hSkeleton]
    exact hTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  exact guarded_lhs_lists xs ys z size n hLhsNe

def ListTypeOrNil (t : Term) (w : Nat) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ∨
    ∀ tail, __eo_list_concat_rec t tail = tail

private theorem typeof_bvmul_args_of_result_bitvec
    (x y width : Term) :
    __eo_typeof (mul x y) =
        Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro h
  exact BvXorOnesSupport.typeof_bvxor_args_of_result_bitvec x y width
    (by have hsimpa := h; (try simp [mul, op] at hsimpa ⊢); exact hsimpa)

private theorem list_concat_rec_cons_of_right_ne_stuck
    (f x xs z : Term) :
    z ≠ Term.Stuck ->
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs z) := by
  intro hZ
  cases z <;> first | exact absurd rfl hZ | rfl

private theorem mk_apply_right_stuck_local (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  cases f <;> rfl

private theorem mk_apply_eq_apply_of_args_ne_stuck
    (f x : Term) :
    f ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hF hX
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem list_concat_rec_right_type_ne_stuck
    (a z : Term) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof z ≠ Term.Stuck := by
  intro hList hTyNe
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA =>
      apply False.elim
      apply hTyNe
      cases a <;> rfl
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hTyNe
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          h, mk_apply_right_stuck_local]
        rfl
      have hTailTyNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        intro h
        apply hTyNe
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe]
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) = Term.Stuck
        rw [h]
        simp [__eo_typeof_bvand]
      exact ih hTailList hTailTyNe
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hTyNe

private theorem list_concat_rec_result_type
    (a z width : Term) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hZTy hResultNe
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA => cases hZTy
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hResultNe
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          h, mk_apply_right_stuck_local]
        rfl
      have hTailTyNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        intro h
        apply hResultNe
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe]
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) = Term.Stuck
        rw [h]
        simp [__eo_typeof_bvand]
      have hTailTy := ih hTailList hZTy hTailTyNe
      have hOuterNe :
          __eo_typeof_bvand (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec xs z)) ≠ Term.Stuck := by
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe]
          at hResultNe
        exact hResultNe
      rcases BvXorOnesSupport.typeof_bvand_arg_types_of_ne_stuck hOuterNe with
        ⟨actualWidth, hXTy, hTailShape⟩
      have hWidth : actualWidth = width := by
        rw [hTailTy] at hTailShape
        cases hTailShape
        rfl
      subst actualWidth
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        apply hOuterNe
        rw [hXTy, hTailTy, h]
        simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
          native_teq, native_not]
      rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
        mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe]
      change __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (__eo_list_concat_rec xs z)) = _
      rw [hXTy, hTailTy]
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hZTy

private theorem list_concat_rec_replace_tail_type
    (a z₁ z₂ width : Term) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z₁) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof z₂ = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_concat_rec a z₂) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hFirstTy hZ₂Ty
  induction a, z₁ using __eo_list_concat_rec.induct generalizing z₂ with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA =>
      have hBad : __eo_typeof (__eo_list_concat_rec a Term.Stuck) =
          Term.Stuck := by
        cases a <;> rfl
      rw [hBad] at hFirstTy
      cases hFirstTy
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTail₁Ne : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          h, mk_apply_right_stuck_local] at hFirstTy
        cases hFirstTy
      rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
        mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTail₁Ne]
        at hFirstTy
      have hParts := typeof_bvmul_args_of_result_bitvec x
        (__eo_list_concat_rec xs z) width (by simpa [mul, op] using hFirstTy)
      have hTail₂Ty := ih z₂ hTailList hParts.2 hZ₂Ty
      have hZ₂Ne : z₂ ≠ Term.Stuck := by
        intro h
        subst z₂
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) width at hZ₂Ty
        cases hZ₂Ty
      have hTail₂Ne : __eo_list_concat_rec xs z₂ ≠ Term.Stuck := by
        intro h
        rw [h] at hTail₂Ty
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) width at hTail₂Ty
        cases hTail₂Ty
      rw [list_concat_rec_cons_of_right_ne_stuck op x xs z₂ hZ₂Ne,
        mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTail₂Ne]
      change __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (__eo_list_concat_rec xs z₂)) = _
      rw [hParts.1, hTail₂Ty]
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        subst width
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) =
            Term.Apply (Term.UOp UserOp.BitVec) Term.Stuck at hFirstTy
        rw [hParts.1, hParts.2] at hFirstTy
        simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
          native_teq, native_not] at hFirstTy
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z₂ = z₂ := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hZ₂Ty

private theorem term_ne_stuck_of_is_list_true (f t : Term) :
    __eo_is_list f t = Term.Boolean true -> t ≠ Term.Stuck := by
  intro hList h
  subst t
  cases f <;> simp [__eo_is_list] at hList

private theorem is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil op t = Term.Boolean b := by
  intro hNe
  cases t <;>
    simp [op, __eo_is_list_nil, __eo_is_list_nil_bvmul, __eo_to_z,
      __eo_is_eq, native_and, native_not, native_teq, native_zeq] at hNe ⊢

private theorem list_singleton_elim_eo_type
    (c width : Term) :
    __eo_is_list op c = Term.Boolean true ->
    __eo_typeof c = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_singleton_elim op c) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hTy
  change __eo_typeof
      (__eo_requires (__eo_is_list op c) (Term.Boolean true)
        (__eo_list_singleton_elim_2 c)) = _
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg := eo_is_list_cons_head_eq_of_true op g head tail hList
          subst g
          have hParts := typeof_bvmul_args_of_result_bitvec head tail width
            (by simpa [mul, op] using hTy)
          have hTailList := eo_is_list_tail_true_of_cons_self op head tail hList
          have hTailNe := term_ne_stuck_of_is_list_true op tail hTailList
          rcases is_list_nil_boolean_of_ne_stuck tail hTailNe with ⟨b, hNil⟩
          cases b <;>
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq, hParts.1, hTy]
      | _ => simpa [__eo_list_singleton_elim_2] using hTy
  | _ => simpa [__eo_list_singleton_elim_2] using hTy

private theorem term_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : native_Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem bvmul_smt_type
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (mul x y)) = SmtType.BitVec w := by
  intro hXTy hYTy
  change __smtx_typeof
      (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [smtx_typeof_bvmul_term_eq_nary]
  simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_nateq, native_ite]

private theorem bvmul_args_of_smt_type
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt (mul x y)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w := by
  intro hTy
  have hNN : term_has_non_none_type
      (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    have hTy' :
        __smtx_typeof (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
          SmtType.BitVec w := by
      have hsimpa := hTy
      try simp [mul] at hsimpa ⊢
      exact hsimpa
    rw [hTy']
    simp
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvmul)
      (smtx_typeof_bvmul_term_eq_nary (__eo_to_smt x) (__eo_to_smt y)) hNN with
    ⟨actual, hXTy, hYTy⟩
  have hWidth : actual = w := by
    have hResult : SmtType.BitVec actual = SmtType.BitVec w := by
      have hTy' :
          __smtx_typeof (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
            SmtType.BitVec w := by
        have hsimpa := hTy
        try simp [mul] at hsimpa ⊢
        exact hsimpa
      rw [smtx_typeof_bvmul_term_eq_nary] at hTy'
      simpa [__smtx_typeof_bv_op_2, hXTy, hYTy, native_ite,
        native_nateq, SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst actual
  exact ⟨hXTy, hYTy⟩

private theorem list_concat_rec_smt_type
    (a z : Term) (w : Nat) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_is_list op z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec w := by
  intro hAList hZList hATy hZTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hAList
  | case2 a hA => simp [op, __eo_is_list] at hZList
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hXsList := eo_is_list_tail_true_of_cons_self op x xs hAList
      have hArgs := bvmul_args_of_smt_type x xs w (by
        simpa [mul, op] using hATy)
      have hTailTy := ih hXsList hZList hArgs.2 hZTy
      have hTailNe := term_ne_stuck_of_smt_bitvec_type hTailTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op x xs z hTailNe]
      exact bvmul_smt_type x (__eo_list_concat_rec xs z) w hArgs.1 hTailTy
  | case4 nil z hNil hZ hNot =>
      have hNilTrue : __eo_is_list_nil op nil = Term.Boolean true := by
        have hGet := eo_get_nil_rec_ne_stuck_of_is_list_true op nil hAList
        have hReq :
            __eo_requires (__eo_is_list_nil op nil) (Term.Boolean true) nil ≠
              Term.Stuck := by
          simpa [__eo_get_nil_rec] using hGet
        exact eo_requires_eq_of_ne_stuck (__eo_is_list_nil op nil)
          (Term.Boolean true) nil hReq
      rw [show __eo_list_concat_rec nil z = z by
        cases nil <;> cases z <;>
          simp [op, __eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
      exact hZTy

private theorem list_singleton_elim_smt_type
    (c : Term) (w : Nat) :
    __eo_is_list op c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_singleton_elim op c)) =
      SmtType.BitVec w := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list op c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c))) = _
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg := eo_is_list_cons_head_eq_of_true op g head tail hList
          subst g
          have hArgs := bvmul_args_of_smt_type head tail w
            (by simpa [mul, op] using hTy)
          have hTailList := eo_is_list_tail_true_of_cons_self op head tail hList
          have hTailNe := term_ne_stuck_of_is_list_true op tail hTailList
          rcases is_list_nil_boolean_of_ne_stuck tail hTailNe with ⟨b, hNil⟩
          cases b <;>
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq, hArgs.1, hTy]
      | _ => simpa [__eo_list_singleton_elim_2] using hTy
  | _ => simpa [__eo_list_singleton_elim_2] using hTy

private theorem list_smt_type_or_nil_of_concat_type
    (a z : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation a ->
    __eo_is_list op a = Term.Boolean true ->
    z ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    ListTypeOrNil a (native_int_to_nat W) := by
  intro hATrans hAList hZNe hConcatTy hW0
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hAList
  | case2 a hA => exact False.elim (hZNe rfl)
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro hTail
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          hTail, mk_apply_right_stuck_local] at hConcatTy
        cases hConcatTy
      rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
        mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe]
        at hConcatTy
      have hXTypeof :=
        (typeof_bvmul_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) (Term.Numeral W)
          (by simpa [mul, op] using hConcatTy)).1
      have hNonNone :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.BitVec (native_int_to_nat W) := by
        have hExpected :=
          RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
            x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
              (__eo_to_smt x) rfl
              (by
                intro hNone
                apply hATrans
                change __smtx_typeof
                    (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt xs)) =
                  SmtType.None
                rw [smtx_typeof_bvmul_term_eq_nary]
                simp [__smtx_typeof_bv_op_2, hNone, native_ite])
              hXTypeof
        simpa [__eo_to_smt_type, hW0, native_ite] using hExpected
      apply Or.inl
      change __smtx_typeof
          (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt xs)) = _
      rw [smtx_typeof_bvmul_term_eq_nary]
      have hXsExpected :
          __smtx_typeof (__eo_to_smt xs) =
            SmtType.BitVec (native_int_to_nat W) := by
        have hWhole :
            __smtx_typeof
                (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt xs)) ≠
              SmtType.None := by
          intro hNone
          exact hATrans hNone
        rcases bv_binop_args_of_non_none (op := SmtTerm.bvmul)
            (show
              __smtx_typeof
                  (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt xs)) =
                __smtx_typeof_bv_op_2
                  (__smtx_typeof (__eo_to_smt x))
                  (__smtx_typeof (__eo_to_smt xs)) by
              rw [smtx_typeof_bvmul_term_eq_nary]) hWhole with
          ⟨w, hXTy, hXsTy⟩
        rw [hNonNone] at hXTy
        cases hXTy
        exact hXsTy
      simp [__smtx_typeof_bv_op_2, hNonNone, hXsExpected,
        native_nateq, native_ite]
  | case4 nil z hNil hZ hNot =>
      apply Or.inr
      intro tail
      unfold __eo_list_concat_rec
      split <;> simp_all

private theorem smt_bitvec_type_of_eo_type
    (x : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hTrans hEoTy hW0
  have hExpected :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt x) rfl hTrans hEoTy
  simpa [__eo_to_smt_type, hW0, native_ite] using hExpected

theorem inferred_argument_types
    (xs ys z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (term xs ys z size n exponent u) = Term.Bool ->
    ∃ W : native_Int,
      size = Term.Numeral W ∧ native_zleq 0 W = true ∧
      ListTypeOrNil xs (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt ys) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt z) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __eo_typeof (base xs ys z) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __smtx_typeof (__eo_to_smt (base xs ys z)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __eo_typeof
          (simpleTerm xs ys z size n exponent u) =
        Term.Bool := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs ys z size n))
    (__eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u))
    (by have hsimpa := hTermTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
  have hLhsTailTyNe := list_concat_rec_right_type_ne_stuck xs
    (mul z (mul (bvMultPow2Const size n) ys)) hXsList hSides.1
  have hOuterNe :
      __eo_typeof_bvand (__eo_typeof z)
          (__eo_typeof (mul (bvMultPow2Const size n) ys)) ≠
        Term.Stuck := by
    have hsimpa := hLhsTailTyNe
    try simp [mul, op] at hsimpa ⊢
    exact hsimpa
  rcases BvXorOnesSupport.typeof_bvand_arg_types_of_ne_stuck hOuterNe with
    ⟨width, hZEoTy, hInnerEoTy⟩
  have hInnerParts := typeof_bvmul_args_of_result_bitvec
    (bvMultPow2Const size n) ys width hInnerEoTy
  have hSizeNe := RuleProofs.term_ne_stuck_of_has_smt_translation size hSizeTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  rcases bv_all_ones_const_context n size width hNNe hSizeNe
      (by simpa [bvMultPow2Const, bvAllOnesConst] using hInnerParts.1) with
    ⟨W, hSize, hWidth, hW0, hNEoTy⟩
  subst width
  subst size
  have hYEoTy :
      __eo_typeof ys =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := hInnerParts.2
  have hZEoTy' :
      __eo_typeof z =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := hZEoTy
  have hYTy := smt_bitvec_type_of_eo_type ys W hYsTrans hYEoTy hW0
  have hZTy := smt_bitvec_type_of_eo_type z W hZTrans hZEoTy' hW0
  have hNTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNEoTy
  have hLhsTy := list_concat_rec_result_type xs
    (mul z (mul (bvMultPow2Const (Term.Numeral W) n) ys))
    (Term.Numeral W) hXsList
    (by
      change __eo_typeof_bvand (__eo_typeof z)
        (__eo_typeof_bvand (__eo_typeof (bvMultPow2Const (Term.Numeral W) n))
          (__eo_typeof ys)) = _
      rw [hZEoTy', hInnerParts.1, hYEoTy]
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not]) hSides.1
  have hTailNe :
      mul z (mul (bvMultPow2Const (Term.Numeral W) n) ys) ≠ Term.Stuck := by
    simp [mul, op]
  have hXsType := list_smt_type_or_nil_of_concat_type xs
    (mul z (mul (bvMultPow2Const (Term.Numeral W) n) ys)) W
    hXsTrans hXsList hTailNe hLhsTy hW0
  have hBaseTailEoTy :
      __eo_typeof (mul z ys) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    change __eo_typeof_bvand (__eo_typeof z) (__eo_typeof ys) = _
    rw [hZEoTy', hYEoTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hBaseListEoTy :
      __eo_typeof (baseList xs ys z) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    unfold baseList
    exact list_concat_rec_replace_tail_type xs
      (mul z (mul (bvMultPow2Const (Term.Numeral W) n) ys))
      (mul z ys) (Term.Numeral W) hXsList hLhsTy hBaseTailEoTy
  have hZYsList : __eo_is_list op (mul z ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op z ys (by decide) hYsList
  have hBaseListList :
      __eo_is_list op (baseList xs ys z) = Term.Boolean true := by
    unfold baseList
    exact eo_list_concat_rec_is_list_true_of_lists op xs (mul z ys)
      hXsList hZYsList
  have hBaseEoTy :
      __eo_typeof (base xs ys z) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    unfold base
    exact list_singleton_elim_eo_type (baseList xs ys z)
      (Term.Numeral W) hBaseListList hBaseListEoTy
  have hZYsTy :
      __smtx_typeof (__eo_to_smt (mul z ys)) =
        SmtType.BitVec (native_int_to_nat W) :=
    bvmul_smt_type z ys (native_int_to_nat W) hZTy hYTy
  have hBaseListSmtTy :
      __smtx_typeof (__eo_to_smt (baseList xs ys z)) =
        SmtType.BitVec (native_int_to_nat W) := by
    rcases hXsType with hXsTy | hXsNil
    · unfold baseList
      exact list_concat_rec_smt_type xs (mul z ys) (native_int_to_nat W)
        hXsList hZYsList hXsTy hZYsTy
    · unfold baseList
      rw [hXsNil]
      exact hZYsTy
  have hBaseSmtTy :
      __smtx_typeof (__eo_to_smt (base xs ys z)) =
        SmtType.BitVec (native_int_to_nat W) := by
    unfold base
    exact list_singleton_elim_smt_type (baseList xs ys z)
      (native_int_to_nat W) hBaseListList hBaseListSmtTy
  have hRhsEoTy :
      __eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq
      (__eo_typeof (lhs xs ys z (Term.Numeral W) n))
      (__eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u))
      (by have hsimpa := hTermTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
    rw [show __eo_typeof (lhs xs ys z (Term.Numeral W) n) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) by
      simpa [lhs] using hLhsTy] at hTypeEq
    exact hTypeEq.symm
  have hSimpleLhsEoTy :
      __eo_typeof (simpleLhs xs ys z (Term.Numeral W) n) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    change __eo_typeof_bvand (__eo_typeof (base xs ys z))
      (__eo_typeof (bvMultPow2Const (Term.Numeral W) n)) = _
    rw [hBaseEoTy, hInnerParts.1]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hSimpleTy :
      __eo_typeof
          (simpleTerm xs ys z (Term.Numeral W) n exponent u) =
        Term.Bool := by
    change __eo_typeof_eq
      (__eo_typeof (simpleLhs xs ys z (Term.Numeral W) n))
      (__eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u)) = Term.Bool
    rw [hSimpleLhsEoTy, hRhsEoTy]
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  exact ⟨W, rfl, hW0, hXsType, hYTy, hZTy, hNTy, hBaseEoTy,
    hBaseSmtTy, hSimpleTy⟩

private theorem pos_term_type_implies_term_type
    (xs ys z size n exponent u : Term) :
    __eo_typeof (posTerm xs ys z size n exponent u) = Term.Bool ->
    __eo_typeof (term xs ys z size n exponent u) = Term.Bool := by
  intro hPosTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs ys z size n))
    (__eo_typeof
      (BvMultPow2PosSupport.bvMultPow2PosRhs
        (base xs ys z) exponent u))
    (by have hsimpa := hPosTy; (try simp [posTerm] at hsimpa ⊢); exact hsimpa)
  have hExtractNe :
      __eo_typeof (bvExtractTerm (base xs ys z) u (Term.Numeral 0)) ≠
        Term.Stuck := by
    intro h
    apply hSides.2
    change __eo_typeof_concat
        (__eo_typeof (bvExtractTerm (base xs ys z) u (Term.Numeral 0)))
        (__eo_typeof (bvMultPow2Zeros exponent)) = Term.Stuck
    rw [h]
    simp [__eo_typeof_concat]
  change __eo_typeof_extract (__eo_typeof u) u
      (Term.UOp UserOp.Int) (Term.Numeral 0)
      (__eo_typeof (base xs ys z)) ≠ Term.Stuck at hExtractNe
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hExtractNe with
    ⟨width, hBaseTy⟩
  have hNegBaseTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) (base xs ys z)) =
        __eo_typeof (base xs ys z) := by
    change __eo_typeof_bvnot (__eo_typeof (base xs ys z)) = _
    rw [hBaseTy]
    rfl
  have hRhsTyEq :
      __eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u) =
        __eo_typeof
          (BvMultPow2PosSupport.bvMultPow2PosRhs
            (base xs ys z) exponent u) := by
    unfold bvMultPow2Rhs BvMultPow2PosSupport.bvMultPow2PosRhs
      bvExtractTerm
    change __eo_typeof_concat
        (__eo_typeof_extract (__eo_typeof u) u
          (Term.UOp UserOp.Int) (Term.Numeral 0)
          (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) (base xs ys z))))
        (__eo_typeof (bvMultPow2Zeros exponent)) =
      __eo_typeof_concat
        (__eo_typeof_extract (__eo_typeof u) u
          (Term.UOp UserOp.Int) (Term.Numeral 0)
          (__eo_typeof (base xs ys z)))
        (__eo_typeof (bvMultPow2Zeros exponent))
    rw [hNegBaseTy]
  change __eo_typeof_eq (__eo_typeof (lhs xs ys z size n))
      (__eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u)) =
    Term.Bool
  rw [hRhsTyEq]
  have hsimpa := hPosTy
  try simp [posTerm] at hsimpa ⊢
  exact hsimpa

theorem inferred_pos_argument_types
    (xs ys z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (posTerm xs ys z size n exponent u) = Term.Bool ->
    ∃ W : native_Int,
      size = Term.Numeral W ∧ native_zleq 0 W = true ∧
      ListTypeOrNil xs (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt ys) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt z) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __eo_typeof (base xs ys z) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __smtx_typeof (__eo_to_smt (base xs ys z)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __eo_typeof (simplePosTerm xs ys z size n exponent u) =
        Term.Bool := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hPosTy
  have hTermTy := pos_term_type_implies_term_type xs ys z size n exponent u
    hPosTy
  rcases inferred_argument_types xs ys z size n exponent u hXsTrans
      hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hTermTy with
    ⟨W, hSize, hW0, hXsType, hYsTy, hZTy, hNTy, hBaseEoTy,
      hBaseSmtTy, hSimpleTy⟩
  have hNegBaseTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) (base xs ys z)) =
        __eo_typeof (base xs ys z) := by
    change __eo_typeof_bvnot (__eo_typeof (base xs ys z)) = _
    rw [hBaseEoTy]
    rfl
  have hRhsTyEq :
      __eo_typeof (bvMultPow2Rhs (base xs ys z) exponent u) =
        __eo_typeof
          (BvMultPow2PosSupport.bvMultPow2PosRhs
            (base xs ys z) exponent u) := by
    unfold bvMultPow2Rhs BvMultPow2PosSupport.bvMultPow2PosRhs
      bvExtractTerm
    change __eo_typeof_concat
        (__eo_typeof_extract (__eo_typeof u) u
          (Term.UOp UserOp.Int) (Term.Numeral 0)
          (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) (base xs ys z))))
        (__eo_typeof (bvMultPow2Zeros exponent)) =
      __eo_typeof_concat
        (__eo_typeof_extract (__eo_typeof u) u
          (Term.UOp UserOp.Int) (Term.Numeral 0)
          (__eo_typeof (base xs ys z)))
        (__eo_typeof (bvMultPow2Zeros exponent))
    rw [hNegBaseTy]
  have hSimplePosTy :
      __eo_typeof (simplePosTerm xs ys z size n exponent u) =
        Term.Bool := by
    change __eo_typeof_eq (__eo_typeof (simpleLhs xs ys z size n))
      (__eo_typeof
        (BvMultPow2PosSupport.bvMultPow2PosRhs
          (base xs ys z) exponent u)) = Term.Bool
    rw [← hRhsTyEq]
    have hsimpa := hSimpleTy
    try simp [simpleTerm] at hsimpa ⊢
    exact hsimpa
  exact ⟨W, hSize, hW0, hXsType, hYsTy, hZTy, hNTy, hBaseEoTy,
    hBaseSmtTy, hSimplePosTy⟩

private theorem emod_mul_left_congr_local
    (a b m : native_Int) :
    ((a % m) * b) % m = (a * b) % m := by
  rw [Int.mul_emod, Int.emod_emod]
  exact (Int.mul_emod a b m).symm

private theorem emod_mul_right_congr_local
    (a b m : native_Int) :
    (a * (b % m)) % m = (a * b) % m := by
  rw [Int.mul_comm a, Int.mul_comm a]
  exact emod_mul_left_congr_local b a m

private theorem eval_mul_assoc
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (mul (mul x y) z)) =
      __smtx_model_eval M (__eo_to_smt (mul x (mul y z))) := by
  intro hXTy hYTy hZTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, _hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, _hYCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z) w hZTy with
    ⟨nz, hZEval, _hZCan⟩
  change __smtx_model_eval_bvmul
      (__smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)))
      (__smtx_model_eval M (__eo_to_smt z)) =
    __smtx_model_eval_bvmul
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt z)))
  rw [hXEval, hYEval, hZEval]
  change SmtValue.Binary (native_nat_to_int w)
      (native_mod_total
        (native_zmult
          (native_mod_total (native_zmult nx ny)
            (native_int_pow2 (native_nat_to_int w))) nz)
        (native_int_pow2 (native_nat_to_int w))) =
    SmtValue.Binary (native_nat_to_int w)
      (native_mod_total
        (native_zmult nx
          (native_mod_total (native_zmult ny nz)
            (native_int_pow2 (native_nat_to_int w))))
        (native_int_pow2 (native_nat_to_int w)))
  have hPayload :
      native_mod_total
          (native_zmult
            (native_mod_total (native_zmult nx ny)
              (native_int_pow2 (native_nat_to_int w))) nz)
          (native_int_pow2 (native_nat_to_int w)) =
        native_mod_total
          (native_zmult nx
            (native_mod_total (native_zmult ny nz)
              (native_int_pow2 (native_nat_to_int w))))
          (native_int_pow2 (native_nat_to_int w)) := by
    unfold native_mod_total native_zmult
    calc
      (((nx * ny) % native_int_pow2 (native_nat_to_int w)) * nz) %
          native_int_pow2 (native_nat_to_int w) =
        ((nx * ny) * nz) % native_int_pow2 (native_nat_to_int w) :=
          emod_mul_left_congr_local _ _ _
      _ = (nx * (ny * nz)) % native_int_pow2 (native_nat_to_int w) := by
        rw [Int.mul_assoc]
      _ = (nx * ((ny * nz) % native_int_pow2 (native_nat_to_int w))) %
          native_int_pow2 (native_nat_to_int w) :=
        (emod_mul_right_congr_local _ _ _).symm
  rw [hPayload]

private theorem eval_mul_comm
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (mul x y)) =
      __smtx_model_eval M (__eo_to_smt (mul y x)) := by
  intro hXTy hYTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, _hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, _hYCan⟩
  change __smtx_model_eval_bvmul
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
    __smtx_model_eval_bvmul
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt x))
  rw [hXEval, hYEval]
  simp [__smtx_model_eval_bvmul, native_zmult, Int.mul_comm]

private theorem eval_mul_rotate
    (M : SmtModel) (hM : model_wf M)
    (x c y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (mul x (mul c y))) =
      __smtx_model_eval M (__eo_to_smt (mul (mul x y) c)) := by
  intro hXTy hCTy hYTy
  calc
    __smtx_model_eval M (__eo_to_smt (mul x (mul c y))) =
        __smtx_model_eval M (__eo_to_smt (mul x (mul y c))) := by
      change __smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt (mul c y))) =
        __smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt (mul y c)))
      rw [eval_mul_comm M hM c y w hCTy hYTy]
    _ = __smtx_model_eval M (__eo_to_smt (mul (mul x y) c)) :=
      (eval_mul_assoc M hM x y c w hXTy hYTy hCTy).symm

private theorem nil_payload_eq_one
    (M : SmtModel) (nil : Term) (w : Nat) (n : Int) :
    __eo_is_list_nil op nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.Binary (native_nat_to_int w) n ->
    n = 1 := by
  intro hNilTrue hNilEval
  cases nil <;>
    simp [op, __eo_is_list_nil, __eo_is_list_nil_bvmul, __eo_to_z,
      __eo_is_eq, native_and, native_not, SmtEval.native_not, native_teq,
      native_zeq] at hNilTrue
  case Numeral z =>
    rw [show __eo_to_smt (Term.Numeral z) = SmtTerm.Numeral z by rfl] at hNilEval
    rw [__smtx_model_eval] at hNilEval
    cases hNilEval
  case Rational q =>
    rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl] at hNilEval
    rw [__smtx_model_eval] at hNilEval
    cases hNilEval
  case String s =>
    rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl] at hNilEval
    rw [__smtx_model_eval] at hNilEval
    cases hNilEval
  case Binary wb nb =>
    have hEvalEq :
        SmtValue.Binary wb nb =
          SmtValue.Binary (native_nat_to_int w) n := by
      rw [show __eo_to_smt (Term.Binary wb nb) =
          SmtTerm.Binary wb nb by rfl] at hNilEval
      rw [__smtx_model_eval] at hNilEval
      exact hNilEval
    injection hEvalEq with hWidthEq hPayloadEq
    subst wb
    subst n
    exact hNilTrue.symm

private theorem eval_mul_right_one
    (M : SmtModel) (hM : model_wf M)
    (x nil : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    __eo_is_list_nil op nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt (mul x nil)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hXTy hNilTy hNil
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt nil) w hNilTy with
    ⟨nnil, hNilEval, _hNilCan⟩
  have hNilOne := nil_payload_eq_one M nil w nnil hNil hNilEval
  subst nnil
  have hMod : native_mod_total nx
      (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq : nx = native_mod_total nx
        (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hXCan
    exact hEq.symm
  change __smtx_model_eval_bvmul
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt nil)) =
    __smtx_model_eval M (__eo_to_smt x)
  rw [hXEval, hNilEval]
  simp [__smtx_model_eval_bvmul, native_zmult, hMod]

private theorem eval_mul_left_one
    (M : SmtModel) (hM : model_wf M)
    (nil x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list_nil op nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt (mul nil x)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hNilTy hXTy hNil
  rw [eval_mul_comm M hM nil x w hNilTy hXTy]
  exact eval_mul_right_one M hM x nil w hXTy hNilTy hNil

private theorem list_concat_rec_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (w : Nat) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_is_list op z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)) =
      __smtx_model_eval M (__eo_to_smt (mul a z)) := by
  intro hAList hZList hATy hZTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hAList
  | case2 a hA => simp [op, __eo_is_list] at hZList
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hXsList := eo_is_list_tail_true_of_cons_self op x xs hAList
      have hArgs := bvmul_args_of_smt_type x xs w (by
        simpa [mul, op] using hATy)
      have hTailTy := list_concat_rec_smt_type xs z w
        hXsList hZList hArgs.2 hZTy
      have hTailNe := term_ne_stuck_of_smt_bitvec_type hTailTy
      have hIH := ih hXsList hZList hArgs.2 hZTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op x xs z hTailNe]
      calc
        __smtx_model_eval M
            (__eo_to_smt (mul x (__eo_list_concat_rec xs z))) =
          __smtx_model_eval M (__eo_to_smt (mul x (mul xs z))) := by
            change __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt x))
                (__smtx_model_eval M
                  (__eo_to_smt (__eo_list_concat_rec xs z))) =
              __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt x))
                (__smtx_model_eval M (__eo_to_smt (mul xs z)))
            rw [hIH]
        _ = __smtx_model_eval M (__eo_to_smt (mul (mul x xs) z)) :=
          (eval_mul_assoc M hM x xs z w hArgs.1 hArgs.2 hZTy).symm
  | case4 nil z hNil hZNe hNot =>
      have hNilTrue : __eo_is_list_nil op nil = Term.Boolean true := by
        have hGet := eo_get_nil_rec_ne_stuck_of_is_list_true op nil hAList
        have hReq :
            __eo_requires (__eo_is_list_nil op nil) (Term.Boolean true) nil ≠
              Term.Stuck := by
          simpa [__eo_get_nil_rec] using hGet
        exact eo_requires_eq_of_ne_stuck (__eo_is_list_nil op nil)
          (Term.Boolean true) nil hReq
      rw [show __eo_list_concat_rec nil z = z by
        cases nil <;> cases z <;>
          simp [op, __eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
      exact (eval_mul_left_one M hM nil z w hATy hZTy hNilTrue).symm

private theorem list_singleton_elim_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (c : Term) (w : Nat) :
    __eo_is_list op c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim op c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hList hTy
  change __smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list op c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c))) =
    __smtx_model_eval M (__eo_to_smt c)
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg := eo_is_list_cons_head_eq_of_true op g head tail hList
          subst g
          have hArgs := bvmul_args_of_smt_type head tail w (by
            simpa [mul, op] using hTy)
          have hTailList := eo_is_list_tail_true_of_cons_self op head tail hList
          have hTailNe := term_ne_stuck_of_is_list_true op tail hTailList
          rcases is_list_nil_boolean_of_ne_stuck tail hTailNe with ⟨b, hNil⟩
          cases b
          · simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq]
          · simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq]
            exact (eval_mul_right_one M hM head tail w hArgs.1 hArgs.2 hNil).symm
      | _ => simpa [__eo_list_singleton_elim_2]
  | _ => simpa [__eo_list_singleton_elim_2]

private theorem eval_lhs_eq_simple_lhs
    (M : SmtModel) (hM : model_wf M)
    (xs ys z n : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    ListTypeOrNil xs (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt ys) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt z) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __smtx_model_eval M
        (__eo_to_smt (lhs xs ys z (Term.Numeral W) n)) =
      __smtx_model_eval M
        (__eo_to_smt (simpleLhs xs ys z (Term.Numeral W) n)) := by
  intro hW0 hXsType hYsTy hZTy hNTy hXsList hYsList
  let width := native_int_to_nat W
  let c := bvMultPow2Const (Term.Numeral W) n
  have hCTy :
      __smtx_typeof (__eo_to_smt c) = SmtType.BitVec width := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hNTy]
    simp [width, __smtx_typeof_int_to_bv, native_ite, hW0]
  have hCYsTy :
      __smtx_typeof (__eo_to_smt (mul c ys)) = SmtType.BitVec width :=
    bvmul_smt_type c ys width hCTy (by simpa [width] using hYsTy)
  have hTailTy :
      __smtx_typeof (__eo_to_smt (mul z (mul c ys))) =
        SmtType.BitVec width :=
    bvmul_smt_type z (mul c ys) width (by simpa [width] using hZTy) hCYsTy
  have hZYsTy :
      __smtx_typeof (__eo_to_smt (mul z ys)) = SmtType.BitVec width :=
    bvmul_smt_type z ys width (by simpa [width] using hZTy)
      (by simpa [width] using hYsTy)
  have hCYsList : __eo_is_list op (mul c ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op c ys (by decide) hYsList
  have hTailList :
      __eo_is_list op (mul z (mul c ys)) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op z (mul c ys) (by decide)
      hCYsList
  have hZYsList : __eo_is_list op (mul z ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op z ys (by decide) hYsList
  have hBaseListList :
      __eo_is_list op (baseList xs ys z) = Term.Boolean true := by
    unfold baseList
    exact eo_list_concat_rec_is_list_true_of_lists op xs (mul z ys)
      hXsList hZYsList
  have hBaseListTy :
      __smtx_typeof (__eo_to_smt (baseList xs ys z)) =
        SmtType.BitVec width := by
    rcases hXsType with hXsTy | hXsNil
    · unfold baseList
      exact list_concat_rec_smt_type xs (mul z ys) width hXsList hZYsList
        hXsTy hZYsTy
    · unfold baseList
      rw [hXsNil]
      exact hZYsTy
  have hBaseElim := list_singleton_elim_eval_eq M hM
    (baseList xs ys z) width hBaseListList hBaseListTy
  have hBaseElim' :
      __smtx_model_eval M (__eo_to_smt (base xs ys z)) =
        __smtx_model_eval M (__eo_to_smt (baseList xs ys z)) := by
    simpa [base] using hBaseElim
  rcases hXsType with hXsTy | hXsNil
  · have hOrigConcat := list_concat_rec_eval_eq M hM xs
      (mul z (mul c ys)) width hXsList hTailList hXsTy hTailTy
    have hBaseConcat := list_concat_rec_eval_eq M hM xs (mul z ys)
      width hXsList hZYsList hXsTy hZYsTy
    have hBaseConcat' :
        __smtx_model_eval M (__eo_to_smt (baseList xs ys z)) =
          __smtx_model_eval M (__eo_to_smt (mul xs (mul z ys))) := by
      simpa [baseList] using hBaseConcat
    have hRotate := eval_mul_rotate M hM z c ys width
      (by simpa [width] using hZTy) hCTy (by simpa [width] using hYsTy)
    have hAssoc := eval_mul_assoc M hM xs (mul z ys) c width
      hXsTy hZYsTy hCTy
    simp only [lhs, simpleLhs, c] at hOrigConcat ⊢
    rw [hOrigConcat]
    calc
      __smtx_model_eval M
          (__eo_to_smt (mul xs (mul z (mul c ys)))) =
        __smtx_model_eval M
          (__eo_to_smt (mul xs (mul (mul z ys) c))) := by
            change __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt xs))
                (__smtx_model_eval M (__eo_to_smt (mul z (mul c ys)))) =
              __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt xs))
                (__smtx_model_eval M (__eo_to_smt (mul (mul z ys) c)))
            rw [hRotate]
      _ = __smtx_model_eval M
          (__eo_to_smt (mul (mul xs (mul z ys)) c)) := hAssoc.symm
      _ = __smtx_model_eval M
          (__eo_to_smt (mul (baseList xs ys z) c)) := by
            change __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt (mul xs (mul z ys))))
                (__smtx_model_eval M (__eo_to_smt c)) =
              __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt (baseList xs ys z)))
                (__smtx_model_eval M (__eo_to_smt c))
            rw [← hBaseConcat']
      _ = __smtx_model_eval M
          (__eo_to_smt (mul (base xs ys z) c)) := by
            change __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt (baseList xs ys z)))
                (__smtx_model_eval M (__eo_to_smt c)) =
              __smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt (base xs ys z)))
                (__smtx_model_eval M (__eo_to_smt c))
            rw [← hBaseElim']
  · have hRotate := eval_mul_rotate M hM z c ys width
      (by simpa [width] using hZTy) hCTy (by simpa [width] using hYsTy)
    simp only [lhs, simpleLhs, base, baseList, c]
    rw [hXsNil, hXsNil]
    change __smtx_model_eval M (__eo_to_smt (mul z (mul c ys))) =
      __smtx_model_eval M
        (__eo_to_smt
          (mul (__eo_list_singleton_elim op (mul z ys)) c))
    rw [hRotate]
    change __smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt (mul z ys)))
        (__smtx_model_eval M (__eo_to_smt c)) =
      __smtx_model_eval_bvmul
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim op (mul z ys))))
        (__smtx_model_eval M (__eo_to_smt c))
    simpa [base, baseList, hXsNil] using congrArg
      (fun v => __smtx_model_eval_bvmul v
        (__smtx_model_eval M (__eo_to_smt c))) hBaseElim'.symm

theorem typed_term
    (xs ys z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (term xs ys z size n exponent u) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term xs ys z size n exponent u) := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hXsList hYsList hTermTy
  rcases inferred_argument_types xs ys z size n exponent u hXsTrans
      hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hTermTy with
    ⟨W, rfl, hW0, hXsType, hYsTy, hZTy, hNTy, _hBaseEoTy,
      hBaseTy, hSimpleTy⟩
  let width := native_int_to_nat W
  let c := bvMultPow2Const (Term.Numeral W) n
  have hBaseTrans : RuleProofs.eo_has_smt_translation (base xs ys z) := by
    intro hNone
    rw [hNone] at hBaseTy
    cases hBaseTy
  have hDirectBool :
      RuleProofs.eo_has_bool_type
        (bvMultPow2DirectTerm (base xs ys z) (Term.Numeral W) n exponent u) :=
    typed_bv_mult_pow2_direct_term (base xs ys z) (Term.Numeral W) n exponent u
      hBaseTrans hSizeTrans hNTrans hExponentTrans
      (by simpa [simpleTerm, simpleLhs, bvMultPow2DirectTerm,
          bvMultPow2DirectLhs, mul, op] using hSimpleTy)
  have hDirectSides := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (bvMultPow2DirectLhs (base xs ys z) (Term.Numeral W) n)
    (bvMultPow2Rhs (base xs ys z) exponent u) hDirectBool
  have hCTy :
      __smtx_typeof (__eo_to_smt c) = SmtType.BitVec width := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hNTy]
    simp [width, __smtx_typeof_int_to_bv, native_ite, hW0]
  have hCYsTy :
      __smtx_typeof (__eo_to_smt (mul c ys)) = SmtType.BitVec width :=
    bvmul_smt_type c ys width hCTy (by simpa [width] using hYsTy)
  have hTailTy :
      __smtx_typeof (__eo_to_smt (mul z (mul c ys))) =
        SmtType.BitVec width :=
    bvmul_smt_type z (mul c ys) width (by simpa [width] using hZTy) hCYsTy
  have hCYsList : __eo_is_list op (mul c ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op c ys (by decide) hYsList
  have hTailList :
      __eo_is_list op (mul z (mul c ys)) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op z (mul c ys) (by decide)
      hCYsList
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (lhs xs ys z (Term.Numeral W) n)) =
        SmtType.BitVec width := by
    rcases hXsType with hXsTy | hXsNil
    · unfold lhs
      exact list_concat_rec_smt_type xs (mul z (mul c ys)) width
        hXsList hTailList hXsTy hTailTy
    · unfold lhs
      rw [hXsNil]
      exact hTailTy
  have hDirectLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2DirectLhs (base xs ys z) (Term.Numeral W) n)) =
        SmtType.BitVec width := by
    change __smtx_typeof (__eo_to_smt (mul (base xs ys z) c)) = _
    exact bvmul_smt_type (base xs ys z) c width
      (by simpa [width] using hBaseTy) hCTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (bvMultPow2Rhs (base xs ys z) exponent u)) =
        SmtType.BitVec width := by
    rw [← hDirectSides.1]
    exact hDirectLhsTy
  unfold term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

theorem facts_term
    (M : SmtModel) (hM : model_wf M)
    (xs ys z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (term xs ys z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2IspowPrem size n) true ->
    eo_interprets M (bvMultPow2ExponentPrem size n exponent) true ->
    eo_interprets M (bvMultPow2UpperPrem size n u) true ->
    eo_interprets M (term xs ys z size n exponent u) true := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hXsList hYsList hTermTy hIspPrem hExponentPrem _hUpperPrem
  have hBool := typed_term xs ys z size n exponent u hXsTrans hYsTrans
    hZTrans hSizeTrans hNTrans hExponentTrans hXsList hYsList hTermTy
  rcases inferred_argument_types xs ys z size n exponent u hXsTrans
      hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hTermTy with
    ⟨W, rfl, hW0, hXsType, hYsTy, hZTy, hNTy, _hBaseEoTy,
      hBaseTy, hSimpleTy⟩
  have hBaseTrans : RuleProofs.eo_has_smt_translation (base xs ys z) := by
    intro hNone
    rw [hNone] at hBaseTy
    cases hBaseTy
  have hDirectEval := eval_bv_mult_pow2_direct M hM (base xs ys z)
    (Term.Numeral W) n exponent u hBaseTrans hSizeTrans hNTrans
    hExponentTrans
    (by simpa [simpleTerm, simpleLhs, bvMultPow2DirectTerm,
        bvMultPow2DirectLhs, mul, op] using hSimpleTy)
    (by simpa using hIspPrem) (by simpa using hExponentPrem)
  have hLhsEval := eval_lhs_eq_simple_lhs M hM xs ys z n W hW0
    hXsType hYsTy hZTy hNTy hXsList hYsList
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (lhs xs ys z (Term.Numeral W) n)))
      (__smtx_model_eval M
        (__eo_to_smt (bvMultPow2Rhs (base xs ys z) exponent u)))
    rw [hLhsEval]
    have hDirectEval' :
        __smtx_model_eval M
            (__eo_to_smt
              (simpleLhs xs ys z (Term.Numeral W) n)) =
          __smtx_model_eval M
            (__eo_to_smt (bvMultPow2Rhs (base xs ys z) exponent u)) := by
      simpa [simpleLhs, bvMultPow2DirectLhs, mul, op] using hDirectEval
    rw [hDirectEval']
    exact RuleProofs.smt_value_rel_refl _

theorem typed_pos_term
    (xs ys z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (posTerm xs ys z size n exponent u) = Term.Bool ->
    RuleProofs.eo_has_bool_type (posTerm xs ys z size n exponent u) := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hXsList hYsList hTermTy
  rcases inferred_pos_argument_types xs ys z size n exponent u hXsTrans
      hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hTermTy with
    ⟨W, rfl, hW0, hXsType, hYsTy, hZTy, hNTy, _hBaseEoTy,
      hBaseTy, hSimpleTy⟩
  let width := native_int_to_nat W
  let c := bvMultPow2Const (Term.Numeral W) n
  have hBaseTrans : RuleProofs.eo_has_smt_translation (base xs ys z) := by
    intro hNone
    rw [hNone] at hBaseTy
    cases hBaseTy
  have hDirectBool := BvMultPow2PosSupport.typed_direct_term
    (base xs ys z) (Term.Numeral W) n exponent u hBaseTrans hSizeTrans
    hNTrans hExponentTrans hSimpleTy
  have hDirectSides := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (bvMultPow2DirectLhs (base xs ys z) (Term.Numeral W) n)
    (BvMultPow2PosSupport.bvMultPow2PosRhs
      (base xs ys z) exponent u) hDirectBool
  have hCTy :
      __smtx_typeof (__eo_to_smt c) = SmtType.BitVec width := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hNTy]
    simp [width, __smtx_typeof_int_to_bv, native_ite, hW0]
  have hCYsTy :
      __smtx_typeof (__eo_to_smt (mul c ys)) = SmtType.BitVec width :=
    bvmul_smt_type c ys width hCTy (by simpa [width] using hYsTy)
  have hTailTy :
      __smtx_typeof (__eo_to_smt (mul z (mul c ys))) =
        SmtType.BitVec width :=
    bvmul_smt_type z (mul c ys) width (by simpa [width] using hZTy) hCYsTy
  have hCYsList : __eo_is_list op (mul c ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op c ys (by decide) hYsList
  have hTailList :
      __eo_is_list op (mul z (mul c ys)) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op z (mul c ys) (by decide)
      hCYsList
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (lhs xs ys z (Term.Numeral W) n)) =
        SmtType.BitVec width := by
    rcases hXsType with hXsTy | hXsNil
    · unfold lhs
      exact list_concat_rec_smt_type xs (mul z (mul c ys)) width
        hXsList hTailList hXsTy hTailTy
    · unfold lhs
      rw [hXsNil]
      exact hTailTy
  have hDirectLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2DirectLhs (base xs ys z) (Term.Numeral W) n)) =
        SmtType.BitVec width := by
    change __smtx_typeof (__eo_to_smt (mul (base xs ys z) c)) = _
    exact bvmul_smt_type (base xs ys z) c width
      (by simpa [width] using hBaseTy) hCTy
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (BvMultPow2PosSupport.bvMultPow2PosRhs
              (base xs ys z) exponent u)) = SmtType.BitVec width := by
    rw [← hDirectSides.1]
    exact hDirectLhsTy
  unfold posTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

theorem facts_pos_term
    (M : SmtModel) (hM : model_wf M)
    (xs ys z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (posTerm xs ys z size n exponent u) = Term.Bool ->
    eo_interprets M (BvMultPow2PosSupport.bvMultPow2PosIspowPrem n) true ->
    eo_interprets M
      (BvMultPow2PosSupport.bvMultPow2PosExponentPrem n exponent) true ->
    eo_interprets M
      (BvMultPow2PosSupport.bvMultPow2PosUpperPrem size n u) true ->
    eo_interprets M (posTerm xs ys z size n exponent u) true := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hXsList hYsList hTermTy hIspPrem hExponentPrem _hUpperPrem
  have hBool := typed_pos_term xs ys z size n exponent u hXsTrans
    hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hXsList hYsList hTermTy
  rcases inferred_pos_argument_types xs ys z size n exponent u hXsTrans
      hYsTrans hZTrans hSizeTrans hNTrans hXsList hYsList hTermTy with
    ⟨W, rfl, hW0, hXsType, hYsTy, hZTy, hNTy, _hBaseEoTy,
      hBaseTy, hSimpleTy⟩
  have hBaseTrans : RuleProofs.eo_has_smt_translation (base xs ys z) := by
    intro hNone
    rw [hNone] at hBaseTy
    cases hBaseTy
  have hDirectEval := BvMultPow2PosSupport.eval_direct M hM (base xs ys z)
    (Term.Numeral W) n exponent u hBaseTrans hSizeTrans hNTrans
    hExponentTrans hSimpleTy (by simpa using hIspPrem)
    (by simpa using hExponentPrem)
  have hLhsEval := eval_lhs_eq_simple_lhs M hM xs ys z n W hW0
    hXsType hYsTy hZTy hNTy hXsList hYsList
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (lhs xs ys z (Term.Numeral W) n)))
      (__smtx_model_eval M
        (__eo_to_smt
          (BvMultPow2PosSupport.bvMultPow2PosRhs
            (base xs ys z) exponent u)))
    rw [hLhsEval]
    have hDirectEval' :
        __smtx_model_eval M
            (__eo_to_smt (simpleLhs xs ys z (Term.Numeral W) n)) =
          __smtx_model_eval M
            (__eo_to_smt
              (BvMultPow2PosSupport.bvMultPow2PosRhs
                (base xs ys z) exponent u)) := by
      simpa [simpleLhs, bvMultPow2DirectLhs, mul, op] using hDirectEval
    rw [hDirectEval']
    exact RuleProofs.smt_value_rel_refl _

theorem typed_program
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (program xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (program xs ys z size n exponent u P1 P2 P3) := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProgramTy
  rcases program_eq_term_of_type_bool xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProgramTy with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hLists := program_lists_of_type_bool xs ys z size n exponent u P1 P2 P3
    hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
    hProgramTy
  have hTermTy :
      __eo_typeof (term xs ys z size n exponent u) = Term.Bool := by
    rw [← hProgramEq]
    exact hProgramTy
  rw [hProgramEq]
  exact typed_term xs ys z size n exponent u hXsTrans hYsTrans hZTrans
    hSizeTrans hNTrans hExponentTrans hLists.1 hLists.2 hTermTy

theorem facts_program
    (M : SmtModel) (hM : model_wf M)
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (program xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M (program xs ys z size n exponent u P1 P2 P3) true := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProgramTy hP1True hP2True hP3True
  rcases program_eq_term_of_type_bool xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProgramTy with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hLists := program_lists_of_type_bool xs ys z size n exponent u P1 P2 P3
    hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
    hProgramTy
  have hTermTy :
      __eo_typeof (term xs ys z size n exponent u) = Term.Bool := by
    rw [← hProgramEq]
    exact hProgramTy
  have hIspPrem : eo_interprets M (bvMultPow2IspowPrem size n) true := by
    simpa [hP1] using hP1True
  have hExponentPrem :
      eo_interprets M (bvMultPow2ExponentPrem size n exponent) true := by
    simpa [hP2] using hP2True
  have hUpperPrem :
      eo_interprets M (bvMultPow2UpperPrem size n u) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_term M hM xs ys z size n exponent u hXsTrans hYsTrans
    hZTrans hSizeTrans hNTrans hExponentTrans hLists.1 hLists.2 hTermTy
    hIspPrem hExponentPrem hUpperPrem

private def guardedPosExtract (xs ys z u : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract u (Term.Numeral 0))
    (guardedBase xs ys z)

private def guardedPosRhs (xs ys z exponent u : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.concat)
      (guardedPosExtract xs ys z u))
    (bvMultPow2Zeros exponent)

private def posSkeleton
    (xs ys z size n exponent u : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys z size n))
    (guardedPosRhs xs ys z exponent u)

def posProgram
    (xs ys z size n exponent u P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_mult_pow2_1 xs ys z size n exponent u
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

def posUpperPremRefs (size n u : Term) : Term :=
  BvMultPow2PosSupport.bvMultPow2PosUpperPrem size n u

private def posGuard
    (size n exponent u nRef1 exponentRef nRef2 uRef sizeRef nRef3 : Term) :
    Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and (__eo_eq n nRef1) (__eo_eq exponent exponentRef))
          (__eo_eq n nRef2))
        (__eo_eq u uRef))
      (__eo_eq size sizeRef))
    (__eo_eq n nRef3)

private theorem pos_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h |-
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h |-

private theorem pos_guard_refs
    {size n exponent u nRef1 exponentRef nRef2 uRef sizeRef nRef3 body : Term} :
    __eo_requires
        (posGuard size n exponent u nRef1 exponentRef nRef2 uRef sizeRef nRef3)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nRef1 = n ∧ exponentRef = exponent ∧ nRef2 = n ∧ uRef = u ∧
      sizeRef = size ∧ nRef3 = n := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold posGuard at hGuard
  rcases pos_and_true hGuard with ⟨hG5, hN3⟩
  rcases pos_and_true hG5 with ⟨hG4, hSize⟩
  rcases pos_and_true hG4 with ⟨hG3, hU⟩
  rcases pos_and_true hG3 with ⟨hG2, hN2⟩
  rcases pos_and_true hG2 with ⟨hN1, hExponent⟩
  exact ⟨support_eq_of_eo_eq_true n nRef1 hN1,
    support_eq_of_eo_eq_true exponent exponentRef hExponent,
    support_eq_of_eo_eq_true n nRef2 hN2,
    support_eq_of_eo_eq_true u uRef hU,
    support_eq_of_eo_eq_true size sizeRef hSize,
    support_eq_of_eo_eq_true n nRef3 hN3⟩

private theorem pos_premise_shape
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> z ≠ Term.Stuck ->
    size ≠ Term.Stuck -> n ≠ Term.Stuck -> exponent ≠ Term.Stuck ->
    u ≠ Term.Stuck ->
    posProgram xs ys z size n exponent u P1 P2 P3 ≠ Term.Stuck ->
    ∃ nRef1 exponentRef nRef2 uRef sizeRef nRef3,
      P1 = BvMultPow2PosSupport.bvMultPow2PosIspowPrem nRef1 ∧
      P2 = BvMultPow2PosSupport.bvMultPow2PosExponentPrem nRef2 exponentRef ∧
      P3 = posUpperPremRefs sizeRef nRef3 uRef := by
  intro hXs hYs hZ hSize hN hExponent hU hProg
  by_cases hShape :
      ∃ nRef1 exponentRef nRef2 uRef sizeRef nRef3,
        P1 = BvMultPow2PosSupport.bvMultPow2PosIspowPrem nRef1 ∧
        P2 = BvMultPow2PosSupport.bvMultPow2PosExponentPrem nRef2 exponentRef ∧
        P3 = posUpperPremRefs sizeRef nRef3 uRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_mult_pow2_1.eq_9 xs ys z size n exponent u
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hXs hYs hZ hSize hN hExponent hU (by
        intro nRef1 exponentRef nRef2 uRef sizeRef nRef3 hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨nRef1, exponentRef, nRef2, uRef, sizeRef, nRef3,
            rfl, rfl, rfl⟩)

private theorem pos_program_canonical
    (xs ys z size n exponent u : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> z ≠ Term.Stuck ->
    size ≠ Term.Stuck -> n ≠ Term.Stuck -> exponent ≠ Term.Stuck ->
    u ≠ Term.Stuck ->
    posProgram xs ys z size n exponent u
        (BvMultPow2PosSupport.bvMultPow2PosIspowPrem n)
        (BvMultPow2PosSupport.bvMultPow2PosExponentPrem n exponent)
        (BvMultPow2PosSupport.bvMultPow2PosUpperPrem size n u) =
      posSkeleton xs ys z size n exponent u := by
  intro hXs hYs hZ hSize hN hExponent hU
  unfold posProgram BvMultPow2PosSupport.bvMultPow2PosIspowPrem
    BvMultPow2PosSupport.bvMultPow2PosExponentPrem
    BvMultPow2PosSupport.bvMultPow2PosUpperPrem
  rw [__eo_prog_bv_mult_pow2_1.eq_8 xs ys z size n exponent u
    n exponent n u size n hXs hYs hZ hSize hN hExponent hU]
  simp [posSkeleton, guardedLhs, guardedPosRhs, guardedPosExtract,
    guardedBase, mul, op, bvMultPow2Const, bvMultPow2Zeros, __eo_requires,
    __eo_and, __eo_eq, native_ite, native_teq, native_not, native_and,
    hXs, hYs, hZ, hSize, hN, hExponent, hU]

private theorem pos_program_normalize
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    posProgram xs ys z size n exponent u P1 P2 P3 ≠ Term.Stuck ->
    P1 = BvMultPow2PosSupport.bvMultPow2PosIspowPrem n ∧
      P2 = BvMultPow2PosSupport.bvMultPow2PosExponentPrem n exponent ∧
      P3 = BvMultPow2PosSupport.bvMultPow2PosUpperPrem size n u ∧
      posProgram xs ys z size n exponent u P1 P2 P3 =
        posSkeleton xs ys z size n exponent u := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hSize := RuleProofs.term_ne_stuck_of_has_smt_translation size hSizeTrans
  have hN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hExponent :=
    RuleProofs.term_ne_stuck_of_has_smt_translation exponent hExponentTrans
  have hU := RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
  rcases pos_premise_shape xs ys z size n exponent u P1 P2 P3
      hXs hYs hZ hSize hN hExponent hU hProg with
    ⟨nRef1, exponentRef, nRef2, uRef, sizeRef, nRef3, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold posProgram BvMultPow2PosSupport.bvMultPow2PosIspowPrem
    BvMultPow2PosSupport.bvMultPow2PosExponentPrem posUpperPremRefs
    BvMultPow2PosSupport.bvMultPow2PosUpperPrem at hReq
  rw [__eo_prog_bv_mult_pow2_1.eq_8 xs ys z size n exponent u
    nRef1 exponentRef nRef2 uRef sizeRef nRef3
    hXs hYs hZ hSize hN hExponent hU] at hReq
  rcases pos_guard_refs
      (size := size) (n := n) (exponent := exponent) (u := u)
      (nRef1 := nRef1) (exponentRef := exponentRef) (nRef2 := nRef2)
      (uRef := uRef) (sizeRef := sizeRef) (nRef3 := nRef3)
      (by simpa [posGuard] using hReq) with
    ⟨hN1, hExponentRef, hN2, hURef, hSizeRef, hN3⟩
  subst nRef1
  subst exponentRef
  subst nRef2
  subst uRef
  subst sizeRef
  subst nRef3
  refine ⟨hP1, hP2, ?_, ?_⟩
  · simpa [posUpperPremRefs] using hP3
  · rw [hP1, hP2, hP3]
    simpa [posUpperPremRefs] using
      (pos_program_canonical xs ys z size n exponent u
        hXs hYs hZ hSize hN hExponent hU)

theorem pos_program_eq_term_of_type_bool
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (posProgram xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    P1 = BvMultPow2PosSupport.bvMultPow2PosIspowPrem n ∧
      P2 = BvMultPow2PosSupport.bvMultPow2PosExponentPrem n exponent ∧
      P3 = BvMultPow2PosSupport.bvMultPow2PosUpperPrem size n u ∧
      posProgram xs ys z size n exponent u P1 P2 P3 =
        posTerm xs ys z size n exponent u := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases pos_program_normalize xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProg with
    ⟨hP1, hP2, hP3, hSkeleton⟩
  have hSkeletonTy :
      __eo_typeof (posSkeleton xs ys z size n exponent u) = Term.Bool := by
    rw [← hSkeleton]
    exact hTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLists := guarded_lhs_lists xs ys z size n hLhsNe
  have hLhsEq := guarded_lhs_eq_lhs xs ys z size n hLhsNe
  have hBaseEq := guarded_base_eq_base xs ys z hLists.1 hLists.2
  have hOuterConcatFunNe :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
  have hExtractNe :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOuterConcatFunNe
  refine ⟨hP1, hP2, hP3, ?_⟩
  calc
    posProgram xs ys z size n exponent u P1 P2 P3 =
        posSkeleton xs ys z size n exponent u := hSkeleton
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (guardedLhs xs ys z size n))
          (guardedPosRhs xs ys z exponent u) := by
      unfold posSkeleton
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
    _ = posTerm xs ys z size n exponent u := by
      unfold guardedPosRhs at hRhsNe ⊢
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hOuterConcatFunNe]
      unfold guardedPosExtract at hExtractNe ⊢
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hExtractNe]
      unfold posTerm BvMultPow2PosSupport.bvMultPow2PosRhs bvExtractTerm
      rw [hLhsEq, hBaseEq]

theorem pos_program_lists_of_type_bool
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (posProgram xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases pos_program_normalize xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProg with
    ⟨_hP1, _hP2, _hP3, hSkeleton⟩
  have hSkeletonTy :
      __eo_typeof (posSkeleton xs ys z size n exponent u) = Term.Bool := by
    rw [← hSkeleton]
    exact hTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  exact guarded_lhs_lists xs ys z size n hLhsNe

theorem typed_pos_program
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (posProgram xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (posProgram xs ys z size n exponent u P1 P2 P3) := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProgramTy
  rcases pos_program_eq_term_of_type_bool xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProgramTy with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hLists := pos_program_lists_of_type_bool xs ys z size n exponent u
    P1 P2 P3 hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProgramTy
  have hTermTy :
      __eo_typeof (posTerm xs ys z size n exponent u) = Term.Bool := by
    rw [← hProgramEq]
    exact hProgramTy
  rw [hProgramEq]
  exact typed_pos_term xs ys z size n exponent u hXsTrans hYsTrans hZTrans
    hSizeTrans hNTrans hExponentTrans hLists.1 hLists.2 hTermTy

theorem facts_pos_program
    (M : SmtModel) (hM : model_wf M)
    (xs ys z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (posProgram xs ys z size n exponent u P1 P2 P3) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M (posProgram xs ys z size n exponent u P1 P2 P3) true := by
  intro hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProgramTy hP1True hP2True hP3True
  rcases pos_program_eq_term_of_type_bool xs ys z size n exponent u P1 P2 P3
      hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans hUTrans
      hProgramTy with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hLists := pos_program_lists_of_type_bool xs ys z size n exponent u
    P1 P2 P3 hXsTrans hYsTrans hZTrans hSizeTrans hNTrans hExponentTrans
    hUTrans hProgramTy
  have hTermTy :
      __eo_typeof (posTerm xs ys z size n exponent u) = Term.Bool := by
    rw [← hProgramEq]
    exact hProgramTy
  have hIspPrem :
      eo_interprets M
        (BvMultPow2PosSupport.bvMultPow2PosIspowPrem n) true := by
    simpa [hP1] using hP1True
  have hExponentPrem :
      eo_interprets M
        (BvMultPow2PosSupport.bvMultPow2PosExponentPrem n exponent) true := by
    simpa [hP2] using hP2True
  have hUpperPrem :
      eo_interprets M
        (BvMultPow2PosSupport.bvMultPow2PosUpperPrem size n u) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_pos_term M hM xs ys z size n exponent u hXsTrans hYsTrans
    hZTrans hSizeTrans hNTrans hExponentTrans hLists.1 hLists.2 hTermTy
    hIspPrem hExponentPrem hUpperPrem

end BvMultPow2NarySupport
