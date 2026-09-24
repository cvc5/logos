module

public import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import all Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.BvNaryAndSupport
import all Cpc.Proofs.RuleSupport.BvNaryAndSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

/-! Shared support for the two n-ary bit-vector AND simplification rules. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAndSimplifySupport

private def op : Term := Term.UOp UserOp.bvand

private def band (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bvnot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) x

private def eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private def guardedInner (ys zs second : Term) : Term :=
  __eo_list_concat op ys (band second zs)

private def guardedInserted (ys zs first second : Term) : Term :=
  __eo_mk_apply (Term.Apply op first) (guardedInner ys zs second)

private def guardedLhs (xs ys zs first second : Term) : Term :=
  __eo_list_concat op xs (guardedInserted ys zs first second)

private def inner (ys zs second : Term) : Term :=
  __eo_list_concat_rec ys (band second zs)

private def inserted (ys zs first second : Term) : Term :=
  band first (inner ys zs second)

private def lhs (xs ys zs first second : Term) : Term :=
  __eo_list_concat_rec xs (inserted ys zs first second)

def ListTypeOrNil (t : Term) (w : Nat) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ∨
    ∀ tail, __eo_list_concat_rec t tail = tail

private def listIdentity (w : Nat) : Term :=
  Term.Binary (native_nat_to_int w)
    (native_int_pow2 (native_nat_to_int w) - 1)

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem native_pow2_minus_one_mod_self_nat (w : Nat) :
    native_mod_total
        (native_int_pow2 (native_nat_to_int w) - 1)
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 := by
  rw [native_int_pow2_nat]
  have hPowPos : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hLower : 0 <= (2 ^ w : Int) - 1 := by omega
  have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by omega
  simpa [native_mod_total] using Int.emod_eq_of_lt hLower hUpper

private theorem listIdentity_smt_type (w : Nat) :
    __smtx_typeof (__eo_to_smt (listIdentity w)) = SmtType.BitVec w := by
  change __smtx_typeof
      (SmtTerm.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1)) = _
  have hMod := native_pow2_minus_one_mod_self_nat w
  have hMod' :
      native_mod_total (native_int_pow2 (↑w) - 1) (native_int_pow2 (↑w)) =
        native_int_pow2 (↑w) - 1 := by
    simpa [native_nat_to_int] using hMod
  simp [__smtx_typeof, SmtEval.native_and, native_ite, native_zleq,
    native_zeq, hMod', native_nat_to_int,
    SmtEval.native_int_to_nat, native_int_to_nat]

private theorem listIdentity_is_list (w : Nat) :
    __eo_is_list (Term.UOp UserOp.bvand) (listIdentity w) = Term.Boolean true := by
  simp [op, listIdentity, __eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
    __eo_is_list_nil_bvand, __eo_to_z, __eo_not, __eo_is_eq, __eo_is_ok,
    native_binary_not, native_zplus, native_zneg, native_mod_total,
    __eo_requires, native_ite, native_and, native_not, native_teq,
    native_zeq]

@[simp] private theorem listIdentity_concat_rec (w : Nat) (tail : Term) :
    __eo_list_concat_rec (listIdentity w) tail = tail := by
  cases tail <;>
    simp [listIdentity, __eo_list_concat_rec, __eo_is_list_nil,
      __eo_is_list_nil_bvand, __eo_to_z, __eo_not, __eo_is_eq,
      native_binary_not, native_zplus, native_zneg, native_mod_total,
      native_and, native_not, SmtEval.native_not, native_teq]

private theorem lhs_congr_lists
    (xs xs' ys ys' zs first second : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    lhs xs ys zs first second = lhs xs' ys' zs first second := by
  unfold lhs inserted inner
  rw [hYs, hXs]

private theorem list_concat_reduce (f a b : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f b = Term.Boolean true ->
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  intro hA hB
  simp [__eo_list_concat, hA, hB, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

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

private theorem term_ne_stuck_of_is_list_true (f t : Term) :
    __eo_is_list f t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList h
  subst t
  cases f <;> simp [__eo_is_list] at hList

private theorem guardedLhs_lists_of_ne_stuck
    (xs ys zs first second : Term) :
    guardedLhs xs ys zs first second ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true := by
  intro hLhs
  have hOuter := list_concat_parts_of_ne_stuck op xs
    (guardedInserted ys zs first second) (by
      simpa [guardedLhs] using hLhs)
  have hInsertedNe :=
    term_ne_stuck_of_is_list_true op (guardedInserted ys zs first second)
      hOuter.2
  have hInsertedEq :
      guardedInserted ys zs first second =
        band first (guardedInner ys zs second) := by
    exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hInsertedNe
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.bvand) (guardedInner ys zs second) =
        Term.Boolean true := by
    rw [hInsertedEq] at hOuter
    exact eo_is_list_tail_true_of_cons_self op first
      (guardedInner ys zs second) hOuter.2
  have hInnerNe := term_ne_stuck_of_is_list_true op
    (guardedInner ys zs second) hInnerList
  have hInner := list_concat_parts_of_ne_stuck op ys (band second zs) (by
    simpa [guardedInner] using hInnerNe)
  have hZs : __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op second zs hInner.2
  exact ⟨hOuter.1, hInner.1, hZs⟩

private theorem guardedLhs_eq_lhs_of_ne_stuck
    (xs ys zs first second : Term) :
    guardedLhs xs ys zs first second ≠ Term.Stuck ->
    guardedLhs xs ys zs first second = lhs xs ys zs first second := by
  intro hLhs
  have hOuter := list_concat_parts_of_ne_stuck op xs
    (guardedInserted ys zs first second) (by
      simpa [guardedLhs] using hLhs)
  have hInsertedNe :=
    term_ne_stuck_of_is_list_true op (guardedInserted ys zs first second)
      hOuter.2
  have hInsertedEq :
      guardedInserted ys zs first second =
        band first (guardedInner ys zs second) :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hInsertedNe
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.bvand) (guardedInner ys zs second) =
        Term.Boolean true := by
    rw [hInsertedEq] at hOuter
    exact eo_is_list_tail_true_of_cons_self op first
      (guardedInner ys zs second) hOuter.2
  have hInnerNe := term_ne_stuck_of_is_list_true op
    (guardedInner ys zs second) hInnerList
  have hInnerParts := list_concat_parts_of_ne_stuck op ys
    (band second zs) (by simpa [guardedInner] using hInnerNe)
  have hOuterReduce := list_concat_reduce op xs
    (guardedInserted ys zs first second) hOuter.1 hOuter.2
  have hInnerReduce := list_concat_reduce op ys (band second zs)
    hInnerParts.1 hInnerParts.2
  calc
    guardedLhs xs ys zs first second =
        __eo_list_concat_rec xs (guardedInserted ys zs first second) := by
      simpa [guardedLhs] using hOuterReduce
    _ = __eo_list_concat_rec xs
        (band first (guardedInner ys zs second)) := by rw [hInsertedEq]
    _ = lhs xs ys zs first second := by
      rw [show guardedInner ys zs second = inner ys zs second by
        simpa [guardedInner, inner] using hInnerReduce]
      rfl

private theorem smtx_typeof_bvand_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvand x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_eval_bvand_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvand x y) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem bvand_smt_type
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (band x y)) = SmtType.BitVec w := by
  intro hXTy hYTy
  change __smtx_typeof
      (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [smtx_typeof_bvand_term_eq]
  simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_nateq, native_ite]

private theorem bvnot_smt_type
    (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (bvnot x)) = SmtType.BitVec w := by
  intro hXTy
  change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)) = _
  rw [smtx_typeof_bvnot_term_eq]
  simp [__smtx_typeof_bv_op_1, hXTy, native_ite]

private theorem typeof_bvand_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec =>
                          have hReq :
                              __eo_requires (__eo_eq n m)
                                  (Term.Boolean true)
                                  (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
                                Term.Stuck := by
                            simpa [__eo_typeof_bvand] using h
                          have hm : m = n :=
                            support_eq_of_eo_eq_true n m
                              (support_eo_requires_cond_eq_of_non_stuck hReq)
                          exact ⟨n, rfl, by rw [hm]⟩
                      | _ => simp [__eo_typeof_bvand] at h
                  | _ => simp [__eo_typeof_bvand] at h
              | _ => simp [__eo_typeof_bvand] at h
          | _ => simp [__eo_typeof_bvand] at h
      | _ => simp [__eo_typeof_bvand] at h
  | _ => simp [__eo_typeof_bvand] at h

private theorem typeof_bvand_args_of_result_bitvec
    (x y width : Term) :
    __eo_typeof (band x y) =
        Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro h
  have hNe :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    have hsimpa := (show __eo_typeof (band x y) ≠ Term.Stuck by
      rw [h]
      intro hBad
      cases hBad)
    try simp [band] at hsimpa ⊢
    exact hsimpa
  rcases typeof_bvand_arg_types_of_ne_stuck hNe with
    ⟨actualWidth, hXTy, hYTy⟩
  have hActualWidthNe : actualWidth ≠ Term.Stuck := by
    intro hStuck
    apply hNe
    rw [hXTy, hYTy, hStuck]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hReduce :
      __eo_typeof_bvand
          (Term.Apply (Term.UOp UserOp.BitVec) actualWidth)
          (Term.Apply (Term.UOp UserOp.BitVec) actualWidth) =
        Term.Apply (Term.UOp UserOp.BitVec) actualWidth := by
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hActualWidthNe]
  have hWidth : actualWidth = width := by
    change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) = _ at h
    rw [hXTy, hYTy, hReduce] at h
    cases h
    rfl
  subst actualWidth
  exact ⟨hXTy, hYTy⟩

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
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hF hX
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem list_concat_rec_right_type
    (a z width : Term) :
    __eo_is_list (Term.UOp UserOp.bvand) a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA =>
      have hEq : __eo_list_concat_rec a Term.Stuck = Term.Stuck := by
        cases a <;> rfl
      rw [hEq] at hTy
      exact hTy
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          h, mk_apply_right_stuck_local] at hTy
        cases hTy
      rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
        mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe] at hTy
      exact ih hTailList
        (typeof_bvand_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) width (by simpa [band, op] using hTy)).2
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hTy

private theorem list_concat_rec_right_type_ne_stuck
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.bvand) a = Term.Boolean true ->
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
    __eo_is_list (Term.UOp UserOp.bvand) a = Term.Boolean true ->
    __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hZTy hResultNe
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA =>
      cases hZTy
  | case3 f x xs z hz ih =>
      have hf : f = op :=
        eo_is_list_cons_head_eq_of_true op f x xs hList
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
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) ≠ Term.Stuck at hResultNe
        exact hResultNe
      rcases typeof_bvand_arg_types_of_ne_stuck hOuterNe with
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

private theorem list_smt_type_or_nil_of_concat_type
    (a z : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation a ->
    __eo_is_list (Term.UOp UserOp.bvand) a = Term.Boolean true ->
    z ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt a) =
        SmtType.BitVec (native_int_to_nat W) ∨
      ∀ tail, __eo_list_concat_rec a tail = tail := by
  intro hATrans hAList hZNe hConcatTy hW0
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      simp [op, __eo_is_list] at hAList
  | case2 a hA =>
      exact False.elim (hZNe rfl)
  | case3 f x xs z hz ih =>
      have hf : f = op :=
        eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro hTail
        rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
          hTail, mk_apply_right_stuck_local] at hConcatTy
        cases hConcatTy
      rw [list_concat_rec_cons_of_right_ne_stuck op x xs z hz,
        mk_apply_eq_apply_of_args_ne_stuck _ _ (by simp [op]) hTailNe] at hConcatTy
      have hXTypeof :=
        (typeof_bvand_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) (Term.Numeral W)
          (by simpa [band, op] using hConcatTy)).1
      have hNonNone :
          term_has_non_none_type
            (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt xs)) := by
        have hsimpa := hATrans
        try simp [RuleProofs.eo_has_smt_translation, band, op] at hsimpa ⊢
        exact hsimpa
      rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
          (show
            __smtx_typeof (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt xs)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt x))
                (__smtx_typeof (__eo_to_smt xs)) by
            rw [__smtx_typeof.eq_def] <;> simp only) hNonNone with
        ⟨smtWidth, hXTy, hXsTy⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        rw [RuleProofs.eo_has_smt_translation, hXTy]
        intro h
        cases h
      have hXExpected :=
        RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
          x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
            (__eo_to_smt x) rfl hXTrans hXTypeof
      have hXExpected' :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.BitVec (native_int_to_nat W) := by
        simpa [__eo_to_smt_type, hW0, native_ite] using hXExpected
      have hWidth : smtWidth = native_int_to_nat W := by
        rw [hXTy] at hXExpected'
        cases hXExpected'
        rfl
      subst smtWidth
      apply Or.inl
      change __smtx_typeof
          (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt xs)) = _
      rw [__smtx_typeof.eq_def] <;> simp only
      simp [__smtx_typeof_bv_op_2, hXTy, hXsTy,
        native_nateq, native_ite]
  | case4 nil z hNil hZ hNot =>
      apply Or.inr
      intro tail
      unfold __eo_list_concat_rec
      split <;> simp_all

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat n) := by
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

private theorem lhs_component_types
    (xs ys zs first second : Term) :
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_typeof (lhs xs ys zs first second) ≠ Term.Stuck ->
    ∃ width,
      __eo_typeof (lhs xs ys zs first second) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (inner ys zs second) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof first =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof second =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof zs =
          Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hXsList hYsList hLhsNe
  have hInsertedNe :
      __eo_typeof (inserted ys zs first second) ≠ Term.Stuck :=
    list_concat_rec_right_type_ne_stuck xs
      (inserted ys zs first second) hXsList (by simpa [lhs] using hLhsNe)
  have hInsertedOpNe :
      __eo_typeof_bvand (__eo_typeof first)
          (__eo_typeof (inner ys zs second)) ≠ Term.Stuck := by
    have hsimpa := hInsertedNe
    try simp [inserted, band, op] at hsimpa ⊢
    exact hsimpa
  rcases typeof_bvand_arg_types_of_ne_stuck hInsertedOpNe with
    ⟨width, hFirstTy, hInnerTy⟩
  have hWidthNe : width ≠ Term.Stuck := by
    intro h
    apply hInsertedOpNe
    rw [hFirstTy, hInnerTy, h]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hInsertedTy :
      __eo_typeof (inserted ys zs first second) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    change __eo_typeof_bvand (__eo_typeof first)
      (__eo_typeof (inner ys zs second)) = _
    rw [hFirstTy, hInnerTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hWidthNe]
  have hLhsTy := list_concat_rec_result_type xs
    (inserted ys zs first second) width hXsList hInsertedTy
      (by simpa [lhs] using hLhsNe)
  have hSecondZsTy := list_concat_rec_right_type ys (band second zs) width
    hYsList (by simpa [inner] using hInnerTy)
  have hSecondZsParts := typeof_bvand_args_of_result_bitvec
    second zs width hSecondZsTy
  exact ⟨width, by simpa [lhs] using hLhsTy, hInnerTy, hFirstTy,
    hSecondZsParts.1, hSecondZsParts.2⟩

private theorem inferred_argument_types_common
    (xs ys zs first second x : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_typeof (lhs xs ys zs first second) ≠ Term.Stuck ->
    (∀ width,
      __eo_typeof first = Term.Apply (Term.UOp UserOp.BitVec) width ->
      __eo_typeof second = Term.Apply (Term.UOp UserOp.BitVec) width ->
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width) ->
    ∃ W : native_Int,
      native_zleq 0 W = true ∧
        __eo_typeof (lhs xs ys zs first second) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
        ListTypeOrNil xs (native_int_to_nat W) ∧
        ListTypeOrNil ys (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt zs) =
          SmtType.BitVec (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt x) =
          SmtType.BitVec (native_int_to_nat W) := by
  intro hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hLhsNe hPickX
  rcases lhs_component_types xs ys zs first second hXsList hYsList hLhsNe with
    ⟨width, hLhsTy, hInnerTy, hFirstTy, hSecondTy, hZsEoTy⟩
  have hXEoTy := hPickX width hFirstTy hSecondTy
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x width
      hXTrans hXEoTy with
    ⟨W, hWidth, hW0, hXTy⟩
  subst width
  have hZsExpected :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      zs (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt zs) rfl hZsTrans hZsEoTy
  have hZsTy :
      __smtx_typeof (__eo_to_smt zs) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [__eo_to_smt_type, hW0, native_ite] using hZsExpected
  have hYsTypeOrNil := list_smt_type_or_nil_of_concat_type
    ys (band second zs) W hYsTrans hYsList (by simp [band])
      (by simpa [inner] using hInnerTy) hW0
  have hXsTypeOrNil := list_smt_type_or_nil_of_concat_type
    xs (inserted ys zs first second) W hXsTrans hXsList
      (by simp [inserted, band]) (by simpa [lhs] using hLhsTy) hW0
  exact ⟨W, hW0, hLhsTy,
    by simpa [ListTypeOrNil] using hXsTypeOrNil,
    by simpa [ListTypeOrNil] using hYsTypeOrNil, hZsTy, hXTy⟩

def zeroConst (w : Term) : Term :=
  bvAllOnesConst (Term.Numeral 0) w

def andTerm1 (xs ys zs x w : Term) : Term :=
  eqTerm (lhs xs ys zs (bvnot x) x) (zeroConst w)

def andTerm2 (xs ys zs x w : Term) : Term :=
  eqTerm (lhs xs ys zs x (bvnot x)) (zeroConst w)

private def andSkeleton1 (xs ys zs x w : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys zs (bvnot x) x))
    (zeroConst w)

private def andSkeleton2 (xs ys zs x w : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys zs x (bvnot x)))
    (zeroConst w)

private theorem program1_eq_skeleton_of_ne_stuck
    (xs ys zs x w : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    x ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_prog_bv_and_simplify_1 xs ys zs x w
        (Proof.pf (bvAllOnesWidthPrem x w)) =
      andSkeleton1 xs ys zs x w := by
  intro hXs hYs hZs hX hW
  unfold bvAllOnesWidthPrem
  rw [__eo_prog_bv_and_simplify_1.eq_6 xs ys zs x w w x
    hXs hYs hZs hX hW]
  simp [andSkeleton1, guardedLhs, guardedInserted, guardedInner, zeroConst,
    bvAllOnesConst, bvnot, band, op, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    SmtEval.native_and, hX, hW]

private theorem program2_eq_skeleton_of_ne_stuck
    (xs ys zs x w : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    x ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_prog_bv_and_simplify_2 xs ys zs x w
        (Proof.pf (bvAllOnesWidthPrem x w)) =
      andSkeleton2 xs ys zs x w := by
  intro hXs hYs hZs hX hW
  unfold bvAllOnesWidthPrem
  rw [__eo_prog_bv_and_simplify_2.eq_6 xs ys zs x w w x
    hXs hYs hZs hX hW]
  simp [andSkeleton2, guardedLhs, guardedInserted, guardedInner, zeroConst,
    bvAllOnesConst, bvnot, band, op, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    SmtEval.native_and, hX, hW]

private theorem skeleton_lhs_ne_of_ne_stuck (left right : Term) :
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) left) right ≠
        Term.Stuck ->
    left ≠ Term.Stuck := by
  intro hTop
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFun

private theorem skeleton1_eq_term_of_ne_stuck
    (xs ys zs x w : Term) :
    andSkeleton1 xs ys zs x w ≠ Term.Stuck ->
    andSkeleton1 xs ys zs x w = andTerm1 xs ys zs x w ∧
      __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true := by
  intro hTop
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  have hLhsNe : guardedLhs xs ys zs (bvnot x) x ≠ Term.Stuck :=
    skeleton_lhs_ne_of_ne_stuck _ _ (by simpa [andSkeleton1] using hTop)
  have hLists := guardedLhs_lists_of_ne_stuck xs ys zs (bvnot x) x hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck xs ys zs (bvnot x) x hLhsNe
  constructor
  · unfold andSkeleton1 andTerm1 eqTerm
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hTop]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFun]
    rw [hLhsEq]
  · exact hLists

private theorem skeleton2_eq_term_of_ne_stuck
    (xs ys zs x w : Term) :
    andSkeleton2 xs ys zs x w ≠ Term.Stuck ->
    andSkeleton2 xs ys zs x w = andTerm2 xs ys zs x w ∧
      __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true := by
  intro hTop
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  have hLhsNe : guardedLhs xs ys zs x (bvnot x) ≠ Term.Stuck :=
    skeleton_lhs_ne_of_ne_stuck _ _ (by simpa [andSkeleton2] using hTop)
  have hLists := guardedLhs_lists_of_ne_stuck xs ys zs x (bvnot x) hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck xs ys zs x (bvnot x) hLhsNe
  constructor
  · unfold andSkeleton2 andTerm2 eqTerm
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hTop]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFun]
    rw [hLhsEq]
  · exact hLists

theorem program1_context
    (xs ys zs x w : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    x ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_typeof
        (__eo_prog_bv_and_simplify_1 xs ys zs x w
          (Proof.pf (bvAllOnesWidthPrem x w))) = Term.Bool ->
    __eo_prog_bv_and_simplify_1 xs ys zs x w
        (Proof.pf (bvAllOnesWidthPrem x w)) = andTerm1 xs ys zs x w ∧
      __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true := by
  intro hXs hYs hZs hX hW hTy
  have hEq := program1_eq_skeleton_of_ne_stuck xs ys zs x w
    hXs hYs hZs hX hW
  have hSkeletonNe : andSkeleton1 xs ys zs x w ≠ Term.Stuck := by
    rw [← hEq]
    exact term_ne_stuck_of_typeof_bool hTy
  have h := skeleton1_eq_term_of_ne_stuck xs ys zs x w hSkeletonNe
  exact ⟨hEq.trans h.1, h.2⟩

theorem program2_context
    (xs ys zs x w : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    x ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_typeof
        (__eo_prog_bv_and_simplify_2 xs ys zs x w
          (Proof.pf (bvAllOnesWidthPrem x w))) = Term.Bool ->
    __eo_prog_bv_and_simplify_2 xs ys zs x w
        (Proof.pf (bvAllOnesWidthPrem x w)) = andTerm2 xs ys zs x w ∧
      __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true := by
  intro hXs hYs hZs hX hW hTy
  have hEq := program2_eq_skeleton_of_ne_stuck xs ys zs x w
    hXs hYs hZs hX hW
  have hSkeletonNe : andSkeleton2 xs ys zs x w ≠ Term.Stuck := by
    rw [← hEq]
    exact term_ne_stuck_of_typeof_bool hTy
  have h := skeleton2_eq_term_of_ne_stuck xs ys zs x w hSkeletonNe
  exact ⟨hEq.trans h.1, h.2⟩

theorem program1_shape_of_ne_stuck
    (xs ys zs x w P : Term) :
    __eo_prog_bv_and_simplify_1 xs ys zs x w (Proof.pf P) ≠
      Term.Stuck ->
    xs ≠ Term.Stuck ∧ ys ≠ Term.Stuck ∧ zs ≠ Term.Stuck ∧
      x ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      ∃ pw px, P = bvAllOnesWidthPrem px pw := by
  intro hProg
  have hXs : xs ≠ Term.Stuck := by
    intro h
    subst xs
    exact hProg (__eo_prog_bv_and_simplify_1.eq_1 ys zs x w (Proof.pf P))
  have hYs : ys ≠ Term.Stuck := by
    intro h
    subst ys
    exact hProg
      (__eo_prog_bv_and_simplify_1.eq_2 xs zs x w (Proof.pf P) hXs)
  have hZs : zs ≠ Term.Stuck := by
    intro h
    subst zs
    exact hProg
      (__eo_prog_bv_and_simplify_1.eq_3 xs ys x w (Proof.pf P) hXs hYs)
  have hX : x ≠ Term.Stuck := by
    intro h
    subst x
    exact hProg
      (__eo_prog_bv_and_simplify_1.eq_4 xs ys zs w (Proof.pf P)
        hXs hYs hZs)
  have hW : w ≠ Term.Stuck := by
    intro h
    subst w
    exact hProg
      (__eo_prog_bv_and_simplify_1.eq_5 xs ys zs x (Proof.pf P)
        hXs hYs hZs hX)
  by_cases hShape : ∃ pw px, P = bvAllOnesWidthPrem px pw
  · exact ⟨hXs, hYs, hZs, hX, hW, hShape⟩
  · have hStuck :
        __eo_prog_bv_and_simplify_1 xs ys zs x w (Proof.pf P) =
          Term.Stuck :=
      __eo_prog_bv_and_simplify_1.eq_7 xs ys zs x w (Proof.pf P)
        hXs hYs hZs hX hW (by
          intro pw px hp
          cases hp
          exact hShape ⟨pw, px, rfl⟩)
    exact False.elim (hProg hStuck)

theorem program2_shape_of_ne_stuck
    (xs ys zs x w P : Term) :
    __eo_prog_bv_and_simplify_2 xs ys zs x w (Proof.pf P) ≠
      Term.Stuck ->
    xs ≠ Term.Stuck ∧ ys ≠ Term.Stuck ∧ zs ≠ Term.Stuck ∧
      x ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      ∃ pw px, P = bvAllOnesWidthPrem px pw := by
  intro hProg
  have hXs : xs ≠ Term.Stuck := by
    intro h
    subst xs
    exact hProg (__eo_prog_bv_and_simplify_2.eq_1 ys zs x w (Proof.pf P))
  have hYs : ys ≠ Term.Stuck := by
    intro h
    subst ys
    exact hProg
      (__eo_prog_bv_and_simplify_2.eq_2 xs zs x w (Proof.pf P) hXs)
  have hZs : zs ≠ Term.Stuck := by
    intro h
    subst zs
    exact hProg
      (__eo_prog_bv_and_simplify_2.eq_3 xs ys x w (Proof.pf P) hXs hYs)
  have hX : x ≠ Term.Stuck := by
    intro h
    subst x
    exact hProg
      (__eo_prog_bv_and_simplify_2.eq_4 xs ys zs w (Proof.pf P)
        hXs hYs hZs)
  have hW : w ≠ Term.Stuck := by
    intro h
    subst w
    exact hProg
      (__eo_prog_bv_and_simplify_2.eq_5 xs ys zs x (Proof.pf P)
        hXs hYs hZs hX)
  by_cases hShape : ∃ pw px, P = bvAllOnesWidthPrem px pw
  · exact ⟨hXs, hYs, hZs, hX, hW, hShape⟩
  · have hStuck :
        __eo_prog_bv_and_simplify_2 xs ys zs x w (Proof.pf P) =
          Term.Stuck :=
      __eo_prog_bv_and_simplify_2.eq_7 xs ys zs x w (Proof.pf P)
        hXs hYs hZs hX hW (by
          intro pw px hp
          cases hp
          exact hShape ⟨pw, px, rfl⟩)
    exact False.elim (hProg hStuck)

private theorem inferred_argument_types
    (xs ys zs first second x w result : Term) :
    result = eqTerm (lhs xs ys zs first second) (zeroConst w) ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_typeof result = Term.Bool ->
    (∀ width,
      __eo_typeof first = Term.Apply (Term.UOp UserOp.BitVec) width ->
      __eo_typeof second = Term.Apply (Term.UOp UserOp.BitVec) width ->
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width) ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ native_zleq 0 W = true ∧
        ListTypeOrNil xs (native_int_to_nat W) ∧
        ListTypeOrNil ys (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt zs) =
          SmtType.BitVec (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt x) =
          SmtType.BitVec (native_int_to_nat W) := by
  intro hResult hXsTrans hYsTrans hZsTrans hXTrans hWTrans
    hXsList hYsList hResultTy hPickX
  subst result
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs ys zs first second)) (__eo_typeof (zeroConst w))
    (by have hsimpa := hResultTy; (try simp [eqTerm] at hsimpa ⊢); exact hsimpa)
  have hTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof (lhs xs ys zs first second)) (__eo_typeof (zeroConst w))
    (by have hsimpa := hResultTy; (try simp [eqTerm] at hsimpa ⊢); exact hsimpa)
  rcases inferred_argument_types_common xs ys zs first second x
      hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hSides.1 hPickX with
    ⟨W, hW0, hLhsEoTy, hXsTy, hYsTy, hZsTy, hXTy⟩
  have hRhsEoTy :
      __eo_typeof (zeroConst w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) :=
    hTypesEq.symm.trans hLhsEoTy
  have hConstEoTy :
      __eo_typeof (bvAllOnesConst (Term.Numeral 0) w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) :=
    by simpa [zeroConst] using hRhsEoTy
  have hWNe := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) w (Term.Numeral W)
      (by decide) hWNe hConstEoTy with
    ⟨W', hW, hWidth, _hW'0, _hZeroTy⟩
  have hWEq : W' = W := by
    injection hWidth with h
    exact h.symm
  subst W'
  exact ⟨W, hW, hW0, hXsTy, hYsTy, hZsTy, hXTy⟩

theorem inferred_argument_types1
    (xs ys zs x w : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_typeof (andTerm1 xs ys zs x w) = Term.Bool ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ native_zleq 0 W = true ∧
        ListTypeOrNil xs (native_int_to_nat W) ∧
        ListTypeOrNil ys (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt zs) =
          SmtType.BitVec (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt x) =
          SmtType.BitVec (native_int_to_nat W) := by
  intro hXs hYs hZs hX hW hXsList hYsList hTy
  exact inferred_argument_types xs ys zs (bvnot x) x x w
    (andTerm1 xs ys zs x w) (by rfl) hXs hYs hZs hX hW
    hXsList hYsList hTy (fun _ _ hSecond => hSecond)

theorem inferred_argument_types2
    (xs ys zs x w : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_typeof (andTerm2 xs ys zs x w) = Term.Bool ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ native_zleq 0 W = true ∧
        ListTypeOrNil xs (native_int_to_nat W) ∧
        ListTypeOrNil ys (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt zs) =
          SmtType.BitVec (native_int_to_nat W) ∧
        __smtx_typeof (__eo_to_smt x) =
          SmtType.BitVec (native_int_to_nat W) := by
  intro hXs hYs hZs hX hW hXsList hYsList hTy
  exact inferred_argument_types xs ys zs x (bvnot x) x w
    (andTerm2 xs ys zs x w) (by rfl) hXs hYs hZs hX hW
    hXsList hYsList hTy (fun _ hFirst _ => hFirst)

private theorem native_width_roundtrip (W : native_Int) :
    native_zleq 0 W = true ->
    native_nat_to_int (native_int_to_nat W) = W := by
  intro hW
  have hNonneg : (0 : native_Int) <= W := by
    simpa [SmtEval.native_zleq] using hW
  have hInt : (Int.ofNat (Int.toNat W) : Int) = W :=
    Int.toNat_of_nonneg hNonneg
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem andTerm1_congr_lists
    (xs xs' ys ys' zs x w : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    andTerm1 xs ys zs x w = andTerm1 xs' ys' zs x w := by
  unfold andTerm1 eqTerm
  rw [lhs_congr_lists xs xs' ys ys' zs (bvnot x) x hXs hYs]

private theorem andTerm2_congr_lists
    (xs xs' ys ys' zs x w : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    andTerm2 xs ys zs x w = andTerm2 xs' ys' zs x w := by
  unfold andTerm2 eqTerm
  rw [lhs_congr_lists xs xs' ys ys' zs x (bvnot x) hXs hYs]

private theorem concat_rec_equiv_listIdentity (t : Term) (width : Nat) :
    (∀ tail, __eo_list_concat_rec t tail = tail) ->
    ∀ tail, __eo_list_concat_rec t tail =
      __eo_list_concat_rec (listIdentity width) tail := by
  intro hNil tail
  rw [hNil, listIdentity_concat_rec]

private theorem lhs_smt_type
    (xs ys zs first second : Term) (width : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt first) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt second) = SmtType.BitVec width ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt (lhs xs ys zs first second)) =
      SmtType.BitVec width := by
  intro hXsTy hYsTy hZsTy hFirstTy hSecondTy
    hXsList hYsList hZsList
  have hSecondZsList :
      __eo_is_list (Term.UOp UserOp.bvand) (band second zs) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op second zs
      (by decide) hZsList
  have hSecondZsTy := bvand_smt_type second zs width hSecondTy hZsTy
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.bvand) (inner ys zs second) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys (band second zs)
      hYsList hSecondZsList
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (inner ys zs second)) =
        SmtType.BitVec width :=
    BvNaryAndSupport.listConcatRecSmtType ys (band second zs) width
      (by simpa [op] using hYsList)
      (by simpa [op] using hSecondZsList) hYsTy hSecondZsTy
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvand) (inserted ys zs first second) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op first
      (inner ys zs second) (by decide) hInnerList
  have hInsertedTy := bvand_smt_type first (inner ys zs second) width
    hFirstTy hInnerTy
  exact BvNaryAndSupport.listConcatRecSmtType xs
    (inserted ys zs first second) width
    (by simpa [op] using hXsList)
    (by simpa [op] using hInsertedList) hXsTy hInsertedTy

private theorem typed_term_core
    (xs ys zs first second w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt ys) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt first) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt second) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type
      (eqTerm (lhs xs ys zs first second) (zeroConst w)) := by
  intro hXsTy hYsTy hZsTy hFirstTy hSecondTy hW hW0
    hXsList hYsList hZsList
  subst w
  let width := native_int_to_nat W
  have hLhsTy := lhs_smt_type xs ys zs first second width
    (by simpa [width] using hXsTy) (by simpa [width] using hYsTy)
    (by simpa [width] using hZsTy) (by simpa [width] using hFirstTy)
    (by simpa [width] using hSecondTy) hXsList hYsList hZsList
  have hZeroTy :
      __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by rfl
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt (bvAllOnesConst (Term.Numeral 0) (Term.Numeral W))) =
        SmtType.BitVec width := by
    have hsimpa :=
      smt_typeof_bv_const_of_int_type (Term.Numeral 0) W hZeroTy hW0
    try simp [width] at hsimpa ⊢
    exact hsimpa
  have hZeroConstTy :
      __smtx_typeof (__eo_to_smt (zeroConst (Term.Numeral W))) =
        SmtType.BitVec width := by
    simpa [zeroConst] using hConstTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhs xs ys zs first second) (zeroConst (Term.Numeral W))
    (by rw [hLhsTy, hZeroConstTy]) (by rw [hLhsTy]; simp)

private theorem typed_term1_core
    (xs ys zs x w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt ys) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (andTerm1 xs ys zs x w) := by
  intro hXs hYs hZs hX hW hW0 hXsList hYsList hZsList
  have hNotX := bvnot_smt_type x (native_int_to_nat W) hX
  simpa [andTerm1] using typed_term_core xs ys zs (bvnot x) x w W
    hXs hYs hZs hNotX hX hW hW0 hXsList hYsList hZsList

private theorem typed_term2_core
    (xs ys zs x w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt ys) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (andTerm2 xs ys zs x w) := by
  intro hXs hYs hZs hX hW hW0 hXsList hYsList hZsList
  have hNotX := bvnot_smt_type x (native_int_to_nat W) hX
  simpa [andTerm2] using typed_term_core xs ys zs x (bvnot x) w W
    hXs hYs hZs hX hNotX hW hW0 hXsList hYsList hZsList

theorem typed_term1_of_type_or_nil
    (xs ys zs x w : Term) (W : native_Int) :
    ListTypeOrNil xs (native_int_to_nat W) ->
    ListTypeOrNil ys (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (andTerm1 xs ys zs x w) := by
  intro hXs hYs hZsTy hXTy hW hW0 hXsList hYsList hZsList
  let width := native_int_to_nat W
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact typed_term1_core xs ys zs x w W hXsTy hYsTy hZsTy hXTy
        hW hW0 hXsList hYsList hZsList
    · rw [andTerm1_congr_lists xs xs ys (listIdentity width) zs x w
        (fun _ => rfl) (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact typed_term1_core xs (listIdentity width) zs x w W hXsTy
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 hXsList (listIdentity_is_list width) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [andTerm1_congr_lists xs (listIdentity width) ys ys zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil) (fun _ => rfl)]
      exact typed_term1_core (listIdentity width) ys zs x w W
        (by simpa [width] using listIdentity_smt_type width) hYsTy hZsTy hXTy
        hW hW0 (listIdentity_is_list width) hYsList hZsList
    · rw [andTerm1_congr_lists xs (listIdentity width) ys (listIdentity width) zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil)
        (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact typed_term1_core (listIdentity width) (listIdentity width) zs x w W
        (by simpa [width] using listIdentity_smt_type width)
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 (listIdentity_is_list width) (listIdentity_is_list width) hZsList

theorem typed_term2_of_type_or_nil
    (xs ys zs x w : Term) (W : native_Int) :
    ListTypeOrNil xs (native_int_to_nat W) ->
    ListTypeOrNil ys (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (andTerm2 xs ys zs x w) := by
  intro hXs hYs hZsTy hXTy hW hW0 hXsList hYsList hZsList
  let width := native_int_to_nat W
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact typed_term2_core xs ys zs x w W hXsTy hYsTy hZsTy hXTy
        hW hW0 hXsList hYsList hZsList
    · rw [andTerm2_congr_lists xs xs ys (listIdentity width) zs x w
        (fun _ => rfl) (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact typed_term2_core xs (listIdentity width) zs x w W hXsTy
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 hXsList (listIdentity_is_list width) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [andTerm2_congr_lists xs (listIdentity width) ys ys zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil) (fun _ => rfl)]
      exact typed_term2_core (listIdentity width) ys zs x w W
        (by simpa [width] using listIdentity_smt_type width) hYsTy hZsTy hXTy
        hW hW0 (listIdentity_is_list width) hYsList hZsList
    · rw [andTerm2_congr_lists xs (listIdentity width) ys (listIdentity width) zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil)
        (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact typed_term2_core (listIdentity width) (listIdentity width) zs x w W
        (by simpa [width] using listIdentity_smt_type width)
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 (listIdentity_is_list width) (listIdentity_is_list width) hZsList

private theorem eval_lhs
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs first second : Term) (width : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt first) = SmtType.BitVec width ->
    __smtx_typeof (__eo_to_smt second) = SmtType.BitVec width ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    __smtx_model_eval M
        (__eo_to_smt (lhs xs ys zs first second)) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M (__eo_to_smt xs))
        (__smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt first))
          (__smtx_model_eval_bvand
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval_bvand
              (__smtx_model_eval M (__eo_to_smt second))
              (__smtx_model_eval M (__eo_to_smt zs))))) := by
  intro hXsTy hYsTy hZsTy hFirstTy hSecondTy
    hXsList hYsList hZsList
  have hSecondZsList :
      __eo_is_list (Term.UOp UserOp.bvand) (band second zs) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op second zs
      (by decide) hZsList
  have hSecondZsTy := bvand_smt_type second zs width hSecondTy hZsTy
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.bvand) (inner ys zs second) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys (band second zs)
      hYsList hSecondZsList
  have hInnerTy := BvNaryAndSupport.listConcatRecSmtType
    ys (band second zs) width
    (by simpa [op] using hYsList)
    (by simpa [op] using hSecondZsList) hYsTy hSecondZsTy
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvand) (inserted ys zs first second) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op first
      (inner ys zs second) (by decide) hInnerList
  have hInsertedTy := bvand_smt_type first (inner ys zs second) width
    hFirstTy hInnerTy
  have hLhsConcat := BvNaryAndSupport.listConcatRecEvalEq M hM xs
    (inserted ys zs first second) width
    (by simpa [op] using hXsList)
    (by simpa [op] using hInsertedList) hXsTy hInsertedTy
  have hInnerConcat := BvNaryAndSupport.listConcatRecEvalEq M hM ys
    (band second zs) width
    (by simpa [op] using hYsList)
    (by simpa [op] using hSecondZsList) hYsTy hSecondZsTy
  have hSecondZsEval :
      __smtx_model_eval M (__eo_to_smt (band second zs)) =
        __smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt second))
          (__smtx_model_eval M (__eo_to_smt zs)) := by
    change __smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt second) (__eo_to_smt zs)) = _
    exact smtx_eval_bvand_term_eq M _ _
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt (inner ys zs second)) =
        __smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt ys))
          (__smtx_model_eval_bvand
            (__smtx_model_eval M (__eo_to_smt second))
            (__smtx_model_eval M (__eo_to_smt zs))) := by
    unfold inner
    rw [hInnerConcat]
    change __smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt ys)
          (__eo_to_smt (band second zs))) = _
    rw [smtx_eval_bvand_term_eq, hSecondZsEval]
  have hInsertedEval :
      __smtx_model_eval M
          (__eo_to_smt (inserted ys zs first second)) =
        __smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt first))
          (__smtx_model_eval_bvand
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval_bvand
              (__smtx_model_eval M (__eo_to_smt second))
              (__smtx_model_eval M (__eo_to_smt zs)))) := by
    change __smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt first)
          (__eo_to_smt (inner ys zs second))) = _
    rw [smtx_eval_bvand_term_eq, hInnerEval]
  unfold lhs
  rw [hLhsConcat]
  change __smtx_model_eval M
      (SmtTerm.bvand (__eo_to_smt xs)
        (__eo_to_smt (inserted ys zs first second))) = _
  rw [smtx_eval_bvand_term_eq, hInsertedEval]

private theorem eval_zeroConst
    (M : SmtModel) (w : Term) (W : native_Int) :
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __smtx_model_eval M (__eo_to_smt (zeroConst w)) =
      SmtValue.Binary
        (native_nat_to_int (native_int_to_nat W)) 0 := by
  intro hW hW0
  subst w
  have hMod0 : native_mod_total 0 (native_int_pow2 W) = 0 := by
    simp [native_mod_total]
  have hWidth := native_width_roundtrip W hW0
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (SmtTerm.Numeral 0)) = _
  rw [smtx_eval_int_to_bv_numerals, hMod0]
  rw [hWidth]

private theorem facts_term1_core
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt ys) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    eo_interprets M (andTerm1 xs ys zs x w) true := by
  intro hXsTy hYsTy hZsTy hXTy hW hW0 hXsList hYsList hZsList
  let width := native_int_to_nat W
  have hNotXTy := bvnot_smt_type x width (by simpa [width] using hXTy)
  have hBool := typed_term1_core xs ys zs x w W
    hXsTy hYsTy hZsTy hXTy hW hW0 hXsList hYsList hZsList
  have hLhsEval := eval_lhs M hM xs ys zs (bvnot x) x width
    (by simpa [width] using hXsTy) (by simpa [width] using hYsTy)
    (by simpa [width] using hZsTy) hNotXTy
    (by simpa [width] using hXTy) hXsList hYsList hZsList
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) width
      (by simpa [width] using hXsTy) with
    ⟨nxs, hXsEval, hXsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt ys) width
      (by simpa [width] using hYsTy) with
    ⟨nys, hYsEval, hYsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) width
      (by simpa [width] using hZsTy) with
    ⟨nzs, hZsEval, hZsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) width
      (by simpa [width] using hXTy) with
    ⟨nx, hXEval, hXCan⟩
  have hNotXEval :
      __smtx_model_eval M (__eo_to_smt (bvnot x)) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int width) nx) := by
    change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
    rw [smtx_eval_bvnot_term_eq, hXEval]
  have hZeroConstEval := eval_zeroConst M w W hW hW0
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (lhs xs ys zs (bvnot x) x)) =
        __smtx_model_eval M (__eo_to_smt (zeroConst w)) := by
    rw [hLhsEval, hXsEval, hNotXEval, hYsEval, hXEval, hZsEval,
      hZeroConstEval]
    exact BvNaryAndSupport.bvand_not_pair_nested_eval
      width nxs nx nys nzs hXsCan hXCan hYsCan hZsCan
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (lhs xs ys zs (bvnot x) x)))
      (__smtx_model_eval M (__eo_to_smt (zeroConst w)))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

private theorem facts_term2_core
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt ys) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    eo_interprets M (andTerm2 xs ys zs x w) true := by
  intro hXsTy hYsTy hZsTy hXTy hW hW0 hXsList hYsList hZsList
  let width := native_int_to_nat W
  have hNotXTy := bvnot_smt_type x width (by simpa [width] using hXTy)
  have hBool := typed_term2_core xs ys zs x w W
    hXsTy hYsTy hZsTy hXTy hW hW0 hXsList hYsList hZsList
  have hLhsEval := eval_lhs M hM xs ys zs x (bvnot x) width
    (by simpa [width] using hXsTy) (by simpa [width] using hYsTy)
    (by simpa [width] using hZsTy) (by simpa [width] using hXTy)
    hNotXTy hXsList hYsList hZsList
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) width
      (by simpa [width] using hXsTy) with
    ⟨nxs, hXsEval, hXsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt ys) width
      (by simpa [width] using hYsTy) with
    ⟨nys, hYsEval, hYsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) width
      (by simpa [width] using hZsTy) with
    ⟨nzs, hZsEval, hZsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) width
      (by simpa [width] using hXTy) with
    ⟨nx, hXEval, hXCan⟩
  have hNotXEval :
      __smtx_model_eval M (__eo_to_smt (bvnot x)) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int width) nx) := by
    change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
    rw [smtx_eval_bvnot_term_eq, hXEval]
  have hZeroConstEval := eval_zeroConst M w W hW hW0
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (lhs xs ys zs x (bvnot x))) =
        __smtx_model_eval M (__eo_to_smt (zeroConst w)) := by
    rw [hLhsEval, hXsEval, hXEval, hYsEval, hNotXEval, hZsEval,
      hZeroConstEval]
    exact BvNaryAndSupport.bvand_pair_not_nested_eval
      width nxs nx nys nzs hXsCan hXCan hYsCan hZsCan
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (lhs xs ys zs x (bvnot x))))
      (__smtx_model_eval M (__eo_to_smt (zeroConst w)))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_term1_of_type_or_nil
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x w : Term) (W : native_Int) :
    ListTypeOrNil xs (native_int_to_nat W) ->
    ListTypeOrNil ys (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    eo_interprets M (andTerm1 xs ys zs x w) true := by
  intro hXs hYs hZsTy hXTy hW hW0 hXsList hYsList hZsList
  let width := native_int_to_nat W
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact facts_term1_core M hM xs ys zs x w W hXsTy hYsTy
        hZsTy hXTy hW hW0 hXsList hYsList hZsList
    · rw [andTerm1_congr_lists xs xs ys (listIdentity width) zs x w
        (fun _ => rfl) (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact facts_term1_core M hM xs (listIdentity width) zs x w W hXsTy
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 hXsList (listIdentity_is_list width) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [andTerm1_congr_lists xs (listIdentity width) ys ys zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil) (fun _ => rfl)]
      exact facts_term1_core M hM (listIdentity width) ys zs x w W
        (by simpa [width] using listIdentity_smt_type width) hYsTy hZsTy hXTy
        hW hW0 (listIdentity_is_list width) hYsList hZsList
    · rw [andTerm1_congr_lists xs (listIdentity width) ys (listIdentity width) zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil)
        (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact facts_term1_core M hM (listIdentity width) (listIdentity width) zs x w W
        (by simpa [width] using listIdentity_smt_type width)
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 (listIdentity_is_list width) (listIdentity_is_list width) hZsList

theorem facts_term2_of_type_or_nil
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x w : Term) (W : native_Int) :
    ListTypeOrNil xs (native_int_to_nat W) ->
    ListTypeOrNil ys (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    w = Term.Numeral W -> native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvand) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) zs = Term.Boolean true ->
    eo_interprets M (andTerm2 xs ys zs x w) true := by
  intro hXs hYs hZsTy hXTy hW hW0 hXsList hYsList hZsList
  let width := native_int_to_nat W
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact facts_term2_core M hM xs ys zs x w W hXsTy hYsTy
        hZsTy hXTy hW hW0 hXsList hYsList hZsList
    · rw [andTerm2_congr_lists xs xs ys (listIdentity width) zs x w
        (fun _ => rfl) (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact facts_term2_core M hM xs (listIdentity width) zs x w W hXsTy
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 hXsList (listIdentity_is_list width) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [andTerm2_congr_lists xs (listIdentity width) ys ys zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil) (fun _ => rfl)]
      exact facts_term2_core M hM (listIdentity width) ys zs x w W
        (by simpa [width] using listIdentity_smt_type width) hYsTy hZsTy hXTy
        hW hW0 (listIdentity_is_list width) hYsList hZsList
    · rw [andTerm2_congr_lists xs (listIdentity width) ys (listIdentity width) zs x w
        (concat_rec_equiv_listIdentity xs width hXsNil)
        (concat_rec_equiv_listIdentity ys width hYsNil)]
      exact facts_term2_core M hM (listIdentity width) (listIdentity width) zs x w W
        (by simpa [width] using listIdentity_smt_type width)
        (by simpa [width] using listIdentity_smt_type width) hZsTy hXTy
        hW hW0 (listIdentity_is_list width) (listIdentity_is_list width) hZsList

end BvAndSimplifySupport
