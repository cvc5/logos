module

public import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import all Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.BvNaryXorSupport
import all Cpc.Proofs.RuleSupport.BvNaryXorSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

/-! Shared support for the three n-ary bit-vector XOR simplification rules. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvXorSimplifySupport

private def op : Term := Term.UOp UserOp.bvxor

private def xor (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bvnot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) x

private def eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private def guardedInner (ys zs second : Term) : Term :=
  __eo_list_concat op ys (xor second zs)

private def guardedInserted (ys zs first second : Term) : Term :=
  __eo_mk_apply (Term.Apply op first) (guardedInner ys zs second)

private def guardedLhs (xs ys zs first second : Term) : Term :=
  __eo_list_concat op xs (guardedInserted ys zs first second)

private def guardedBase (xs ys zs : Term) : Term :=
  __eo_list_singleton_elim op
    (__eo_list_concat op xs (__eo_list_concat op ys zs))

private def inner (ys zs second : Term) : Term :=
  __eo_list_concat_rec ys (xor second zs)

private def inserted (ys zs first second : Term) : Term :=
  xor first (inner ys zs second)

private def lhs (xs ys zs first second : Term) : Term :=
  __eo_list_concat_rec xs (inserted ys zs first second)

private def baseList (xs ys zs : Term) : Term :=
  __eo_list_concat_rec xs (__eo_list_concat_rec ys zs)

private def base (xs ys zs : Term) : Term :=
  __eo_list_singleton_elim op (baseList xs ys zs)

def term1 (xs ys zs x : Term) : Term :=
  eqTerm (lhs xs ys zs x x) (base xs ys zs)

def term2 (xs ys zs x : Term) : Term :=
  eqTerm (lhs xs ys zs x (bvnot x)) (bvnot (base xs ys zs))

def term3 (xs ys zs x : Term) : Term :=
  eqTerm (lhs xs ys zs (bvnot x) x) (bvnot (base xs ys zs))

def ListTypeOrNil (t : Term) (w : Nat) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ∨
    ∀ tail, __eo_list_concat_rec t tail = tail

private def zero (w : Nat) : Term :=
  Term.Binary (native_nat_to_int w) 0

private theorem zero_smt_type (w : Nat) :
    __smtx_typeof (__eo_to_smt (zero w)) = SmtType.BitVec w := by
  change __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) = _
  simp [__smtx_typeof, SmtEval.native_and, native_ite, native_zleq,
    native_zeq, native_nat_to_int, native_mod_total,
    SmtEval.native_int_to_nat, native_int_to_nat]

private theorem zero_is_list (w : Nat) :
    __eo_is_list op (zero w) = Term.Boolean true := by
  simp [op, zero, __eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
    __eo_is_list_nil_bvxor, __eo_to_z, __eo_is_eq, __eo_is_ok,
    __eo_requires, native_ite, native_and, native_not, native_teq,
    native_zeq]

@[simp] private theorem zero_concat_rec (w : Nat) (tail : Term) :
    __eo_list_concat_rec (zero w) tail = tail := by
  cases tail <;> rfl

private theorem lhs_congr_lists
    (xs xs' ys ys' zs first second : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    lhs xs ys zs first second = lhs xs' ys' zs first second := by
  unfold lhs inserted inner
  rw [hYs, hXs]

private theorem base_congr_lists
    (xs xs' ys ys' zs : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    base xs ys zs = base xs' ys' zs := by
  unfold base baseList
  rw [hYs, hXs]

private theorem term1_congr_lists
    (xs xs' ys ys' zs x : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    term1 xs ys zs x = term1 xs' ys' zs x := by
  unfold term1 eqTerm
  rw [lhs_congr_lists xs xs' ys ys' zs x x hXs hYs,
    base_congr_lists xs xs' ys ys' zs hXs hYs]

private theorem term2_congr_lists
    (xs xs' ys ys' zs x : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    term2 xs ys zs x = term2 xs' ys' zs x := by
  unfold term2 eqTerm
  rw [lhs_congr_lists xs xs' ys ys' zs x (bvnot x) hXs hYs,
    base_congr_lists xs xs' ys ys' zs hXs hYs]

private theorem term3_congr_lists
    (xs xs' ys ys' zs x : Term)
    (hXs : ∀ tail, __eo_list_concat_rec xs tail =
      __eo_list_concat_rec xs' tail)
    (hYs : ∀ tail, __eo_list_concat_rec ys tail =
      __eo_list_concat_rec ys' tail) :
    term3 xs ys zs x = term3 xs' ys' zs x := by
  unfold term3 eqTerm
  rw [lhs_congr_lists xs xs' ys ys' zs (bvnot x) x hXs hYs,
    base_congr_lists xs xs' ys ys' zs hXs hYs]

private def skeleton1 (xs ys zs x : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq) (guardedLhs xs ys zs x x))
    (guardedBase xs ys zs)

private def skeleton2 (xs ys zs x : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys zs x (bvnot x)))
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))

private def skeleton3 (xs ys zs x : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys zs (bvnot x) x))
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))

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
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true := by
  intro hLhs
  have hOuter := list_concat_parts_of_ne_stuck op xs
    (guardedInserted ys zs first second) (by
      simpa [guardedLhs] using hLhs)
  have hInsertedNe :=
    term_ne_stuck_of_is_list_true op (guardedInserted ys zs first second)
      hOuter.2
  have hInsertedEq :
      guardedInserted ys zs first second =
        xor first (guardedInner ys zs second) := by
    exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hInsertedNe
  have hInnerList :
      __eo_is_list op (guardedInner ys zs second) =
        Term.Boolean true := by
    rw [hInsertedEq] at hOuter
    exact eo_is_list_tail_true_of_cons_self op first
      (guardedInner ys zs second) hOuter.2
  have hInnerNe := term_ne_stuck_of_is_list_true op
    (guardedInner ys zs second) hInnerList
  have hInner := list_concat_parts_of_ne_stuck op ys (xor second zs) (by
    simpa [guardedInner] using hInnerNe)
  have hZs : __eo_is_list op zs = Term.Boolean true :=
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
        xor first (guardedInner ys zs second) :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hInsertedNe
  have hInnerList :
      __eo_is_list op (guardedInner ys zs second) =
        Term.Boolean true := by
    rw [hInsertedEq] at hOuter
    exact eo_is_list_tail_true_of_cons_self op first
      (guardedInner ys zs second) hOuter.2
  have hInnerNe := term_ne_stuck_of_is_list_true op
    (guardedInner ys zs second) hInnerList
  have hInnerParts := list_concat_parts_of_ne_stuck op ys
    (xor second zs) (by simpa [guardedInner] using hInnerNe)
  have hOuterReduce := list_concat_reduce op xs
    (guardedInserted ys zs first second) hOuter.1 hOuter.2
  have hInnerReduce := list_concat_reduce op ys (xor second zs)
    hInnerParts.1 hInnerParts.2
  calc
    guardedLhs xs ys zs first second =
        __eo_list_concat_rec xs (guardedInserted ys zs first second) := by
      simpa [guardedLhs] using hOuterReduce
    _ = __eo_list_concat_rec xs
        (xor first (guardedInner ys zs second)) := by rw [hInsertedEq]
    _ = lhs xs ys zs first second := by
      rw [show guardedInner ys zs second = inner ys zs second by
        simpa [guardedInner, inner] using hInnerReduce]
      rfl

private theorem guardedBase_eq_base_of_lists
    (xs ys zs : Term) :
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    guardedBase xs ys zs = base xs ys zs := by
  intro hXs hYs hZs
  have hYZReduce := list_concat_reduce op ys zs hYs hZs
  have hYZRecList :
      __eo_is_list op (__eo_list_concat_rec ys zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys zs hYs hZs
  have hYZGuardList :
      __eo_is_list op (__eo_list_concat op ys zs) = Term.Boolean true := by
    rw [hYZReduce]
    exact hYZRecList
  have hOuterReduce := list_concat_reduce op xs
    (__eo_list_concat op ys zs) hXs hYZGuardList
  unfold guardedBase base baseList
  rw [hOuterReduce, hYZReduce]

private theorem prog1_eq_skeleton_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_prog_bv_xor_simplify_1 xs ys zs x = skeleton1 xs ys zs x := by
  intro hXs hYs hZs hX
  unfold __eo_prog_bv_xor_simplify_1
  split
  · exact absurd rfl hXs
  · exact absurd rfl hYs
  · exact absurd rfl hZs
  · exact absurd rfl hX
  · rfl

private theorem prog2_eq_skeleton_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_prog_bv_xor_simplify_2 xs ys zs x = skeleton2 xs ys zs x := by
  intro hXs hYs hZs hX
  unfold __eo_prog_bv_xor_simplify_2
  split
  · exact absurd rfl hXs
  · exact absurd rfl hYs
  · exact absurd rfl hZs
  · exact absurd rfl hX
  · rfl

private theorem prog3_eq_skeleton_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_prog_bv_xor_simplify_3 xs ys zs x = skeleton3 xs ys zs x := by
  intro hXs hYs hZs hX
  unfold __eo_prog_bv_xor_simplify_3
  split
  · exact absurd rfl hXs
  · exact absurd rfl hYs
  · exact absurd rfl hZs
  · exact absurd rfl hX
  · rfl

private theorem ne_stuck_of_bitvec_smt_type (t : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.term_ne_stuck_of_has_smt_translation t (by
    intro hNone
    rw [hTy] at hNone
    cases hNone)

private theorem skeleton_lhs_ne_of_type_bool (left right : Term) :
    __eo_typeof
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) left) right) =
      Term.Bool ->
    left ≠ Term.Stuck := by
  intro hTy
  have hTop := term_ne_stuck_of_typeof_bool hTy
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFun

private theorem program1_lhs_ne_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs x x ≠ Term.Stuck := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  have hProgEq := prog1_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  apply skeleton_lhs_ne_of_type_bool
    (guardedLhs xs ys zs x x) (guardedBase xs ys zs)
  rw [hProgEq] at hResultTy
  exact hResultTy

private theorem program2_lhs_ne_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs x (bvnot x) ≠ Term.Stuck := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  have hProgEq := prog2_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  apply skeleton_lhs_ne_of_type_bool
    (guardedLhs xs ys zs x (bvnot x))
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))
  rw [hProgEq] at hResultTy
  exact hResultTy

private theorem program3_lhs_ne_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs (bvnot x) x ≠ Term.Stuck := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  have hProgEq := prog3_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  apply skeleton_lhs_ne_of_type_bool
    (guardedLhs xs ys zs (bvnot x) x)
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))
  rw [hProgEq] at hResultTy
  exact hResultTy

private theorem program1_lhs_ne
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs x x ≠ Term.Stuck := by
  intro hXsTy hYsTy hZsTy hXTy
  exact program1_lhs_ne_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)

private theorem program2_lhs_ne
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs x (bvnot x) ≠ Term.Stuck := by
  intro hXsTy hYsTy hZsTy hXTy
  exact program2_lhs_ne_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)

private theorem program3_lhs_ne
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs (bvnot x) x ≠ Term.Stuck := by
  intro hXsTy hYsTy hZsTy hXTy
  exact program3_lhs_ne_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)

theorem program1_eq_term_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_1 xs ys zs x = term1 xs ys zs x := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  have hProgEq := prog1_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  have hSkeletonTy : __eo_typeof (skeleton1 xs ys zs x) = Term.Bool := by
    rw [← hProgEq]
    exact hResultTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := program1_lhs_ne_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe hResultTy
  have hLists := guardedLhs_lists_of_ne_stuck xs ys zs x x hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck xs ys zs x x hLhsNe
  have hBaseEq := guardedBase_eq_base_of_lists xs ys zs
    hLists.1 hLists.2.1 hLists.2.2
  calc
    __eo_prog_bv_xor_simplify_1 xs ys zs x = skeleton1 xs ys zs x := hProgEq
    _ = eqTerm (guardedLhs xs ys zs x x) (guardedBase xs ys zs) := by
      unfold skeleton1 eqTerm
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
    _ = term1 xs ys zs x := by rw [hLhsEq, hBaseEq]; rfl

theorem program1_eq_term
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_1 xs ys zs x = term1 xs ys zs x := by
  intro hXsTy hYsTy hZsTy hXTy
  exact program1_eq_term_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)

theorem program2_eq_term_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_2 xs ys zs x = term2 xs ys zs x := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  have hProgEq := prog2_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  have hSkeletonTy : __eo_typeof (skeleton2 xs ys zs x) = Term.Bool := by
    rw [← hProgEq]
    exact hResultTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := program2_lhs_ne_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe hResultTy
  have hLists := guardedLhs_lists_of_ne_stuck
    xs ys zs x (bvnot x) hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck
    xs ys zs x (bvnot x) hLhsNe
  have hBaseEq := guardedBase_eq_base_of_lists xs ys zs
    hLists.1 hLists.2.1 hLists.2.2
  calc
    __eo_prog_bv_xor_simplify_2 xs ys zs x = skeleton2 xs ys zs x := hProgEq
    _ = eqTerm (guardedLhs xs ys zs x (bvnot x))
        (bvnot (guardedBase xs ys zs)) := by
      unfold skeleton2 eqTerm
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe]
      rfl
    _ = term2 xs ys zs x := by rw [hLhsEq, hBaseEq]; rfl

theorem program2_eq_term
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_2 xs ys zs x = term2 xs ys zs x := by
  intro hXsTy hYsTy hZsTy hXTy
  exact program2_eq_term_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)

theorem program3_eq_term_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_3 xs ys zs x = term3 xs ys zs x := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  have hProgEq := prog3_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  have hSkeletonTy : __eo_typeof (skeleton3 xs ys zs x) = Term.Bool := by
    rw [← hProgEq]
    exact hResultTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := program3_lhs_ne_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe hResultTy
  have hLists := guardedLhs_lists_of_ne_stuck
    xs ys zs (bvnot x) x hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck
    xs ys zs (bvnot x) x hLhsNe
  have hBaseEq := guardedBase_eq_base_of_lists xs ys zs
    hLists.1 hLists.2.1 hLists.2.2
  calc
    __eo_prog_bv_xor_simplify_3 xs ys zs x = skeleton3 xs ys zs x := hProgEq
    _ = eqTerm (guardedLhs xs ys zs (bvnot x) x)
        (bvnot (guardedBase xs ys zs)) := by
      unfold skeleton3 eqTerm
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe]
      rfl
    _ = term3 xs ys zs x := by rw [hLhsEq, hBaseEq]; rfl

theorem program3_eq_term
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_3 xs ys zs x = term3 xs ys zs x := by
  intro hXsTy hYsTy hZsTy hXTy
  exact program3_eq_term_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)

private theorem smtx_typeof_bvxor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvxor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_eval_bvxor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvxor x y) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem bvxor_smt_type
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (xor x y)) = SmtType.BitVec w := by
  intro hXTy hYTy
  change __smtx_typeof
      (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [smtx_typeof_bvxor_term_eq]
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

private theorem typeof_bvxor_args_of_result_bitvec
    (x y width : Term) :
    __eo_typeof (xor x y) =
        Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro h
  have hNe :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    exact (show __eo_typeof (xor x y) ≠ Term.Stuck by
      rw [h]
      intro hBad
      cases hBad)
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
    __eo_is_list op a = Term.Boolean true ->
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
        (typeof_bvxor_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) width (by simpa [xor, op] using hTy)).2
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hTy

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
    __eo_is_list op a = Term.Boolean true ->
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
        (typeof_bvxor_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) (Term.Numeral W)
          (by simpa [xor, op] using hConcatTy)).1
      have hNonNone :
          term_has_non_none_type
            (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt xs)) := by
        exact hATrans
      rcases bv_binop_args_of_non_none (op := SmtTerm.bvxor)
          (show
            __smtx_typeof (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt xs)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt x))
                (__smtx_typeof (__eo_to_smt xs)) by
            rw [__smtx_typeof.eq_44]) hNonNone with
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
          (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt xs)) = _
      rw [__smtx_typeof.eq_44]
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

theorem program1_lists_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  exact guardedLhs_lists_of_ne_stuck xs ys zs x x
    (program1_lhs_ne_of_ne_stuck xs ys zs x
      hXsNe hYsNe hZsNe hXNe hResultTy)

theorem program2_lists_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  exact guardedLhs_lists_of_ne_stuck xs ys zs x (bvnot x)
    (program2_lhs_ne_of_ne_stuck xs ys zs x
      hXsNe hYsNe hZsNe hXNe hResultTy)

theorem program3_lists_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true := by
  intro hXsNe hYsNe hZsNe hXNe hResultTy
  exact guardedLhs_lists_of_ne_stuck xs ys zs (bvnot x) x
    (program3_lhs_ne_of_ne_stuck xs ys zs x
      hXsNe hYsNe hZsNe hXNe hResultTy)

private theorem lhs_component_types
    (xs ys zs first second : Term) :
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
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
    exact hInsertedNe
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
  have hSecondZsTy := list_concat_rec_right_type ys (xor second zs) width
    hYsList (by simpa [inner] using hInnerTy)
  have hSecondZsParts := typeof_bvxor_args_of_result_bitvec
    second zs width hSecondZsTy
  exact ⟨width, by simpa [lhs] using hLhsTy, hInnerTy, hFirstTy,
    hSecondZsParts.1, hSecondZsParts.2⟩

private theorem inferred_argument_types_common
    (xs ys zs first second x : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_typeof (lhs xs ys zs first second) ≠ Term.Stuck ->
    (∀ width,
      __eo_typeof first = Term.Apply (Term.UOp UserOp.BitVec) width ->
      __eo_typeof second = Term.Apply (Term.UOp UserOp.BitVec) width ->
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width) ->
    ∃ width : Nat,
      ListTypeOrNil xs width ∧
        ListTypeOrNil ys width ∧
        __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec width ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec width := by
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
    ys (xor second zs) W hYsTrans hYsList (by simp [xor])
      (by simpa [inner] using hInnerTy) hW0
  have hXsTypeOrNil := list_smt_type_or_nil_of_concat_type
    xs (inserted ys zs first second) W hXsTrans hXsList
      (by simp [inserted, xor]) (by simpa [lhs] using hLhsTy) hW0
  exact ⟨native_int_to_nat W,
    by simpa [ListTypeOrNil] using hXsTypeOrNil,
    by simpa [ListTypeOrNil] using hYsTypeOrNil, hZsTy, hXTy⟩

theorem inferred_argument_types1
    (xs ys zs x : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_typeof (term1 xs ys zs x) = Term.Bool ->
    ∃ width : Nat,
      ListTypeOrNil xs width ∧
        ListTypeOrNil ys width ∧
        __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec width ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec width := by
  intro hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hResultTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs ys zs x x)) (__eo_typeof (base xs ys zs))
    (by have hsimpa := hResultTy; (try simp [term1, eqTerm] at hsimpa ⊢); exact hsimpa)
  exact inferred_argument_types_common xs ys zs x x x
    hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hSides.1
      (fun _ hFirst _ => hFirst)

theorem inferred_argument_types2
    (xs ys zs x : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_typeof (term2 xs ys zs x) = Term.Bool ->
    ∃ width : Nat,
      ListTypeOrNil xs width ∧
        ListTypeOrNil ys width ∧
        __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec width ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec width := by
  intro hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hResultTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs ys zs x (bvnot x)))
    (__eo_typeof (bvnot (base xs ys zs)))
    (by have hsimpa := hResultTy; (try simp [term2, eqTerm] at hsimpa ⊢); exact hsimpa)
  exact inferred_argument_types_common xs ys zs x (bvnot x) x
    hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hSides.1
      (fun _ hFirst _ => hFirst)

theorem inferred_argument_types3
    (xs ys zs x : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation x ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_typeof (term3 xs ys zs x) = Term.Bool ->
    ∃ width : Nat,
      ListTypeOrNil xs width ∧
        ListTypeOrNil ys width ∧
        __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec width ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec width := by
  intro hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hResultTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs ys zs (bvnot x) x))
    (__eo_typeof (bvnot (base xs ys zs)))
    (by have hsimpa := hResultTy; (try simp [term3, eqTerm] at hsimpa ⊢); exact hsimpa)
  exact inferred_argument_types_common xs ys zs (bvnot x) x x
    hXsTrans hYsTrans hZsTrans hXTrans hXsList hYsList hSides.1
      (fun _ _ hSecond => hSecond)

private theorem program1_lists
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  exact guardedLhs_lists_of_ne_stuck xs ys zs x x
    (program1_lhs_ne xs ys zs x w
      hXsTy hYsTy hZsTy hXTy hResultTy)

private theorem program2_lists
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  exact guardedLhs_lists_of_ne_stuck xs ys zs x (bvnot x)
    (program2_lhs_ne xs ys zs x w
      hXsTy hYsTy hZsTy hXTy hResultTy)

private theorem program3_lists
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  exact guardedLhs_lists_of_ne_stuck xs ys zs (bvnot x) x
    (program3_lhs_ne xs ys zs x w
      hXsTy hYsTy hZsTy hXTy hResultTy)

private theorem lhs_base_smt_types
    (xs ys zs first second : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt first) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt second) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt (lhs xs ys zs first second)) =
        SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt (base xs ys zs)) =
        SmtType.BitVec w := by
  intro hXsTy hYsTy hZsTy hFirstTy hSecondTy
    hXsList hYsList hZsList
  have hSecondZsList :
      __eo_is_list op (xor second zs) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op second zs
      (by decide) hZsList
  have hSecondZsTy := bvxor_smt_type second zs w hSecondTy hZsTy
  have hInnerList :
      __eo_is_list op (inner ys zs second) = Term.Boolean true := by
    exact eo_list_concat_rec_is_list_true_of_lists op ys (xor second zs)
      hYsList hSecondZsList
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (inner ys zs second)) =
        SmtType.BitVec w := by
    exact BvNaryXorSupport.listConcatRecSmtType ys (xor second zs) w
      (by simpa [op] using hYsList)
      (by simpa [op] using hSecondZsList) hYsTy hSecondZsTy
  have hInsertedList :
      __eo_is_list op (inserted ys zs first second) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op first (inner ys zs second)
      (by decide) hInnerList
  have hInsertedTy :=
    bvxor_smt_type first (inner ys zs second) w hFirstTy hInnerTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs xs ys zs first second)) =
        SmtType.BitVec w := by
    exact BvNaryXorSupport.listConcatRecSmtType xs
      (inserted ys zs first second) w
      (by simpa [op] using hXsList)
      (by simpa [op] using hInsertedList) hXsTy hInsertedTy
  have hYZList :
      __eo_is_list op (__eo_list_concat_rec ys zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys zs hYsList hZsList
  have hYZTy := BvNaryXorSupport.listConcatRecSmtType ys zs w
    (by simpa [op] using hYsList) (by simpa [op] using hZsList)
    hYsTy hZsTy
  have hBaseListList :
      __eo_is_list op (baseList xs ys zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op xs
      (__eo_list_concat_rec ys zs) hXsList hYZList
  have hBaseListTy := BvNaryXorSupport.listConcatRecSmtType xs
    (__eo_list_concat_rec ys zs) w
    (by simpa [op] using hXsList) (by simpa [op] using hYZList)
    hXsTy hYZTy
  have hBaseTy := BvNaryXorSupport.listSingletonElimSmtType
    (baseList xs ys zs) w (by simpa [op] using hBaseListList) hBaseListTy
  exact ⟨hLhsTy, by have hsimpa := hBaseTy; (try simp [base] at hsimpa ⊢); exact hsimpa⟩

private theorem eval_lhs_base
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs first second : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt first) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt second) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    __smtx_model_eval M
        (__eo_to_smt (lhs xs ys zs first second)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M (__eo_to_smt xs))
        (__smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt first))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval_bvxor
              (__smtx_model_eval M (__eo_to_smt second))
              (__smtx_model_eval M (__eo_to_smt zs))))) ∧
      __smtx_model_eval M (__eo_to_smt (base xs ys zs)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt xs))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval M (__eo_to_smt zs))) := by
  intro hXsTy hYsTy hZsTy hFirstTy hSecondTy
    hXsList hYsList hZsList
  have hSecondZsList :
      __eo_is_list op (xor second zs) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op second zs
      (by decide) hZsList
  have hSecondZsTy := bvxor_smt_type second zs w hSecondTy hZsTy
  have hInnerList :
      __eo_is_list op (inner ys zs second) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys (xor second zs)
      hYsList hSecondZsList
  have hInnerTy := BvNaryXorSupport.listConcatRecSmtType
    ys (xor second zs) w
    (by simpa [op] using hYsList)
    (by simpa [op] using hSecondZsList) hYsTy hSecondZsTy
  have hInsertedList :
      __eo_is_list op (inserted ys zs first second) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op first (inner ys zs second)
      (by decide) hInnerList
  have hInsertedTy :=
    bvxor_smt_type first (inner ys zs second) w hFirstTy hInnerTy
  have hYZList :
      __eo_is_list op (__eo_list_concat_rec ys zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys zs hYsList hZsList
  have hYZTy := BvNaryXorSupport.listConcatRecSmtType ys zs w
    (by simpa [op] using hYsList) (by simpa [op] using hZsList)
    hYsTy hZsTy
  have hBaseListList :
      __eo_is_list op (baseList xs ys zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op xs
      (__eo_list_concat_rec ys zs) hXsList hYZList
  have hBaseListTy := BvNaryXorSupport.listConcatRecSmtType xs
    (__eo_list_concat_rec ys zs) w
    (by simpa [op] using hXsList) (by simpa [op] using hYZList)
    hXsTy hYZTy
  have hLhsConcat := BvNaryXorSupport.listConcatRecEvalEq M hM xs
    (inserted ys zs first second) w
    (by simpa [op] using hXsList)
    (by simpa [op] using hInsertedList) hXsTy hInsertedTy
  have hInnerConcat := BvNaryXorSupport.listConcatRecEvalEq M hM ys
    (xor second zs) w
    (by simpa [op] using hYsList)
    (by simpa [op] using hSecondZsList) hYsTy hSecondZsTy
  have hYZConcat := BvNaryXorSupport.listConcatRecEvalEq M hM ys zs w
    (by simpa [op] using hYsList) (by simpa [op] using hZsList)
    hYsTy hZsTy
  have hBaseConcat := BvNaryXorSupport.listConcatRecEvalEq M hM xs
    (__eo_list_concat_rec ys zs) w
    (by simpa [op] using hXsList) (by simpa [op] using hYZList)
    hXsTy hYZTy
  have hSingleton := BvNaryXorSupport.listSingletonElimEvalEq M hM
    (baseList xs ys zs) w (by simpa [op] using hBaseListList) hBaseListTy
  have hSecondZsEval :
      __smtx_model_eval M (__eo_to_smt (xor second zs)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt second))
          (__smtx_model_eval M (__eo_to_smt zs)) := by
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt second) (__eo_to_smt zs)) = _
    exact smtx_eval_bvxor_term_eq M _ _
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt (inner ys zs second)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt ys))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt second))
            (__smtx_model_eval M (__eo_to_smt zs))) := by
    unfold inner
    rw [hInnerConcat]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt ys)
          (__eo_to_smt (xor second zs))) = _
    rw [smtx_eval_bvxor_term_eq, hSecondZsEval]
  have hInsertedEval :
      __smtx_model_eval M
          (__eo_to_smt (inserted ys zs first second)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt first))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval_bvxor
              (__smtx_model_eval M (__eo_to_smt second))
              (__smtx_model_eval M (__eo_to_smt zs)))) := by
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt first)
          (__eo_to_smt (inner ys zs second))) = _
    rw [smtx_eval_bvxor_term_eq, hInnerEval]
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt (lhs xs ys zs first second)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt xs))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt first))
            (__smtx_model_eval_bvxor
              (__smtx_model_eval M (__eo_to_smt ys))
              (__smtx_model_eval_bvxor
                (__smtx_model_eval M (__eo_to_smt second))
                (__smtx_model_eval M (__eo_to_smt zs))))) := by
    unfold lhs
    rw [hLhsConcat]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt xs)
          (__eo_to_smt (inserted ys zs first second))) = _
    rw [smtx_eval_bvxor_term_eq, hInsertedEval]
  have hYZEval :
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec ys zs)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt ys))
          (__smtx_model_eval M (__eo_to_smt zs)) := by
    rw [hYZConcat]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt ys) (__eo_to_smt zs)) = _
    exact smtx_eval_bvxor_term_eq M _ _
  have hBaseListEval :
      __smtx_model_eval M (__eo_to_smt (baseList xs ys zs)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt xs))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval M (__eo_to_smt zs))) := by
    unfold baseList
    rw [hBaseConcat]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt xs)
          (__eo_to_smt (__eo_list_concat_rec ys zs))) = _
    rw [smtx_eval_bvxor_term_eq, hYZEval]
  have hBaseEval :
      __smtx_model_eval M (__eo_to_smt (base xs ys zs)) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt xs))
          (__smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval M (__eo_to_smt zs))) := by
    rw [show base xs ys zs =
        __eo_list_singleton_elim op (baseList xs ys zs) by rfl]
    rw [show __smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim op (baseList xs ys zs))) =
        __smtx_model_eval M (__eo_to_smt (baseList xs ys zs)) by
      simpa [op] using hSingleton]
    exact hBaseListEval
  exact ⟨hLhsEval, hBaseEval⟩

private theorem typed_term1_core
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (term1 xs ys zs x) := by
  intro hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hTypes := lhs_base_smt_types xs ys zs x x w
    hXsTy hYsTy hZsTy hXTy hXTy hXsList hYsList hZsList
  simpa [term1, eqTerm] using
    (RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys zs x x) (base xs ys zs)
      (by rw [hTypes.1, hTypes.2]) (by rw [hTypes.1]; simp))

private theorem typed_term2_core
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (term2 xs ys zs x) := by
  intro hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hNotXTy := bvnot_smt_type x w hXTy
  have hTypes := lhs_base_smt_types xs ys zs x (bvnot x) w
    hXsTy hYsTy hZsTy hXTy hNotXTy hXsList hYsList hZsList
  have hRhsTy := bvnot_smt_type (base xs ys zs) w hTypes.2
  simpa [term2, eqTerm] using
    (RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys zs x (bvnot x)) (bvnot (base xs ys zs))
      (by rw [hTypes.1, hRhsTy]) (by rw [hTypes.1]; simp))

private theorem typed_term3_core
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (term3 xs ys zs x) := by
  intro hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hNotXTy := bvnot_smt_type x w hXTy
  have hTypes := lhs_base_smt_types xs ys zs (bvnot x) x w
    hXsTy hYsTy hZsTy hNotXTy hXTy hXsList hYsList hZsList
  have hRhsTy := bvnot_smt_type (base xs ys zs) w hTypes.2
  simpa [term3, eqTerm] using
    (RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys zs (bvnot x) x) (bvnot (base xs ys zs))
      (by rw [hTypes.1, hRhsTy]) (by rw [hTypes.1]; simp))

theorem typed_term1
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term1 xs ys zs x) := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := program1_lists xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  exact typed_term1_core xs ys zs x w hXsTy hYsTy hZsTy hXTy
    hLists.1 hLists.2.1 hLists.2.2

theorem typed_term2
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term2 xs ys zs x) := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := program2_lists xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  exact typed_term2_core xs ys zs x w hXsTy hYsTy hZsTy hXTy
    hLists.1 hLists.2.1 hLists.2.2

theorem typed_term3
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term3 xs ys zs x) := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := program3_lists xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  exact typed_term3_core xs ys zs x w hXsTy hYsTy hZsTy hXTy
    hLists.1 hLists.2.1 hLists.2.2

private theorem concat_rec_equiv_zero
    (t : Term) (w : Nat) :
    (∀ tail, __eo_list_concat_rec t tail = tail) ->
    ∀ tail, __eo_list_concat_rec t tail =
      __eo_list_concat_rec (zero w) tail := by
  intro hNil tail
  rw [hNil, zero_concat_rec]

theorem typed_term1_of_type_or_nil
    (xs ys zs x : Term) (w : Nat) :
    ListTypeOrNil xs w ->
    ListTypeOrNil ys w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (term1 xs ys zs x) := by
  intro hXs hYs hZsTy hXTy hXsList hYsList hZsList
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact typed_term1_core xs ys zs x w hXsTy hYsTy hZsTy hXTy
        hXsList hYsList hZsList
    · rw [term1_congr_lists xs xs ys (zero w) zs x
        (fun _ => rfl) (concat_rec_equiv_zero ys w hYsNil)]
      exact typed_term1_core xs (zero w) zs x w hXsTy
        (zero_smt_type w) hZsTy hXTy hXsList (zero_is_list w) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [term1_congr_lists xs (zero w) ys ys zs x
        (concat_rec_equiv_zero xs w hXsNil) (fun _ => rfl)]
      exact typed_term1_core (zero w) ys zs x w (zero_smt_type w)
        hYsTy hZsTy hXTy (zero_is_list w) hYsList hZsList
    · rw [term1_congr_lists xs (zero w) ys (zero w) zs x
        (concat_rec_equiv_zero xs w hXsNil)
        (concat_rec_equiv_zero ys w hYsNil)]
      exact typed_term1_core (zero w) (zero w) zs x w
        (zero_smt_type w) (zero_smt_type w) hZsTy hXTy
        (zero_is_list w) (zero_is_list w) hZsList

theorem typed_term2_of_type_or_nil
    (xs ys zs x : Term) (w : Nat) :
    ListTypeOrNil xs w ->
    ListTypeOrNil ys w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (term2 xs ys zs x) := by
  intro hXs hYs hZsTy hXTy hXsList hYsList hZsList
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact typed_term2_core xs ys zs x w hXsTy hYsTy hZsTy hXTy
        hXsList hYsList hZsList
    · rw [term2_congr_lists xs xs ys (zero w) zs x
        (fun _ => rfl) (concat_rec_equiv_zero ys w hYsNil)]
      exact typed_term2_core xs (zero w) zs x w hXsTy
        (zero_smt_type w) hZsTy hXTy hXsList (zero_is_list w) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [term2_congr_lists xs (zero w) ys ys zs x
        (concat_rec_equiv_zero xs w hXsNil) (fun _ => rfl)]
      exact typed_term2_core (zero w) ys zs x w (zero_smt_type w)
        hYsTy hZsTy hXTy (zero_is_list w) hYsList hZsList
    · rw [term2_congr_lists xs (zero w) ys (zero w) zs x
        (concat_rec_equiv_zero xs w hXsNil)
        (concat_rec_equiv_zero ys w hYsNil)]
      exact typed_term2_core (zero w) (zero w) zs x w
        (zero_smt_type w) (zero_smt_type w) hZsTy hXTy
        (zero_is_list w) (zero_is_list w) hZsList

theorem typed_term3_of_type_or_nil
    (xs ys zs x : Term) (w : Nat) :
    ListTypeOrNil xs w ->
    ListTypeOrNil ys w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    RuleProofs.eo_has_bool_type (term3 xs ys zs x) := by
  intro hXs hYs hZsTy hXTy hXsList hYsList hZsList
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact typed_term3_core xs ys zs x w hXsTy hYsTy hZsTy hXTy
        hXsList hYsList hZsList
    · rw [term3_congr_lists xs xs ys (zero w) zs x
        (fun _ => rfl) (concat_rec_equiv_zero ys w hYsNil)]
      exact typed_term3_core xs (zero w) zs x w hXsTy
        (zero_smt_type w) hZsTy hXTy hXsList (zero_is_list w) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [term3_congr_lists xs (zero w) ys ys zs x
        (concat_rec_equiv_zero xs w hXsNil) (fun _ => rfl)]
      exact typed_term3_core (zero w) ys zs x w (zero_smt_type w)
        hYsTy hZsTy hXTy (zero_is_list w) hYsList hZsList
    · rw [term3_congr_lists xs (zero w) ys (zero w) zs x
        (concat_rec_equiv_zero xs w hXsNil)
        (concat_rec_equiv_zero ys w hYsNil)]
      exact typed_term3_core (zero w) (zero w) zs x w
        (zero_smt_type w) (zero_smt_type w) hZsTy hXTy
        (zero_is_list w) (zero_is_list w) hZsList

private theorem facts_term1_core
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    eo_interprets M (term1 xs ys zs x) true := by
  intro hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hBool := typed_term1_core xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hEvals := eval_lhs_base M hM xs ys zs x x w
    hXsTy hYsTy hZsTy hXTy hXTy
    hXsList hYsList hZsList
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) w
      hXsTy with ⟨nxs, hXsEval, hXsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt ys) w
      hYsTy with ⟨nys, hYsEval, hYsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) w
      hZsTy with ⟨nzs, hZsEval, hZsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, hXCan⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs xs ys zs x x)) =
        __smtx_model_eval M (__eo_to_smt (base xs ys zs)) := by
    rw [hEvals.1, hEvals.2, hXsEval, hYsEval, hZsEval, hXEval]
    exact bvxor_cancel_nested_eval w nxs nx nys nzs
      hXsCan hXCan hYsCan hZsCan
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (lhs xs ys zs x x)))
      (__smtx_model_eval M (__eo_to_smt (base xs ys zs)))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_term1
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    eo_interprets M (term1 xs ys zs x) true := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := program1_lists xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  exact facts_term1_core M hM xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hLists.1 hLists.2.1 hLists.2.2

private theorem facts_term2_core
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    eo_interprets M (term2 xs ys zs x) true := by
  intro hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hBool := typed_term2_core xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hNotXTy := bvnot_smt_type x w hXTy
  have hEvals := eval_lhs_base M hM xs ys zs x (bvnot x) w
    hXsTy hYsTy hZsTy hXTy hNotXTy
    hXsList hYsList hZsList
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) w
      hXsTy with ⟨nxs, hXsEval, hXsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt ys) w
      hYsTy with ⟨nys, hYsEval, hYsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) w
      hZsTy with ⟨nzs, hZsEval, hZsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, hXCan⟩
  have hNotXEval :
      __smtx_model_eval M (__eo_to_smt (bvnot x)) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) nx) := by
    change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
    rw [smtx_eval_bvnot_term_eq, hXEval]
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (lhs xs ys zs x (bvnot x))) =
        __smtx_model_eval M
          (__eo_to_smt (bvnot (base xs ys zs))) := by
    rw [hEvals.1]
    change _ = __smtx_model_eval M
      (SmtTerm.bvnot (__eo_to_smt (base xs ys zs)))
    rw [smtx_eval_bvnot_term_eq, hEvals.2, hNotXEval,
      hXsEval, hYsEval, hZsEval, hXEval]
    exact bvxor_not_cancel_nested_eval w nxs nx nys nzs
      hXsCan hXCan hYsCan hZsCan
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (lhs xs ys zs x (bvnot x))))
      (__smtx_model_eval M
        (__eo_to_smt (bvnot (base xs ys zs))))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_term2
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    eo_interprets M (term2 xs ys zs x) true := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := program2_lists xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  exact facts_term2_core M hM xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hLists.1 hLists.2.1 hLists.2.2

private theorem facts_term3_core
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    eo_interprets M (term3 xs ys zs x) true := by
  intro hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hBool := typed_term3_core xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hXsList hYsList hZsList
  have hNotXTy := bvnot_smt_type x w hXTy
  have hEvals := eval_lhs_base M hM xs ys zs (bvnot x) x w
    hXsTy hYsTy hZsTy hNotXTy hXTy
    hXsList hYsList hZsList
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) w
      hXsTy with ⟨nxs, hXsEval, hXsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt ys) w
      hYsTy with ⟨nys, hYsEval, hYsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) w
      hZsTy with ⟨nzs, hZsEval, hZsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, hXCan⟩
  have hNotXEval :
      __smtx_model_eval M (__eo_to_smt (bvnot x)) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) nx) := by
    change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
    rw [smtx_eval_bvnot_term_eq, hXEval]
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (lhs xs ys zs (bvnot x) x)) =
        __smtx_model_eval M
          (__eo_to_smt (bvnot (base xs ys zs))) := by
    rw [hEvals.1]
    change _ = __smtx_model_eval M
      (SmtTerm.bvnot (__eo_to_smt (base xs ys zs)))
    rw [smtx_eval_bvnot_term_eq, hEvals.2, hNotXEval,
      hXsEval, hYsEval, hZsEval, hXEval]
    exact bvxor_not_cancel_nested_eval_rev w nxs nx nys nzs
      hXsCan hXCan hYsCan hZsCan
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (lhs xs ys zs (bvnot x) x)))
      (__smtx_model_eval M
        (__eo_to_smt (bvnot (base xs ys zs))))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_term3
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    eo_interprets M (term3 xs ys zs x) true := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := program3_lists xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  exact facts_term3_core M hM xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hLists.1 hLists.2.1 hLists.2.2

theorem facts_term1_of_type_or_nil
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    ListTypeOrNil xs w ->
    ListTypeOrNil ys w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    eo_interprets M (term1 xs ys zs x) true := by
  intro hXs hYs hZsTy hXTy hXsList hYsList hZsList
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact facts_term1_core M hM xs ys zs x w hXsTy hYsTy hZsTy hXTy
        hXsList hYsList hZsList
    · rw [term1_congr_lists xs xs ys (zero w) zs x
        (fun _ => rfl) (concat_rec_equiv_zero ys w hYsNil)]
      exact facts_term1_core M hM xs (zero w) zs x w hXsTy
        (zero_smt_type w) hZsTy hXTy hXsList (zero_is_list w) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [term1_congr_lists xs (zero w) ys ys zs x
        (concat_rec_equiv_zero xs w hXsNil) (fun _ => rfl)]
      exact facts_term1_core M hM (zero w) ys zs x w (zero_smt_type w)
        hYsTy hZsTy hXTy (zero_is_list w) hYsList hZsList
    · rw [term1_congr_lists xs (zero w) ys (zero w) zs x
        (concat_rec_equiv_zero xs w hXsNil)
        (concat_rec_equiv_zero ys w hYsNil)]
      exact facts_term1_core M hM (zero w) (zero w) zs x w
        (zero_smt_type w) (zero_smt_type w) hZsTy hXTy
        (zero_is_list w) (zero_is_list w) hZsList

theorem facts_term2_of_type_or_nil
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    ListTypeOrNil xs w ->
    ListTypeOrNil ys w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    eo_interprets M (term2 xs ys zs x) true := by
  intro hXs hYs hZsTy hXTy hXsList hYsList hZsList
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact facts_term2_core M hM xs ys zs x w hXsTy hYsTy hZsTy hXTy
        hXsList hYsList hZsList
    · rw [term2_congr_lists xs xs ys (zero w) zs x
        (fun _ => rfl) (concat_rec_equiv_zero ys w hYsNil)]
      exact facts_term2_core M hM xs (zero w) zs x w hXsTy
        (zero_smt_type w) hZsTy hXTy hXsList (zero_is_list w) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [term2_congr_lists xs (zero w) ys ys zs x
        (concat_rec_equiv_zero xs w hXsNil) (fun _ => rfl)]
      exact facts_term2_core M hM (zero w) ys zs x w (zero_smt_type w)
        hYsTy hZsTy hXTy (zero_is_list w) hYsList hZsList
    · rw [term2_congr_lists xs (zero w) ys (zero w) zs x
        (concat_rec_equiv_zero xs w hXsNil)
        (concat_rec_equiv_zero ys w hYsNil)]
      exact facts_term2_core M hM (zero w) (zero w) zs x w
        (zero_smt_type w) (zero_smt_type w) hZsTy hXTy
        (zero_is_list w) (zero_is_list w) hZsList

theorem facts_term3_of_type_or_nil
    (M : SmtModel) (hM : model_wf M)
    (xs ys zs x : Term) (w : Nat) :
    ListTypeOrNil xs w ->
    ListTypeOrNil ys w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) ys = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    eo_interprets M (term3 xs ys zs x) true := by
  intro hXs hYs hZsTy hXTy hXsList hYsList hZsList
  rcases hXs with hXsTy | hXsNil
  · rcases hYs with hYsTy | hYsNil
    · exact facts_term3_core M hM xs ys zs x w hXsTy hYsTy hZsTy hXTy
        hXsList hYsList hZsList
    · rw [term3_congr_lists xs xs ys (zero w) zs x
        (fun _ => rfl) (concat_rec_equiv_zero ys w hYsNil)]
      exact facts_term3_core M hM xs (zero w) zs x w hXsTy
        (zero_smt_type w) hZsTy hXTy hXsList (zero_is_list w) hZsList
  · rcases hYs with hYsTy | hYsNil
    · rw [term3_congr_lists xs (zero w) ys ys zs x
        (concat_rec_equiv_zero xs w hXsNil) (fun _ => rfl)]
      exact facts_term3_core M hM (zero w) ys zs x w (zero_smt_type w)
        hYsTy hZsTy hXTy (zero_is_list w) hYsList hZsList
    · rw [term3_congr_lists xs (zero w) ys (zero w) zs x
        (concat_rec_equiv_zero xs w hXsNil)
        (concat_rec_equiv_zero ys w hYsNil)]
      exact facts_term3_core M hM (zero w) (zero w) zs x w
        (zero_smt_type w) (zero_smt_type w) hZsTy hXTy
        (zero_is_list w) (zero_is_list w) hZsList

end BvXorSimplifySupport
