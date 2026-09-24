module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import all Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
public import Cpc.Proofs.RuleSupport.BvNaryXorSupport
import all Cpc.Proofs.RuleSupport.BvNaryXorSupport

public section

/-! Support for eliminating an all-ones element from an n-ary bit-vector XOR. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvXorOnesSupport

def insertedTail (zs n w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
    (bvAllOnesConst n w)) zs

def lhs (xs zs n w : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.bvxor) xs (insertedTail zs n w)

def baseList (xs zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.bvxor) xs zs

def base (xs zs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.bvxor) (baseList xs zs)

def rhs (xs zs : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) (base xs zs)

def term (xs zs n w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs zs n w))
    (rhs xs zs)

private theorem native_width_roundtrip
    (W : native_Int) :
    native_zleq 0 W = true ->
    native_nat_to_int (native_int_to_nat W) = W := by
  intro hW
  have hWProp : (0 : native_Int) <= W := by
    simpa [SmtEval.native_zleq] using hW
  have hInt : (Int.ofNat (Int.toNat W) : Int) = W :=
    Int.toNat_of_nonneg hWProp
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem list_concat_eq_rec_of_lists
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) z = Term.Boolean true ->
    __eo_list_concat (Term.UOp UserOp.bvxor) a z =
      __eo_list_concat_rec a z := by
  intro hA hZ
  simp [__eo_list_concat, hA, hZ, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem list_concat_lists_of_ne_stuck
    (f a b : Term) :
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
          (__eo_list_concat_rec a b) ≠ Term.Stuck := by
    exact eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hReq
  have hB := support_eo_requires_cond_eq_of_non_stuck hTail
  exact ⟨hA, hB⟩

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

private theorem context
    (xs zs n w : Term) :
    __eo_typeof (term xs zs n w) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true := by
  intro hResultTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs zs n w)) (__eo_typeof (rhs xs zs))
    (by have hsimpa := hResultTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : lhs xs zs n w ≠ Term.Stuck := by
    intro h
    apply hSides.1
    rw [h]
    rfl
  have hLists := list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.bvxor) xs (insertedTail zs n w) hLhsNe
  have hZsList := eo_is_list_tail_true_of_cons_self
    (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs hLists.2
  exact ⟨hLists.1, hZsList⟩

theorem typeof_bvand_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
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

theorem typeof_bvxor_args_of_result_bitvec
    (x y width : Term) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y) =
        Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro h
  change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) = _ at h
  have hNe :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    rw [h]
    intro hBad
    cases hBad
  rcases typeof_bvand_arg_types_of_ne_stuck hNe with
    ⟨actualWidth, hx, hy⟩
  have hWidthNe : actualWidth ≠ Term.Stuck := by
    intro hStuck
    apply hNe
    rw [hx, hy, hStuck]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hReduce :
      __eo_typeof_bvand
          (Term.Apply (Term.UOp UserOp.BitVec) actualWidth)
          (Term.Apply (Term.UOp UserOp.BitVec) actualWidth) =
        Term.Apply (Term.UOp UserOp.BitVec) actualWidth := by
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hWidthNe]
  have hWidth : actualWidth = width := by
    rw [hx, hy, hReduce] at h
    cases h
    rfl
  subst width
  exact ⟨hx, hy⟩

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

private theorem mk_apply_eq_apply_of_ne_stuck
    (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hF hX
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem list_concat_rec_right_type
    (a z width : Term) :
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [__eo_is_list] at hList
  | case2 a h =>
      have hEq : __eo_list_concat_rec a Term.Stuck = Term.Stuck := by
        cases a <;> rfl
      rw [hEq] at hTy
      exact hTy
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true
        (Term.UOp UserOp.bvxor) f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self
        (Term.UOp UserOp.bvxor) x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        rw [list_concat_rec_cons_of_right_ne_stuck
              (Term.UOp UserOp.bvxor) x xs z hz,
          h, mk_apply_right_stuck_local] at hTy
        cases hTy
      rw [list_concat_rec_cons_of_right_ne_stuck
            (Term.UOp UserOp.bvxor) x xs z hz,
        mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hTailNe] at hTy
      exact ih hTailList
        (typeof_bvxor_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) width hTy).2
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hTy

private theorem list_smt_type_or_nil_of_concat_type
    (a z : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation a ->
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
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
      simp [__eo_is_list] at hAList
  | case2 a hA =>
      exact False.elim (hZNe rfl)
  | case3 f x xs z hz ih =>
      have hf : f = Term.UOp UserOp.bvxor :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.bvxor) f x xs hAList
      subst f
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro hTail
        rw [list_concat_rec_cons_of_right_ne_stuck
              (Term.UOp UserOp.bvxor) x xs z hz,
          hTail, mk_apply_right_stuck_local] at hConcatTy
        cases hConcatTy
      rw [list_concat_rec_cons_of_right_ne_stuck
            (Term.UOp UserOp.bvxor) x xs z hz,
        mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hTailNe] at hConcatTy
      have hXTypeof :=
        (typeof_bvxor_args_of_result_bitvec x
          (__eo_list_concat_rec xs z) (Term.Numeral W) hConcatTy).1
      have hNonNone :
          term_has_non_none_type
            (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt xs)) := by
        have hsimpa := hATrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
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

theorem inferred_argument_types
    (xs zs n w : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧
      native_zleq 0 W = true ∧
      __smtx_typeof (__eo_to_smt zs) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      (__smtx_typeof (__eo_to_smt xs) =
          SmtType.BitVec (native_int_to_nat W) ∨
        ∀ tail, __eo_list_concat_rec xs tail = tail) := by
  intro hXsTrans hZsTrans hNTrans hWTrans hResultTy
  have hLists := context xs zs n w hResultTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs zs n w)) (__eo_typeof (rhs xs zs))
    (by have hsimpa := hResultTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
  have hTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof (lhs xs zs n w)) (__eo_typeof (rhs xs zs))
    (by have hsimpa := hResultTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
  have hBaseTy : ∃ width,
      __eo_typeof (base xs zs) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    have hRhsNe := hSides.2
    change __eo_typeof_bvnot (__eo_typeof (base xs zs)) ≠ Term.Stuck at hRhsNe
    cases hb : __eo_typeof (base xs zs) <;>
      simp [__eo_typeof_bvnot, hb] at hRhsNe ⊢
    case Apply f width =>
      cases f <;> simp [__eo_typeof_bvnot, hb] at hRhsNe ⊢
      case UOp op => cases op <;> simp [__eo_typeof_bvnot, hb] at hRhsNe ⊢
  rcases hBaseTy with ⟨width, hBaseTy⟩
  have hRhsTy : __eo_typeof (rhs xs zs) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
    change __eo_typeof_bvnot (__eo_typeof (base xs zs)) = _
    rw [hBaseTy]
    simp [__eo_typeof_bvnot]
  have hLhsTy : __eo_typeof (lhs xs zs n w) =
      Term.Apply (Term.UOp UserOp.BitVec) width := hTypesEq.trans hRhsTy
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor) (insertedTail zs n w) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs (by decide) hLists.2
  have hLhsRecTy :
      __eo_typeof (__eo_list_concat_rec xs (insertedTail zs n w)) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    simpa [lhs, __eo_list_concat, hLists.1, hInsertedList,
      __eo_requires, native_ite, native_teq, native_not] using hLhsTy
  have hInsertedTy := list_concat_rec_right_type xs
    (insertedTail zs n w) width hLists.1 hLhsRecTy
  have hParts := typeof_bvxor_args_of_result_bitvec
    (bvAllOnesConst n w) zs width (by simpa [insertedTail] using hInsertedTy)
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hWNe := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_all_ones_const_context n w width hNNe hWNe hParts.1 with
    ⟨W, hW, hWidth, hW0, hNTy⟩
  subst w
  subst width
  have hZsSmt := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    zs (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
      (__eo_to_smt zs) rfl hZsTrans (by simpa using hParts.2)
  have hNSmt := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNTy
  have hXsTypeOrNil := list_smt_type_or_nil_of_concat_type
    xs (insertedTail zs n (Term.Numeral W)) W hXsTrans hLists.1
      (by
        intro hInserted
        rw [hInserted] at hInsertedTy
        cases hInsertedTy)
      (by simpa using hLhsRecTy) hW0
  exact ⟨W, rfl, hW0,
    by simpa [__eo_to_smt_type, hW0, native_ite] using hZsSmt,
    by simpa using hNSmt, hXsTypeOrNil⟩

private theorem common_types
    (xs zs n w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    let width := native_int_to_nat W
    __smtx_typeof (__eo_to_smt (bvAllOnesConst n w)) =
        SmtType.BitVec width ∧
      __smtx_typeof (__eo_to_smt (insertedTail zs n w)) =
        SmtType.BitVec width ∧
      __smtx_typeof
          (__eo_to_smt (__eo_list_concat_rec xs (insertedTail zs n w))) =
        SmtType.BitVec width ∧
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs zs)) =
        SmtType.BitVec width ∧
      __smtx_typeof (__eo_to_smt (base xs zs)) =
        SmtType.BitVec width := by
  intro hXsTy hZsTy hNTy hW hW0 hXsList hZsList
  subst w
  let width := native_int_to_nat W
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt
            (bvAllOnesConst n (Term.Numeral W))) =
        SmtType.BitVec width := by
    simpa [bvAllOnesConst, width] using
      smt_typeof_bv_const_of_int_type n W hNTy hW0
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor)
          (insertedTail zs n (Term.Numeral W)) =
        Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor)
      (bvAllOnesConst n (Term.Numeral W)) zs
      (by decide) hZsList
  have hInsertedTy :
      __smtx_typeof
          (__eo_to_smt
            (insertedTail zs n (Term.Numeral W))) =
        SmtType.BitVec width := by
    change __smtx_typeof
        (SmtTerm.bvxor
          (__eo_to_smt
            (bvAllOnesConst n (Term.Numeral W)))
          (__eo_to_smt zs)) = _
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hConstTy, hZsTy, width,
      native_nateq, native_ite]
  have hLhsRecTy := BvNaryXorSupport.listConcatRecSmtType
    xs (insertedTail zs n (Term.Numeral W)) width
    hXsList hInsertedList (by simpa [width] using hXsTy) hInsertedTy
  have hBaseRecTy := BvNaryXorSupport.listConcatRecSmtType
    xs zs width hXsList hZsList
    (by simpa [width] using hXsTy) (by simpa [width] using hZsTy)
  have hBaseList :
      __eo_is_list (Term.UOp UserOp.bvxor)
          (__eo_list_concat_rec xs zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.bvxor) xs zs hXsList hZsList
  have hBaseTy := BvNaryXorSupport.listSingletonElimSmtType
    (__eo_list_concat_rec xs zs) width hBaseList hBaseRecTy
  have hBaseEq := list_concat_eq_rec_of_lists xs zs hXsList hZsList
  exact ⟨hConstTy, hInsertedTy, hLhsRecTy, hBaseRecTy, by
    simpa [base, baseList, hBaseEq] using hBaseTy⟩

theorem typed_term
    (xs zs n w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term xs zs n w) := by
  intro hXsTy hZsTy hNTy hW hW0 hResultTy
  have hLists := context xs zs n w hResultTy
  have hTypes := common_types xs zs n w W hXsTy hZsTy
    hNTy hW hW0 hLists.1 hLists.2
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor) (insertedTail zs n w) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs
      (by decide) hLists.2
  have hLhsEq := list_concat_eq_rec_of_lists xs (insertedTail zs n w)
    hLists.1 hInsertedList
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs xs zs n w)) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [lhs, hLhsEq] using hTypes.2.2.1
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs xs zs)) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt (base xs zs))) = _
    rw [smtx_typeof_bvnot_term_eq]
    simp [__smtx_typeof_bv_op_1, hTypes.2.2.2.2, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhs xs zs n w) (rhs xs zs)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

theorem typed_term_of_type_or_nil
    (xs zs n w : Term) (W : native_Int) :
    (__smtx_typeof (__eo_to_smt xs) =
        SmtType.BitVec (native_int_to_nat W) ∨
      ∀ tail, __eo_list_concat_rec xs tail = tail) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term xs zs n w) := by
  intro hXsTypeOrNil hZsTy hNTy hW hW0 hResultTy
  rcases hXsTypeOrNil with hXsTy | hXsEmpty
  · exact typed_term xs zs n w W hXsTy hZsTy hNTy hW hW0 hResultTy
  · subst w
    let width := native_int_to_nat W
    have hLists := context xs zs n (Term.Numeral W) hResultTy
    have hConstTy :
        __smtx_typeof
            (__eo_to_smt (bvAllOnesConst n (Term.Numeral W))) =
          SmtType.BitVec width := by
      simpa [bvAllOnesConst, width] using
        smt_typeof_bv_const_of_int_type n W hNTy hW0
    have hInsertedTy :
        __smtx_typeof
            (__eo_to_smt (insertedTail zs n (Term.Numeral W))) =
          SmtType.BitVec width := by
      change __smtx_typeof
          (SmtTerm.bvxor
            (__eo_to_smt (bvAllOnesConst n (Term.Numeral W)))
            (__eo_to_smt zs)) = _
      rw [smtx_typeof_bvxor_term_eq]
      simp [__smtx_typeof_bv_op_2, hConstTy, hZsTy, width,
        native_nateq, native_ite]
    have hInsertedList :
        __eo_is_list (Term.UOp UserOp.bvxor)
            (insertedTail zs n (Term.Numeral W)) =
          Term.Boolean true :=
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.bvxor)
        (bvAllOnesConst n (Term.Numeral W)) zs
        (by decide) hLists.2
    have hLhsGuardEq := list_concat_eq_rec_of_lists xs
      (insertedTail zs n (Term.Numeral W)) hLists.1 hInsertedList
    have hLhsRecEq := hXsEmpty
      (insertedTail zs n (Term.Numeral W))
    have hLhsTy :
        __smtx_typeof
            (__eo_to_smt (lhs xs zs n (Term.Numeral W))) =
          SmtType.BitVec width := by
      rw [show lhs xs zs n (Term.Numeral W) =
          __eo_list_concat_rec xs
            (insertedTail zs n (Term.Numeral W)) by
        simpa [lhs] using hLhsGuardEq]
      rw [hLhsRecEq]
      exact hInsertedTy
    have hBaseGuardEq := list_concat_eq_rec_of_lists xs zs
      hLists.1 hLists.2
    have hBaseRecEq := hXsEmpty zs
    have hBaseEq :
        base xs zs =
          __eo_list_singleton_elim (Term.UOp UserOp.bvxor) zs := by
      unfold base baseList
      rw [hBaseGuardEq, hBaseRecEq]
    have hBaseTy :
        __smtx_typeof (__eo_to_smt (base xs zs)) =
          SmtType.BitVec width := by
      rw [hBaseEq]
      exact BvNaryXorSupport.listSingletonElimSmtType zs width
        hLists.2 (by simpa [width] using hZsTy)
    have hRhsTy :
        __smtx_typeof (__eo_to_smt (rhs xs zs)) =
          SmtType.BitVec width := by
      change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt (base xs zs))) = _
      rw [smtx_typeof_bvnot_term_eq]
      simp [__smtx_typeof_bv_op_1, hBaseTy, native_ite]
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs zs n (Term.Numeral W)) (rhs xs zs)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

theorem facts_term
    (M : SmtModel) (hM : model_wf M)
    (xs zs n w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    eo_interprets M (bvAllOnesValuePrem n w) true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    eo_interprets M (term xs zs n w) true := by
  intro hXsTy hZsTy hNTy hW hW0 hPrem hResultTy
  have hBool := typed_term xs zs n w W hXsTy hZsTy
    hNTy hW hW0 hResultTy
  have hLists := context xs zs n w hResultTy
  have hTypes := common_types xs zs n w W hXsTy hZsTy
    hNTy hW hW0 hLists.1 hLists.2
  let width := native_int_to_nat W
  have hWidthEq : native_nat_to_int width = W := by
    exact native_width_roundtrip W hW0
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor) (insertedTail zs n w) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs
      (by decide) hLists.2
  have hLhsEq := list_concat_eq_rec_of_lists xs (insertedTail zs n w)
    hLists.1 hInsertedList
  have hBaseEq := list_concat_eq_rec_of_lists xs zs hLists.1 hLists.2
  have hBaseRecList :
      __eo_is_list (Term.UOp UserOp.bvxor)
          (__eo_list_concat_rec xs zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.bvxor) xs zs hLists.1 hLists.2
  have hLhsConcatEval := BvNaryXorSupport.listConcatRecEvalEq
    M hM xs (insertedTail zs n w) width hLists.1 hInsertedList
    (by simpa [width] using hXsTy) (by simpa [width] using hTypes.2.1)
  have hBaseConcatEval := BvNaryXorSupport.listConcatRecEvalEq
    M hM xs zs width hLists.1 hLists.2
    (by simpa [width] using hXsTy) (by simpa [width] using hZsTy)
  have hSingletonEval := BvNaryXorSupport.listSingletonElimEvalEq
    M hM (__eo_list_concat_rec xs zs) width hBaseRecList
    (by simpa [width] using hTypes.2.2.2.1)
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) width
      (by simpa [width] using hXsTy) with
    ⟨px, hXsEval, hXsCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) width
      (by simpa [width] using hZsTy) with
    ⟨pz, hZsEval, hZsCan⟩
  have hMaxEval := eval_bv_all_ones_const_of_prem M hM n w W
    hNTy hW hW0 hPrem
  have hMaxEvalNat :
      __smtx_model_eval M (__eo_to_smt (bvAllOnesConst n w)) =
        SmtValue.Binary (native_nat_to_int width)
          (native_int_pow2 (native_nat_to_int width) - 1) := by
    simpa [hWidthEq] using hMaxEval
  have hInsertedEval :
      __smtx_model_eval M (__eo_to_smt (insertedTail zs n w)) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int width) pz) := by
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt (bvAllOnesConst n w))
          (__eo_to_smt zs)) = _
    rw [smtx_eval_bvxor_term_eq, hMaxEvalNat, hZsEval]
    exact bvxor_all_ones_eval_eq_bvnot width pz hZsCan
  have hBaseConcatEval' :
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec xs zs)) =
        __smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int width) px)
          (SmtValue.Binary (native_nat_to_int width) pz) := by
    rw [hBaseConcatEval]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt xs) (__eo_to_smt zs)) = _
    rw [smtx_eval_bvxor_term_eq, hXsEval, hZsEval]
  have hRhsEq :
      rhs xs zs =
        Term.Apply (Term.UOp UserOp.bvnot)
          (__eo_list_singleton_elim (Term.UOp UserOp.bvxor)
            (__eo_list_concat_rec xs zs)) := by
    unfold rhs base baseList
    rw [hBaseEq]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs xs zs n w)) =
        __smtx_model_eval M (__eo_to_smt (rhs xs zs)) := by
    rw [show __eo_to_smt (lhs xs zs n w) =
        __eo_to_smt (__eo_list_concat_rec xs (insertedTail zs n w)) by
      rw [← hLhsEq]
      rfl]
    rw [hRhsEq]
    rw [hLhsConcatEval]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt xs)
          (__eo_to_smt (insertedTail zs n w))) = _
    rw [smtx_eval_bvxor_term_eq, hXsEval, hInsertedEval]
    rw [bvxor_bvnot_right_eval_eq_bvnot_bvxor width px pz
      hXsCan hZsCan]
    rw [← hBaseConcatEval']
    rw [← hSingletonEval]
    rw [← smtx_eval_bvnot_term_eq]
    change __smtx_model_eval M
        (SmtTerm.bvnot
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.bvxor)
              (__eo_list_concat_rec xs zs)))) =
      __smtx_model_eval M
        (SmtTerm.bvnot
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.bvxor)
              (__eo_list_concat_rec xs zs))))
    rfl
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (lhs xs zs n w)))
      (__smtx_model_eval M (__eo_to_smt (rhs xs zs)))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_term_of_type_or_nil
    (M : SmtModel) (hM : model_wf M)
    (xs zs n w : Term) (W : native_Int) :
    (__smtx_typeof (__eo_to_smt xs) =
        SmtType.BitVec (native_int_to_nat W) ∨
      ∀ tail, __eo_list_concat_rec xs tail = tail) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    eo_interprets M (bvAllOnesValuePrem n w) true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    eo_interprets M (term xs zs n w) true := by
  intro hXsTypeOrNil hZsTy hNTy hW hW0 hPrem hResultTy
  rcases hXsTypeOrNil with hXsTy | hXsEmpty
  · exact facts_term M hM xs zs n w W hXsTy hZsTy hNTy
      hW hW0 hPrem hResultTy
  · have hBool := typed_term_of_type_or_nil xs zs n w W
      (Or.inr hXsEmpty) hZsTy hNTy hW hW0 hResultTy
    subst w
    let width := native_int_to_nat W
    have hWidthEq : native_nat_to_int width = W :=
      native_width_roundtrip W hW0
    have hLists := context xs zs n (Term.Numeral W) hResultTy
    have hInsertedList :
        __eo_is_list (Term.UOp UserOp.bvxor)
            (insertedTail zs n (Term.Numeral W)) =
          Term.Boolean true :=
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.bvxor)
        (bvAllOnesConst n (Term.Numeral W)) zs
        (by decide) hLists.2
    have hLhsGuardEq := list_concat_eq_rec_of_lists xs
      (insertedTail zs n (Term.Numeral W)) hLists.1 hInsertedList
    have hLhsEq :
        lhs xs zs n (Term.Numeral W) =
          insertedTail zs n (Term.Numeral W) := by
      unfold lhs
      rw [hLhsGuardEq, hXsEmpty]
    have hBaseGuardEq := list_concat_eq_rec_of_lists xs zs
      hLists.1 hLists.2
    have hBaseEq :
        base xs zs =
          __eo_list_singleton_elim (Term.UOp UserOp.bvxor) zs := by
      unfold base baseList
      rw [hBaseGuardEq, hXsEmpty]
    have hRhsEq :
        rhs xs zs =
          Term.Apply (Term.UOp UserOp.bvnot)
            (__eo_list_singleton_elim (Term.UOp UserOp.bvxor) zs) := by
      unfold rhs
      rw [hBaseEq]
    have hSingletonEval := BvNaryXorSupport.listSingletonElimEvalEq
      M hM zs width hLists.2 (by simpa [width] using hZsTy)
    rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) width
        (by simpa [width] using hZsTy) with
      ⟨pz, hZsEval, hZsCan⟩
    have hMaxEval := eval_bv_all_ones_const_of_prem M hM n
      (Term.Numeral W) W hNTy rfl hW0 hPrem
    have hMaxEvalNat :
        __smtx_model_eval M
            (__eo_to_smt (bvAllOnesConst n (Term.Numeral W))) =
          SmtValue.Binary (native_nat_to_int width)
            (native_int_pow2 (native_nat_to_int width) - 1) := by
      simpa [hWidthEq] using hMaxEval
    have hEvalEq :
        __smtx_model_eval M
            (__eo_to_smt (lhs xs zs n (Term.Numeral W))) =
          __smtx_model_eval M (__eo_to_smt (rhs xs zs)) := by
      rw [hLhsEq, hRhsEq]
      change __smtx_model_eval M
          (SmtTerm.bvxor
            (__eo_to_smt (bvAllOnesConst n (Term.Numeral W)))
            (__eo_to_smt zs)) =
        __smtx_model_eval M
          (SmtTerm.bvnot
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.bvxor) zs)))
      rw [smtx_eval_bvxor_term_eq, hMaxEvalNat, hZsEval]
      rw [bvxor_all_ones_eval_eq_bvnot width pz hZsCan]
      rw [smtx_eval_bvnot_term_eq, hSingletonEval, hZsEval]
    apply RuleProofs.eo_interprets_eq_of_rel M
    · exact hBool
    · change RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (lhs xs zs n (Term.Numeral W))))
        (__smtx_model_eval M (__eo_to_smt (rhs xs zs)))
      rw [hEvalEq]
      exact RuleProofs.smt_value_rel_refl _

end BvXorOnesSupport
