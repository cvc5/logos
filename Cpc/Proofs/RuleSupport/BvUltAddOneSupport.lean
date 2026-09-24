module

public import Cpc.Proofs.RuleSupport.BvNaryAddSupport
import all Cpc.Proofs.RuleSupport.BvNaryAddSupport

public section

/-! Support for the `bv_ult_add_one` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvUltAddOneSupport

open BvNaryAddSupport

def bvConst (w : Term) (n : native_Int) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral n)

def baseList (ys zs : Term) : Term :=
  __eo_list_concat_rec ys zs

def base (ys zs : Term) : Term :=
  __eo_list_singleton_elim op (baseList ys zs)

def incList (ys zs c : Term) : Term :=
  __eo_list_concat_rec ys (add c zs)

def lhs (x ys zs c : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x) (incList ys zs c)

def maxValue (w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) (bvConst w 0)

def rhs (x ys zs w : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (base ys zs))
          (maxValue w))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) (base ys zs)) x)))
      (Term.Boolean true))

def term (x ys zs c w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs x ys zs c))
    (rhs x ys zs w)

def constPrem (c w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) c) (bvConst w 1)

def widthPrem (w x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)

private def guardedBaseList (ys zs : Term) : Term :=
  __eo_list_concat op ys zs

private def guardedBase (ys zs : Term) : Term :=
  __eo_list_singleton_elim op (guardedBaseList ys zs)

private def guardedIncList (ys zs c : Term) : Term :=
  __eo_list_concat op ys (add c zs)

private def guardedLhs (x ys zs c : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvult) x)
    (guardedIncList ys zs c)

private def guardedRhs (x ys zs w : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and)
      (__eo_mk_apply (Term.UOp UserOp.not)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.eq) (guardedBase ys zs))
          (maxValue w))))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.UOp UserOp.not)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.bvult) (guardedBase ys zs)) x)))
      (Term.Boolean true))

private def skeleton (x ys zs c w : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq) (guardedLhs x ys zs c))
    (guardedRhs x ys zs w)

def program (x ys zs c w P1 P2 : Term) : Term :=
  __eo_prog_bv_ult_add_one x ys zs c w (Proof.pf P1) (Proof.pf P2)

private theorem listConcatPartsOfNeStuck (f a b : Term) :
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

private theorem listConcatReduce (f a b : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f b = Term.Boolean true ->
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  intro hA hB
  simp [__eo_list_concat, hA, hB, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem premiseShape (x ys zs c w P1 P2 : Term) :
    x ≠ Term.Stuck -> ys ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    c ≠ Term.Stuck -> w ≠ Term.Stuck ->
    program x ys zs c w P1 P2 ≠ Term.Stuck ->
    ∃ cRef wRef1 wRef2 xRef,
      P1 = constPrem cRef wRef1 ∧
      P2 = widthPrem wRef2 xRef := by
  intro hX hYs hZs hC hW hProg
  by_cases hShape :
      ∃ cRef wRef1 wRef2 xRef,
        P1 = constPrem cRef wRef1 ∧
        P2 = widthPrem wRef2 xRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_ult_add_one.eq_7 x ys zs c w
      (Proof.pf P1) (Proof.pf P2) hX hYs hZs hC hW (by
        intro cRef wRef1 wRef2 xRef hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨cRef, wRef1, wRef2, xRef, rfl, rfl⟩)

private theorem programCanonical (x ys zs c w : Term) :
    x ≠ Term.Stuck -> ys ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    c ≠ Term.Stuck -> w ≠ Term.Stuck ->
    program x ys zs c w (constPrem c w) (widthPrem w x) =
      skeleton x ys zs c w := by
  intro hX hYs hZs hC hW
  unfold program constPrem widthPrem bvConst
  rw [__eo_prog_bv_ult_add_one.eq_6 x ys zs c w c w w x
    hX hYs hZs hC hW]
  simp [skeleton, guardedLhs, guardedIncList, guardedRhs, guardedBase,
    guardedBaseList, maxValue, bvConst, add, op, __eo_requires,
    __eo_and, __eo_eq, native_ite, native_teq, native_not, native_and,
    hX, hYs, hZs, hC, hW]

private theorem programNormalize (x ys zs c w P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    program x ys zs c w P1 P2 ≠ Term.Stuck ->
    P1 = constPrem c w ∧ P2 = widthPrem w x ∧
      program x ys zs c w P1 P2 = skeleton x ys zs c w := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZs := RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hW := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases premiseShape x ys zs c w P1 P2 hX hYs hZs hC hW hProg with
    ⟨cRef, wRef1, wRef2, xRef, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold program constPrem widthPrem bvConst at hReq
  rw [__eo_prog_bv_ult_add_one.eq_6 x ys zs c w
    cRef wRef1 wRef2 xRef hX hYs hZs hC hW] at hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hFirst3, hXRef⟩
  rcases bv_extract_support_and_true hFirst3 with ⟨hFirst2, hWRef2⟩
  rcases bv_extract_support_and_true hFirst2 with ⟨hCRef, hWRef1⟩
  have hCRefEq := bv_extract_support_eq_true hCRef
  have hWRef1Eq := bv_extract_support_eq_true hWRef1
  have hWRef2Eq := bv_extract_support_eq_true hWRef2
  have hXRefEq := bv_extract_support_eq_true hXRef
  subst cRef
  subst wRef1
  subst wRef2
  subst xRef
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact programCanonical x ys zs c w hX hYs hZs hC hW

private theorem termNeStuckOfTypeofBool {t : Term} :
    __eo_typeof t = Term.Bool -> t ≠ Term.Stuck := by
  intro h hStuck
  subst t
  cases h

private theorem guardedListsAndReductions
    (x ys zs c : Term) :
    guardedLhs x ys zs c ≠ Term.Stuck ->
    __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true ∧
      guardedIncList ys zs c = incList ys zs c ∧
      guardedBaseList ys zs = baseList ys zs := by
  intro hLhs
  have hIncNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hLhs
  have hParts := listConcatPartsOfNeStuck op ys (add c zs)
    (by simpa [guardedIncList] using hIncNe)
  have hZsList := eo_is_list_tail_true_of_cons_self op c zs hParts.2
  have hIncEq := listConcatReduce op ys (add c zs) hParts.1 hParts.2
  have hBaseEq := listConcatReduce op ys zs hParts.1 hZsList
  exact ⟨hParts.1, hZsList,
    by simpa [guardedIncList, incList] using hIncEq,
    by simpa [guardedBaseList, baseList] using hBaseEq⟩

theorem programEqTermOfTypeBool (x ys zs c w P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (program x ys zs c w P1 P2) = Term.Bool ->
    P1 = constPrem c w ∧ P2 = widthPrem w x ∧
      program x ys zs c w P1 P2 = term x ys zs c w := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hTy
  have hProgNe := termNeStuckOfTypeofBool hTy
  rcases programNormalize x ys zs c w P1 P2 hXTrans hYsTrans hZsTrans
      hCTrans hWTrans hProgNe with ⟨hP1, hP2, hSkeleton⟩
  have hSkeletonTy : __eo_typeof (skeleton x ys zs c w) = Term.Bool := by
    rw [← hSkeleton]
    exact hTy
  have hSkeletonNe := termNeStuckOfTypeofBool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  rcases guardedListsAndReductions x ys zs c hLhsNe with
    ⟨hYsList, hZsList, hIncEq, hBaseListEq⟩
  have hBaseEq : guardedBase ys zs = base ys zs := by
    unfold guardedBase base
    rw [hBaseListEq]
  have hLhsEq : guardedLhs x ys zs c = lhs x ys zs c := by
    unfold guardedLhs lhs
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsNe, hIncEq]
  have hOuterAndFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
  have hNotEqNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOuterAndFunNe
  have hInnerAndNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhsNe
  have hNotEqArgNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNotEqNe
  have hEqBaseFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hNotEqArgNe
  have hInnerAndFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hInnerAndNe
  have hNotUltNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerAndFunNe
  have hUltNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNotUltNe
  have hUltFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hUltNe
  refine ⟨hP1, hP2, ?_⟩
  calc
    program x ys zs c w P1 P2 = skeleton x ys zs c w := hSkeleton
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (guardedLhs x ys zs c)) (guardedRhs x ys zs w) := by
      unfold skeleton
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
    _ = term x ys zs c w := by
      unfold guardedRhs
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hOuterAndFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hNotEqNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hNotEqArgNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqBaseFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerAndNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerAndFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hNotUltNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hUltNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hUltFunNe]
      simp only [term, rhs]
      rw [hLhsEq, hBaseEq]

private theorem typeofAndBoolArgs {a b : Term} :
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) = Term.Bool ->
    __eo_typeof a = Term.Bool ∧ __eo_typeof b = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_or_bool_args (__eo_typeof a) (__eo_typeof b)
    (by have hsimpa := h; (try simp at hsimpa ⊢); exact hsimpa)

private theorem typeofNotArgBool {a : Term} :
    __eo_typeof (Term.Apply (Term.UOp UserOp.not) a) = Term.Bool ->
    __eo_typeof a = Term.Bool := by
  intro h
  change __eo_typeof_not (__eo_typeof a) = Term.Bool at h
  cases ha : __eo_typeof a <;>
    simp [__eo_typeof_not, ha] at h ⊢

private theorem typeofBvnotArgOfResultBitvec
    (t width : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) t) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hTy
  change __eo_typeof_bvnot (__eo_typeof t) = _ at hTy
  cases ht : __eo_typeof t <;>
    simp [__eo_typeof_bvnot, ht] at hTy ⊢
  case Apply f arg =>
    cases f <;> simp [__eo_typeof_bvnot, ht] at hTy ⊢
    case UOp u =>
      cases u <;> simp [__eo_typeof_bvnot, ht] at hTy ⊢
      cases hTy
      rfl

private theorem smtBitvecTypeOfEoType
    (t : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt t) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hTrans hTy hW0
  have hExpected :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt t) rfl hTrans hTy
  simpa [__eo_to_smt_type, hW0, native_ite] using hExpected

theorem inferredArgumentTypes (x ys zs c w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    __eo_typeof (term x ys zs c w) = Term.Bool ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ native_zleq 0 W = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt c) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt zs) =
        SmtType.BitVec (native_int_to_nat W) ∧
      ListTypeOrNil ys (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (base ys zs)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (incList ys zs c)) =
        SmtType.BitVec (native_int_to_nat W) := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hYsList hZsList hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs x ys zs c)) (__eo_typeof (rhs x ys zs w))
    (by have hsimpa := hTermTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
  rcases typeof_bvult_args_of_ne_stuck (by
      have hsimpa := hSides.1; (try simp [lhs] at hsimpa ⊢); exact hsimpa) with ⟨width, hXTy, hIncTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x width
      hXTrans hXTy with ⟨W, hWidth, hW0, hXSTy⟩
  subst width
  have hIncTyNe : __eo_typeof (incList ys zs c) ≠ Term.Stuck := by
    rw [hIncTy]
    intro h
    cases h
  have hTailTyNe : __eo_typeof (add c zs) ≠ Term.Stuck :=
    listConcatRecRightTypeNeStuck ys (add c zs) hYsList hIncTyNe
  rcases BvXorOnesSupport.typeof_bvand_arg_types_of_ne_stuck
      (by have hsimpa := hTailTyNe; (try simp [add, op] at hsimpa ⊢); exact hsimpa) with
    ⟨tailWidth, hCTy, hZsTy⟩
  have hTailWidthNe : tailWidth ≠ Term.Stuck := by
    intro h
    apply hTailTyNe
    change __eo_typeof_bvand (__eo_typeof c) (__eo_typeof zs) = Term.Stuck
    rw [hCTy, hZsTy, h]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hIncTailTy :
      __eo_typeof (incList ys zs c) =
        Term.Apply (Term.UOp UserOp.BitVec) tailWidth := by
    unfold incList
    exact listConcatRecResultType ys (add c zs) tailWidth hYsList
      (by
        change __eo_typeof_bvand (__eo_typeof c) (__eo_typeof zs) = _
        rw [hCTy, hZsTy]
        simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
          native_teq, native_not, hTailWidthNe]) hIncTyNe
  have hTailWidth : tailWidth = Term.Numeral W := by
    rw [hIncTy] at hIncTailTy
    cases hIncTailTy
    rfl
  subst tailWidth
  have hCSTy := smtBitvecTypeOfEoType c W hCTrans hCTy hW0
  have hZsSTy := smtBitvecTypeOfEoType zs W hZsTrans hZsTy hW0
  have hTailNe : add c zs ≠ Term.Stuck := by
    have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
    have hZsNe := RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
    simp [add, op, hCNe, hZsNe]
  have hYsType := listSmtTypeOrNilOfConcatType ys (add c zs) W hYsTrans
    hYsList hTailNe (by simpa [incList] using hIncTy) hW0
  have hBaseListTy :
      __eo_typeof (baseList ys zs) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    unfold baseList
    exact listConcatRecReplaceTailType ys (add c zs) zs
      (Term.Numeral W) hYsList (by simpa [incList] using hIncTy) hZsTy
  have hBaseListList :
      __eo_is_list op (baseList ys zs) = Term.Boolean true := by
    unfold baseList
    exact eo_list_concat_rec_is_list_true_of_lists op ys zs hYsList hZsList
  have hBaseTy :
      __eo_typeof (base ys zs) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) :=
    listSingletonElimEoType (baseList ys zs) (Term.Numeral W)
      hBaseListList hBaseListTy
  have hLhsTy : __eo_typeof (lhs x ys zs c) = Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof x)
      (__eo_typeof (incList ys zs c)) = Term.Bool
    rw [hXTy, hIncTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof (lhs x ys zs c)) (__eo_typeof (rhs x ys zs w))
    (by have hsimpa := hTermTy; (try simp [term] at hsimpa ⊢); exact hsimpa)
  rw [hLhsTy] at hTypeEq
  have hRhsTy : __eo_typeof (rhs x ys zs w) = Term.Bool := hTypeEq.symm
  have hRhsParts := typeofAndBoolArgs (by simpa [rhs] using hRhsTy)
  have hEqBaseMaxTy := typeofNotArgBool hRhsParts.1
  have hBaseMaxTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof (base ys zs)) (__eo_typeof (maxValue w))
    (by have hsimpa := hEqBaseMaxTy; (try simp at hsimpa ⊢); exact hsimpa)
  have hMaxTy :
      __eo_typeof (maxValue w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hBaseTy] at hBaseMaxTypeEq
    exact hBaseMaxTypeEq.symm
  have hZeroTy :
      __eo_typeof (bvConst w 0) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) :=
    typeofBvnotArgOfResultBitvec (bvConst w 0) (Term.Numeral W)
      (by simpa [maxValue] using hMaxTy)
  have hZeroTrans :
      RuleProofs.eo_has_smt_translation (Term.Numeral 0) := by
    intro h
    change SmtType.Int = SmtType.None at h
    cases h
  have hZeroNe := RuleProofs.term_ne_stuck_of_has_smt_translation
    (Term.Numeral 0) hZeroTrans
  have hWNe := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) w (Term.Numeral W)
      hZeroNe hWNe (by simpa [bvConst, bvAllOnesConst] using hZeroTy) with
    ⟨W', hWEq, hWidthEq, hW'0, _hZeroEoTy⟩
  have hW' : W' = W := by
    injection hWidthEq with h
    exact h.symm
  subst W'
  have hTailSTy := addSmtType c zs (native_int_to_nat W) hCSTy hZsSTy
  have hIncSTy :
      __smtx_typeof (__eo_to_smt (incList ys zs c)) =
        SmtType.BitVec (native_int_to_nat W) := by
    rcases hYsType with hYsSTy | hYsNil
    · unfold incList
      exact listConcatRecSmtType ys (add c zs) (native_int_to_nat W)
        hYsList
        (eo_is_list_cons_self_true_of_tail_list op c zs (by decide) hZsList)
        hYsSTy hTailSTy
    · unfold incList
      rw [hYsNil]
      exact hTailSTy
  have hBaseListSTy :
      __smtx_typeof (__eo_to_smt (baseList ys zs)) =
        SmtType.BitVec (native_int_to_nat W) := by
    rcases hYsType with hYsSTy | hYsNil
    · unfold baseList
      exact listConcatRecSmtType ys zs (native_int_to_nat W)
        hYsList hZsList hYsSTy hZsSTy
    · unfold baseList
      rw [hYsNil]
      exact hZsSTy
  have hBaseSTy := listSingletonElimSmtType (baseList ys zs)
    (native_int_to_nat W) hBaseListList hBaseListSTy
  exact ⟨W, hWEq, hW0, hXSTy, hCSTy, hZsSTy, hYsType,
    by simpa [base] using hBaseSTy, hIncSTy⟩

private theorem smtTypeofBvnot
    (a : SmtTerm) (W : Nat) :
    __smtx_typeof a = SmtType.BitVec W ->
    __smtx_typeof (SmtTerm.bvnot a) = SmtType.BitVec W := by
  intro h
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, h]

private theorem hasBoolTypeBvult
    (a b : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec W ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [__smtx_typeof.eq_56]
  simp [__smtx_typeof_bv_op_2_ret, hA, hB, native_nateq, native_ite]

theorem typedTerm (x ys zs c w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    __eo_typeof (term x ys zs c w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term x ys zs c w) := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hYsList hZsList hTy
  rcases inferredArgumentTypes x ys zs c w hXTrans hYsTrans hZsTrans
      hCTrans hWTrans hYsList hZsList hTy with
    ⟨W, rfl, hW0, hXSTy, _hCSTy, _hZsSTy, _hYsType,
      hBaseSTy, hIncSTy⟩
  let width := native_int_to_nat W
  have hZeroSTy :
      __smtx_typeof (__eo_to_smt (bvConst (Term.Numeral W) 0)) =
        SmtType.BitVec width := by
    have h := smt_typeof_bv_const_of_int_type (Term.Numeral 0) W rfl hW0
    simpa [bvConst, width] using h
  have hMaxSTy :
      __smtx_typeof (__eo_to_smt (maxValue (Term.Numeral W))) =
        SmtType.BitVec width := by
    change __smtx_typeof
      (SmtTerm.bvnot (__eo_to_smt (bvConst (Term.Numeral W) 0))) = _
    exact smtTypeofBvnot _ width hZeroSTy
  have hLhsBool := hasBoolTypeBvult x (incList ys zs c) width
    (by simpa [width] using hXSTy) (by simpa [width] using hIncSTy)
  have hBaseTrans : RuleProofs.eo_has_smt_translation (base ys zs) := by
    intro hNone
    rw [hNone] at hBaseSTy
    cases hBaseSTy
  have hEqBaseMax : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (base ys zs))
        (maxValue (Term.Numeral W))) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by simpa [width] using hBaseSTy.trans hMaxSTy.symm) hBaseTrans
  have hNotEq := RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqBaseMax
  have hBaseUltX := hasBoolTypeBvult (base ys zs) x width
    (by simpa [width] using hBaseSTy) (by simpa [width] using hXSTy)
  have hNotUlt := RuleProofs.eo_has_bool_type_not_of_bool_arg _ hBaseUltX
  have hInnerAnd := RuleProofs.eo_has_bool_type_and_of_bool_args _ _
    hNotUlt RuleProofs.eo_has_bool_type_true
  have hRhsBool := RuleProofs.eo_has_bool_type_and_of_bool_args _ _
    hNotEq hInnerAnd
  unfold term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by
      simpa [lhs] using
        (show __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
                (incList ys zs c))) ≠ SmtType.None by
          rw [hLhsBool]
          intro h
          cases h))

theorem evalIncEqBaseAdd
    (M : SmtModel) (hM : model_wf M)
    (ys zs c : Term) (W : Nat) :
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    ListTypeOrNil ys W ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt (base ys zs)) = SmtType.BitVec W ->
    __smtx_model_eval M (__eo_to_smt (incList ys zs c)) =
      __smtx_model_eval M (__eo_to_smt (add (base ys zs) c)) := by
  intro hYsList hZsList hYsType hZsTy hCTy hBaseTy
  have hCZSList : __eo_is_list op (add c zs) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op c zs (by decide) hZsList
  have hCZSTy := addSmtType c zs W hCTy hZsTy
  have hBaseListList :
      __eo_is_list op (baseList ys zs) = Term.Boolean true := by
    unfold baseList
    exact eo_list_concat_rec_is_list_true_of_lists op ys zs hYsList hZsList
  have hBaseListTy :
      __smtx_typeof (__eo_to_smt (baseList ys zs)) = SmtType.BitVec W := by
    rcases hYsType with hYsTy | hYsNil
    · unfold baseList
      exact listConcatRecSmtType ys zs W hYsList hZsList hYsTy hZsTy
    · unfold baseList
      rw [hYsNil]
      exact hZsTy
  have hBaseElim := listSingletonElimEvalEq M hM (baseList ys zs) W
    hBaseListList hBaseListTy
  have hBaseElim' :
      __smtx_model_eval M (__eo_to_smt (base ys zs)) =
        __smtx_model_eval M (__eo_to_smt (baseList ys zs)) := by
    simpa [base] using hBaseElim
  rcases hYsType with hYsTy | hYsNil
  · have hIncConcat := listConcatRecEvalEq M hM ys (add c zs) W
      hYsList hCZSList hYsTy hCZSTy
    have hBaseConcat := listConcatRecEvalEq M hM ys zs W
      hYsList hZsList hYsTy hZsTy
    have hBaseConcat' :
        __smtx_model_eval M (__eo_to_smt (baseList ys zs)) =
          __smtx_model_eval M (__eo_to_smt (add ys zs)) := by
      simpa [baseList] using hBaseConcat
    have hSwap := addCommEval M hM c zs W hCTy hZsTy
    have hAssoc := addAssocEval M hM ys zs c W hYsTy hZsTy hCTy
    unfold incList at hIncConcat ⊢
    rw [hIncConcat]
    calc
      __smtx_model_eval M (__eo_to_smt (add ys (add c zs))) =
          __smtx_model_eval M (__eo_to_smt (add ys (add zs c))) := by
        change __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval M (__eo_to_smt (add c zs))) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt ys))
            (__smtx_model_eval M (__eo_to_smt (add zs c)))
        rw [hSwap]
      _ = __smtx_model_eval M (__eo_to_smt (add (add ys zs) c)) :=
        hAssoc.symm
      _ = __smtx_model_eval M
          (__eo_to_smt (add (baseList ys zs) c)) := by
        change __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt (add ys zs)))
            (__smtx_model_eval M (__eo_to_smt c)) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt (baseList ys zs)))
            (__smtx_model_eval M (__eo_to_smt c))
        rw [← hBaseConcat']
      _ = __smtx_model_eval M (__eo_to_smt (add (base ys zs) c)) := by
        change __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt (baseList ys zs)))
            (__smtx_model_eval M (__eo_to_smt c)) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt (base ys zs)))
            (__smtx_model_eval M (__eo_to_smt c))
        rw [hBaseElim']
  · unfold incList
    rw [hYsNil]
    have hSwap := addCommEval M hM c zs W hCTy hZsTy
    calc
      __smtx_model_eval M (__eo_to_smt (add c zs)) =
          __smtx_model_eval M (__eo_to_smt (add zs c)) := hSwap
      _ = __smtx_model_eval M
          (__eo_to_smt (add (baseList ys zs) c)) := by
        unfold baseList
        rw [hYsNil]
      _ = __smtx_model_eval M (__eo_to_smt (add (base ys zs) c)) := by
        change __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt (baseList ys zs)))
            (__smtx_model_eval M (__eo_to_smt c)) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt (base ys zs)))
            (__smtx_model_eval M (__eo_to_smt c))
        rw [hBaseElim']

private theorem nativeIntPow2PosOfNonneg
    (W : native_Int) :
    native_zleq 0 W = true -> 0 < native_int_pow2 W := by
  intro hW0
  have hW : 0 ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have hNot : ¬ W < 0 := Int.not_lt_of_ge hW
  simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hNot]
  exact Int.pow_pos (by decide)

private theorem ultAddOneBoolIdentity
    (m x b : native_Int) :
    0 < m -> 0 ≤ x -> x < m -> 0 ≤ b -> b < m ->
    (decide (x < native_mod_total
      (b + native_mod_total 1 m) m) : Bool) =
      ((decide (b ≠ m - 1) : Bool) && !(decide (b < x) : Bool)) := by
  intro hm hx0 hxm hb0 hbm
  change (0 : Int) < m at hm
  change (0 : Int) ≤ x at hx0
  change x < (m : Int) at hxm
  change (0 : Int) ≤ b at hb0
  change b < (m : Int) at hbm
  by_cases hbMax : b = m - 1
  · have hInc : native_mod_total
        (b + native_mod_total 1 m) m = 0 := by
      subst b
      by_cases hm1 : m = 1
      · subst m
        decide
      · have hm2 : (1 : Int) < m := by
          rcases Int.lt_trichotomy (1 : Int) m with h | h | h
          · exact h
          · exact False.elim (hm1 h.symm)
          · exact False.elim ((Int.not_lt_of_ge
              (Int.add_one_le_iff.mpr hm)) h)
        have hOneMod : native_mod_total 1 m = 1 := by
          unfold native_mod_total
          exact Int.emod_eq_of_lt (by decide) hm2
        rw [hOneMod]
        have hSum : m - 1 + 1 = m := Int.sub_add_cancel m 1
        rw [hSum]
        simp [native_mod_total]
    have hNotLt : ¬ x < 0 := Int.not_lt_of_ge hx0
    rw [hInc]
    simp [hbMax, hNotLt]
  · have hbLe : b ≤ m - 1 := Int.le_sub_one_of_lt hbm
    have hbLt : b < m - 1 := by
      rcases Int.lt_trichotomy b (m - 1) with h | h | h
      · exact h
      · exact False.elim (hbMax h)
      · exact False.elim ((Int.not_lt_of_ge hbLe) h)
    change (b : Int) < m - 1 at hbLt
    have hZeroLt : (0 : Int) < m - 1 := Int.lt_of_le_of_lt hb0 hbLt
    have hm2 : (1 : Int) < m := by
      have h := Int.add_lt_add_right hZeroLt 1
      simpa [Int.sub_add_cancel] using h
    have hOneMod : native_mod_total 1 m = 1 := by
      unfold native_mod_total
      exact Int.emod_eq_of_lt (by decide) hm2
    have hInc : native_mod_total
        (b + native_mod_total 1 m) m = b + 1 := by
      rw [hOneMod]
      unfold native_mod_total
      have hUpper : b + 1 < m := by
        have h := Int.add_lt_add_right hbLt 1
        simpa [Int.sub_add_cancel] using h
      exact Int.emod_eq_of_lt (Int.add_nonneg hb0 (by decide)) hUpper
    rw [hInc]
    by_cases hBx : b < x
    · have hNot : ¬ x < b + 1 :=
        Int.not_lt_of_ge (Int.add_one_le_iff.mpr hBx)
      simp [hbMax, hBx, hNot]
    · have hLt : x < b + 1 :=
        Int.lt_add_one_iff.mpr (Int.le_of_not_gt hBx)
      simp [hbMax, hBx, hLt]

private theorem binaryRelPayloadEq
    {W a b : native_Int} :
    RuleProofs.smt_value_rel (SmtValue.Binary W a) (SmtValue.Binary W b) ->
    a = b := by
  intro h
  simpa [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
    native_veq] using h

theorem factsTerm
    (M : SmtModel) (hM : model_wf M)
    (x ys zs c w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    __eo_typeof (term x ys zs c w) = Term.Bool ->
    eo_interprets M (constPrem c w) true ->
    eo_interprets M (widthPrem w x) true ->
    eo_interprets M (term x ys zs c w) true := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hYsList hZsList
    hTermTy hConstPrem _hWidthPrem
  have hBool := typedTerm x ys zs c w hXTrans hYsTrans hZsTrans hCTrans
    hWTrans hYsList hZsList hTermTy
  rcases inferredArgumentTypes x ys zs c w hXTrans hYsTrans hZsTrans
      hCTrans hWTrans hYsList hZsList hTermTy with
    ⟨W, rfl, hW0, hXTy, hCTy, hZsTy, hYsType, hBaseTy, hIncTy⟩
  let width := native_int_to_nat W
  have hWidthInt : native_nat_to_int width = W := by
    simpa [width] using native_nat_to_int_int_to_nat_eq W hW0
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) width
      (by simpa [width] using hXTy) with ⟨px, hXEval, hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt (base ys zs)) width
      (by simpa [width] using hBaseTy) with ⟨pb, hBaseEval, hBaseCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt c) width
      (by simpa [width] using hCTy) with ⟨pc, hCEval, _hCCan⟩
  rw [hWidthInt] at hXEval hXCan hBaseEval hBaseCan hCEval
  have hXRange := bitvec_payload_range_of_canonical hW0 hXCan
  have hBaseRange := bitvec_payload_range_of_canonical hW0 hBaseCan
  have hOneEval := eval_bv_const M 1 W hW0
  have hConstRel := RuleProofs.eo_interprets_eq_rel M c
    (bvConst (Term.Numeral W) 1) (by simpa [constPrem] using hConstPrem)
  rw [hCEval] at hConstRel
  have hConstRel' :
      RuleProofs.smt_value_rel
        (SmtValue.Binary W pc)
        (SmtValue.Binary W
          (native_mod_total 1 (native_int_pow2 W))) := by
    have hsimpa := (show RuleProofs.smt_value_rel
      (SmtValue.Binary W pc)
      (__smtx_model_eval M (__eo_to_smt (bvConst (Term.Numeral W) 1))) from
        hConstRel)
    try simp [bvConst] at hsimpa ⊢
    exact hsimpa
  have hPc : pc = native_mod_total 1 (native_int_pow2 W) :=
    binaryRelPayloadEq hConstRel'
  have hIncBaseAdd := evalIncEqBaseAdd M hM ys zs c width hYsList
    hZsList hYsType (by simpa [width] using hZsTy)
    (by simpa [width] using hCTy) (by simpa [width] using hBaseTy)
  have hIncEval :
      __smtx_model_eval M (__eo_to_smt (incList ys zs c)) =
        SmtValue.Binary W
          (native_mod_total
            (pb + native_mod_total 1 (native_int_pow2 W))
            (native_int_pow2 W)) := by
    rw [hIncBaseAdd]
    change __smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt (base ys zs)))
        (__smtx_model_eval M (__eo_to_smt c)) = _
    rw [hBaseEval, hCEval, hPc]
    rfl
  have hPowPos := nativeIntPow2PosOfNonneg W hW0
  have hZeroEval := eval_bv_const M 0 W hW0
  have hZeroEval' :
      __smtx_model_eval M
          (__eo_to_smt (bvConst (Term.Numeral W) 0)) =
        SmtValue.Binary W (native_mod_total 0 (native_int_pow2 W)) := by
    simpa [bvConst] using hZeroEval
  have hZeroMod : native_mod_total 0 (native_int_pow2 W) = 0 := by
    unfold native_mod_total
    exact Int.emod_eq_of_lt (by decide) hPowPos
  have hMaxMod :
      native_mod_total (native_int_pow2 W - 1) (native_int_pow2 W) =
        native_int_pow2 W - 1 := by
    unfold native_mod_total
    exact Int.emod_eq_of_lt
      (Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr hPowPos))
      (Int.sub_lt_self _ (by decide))
  have hMaxEval :
      __smtx_model_eval M (__eo_to_smt (maxValue (Term.Numeral W))) =
        SmtValue.Binary W (native_int_pow2 W - 1) := by
    change __smtx_model_eval_bvnot
        (__smtx_model_eval M
          (__eo_to_smt (bvConst (Term.Numeral W) 0))) = _
    rw [hZeroEval', hZeroMod]
    simp only [__smtx_model_eval_bvnot, native_binary_not,
      SmtEval.native_zplus, SmtEval.native_zneg]
    change SmtValue.Binary W
      (native_mod_total (native_int_pow2 W - 1) (native_int_pow2 W)) = _
    rw [hMaxMod]
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs x ys zs c)) =
        SmtValue.Boolean
          (decide (px < native_mod_total
            (pb + native_mod_total 1 (native_int_pow2 W))
            (native_int_pow2 W))) := by
    change __smtx_model_eval_bvult
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (incList ys zs c))) = _
    rw [hXEval, hIncEval]
    rfl
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt (rhs x ys zs (Term.Numeral W))) =
        SmtValue.Boolean
          ((decide (pb ≠ native_int_pow2 W - 1) : Bool) &&
            !(decide (pb < px) : Bool)) := by
    unfold rhs
    change __smtx_model_eval_and
      (__smtx_model_eval_not
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt (base ys zs)))
          (__smtx_model_eval M
            (__eo_to_smt (maxValue (Term.Numeral W))))))
      (__smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval_bvult
            (__smtx_model_eval M (__eo_to_smt (base ys zs)))
            (__smtx_model_eval M (__eo_to_smt x))))
        (SmtValue.Boolean true)) = _
    rw [hBaseEval, hMaxEval, hXEval]
    simp [__smtx_model_eval_eq, __smtx_model_eval_not,
      __smtx_model_eval_and, __smtx_model_eval_bvult,
      __smtx_model_eval_bvugt, native_veq, native_not, native_and,
      SmtEval.native_zlt]
  have hCore := ultAddOneBoolIdentity (native_int_pow2 W) px pb hPowPos
    hXRange.1 hXRange.2 hBaseRange.1 hBaseRange.2
  have hSidesEval :
      __smtx_model_eval M (__eo_to_smt (lhs x ys zs c)) =
        __smtx_model_eval M
          (__eo_to_smt (rhs x ys zs (Term.Numeral W))) := by
    rw [hLhsEval, hRhsEval, hCore]
  unfold term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [term] using hBool
  · rw [hSidesEval]
    exact RuleProofs.smt_value_rel_refl _

theorem programListsOfTypeBool (x ys zs c w P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (program x ys zs c w P1 P2) = Term.Bool ->
    __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hTy
  have hProgNe := termNeStuckOfTypeofBool hTy
  rcases programNormalize x ys zs c w P1 P2 hXTrans hYsTrans hZsTrans
      hCTrans hWTrans hProgNe with ⟨_hP1, _hP2, hSkeleton⟩
  have hSkeletonTy : __eo_typeof (skeleton x ys zs c w) = Term.Bool := by
    rw [← hSkeleton]
    exact hTy
  have hSkeletonNe := termNeStuckOfTypeofBool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  have hLists := guardedListsAndReductions x ys zs c hLhsNe
  exact ⟨hLists.1, hLists.2.1⟩

theorem typedProgram (x ys zs c w P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (program x ys zs c w P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type (program x ys zs c w P1 P2) := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hProgramTy
  rcases programEqTermOfTypeBool x ys zs c w P1 P2 hXTrans hYsTrans
      hZsTrans hCTrans hWTrans hProgramTy with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hLists := programListsOfTypeBool x ys zs c w P1 P2 hXTrans
    hYsTrans hZsTrans hCTrans hWTrans hProgramTy
  have hTermTy : __eo_typeof (term x ys zs c w) = Term.Bool := by
    rw [← hProgramEq]
    exact hProgramTy
  rw [hProgramEq]
  exact typedTerm x ys zs c w hXTrans hYsTrans hZsTrans hCTrans hWTrans
    hLists.1 hLists.2 hTermTy

theorem factsProgram
    (M : SmtModel) (hM : model_wf M)
    (x ys zs c w P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (program x ys zs c w P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (program x ys zs c w P1 P2) true := by
  intro hXTrans hYsTrans hZsTrans hCTrans hWTrans hProgramTy
    hP1True hP2True
  rcases programEqTermOfTypeBool x ys zs c w P1 P2 hXTrans hYsTrans
      hZsTrans hCTrans hWTrans hProgramTy with
    ⟨hP1, hP2, hProgramEq⟩
  have hLists := programListsOfTypeBool x ys zs c w P1 P2 hXTrans
    hYsTrans hZsTrans hCTrans hWTrans hProgramTy
  have hTermTy : __eo_typeof (term x ys zs c w) = Term.Bool := by
    rw [← hProgramEq]
    exact hProgramTy
  have hConstTrue : eo_interprets M (constPrem c w) true := by
    simpa [hP1] using hP1True
  have hWidthTrue : eo_interprets M (widthPrem w x) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact factsTerm M hM x ys zs c w hXTrans hYsTrans hZsTrans hCTrans
    hWTrans hLists.1 hLists.2 hTermTy hConstTrue hWidthTrue

end BvUltAddOneSupport
