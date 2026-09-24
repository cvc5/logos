module

public import Cpc.Proofs.RuleSupport.BvConcatMergeConstSupport
import all Cpc.Proofs.RuleSupport.BvConcatMergeConstSupport

public section

/-! Support for merging adjacent extracts under bit-vector concat. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvConcatExtractMergePremRaw (j2Ref j1Ref : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) j2Ref)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) j1Ref)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0)))

def bvConcatExtractMergePrem (j2 j1 : Term) : Term :=
  bvConcatExtractMergePremRaw j2 j1

def bvConcatExtractMergeHigh (s k j2 : Term) : Term :=
  bvExtractTerm s k j2

def bvConcatExtractMergeLow (s j1 i : Term) : Term :=
  bvExtractTerm s j1 i

def bvConcatExtractMergeWhole (s k i : Term) : Term :=
  bvExtractTerm s k i

def bvConcatExtractMergeLeftSeed
    (s i j1 j2 k ys : Term) : Term :=
  bvConcatTerm (bvConcatExtractMergeHigh s k j2)
    (bvConcatTerm (bvConcatExtractMergeLow s j1 i) ys)

def bvConcatExtractMergeRightSeed
    (s i k ys : Term) : Term :=
  bvConcatTerm (bvConcatExtractMergeWhole s k i) ys

def bvConcatExtractMergeLhs
    (xs s ys i j1 j2 k : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvConcatExtractMergeLeftSeed s i j1 j2 k ys)

def bvConcatExtractMergeRhsList
    (xs s ys i k : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvConcatExtractMergeRightSeed s i k ys)

def bvConcatExtractMergeRhs
    (xs s ys i k : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.concat)
    (bvConcatExtractMergeRhsList xs s ys i k)

def bvConcatExtractMergeTerm
    (xs s ys i j1 j2 k : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvConcatExtractMergeLhs xs s ys i j1 j2 k))
    (bvConcatExtractMergeRhs xs s ys i k)

def bvConcatExtractMergeProgramBody
    (xs s ys i j1 j2 k : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (bvConcatExtractMergeLhs xs s ys i j1 j2 k))
    (bvConcatExtractMergeRhs xs s ys i k)

def bvConcatExtractMergeProgram
    (xs s ys i j1 j2 k P : Term) : Term :=
  __eo_prog_bv_concat_extract_merge xs s ys i j1 j2 k (Proof.pf P)

private theorem bv_concat_extract_merge_guard_refs
    {j2 j1 j2Ref j1Ref body : Term} :
    __eo_requires
        (__eo_and (__eo_eq j2 j2Ref) (__eo_eq j1 j1Ref))
        (Term.Boolean true) body ≠ Term.Stuck ->
    j2Ref = j2 ∧ j1Ref = j1 := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  rcases bv_extract_support_and_true hGuard with ⟨hJ2, hJ1⟩
  exact ⟨(bv_extract_support_eq_true hJ2).symm,
    (bv_extract_support_eq_true hJ1).symm⟩

private theorem bv_concat_extract_merge_premise_shape
    (xs s ys i j1 j2 k P : Term) :
    xs ≠ Term.Stuck -> s ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j1 ≠ Term.Stuck -> j2 ≠ Term.Stuck ->
    k ≠ Term.Stuck ->
    bvConcatExtractMergeProgram xs s ys i j1 j2 k P ≠ Term.Stuck ->
    ∃ j2Ref j1Ref,
      P = bvConcatExtractMergePremRaw j2Ref j1Ref := by
  intro hXs hS hYs hI hJ1 hJ2 hK hProg
  by_cases hShape : ∃ j2Ref j1Ref,
      P = bvConcatExtractMergePremRaw j2Ref j1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_concat_extract_merge.eq_9
      xs s ys i j1 j2 k (Proof.pf P)
      hXs hS hYs hI hJ1 hJ2 hK (by
        intro j2Ref j1Ref hP
        cases hP
        exact hShape ⟨j2Ref, j1Ref, rfl⟩)

private theorem bv_concat_extract_merge_program_canonical
    (xs s ys i j1 j2 k : Term) :
    xs ≠ Term.Stuck -> s ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j1 ≠ Term.Stuck -> j2 ≠ Term.Stuck ->
    k ≠ Term.Stuck ->
    bvConcatExtractMergeProgram xs s ys i j1 j2 k
        (bvConcatExtractMergePrem j2 j1) =
      bvConcatExtractMergeProgramBody xs s ys i j1 j2 k := by
  intro hXs hS hYs hI hJ1 hJ2 hK
  unfold bvConcatExtractMergeProgram bvConcatExtractMergePrem
    bvConcatExtractMergePremRaw
  rw [__eo_prog_bv_concat_extract_merge.eq_8
    xs s ys i j1 j2 k j2 j1 hXs hS hYs hI hJ1 hJ2 hK]
  simp [bvConcatExtractMergeProgramBody, bvConcatExtractMergeLhs,
    bvConcatExtractMergeRhs, bvConcatExtractMergeRhsList,
    bvConcatExtractMergeLeftSeed, bvConcatExtractMergeRightSeed,
    bvConcatExtractMergeHigh, bvConcatExtractMergeLow,
    bvConcatExtractMergeWhole, bvConcatTerm, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and,
    hXs, hS, hYs, hI, hJ1, hJ2, hK]

theorem bvConcatExtractMergeProgram_normalize
    (xs s ys i j1 j2 k P : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j1 ->
    RuleProofs.eo_has_smt_translation j2 ->
    RuleProofs.eo_has_smt_translation k ->
    bvConcatExtractMergeProgram xs s ys i j1 j2 k P ≠ Term.Stuck ->
    P = bvConcatExtractMergePrem j2 j1 ∧
      bvConcatExtractMergeProgram xs s ys i j1 j2 k P =
        bvConcatExtractMergeProgramBody xs s ys i j1 j2 k := by
  intro hXsTrans hSTrans hYsTrans hITrans hJ1Trans hJ2Trans hKTrans
    hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hS := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ1 := RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hJ2 := RuleProofs.term_ne_stuck_of_has_smt_translation j2 hJ2Trans
  have hK := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  rcases bv_concat_extract_merge_premise_shape xs s ys i j1 j2 k P
      hXs hS hYs hI hJ1 hJ2 hK hProg with ⟨j2Ref, j1Ref, hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvConcatExtractMergeProgram bvConcatExtractMergePremRaw at hReq
  rw [__eo_prog_bv_concat_extract_merge.eq_8
    xs s ys i j1 j2 k j2Ref j1Ref
    hXs hS hYs hI hJ1 hJ2 hK] at hReq
  rcases bv_concat_extract_merge_guard_refs hReq with
    ⟨hJ2Ref, hJ1Ref⟩
  subst j2Ref
  subst j1Ref
  have hPCanon : P = bvConcatExtractMergePrem j2 j1 := by
    simpa [bvConcatExtractMergePrem] using hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_concat_extract_merge_program_canonical
    xs s ys i j1 j2 k hXs hS hYs hI hJ1 hJ2 hK

private theorem bv_concat_extract_merge_mk_apply_args_ne_stuck
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck -> f ≠ Term.Stuck ∧ x ≠ Term.Stuck := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem bv_concat_extract_merge_mk_apply_eq
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

theorem bvConcatExtractMergeProgramBody_eq_term_of_type_bool
    (xs s ys i j1 j2 k : Term) :
    __eo_typeof
        (bvConcatExtractMergeProgramBody xs s ys i j1 j2 k) =
      Term.Bool ->
    bvConcatExtractMergeProgramBody xs s ys i j1 j2 k =
      bvConcatExtractMergeTerm xs s ys i j1 j2 k := by
  intro hTy
  let lhs := bvConcatExtractMergeLhs xs s ys i j1 j2 k
  let rhs := bvConcatExtractMergeRhs xs s ys i k
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvConcatExtractMergeProgramBody, lhs, rhs, eqHead] using hNe
  have hEqHeadNe :=
    (bv_concat_extract_merge_mk_apply_args_ne_stuck hBodyNe).1
  have hOuter := bv_concat_extract_merge_mk_apply_eq hBodyNe
  have hHead := bv_concat_extract_merge_mk_apply_eq hEqHeadNe
  calc
    bvConcatExtractMergeProgramBody xs s ys i j1 j2 k =
        __eo_mk_apply eqHead rhs := by
      simp [bvConcatExtractMergeProgramBody, lhs, rhs, eqHead]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs := by
      rw [hOuter]
      rw [show eqHead = Term.Apply (Term.UOp UserOp.eq) lhs by
        simpa [eqHead] using hHead]
    _ = bvConcatExtractMergeTerm xs s ys i j1 j2 k := by
      simp [bvConcatExtractMergeTerm, lhs, rhs]

private theorem bv_concat_extract_merge_body_args_ne_stuck
    (xs s ys i j1 j2 k : Term) :
    __eo_typeof
        (bvConcatExtractMergeProgramBody xs s ys i j1 j2 k) =
      Term.Bool ->
    bvConcatExtractMergeLhs xs s ys i j1 j2 k ≠ Term.Stuck ∧
      bvConcatExtractMergeRhs xs s ys i k ≠ Term.Stuck := by
  intro hTy
  let lhs := bvConcatExtractMergeLhs xs s ys i j1 j2 k
  let rhs := bvConcatExtractMergeRhs xs s ys i k
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvConcatExtractMergeProgramBody, lhs, rhs, eqHead] using hNe
  have hHeadNe :=
    (bv_concat_extract_merge_mk_apply_args_ne_stuck hBodyNe).1
  exact
    ⟨(bv_concat_extract_merge_mk_apply_args_ne_stuck hHeadNe).2,
      (bv_concat_extract_merge_mk_apply_args_ne_stuck hBodyNe).2⟩

private theorem bv_concat_extract_merge_singleton_list_of_ne_stuck
    (c : Term) :
    __eo_list_singleton_elim (Term.UOp UserOp.concat) c ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c) ≠
        Term.Stuck := by
    simpa [__eo_list_singleton_elim] using h
  exact support_eo_requires_cond_eq_of_non_stuck hReq

private theorem bv_concat_extract_merge_list_rec_right_type_ne
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof z ≠ Term.Stuck := by
  intro hList
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [__eo_is_list] at hList
  | case2 a =>
      intro h
      exfalso
      apply h
      cases a <;> rfl
  | case3 g x y z hZ ih =>
      intro hTy
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) g x y hList
      subst g
      have hTailList := eo_is_list_tail_true_of_cons_self
        (Term.UOp UserOp.concat) x y hList
      have hTailRecNe : __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.concat) y z hTailList hZ
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailRecNe] at hTy
      change __eo_typeof_concat (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec y z)) ≠ Term.Stuck at hTy
      rcases bvConcat_eo_typeof_concat_args_bitvec hTy with
        ⟨_wh, wt, _hHeadTy, hTailTy⟩
      apply ih hTailList
      rw [hTailTy]
      intro h
      cases h
  | case4 nil z hNil hZ hNot =>
      intro hTy
      simpa [__eo_list_concat_rec, hZ] using hTy

private theorem bv_concat_extract_merge_list_right_type_ne
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __eo_typeof (__eo_list_concat (Term.UOp UserOp.concat) a z) ≠
      Term.Stuck ->
    __eo_typeof z ≠ Term.Stuck := by
  intro hAList hZList hTy
  have hRecTy : __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck := by
    simpa [__eo_list_concat, hAList, hZList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] using hTy
  exact bv_concat_extract_merge_list_rec_right_type_ne a z hAList hRecTy

private theorem bv_concat_extract_merge_body_context
    (xs s ys i j1 j2 k : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation ys ->
    __eo_typeof
        (bvConcatExtractMergeProgramBody xs s ys i j1 j2 k) =
      Term.Bool ->
    ∃ w kv j2v j1v iv : native_Int, ∃ wxs wys : Nat,
      k = Term.Numeral kv ∧ j2 = Term.Numeral j2v ∧
      j1 = Term.Numeral j1v ∧ i = Term.Numeral iv ∧
      native_zleq 0 w = true ∧ native_zleq 0 j2v = true ∧
      native_zlt kv w = true ∧
      native_zlt 0
        (native_zplus (native_zplus kv 1) (native_zneg j2v)) = true ∧
      native_zleq 0 iv = true ∧ native_zlt j1v w = true ∧
      native_zlt 0
        (native_zplus (native_zplus j1v 1) (native_zneg iv)) = true ∧
      native_zlt 0
        (native_zplus (native_zplus kv 1) (native_zneg iv)) = true ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt s) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys := by
  intro hXsTrans hSTrans hYsTrans hBodyTy
  have hBodyEq := bvConcatExtractMergeProgramBody_eq_term_of_type_bool
    xs s ys i j1 j2 k hBodyTy
  have hTermTy :
      __eo_typeof (bvConcatExtractMergeTerm xs s ys i j1 j2 k) =
        Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hLhsTyNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvConcatExtractMergeLhs xs s ys i j1 j2 k))
      (__eo_typeof (bvConcatExtractMergeRhs xs s ys i k))
      (by have hsimpa := hTermTy; (try simp [bvConcatExtractMergeTerm] at hsimpa ⊢); exact hsimpa)).1
  have hLhsTermNe :=
    (bv_concat_extract_merge_body_args_ne_stuck
      xs s ys i j1 j2 k hBodyTy).1
  rcases bvConcat_list_concat_lists_of_ne_stuck xs
      (bvConcatExtractMergeLeftSeed s i j1 j2 k ys)
      (by simpa [bvConcatExtractMergeLhs] using hLhsTermNe) with
    ⟨hXsList, hLeftSeedList⟩
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatTerm (bvConcatExtractMergeLow s j1 i) ys) =
        Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self
      (Term.UOp UserOp.concat) (bvConcatExtractMergeHigh s k j2)
      (bvConcatTerm (bvConcatExtractMergeLow s j1 i) ys)
      (by have hsimpa := hLeftSeedList; (try simp [bvConcatExtractMergeLeftSeed] at hsimpa ⊢); exact hsimpa)
  have hYsList :
      __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self
      (Term.UOp UserOp.concat) (bvConcatExtractMergeLow s j1 i) ys
      (by have hsimpa := hInnerList; (try simp at hsimpa ⊢); exact hsimpa)
  have hLeftSeedTyNe :
      __eo_typeof (bvConcatExtractMergeLeftSeed s i j1 j2 k ys) ≠
        Term.Stuck :=
    bv_concat_extract_merge_list_right_type_ne xs
      (bvConcatExtractMergeLeftSeed s i j1 j2 k ys)
      hXsList hLeftSeedList
      (by simpa [bvConcatExtractMergeLhs] using hLhsTyNe)
  change __eo_typeof_concat
      (__eo_typeof (bvConcatExtractMergeHigh s k j2))
      (__eo_typeof (bvConcatTerm (bvConcatExtractMergeLow s j1 i) ys)) ≠
        Term.Stuck at hLeftSeedTyNe
  rcases bvConcat_eo_typeof_concat_args_bitvec hLeftSeedTyNe with
    ⟨widthHigh, widthTail, hHighTy, hTailTy⟩
  have hTailTyNe :
      __eo_typeof (bvConcatTerm (bvConcatExtractMergeLow s j1 i) ys) ≠
        Term.Stuck := by
    rw [hTailTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof (bvConcatExtractMergeLow s j1 i))
      (__eo_typeof ys) ≠ Term.Stuck at hTailTyNe
  rcases bvConcat_eo_typeof_concat_args_bitvec hTailTyNe with
    ⟨widthLow, widthYs, hLowTy, _hYsTy⟩
  have hHighTyNe :
      __eo_typeof (bvConcatExtractMergeHigh s k j2) ≠ Term.Stuck := by
    rw [hHighTy]
    intro h
    cases h
  have hLowTyNe :
      __eo_typeof (bvConcatExtractMergeLow s j1 i) ≠ Term.Stuck := by
    rw [hLowTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck s k j2 hSTrans
      (by simpa [bvConcatExtractMergeHigh] using hHighTyNe) with
    ⟨w, kv, j2v, hSEoTy, hK, hJ2, hw0, hj20, hkw,
      hDHigh0, hSSmtTy⟩
  rcases bv_extract_context_of_non_stuck s j1 i hSTrans
      (by simpa [bvConcatExtractMergeLow] using hLowTyNe) with
    ⟨wLow, j1v, iv, hSEoTyLow, hJ1, hI, hwLow0, hi0, hj1wLow,
      hDLow0, hSSmtTyLow⟩
  have hWEq : wLow = w := by
    rw [hSEoTy] at hSEoTyLow
    cases hSEoTyLow
    rfl
  subst wLow
  rcases bvConcat_list_smt_type_of_translation xs hXsList hXsTrans with
    ⟨wxs, hXsSmtTy⟩
  rcases bvConcat_list_smt_type_of_translation ys hYsList hYsTrans with
    ⟨wys, hYsSmtTy⟩
  let dHigh := native_zplus (native_zplus kv 1) (native_zneg j2v)
  let dLow := native_zplus (native_zplus j1v 1) (native_zneg iv)
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeHigh s (Term.Numeral kv)
              (Term.Numeral j2v))) =
        SmtType.BitVec (native_int_to_nat dHigh) := by
    simpa [bvConcatExtractMergeHigh, dHigh] using
      smt_typeof_extract_of_context s w kv j2v hSSmtTy
        hw0 hj20 hkw hDHigh0
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLow s (Term.Numeral j1v)
              (Term.Numeral iv))) =
        SmtType.BitVec (native_int_to_nat dLow) := by
    simpa [bvConcatExtractMergeLow, dLow] using
      smt_typeof_extract_of_context s w j1v iv hSSmtTy
        hw0 hi0 hj1wLow hDLow0
  have hInnerSmtTy := bvConcat_term_smt_type
    (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys
    (native_int_to_nat dLow) wys hLowSmtTy hYsSmtTy
  have hLeftSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv) ys)) =
        SmtType.BitVec
          (native_int_to_nat dHigh + (native_int_to_nat dLow + wys)) := by
    simpa [bvConcatExtractMergeLeftSeed] using
      bvConcat_term_smt_type
        (bvConcatExtractMergeHigh s (Term.Numeral kv) (Term.Numeral j2v))
        (bvConcatTerm
          (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv))
          ys)
        (native_int_to_nat dHigh) (native_int_to_nat dLow + wys)
        hHighSmtTy hInnerSmtTy
  have hLhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv))) =
        SmtType.BitVec
          (wxs + (native_int_to_nat dHigh +
            (native_int_to_nat dLow + wys))) := by
    exact bvConcat_list_concat_smt_type xs
      (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv) ys)
      wxs (native_int_to_nat dHigh + (native_int_to_nat dLow + wys))
      hXsList (by simpa [hK, hJ2, hJ1, hI] using hLeftSeedList)
      hXsSmtTy hLeftSeedSmtTy
  have hLhsTrans : RuleProofs.eo_has_smt_translation
      (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsSmtTy]
    intro h
    cases h
  have hLhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv))
      (__eo_typeof
        (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
          (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)))
      (__eo_to_smt
        (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
          (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)))
      rfl hLhsTrans rfl
  have hLhsEoTy :=
    TranslationProofs.eo_typeof_eq_bitvec_of_smt_bitvec_from_ih
      (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv))
      (fun _ => hLhsBridge)
      (wxs + (native_int_to_nat dHigh +
        (native_int_to_nat dLow + wys))) hLhsSmtTy
  have hTypeEq :
      __eo_typeof (bvConcatExtractMergeLhs xs s ys i j1 j2 k) =
        __eo_typeof (bvConcatExtractMergeRhs xs s ys i k) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _
      (by have hsimpa := hTermTy; (try simp [bvConcatExtractMergeTerm] at hsimpa ⊢); exact hsimpa)
  have hRhsEoTy :
      __eo_typeof
          (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
            (Term.Numeral kv)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_nat_to_int
              (wxs + (native_int_to_nat dHigh +
                (native_int_to_nat dLow + wys))))) := by
    have hTypeEq' :
        __eo_typeof
            (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)) =
          __eo_typeof
            (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
              (Term.Numeral kv)) := by
      simpa [hK, hJ2, hJ1, hI] using hTypeEq
    rw [← hTypeEq']
    exact hLhsEoTy
  have hRhsTermNe :=
    (bv_concat_extract_merge_body_args_ne_stuck
      xs s ys i j1 j2 k hBodyTy).2
  have hRhsListList :=
    bv_concat_extract_merge_singleton_list_of_ne_stuck
      (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
        (Term.Numeral kv))
      (by simpa [hK, hI, bvConcatExtractMergeRhs] using hRhsTermNe)
  have hRhsListEoTy := bvConcat_singleton_elim_eo_type_inv
    (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
      (Term.Numeral kv))
    (wxs + (native_int_to_nat dHigh + (native_int_to_nat dLow + wys)))
    hRhsListList (by simpa [bvConcatExtractMergeRhs] using hRhsEoTy)
  have hRhsListTermNe :
      bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
          (Term.Numeral kv) ≠ Term.Stuck := by
    intro h
    rw [h] at hRhsListEoTy
    change Term.Stuck = _ at hRhsListEoTy
    cases hRhsListEoTy
  rcases bvConcat_list_concat_lists_of_ne_stuck xs
      (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
        (Term.Numeral kv) ys)
      (by simpa [bvConcatExtractMergeRhsList] using hRhsListTermNe) with
    ⟨_hXsListRhs, hRightSeedList⟩
  rcases bvConcat_eo_typeof_list_concat_right_bitvec xs
      (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
        (Term.Numeral kv) ys)
      (Term.Numeral
        (native_nat_to_int
          (wxs + (native_int_to_nat dHigh +
            (native_int_to_nat dLow + wys)))))
      hXsList hRightSeedList
      (by simpa [bvConcatExtractMergeRhsList] using hRhsListEoTy) with
    ⟨widthRight, hRightSeedEoTy⟩
  have hRightSeedTyNe :
      __eo_typeof
          (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
            (Term.Numeral kv) ys) ≠ Term.Stuck := by
    rw [hRightSeedEoTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof
        (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv)))
      (__eo_typeof ys) ≠ Term.Stuck at hRightSeedTyNe
  rcases bvConcat_eo_typeof_concat_args_bitvec hRightSeedTyNe with
    ⟨widthWhole, widthYsRhs, hWholeTy, _hYsEoTyRhs⟩
  have hWholeTyNe :
      __eo_typeof
          (bvConcatExtractMergeWhole s (Term.Numeral kv)
            (Term.Numeral iv)) ≠ Term.Stuck := by
    rw [hWholeTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck s
      (Term.Numeral kv) (Term.Numeral iv) hSTrans
      (by simpa [bvConcatExtractMergeWhole] using hWholeTyNe) with
    ⟨wWhole, kvWhole, ivWhole, hSEoWhole, hKWhole, hIWhole,
      hwWhole0, hiWhole0, hkWhole, hDWhole0, hSSmtWhole⟩
  have hWWholeEq : wWhole = w := by
    rw [hSEoTy] at hSEoWhole
    cases hSEoWhole
    rfl
  have hKvWholeEq : kvWhole = kv := by
    cases hKWhole
    rfl
  have hIvWholeEq : ivWhole = iv := by
    cases hIWhole
    rfl
  subst wWhole
  subst kvWhole
  subst ivWhole
  exact ⟨w, kv, j2v, j1v, iv, wxs, wys,
    hK, hJ2, hJ1, hI, hw0, hj20, hkw, hDHigh0, hi0, hj1wLow,
    hDLow0, hDWhole0, hXsList, hYsList, hSSmtTy,
    hXsSmtTy, hYsSmtTy⟩

private theorem model_eval_eq_true_of_eo_eq_true_concat_extract_merge
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem bv_concat_extract_merge_premise_index_eq
    (M : SmtModel) (j2v j1v : native_Int) :
    eo_interprets M
        (bvConcatExtractMergePrem (Term.Numeral j2v)
          (Term.Numeral j1v)) true ->
    j2v = j1v + 1 := by
  intro hPrem
  have hEq := model_eval_eq_true_of_eo_eq_true_concat_extract_merge M
    (Term.Numeral j2v)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral j1v))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0)))
    (by simpa [bvConcatExtractMergePrem,
      bvConcatExtractMergePremRaw] using hPrem)
  have hRightEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
                (Term.Numeral j1v))
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
                  (Term.Numeral 1)) (Term.Numeral 0)))) =
        SmtValue.Numeral (j1v + 1) := by
    change __smtx_model_eval M
      (SmtTerm.plus (SmtTerm.Numeral j1v)
        (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) = _
    simp [__smtx_model_eval, __smtx_model_eval_plus,
      SmtEval.native_zplus]
  rw [hRightEval] at hEq
  change __smtx_model_eval_eq (SmtValue.Numeral j2v)
      (SmtValue.Numeral (j1v + 1)) = SmtValue.Boolean true at hEq
  simpa [__smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] using hEq

private theorem bv_concat_extract_merge_concat_bitvec_values
    (x : BitVec A) (y : BitVec B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑B : Int) (↑y.toNat : Int)) =
      SmtValue.Binary (↑(A + B) : Int) (↑(x ++ y).toNat : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hWidth : (↑A + ↑B : Int) = ↑(A + B) := by norm_cast
  rw [hWidth, natpow2_eq B, natpow2_eq (A + B),
    show ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (A + B)) = ((2 ^ (A + B) : Nat) : Int) by
      norm_cast]
  norm_cast
  have hyLt : y.toNat < 2 ^ B := y.isLt
  have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hyLt x.toNat
  have hFormula : x.toNat * 2 ^ B + y.toNat = (x ++ y).toNat := by
    rw [BitVec.toNat_append, ← hShiftOr, Nat.shiftLeft_eq]
  rw [hFormula, Nat.mod_eq_of_lt (x ++ y).isLt]

private theorem bv_concat_extract_merge_adjacent_extracts
    {x : BitVec W} {I J K : Nat}
    (hIJ : I ≤ J + 1) (hJK : J + 1 ≤ K) (hKW : K < W) :
    ((x.extractLsb' (J + 1) (K - J)) ++
        (x.extractLsb' I (J + 1 - I))).cast (by omega) =
      x.extractLsb' I (K + 1 - I) := by
  apply BitVec.eq_of_getElem_eq
  intro q hq
  simp only [BitVec.getElem_cast, BitVec.getElem_append,
    BitVec.getElem_extractLsb']
  by_cases hLow : q < J + 1 - I
  · simp only [hLow, dif_pos]
  · simp only [hLow, dif_neg]
    have hIndexEq :
        J + 1 + (q - (J + 1 - I)) = I + q := by omega
    have hFull : I + q < W := by omega
    rw [hIndexEq]
    simp [hFull]

private theorem bv_concat_extract_merge_value
    (W I J K : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hIJ : I ≤ J + 1) (hJK : J + 1 ≤ K) (hKW : K < W) :
    __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral (↑K : Int))
          (SmtValue.Numeral (↑(J + 1) : Int))
          (SmtValue.Binary (↑W : Int) p))
        (__smtx_model_eval_extract
          (SmtValue.Numeral (↑J : Int))
          (SmtValue.Numeral (↑I : Int))
          (SmtValue.Binary (↑W : Int) p)) =
      __smtx_model_eval_extract
        (SmtValue.Numeral (↑K : Int))
        (SmtValue.Numeral (↑I : Int))
        (SmtValue.Binary (↑W : Int) p) := by
  let x := BitVec.ofInt W p
  rw [extract_val_bitvec_start_len W (J + 1) (K - J) p
      (↑K : Int) (↑(J + 1) : Int) hp0 hp1 rfl (by
        norm_cast
        omega)]
  rw [extract_val_bitvec_start_len W I (J + 1 - I) p
      (↑J : Int) (↑I : Int) hp0 hp1 rfl (by
        norm_cast
        omega)]
  rw [extract_val_bitvec_start_len W I (K + 1 - I) p
      (↑K : Int) (↑I : Int) hp0 hp1 rfl (by
        norm_cast
        omega)]
  rw [bv_concat_extract_merge_concat_bitvec_values]
  have hWidth : (K - J) + (J + 1 - I) = K + 1 - I := by omega
  congr 2
  have hAdjacent := bv_concat_extract_merge_adjacent_extracts
    (x := x) hIJ hJK hKW
  simpa [x, BitVec.toNat_cast] using congrArg BitVec.toNat hAdjacent

private theorem eval_bv_concat_extract_merge_core
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (w kv j2v j1v iv : native_Int) :
    __smtx_typeof (__eo_to_smt s) =
        SmtType.BitVec (native_int_to_nat w) ->
    native_zleq 0 w = true ->
    native_zleq 0 j2v = true ->
    native_zlt kv w = true ->
    native_zlt 0
        (native_zplus (native_zplus kv 1) (native_zneg j2v)) = true ->
    native_zleq 0 iv = true ->
    native_zlt 0
        (native_zplus (native_zplus j1v 1) (native_zneg iv)) = true ->
    j2v = j1v + 1 ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm
            (bvConcatExtractMergeHigh s (Term.Numeral kv)
              (Term.Numeral j2v))
            (bvConcatExtractMergeLow s (Term.Numeral j1v)
              (Term.Numeral iv)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatExtractMergeWhole s (Term.Numeral kv)
            (Term.Numeral iv))) := by
  intro hSTy hw0 hj20 hkw hDHigh0 hi0 hDLow0 hAdjacent
  have hW0Int : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  have hJ20Int : (0 : Int) ≤ j2v := by
    simpa [SmtEval.native_zleq] using hj20
  have hI0Int : (0 : Int) ≤ iv := by
    simpa [SmtEval.native_zleq] using hi0
  have hKwInt : kv < w := by
    simpa [SmtEval.native_zlt] using hkw
  have hDHighInt : 0 < kv + 1 + -j2v := by
    have hsimpa := hDHigh0
    try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact of_decide_eq_true hsimpa
  have hDLowInt : 0 < j1v + 1 + -iv := by
    have hsimpa := hDLow0
    try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact of_decide_eq_true hsimpa
  have hJ2LtK1 : j2v < kv + 1 := by
    have hSub : 0 < (kv + 1 - j2v) := by
      rw [Int.sub_eq_add_neg]
      exact hDHighInt
    exact Int.sub_pos.mp hSub
  have hILtJ11 : iv < j1v + 1 := by
    have hSub : 0 < (j1v + 1 - iv) := by
      rw [Int.sub_eq_add_neg]
      exact hDLowInt
    exact Int.sub_pos.mp hSub
  have hJ2LeK : j2v ≤ kv := Int.lt_add_one_iff.mp hJ2LtK1
  have hILeJ1 : iv ≤ j1v := Int.lt_add_one_iff.mp hILtJ11
  have hJ10Int : (0 : Int) ≤ j1v := Int.le_trans hI0Int hILeJ1
  have hK0Int : (0 : Int) ≤ kv := Int.le_trans hJ20Int hJ2LeK
  have hJ10 : native_zleq 0 j1v = true := by
    simpa [SmtEval.native_zleq] using hJ10Int
  have hK0 : native_zleq 0 kv = true := by
    simpa [SmtEval.native_zleq] using hK0Int
  let W := native_int_to_nat w
  let K := native_int_to_nat kv
  let J := native_int_to_nat j1v
  let I := native_int_to_nat iv
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hKRound : (↑K : Int) = kv := by
    simpa [K, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip kv hK0
  have hJRound : (↑J : Int) = j1v := by
    simpa [J, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip j1v hJ10
  have hIRound : (↑I : Int) = iv := by
    simpa [I, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip iv hi0
  have hJ2Round : (↑(J + 1) : Int) = j2v := by
    calc
      (↑(J + 1) : Int) = (↑J : Int) + 1 := by norm_cast
      _ = j1v + 1 := by rw [hJRound]
      _ = j2v := hAdjacent.symm
  have hIJ : I ≤ J + 1 := by
    have hCast : (↑I : Int) ≤ (↑(J + 1) : Int) := by
      rw [hIRound, hJ2Round, hAdjacent]
      exact Int.le_trans hILeJ1 (Int.le_add_one (Int.le_refl j1v))
    exact_mod_cast hCast
  have hJK : J + 1 ≤ K := by
    have hCast : (↑(J + 1) : Int) ≤ (↑K : Int) := by
      rw [hJ2Round, hKRound]
      exact hJ2LeK
    exact_mod_cast hCast
  have hKW : K < W := by
    have hCast : (↑K : Int) < (↑W : Int) := by
      rw [hKRound, hWRound]
      exact hKwInt
    exact_mod_cast hCast
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt s) W
      (by simpa [W] using hSTy) with ⟨p, hSEval, hCanonical⟩
  have hSEval' :
      __smtx_model_eval M (__eo_to_smt s) =
        SmtValue.Binary (↑W : Int) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hSEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCanonical
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hRange.2
  change __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatExtractMergeHigh s (Term.Numeral kv)
            (Term.Numeral j2v))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatExtractMergeLow s (Term.Numeral j1v)
            (Term.Numeral iv)))) = _
  simp only [bvConcatExtractMergeHigh, bvConcatExtractMergeLow,
    bvConcatExtractMergeWhole]
  rw [eval_extract_term M s kv j2v,
    eval_extract_term M s j1v iv,
    eval_extract_term M s kv iv, hSEval']
  simpa [hKRound, hJ2Round, hJRound, hIRound] using
    bv_concat_extract_merge_value W I J K p hp0 hp1 hIJ hJK hKW

theorem typed_bv_concat_extract_merge_program
    (xs s ys i j1 j2 k P : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j1 ->
    RuleProofs.eo_has_smt_translation j2 ->
    RuleProofs.eo_has_smt_translation k ->
    bvConcatExtractMergeProgram xs s ys i j1 j2 k P ≠ Term.Stuck ->
    __eo_typeof (bvConcatExtractMergeProgram xs s ys i j1 j2 k P) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvConcatExtractMergeProgram xs s ys i j1 j2 k P) := by
  intro hXsTrans hSTrans hYsTrans hITrans hJ1Trans hJ2Trans hKTrans
    hProgNe hProgTy
  rcases bvConcatExtractMergeProgram_normalize xs s ys i j1 j2 k P
      hXsTrans hSTrans hYsTrans hITrans hJ1Trans hJ2Trans hKTrans
      hProgNe with ⟨_hP, hProgEq⟩
  have hBodyTy :
      __eo_typeof
          (bvConcatExtractMergeProgramBody xs s ys i j1 j2 k) =
        Term.Bool := by
    rw [← hProgEq]
    exact hProgTy
  rcases bv_concat_extract_merge_body_context xs s ys i j1 j2 k
      hXsTrans hSTrans hYsTrans hBodyTy with
    ⟨w, kv, j2v, j1v, iv, wxs, wys, rfl, rfl, rfl, rfl,
      hw0, hj20, hkw, hDHigh0, hi0, hj1w, hDLow0, hDWhole0,
      hXsList, hYsList, hSSmtTy, hXsSmtTy, hYsSmtTy⟩
  let dHigh := native_zplus (native_zplus kv 1) (native_zneg j2v)
  let dLow := native_zplus (native_zplus j1v 1) (native_zneg iv)
  let dWhole := native_zplus (native_zplus kv 1) (native_zneg iv)
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeHigh s (Term.Numeral kv)
              (Term.Numeral j2v))) =
        SmtType.BitVec (native_int_to_nat dHigh) := by
    simpa [bvConcatExtractMergeHigh, dHigh] using
      smt_typeof_extract_of_context s w kv j2v hSSmtTy
        hw0 hj20 hkw hDHigh0
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLow s (Term.Numeral j1v)
              (Term.Numeral iv))) =
        SmtType.BitVec (native_int_to_nat dLow) := by
    simpa [bvConcatExtractMergeLow, dLow] using
      smt_typeof_extract_of_context s w j1v iv hSSmtTy
        hw0 hi0 hj1w hDLow0
  have hWholeSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeWhole s (Term.Numeral kv)
              (Term.Numeral iv))) =
        SmtType.BitVec (native_int_to_nat dWhole) := by
    simpa [bvConcatExtractMergeWhole, dWhole] using
      smt_typeof_extract_of_context s w kv iv hSSmtTy
        hw0 hi0 hkw hDWhole0
  have hInnerSmtTy := bvConcat_term_smt_type
    (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys
    (native_int_to_nat dLow) wys hLowSmtTy hYsSmtTy
  have hLeftSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv) ys)) =
        SmtType.BitVec
          (native_int_to_nat dHigh + (native_int_to_nat dLow + wys)) := by
    simpa [bvConcatExtractMergeLeftSeed] using
      bvConcat_term_smt_type
        (bvConcatExtractMergeHigh s (Term.Numeral kv) (Term.Numeral j2v))
        (bvConcatTerm
          (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv))
          ys)
        (native_int_to_nat dHigh) (native_int_to_nat dLow + wys)
        hHighSmtTy hInnerSmtTy
  have hInnerList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat)
    (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys
    (by intro h; cases h) hYsList
  have hLeftSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
            (Term.Numeral j1v) (Term.Numeral j2v)
            (Term.Numeral kv) ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatExtractMergeHigh s (Term.Numeral kv) (Term.Numeral j2v))
      (bvConcatTerm
        (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys)
      (by intro h; cases h) hInnerList
  have hLhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv))) =
        SmtType.BitVec
          (wxs + (native_int_to_nat dHigh +
            (native_int_to_nat dLow + wys))) :=
    bvConcat_list_concat_smt_type xs
      (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv) ys)
      wxs (native_int_to_nat dHigh + (native_int_to_nat dLow + wys))
      hXsList hLeftSeedList hXsSmtTy hLeftSeedSmtTy
  have hRightSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
              (Term.Numeral kv) ys)) =
        SmtType.BitVec (native_int_to_nat dWhole + wys) := by
    simpa [bvConcatExtractMergeRightSeed] using
      bvConcat_term_smt_type
        (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv))
        ys (native_int_to_nat dWhole) wys hWholeSmtTy hYsSmtTy
  have hRightSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
            (Term.Numeral kv) ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv))
      ys (by intro h; cases h) hYsList
  have hRhsListSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
              (Term.Numeral kv))) =
        SmtType.BitVec (wxs + (native_int_to_nat dWhole + wys)) :=
    bvConcat_list_concat_smt_type xs
      (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
        (Term.Numeral kv) ys)
      wxs (native_int_to_nat dWhole + wys) hXsList hRightSeedList
      hXsSmtTy hRightSeedSmtTy
  have hRhsListList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
            (Term.Numeral kv)) = Term.Boolean true := by
    have hRecList := eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.concat) xs
      (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
        (Term.Numeral kv) ys) hXsList hRightSeedList
    simpa [bvConcatExtractMergeRhsList, __eo_list_concat,
      hXsList, hRightSeedList, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not] using hRecList
  have hRhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
              (Term.Numeral kv))) =
        SmtType.BitVec (wxs + (native_int_to_nat dWhole + wys)) :=
    bvConcat_singleton_elim_smt_type
      (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
        (Term.Numeral kv))
      (wxs + (native_int_to_nat dWhole + wys))
      hRhsListList hRhsListSmtTy
  have hBodyEq := bvConcatExtractMergeProgramBody_eq_term_of_type_bool
    xs s ys (Term.Numeral iv) (Term.Numeral j1v)
      (Term.Numeral j2v) (Term.Numeral kv) hBodyTy
  have hTermTy :
      __eo_typeof
          (bvConcatExtractMergeTerm xs s ys (Term.Numeral iv)
            (Term.Numeral j1v) (Term.Numeral j2v)
            (Term.Numeral kv)) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hEOTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof
      (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)))
    (__eo_typeof
      (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
        (Term.Numeral kv)))
    (by have hsimpa := hTermTy; (try simp [bvConcatExtractMergeTerm] at hsimpa ⊢); exact hsimpa)
  have hLhsTrans : RuleProofs.eo_has_smt_translation
      (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsSmtTy]
    intro h
    cases h
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
        (Term.Numeral kv)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hRhsSmtTy]
    intro h
    cases h
  have hLhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      _ _ _ rfl hLhsTrans rfl
  have hRhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      _ _ _ rfl hRhsTrans rfl
  have hTermBool : RuleProofs.eo_has_bool_type
      (bvConcatExtractMergeTerm xs s ys (Term.Numeral iv)
        (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv)) := by
    unfold bvConcatExtractMergeTerm
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
      (by rw [hLhsSmtTy]; intro h; cases h)
  rw [hProgEq]
  simpa [hBodyEq] using hTermBool

theorem facts_bv_concat_extract_merge_program
    (M : SmtModel) (hM : model_wf M)
    (xs s ys i j1 j2 k P : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j1 ->
    RuleProofs.eo_has_smt_translation j2 ->
    RuleProofs.eo_has_smt_translation k ->
    bvConcatExtractMergeProgram xs s ys i j1 j2 k P ≠ Term.Stuck ->
    __eo_typeof (bvConcatExtractMergeProgram xs s ys i j1 j2 k P) =
      Term.Bool ->
    eo_interprets M P true ->
    eo_interprets M
      (bvConcatExtractMergeProgram xs s ys i j1 j2 k P) true := by
  intro hXsTrans hSTrans hYsTrans hITrans hJ1Trans hJ2Trans hKTrans
    hProgNe hProgTy hPremTrue
  have hTyped := typed_bv_concat_extract_merge_program
    xs s ys i j1 j2 k P hXsTrans hSTrans hYsTrans hITrans hJ1Trans
    hJ2Trans hKTrans hProgNe hProgTy
  rcases bvConcatExtractMergeProgram_normalize xs s ys i j1 j2 k P
      hXsTrans hSTrans hYsTrans hITrans hJ1Trans hJ2Trans hKTrans
      hProgNe with ⟨hP, hProgEq⟩
  have hBodyTy :
      __eo_typeof
          (bvConcatExtractMergeProgramBody xs s ys i j1 j2 k) =
        Term.Bool := by
    rw [← hProgEq]
    exact hProgTy
  rcases bv_concat_extract_merge_body_context xs s ys i j1 j2 k
      hXsTrans hSTrans hYsTrans hBodyTy with
    ⟨w, kv, j2v, j1v, iv, wxs, wys, rfl, rfl, rfl, rfl,
      hw0, hj20, hkw, hDHigh0, hi0, hj1w, hDLow0, hDWhole0,
      hXsList, hYsList, hSSmtTy, hXsSmtTy, hYsSmtTy⟩
  have hPremNumeric : eo_interprets M
      (bvConcatExtractMergePrem (Term.Numeral j2v)
        (Term.Numeral j1v)) true := by
    rw [hP] at hPremTrue
    exact hPremTrue
  have hAdjacent : j2v = j1v + 1 :=
    bv_concat_extract_merge_premise_index_eq M j2v j1v hPremNumeric
  let dHigh := native_zplus (native_zplus kv 1) (native_zneg j2v)
  let dLow := native_zplus (native_zplus j1v 1) (native_zneg iv)
  let dWhole := native_zplus (native_zplus kv 1) (native_zneg iv)
  let DH := native_int_to_nat dHigh
  let DL := native_int_to_nat dLow
  let DW := native_int_to_nat dWhole
  have hDHighNonneg : native_zleq 0 dHigh = true :=
    native_zleq_of_zlt_true _ _ hDHigh0
  have hDLowNonneg : native_zleq 0 dLow = true :=
    native_zleq_of_zlt_true _ _ hDLow0
  have hDWholeNonneg : native_zleq 0 dWhole = true :=
    native_zleq_of_zlt_true _ _ hDWhole0
  have hDHighRound : (↑DH : Int) = dHigh := by
    simpa [DH, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip dHigh hDHighNonneg
  have hDLowRound : (↑DL : Int) = dLow := by
    simpa [DL, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip dLow hDLowNonneg
  have hDWholeRound : (↑DW : Int) = dWhole := by
    simpa [DW, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip dWhole hDWholeNonneg
  have hDIntEq : dWhole = dHigh + dLow := by
    have hArithmetic :
        kv + 1 + -iv =
          (kv + 1 + -(j1v + 1)) + (j1v + 1 + -iv) := by
      symm
      calc
        (kv + 1 + -(j1v + 1)) + (j1v + 1 + -iv) =
            (kv + 1) + (-(j1v + 1) + (j1v + 1)) + -iv := by
          ac_rfl
        _ = kv + 1 + -iv := by
          rw [Int.add_left_neg, Int.add_zero]
    simpa [dWhole, dHigh, dLow, SmtEval.native_zplus,
      SmtEval.native_zneg, hAdjacent] using hArithmetic
  have hWidthEq : DW = DH + DL := by
    have hCast : (↑DW : Int) = (↑(DH + DL) : Int) := by
      calc
        (↑DW : Int) = dWhole := hDWholeRound
        _ = dHigh + dLow := hDIntEq
        _ = (↑DH : Int) + (↑DL : Int) := by
          rw [hDHighRound, hDLowRound]
        _ = (↑(DH + DL) : Int) := by norm_cast
    exact_mod_cast hCast
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeHigh s (Term.Numeral kv)
              (Term.Numeral j2v))) = SmtType.BitVec DH := by
    simpa [bvConcatExtractMergeHigh, DH, dHigh] using
      smt_typeof_extract_of_context s w kv j2v hSSmtTy
        hw0 hj20 hkw hDHigh0
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLow s (Term.Numeral j1v)
              (Term.Numeral iv))) = SmtType.BitVec DL := by
    simpa [bvConcatExtractMergeLow, DL, dLow] using
      smt_typeof_extract_of_context s w j1v iv hSSmtTy
        hw0 hi0 hj1w hDLow0
  have hWholeSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeWhole s (Term.Numeral kv)
              (Term.Numeral iv))) = SmtType.BitVec DW := by
    simpa [bvConcatExtractMergeWhole, DW, dWhole] using
      smt_typeof_extract_of_context s w kv iv hSSmtTy
        hw0 hi0 hkw hDWhole0
  have hInnerSmtTy := bvConcat_term_smt_type
    (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys
    DL wys hLowSmtTy hYsSmtTy
  have hLeftSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv) ys)) =
        SmtType.BitVec (DH + (DL + wys)) := by
    simpa [bvConcatExtractMergeLeftSeed] using
      bvConcat_term_smt_type
        (bvConcatExtractMergeHigh s (Term.Numeral kv) (Term.Numeral j2v))
        (bvConcatTerm
          (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv))
          ys) DH (DL + wys) hHighSmtTy hInnerSmtTy
  have hInnerList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat)
    (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys
    (by intro h; cases h) hYsList
  have hLeftSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
            (Term.Numeral j1v) (Term.Numeral j2v)
            (Term.Numeral kv) ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatExtractMergeHigh s (Term.Numeral kv) (Term.Numeral j2v))
      (bvConcatTerm
        (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv)) ys)
      (by intro h; cases h) hInnerList
  have hRightSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
              (Term.Numeral kv) ys)) = SmtType.BitVec (DW + wys) := by
    simpa [bvConcatExtractMergeRightSeed] using
      bvConcat_term_smt_type
        (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv))
        ys DW wys hWholeSmtTy hYsSmtTy
  have hRightSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
            (Term.Numeral kv) ys) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv))
      ys (by intro h; cases h) hYsList
  have hRhsListSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
              (Term.Numeral kv))) =
        SmtType.BitVec (wxs + (DW + wys)) :=
    bvConcat_list_concat_smt_type xs
      (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
        (Term.Numeral kv) ys)
      wxs (DW + wys) hXsList hRightSeedList hXsSmtTy hRightSeedSmtTy
  have hRhsListList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
            (Term.Numeral kv)) = Term.Boolean true := by
    have hRecList := eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.concat) xs
      (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
        (Term.Numeral kv) ys) hXsList hRightSeedList
    simpa [bvConcatExtractMergeRhsList, __eo_list_concat,
      hXsList, hRightSeedList, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not] using hRecList
  have hCore := eval_bv_concat_extract_merge_core M hM s
    w kv j2v j1v iv hSSmtTy hw0 hj20 hkw hDHigh0 hi0 hDLow0
    hAdjacent
  have hAssoc := bvConcat_assoc_eval M hM
    (bvConcatExtractMergeHigh s (Term.Numeral kv) (Term.Numeral j2v))
    (bvConcatExtractMergeLow s (Term.Numeral j1v) (Term.Numeral iv))
    ys DH DL wys hHighSmtTy hLowSmtTy hYsSmtTy
  have hCoreWithYs :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatTerm
                (bvConcatExtractMergeHigh s (Term.Numeral kv)
                  (Term.Numeral j2v))
                (bvConcatExtractMergeLow s (Term.Numeral j1v)
                  (Term.Numeral iv))) ys)) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatExtractMergeWhole s (Term.Numeral kv)
                (Term.Numeral iv)) ys)) := by
    change __smtx_model_eval_concat
        (__smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatExtractMergeHigh s (Term.Numeral kv)
                (Term.Numeral j2v))
              (bvConcatExtractMergeLow s (Term.Numeral j1v)
                (Term.Numeral iv)))))
        (__smtx_model_eval M (__eo_to_smt ys)) =
      __smtx_model_eval_concat
        (__smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeWhole s (Term.Numeral kv)
              (Term.Numeral iv))))
        (__smtx_model_eval M (__eo_to_smt ys))
    rw [hCore]
  have hSeedEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv) ys)) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
              (Term.Numeral kv) ys)) := by
    simpa [bvConcatExtractMergeLeftSeed,
      bvConcatExtractMergeRightSeed] using hAssoc.trans hCoreWithYs
  have hPrefixLeft := bvConcat_list_concat_rec_eval_append M hM xs
    (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
      (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv) ys)
    (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv))
    ys wxs DW wys hXsList hXsSmtTy
    (by simpa [hWidthEq, Nat.add_assoc] using hLeftSeedSmtTy)
    hWholeSmtTy hYsSmtTy hSeedEval
  have hPrefixRight := bvConcat_list_concat_rec_eval_append M hM xs
    (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
      (Term.Numeral kv) ys)
    (bvConcatExtractMergeWhole s (Term.Numeral kv) (Term.Numeral iv))
    ys wxs DW wys hXsList hXsSmtTy hRightSeedSmtTy
    hWholeSmtTy hYsSmtTy rfl
  have hLhsTermEq :
      bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
          (Term.Numeral j1v) (Term.Numeral j2v) (Term.Numeral kv) =
        __eo_list_concat_rec xs
          (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
            (Term.Numeral j1v) (Term.Numeral j2v)
            (Term.Numeral kv) ys) := by
    simp [bvConcatExtractMergeLhs, __eo_list_concat, hXsList,
      hLeftSeedList, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not]
  have hRhsListTermEq :
      bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
          (Term.Numeral kv) =
        __eo_list_concat_rec xs
          (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
            (Term.Numeral kv) ys) := by
    simp [bvConcatExtractMergeRhsList, __eo_list_concat, hXsList,
      hRightSeedList, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not]
  have hSingletonEval := bvConcat_singleton_elim_eval_eq M hM
    (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
      (Term.Numeral kv))
    (wxs + (DW + wys)) hRhsListList hRhsListSmtTy
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
              (Term.Numeral j1v) (Term.Numeral j2v)
              (Term.Numeral kv))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
              (Term.Numeral kv))) := by
    calc
      _ = __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat_rec xs
              (bvConcatExtractMergeLeftSeed s (Term.Numeral iv)
                (Term.Numeral j1v) (Term.Numeral j2v)
                (Term.Numeral kv) ys))) := by rw [hLhsTermEq]
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (__eo_list_concat_rec xs
                (bvConcatExtractMergeWhole s (Term.Numeral kv)
                  (Term.Numeral iv))) ys)) := hPrefixLeft
      _ = __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat_rec xs
              (bvConcatExtractMergeRightSeed s (Term.Numeral iv)
                (Term.Numeral kv) ys))) := hPrefixRight.symm
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeRhsList xs s ys (Term.Numeral iv)
              (Term.Numeral kv))) := by rw [hRhsListTermEq]
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
              (Term.Numeral kv))) := hSingletonEval.symm
  rw [hProgEq] at hTyped ⊢
  have hBodyEq := bvConcatExtractMergeProgramBody_eq_term_of_type_bool
    xs s ys (Term.Numeral iv) (Term.Numeral j1v)
      (Term.Numeral j2v) (Term.Numeral kv) hBodyTy
  rw [hBodyEq] at hTyped ⊢
  unfold bvConcatExtractMergeTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvConcatExtractMergeTerm] using hTyped
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatExtractMergeLhs xs s ys (Term.Numeral iv)
            (Term.Numeral j1v) (Term.Numeral j2v)
            (Term.Numeral kv))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatExtractMergeRhs xs s ys (Term.Numeral iv)
            (Term.Numeral kv))))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _
