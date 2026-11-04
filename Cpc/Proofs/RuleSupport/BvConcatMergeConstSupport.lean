module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport
public import Cpc.Proofs.RuleSupport.Cong.Core
import all Cpc.Proofs.RuleSupport.Cong.Core

public section

/-! Support for merging adjacent integer bit-vector constants under concat. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvConcatMergeConstAt (w n : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n

def bvConcatMergeConstPremRaw
    (wwRef w1Ref w2Ref : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) wwRef)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) w1Ref)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) w2Ref)
        (Term.Numeral 0)))

def bvConcatMergeConstPrem (ww w1 w2 : Term) : Term :=
  bvConcatMergeConstPremRaw ww w1 w2

def bvConcatMergeConstMergedValue (n1 w2 n2 : Term) : Term :=
  let p2 := Term.Apply (Term.UOp UserOp.int_pow2) w2
  Term.Apply
    (Term.Apply (Term.UOp UserOp.plus)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n1)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) p2)
          (Term.Numeral 1))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) n2) p2))
      (Term.Numeral 0))

def bvConcatMergeConstLeftSeed
    (n1 w1 n2 w2 zs : Term) : Term :=
  bvConcatTerm (bvConcatMergeConstAt w1 n1)
    (bvConcatTerm (bvConcatMergeConstAt w2 n2) zs)

def bvConcatMergeConstRightSeed
    (n1 n2 w2 ww zs : Term) : Term :=
  bvConcatTerm
    (bvConcatMergeConstAt ww
      (bvConcatMergeConstMergedValue n1 w2 n2)) zs

def bvConcatMergeConstLhs
    (xs n1 w1 n2 w2 zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvConcatMergeConstLeftSeed n1 w1 n2 w2 zs)

def bvConcatMergeConstRhsList
    (xs n1 n2 w2 ww zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvConcatMergeConstRightSeed n1 n2 w2 ww zs)

def bvConcatMergeConstRhs
    (xs n1 n2 w2 ww zs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.concat)
    (bvConcatMergeConstRhsList xs n1 n2 w2 ww zs)

def bvConcatMergeConstTerm
    (xs n1 w1 n2 w2 ww zs : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvConcatMergeConstLhs xs n1 w1 n2 w2 zs))
    (bvConcatMergeConstRhs xs n1 n2 w2 ww zs)

def bvConcatMergeConstProgramBody
    (xs n1 w1 n2 w2 ww zs : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (bvConcatMergeConstLhs xs n1 w1 n2 w2 zs))
    (bvConcatMergeConstRhs xs n1 n2 w2 ww zs)

def bvConcatMergeConstProgram
    (xs n1 w1 n2 w2 ww zs P : Term) : Term :=
  __eo_prog_bv_concat_merge_const xs n1 w1 n2 w2 ww zs (Proof.pf P)

private theorem bv_concat_merge_const_and_true {a b : Term} :
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

private theorem bv_concat_merge_const_guard_refs
    {ww w1 w2 wwRef w1Ref w2Ref body : Term} :
    __eo_requires
        (__eo_and (__eo_and (__eo_eq ww wwRef) (__eo_eq w1 w1Ref))
          (__eo_eq w2 w2Ref))
        (Term.Boolean true) body ≠ Term.Stuck ->
    wwRef = ww ∧ w1Ref = w1 ∧ w2Ref = w2 := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  rcases bv_concat_merge_const_and_true hGuard with ⟨hLeft, hW2⟩
  rcases bv_concat_merge_const_and_true hLeft with ⟨hWw, hW1⟩
  exact ⟨support_eq_of_eo_eq_true ww wwRef hWw,
    support_eq_of_eo_eq_true w1 w1Ref hW1,
    support_eq_of_eo_eq_true w2 w2Ref hW2⟩

private theorem bv_concat_merge_const_premise_shape
    (xs n1 w1 n2 w2 ww zs P : Term) :
    xs ≠ Term.Stuck -> n1 ≠ Term.Stuck -> w1 ≠ Term.Stuck ->
    n2 ≠ Term.Stuck -> w2 ≠ Term.Stuck -> ww ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P ≠ Term.Stuck ->
    ∃ wwRef w1Ref w2Ref,
      P = bvConcatMergeConstPremRaw wwRef w1Ref w2Ref := by
  intro hXs hN1 hW1 hN2 hW2 hWw hZs hProg
  by_cases hShape : ∃ wwRef w1Ref w2Ref,
      P = bvConcatMergeConstPremRaw wwRef w1Ref w2Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_concat_merge_const.eq_9
      xs n1 w1 n2 w2 ww zs (Proof.pf P)
      hXs hN1 hW1 hN2 hW2 hWw hZs (by
        intro wwRef w1Ref w2Ref hP
        cases hP
        exact hShape ⟨wwRef, w1Ref, w2Ref, rfl⟩)

private theorem bv_concat_merge_const_program_canonical
    (xs n1 w1 n2 w2 ww zs : Term) :
    xs ≠ Term.Stuck -> n1 ≠ Term.Stuck -> w1 ≠ Term.Stuck ->
    n2 ≠ Term.Stuck -> w2 ≠ Term.Stuck -> ww ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs
        (bvConcatMergeConstPrem ww w1 w2) =
      bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs := by
  intro hXs hN1 hW1 hN2 hW2 hWw hZs
  unfold bvConcatMergeConstProgram bvConcatMergeConstPrem
    bvConcatMergeConstPremRaw
  rw [__eo_prog_bv_concat_merge_const.eq_8
    xs n1 w1 n2 w2 ww zs ww w1 w2
    hXs hN1 hW1 hN2 hW2 hWw hZs]
  simp [bvConcatMergeConstProgramBody, bvConcatMergeConstLhs,
    bvConcatMergeConstRhs, bvConcatMergeConstRhsList,
    bvConcatMergeConstLeftSeed, bvConcatMergeConstRightSeed,
    bvConcatMergeConstAt, bvConcatMergeConstMergedValue, bvConcatTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and,
    hXs, hN1, hW1, hN2, hW2, hWw, hZs]

theorem bvConcatMergeConstProgram_normalize
    (xs n1 w1 n2 w2 ww zs P : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation n1 ->
    RuleProofs.eo_has_smt_translation w1 ->
    RuleProofs.eo_has_smt_translation n2 ->
    RuleProofs.eo_has_smt_translation w2 ->
    RuleProofs.eo_has_smt_translation ww ->
    RuleProofs.eo_has_smt_translation zs ->
    bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P ≠ Term.Stuck ->
    P = bvConcatMergeConstPrem ww w1 w2 ∧
      bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P =
        bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs := by
  intro hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
    hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hN1 := RuleProofs.term_ne_stuck_of_has_smt_translation n1 hN1Trans
  have hW1 := RuleProofs.term_ne_stuck_of_has_smt_translation w1 hW1Trans
  have hN2 := RuleProofs.term_ne_stuck_of_has_smt_translation n2 hN2Trans
  have hW2 := RuleProofs.term_ne_stuck_of_has_smt_translation w2 hW2Trans
  have hWw := RuleProofs.term_ne_stuck_of_has_smt_translation ww hWwTrans
  have hZs := RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  rcases bv_concat_merge_const_premise_shape xs n1 w1 n2 w2 ww zs P
      hXs hN1 hW1 hN2 hW2 hWw hZs hProg with
    ⟨wwRef, w1Ref, w2Ref, hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvConcatMergeConstProgram bvConcatMergeConstPremRaw at hReq
  rw [__eo_prog_bv_concat_merge_const.eq_8
    xs n1 w1 n2 w2 ww zs wwRef w1Ref w2Ref
    hXs hN1 hW1 hN2 hW2 hWw hZs] at hReq
  rcases bv_concat_merge_const_guard_refs hReq with
    ⟨hWwRef, hW1Ref, hW2Ref⟩
  subst wwRef
  subst w1Ref
  subst w2Ref
  have hPCanon : P = bvConcatMergeConstPrem ww w1 w2 := by
    simpa [bvConcatMergeConstPrem] using hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_concat_merge_const_program_canonical
    xs n1 w1 n2 w2 ww zs hXs hN1 hW1 hN2 hW2 hWw hZs

private theorem bv_concat_merge_const_mk_apply_args_ne_stuck
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck -> f ≠ Term.Stuck ∧ x ≠ Term.Stuck := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem bv_concat_merge_const_mk_apply_eq
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

theorem bvConcatMergeConstProgramBody_eq_term_of_type_bool
    (xs n1 w1 n2 w2 ww zs : Term) :
    __eo_typeof
        (bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs) =
      Term.Bool ->
    bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs =
      bvConcatMergeConstTerm xs n1 w1 n2 w2 ww zs := by
  intro hTy
  let lhs := bvConcatMergeConstLhs xs n1 w1 n2 w2 zs
  let rhs := bvConcatMergeConstRhs xs n1 n2 w2 ww zs
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvConcatMergeConstProgramBody, lhs, rhs, eqHead] using hNe
  have hEqHeadNe :=
    (bv_concat_merge_const_mk_apply_args_ne_stuck hBodyNe).1
  have hOuter := bv_concat_merge_const_mk_apply_eq hBodyNe
  have hHead := bv_concat_merge_const_mk_apply_eq hEqHeadNe
  calc
    bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs =
        __eo_mk_apply eqHead rhs := by
      simp [bvConcatMergeConstProgramBody, lhs, rhs, eqHead]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs := by
      rw [hOuter]
      rw [show eqHead = Term.Apply (Term.UOp UserOp.eq) lhs by
        simpa [eqHead] using hHead]
    _ = bvConcatMergeConstTerm xs n1 w1 n2 w2 ww zs := by
      simp [bvConcatMergeConstTerm, lhs, rhs]

private theorem bv_concat_merge_const_body_args_ne_stuck
    (xs n1 w1 n2 w2 ww zs : Term) :
    __eo_typeof
        (bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs) =
      Term.Bool ->
    bvConcatMergeConstLhs xs n1 w1 n2 w2 zs ≠ Term.Stuck ∧
      bvConcatMergeConstRhs xs n1 n2 w2 ww zs ≠ Term.Stuck := by
  intro hTy
  let lhs := bvConcatMergeConstLhs xs n1 w1 n2 w2 zs
  let rhs := bvConcatMergeConstRhs xs n1 n2 w2 ww zs
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvConcatMergeConstProgramBody, lhs, rhs, eqHead] using hNe
  have hHeadNe :=
    (bv_concat_merge_const_mk_apply_args_ne_stuck hBodyNe).1
  exact ⟨(bv_concat_merge_const_mk_apply_args_ne_stuck hHeadNe).2,
    (bv_concat_merge_const_mk_apply_args_ne_stuck hBodyNe).2⟩

private theorem bv_concat_merge_const_singleton_list_of_ne_stuck
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

private theorem bv_concat_merge_const_list_rec_right_type_ne
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

private theorem bv_concat_merge_const_list_right_type_ne
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
  exact bv_concat_merge_const_list_rec_right_type_ne a z hAList hRecTy

private theorem bv_concat_merge_const_int_to_bv_context
    (w n width : Term) :
    w ≠ Term.Stuck -> n ≠ Term.Stuck ->
    __eo_typeof (bvConcatMergeConstAt w n) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ width = Term.Numeral W ∧
      native_zleq 0 W = true ∧
      __eo_typeof n = Term.UOp UserOp.Int := by
  intro hWNe hNNe hTy
  change __eo_typeof_int_to_bv (__eo_typeof w) w (__eo_typeof n) =
    Term.Apply (Term.UOp UserOp.BitVec) width at hTy
  have hNTy : __eo_typeof n = Term.UOp UserOp.Int := by
    cases hn : __eo_typeof n <;>
      simp [__eo_typeof_int_to_bv, hn, hWNe] at hTy ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_int_to_bv, hn, hWNe] at hTy ⊢
  have hWTy : __eo_typeof w = Term.UOp UserOp.Int := by
    cases hw : __eo_typeof w <;>
      simp [__eo_typeof_int_to_bv, hNTy, hw, hWNe] at hTy ⊢
    case UOp op =>
      cases op <;>
        simp [__eo_typeof_int_to_bv, hNTy, hw, hWNe] at hTy ⊢
  have hReqTy :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    simpa [__eo_typeof_int_to_bv, hNTy, hWTy, hWNe] using hTy
  have hReqNe :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReqTy]
    intro h
    cases h
  have hGuard : __eo_gt w (Term.Numeral (-1 : native_Int)) =
      Term.Boolean true := support_eo_requires_cond_eq_of_non_stuck hReqNe
  have hReqEq :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    simp [__eo_requires, hGuard, native_ite, native_teq, native_not]
  rw [hReqEq] at hReqTy
  have hWidth : width = w := by
    injection hReqTy with _ h
    exact h.symm
  cases w <;> simp [__eo_gt] at hGuard
  case Numeral W =>
    have hW0 : native_zleq 0 W = true := by
      have hsimpa := hGuard
      try simp [SmtEval.native_zlt, SmtEval.native_zleq] at hsimpa ⊢
      exact hsimpa
    exact ⟨W, rfl, hWidth, hW0, hNTy⟩

private theorem int_pow2_add_nat (w1 w2 : Nat) :
    native_int_pow2 (native_nat_to_int (w1 + w2)) =
      native_int_pow2 (native_nat_to_int w1) *
        native_int_pow2 (native_nat_to_int w2) := by
  have h1 := natpow2_eq w1
  have h2 := natpow2_eq w2
  have h12 := natpow2_eq (w1 + w2)
  have hsimpa :=
    h12.trans (Int.pow_add 2 w1 w2)
  try simp [native_nat_to_int, SmtEval.native_nat_to_int, Int.pow_add] at hsimpa ⊢
  exact hsimpa

private theorem int_mod_mul_pow2_congr
    (p : Int) (w1 w2 : Nat) :
    ((p % native_int_pow2 (native_nat_to_int w1)) *
          native_int_pow2 (native_nat_to_int w2)) %
        native_int_pow2 (native_nat_to_int (w1 + w2)) =
      (p * native_int_pow2 (native_nat_to_int w2)) %
        native_int_pow2 (native_nat_to_int (w1 + w2)) := by
  let a := native_int_pow2 (native_nat_to_int w1)
  let b := native_int_pow2 (native_nat_to_int w2)
  have hPow : native_int_pow2 (native_nat_to_int (w1 + w2)) = a * b := by
    simpa [a, b] using int_pow2_add_nat w1 w2
  let q := p / a
  let r := p % a
  have hDivMod : a * q + r = p := by
    simpa [q, r] using Int.mul_ediv_add_emod p a
  have hDistrib : (a * q + r) * b = (a * b) * q + r * b := by
    rw [Int.add_mul]
    congr 1
    ac_rfl
  rw [hPow]
  calc
    (p % a * b) % (a * b) = (r * b) % (a * b) := by rfl
    _ = ((a * b) * q + r * b) % (a * b) := by
      rw [Int.add_emod]
      simp [Int.mul_emod_right]
    _ = ((a * q + r) * b) % (a * b) := by rw [hDistrib]
    _ = (p * b) % (a * b) := by rw [hDivMod]

private theorem int_concat_merge_payload
    (p q : Int) (w1 w2 : Nat) :
    native_mod_total
        (native_binary_concat (native_nat_to_int w1)
          (native_mod_total p
            (native_int_pow2 (native_nat_to_int w1)))
          (native_nat_to_int w2)
          (native_mod_total q
            (native_int_pow2 (native_nat_to_int w2))))
        (native_int_pow2 (native_nat_to_int (w1 + w2))) =
      native_mod_total
        (p * native_int_pow2 (native_nat_to_int w2) +
          native_mod_total q
            (native_int_pow2 (native_nat_to_int w2)))
        (native_int_pow2 (native_nat_to_int (w1 + w2))) := by
  have hPow := int_pow2_add_nat w1 w2
  have hAOne : (1 : Int) ≤
      native_int_pow2 (native_nat_to_int w1) := by
    have h := natpow2_eq w1
    rw [show native_int_pow2 (native_nat_to_int w1) = (2 : Int) ^ w1 by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using h]
    exact_mod_cast Nat.one_le_two_pow
  have hBPos : (0 : Int) <
      native_int_pow2 (native_nat_to_int w2) := by
    have h := natpow2_eq w2
    rw [show native_int_pow2 (native_nat_to_int w2) = (2 : Int) ^ w2 by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using h]
    exact_mod_cast Nat.two_pow_pos w2
  have hABPos : (0 : Int) <
      native_int_pow2 (native_nat_to_int (w1 + w2)) := by
    have h := natpow2_eq (w1 + w2)
    rw [show native_int_pow2 (native_nat_to_int (w1 + w2)) =
        (2 : Int) ^ (w1 + w2) by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using h]
    exact_mod_cast Nat.two_pow_pos (w1 + w2)
  have hBLe : native_int_pow2 (native_nat_to_int w2) ≤
      native_int_pow2 (native_nat_to_int (w1 + w2)) := by
    rw [hPow]
    calc
      native_int_pow2 (native_nat_to_int w2) =
          1 * native_int_pow2 (native_nat_to_int w2) := by simp
      _ ≤ native_int_pow2 (native_nat_to_int w1) *
          native_int_pow2 (native_nat_to_int w2) :=
        Int.mul_le_mul_of_nonneg_right hAOne (Int.le_of_lt hBPos)
  have hLow0 : 0 ≤ q % native_int_pow2 (native_nat_to_int w2) :=
    Int.emod_nonneg q (Int.ne_of_gt hBPos)
  have hLowLt : q % native_int_pow2 (native_nat_to_int w2) <
      native_int_pow2 (native_nat_to_int (w1 + w2)) :=
    Int.lt_of_lt_of_le (Int.emod_lt_of_pos q hBPos) hBLe
  have hLowMod :
      (q % native_int_pow2 (native_nat_to_int w2)) %
          native_int_pow2 (native_nat_to_int (w1 + w2)) =
        q % native_int_pow2 (native_nat_to_int w2) :=
    Int.emod_eq_of_lt hLow0 hLowLt
  simp only [native_mod_total, native_binary_concat, native_zmult,
    SmtEval.native_zplus]
  rw [Int.add_emod, Int.add_emod,
    int_mod_mul_pow2_congr p w1 w2]
  simp [Int.emod_emod, hLowMod]

theorem bvConcat_int_to_bv_merge_eval
    (M : SmtModel) (n1 n2 : Term) (w1 w2 : Nat) (p q : Int) :
    __smtx_model_eval M (__eo_to_smt n1) = SmtValue.Numeral p ->
    __smtx_model_eval M (__eo_to_smt n2) = SmtValue.Numeral q ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm
            (Term.Apply
              (Term.UOp1 UserOp1.int_to_bv
                (Term.Numeral (native_nat_to_int w1))) n1)
            (Term.Apply
              (Term.UOp1 UserOp1.int_to_bv
                (Term.Numeral (native_nat_to_int w2))) n2))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.UOp1 UserOp1.int_to_bv
              (Term.Numeral (native_nat_to_int (w1 + w2))))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.plus)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.mult) n1)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.mult)
                      (Term.Apply (Term.UOp UserOp.int_pow2)
                        (Term.Numeral (native_nat_to_int w2))))
                    (Term.Numeral 1))))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.plus)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.mod) n2)
                    (Term.Apply (Term.UOp UserOp.int_pow2)
                      (Term.Numeral (native_nat_to_int w2)))))
                (Term.Numeral 0))))) := by
  intro hn1 hn2
  unfold bvConcatTerm
  change __smtx_model_eval M
      (SmtTerm.concat
        (SmtTerm.int_to_bv
          (SmtTerm.Numeral (native_nat_to_int w1)) (__eo_to_smt n1))
        (SmtTerm.int_to_bv
          (SmtTerm.Numeral (native_nat_to_int w2)) (__eo_to_smt n2))) =
    __smtx_model_eval M
      (SmtTerm.int_to_bv
        (SmtTerm.Numeral (native_nat_to_int (w1 + w2)))
        (SmtTerm.plus
          (SmtTerm.mult (__eo_to_smt n1)
            (SmtTerm.mult
              (SmtTerm.int_pow2
                (SmtTerm.Numeral (native_nat_to_int w2)))
              (SmtTerm.Numeral 1)))
          (SmtTerm.plus
            (SmtTerm.mod (__eo_to_smt n2)
              (SmtTerm.int_pow2
                (SmtTerm.Numeral (native_nat_to_int w2))))
            (SmtTerm.Numeral 0))))
  simp only [__smtx_model_eval, hn1, hn2,
    __smtx_model_eval_int_to_bv, __smtx_model_eval_concat,
    __smtx_model_eval_mult, __smtx_model_eval_int_pow2,
    __smtx_model_eval_plus,
    SmtEval.native_zmult, SmtEval.native_zplus]
  rw [show native_nat_to_int w1 + native_nat_to_int w2 =
      native_nat_to_int (w1 + w2) by
        simp [native_nat_to_int, SmtEval.native_nat_to_int,
          SmtEval.native_zplus]]
  have hPow2Pos : (0 : Int) <
      native_int_pow2 (native_nat_to_int w2) := by
    have h := natpow2_eq w2
    rw [show native_int_pow2 (native_nat_to_int w2) = (2 : Int) ^ w2 by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using h]
    exact_mod_cast Nat.two_pow_pos w2
  have hPow2Ne : native_int_pow2 (native_nat_to_int w2) ≠ 0 :=
    Int.ne_of_gt hPow2Pos
  simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
    __smtx_model_eval_mod_total, native_veq, SmtEval.native_zeq,
    native_ite, hPow2Ne]
  exact int_concat_merge_payload p q w1 w2

private theorem bv_concat_merge_const_lhs_context
    (xs n1 w1 n2 w2 ww zs : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation n1 ->
    RuleProofs.eo_has_smt_translation w1 ->
    RuleProofs.eo_has_smt_translation n2 ->
    RuleProofs.eo_has_smt_translation w2 ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof
        (bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs) =
      Term.Bool ->
    ∃ W1 W2 : native_Int, ∃ wxs wzs : Nat,
      w1 = Term.Numeral W1 ∧ w2 = Term.Numeral W2 ∧
      native_zleq 0 W1 = true ∧ native_zleq 0 W2 = true ∧
      __smtx_typeof (__eo_to_smt n1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt n2) = SmtType.Int ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) zs = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec wzs := by
  intro hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hZsTrans hBodyTy
  have hBodyEq := bvConcatMergeConstProgramBody_eq_term_of_type_bool
    xs n1 w1 n2 w2 ww zs hBodyTy
  have hTermTy :
      __eo_typeof (bvConcatMergeConstTerm xs n1 w1 n2 w2 ww zs) =
        Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hLhsTyNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvConcatMergeConstLhs xs n1 w1 n2 w2 zs))
      (__eo_typeof (bvConcatMergeConstRhs xs n1 n2 w2 ww zs))
      (by have hsimpa := hTermTy; (try simp [bvConcatMergeConstTerm] at hsimpa ⊢); exact hsimpa)).1
  have hLhsTermNe :=
    (bv_concat_merge_const_body_args_ne_stuck
      xs n1 w1 n2 w2 ww zs hBodyTy).1
  rcases bvConcat_list_concat_lists_of_ne_stuck xs
      (bvConcatMergeConstLeftSeed n1 w1 n2 w2 zs)
      (by simpa [bvConcatMergeConstLhs] using hLhsTermNe) with
    ⟨hXsList, hLeftSeedList⟩
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatTerm (bvConcatMergeConstAt w2 n2) zs) =
        Term.Boolean true := by
    exact eo_is_list_tail_true_of_cons_self
      (Term.UOp UserOp.concat) (bvConcatMergeConstAt w1 n1)
      (bvConcatTerm (bvConcatMergeConstAt w2 n2) zs)
      (by have hsimpa := hLeftSeedList; (try simp [bvConcatMergeConstLeftSeed] at hsimpa ⊢); exact hsimpa)
  have hZsList :
      __eo_is_list (Term.UOp UserOp.concat) zs = Term.Boolean true := by
    exact eo_is_list_tail_true_of_cons_self
      (Term.UOp UserOp.concat) (bvConcatMergeConstAt w2 n2) zs
      (by have hsimpa := hInnerList; (try simp at hsimpa ⊢); exact hsimpa)
  have hLeftSeedTyNe :
      __eo_typeof (bvConcatMergeConstLeftSeed n1 w1 n2 w2 zs) ≠
        Term.Stuck :=
    bv_concat_merge_const_list_right_type_ne xs
      (bvConcatMergeConstLeftSeed n1 w1 n2 w2 zs)
      hXsList hLeftSeedList
      (by simpa [bvConcatMergeConstLhs] using hLhsTyNe)
  change __eo_typeof_concat (__eo_typeof (bvConcatMergeConstAt w1 n1))
      (__eo_typeof (bvConcatTerm (bvConcatMergeConstAt w2 n2) zs)) ≠
        Term.Stuck at hLeftSeedTyNe
  rcases bvConcat_eo_typeof_concat_args_bitvec hLeftSeedTyNe with
    ⟨width1, widthTail, hAt1Ty, hTailTy⟩
  have hTailTyNe :
      __eo_typeof (bvConcatTerm (bvConcatMergeConstAt w2 n2) zs) ≠
        Term.Stuck := by
    rw [hTailTy]
    intro h
    cases h
  change __eo_typeof_concat (__eo_typeof (bvConcatMergeConstAt w2 n2))
      (__eo_typeof zs) ≠ Term.Stuck at hTailTyNe
  rcases bvConcat_eo_typeof_concat_args_bitvec hTailTyNe with
    ⟨width2, widthZs, hAt2Ty, _hZsEoTy⟩
  have hW1Ne := RuleProofs.term_ne_stuck_of_has_smt_translation w1 hW1Trans
  have hN1Ne := RuleProofs.term_ne_stuck_of_has_smt_translation n1 hN1Trans
  have hW2Ne := RuleProofs.term_ne_stuck_of_has_smt_translation w2 hW2Trans
  have hN2Ne := RuleProofs.term_ne_stuck_of_has_smt_translation n2 hN2Trans
  rcases bv_concat_merge_const_int_to_bv_context w1 n1 width1
      hW1Ne hN1Ne hAt1Ty with
    ⟨W1, hW1, _hWidth1, hW10, hN1EoTy⟩
  rcases bv_concat_merge_const_int_to_bv_context w2 n2 width2
      hW2Ne hN2Ne hAt2Ty with
    ⟨W2, hW2, _hWidth2, hW20, hN2EoTy⟩
  have hN1SmtTy : __smtx_typeof (__eo_to_smt n1) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n1 (Term.UOp UserOp.Int) (__eo_to_smt n1) rfl hN1Trans hN1EoTy
  have hN2SmtTy : __smtx_typeof (__eo_to_smt n2) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n2 (Term.UOp UserOp.Int) (__eo_to_smt n2) rfl hN2Trans hN2EoTy
  rcases bvConcat_list_smt_type_of_translation xs hXsList hXsTrans with
    ⟨wxs, hXsSmtTy⟩
  rcases bvConcat_list_smt_type_of_translation zs hZsList hZsTrans with
    ⟨wzs, hZsSmtTy⟩
  exact ⟨W1, W2, wxs, wzs, hW1, hW2, hW10, hW20,
    hN1SmtTy, hN2SmtTy, hXsList, hZsList, hXsSmtTy, hZsSmtTy⟩

private theorem bv_concat_merge_const_body_context
    (xs n1 w1 n2 w2 ww zs : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation n1 ->
    RuleProofs.eo_has_smt_translation w1 ->
    RuleProofs.eo_has_smt_translation n2 ->
    RuleProofs.eo_has_smt_translation w2 ->
    RuleProofs.eo_has_smt_translation ww ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof
        (bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs) =
      Term.Bool ->
    ∃ W1 W2 WW : native_Int, ∃ wxs wzs : Nat,
      w1 = Term.Numeral W1 ∧ w2 = Term.Numeral W2 ∧
      ww = Term.Numeral WW ∧
      native_zleq 0 W1 = true ∧ native_zleq 0 W2 = true ∧
      native_zleq 0 WW = true ∧
      __smtx_typeof (__eo_to_smt n1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt n2) = SmtType.Int ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) zs = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec wzs := by
  intro hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
    hBodyTy
  rcases bv_concat_merge_const_lhs_context xs n1 w1 n2 w2 ww zs
      hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hZsTrans hBodyTy with
    ⟨W1, W2, wxs, wzs, hW1, hW2, hW10, hW20, hN1SmtTy,
      hN2SmtTy, hXsList, hZsList, hXsSmtTy, hZsSmtTy⟩
  have hAt1SmtTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatMergeConstAt (Term.Numeral W1) n1)) =
        SmtType.BitVec (native_int_to_nat W1) := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W1) (__eo_to_smt n1)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hN1SmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW10]
  have hAt2SmtTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatMergeConstAt (Term.Numeral W2) n2)) =
        SmtType.BitVec (native_int_to_nat W2) := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W2) (__eo_to_smt n2)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hN2SmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW20]
  have hInnerSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)) =
        SmtType.BitVec (native_int_to_nat W2 + wzs) :=
    bvConcat_term_smt_type _ _ _ _ hAt2SmtTy hZsSmtTy
  have hLeftSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        SmtType.BitVec
          (native_int_to_nat W1 + (native_int_to_nat W2 + wzs)) := by
    simpa [bvConcatMergeConstLeftSeed] using
      bvConcat_term_smt_type
        (bvConcatMergeConstAt (Term.Numeral W1) n1)
        (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)
        (native_int_to_nat W1) (native_int_to_nat W2 + wzs)
        hAt1SmtTy hInnerSmtTy
  have hLeftSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
            n2 (Term.Numeral W2) zs) = Term.Boolean true := by
    have hInnerList := eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatMergeConstAt (Term.Numeral W2) n2) zs
      (by intro h; cases h) hZsList
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatMergeConstAt (Term.Numeral W1) n1)
      (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)
      (by intro h; cases h) hInnerList
  have hLhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        SmtType.BitVec
          (wxs + (native_int_to_nat W1 +
            (native_int_to_nat W2 + wzs))) := by
    simpa [bvConcatMergeConstLhs] using
      bvConcat_list_concat_smt_type xs
        (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
          n2 (Term.Numeral W2) zs)
        wxs (native_int_to_nat W1 + (native_int_to_nat W2 + wzs))
        hXsList hLeftSeedList hXsSmtTy hLeftSeedSmtTy
  have hBodyEq := bvConcatMergeConstProgramBody_eq_term_of_type_bool
    xs n1 w1 n2 w2 ww zs hBodyTy
  have hTermTy :
      __eo_typeof (bvConcatMergeConstTerm xs n1 w1 n2 w2 ww zs) =
        Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hTypeEq :
      __eo_typeof (bvConcatMergeConstLhs xs n1 w1 n2 w2 zs) =
        __eo_typeof (bvConcatMergeConstRhs xs n1 n2 w2 ww zs) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _
      (by have hsimpa := hTermTy; (try simp [bvConcatMergeConstTerm] at hsimpa ⊢); exact hsimpa)
  have hLhsTrans : RuleProofs.eo_has_smt_translation
      (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
        n2 (Term.Numeral W2) zs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsSmtTy]
    intro h
    cases h
  have hLhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
        n2 (Term.Numeral W2) zs)
      (__eo_typeof
        (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
          n2 (Term.Numeral W2) zs))
      (__eo_to_smt
        (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
          n2 (Term.Numeral W2) zs)) rfl hLhsTrans rfl
  have hLhsEoTy :=
    TranslationProofs.eo_typeof_eq_bitvec_of_smt_bitvec_from_ih
      (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
        n2 (Term.Numeral W2) zs)
      (fun _ => hLhsBridge)
      (wxs + (native_int_to_nat W1 + (native_int_to_nat W2 + wzs)))
      hLhsSmtTy
  have hRhsEoTy :
      __eo_typeof
          (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2) ww zs) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_nat_to_int
              (wxs + (native_int_to_nat W1 +
                (native_int_to_nat W2 + wzs))))) := by
    have hTypeEq' :
        __eo_typeof
            (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs) =
          __eo_typeof
            (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2) ww zs) := by
      simpa [hW1, hW2] using hTypeEq
    rw [← hTypeEq']
    exact hLhsEoTy
  have hRhsTermNe :=
    (bv_concat_merge_const_body_args_ne_stuck
      xs n1 w1 n2 w2 ww zs hBodyTy).2
  have hRhsListList :=
    bv_concat_merge_const_singleton_list_of_ne_stuck
      (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2) ww zs)
      (by simpa [hW2, bvConcatMergeConstRhs] using hRhsTermNe)
  have hRhsListEoTy :=
    bvConcat_singleton_elim_eo_type_inv
      (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2) ww zs)
      (wxs + (native_int_to_nat W1 + (native_int_to_nat W2 + wzs)))
      hRhsListList (by simpa [bvConcatMergeConstRhs] using hRhsEoTy)
  have hRhsListTermNe :
      bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2) ww zs ≠
        Term.Stuck := by
    intro h
    rw [h] at hRhsListEoTy
    change Term.Stuck = _ at hRhsListEoTy
    cases hRhsListEoTy
  rcases bvConcat_list_concat_lists_of_ne_stuck xs
      (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2) ww zs)
      (by simpa [bvConcatMergeConstRhsList] using hRhsListTermNe) with
    ⟨_hXsListRhs, hRightSeedList⟩
  rcases bvConcat_eo_typeof_list_concat_right_bitvec xs
      (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2) ww zs)
      (Term.Numeral
        (native_nat_to_int
          (wxs + (native_int_to_nat W1 + (native_int_to_nat W2 + wzs)))))
      hXsList hRightSeedList
      (by simpa [bvConcatMergeConstRhsList] using hRhsListEoTy) with
    ⟨widthRight, hRightSeedEoTy⟩
  have hRightSeedTyNe :
      __eo_typeof
          (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2) ww zs) ≠
        Term.Stuck := by
    rw [hRightSeedEoTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof
        (bvConcatMergeConstAt ww
          (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2)))
      (__eo_typeof zs) ≠ Term.Stuck at hRightSeedTyNe
  rcases bvConcat_eo_typeof_concat_args_bitvec hRightSeedTyNe with
    ⟨widthMerged, widthZs, hMergedAtEoTy, _hZsEoTy⟩
  have hWwNe := RuleProofs.term_ne_stuck_of_has_smt_translation ww hWwTrans
  have hMergedNe :
      bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2 ≠
        Term.Stuck := by
    intro h
    rw [h] at hMergedAtEoTy
    unfold bvConcatMergeConstAt at hMergedAtEoTy
    change __eo_typeof_int_to_bv (__eo_typeof ww) ww
        (__eo_typeof Term.Stuck) = _ at hMergedAtEoTy
    rw [show __eo_typeof Term.Stuck = Term.Stuck by rfl] at hMergedAtEoTy
    cases hw : __eo_typeof ww <;>
      simp [__eo_typeof_int_to_bv, hw] at hMergedAtEoTy
  rcases bv_concat_merge_const_int_to_bv_context ww
      (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2)
      widthMerged hWwNe hMergedNe hMergedAtEoTy with
    ⟨WW, hWw, _hWidthMerged, hWW0, _hMergedEoTy⟩
  exact ⟨W1, W2, WW, wxs, wzs, hW1, hW2, hWw,
    hW10, hW20, hWW0, hN1SmtTy, hN2SmtTy, hXsList, hZsList,
    hXsSmtTy, hZsSmtTy⟩

private theorem bv_concat_merge_const_merged_smt_type
    (n1 n2 : Term) (W2 : native_Int) :
    __smtx_typeof (__eo_to_smt n1) = SmtType.Int ->
    __smtx_typeof (__eo_to_smt n2) = SmtType.Int ->
    __smtx_typeof
        (__eo_to_smt
          (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2)) =
      SmtType.Int := by
  intro hN1Ty hN2Ty
  change __smtx_typeof
      (SmtTerm.plus
        (SmtTerm.mult (__eo_to_smt n1)
          (SmtTerm.mult
            (SmtTerm.int_pow2 (SmtTerm.Numeral W2))
            (SmtTerm.Numeral 1)))
        (SmtTerm.plus
          (SmtTerm.mod (__eo_to_smt n2)
            (SmtTerm.int_pow2 (SmtTerm.Numeral W2)))
          (SmtTerm.Numeral 0))) = SmtType.Int
  rw [typeof_plus_eq, typeof_mult_eq, typeof_mult_eq,
    typeof_int_pow2_eq, typeof_plus_eq, typeof_mod_eq,
    typeof_int_pow2_eq, hN1Ty, hN2Ty]
  simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2,
    native_ite, native_Teq]

private theorem model_eval_eq_true_of_eo_eq_true_concat_merge
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

private theorem bv_concat_merge_const_premise_width_eq
    (M : SmtModel) (W1 W2 WW : native_Int) :
    eo_interprets M
        (bvConcatMergeConstPrem (Term.Numeral WW)
          (Term.Numeral W1) (Term.Numeral W2)) true ->
    WW = W1 + W2 := by
  intro hPrem
  have hEq := model_eval_eq_true_of_eo_eq_true_concat_merge M
    (Term.Numeral WW)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral W1))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral W2))
        (Term.Numeral 0)))
    (by simpa [bvConcatMergeConstPrem, bvConcatMergeConstPremRaw] using hPrem)
  have hRightEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
                (Term.Numeral W1))
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
                  (Term.Numeral W2)) (Term.Numeral 0)))) =
        SmtValue.Numeral (W1 + W2) := by
    change __smtx_model_eval M
      (SmtTerm.plus (SmtTerm.Numeral W1)
        (SmtTerm.plus (SmtTerm.Numeral W2) (SmtTerm.Numeral 0))) = _
    simp [__smtx_model_eval, __smtx_model_eval_plus,
      SmtEval.native_zplus]
  rw [hRightEval] at hEq
  change __smtx_model_eval_eq (SmtValue.Numeral WW)
      (SmtValue.Numeral (W1 + W2)) = SmtValue.Boolean true at hEq
  simpa [__smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] using hEq

theorem typed_bv_concat_merge_const_program
    (xs n1 w1 n2 w2 ww zs P : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation n1 ->
    RuleProofs.eo_has_smt_translation w1 ->
    RuleProofs.eo_has_smt_translation n2 ->
    RuleProofs.eo_has_smt_translation w2 ->
    RuleProofs.eo_has_smt_translation ww ->
    RuleProofs.eo_has_smt_translation zs ->
    bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P ≠ Term.Stuck ->
    __eo_typeof (bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P) := by
  intro hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
    hProgNe hProgTy
  rcases bvConcatMergeConstProgram_normalize xs n1 w1 n2 w2 ww zs P
      hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
      hProgNe with ⟨_hP, hProgEq⟩
  have hBodyTy :
      __eo_typeof
          (bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs) =
        Term.Bool := by
    rw [← hProgEq]
    exact hProgTy
  rcases bv_concat_merge_const_body_context xs n1 w1 n2 w2 ww zs
      hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
      hBodyTy with
    ⟨W1, W2, WW, wxs, wzs, rfl, rfl, rfl, hW10, hW20, hWW0,
      hN1SmtTy, hN2SmtTy, hXsList, hZsList, hXsSmtTy, hZsSmtTy⟩
  have hAt1SmtTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatMergeConstAt (Term.Numeral W1) n1)) =
        SmtType.BitVec (native_int_to_nat W1) := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W1) (__eo_to_smt n1)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hN1SmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW10]
  have hAt2SmtTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatMergeConstAt (Term.Numeral W2) n2)) =
        SmtType.BitVec (native_int_to_nat W2) := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W2) (__eo_to_smt n2)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hN2SmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW20]
  have hInnerSmtTy := bvConcat_term_smt_type
    (bvConcatMergeConstAt (Term.Numeral W2) n2) zs
    (native_int_to_nat W2) wzs hAt2SmtTy hZsSmtTy
  have hLeftSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        SmtType.BitVec
          (native_int_to_nat W1 + (native_int_to_nat W2 + wzs)) := by
    simpa [bvConcatMergeConstLeftSeed] using
      bvConcat_term_smt_type
        (bvConcatMergeConstAt (Term.Numeral W1) n1)
        (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)
        (native_int_to_nat W1) (native_int_to_nat W2 + wzs)
        hAt1SmtTy hInnerSmtTy
  have hInnerList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat)
    (bvConcatMergeConstAt (Term.Numeral W2) n2) zs
    (by intro h; cases h) hZsList
  have hLeftSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
            n2 (Term.Numeral W2) zs) = Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatMergeConstAt (Term.Numeral W1) n1)
      (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)
      (by intro h; cases h) hInnerList
  have hLhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        SmtType.BitVec
          (wxs + (native_int_to_nat W1 +
            (native_int_to_nat W2 + wzs))) := by
    exact bvConcat_list_concat_smt_type xs
      (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
        n2 (Term.Numeral W2) zs)
      wxs (native_int_to_nat W1 + (native_int_to_nat W2 + wzs))
      hXsList hLeftSeedList hXsSmtTy hLeftSeedSmtTy
  have hMergedSmtTy := bv_concat_merge_const_merged_smt_type
    n1 n2 W2 hN1SmtTy hN2SmtTy
  have hMergedAtSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstAt (Term.Numeral WW)
              (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))) =
        SmtType.BitVec (native_int_to_nat WW) := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral WW)
        (__eo_to_smt
          (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))) = _
    rw [smtx_typeof_int_to_bv_term_eq, hMergedSmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hWW0]
  have hRightSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
              (Term.Numeral WW) zs)) =
        SmtType.BitVec (native_int_to_nat WW + wzs) := by
    simpa [bvConcatMergeConstRightSeed] using
      bvConcat_term_smt_type
        (bvConcatMergeConstAt (Term.Numeral WW)
          (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
        zs (native_int_to_nat WW) wzs hMergedAtSmtTy hZsSmtTy
  have hRightSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
            (Term.Numeral WW) zs) = Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatMergeConstAt (Term.Numeral WW)
        (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
      zs (by intro h; cases h) hZsList
  have hRhsListSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
              (Term.Numeral WW) zs)) =
        SmtType.BitVec (wxs + (native_int_to_nat WW + wzs)) := by
    exact bvConcat_list_concat_smt_type xs
      (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
        (Term.Numeral WW) zs)
      wxs (native_int_to_nat WW + wzs) hXsList hRightSeedList
      hXsSmtTy hRightSeedSmtTy
  have hRhsListList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
            (Term.Numeral WW) zs) = Term.Boolean true := by
    have hRecList := eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.concat) xs
      (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
        (Term.Numeral WW) zs)
      hXsList hRightSeedList
    simpa [bvConcatMergeConstRhsList, __eo_list_concat,
      hXsList, hRightSeedList, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not] using hRecList
  have hRhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2)
              (Term.Numeral WW) zs)) =
        SmtType.BitVec (wxs + (native_int_to_nat WW + wzs)) := by
    exact bvConcat_singleton_elim_smt_type
      (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
        (Term.Numeral WW) zs)
      (wxs + (native_int_to_nat WW + wzs)) hRhsListList hRhsListSmtTy
  have hBodyEq := bvConcatMergeConstProgramBody_eq_term_of_type_bool
    xs n1 (Term.Numeral W1) n2 (Term.Numeral W2)
      (Term.Numeral WW) zs hBodyTy
  have hTermTy :
      __eo_typeof
          (bvConcatMergeConstTerm xs n1 (Term.Numeral W1) n2
            (Term.Numeral W2) (Term.Numeral WW) zs) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hEOTypeEq :
      __eo_typeof
          (bvConcatMergeConstLhs xs n1 (Term.Numeral W1) n2
            (Term.Numeral W2) zs) =
        __eo_typeof
          (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2)
            (Term.Numeral WW) zs) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _
      (by have hsimpa := hTermTy; (try simp [bvConcatMergeConstTerm] at hsimpa ⊢); exact hsimpa)
  have hLhsTrans : RuleProofs.eo_has_smt_translation
      (bvConcatMergeConstLhs xs n1 (Term.Numeral W1) n2
        (Term.Numeral W2) zs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsSmtTy]
    intro h
    cases h
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2)
        (Term.Numeral WW) zs) := by
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
      (bvConcatMergeConstTerm xs n1 (Term.Numeral W1) n2
        (Term.Numeral W2) (Term.Numeral WW) zs) := by
    unfold bvConcatMergeConstTerm
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
      (by rw [hLhsSmtTy]; intro h; cases h)
  rw [hProgEq]
  simpa [hBodyEq] using hTermBool

theorem facts_bv_concat_merge_const_program
    (M : SmtModel) (hM : model_wf M)
    (xs n1 w1 n2 w2 ww zs P : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation n1 ->
    RuleProofs.eo_has_smt_translation w1 ->
    RuleProofs.eo_has_smt_translation n2 ->
    RuleProofs.eo_has_smt_translation w2 ->
    RuleProofs.eo_has_smt_translation ww ->
    RuleProofs.eo_has_smt_translation zs ->
    bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P ≠ Term.Stuck ->
    __eo_typeof (bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P) =
      Term.Bool ->
    eo_interprets M P true ->
    eo_interprets M
      (bvConcatMergeConstProgram xs n1 w1 n2 w2 ww zs P) true := by
  intro hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
    hProgNe hProgTy hPremTrue
  have hTyped := typed_bv_concat_merge_const_program
    xs n1 w1 n2 w2 ww zs P hXsTrans hN1Trans hW1Trans hN2Trans
    hW2Trans hWwTrans hZsTrans hProgNe hProgTy
  rcases bvConcatMergeConstProgram_normalize xs n1 w1 n2 w2 ww zs P
      hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
      hProgNe with ⟨hP, hProgEq⟩
  have hBodyTy :
      __eo_typeof
          (bvConcatMergeConstProgramBody xs n1 w1 n2 w2 ww zs) =
        Term.Bool := by
    rw [← hProgEq]
    exact hProgTy
  rcases bv_concat_merge_const_body_context xs n1 w1 n2 w2 ww zs
      hXsTrans hN1Trans hW1Trans hN2Trans hW2Trans hWwTrans hZsTrans
      hBodyTy with
    ⟨W1, W2, WW, wxs, wzs, rfl, rfl, rfl, hW10, hW20, hWW0,
      hN1SmtTy, hN2SmtTy, hXsList, hZsList, hXsSmtTy, hZsSmtTy⟩
  have hPremNumeric : eo_interprets M
      (bvConcatMergeConstPrem (Term.Numeral WW)
        (Term.Numeral W1) (Term.Numeral W2)) true := by
    rw [hP] at hPremTrue
    exact hPremTrue
  have hWidthEq : WW = W1 + W2 :=
    bv_concat_merge_const_premise_width_eq M W1 W2 WW hPremNumeric
  let W1n := native_int_to_nat W1
  let W2n := native_int_to_nat W2
  have hRound1 : native_nat_to_int W1n = W1 := by
    simpa [W1n] using native_int_to_nat_roundtrip W1 hW10
  have hRound2 : native_nat_to_int W2n = W2 := by
    simpa [W2n] using native_int_to_nat_roundtrip W2 hW20
  have hWidthNat : native_nat_to_int (W1n + W2n) = WW := by
    calc
      native_nat_to_int (W1n + W2n) =
          native_nat_to_int W1n + native_nat_to_int W2n := by
        simp [native_nat_to_int, SmtEval.native_nat_to_int]
      _ = W1 + W2 := by rw [hRound1, hRound2]
      _ = WW := hWidthEq.symm
  subst WW
  have hAt1SmtTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatMergeConstAt (Term.Numeral W1) n1)) =
        SmtType.BitVec W1n := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W1) (__eo_to_smt n1)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hN1SmtTy]
    simp [W1n, __smtx_typeof_int_to_bv, native_ite, hW10]
  have hAt2SmtTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatMergeConstAt (Term.Numeral W2) n2)) =
        SmtType.BitVec W2n := by
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W2) (__eo_to_smt n2)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hN2SmtTy]
    simp [W2n, __smtx_typeof_int_to_bv, native_ite, hW20]
  have hMergedSmtTy := bv_concat_merge_const_merged_smt_type
    n1 n2 W2 hN1SmtTy hN2SmtTy
  have hMergedAtSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstAt (Term.Numeral (native_nat_to_int (W1n + W2n)))
              (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))) =
        SmtType.BitVec (W1n + W2n) := by
    have hWidth0 : native_zleq 0
        (native_nat_to_int (W1n + W2n)) = true := by
      simp only [SmtEval.native_zleq, native_nat_to_int,
        SmtEval.native_nat_to_int]
      exact decide_eq_true (Int.natCast_nonneg _)
    have hWidthRound : native_int_to_nat
        (native_nat_to_int (W1n + W2n)) = W1n + W2n := by
      simp only [native_nat_to_int, SmtEval.native_nat_to_int,
        native_int_to_nat, SmtEval.native_int_to_nat]
      exact Int.toNat_natCast (W1n + W2n)
    change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral (native_nat_to_int (W1n + W2n)))
        (__eo_to_smt
          (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))) = _
    rw [smtx_typeof_int_to_bv_term_eq, hMergedSmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hWidth0, hWidthRound]
  have hInnerSmtTy := bvConcat_term_smt_type
    (bvConcatMergeConstAt (Term.Numeral W2) n2) zs W2n wzs
    hAt2SmtTy hZsSmtTy
  have hLeftSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        SmtType.BitVec (W1n + (W2n + wzs)) := by
    simpa [bvConcatMergeConstLeftSeed] using
      bvConcat_term_smt_type
        (bvConcatMergeConstAt (Term.Numeral W1) n1)
        (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)
        W1n (W2n + wzs) hAt1SmtTy hInnerSmtTy
  have hInnerList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat)
    (bvConcatMergeConstAt (Term.Numeral W2) n2) zs
    (by intro h; cases h) hZsList
  have hLeftSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
            n2 (Term.Numeral W2) zs) = Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatMergeConstAt (Term.Numeral W1) n1)
      (bvConcatTerm (bvConcatMergeConstAt (Term.Numeral W2) n2) zs)
      (by intro h; cases h) hInnerList
  have hRightSeedSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
              (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)) =
        SmtType.BitVec ((W1n + W2n) + wzs) := by
    simpa [bvConcatMergeConstRightSeed] using
      bvConcat_term_smt_type
        (bvConcatMergeConstAt (Term.Numeral (native_nat_to_int (W1n + W2n)))
          (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
        zs (W1n + W2n) wzs hMergedAtSmtTy hZsSmtTy
  have hRightSeedList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
            (Term.Numeral (native_nat_to_int (W1n + W2n))) zs) =
        Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat)
      (bvConcatMergeConstAt (Term.Numeral (native_nat_to_int (W1n + W2n)))
        (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
      zs (by intro h; cases h) hZsList
  have hRhsListSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
              (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)) =
        SmtType.BitVec (wxs + ((W1n + W2n) + wzs)) :=
    bvConcat_list_concat_smt_type xs
      (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
        (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)
      wxs ((W1n + W2n) + wzs) hXsList hRightSeedList
      hXsSmtTy hRightSeedSmtTy
  have hRhsListList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
            (Term.Numeral (native_nat_to_int (W1n + W2n))) zs) =
        Term.Boolean true := by
    have hRecList := eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.concat) xs
      (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
        (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)
      hXsList hRightSeedList
    simpa [bvConcatMergeConstRhsList, __eo_list_concat,
      hXsList, hRightSeedList, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not] using hRecList
  rcases CongSupport.smt_eval_int_of_smt_type_int M hM
      (__eo_to_smt n1) hN1SmtTy with ⟨p, hN1Eval⟩
  rcases CongSupport.smt_eval_int_of_smt_type_int M hM
      (__eo_to_smt n2) hN2SmtTy with ⟨q, hN2Eval⟩
  have hCore :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatMergeConstAt (Term.Numeral W1) n1)
              (bvConcatMergeConstAt (Term.Numeral W2) n2))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstAt
              (Term.Numeral (native_nat_to_int (W1n + W2n)))
              (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))) := by
    simpa [bvConcatMergeConstAt, bvConcatMergeConstMergedValue,
      hRound1, hRound2] using
      bvConcat_int_to_bv_merge_eval M n1 n2 W1n W2n p q
        hN1Eval hN2Eval
  have hAssoc := bvConcat_assoc_eval M hM
    (bvConcatMergeConstAt (Term.Numeral W1) n1)
    (bvConcatMergeConstAt (Term.Numeral W2) n2) zs
    W1n W2n wzs hAt1SmtTy hAt2SmtTy hZsSmtTy
  have hCoreWithZs :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatTerm
                (bvConcatMergeConstAt (Term.Numeral W1) n1)
                (bvConcatMergeConstAt (Term.Numeral W2) n2)) zs)) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatMergeConstAt
                (Term.Numeral (native_nat_to_int (W1n + W2n)))
                (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
              zs)) := by
    change __smtx_model_eval_concat
        (__smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (bvConcatMergeConstAt (Term.Numeral W1) n1)
              (bvConcatMergeConstAt (Term.Numeral W2) n2))))
        (__smtx_model_eval M (__eo_to_smt zs)) =
      __smtx_model_eval_concat
        (__smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstAt
              (Term.Numeral (native_nat_to_int (W1n + W2n)))
              (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))))
        (__smtx_model_eval M (__eo_to_smt zs))
    rw [hCore]
  have hSeedEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
              (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)) := by
    simpa [bvConcatMergeConstLeftSeed, bvConcatMergeConstRightSeed] using
      hAssoc.trans hCoreWithZs
  have hPrefixLeft := bvConcat_list_concat_rec_eval_append M hM xs
    (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
      n2 (Term.Numeral W2) zs)
    (bvConcatMergeConstAt
      (Term.Numeral (native_nat_to_int (W1n + W2n)))
      (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
    zs wxs (W1n + W2n) wzs hXsList hXsSmtTy
    (by simpa [Nat.add_assoc] using hLeftSeedSmtTy)
    hMergedAtSmtTy hZsSmtTy hSeedEval
  have hPrefixRight := bvConcat_list_concat_rec_eval_append M hM xs
    (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
      (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)
    (bvConcatMergeConstAt
      (Term.Numeral (native_nat_to_int (W1n + W2n)))
      (bvConcatMergeConstMergedValue n1 (Term.Numeral W2) n2))
    zs wxs (W1n + W2n) wzs hXsList hXsSmtTy
    hRightSeedSmtTy hMergedAtSmtTy hZsSmtTy rfl
  have hLhsTermEq :
      bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
          n2 (Term.Numeral W2) zs =
        __eo_list_concat_rec xs
          (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
            n2 (Term.Numeral W2) zs) := by
    simp [bvConcatMergeConstLhs, __eo_list_concat, hXsList,
      hLeftSeedList, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not]
  have hRhsListTermEq :
      bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
          (Term.Numeral (native_nat_to_int (W1n + W2n))) zs =
        __eo_list_concat_rec xs
          (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
            (Term.Numeral (native_nat_to_int (W1n + W2n))) zs) := by
    simp [bvConcatMergeConstRhsList, __eo_list_concat, hXsList,
      hRightSeedList, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not]
  have hSingletonEval := bvConcat_singleton_elim_eval_eq M hM
    (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
      (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)
    (wxs + ((W1n + W2n) + wzs)) hRhsListList hRhsListSmtTy
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
              n2 (Term.Numeral W2) zs)) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2)
              (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)) := by
    calc
      _ = __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat_rec xs
              (bvConcatMergeConstLeftSeed n1 (Term.Numeral W1)
                n2 (Term.Numeral W2) zs))) := by rw [hLhsTermEq]
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm
              (__eo_list_concat_rec xs
                (bvConcatMergeConstAt
                  (Term.Numeral (native_nat_to_int (W1n + W2n)))
                  (bvConcatMergeConstMergedValue n1
                    (Term.Numeral W2) n2))) zs)) := hPrefixLeft
      _ = __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat_rec xs
              (bvConcatMergeConstRightSeed n1 n2 (Term.Numeral W2)
                (Term.Numeral (native_nat_to_int (W1n + W2n))) zs))) :=
        hPrefixRight.symm
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstRhsList xs n1 n2 (Term.Numeral W2)
              (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)) := by
        rw [hRhsListTermEq]
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2)
              (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)) :=
        hSingletonEval.symm
  rw [hProgEq] at hTyped ⊢
  rw [← hWidthNat] at hBodyTy hTyped ⊢
  have hBodyEq := bvConcatMergeConstProgramBody_eq_term_of_type_bool
    xs n1 (Term.Numeral W1) n2 (Term.Numeral W2)
      (Term.Numeral (native_nat_to_int (W1n + W2n))) zs hBodyTy
  rw [hBodyEq] at hTyped ⊢
  unfold bvConcatMergeConstTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvConcatMergeConstTerm] using hTyped
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatMergeConstLhs xs n1 (Term.Numeral W1)
            n2 (Term.Numeral W2) zs)))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatMergeConstRhs xs n1 n2 (Term.Numeral W2)
            (Term.Numeral (native_nat_to_int (W1n + W2n))) zs)))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _
