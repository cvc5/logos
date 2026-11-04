module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

/-! Support for bit-vector extract-over-concat rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvConcatTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y

def bvExtractConcat4Tail (y xs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvConcatTerm y (Term.Binary 0 0))

def bvExtractConcat4TailElim (y xs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.concat)
    (bvExtractConcat4Tail y xs)

def bvExtractConcat4Lhs (x y xs i j : Term) : Term :=
  bvExtractTerm (bvConcatTerm x (bvExtractConcat4Tail y xs)) j i

def bvExtractConcat4Rhs (y xs i j : Term) : Term :=
  bvExtractTerm (bvExtractConcat4TailElim y xs) j i

def bvExtractConcat4Term (x y xs i j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractConcat4Lhs x y xs i j)) (bvExtractConcat4Rhs y xs i j)

def bvExtractConcat1Seed (x y : Term) : Term :=
  bvConcatTerm y (bvConcatTerm x (Term.Binary 0 0))

def bvExtractConcat1Whole (x y xs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvExtractConcat1Seed x y)

def bvExtractConcat1Lhs (x y xs i j : Term) : Term :=
  bvExtractTerm (bvExtractConcat1Whole x y xs) j i

def bvExtractConcat1Rhs (x i j : Term) : Term :=
  bvExtractTerm x j i

def bvExtractConcat1Term (x y xs i j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractConcat1Lhs x y xs i j)) (bvExtractConcat1Rhs x i j)

def bvExtractConcat1PremRaw (j x : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) j)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Boolean true)

def bvExtractConcat1Prem (x j : Term) : Term :=
  bvExtractConcat1PremRaw j x

def bvExtractConcat1Program
    (x xs y i j : Term) (p : Proof) : Term :=
  __eo_prog_bv_extract_concat_1 x xs y i j p

def bvExtractConcat1ProgramBody (x xs y i j : Term) : Term :=
  let ext := Term.UOp2 UserOp2.extract j i
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply ext (bvExtractConcat1Whole x y xs)))
    (Term.Apply ext x)

def bvExtractConcat4PremRaw (j x y xs x' : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt) j)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (Term.Apply (Term.UOp UserOp._at_bvsize) x'))))
    (Term.Boolean true)

def bvExtractConcat4Prem (x y xs j : Term) : Term :=
  bvExtractConcat4PremRaw j x y xs x

def bvExtractConcat4Program
    (x y xs i j : Term) (p : Proof) : Term :=
  __eo_prog_bv_extract_concat_4 x y xs i j p

def bvExtractConcat4ProgramBody (x y xs i j : Term) : Term :=
  let tail := bvExtractConcat4Tail y xs
  let ext := Term.UOp2 UserOp2.extract j i
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply ext
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.concat) x) tail)))
    (__eo_mk_apply ext
      (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail))

def bvExtractConcat2Lhs (x y xs i j : Term) : Term :=
  bvExtractTerm (bvExtractConcat1Whole x y xs) j i

def bvExtractConcat2High (y xs u1 : Term) : Term :=
  bvExtractTerm (bvExtractConcat4TailElim y xs) u1 (Term.Numeral 0)

def bvExtractConcat2Low (x i u2 : Term) : Term :=
  bvExtractTerm x u2 i

def bvExtractConcat2Rhs (x y xs i u1 u2 : Term) : Term :=
  bvConcatTerm (bvExtractConcat2High y xs u1)
    (bvConcatTerm (bvExtractConcat2Low x i u2) (Term.Binary 0 0))

def bvExtractConcat2Term (x y xs i j u1 u2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractConcat2Lhs x y xs i j))
    (bvExtractConcat2Rhs x y xs i u1 u2)

def bvExtractConcat2PremI (x i : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) i)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Boolean true)

def bvExtractConcat2PremJ (x j : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) j)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Boolean true)

def bvExtractConcat2PremU1 (x j u1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u1)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) j)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))

def bvExtractConcat2PremU2 (x u2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))
      (Term.Numeral 1))

def bvExtractConcat2Program
    (x xs y i j u1 u2 P1 P2 P3 P4 : Term) : Term :=
  __eo_prog_bv_extract_concat_2 x xs y i j u1 u2
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)

def bvExtractConcat2ProgramBody (x xs y i j u1 u2 : Term) : Term :=
  let lhs := __eo_mk_apply (Term.UOp2 UserOp2.extract j i)
    (bvExtractConcat1Whole x y xs)
  let high := __eo_mk_apply (Term.UOp2 UserOp2.extract u1 (Term.Numeral 0))
    (bvExtractConcat4TailElim y xs)
  let low := Term.Apply (Term.UOp2 UserOp2.extract u2 i) x
  let rhs := __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) high)
    (bvConcatTerm low (Term.Binary 0 0))
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) lhs) rhs

def bvExtractConcat3Lhs (x y xs i j : Term) : Term :=
  bvExtractTerm (bvExtractConcat1Whole x y xs) j i

def bvExtractConcat3Rhs (y xs u l : Term) : Term :=
  bvExtractTerm (bvExtractConcat4TailElim y xs) u l

def bvExtractConcat3Term (x y xs i j u l : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractConcat3Lhs x y xs i j))
    (bvExtractConcat3Rhs y xs u l)

def bvExtractConcat3PremI (x i : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) i)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Boolean true)

def bvExtractConcat3PremU (x j u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) j)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))

def bvExtractConcat3PremL (x i l : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) l)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) i)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))

def bvExtractConcat3Program
    (x y xs i j u l P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_extract_concat_3 x y xs i j u l
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

def bvExtractConcat3ProgramBody (x y xs i j u l : Term) : Term :=
  let lhs :=
    __eo_mk_apply (Term.UOp2 UserOp2.extract j i)
      (bvExtractConcat1Whole x y xs)
  let rhs :=
    __eo_mk_apply (Term.UOp2 UserOp2.extract u l)
      (bvExtractConcat4TailElim y xs)
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) lhs) rhs

private def BvEvalCanonical (M : SmtModel) (t : Term) : Prop :=
  ∃ (w : Nat) (n : Int),
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary ↑w n ∧
      0 ≤ n ∧ n < (2 : Int) ^ w

private def BvConcatListCanonical (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) xs =>
      BvEvalCanonical M x ∧ BvConcatListCanonical M xs
  | t => BvEvalCanonical M t

private theorem term_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : native_Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem bvEvalCanonical_of_smt_type
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    BvEvalCanonical M t := by
  intro hTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt t) w hTy with
    ⟨p, hEval, hCan⟩
  have hWidth0 : native_zleq 0 (native_nat_to_int w) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, SmtEval.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  refine ⟨w, p, ?_, hRange.1, ?_⟩
  · simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hEval
  · simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hRange.2

private theorem bvConcat_args_of_bitvec_type
    (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (bvConcatTerm y x)) = SmtType.BitVec w ->
    ∃ wy wx : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx := by
  intro hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    change __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) ≠
      SmtType.None
    rw [show
      __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w by
      simpa [bvConcatTerm] using hTy]
    intro h
    cases h
  exact bv_concat_args_of_non_none hNN

private theorem smt_typeof_bv_concat_eq
    (x y : Term) (wx wy : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt (bvConcatTerm x y)) =
      SmtType.BitVec (wx + wy) := by
  intro hXTy hYTy
  change __smtx_typeof
      (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.BitVec (wx + wy)
  rw [typeof_concat_eq, hXTy, hYTy]
  simp only [__smtx_typeof_concat, SmtEval.native_zplus,
    native_nat_to_int, SmtEval.native_nat_to_int,
    native_int_to_nat, SmtEval.native_int_to_nat]
  congr

private theorem smt_typeof_bv_concat_width_inv
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt (bvConcatTerm x y)) =
      SmtType.BitVec w ->
    ∃ wx wy,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      w = wx + wy := by
  intro hTy
  rcases bvConcat_args_of_bitvec_type x y w hTy with
    ⟨wx, wy, hXTy, hYTy⟩
  have hConcatTy := smt_typeof_bv_concat_eq x y wx wy hXTy hYTy
  rw [hConcatTy] at hTy
  injection hTy with hW
  exact ⟨wx, wy, hXTy, hYTy, hW.symm⟩

private theorem smt_typeof_concat_empty :
    __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) =
      SmtType.BitVec 0 := by
  change __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0
  simp [__smtx_typeof, SmtEval.native_and, native_ite,
    SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
    native_mod_total, native_int_to_nat, SmtEval.native_int_to_nat]

private theorem bv_concat_empty_is_list_true :
    __eo_is_list (Term.UOp UserOp.concat) (Term.Binary 0 0) =
      Term.Boolean true := by
  simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
    __eo_requires, __eo_is_ok, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem bv_concat_nil_width_zero
    (nil : Term) (w : Nat) :
    (∀ f x y, nil ≠ Term.Apply (Term.Apply f x) y) ->
    __eo_is_list (Term.UOp UserOp.concat) nil = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    w = 0 := by
  intro hNot hList hTy
  cases nil <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_requires, __eo_is_ok, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList hTy ⊢
  case Binary bw bn =>
    -- `split` cannot generalise `Term.Binary bw bn` (it also occurs in `hTy`),
    -- so decide the two literals by hand; only `Binary 0 0` matches the
    -- `concat` nil pattern.
    by_cases hbw : bw = 0
    · subst hbw
      by_cases hbn : bn = 0
      · subst hbn
        rw [smt_typeof_concat_empty] at hTy
        injection hTy with hW
        exact hW.symm
      · exact absurd hList (by simp [__eo_is_list_nil, hbn])
    · exact absurd hList (by simp [__eo_is_list_nil, hbw])

private theorem bv_concat_nil_width_zero_of_nil_true
    (nil : Term) (w : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.concat) nil = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    w = 0 := by
  intro hNil hTy
  cases nil <;> simp [__eo_is_list_nil] at hNil hTy ⊢
  case Binary bw bn =>
    split at hNil <;> simp_all
    rw [smt_typeof_concat_empty] at hTy
    injection hTy with hW
    exact hW.symm

private theorem bv_concat_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.concat) t = Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
    exact False.elim (hNe rfl)
  case Binary w n =>
    by_cases h : w = 0 ∧ n = 0
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨true, by simp [__eo_is_list_nil]⟩
    · have hTerm : Term.Binary w n ≠ Term.Binary 0 0 := by
        intro hEq
        cases hEq
        exact h ⟨rfl, rfl⟩
      exact ⟨false, by simp [__eo_is_list_nil, hTerm]⟩
  all_goals
    exact ⟨false, by simp [__eo_is_list_nil]⟩

private theorem smt_typeof_list_concat_rec_bv_aux
    (f a z : Term) :
    f = Term.UOp UserOp.concat ->
    ∀ wa wz : Nat,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
        SmtType.BitVec (wa + wz) := by
  intro hf
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro wa wz hList haTy hzTy
      subst f
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro wa wz hList haTy hzTy
      change __smtx_typeof SmtTerm.None = SmtType.BitVec wz at hzTy
      rw [TranslationProofs.smtx_typeof_none] at hzTy
      cases hzTy
  | case3 g x y z hZ ih =>
      intro wa wz hList haTy hzTy
      subst f
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.concat) x y
          hList
      rcases smt_typeof_bv_concat_width_inv x y wa (by
          simpa [bvConcatTerm] using haTy) with
        ⟨wx, wy, hXTy, hYTy, hWa⟩
      have hZNonStuck : z ≠ Term.Stuck :=
        term_ne_stuck_of_smt_bitvec_type hzTy
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.concat)
          y z hTailList hZNonStuck
      have hTailTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
            SmtType.BitVec (wy + wz) :=
        ih wy wz hTailList hYTy hzTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailConcat]
      have hConcatTy :=
        smt_typeof_bv_concat_eq x (__eo_list_concat_rec y z)
          wx (wy + wz) hXTy hTailTy
      simpa [bvConcatTerm, hWa, Nat.add_assoc] using hConcatTy
  | case4 nil z hNil hZ hNot =>
      intro wa wz hList haTy hzTy
      subst f
      have hWaZero :
          wa = 0 :=
        bv_concat_nil_width_zero nil wa hNot hList haTy
      subst wa
      simpa [__eo_list_concat_rec] using hzTy

private theorem smt_typeof_list_concat_rec_bv
    (a z : Term) (wa wz : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec (wa + wz) :=
  smt_typeof_list_concat_rec_bv_aux
    (Term.UOp UserOp.concat) a z rfl wa wz

private theorem bv_concat_seed_is_list_true (y : Term) :
    __eo_is_list (Term.UOp UserOp.concat)
        (bvConcatTerm y (Term.Binary 0 0)) =
      Term.Boolean true :=
  eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) y (Term.Binary 0 0)
    (by intro h; cases h) bv_concat_empty_is_list_true

private theorem smt_typeof_bv_concat_seed
    (y : Term) (wy : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof
        (__eo_to_smt (bvConcatTerm y (Term.Binary 0 0))) =
      SmtType.BitVec wy := by
  intro hYTy
  have hTy :=
    smt_typeof_bv_concat_eq y (Term.Binary 0 0) wy 0
      hYTy smt_typeof_concat_empty
  simpa [Nat.add_zero] using hTy

private theorem bv_extract_concat1_seed_is_list_true
    (x y : Term) :
    __eo_is_list (Term.UOp UserOp.concat)
        (bvExtractConcat1Seed x y) =
      Term.Boolean true := by
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatTerm x (Term.Binary 0 0)) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat) x (Term.Binary 0 0)
      (by intro h; cases h) bv_concat_empty_is_list_true
  exact
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat) y
      (bvConcatTerm x (Term.Binary 0 0))
      (by intro h; cases h) hInnerList

private theorem smt_typeof_bv_extract_concat1_seed
    (x y : Term) (wx wy : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt (bvExtractConcat1Seed x y)) =
      SmtType.BitVec (wy + wx) := by
  intro hXTy hYTy
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
        SmtType.BitVec wx := by
    have hTy :=
      smt_typeof_bv_concat_eq x (Term.Binary 0 0) wx 0
        hXTy smt_typeof_concat_empty
    simpa [Nat.add_zero] using hTy
  simpa [bvExtractConcat1Seed] using
    smt_typeof_bv_concat_eq y
      (bvConcatTerm x (Term.Binary 0 0)) wy wx hYTy hInnerTy

private theorem smt_typeof_list_concat_bv
    (a z : Term) (wa wz : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_concat (Term.UOp UserOp.concat) a z)) =
      SmtType.BitVec (wa + wz) := by
  intro hListA hListZ hATy hZTy
  have hRecTy :=
    smt_typeof_list_concat_rec_bv a z wa wz hListA hATy hZTy
  simpa [__eo_list_concat, hListA, hListZ, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] using hRecTy

private theorem smt_typeof_bv_extract_concat1_whole
    (x y xs : Term) (wx wy wxs : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
      SmtType.BitVec (wxs + (wy + wx)) := by
  intro hXsList hXTy hYTy hXsTy
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  have hSeedTy :=
    smt_typeof_bv_extract_concat1_seed x y wx wy hXTy hYTy
  simpa [bvExtractConcat1Whole] using
    smt_typeof_list_concat_bv xs (bvExtractConcat1Seed x y)
      wxs (wy + wx) hXsList hSeedList hXsTy hSeedTy

private theorem smt_typeof_concat_list_of_translation
    (t : Term) :
    __eo_is_list (Term.UOp UserOp.concat) t = Term.Boolean true ->
    RuleProofs.eo_has_smt_translation t ->
    ∃ w : Nat, __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  intro hList hTrans
  revert hList hTrans
  induction t using __eo_get_elements_rec.induct with
  | case1 =>
      intro hList _hTrans
      simp [__eo_is_list] at hList
  | case2 f x xs ih =>
      intro hList hTrans
      have hf : f = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) f x xs hList
      subst f
      have hNN : term_has_non_none_type
          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt xs)) := by
        simpa [RuleProofs.eo_has_smt_translation,
          term_has_non_none_type] using hTrans
      rcases bv_concat_args_of_non_none hNN with
        ⟨wx, wxs, hXTy, hXsTy⟩
      exact ⟨wx + wxs,
        by simpa [bvConcatTerm] using
          smt_typeof_bv_concat_eq x xs wx wxs hXTy hXsTy⟩
  | case3 t _hNil hNot =>
      intro hList hTrans
      cases t with
      | Binary w n =>
          by_cases hEq : Term.Binary w n = Term.Binary 0 0
          · cases hEq
            exact ⟨0, smt_typeof_concat_empty⟩
          · exfalso
            simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
              __eo_requires, __eo_is_ok, native_ite, native_teq,
              native_not, SmtEval.native_not, hEq] at hList
      | Apply f arg =>
          cases f with
          | Apply g head =>
              exact False.elim (hNot g head arg rfl)
          | _ =>
              exfalso
              simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
                __eo_requires, __eo_is_ok, native_ite, native_teq,
                native_not, SmtEval.native_not] at hList
      | Stuck =>
          simp [__eo_is_list] at hList
      | UOp op =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UOp1 op a =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UOp2 op a b =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UOp3 op a b c =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | __eo_List =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | __eo_List_nil =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | __eo_List_cons =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Bool =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Boolean b =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Numeral n =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Rational r =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | String s =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | «Type» =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | FunType =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Var s T =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DatatypeType s d =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DatatypeTypeRef s =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DtcAppType a b =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DtCons s d i =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DtSel s d i j =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | USort s =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UConst i T =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList

private theorem bv_list_concat_lists_of_ne_stuck (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have ha : __eo_is_list f a = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) hReq
  have hReqEq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) =
        __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) :=
    eo_requires_eq_result_of_ne_stuck
      (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) hReq
  have hReqTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck := by
    rwa [hReqEq] at hReq
  have hb : __eo_is_list f b = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list f b) (Term.Boolean true)
      (__eo_list_concat_rec a b) hReqTail
  exact ⟨ha, hb⟩

private theorem bv_extract_concat4_tail_is_list_true
    (y xs : Term) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat)
        (bvExtractConcat4Tail y xs) =
      Term.Boolean true := by
  intro hXsList
  have hSeedList := bv_concat_seed_is_list_true y
  have hRecList :
      __eo_is_list (Term.UOp UserOp.concat)
          (__eo_list_concat_rec xs (bvConcatTerm y (Term.Binary 0 0))) =
        Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.concat) xs (bvConcatTerm y (Term.Binary 0 0))
      hXsList hSeedList
  simpa [bvExtractConcat4Tail, __eo_list_concat, hXsList, hSeedList,
    __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
    using hRecList

private theorem smt_typeof_bv_extract_concat4_tail
    (y xs : Term) (wy wxs : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    __smtx_typeof (__eo_to_smt (bvExtractConcat4Tail y xs)) =
      SmtType.BitVec (wxs + wy) := by
  intro hXsList hYTy hXsTy
  have hSeedList := bv_concat_seed_is_list_true y
  have hSeedTy := smt_typeof_bv_concat_seed y wy hYTy
  exact smt_typeof_list_concat_bv xs
    (bvConcatTerm y (Term.Binary 0 0)) wxs wy
    hXsList hSeedList hXsTy hSeedTy

private theorem smt_typeof_bv_singleton_elim
    (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) =
      SmtType.BitVec w := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.BitVec w
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases bv_concat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · simpa [bvConcatTerm] using hTy
          · rcases smt_typeof_bv_concat_width_inv head tail w (by
                simpa [bvConcatTerm] using hTy) with
              ⟨wh, wt, hHeadTy, hTailTy, hW⟩
            have hWtZero :
                wt = 0 :=
              bv_concat_nil_width_zero_of_nil_true tail wt hNil hTailTy
            subst wt
            simp [Nat.add_zero] at hW
            subst w
            exact hHeadTy
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hTy

private theorem extractLsb'_append_low
    {x : BitVec W} {y : BitVec T} {L D : Nat}
    (hFit : L + D ≤ T) :
    (x ++ y).extractLsb' L D = y.extractLsb' L D := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getElem_extractLsb' hi]
  have hTail : L + i < T := by omega
  have hApp : L + i < W + T := by omega
  rw [BitVec.getLsbD_eq_getElem hApp, BitVec.getElem_append]
  simp [hTail, BitVec.getLsbD_eq_getElem hTail]

private theorem concat_bitvec_values
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

private theorem eval_bv_extract_concat_low
    (M : SmtModel) (hM : model_wf M)
    (x tail : Term) (wx wt : Nat) (h l : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt tail) = SmtType.BitVec wt ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wt) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvConcatTerm x tail)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm tail (Term.Numeral h)
          (Term.Numeral l))) := by
  intro hXTy hTailTy hl0 hHTail hd0
  let d : native_Int :=
    native_zplus (native_zplus h 1) (native_zneg l)
  let L : Nat := native_int_to_nat l
  let D : Nat := native_int_to_nat d
  have hLRound : (↑L : Int) = l := by
    simpa [L, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip l hl0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip d hd0
  have hDDef : d = h + 1 + -l := by
    simp [d, SmtEval.native_zplus, SmtEval.native_zneg,
      Int.add_assoc]
  have hTailBoundInt : h < (↑wt : Int) := by
    exact of_decide_eq_true hHTail
  have hFitInt : (↑L : Int) + (↑D : Int) ≤ (↑wt : Int) := by
    rw [hLRound, hDRound]
    calc
      l + d = h + 1 := by
        rw [hDDef]
        calc
          l + (h + 1 + -l) = (l + (h + 1)) + -l :=
            (Int.add_assoc l (h + 1) (-l)).symm
          _ = ((h + 1) + l) + -l := by
            rw [Int.add_comm l (h + 1)]
          _ = h + 1 := Int.add_neg_cancel_right (h + 1) l
      _ ≤ (↑wt : Int) := Int.add_one_le_iff.mpr hTailBoundInt
  have hFit : L + D ≤ wt := by
    exact_mod_cast hFitInt
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) wx
      hXTy with
    ⟨px, hXEval, hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt tail) wt
      hTailTy with
    ⟨pt, hTailEval, hTailCan⟩
  have hWx0 : native_zleq 0 (native_nat_to_int wx) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hWt0 : native_zleq 0 (native_nat_to_int wt) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hXRange := bitvec_payload_range_of_canonical hWx0 hXCan
  have hTailRange := bitvec_payload_range_of_canonical hWt0 hTailCan
  let bx : BitVec wx := BitVec.ofInt wx px
  let bt : BitVec wt := BitVec.ofInt wt pt
  have hBxPayload : (↑bx.toNat : Int) = px := by
    rw [show bx.toNat = px.toNat by
      exact ofInt_toNat_canonical wx px hXRange.1 (by
        simpa [natpow2_eq, native_nat_to_int,
          SmtEval.native_nat_to_int] using hXRange.2)]
    exact Int.toNat_of_nonneg hXRange.1
  have hBtPayload : (↑bt.toNat : Int) = pt := by
    rw [show bt.toNat = pt.toNat by
      exact ofInt_toNat_canonical wt pt hTailRange.1 (by
        simpa [natpow2_eq, native_nat_to_int,
          SmtEval.native_nat_to_int] using hTailRange.2)]
    exact Int.toNat_of_nonneg hTailRange.1
  have hXEvalB :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑wx : Int) (↑bx.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hBxPayload]
      using hXEval
  have hTailEvalB :
      __smtx_model_eval M (__eo_to_smt tail) =
        SmtValue.Binary (↑wt : Int) (↑bt.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hBtPayload]
      using hTailEval
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt (bvConcatTerm x tail)) =
        SmtValue.Binary (↑(wx + wt) : Int) (↑(bx ++ bt).toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt tail)) =
      SmtValue.Binary (↑(wx + wt) : Int) (↑(bx ++ bt).toNat : Int)
    simp [__smtx_model_eval, hXEvalB, hTailEvalB,
      concat_bitvec_values bx bt]
  have hConcatPayload0 :
      (0 : Int) ≤ (↑(bx ++ bt).toNat : Int) :=
    Int.natCast_nonneg _
  have hConcatPayloadLt :
      (↑(bx ++ bt).toNat : Int) < (2 : Int) ^ (wx + wt) := by
    exact_mod_cast (bx ++ bt).isLt
  have hTailPayload0 : (0 : Int) ≤ (↑bt.toNat : Int) :=
    Int.natCast_nonneg _
  have hTailPayloadLt :
      (↑bt.toNat : Int) < (2 : Int) ^ wt := by
    exact_mod_cast bt.isLt
  rw [eval_extract_term M (bvConcatTerm x tail) h l,
    eval_extract_term M tail h l, hConcatEval, hTailEvalB]
  rw [extract_val_bitvec_start_len (wx + wt) L D
      (↑(bx ++ bt).toNat : Int) h l hConcatPayload0
      hConcatPayloadLt hLRound.symm (by rw [hDRound, hDDef])]
  rw [extract_val_bitvec_start_len wt L D
      (↑bt.toNat : Int) h l hTailPayload0 hTailPayloadLt
      hLRound.symm (by rw [hDRound, hDDef])]
  rw [bitvec_ofInt_natCast_toNat (bx ++ bt),
    bitvec_ofInt_natCast_toNat bt]
  congr 2
  exact congrArg BitVec.toNat
    (extractLsb'_append_low (x := bx) (y := bt) (L := L) (D := D)
      hFit)

private theorem native_zlt_nat_add_right_local
    {h : native_Int} {w extra : Nat} :
    native_zlt h (native_nat_to_int w) = true ->
    native_zlt h (native_nat_to_int (extra + w)) = true := by
  intro hlt
  have hltInt : h < (↑w : Int) := by
    exact of_decide_eq_true hlt
  have hleNat : w ≤ extra + w := by
    omega
  have hleInt : (↑w : Int) ≤ ↑(extra + w) := by
    exact_mod_cast hleNat
  have hltAdd : h < (↑(extra + w) : Int) :=
    Int.lt_of_lt_of_le hltInt hleInt
  exact decide_eq_true hltAdd

private theorem eval_bv_extract_list_concat_rec_low
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (wa wz : Nat) (h l : native_Int) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wz) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (__eo_list_concat_rec a z)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm z (Term.Numeral h) (Term.Numeral l))) := by
  intro hList hATy hZTy hl0 hBound hd0
  revert wa hList hATy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro wa hList hATy
      simp [__eo_is_list] at hList
  | case2 a =>
      intro wa hList hATy
      change __smtx_typeof SmtTerm.None = SmtType.BitVec wz at hZTy
      rw [TranslationProofs.smtx_typeof_none] at hZTy
      cases hZTy
  | case3 g x y z hZ ih =>
      intro wa hList hATy
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.concat) x y hList
      rcases smt_typeof_bv_concat_width_inv x y wa (by
          simpa [bvConcatTerm] using hATy) with
        ⟨wx, wy, hXTy, hYTy, _hWa⟩
      have hZNonStuck : z ≠ Term.Stuck :=
        term_ne_stuck_of_smt_bitvec_type hZTy
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.concat)
          y z hTailList hZNonStuck
      have hTailTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
            SmtType.BitVec (wy + wz) :=
        smt_typeof_list_concat_rec_bv y z wy wz hTailList hYTy hZTy
      have hTailBound :
          native_zlt h (native_nat_to_int (wy + wz)) = true :=
        native_zlt_nat_add_right_local (extra := wy) hBound
      have hHeadLow :=
        eval_bv_extract_concat_low M hM x (__eo_list_concat_rec y z)
          wx (wy + wz) h l hXTy hTailTy hl0 hTailBound hd0
      have hTailLow :=
        ih hZTy wy hTailList hYTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailConcat]
      change __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm (bvConcatTerm x (__eo_list_concat_rec y z))
              (Term.Numeral h) (Term.Numeral l))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm z (Term.Numeral h) (Term.Numeral l)))
      rw [hHeadLow, hTailLow]
  | case4 nil z hNil hZ hNot =>
      intro wa hList hATy
      simpa [__eo_list_concat_rec]

private theorem eval_bv_extract_list_concat_low
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (wa wz : Nat) (h l : native_Int) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wz) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (__eo_list_concat (Term.UOp UserOp.concat) a z)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm z (Term.Numeral h) (Term.Numeral l))) := by
  intro hListA hListZ hATy hZTy hl0 hBound hd0
  have hRec :=
    eval_bv_extract_list_concat_rec_low M hM a z wa wz h l
      hListA hATy hZTy hl0 hBound hd0
  simpa [__eo_list_concat, hListA, hListZ, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] using hRec

private theorem eval_bvsize_of_smt_bitvec
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  have hRound := native_int_to_nat_roundtrip w hw0
  have hSize :
      __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)) = w := by
    rw [hXSmtTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  rw [hSize]
  simp [native_ite, hw0, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem eval_bvsize_of_smt_bitvec_nat
    (M : SmtModel) (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral (native_nat_to_int w) := by
  intro hTy
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hTy' :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat (native_nat_to_int w)) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int,
      native_int_to_nat, SmtEval.native_int_to_nat] using hTy
  exact eval_bvsize_of_smt_bitvec M x (native_nat_to_int w) hw0 hTy'

private theorem bool_eq_true_of_model_eval_eq_true
    (b : native_Bool) :
    __smtx_model_eval_eq (SmtValue.Boolean b) (SmtValue.Boolean true) =
      SmtValue.Boolean true ->
    b = true := by
  cases b <;> simp [__smtx_model_eval_eq, native_veq]

private theorem model_eval_eq_true_of_eo_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
        SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem bvExtractConcat4Prem_bound
    (M : SmtModel) (x y xs : Term) (wx wy wxs : Nat)
    (j : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    eo_interprets M
      (bvExtractConcat4Prem x y xs (Term.Numeral j)) true ->
    native_zlt j (native_nat_to_int (wxs + wy)) = true := by
  intro hXTy hYTy hXsTy hPrem
  have hYXsTy :
      __smtx_typeof (__eo_to_smt (bvConcatTerm y xs)) =
        SmtType.BitVec (wy + wxs) :=
    smt_typeof_bv_concat_eq y xs wy wxs hYTy hXsTy
  have hTotalTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatTerm x (bvConcatTerm y xs))) =
        SmtType.BitVec (wx + (wy + wxs)) :=
    smt_typeof_bv_concat_eq x (bvConcatTerm y xs)
      wx (wy + wxs) hXTy hYXsTy
  have hTotalSize :=
    eval_bvsize_of_smt_bitvec_nat M
      (bvConcatTerm x (bvConcatTerm y xs))
      (wx + (wy + wxs)) hTotalTy
  have hXSize :=
    eval_bvsize_of_smt_bitvec_nat M x wx hXTy
  have hBoundWidth :
      native_zplus (native_nat_to_int (wx + (wy + wxs)))
          (native_zneg (native_nat_to_int wx)) =
        native_nat_to_int (wxs + wy) := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg,
      native_nat_to_int, SmtEval.native_nat_to_int]
    calc
      (↑wx : Int) + (↑wy + ↑wxs) + -↑wx =
          ((↑wy + ↑wxs) + ↑wx) + -↑wx := by
        simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
      _ = ↑wy + ↑wxs :=
          Int.add_neg_cancel_right ((↑wy : Int) + ↑wxs) (↑wx : Int)
      _ = ↑wxs + ↑wy := by
          rw [Int.add_comm]
  have hEqEval :=
    model_eval_eq_true_of_eo_eq_true M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral j))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      (Term.Boolean true) (by
        simpa [bvExtractConcat4Prem, bvExtractConcat4PremRaw] using hPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.lt (SmtTerm.Numeral j)
          (SmtTerm.neg
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp._at_bvsize)
                (bvConcatTerm x (bvConcatTerm y xs))))
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp._at_bvsize) x)))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hEqEval
  simp [__smtx_model_eval, __smtx_model_eval__, __smtx_model_eval_lt,
    hTotalSize, hXSize, hBoundWidth] at hEqEval
  exact bool_eq_true_of_model_eval_eq_true
    (native_zlt j (native_nat_to_int (wxs + wy))) hEqEval

private theorem smt_typeof_bvsize_int_inv (t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) =
      SmtType.Int ->
    ∃ w, __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  intro hTy
  change __smtx_typeof
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t)))))
        SmtTerm.None) = SmtType.Int at hTy
  generalize hT : __smtx_typeof (__eo_to_smt t) = T at hTy
  cases T <;>
    simp [__eo_to_smt_bv_size, SmtEval.native_zleq,
      SmtEval.native_zneg, native_nat_to_int, SmtEval.native_nat_to_int,
      native_ite, __smtx_typeof] at hTy ⊢

private theorem smt_typeof_bvsize_ne_real (t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) ≠
      SmtType.Real := by
  intro hTy
  change __smtx_typeof
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t)))))
        SmtTerm.None) = SmtType.Real at hTy
  generalize hT : __smtx_typeof (__eo_to_smt t) = T at hTy
  cases T <;>
    simp [__eo_to_smt_bv_size, SmtEval.native_zleq,
      SmtEval.native_zneg, native_nat_to_int, SmtEval.native_nat_to_int,
      native_ite, __smtx_typeof] at hTy

private theorem smt_typeof_neg_int_args
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.neg a b) = SmtType.Int ->
    __smtx_typeof a = SmtType.Int ∧
      __smtx_typeof b = SmtType.Int := by
  intro hTy
  have hNN : term_has_non_none_type (SmtTerm.neg a b) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq a b) hNN with hArgs | hArgs
  · exact hArgs
  · rw [typeof_neg_eq] at hTy
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2] at hTy

private theorem smt_typeof_neg_real_left
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.neg a b) = SmtType.Real ->
    __smtx_typeof a = SmtType.Real := by
  intro hTy
  have hNN : term_has_non_none_type (SmtTerm.neg a b) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq a b) hNN with hArgs | hArgs
  · rw [typeof_neg_eq] at hTy
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2] at hTy
  · exact hArgs.1

private theorem bvExtractConcat4Prem_smt_context
    (x y xs j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat4Prem x y xs j) ->
    ∃ wx wy wxs,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __smtx_typeof (__eo_to_smt j) = SmtType.Int := by
  intro hPremBool
  let cond :=
    Term.Apply
      (Term.Apply (Term.UOp UserOp.lt) j)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp._at_bvsize)
            (bvConcatTerm x (bvConcatTerm y xs))))
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        cond (Term.Boolean true) (by
          simpa [bvExtractConcat4Prem, bvExtractConcat4PremRaw, cond]
            using hPremBool) with
      ⟨hEqTy, _hNN⟩
    exact hEqTy
  change __smtx_typeof
      (SmtTerm.lt (__eo_to_smt j)
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) =
    SmtType.Bool at hCondTy
  have hLtNN : term_has_non_none_type
      (SmtTerm.lt (__eo_to_smt j)
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) := by
    unfold term_has_non_none_type
    rw [hCondTy]
    intro h
    cases h
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
      (typeof_lt_eq (__eo_to_smt j)
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))))
      hLtNN with hLtArgs | hLtArgs
  · have hBoundTy : __smtx_typeof
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
        SmtType.Int := hLtArgs.2
    rcases smt_typeof_neg_int_args
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp._at_bvsize)
            (bvConcatTerm x (bvConcatTerm y xs))))
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        hBoundTy with ⟨hTotalSizeTy, hXSizeTy⟩
    rcases smt_typeof_bvsize_int_inv
        (bvConcatTerm x (bvConcatTerm y xs)) hTotalSizeTy with
      ⟨wTotal, hTotalTy⟩
    rcases smt_typeof_bvsize_int_inv x hXSizeTy with
      ⟨wx, hXTy⟩
    have hTotalNN : term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt x)
          (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs))) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (SmtTerm.concat (__eo_to_smt x)
            (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs))) ≠
        SmtType.None
      rw [show __smtx_typeof
          (SmtTerm.concat (__eo_to_smt x)
            (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs))) =
          SmtType.BitVec wTotal by
        simpa [bvConcatTerm] using hTotalTy]
      intro h
      cases h
    rcases bv_concat_args_of_non_none hTotalNN with
      ⟨_wx', wTail, hXTy', hTailTy⟩
    have hTailNN : term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs)) := by
      unfold term_has_non_none_type
      rw [hTailTy]
      intro h
      cases h
    rcases bv_concat_args_of_non_none hTailNN with
      ⟨wy, wxs, hYTy, hXsTy⟩
    exact ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hLtArgs.1⟩
  · rw [typeof_lt_eq] at hCondTy
    simp [__smtx_typeof_arith_overload_op_2_ret, hLtArgs.1, hLtArgs.2]
      at hCondTy
    have hLeftReal := smt_typeof_neg_real_left
      (__eo_to_smt
        (Term.Apply (Term.UOp UserOp._at_bvsize)
          (bvConcatTerm x (bvConcatTerm y xs))))
      (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
      hLtArgs.2
    exact False.elim
      (smt_typeof_bvsize_ne_real (bvConcatTerm x (bvConcatTerm y xs))
        hLeftReal)

private theorem bvExtractConcat1Prem_smt_context
    (x j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    ∃ wx,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt j) = SmtType.Int := by
  intro hPremBool
  let cond :=
    Term.Apply (Term.Apply (Term.UOp UserOp.leq) j)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        cond (Term.Boolean true) (by
          simpa [bvExtractConcat1Prem, bvExtractConcat1PremRaw, cond]
            using hPremBool) with
      ⟨hEqTy, _hNN⟩
    exact hEqTy
  change __smtx_typeof
      (SmtTerm.leq (__eo_to_smt j)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
    SmtType.Bool at hCondTy
  have hLeqNN : term_has_non_none_type
      (SmtTerm.leq (__eo_to_smt j)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) := by
    unfold term_has_non_none_type
    rw [hCondTy]
    intro h
    cases h
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
      (typeof_leq_eq (__eo_to_smt j)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      hLeqNN with hLeqArgs | hLeqArgs
  · rcases smt_typeof_bvsize_int_inv x hLeqArgs.2 with
      ⟨wx, hXTy⟩
    exact ⟨wx, hXTy, hLeqArgs.1⟩
  · exact False.elim
      (smt_typeof_bvsize_ne_real x hLeqArgs.2)

private theorem bv_extract_concat4_guard_refs
    {j x y xs jRef xRef yRef xsRef xRef' body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq j jRef) (__eo_eq x xRef))
              (__eo_eq y yRef))
            (__eo_eq xs xsRef))
          (__eo_eq x xRef'))
        (Term.Boolean true) body ≠ Term.Stuck ->
    jRef = j ∧ xRef = x ∧ yRef = y ∧ xsRef = xs ∧ xRef' = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG1, hX2⟩
  rcases bv_extract_support_and_true hG1 with ⟨hG2, hXs⟩
  rcases bv_extract_support_and_true hG2 with ⟨hG3, hY⟩
  rcases bv_extract_support_and_true hG3 with ⟨hJ, hX1⟩
  exact ⟨(bv_extract_support_eq_true hJ).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hY).symm,
    (bv_extract_support_eq_true hXs).symm,
    (bv_extract_support_eq_true hX2).symm⟩

private theorem bv_extract_concat1_guard_refs
    {j x jRef xRef body : Term} :
    __eo_requires
        (__eo_and (__eo_eq j jRef) (__eo_eq x xRef))
        (Term.Boolean true) body ≠ Term.Stuck ->
    jRef = j ∧ xRef = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hJ, hX⟩
  exact ⟨(bv_extract_support_eq_true hJ).symm,
    (bv_extract_support_eq_true hX).symm⟩

private theorem bv_extract_concat1_premise_shape
    (x xs y i j P : Term) :
    x ≠ Term.Stuck -> xs ≠ Term.Stuck -> y ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat1Program x xs y i j (Proof.pf P) ≠ Term.Stuck ->
    ∃ jRef xRef, P = bvExtractConcat1PremRaw jRef xRef := by
  intro hX hXs hY hI hJ hProg
  by_cases hShape :
      ∃ jRef xRef, P = bvExtractConcat1PremRaw jRef xRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_concat_1.eq_7 x xs y i j
      (Proof.pf P) hX hXs hY hI hJ (by
        intro jRef xRef hP
        cases hP
        exact hShape ⟨jRef, xRef, rfl⟩)

private theorem bv_extract_concat1_program_body_canonical
    (x xs y i j : Term) :
    x ≠ Term.Stuck -> xs ≠ Term.Stuck -> y ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat1Program x xs y i j
        (Proof.pf (bvExtractConcat1Prem x j)) =
      bvExtractConcat1ProgramBody x xs y i j := by
  intro hX hXs hY hI hJ
  unfold bvExtractConcat1Program bvExtractConcat1Prem
    bvExtractConcat1PremRaw bvExtractConcat1ProgramBody
    bvExtractConcat1Whole bvExtractConcat1Seed bvConcatTerm
  rw [__eo_prog_bv_extract_concat_1.eq_6 x xs y i j j x
    hX hXs hY hI hJ]
  simp [bvExtractTerm, __eo_requires, __eo_and, __eo_eq, native_ite,
    native_teq, native_not, SmtEval.native_not, SmtEval.native_and,
    hX, hJ]

theorem bvExtractConcat1Program_normalize
    (x xs y i j P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    bvExtractConcat1Program x xs y i j (Proof.pf P) ≠ Term.Stuck ->
    P = bvExtractConcat1Prem x j ∧
      bvExtractConcat1Program x xs y i j (Proof.pf P) =
        bvExtractConcat1ProgramBody x xs y i j := by
  intro hXTrans hXsTrans hYTrans hITrans hJTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  rcases bv_extract_concat1_premise_shape x xs y i j P
      hX hXs hY hI hJ hProg with
    ⟨jRef, xRef, hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvExtractConcat1Program bvExtractConcat1PremRaw at hReq
  rw [__eo_prog_bv_extract_concat_1.eq_6 x xs y i j
    jRef xRef hX hXs hY hI hJ] at hReq
  rcases bv_extract_concat1_guard_refs hReq with ⟨hJRef, hXRef⟩
  subst jRef
  subst xRef
  have hPCanon : P = bvExtractConcat1Prem x j := hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_extract_concat1_program_body_canonical x xs y i j
    hX hXs hY hI hJ

private theorem bv_extract_concat4_premise_shape
    (x y xs i j P : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> xs ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat4Program x y xs i j (Proof.pf P) ≠ Term.Stuck ->
    ∃ jRef xRef yRef xsRef xRef',
      P = bvExtractConcat4PremRaw jRef xRef yRef xsRef xRef' := by
  intro hX hY hXs hI hJ hProg
  by_cases hShape :
      ∃ jRef xRef yRef xsRef xRef',
        P = bvExtractConcat4PremRaw jRef xRef yRef xsRef xRef'
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_concat_4.eq_7 x y xs i j
      (Proof.pf P) hX hY hXs hI hJ (by
        intro jRef xRef yRef xsRef xRef' hP
        cases hP
        exact hShape ⟨jRef, xRef, yRef, xsRef, xRef', rfl⟩)

private theorem bv_extract_concat4_program_body_canonical
    (x y xs i j : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> xs ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat4Program x y xs i j
        (Proof.pf (bvExtractConcat4Prem x y xs j)) =
      bvExtractConcat4ProgramBody x y xs i j := by
  intro hX hY hXs hI hJ
  unfold bvExtractConcat4Program bvExtractConcat4Prem
    bvExtractConcat4PremRaw bvConcatTerm
  rw [__eo_prog_bv_extract_concat_4.eq_6 x y xs i j j x y xs x
    hX hY hXs hI hJ]
  simp [bvExtractConcat4ProgramBody, bvExtractConcat4Tail, bvConcatTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and,
    hX, hY, hXs, hI, hJ]

theorem bvExtractConcat4Program_normalize
    (x y xs i j P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    bvExtractConcat4Program x y xs i j (Proof.pf P) ≠ Term.Stuck ->
    P = bvExtractConcat4Prem x y xs j ∧
      bvExtractConcat4Program x y xs i j (Proof.pf P) =
        bvExtractConcat4ProgramBody x y xs i j := by
  intro hXTrans hYTrans hXsTrans hITrans hJTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  rcases bv_extract_concat4_premise_shape x y xs i j P
      hX hY hXs hI hJ hProg with
    ⟨jRef, xRef, yRef, xsRef, xRef', hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvExtractConcat4Program bvExtractConcat4PremRaw bvConcatTerm at hReq
  rw [__eo_prog_bv_extract_concat_4.eq_6 x y xs i j
    jRef xRef yRef xsRef xRef' hX hY hXs hI hJ] at hReq
  rcases bv_extract_concat4_guard_refs hReq with
    ⟨hJRef, hXRef, hYRef, hXsRef, hXRef'⟩
  subst jRef
  subst xRef
  subst yRef
  subst xsRef
  subst xRef'
  have hPCanon : P = bvExtractConcat4Prem x y xs j := hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_extract_concat4_program_body_canonical x y xs i j
    hX hY hXs hI hJ

private theorem eo_mk_apply_args_ne_stuck
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck -> f ≠ Term.Stuck ∧ x ≠ Term.Stuck := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_eq_apply_of_ne_stuck_local
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem bvExtractConcat4Tail_ne_of_body_bool
    (x y xs i j : Term) :
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    bvExtractConcat4Tail y xs ≠ Term.Stuck := by
  intro hTy
  let tail := bvExtractConcat4Tail y xs
  let ext := Term.UOp2 UserOp2.extract j i
  let inner :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.concat) x) tail
  let lhs := __eo_mk_apply ext inner
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs :=
    __eo_mk_apply ext
      (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail)
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat4ProgramBody, tail, ext, inner, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hInnerNe : inner ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hLhsNe).2
  exact (eo_mk_apply_args_ne_stuck hInnerNe).2

private theorem bvExtractConcat4Xs_list_of_body_bool
    (x y xs i j : Term) :
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true := by
  intro hTy
  have hTailNe := bvExtractConcat4Tail_ne_of_body_bool x y xs i j hTy
  exact (bv_list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.concat) xs (bvConcatTerm y (Term.Binary 0 0))
    hTailNe).1

theorem bvExtractConcat4ProgramBody_eq_term_of_type_bool
    (x y xs i j : Term) :
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    bvExtractConcat4ProgramBody x y xs i j =
      bvExtractConcat4Term x y xs i j := by
  intro hTy
  let tail := bvExtractConcat4Tail y xs
  let ext := Term.UOp2 UserOp2.extract j i
  let inner :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.concat) x) tail
  let lhs := __eo_mk_apply ext inner
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs :=
    __eo_mk_apply ext
      (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail)
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat4ProgramBody, tail, ext, inner, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hRhsNe : rhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).2
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hInnerNe : inner ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hLhsNe).2
  have hSingletonNe :
      __eo_list_singleton_elim (Term.UOp UserOp.concat) tail ≠
        Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hRhsNe).2
  have hOuterEq :
      __eo_mk_apply eqHead rhs = Term.Apply eqHead rhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hBodyNe
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) lhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hEqHeadNe
  have hLhsEq : lhs = Term.Apply ext inner :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hLhsNe
  have hInnerEq :
      inner = Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) tail :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hInnerNe
  have hRhsEq :
      rhs =
        Term.Apply ext
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail) :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hRhsNe
  calc
    bvExtractConcat4ProgramBody x y xs i j =
        __eo_mk_apply eqHead rhs := by
          simp [bvExtractConcat4ProgramBody, tail, ext, inner, lhs,
            eqHead, rhs]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply ext
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) tail)))
        (Term.Apply ext
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail)) := by
          rw [hOuterEq, hEqHeadEq, hLhsEq, hInnerEq, hRhsEq]
    _ = bvExtractConcat4Term x y xs i j := by
          simp [bvExtractConcat4Term, bvExtractConcat4Lhs,
            bvExtractConcat4Rhs, bvExtractTerm, bvConcatTerm,
            bvExtractConcat4TailElim, tail, ext]

private theorem bvExtractConcat1Whole_ne_of_body_bool
    (x xs y i j : Term) :
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    bvExtractConcat1Whole x y xs ≠ Term.Stuck := by
  intro hTy
  let ext := Term.UOp2 UserOp2.extract j i
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply ext whole
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs := Term.Apply ext x
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat1ProgramBody, ext, whole, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  exact (eo_mk_apply_args_ne_stuck hLhsNe).2

private theorem bvExtractConcat1Xs_list_of_body_bool
    (x xs y i j : Term) :
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true := by
  intro hTy
  have hWholeNe := bvExtractConcat1Whole_ne_of_body_bool x xs y i j hTy
  exact (bv_list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.concat) xs (bvExtractConcat1Seed x y)
    hWholeNe).1

theorem bvExtractConcat1ProgramBody_eq_term_of_type_bool
    (x xs y i j : Term) :
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    bvExtractConcat1ProgramBody x xs y i j =
      bvExtractConcat1Term x y xs i j := by
  intro hTy
  let ext := Term.UOp2 UserOp2.extract j i
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply ext whole
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs := Term.Apply ext x
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat1ProgramBody, ext, whole, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hOuterEq :
      __eo_mk_apply eqHead rhs = Term.Apply eqHead rhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hBodyNe
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) lhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hEqHeadNe
  have hLhsEq : lhs = Term.Apply ext whole :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hLhsNe
  calc
    bvExtractConcat1ProgramBody x xs y i j =
        __eo_mk_apply eqHead rhs := by
          simp [bvExtractConcat1ProgramBody, ext, whole, lhs,
            eqHead, rhs]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply ext whole)) (Term.Apply ext x) := by
          rw [hOuterEq, hEqHeadEq, hLhsEq]
    _ = bvExtractConcat1Term x y xs i j := by
          simp [bvExtractConcat1Term, bvExtractConcat1Lhs,
            bvExtractConcat1Rhs, bvExtractTerm, whole, ext]

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ n m,
      A = Term.Apply (Term.UOp UserOp.BitVec) n ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) m := by
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
                          exact ⟨n, m, rfl, rfl⟩
                      | _ =>
                          simp [__eo_typeof_concat] at h
                  | _ =>
                      simp [__eo_typeof_concat] at h
              | _ =>
                  simp [__eo_typeof_concat] at h
          | _ =>
              simp [__eo_typeof_concat] at h
      | _ =>
          simp [__eo_typeof_concat] at h
  | _ =>
      simp [__eo_typeof_concat] at h

private theorem eo_typeof_list_concat_rec_right_bitvec_of_result
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    ∀ w,
      __eo_typeof (__eo_list_concat_rec a z) =
        Term.Apply (Term.UOp UserOp.BitVec) w ->
      ∃ wz,
        __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) wz := by
  intro hList
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      simp [__eo_is_list] at hList
  | case2 a =>
      intro w hTy
      cases a <;> simp [__eo_list_concat_rec] at hTy <;> cases hTy
  | case3 g x y z hZ ih =>
      intro w hTy
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.concat) x y hList
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck := by
        intro hStuck
        simp [__eo_list_concat_rec, hStuck, __eo_mk_apply] at hTy
        cases hTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailConcat] at hTy
      change __eo_typeof_concat (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec y z)) =
        Term.Apply (Term.UOp UserOp.BitVec) w at hTy
      have hConcatNe :
          __eo_typeof_concat (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec y z)) ≠
            Term.Stuck := by
        rw [hTy]
        intro h
        cases h
      rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local
          hConcatNe with
        ⟨_wh, wt, _hHeadTy, hTailTy⟩
      exact ih hTailList wt hTailTy
  | case4 nil z hNil hZ hNot =>
      intro w hTy
      exact ⟨w, by simpa [__eo_list_concat_rec] using hTy⟩

private theorem eo_typeof_list_concat_right_bitvec_of_result
    (a z w : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __eo_typeof (__eo_list_concat (Term.UOp UserOp.concat) a z) =
      Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ wz,
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) wz := by
  intro hListA hListZ hTy
  have hRecTy :
      __eo_typeof (__eo_list_concat_rec a z) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    simpa [__eo_list_concat, hListA, hListZ, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] using hTy
  exact eo_typeof_list_concat_rec_right_bitvec_of_result
    a z hListA w hRecTy

private theorem bvExtractConcat1_body_smt_context
    (x xs y i j : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    ∃ wx wy wxs,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat)
          (bvExtractConcat1Seed x y) = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
  intro hXsTrans hYTrans hPremBool hBodyTy
  rcases bvExtractConcat1Prem_smt_context x j hPremBool with
    ⟨wx, hXTy, _hJTy⟩
  have hBodyEq :=
    bvExtractConcat1ProgramBody_eq_term_of_type_bool x xs y i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat1Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat1Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat1Rhs x i j))
      (by exact hTermTy) with
    ⟨hLhsNe, _hRhsNe⟩
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck
      (by exact hLhsNe) with
    ⟨wWhole, hWholeEoTy⟩
  have hXsList :=
    bvExtractConcat1Xs_list_of_body_bool x xs y i j hBodyTy
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  rcases eo_typeof_list_concat_right_bitvec_of_result
      xs (bvExtractConcat1Seed x y) wWhole hXsList hSeedList
      (by simpa [bvExtractConcat1Whole] using hWholeEoTy) with
    ⟨wSeed, hSeedEoTy⟩
  have hSeedNe :
      __eo_typeof (bvExtractConcat1Seed x y) ≠ Term.Stuck := by
    rw [hSeedEoTy]
    intro h
    cases h
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local
      (by
        change __eo_typeof_concat (__eo_typeof y)
            (__eo_typeof (bvConcatTerm x (Term.Binary 0 0))) ≠
          Term.Stuck
        exact hSeedNe) with
    ⟨wYTerm, _wInnerTerm, hYEoTy, _hInnerEoTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      y wYTerm hYTrans hYEoTy with
    ⟨wyInt, rfl, _hWy0, hYTy⟩
  let wy : Nat := native_int_to_nat wyInt
  rcases smt_typeof_concat_list_of_translation xs hXsList hXsTrans with
    ⟨wxs, hXsTy⟩
  have hWholeTy :
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
    simpa [wy] using
      smt_typeof_bv_extract_concat1_whole x y xs wx wy wxs
        hXsList hXTy hYTy hXsTy
  exact ⟨wx, wy, wxs, hXTy, by simpa [wy] using hYTy,
    hXsTy, hXsList, hSeedList, hWholeTy⟩

theorem typed_bv_extract_concat1_program_body
    (x xs y i j : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractConcat1ProgramBody x xs y i j) := by
  intro hXsTrans hYTrans hPremBool hBodyTy
  rcases bvExtractConcat1_body_smt_context x xs y i j
      hXsTrans hYTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, _hYTy, _hXsTy, _hXsList,
      _hSeedList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat1ProgramBody_eq_term_of_type_bool x xs y i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat1Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    intro h
    cases h
  have hWholeTrans :
      RuleProofs.eo_has_smt_translation (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat1Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat1Rhs x i j))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      x j i hXTrans (by
        simpa [bvExtractConcat1Rhs] using hRhsNe) with
    ⟨wRhs, h, l, _hXEoTy, hJ, hI, hwRhs0, hl0, hhRhs,
      hd0, hXSmtTy⟩
  subst j
  subst i
  rcases bv_extract_context_of_non_stuck
      (bvExtractConcat1Whole x y xs) (Term.Numeral h) (Term.Numeral l)
      hWholeTrans (by
        simpa [bvExtractConcat1Lhs] using hLhsNe) with
    ⟨wLhs, hL, lL, _hWholeEoTy, hHL, hLL, hwLhs0, hlL0,
      hhLhs, hdLhs0, hWholeSmtTy⟩
  cases hHL
  cases hLL
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractConcat1Lhs x y xs (Term.Numeral l)
              (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat1Lhs, bvExtractTerm, d] using
      smt_typeof_extract_of_context (bvExtractConcat1Whole x y xs)
        wLhs h l hWholeSmtTy hwLhs0 hl0 hhLhs hdLhs0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractConcat1Rhs x (Term.Numeral l)
              (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat1Rhs, bvExtractTerm, d] using
      smt_typeof_extract_of_context x wRhs h l hXSmtTy
        hwRhs0 hl0 hhRhs hd0
  have hTermBool :
      RuleProofs.eo_has_bool_type
        (bvExtractConcat1Term x y xs (Term.Numeral l)
          (Term.Numeral h)) := by
    unfold bvExtractConcat1Term
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (bvExtractConcat1Lhs x y xs (Term.Numeral l) (Term.Numeral h))
      (bvExtractConcat1Rhs x (Term.Numeral l) (Term.Numeral h))
      (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)
  simpa [hBodyEq]
    using hTermBool

theorem typed_bv_extract_concat4_program_body
    (x y xs i j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat4Prem x y xs j) ->
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractConcat4ProgramBody x y xs i j) := by
  intro hPremBool hBodyTy
  rcases bvExtractConcat4Prem_smt_context x y xs j hPremBool with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, _hJTy⟩
  have hBodyEq :=
    bvExtractConcat4ProgramBody_eq_term_of_type_bool x y xs i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat4Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXsList :=
    bvExtractConcat4Xs_list_of_body_bool x y xs i j hBodyTy
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList :
      __eo_is_list (Term.UOp UserOp.concat) tail = Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tail] using
      smt_typeof_bv_extract_concat4_tail y xs wy wxs
        hXsList hYTy hXsTy
  have hTailElimTy :
      __smtx_typeof (__eo_to_smt tailElim) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy)
        hTailList hTailTy
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (bvConcatTerm x tail)) =
        SmtType.BitVec (wx + (wxs + wy)) :=
    smt_typeof_bv_concat_eq x tail wx (wxs + wy) hXTy hTailTy
  have hConcatTrans :
      RuleProofs.eo_has_smt_translation (bvConcatTerm x tail) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConcatTy]
    intro h
    cases h
  have hTailElimTrans :
      RuleProofs.eo_has_smt_translation tailElim := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailElimTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat4Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat4Rhs y xs i j))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatTerm x tail) j i hConcatTrans (by
        simpa [bvExtractConcat4Lhs, bvConcatTerm, tail] using hLhsNe) with
    ⟨wTotal, h, l, _hConcatEOType, hJ, hI, hw0, hl0, hhTotal,
      hd0, hConcatSmtTy⟩
  subst j
  subst i
  rcases bv_extract_context_of_non_stuck
      tailElim (Term.Numeral h) (Term.Numeral l) hTailElimTrans (by
        simpa [bvExtractConcat4Rhs, bvExtractConcat4TailElim, tailElim]
          using hRhsNe) with
    ⟨wRhs, hR, lR, _hTailElimEOType, hHR, hLR, hwRhs0, hlR0,
      hhRhs, hdRhs0, hTailElimSmtTy⟩
  cases hHR
  cases hLR
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (bvExtractConcat4Lhs x y xs (Term.Numeral l)
            (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat4Lhs, bvExtractTerm, bvConcatTerm, tail, d] using
      smt_typeof_extract_of_context (bvConcatTerm x tail)
        wTotal h l hConcatSmtTy hw0 hl0 hhTotal hd0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (bvExtractConcat4Rhs y xs (Term.Numeral l)
            (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat4Rhs, bvExtractTerm,
      bvExtractConcat4TailElim, tailElim, d] using
      smt_typeof_extract_of_context tailElim
        wRhs h l hTailElimSmtTy hwRhs0 hl0 hhRhs hdRhs0
  have hTermBool :
      RuleProofs.eo_has_bool_type
        (bvExtractConcat4Term x y xs (Term.Numeral l)
          (Term.Numeral h)) := by
    unfold bvExtractConcat4Term
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (bvExtractConcat4Lhs x y xs (Term.Numeral l) (Term.Numeral h))
      (bvExtractConcat4Rhs y xs (Term.Numeral l) (Term.Numeral h))
      (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)
  simpa [hBodyEq]
    using hTermBool

private theorem bvConcatListCanonical_of_smt_type
    (M : SmtModel) (hM : model_wf M) :
    (t : Term) -> (w : Nat) ->
    __eo_is_list (Term.UOp UserOp.concat) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    BvConcatListCanonical M t
  | t, w, hList, hTy => by
      revert w hList hTy
      induction t using __eo_get_elements_rec.induct with
      | case1 =>
          intro w hList hTy
          simp [__eo_is_list] at hList
      | case2 f x xs ih =>
          intro w hList hTy
          have hf : f = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) f x xs hList
          subst f
          have hXsList :
              __eo_is_list (Term.UOp UserOp.concat) xs =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) x xs hList
          rcases bvConcat_args_of_bitvec_type x xs w (by
              simpa [bvConcatTerm] using hTy) with
            ⟨wx, wxs, hXTy, hXsTy⟩
          exact ⟨
            bvEvalCanonical_of_smt_type M hM x wx hXTy,
            ih wxs hXsList hXsTy⟩
      | case3 t _hNil hNot =>
          intro w hList hTy
          cases t with
          | Apply f xs =>
              cases f with
              | Apply g x =>
                  exact False.elim (hNot g x xs rfl)
              | _ =>
                  simpa [BvConcatListCanonical] using
                    bvEvalCanonical_of_smt_type M hM _ w hTy
          | _ =>
              simpa [BvConcatListCanonical] using
                bvEvalCanonical_of_smt_type M hM _ w hTy

private theorem concat_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.concat) t = Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
    exact False.elim (hNe rfl)
  case Binary w n =>
    by_cases h : w = 0 ∧ n = 0
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨true, by simp [__eo_is_list_nil]⟩
    · have hTerm : Term.Binary w n ≠ Term.Binary 0 0 := by
        intro hEq
        cases hEq
        exact h ⟨rfl, rfl⟩
      exact ⟨false, by simp [__eo_is_list_nil, hTerm]⟩
  all_goals
    exact ⟨false, by simp [__eo_is_list_nil]⟩

private theorem concat_nil_eval_binary_zero_of_is_list_nil_true
    (M : SmtModel) (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.concat) nil = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0 := by
  cases nil <;> simp [__eo_is_list_nil] at hNil ⊢
  case Binary w n =>
    split at hNil <;> simp_all
    rfl

private theorem bvConcat_right_empty_rel_of_canonical
    (M : SmtModel) (x nil : Term)
    (hx : BvEvalCanonical M x)
    (hnil : __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvConcatTerm x nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases hx with ⟨w, n, hxEval, hn0, hn1⟩
  have hModEq :
      native_mod_total n (native_int_pow2 (↑w : Int)) = n := by
    rw [natpow2_eq w]
    simpa [native_mod_total] using Int.emod_eq_of_lt hn0 hn1
  have hPow0 : native_int_pow2 (0 : native_Int) = 1 := by decide
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt nil)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hnil]
  simp [SmtEval.native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hPow0, hModEq, __smtx_model_eval_eq, native_veq]

private theorem bvConcatListCanonical_eval
    (M : SmtModel) :
    (t : Term) -> BvConcatListCanonical M t -> BvEvalCanonical M t
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case concat =>
                    rcases h.1 with ⟨wx, nx, hxEval, hx0, hx1⟩
                    rcases bvConcatListCanonical_eval M xs h.2 with
                      ⟨wxs, nxs, hXsEval, hxs0, hxs1⟩
                    let wsum : Nat := wx + wxs
                    let payload : Int :=
                      native_mod_total (native_binary_concat (↑wx) nx (↑wxs) nxs)
                        (native_int_pow2 (↑wsum : Int))
                    refine ⟨wsum, payload, ?_, ?_, ?_⟩
                    have hWidth :
                        (↑wsum : Int) = native_zplus (↑wx : Int) (↑wxs : Int) := by
                      simp [wsum, SmtEval.native_zplus]
                    have hPayload :
                        payload =
                        native_mod_total (native_binary_concat wx nx wxs nxs)
                          (native_int_pow2 (native_zplus wx wxs)) := by
                      simp [payload, hWidth]
                    · change __smtx_model_eval M
                          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt xs)) =
                        SmtValue.Binary (↑wsum) payload
                      rw [hWidth, hPayload]
                      change __smtx_model_eval M
                          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt xs)) =
                        SmtValue.Binary (native_zplus (↑wx) (↑wxs))
                          (native_mod_total
                            (native_binary_concat (↑wx) nx (↑wxs) nxs)
                            (native_int_pow2 (native_zplus (↑wx) (↑wxs))))
                      simp [__smtx_model_eval, __smtx_model_eval_concat,
                        hxEval, hXsEval]
                    · have hWidth0 : native_zleq 0 (↑wsum : Int) = true := by
                        simp [SmtEval.native_zleq]
                      have hCan :
                          native_zeq payload
                              (native_mod_total payload
                                (native_int_pow2 (↑wsum : Int))) = true := by
                        simpa [payload] using native_mod_total_canonical
                          (↑wsum : Int)
                          (native_binary_concat (↑wx) nx (↑wxs) nxs)
                      exact (bitvec_payload_range_of_canonical hWidth0 hCan).1
                    · have hWidth0 : native_zleq 0 (↑wsum : Int) = true := by
                        simp [SmtEval.native_zleq]
                      have hCan :
                          native_zeq payload
                              (native_mod_total payload
                                (native_int_pow2 (↑wsum : Int))) = true := by
                        simpa [payload] using native_mod_total_canonical
                          (↑wsum : Int)
                          (native_binary_concat (↑wx) nx (↑wxs) nxs)
                      simpa [natpow2_eq] using
                        (bitvec_payload_range_of_canonical hWidth0 hCan).2
                  all_goals
                    simpa [BvConcatListCanonical] using h
              | _ =>
                  simpa [BvConcatListCanonical] using h
          | _ =>
              simpa [BvConcatListCanonical] using h
      | _ =>
          simpa [BvConcatListCanonical] using h

theorem bvConcatSingletonElimEvalRel
    (M : SmtModel) (hM : model_wf M) (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hTy
  have hCan := bvConcatListCanonical_of_smt_type M hM c w hList hTy
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g head tail hList
          subst g
          have hHeadCan : BvEvalCanonical M head := hCan.1
          have hTailCan : BvConcatListCanonical M tail := hCan.2
          have hTailList :
              __eo_is_list (Term.UOp UserOp.concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases concat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M
                (__eo_to_smt (bvConcatTerm head tail)))
          · exact RuleProofs.smt_value_rel_symm _ _
              (bvConcat_right_empty_rel_of_canonical M head tail hHeadCan
                (concat_nil_eval_binary_zero_of_is_list_nil_true M tail hNil))
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem bvConcat_right_empty_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (wx : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hXTy
  have hCan := bvEvalCanonical_of_smt_type M hM x wx hXTy
  have hRel :=
    bvConcat_right_empty_rel_of_canonical M x (Term.Binary 0 0)
      hCan (by rfl)
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
        SmtType.BitVec wx := by
    have hTy :=
      smt_typeof_bv_concat_eq x (Term.Binary 0 0) wx 0
        hXTy smt_typeof_concat_empty
    simpa [Nat.add_zero] using hTy
  have hConcatValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0)))) =
        SmtType.BitVec wx := by
    have hNN : term_has_non_none_type
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) := by
      unfold term_has_non_none_type
      rw [hConcatTy]
      intro h
      cases h
    simpa [hConcatTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) hNN
  exact (RuleProofs.smt_value_rel_iff_eq _ _ (by
    rintro ⟨r1, r2, hLeft, _hRight⟩
    rw [hLeft] at hConcatValueTy
    cases hConcatValueTy)).mp hRel

private theorem eval_bv_extract_concat1_seed_low
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (wx wy : Nat) (h l : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wx) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Seed x y)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h)
          (Term.Numeral l))) := by
  intro hXTy hYTy hl0 hBound hd0
  let inner := bvConcatTerm x (Term.Binary 0 0)
  have hInnerTy :
      __smtx_typeof (__eo_to_smt inner) = SmtType.BitVec wx := by
    have hTy :=
      smt_typeof_bv_concat_eq x (Term.Binary 0 0) wx 0
        hXTy smt_typeof_concat_empty
    simpa [inner, Nat.add_zero] using hTy
  have hStrip :=
    eval_bv_extract_concat_low M hM y inner wy wx h l
      hYTy hInnerTy hl0 hBound hd0
  have hStrip' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm (bvExtractConcat1Seed x y)
              (Term.Numeral h) (Term.Numeral l))) =
        __smtx_model_eval M
          (__eo_to_smt (bvExtractTerm inner (Term.Numeral h)
            (Term.Numeral l))) := by
    simpa [bvExtractConcat1Seed, inner] using hStrip
  have hInnerEval :=
    bvConcat_right_empty_eval_eq M hM x wx hXTy
  rw [hStrip']
  rw [eval_extract_term M inner h l, eval_extract_term M x h l,
    hInnerEval]

private theorem eval_bv_extract_concat1_whole_low
    (M : SmtModel) (hM : model_wf M)
    (x y xs : Term) (wx wy wxs : Nat) (h l : native_Int) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wx) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Whole x y xs)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h)
          (Term.Numeral l))) := by
  intro hXsList hXTy hYTy hXsTy hl0 hBound hd0
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  have hSeedTy :=
    smt_typeof_bv_extract_concat1_seed x y wx wy hXTy hYTy
  have hSeedBound :
      native_zlt h (native_nat_to_int (wy + wx)) = true :=
    native_zlt_nat_add_right_local (extra := wy) hBound
  have hStrip :=
    eval_bv_extract_list_concat_low M hM xs
      (bvExtractConcat1Seed x y) wxs (wy + wx) h l
      hXsList hSeedList hXsTy hSeedTy hl0 hSeedBound hd0
  have hSeedLow :=
    eval_bv_extract_concat1_seed_low M hM x y wx wy h l
      hXTy hYTy hl0 hBound hd0
  calc
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Whole x y xs)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Seed x y)
            (Term.Numeral h) (Term.Numeral l))) := by
        simpa [bvExtractConcat1Whole] using hStrip
    _ = __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h)
          (Term.Numeral l))) := hSeedLow

theorem facts_bv_extract_concat1_program_body
    (M : SmtModel) (hM : model_wf M)
    (x xs y i j : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    eo_interprets M (bvExtractConcat1Prem x j) true ->
    eo_interprets M (bvExtractConcat1ProgramBody x xs y i j) true := by
  intro hXsTrans hYTrans hPremBool hBodyTy _hPremTrue
  rcases bvExtractConcat1_body_smt_context x xs y i j
      hXsTrans hYTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hXsList,
      _hSeedList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat1ProgramBody_eq_term_of_type_bool x xs y i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat1Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    intro h
    cases h
  have hWholeTrans :
      RuleProofs.eo_has_smt_translation (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat1Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat1Rhs x i j))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      x j i hXTrans (by
        simpa [bvExtractConcat1Rhs] using hRhsNe) with
    ⟨wRhs, h, l, _hXEoTy, hJ, hI, hwRhs0, hl0, hhRhs,
      hd0, hXSmtTy⟩
  subst j
  subst i
  have hBoundNat :
      native_zlt h (native_nat_to_int (native_int_to_nat wRhs)) = true := by
    have hRound := native_int_to_nat_roundtrip wRhs hwRhs0
    have hWidthEq :
        native_nat_to_int (native_int_to_nat wRhs) = wRhs := by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hRound
    simpa [hWidthEq] using hhRhs
  have hEvalEq :=
    eval_bv_extract_concat1_whole_low M hM x y xs
      (native_int_to_nat wRhs) wy wxs h l hXsList hXSmtTy
      hYTy hXsTy hl0 hBoundNat (native_zleq_of_zlt_true _ _ hd0)
  have hBool :=
    typed_bv_extract_concat1_program_body x xs y
      (Term.Numeral l) (Term.Numeral h)
      hXsTrans hYTrans (by simpa using hPremBool) hBodyTy
  rw [hBodyEq] at hBool
  rw [hBodyEq]
  unfold bvExtractConcat1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractConcat1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Whole x y xs)
            (Term.Numeral h) (Term.Numeral l))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm x (Term.Numeral h) (Term.Numeral l))))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_bv_extract_concat4_program_body
    (M : SmtModel) (hM : model_wf M)
    (x y xs i j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat4Prem x y xs j) ->
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    eo_interprets M (bvExtractConcat4Prem x y xs j) true ->
    eo_interprets M (bvExtractConcat4ProgramBody x y xs i j) true := by
  intro hPremBool hBodyTy hPremTrue
  rcases bvExtractConcat4Prem_smt_context x y xs j hPremBool with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, _hJTy⟩
  have hBodyEq :=
    bvExtractConcat4ProgramBody_eq_term_of_type_bool x y xs i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat4Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXsList :=
    bvExtractConcat4Xs_list_of_body_bool x y xs i j hBodyTy
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList :
      __eo_is_list (Term.UOp UserOp.concat) tail = Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tail] using
      smt_typeof_bv_extract_concat4_tail y xs wy wxs
        hXsList hYTy hXsTy
  have hTailElimTy :
      __smtx_typeof (__eo_to_smt tailElim) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy)
        hTailList hTailTy
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (bvConcatTerm x tail)) =
        SmtType.BitVec (wx + (wxs + wy)) :=
    smt_typeof_bv_concat_eq x tail wx (wxs + wy) hXTy hTailTy
  have hConcatTrans :
      RuleProofs.eo_has_smt_translation (bvConcatTerm x tail) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConcatTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat4Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat4Rhs y xs i j))
      (by exact hTermTy) with
    ⟨hLhsNe, _hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatTerm x tail) j i hConcatTrans (by
        simpa [bvExtractConcat4Lhs, bvConcatTerm, tail] using hLhsNe) with
    ⟨wTotal, h, l, _hConcatEOType, hJ, hI, hw0, hl0, hhTotal,
      hd0, hConcatSmtTy⟩
  subst j
  subst i
  have hTailBound :
      native_zlt h (native_nat_to_int (wxs + wy)) = true :=
    bvExtractConcat4Prem_bound M x y xs wx wy wxs h
      hXTy hYTy hXsTy (by simpa using hPremTrue)
  have hLowExtract :=
    eval_bv_extract_concat_low M hM x tail wx (wxs + wy) h l
      hXTy hTailTy hl0 hTailBound (native_zleq_of_zlt_true _ _ hd0)
  have hTailElimRel :=
    bvConcatSingletonElimEvalRel M hM tail (wxs + wy)
      hTailList hTailTy
  have hTailValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtType.BitVec (wxs + wy) := by
    have hNN : term_has_non_none_type (__eo_to_smt tail) := by
      unfold term_has_non_none_type
      rw [hTailTy]
      intro hNone
      cases hNone
    simpa [hTailTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt tail) hNN
  have hTailElimEq :
      __smtx_model_eval M (__eo_to_smt tailElim) =
        __smtx_model_eval M (__eo_to_smt tail) :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, _hElimReg, hTailReg⟩
      rw [hTailReg] at hTailValueTy
      cases hTailValueTy)).mp (by
        simpa [tailElim, bvExtractConcat4TailElim] using hTailElimRel)
  have hBool :=
    typed_bv_extract_concat4_program_body x y xs
      (Term.Numeral l) (Term.Numeral h)
      (by simpa using hPremBool) hBodyTy
  rw [hBodyEq] at hBool
  rw [hBodyEq]
  unfold bvExtractConcat4Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractConcat4Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvConcatTerm x tail)
            (Term.Numeral h) (Term.Numeral l))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm tailElim (Term.Numeral h)
            (Term.Numeral l))))
    rw [hLowExtract]
    rw [eval_extract_term M tail h l,
      eval_extract_term M tailElim h l, hTailElimEq]
    exact RuleProofs.smt_value_rel_refl _

/-! The two middle extract-over-concat cases share the same concat spine as
    cases 1 and 4.  Case 3 removes the low `x` component and shifts both
    extract indices by its width. -/

private theorem bv_extract_concat3_guard_refs
    {i x u j l iRef xRef1 uRef jRef xRef2 lRef iRef2 xRef3 body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and (__eo_eq i iRef) (__eo_eq x xRef1))
                    (__eo_eq u uRef))
                  (__eo_eq j jRef))
                (__eo_eq x xRef2))
              (__eo_eq l lRef))
            (__eo_eq i iRef2))
          (__eo_eq x xRef3))
        (Term.Boolean true) body ≠ Term.Stuck ->
    iRef = i ∧ xRef1 = x ∧ uRef = u ∧ jRef = j ∧
      xRef2 = x ∧ lRef = l ∧ iRef2 = i ∧ xRef3 = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG7, hX3⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hI2⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hL⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hX2⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hJ⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hU⟩
  rcases bv_extract_support_and_true hG2 with ⟨hI, hX1⟩
  exact ⟨(bv_extract_support_eq_true hI).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hU).symm,
    (bv_extract_support_eq_true hJ).symm,
    (bv_extract_support_eq_true hX2).symm,
    (bv_extract_support_eq_true hL).symm,
    (bv_extract_support_eq_true hI2).symm,
    (bv_extract_support_eq_true hX3).symm⟩

private theorem bv_extract_concat3_premise_shape
    (x y xs i j u l P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> xs ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck -> u ≠ Term.Stuck ->
    l ≠ Term.Stuck ->
    bvExtractConcat3Program x y xs i j u l P1 P2 P3 ≠ Term.Stuck ->
    ∃ iRef xRef1 uRef jRef xRef2 lRef iRef2 xRef3,
      P1 = bvExtractConcat3PremI xRef1 iRef ∧
      P2 = bvExtractConcat3PremU xRef2 jRef uRef ∧
      P3 = bvExtractConcat3PremL xRef3 iRef2 lRef := by
  intro hX hY hXs hI hJ hU hL hProg
  by_cases hShape :
      ∃ iRef xRef1 uRef jRef xRef2 lRef iRef2 xRef3,
        P1 = bvExtractConcat3PremI xRef1 iRef ∧
        P2 = bvExtractConcat3PremU xRef2 jRef uRef ∧
        P3 = bvExtractConcat3PremL xRef3 iRef2 lRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_concat_3.eq_9
      x y xs i j u l (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hY hXs hI hJ hU hL (by
        intro iRef xRef1 uRef jRef xRef2 lRef iRef2 xRef3
          hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨iRef, xRef1, uRef, jRef, xRef2, lRef, iRef2, xRef3,
            rfl, rfl, rfl⟩)

private theorem bv_extract_concat3_program_body_canonical
    (x y xs i j u l : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> xs ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck -> u ≠ Term.Stuck ->
    l ≠ Term.Stuck ->
    bvExtractConcat3Program x y xs i j u l
        (bvExtractConcat3PremI x i)
        (bvExtractConcat3PremU x j u)
        (bvExtractConcat3PremL x i l) =
      bvExtractConcat3ProgramBody x y xs i j u l := by
  intro hX hY hXs hI hJ hU hL
  unfold bvExtractConcat3Program bvExtractConcat3PremI
    bvExtractConcat3PremU bvExtractConcat3PremL
    bvExtractConcat3ProgramBody bvExtractConcat1Whole
    bvExtractConcat1Seed bvExtractConcat4TailElim bvExtractConcat4Tail
    bvConcatTerm
  rw [__eo_prog_bv_extract_concat_3.eq_8
    x y xs i j u l i x u j x l i x hX hY hXs hI hJ hU hL]
  simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hY, hXs, hI, hJ, hU, hL]

theorem bvExtractConcat3Program_normalize
    (x y xs i j u l P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation u ->
    RuleProofs.eo_has_smt_translation l ->
    bvExtractConcat3Program x y xs i j u l P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvExtractConcat3PremI x i ∧
      P2 = bvExtractConcat3PremU x j u ∧
      P3 = bvExtractConcat3PremL x i l ∧
      bvExtractConcat3Program x y xs i j u l P1 P2 P3 =
        bvExtractConcat3ProgramBody x y xs i j u l := by
  intro hXTrans hYTrans hXsTrans hITrans hJTrans hUTrans hLTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hU := RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
  have hL := RuleProofs.term_ne_stuck_of_has_smt_translation l hLTrans
  rcases bv_extract_concat3_premise_shape x y xs i j u l P1 P2 P3
      hX hY hXs hI hJ hU hL hProg with
    ⟨iRef, xRef1, uRef, jRef, xRef2, lRef, iRef2, xRef3,
      hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvExtractConcat3Program bvExtractConcat3PremI
    bvExtractConcat3PremU bvExtractConcat3PremL at hReq
  rw [__eo_prog_bv_extract_concat_3.eq_8
    x y xs i j u l iRef xRef1 uRef jRef xRef2 lRef iRef2 xRef3
    hX hY hXs hI hJ hU hL] at hReq
  rcases bv_extract_concat3_guard_refs hReq with
    ⟨hIRef, hXRef1, hURef, hJRef, hXRef2, hLRef, hIRef2, hXRef3⟩
  subst iRef
  subst xRef1
  subst uRef
  subst jRef
  subst xRef2
  subst lRef
  subst iRef2
  subst xRef3
  have hP1Canon : P1 = bvExtractConcat3PremI x i := hP1
  have hP2Canon : P2 = bvExtractConcat3PremU x j u := hP2
  have hP3Canon : P3 = bvExtractConcat3PremL x i l := hP3
  refine ⟨hP1Canon, hP2Canon, hP3Canon, ?_⟩
  rw [hP1Canon, hP2Canon, hP3Canon]
  exact bv_extract_concat3_program_body_canonical
    x y xs i j u l hX hY hXs hI hJ hU hL

private theorem bv_extract_concat2_guard_refs
    (x xs y i j u1 u2 iRef xRef1 jRef xRef2 u1Ref jRef2 xRef3
      u2Ref xRef4 body : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and
                      (__eo_and (__eo_eq i iRef) (__eo_eq x xRef1))
                      (__eo_eq j jRef))
                    (__eo_eq x xRef2))
                  (__eo_eq u1 u1Ref))
                (__eo_eq j jRef2))
              (__eo_eq x xRef3))
            (__eo_eq u2 u2Ref))
          (__eo_eq x xRef4))
        (Term.Boolean true) body ≠ Term.Stuck ->
    iRef = i ∧ xRef1 = x ∧ jRef = j ∧ xRef2 = x ∧
      u1Ref = u1 ∧ jRef2 = j ∧ xRef3 = x ∧
      u2Ref = u2 ∧ xRef4 = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG8, hX4⟩
  rcases bv_extract_support_and_true hG8 with ⟨hG7, hU2⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hX3⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hJ2⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hU1⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hX2⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hJ⟩
  rcases bv_extract_support_and_true hG2 with ⟨hI, hX1⟩
  exact ⟨(bv_extract_support_eq_true hI).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hJ).symm,
    (bv_extract_support_eq_true hX2).symm,
    (bv_extract_support_eq_true hU1).symm,
    (bv_extract_support_eq_true hJ2).symm,
    (bv_extract_support_eq_true hX3).symm,
    (bv_extract_support_eq_true hU2).symm,
    (bv_extract_support_eq_true hX4).symm⟩

private theorem bv_extract_concat2_premise_shape
    (x xs y i j u1 u2 P1 P2 P3 P4 : Term) :
    x ≠ Term.Stuck -> xs ≠ Term.Stuck -> y ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck -> u1 ≠ Term.Stuck ->
    u2 ≠ Term.Stuck ->
    bvExtractConcat2Program x xs y i j u1 u2 P1 P2 P3 P4 ≠ Term.Stuck ->
    ∃ iRef xRef1 jRef xRef2 u1Ref jRef2 xRef3 u2Ref xRef4,
      P1 = bvExtractConcat2PremI xRef1 iRef ∧
      P2 = bvExtractConcat2PremJ xRef2 jRef ∧
      P3 = bvExtractConcat2PremU1 xRef3 jRef2 u1Ref ∧
      P4 = bvExtractConcat2PremU2 xRef4 u2Ref := by
  intro hX hXs hY hI hJ hU1 hU2 hProg
  by_cases hShape :
      ∃ iRef xRef1 jRef xRef2 u1Ref jRef2 xRef3 u2Ref xRef4,
        P1 = bvExtractConcat2PremI xRef1 iRef ∧
        P2 = bvExtractConcat2PremJ xRef2 jRef ∧
        P3 = bvExtractConcat2PremU1 xRef3 jRef2 u1Ref ∧
        P4 = bvExtractConcat2PremU2 xRef4 u2Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_concat_2.eq_9
      x xs y i j u1 u2 (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      (Proof.pf P4) hX hXs hY hI hJ hU1 hU2 (by
        intro iRef xRef1 jRef xRef2 u1Ref jRef2 xRef3 u2Ref xRef4
          hP1 hP2 hP3 hP4
        cases hP1
        cases hP2
        cases hP3
        cases hP4
        exact hShape
          ⟨iRef, xRef1, jRef, xRef2, u1Ref, jRef2, xRef3, u2Ref,
            xRef4, rfl, rfl, rfl, rfl⟩)

private theorem bv_extract_concat2_program_body_canonical
    (x xs y i j u1 u2 : Term) :
    x ≠ Term.Stuck -> xs ≠ Term.Stuck -> y ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck -> u1 ≠ Term.Stuck ->
    u2 ≠ Term.Stuck ->
    bvExtractConcat2Program x xs y i j u1 u2
        (bvExtractConcat2PremI x i)
        (bvExtractConcat2PremJ x j)
        (bvExtractConcat2PremU1 x j u1)
        (bvExtractConcat2PremU2 x u2) =
      bvExtractConcat2ProgramBody x xs y i j u1 u2 := by
  intro hX hXs hY hI hJ hU1 hU2
  unfold bvExtractConcat2Program bvExtractConcat2PremI
    bvExtractConcat2PremJ bvExtractConcat2PremU1 bvExtractConcat2PremU2
    bvExtractConcat2ProgramBody bvExtractConcat1Whole
    bvExtractConcat1Seed bvExtractConcat4TailElim bvExtractConcat4Tail
    bvConcatTerm
  rw [__eo_prog_bv_extract_concat_2.eq_8
    x xs y i j u1 u2 i x j x u1 j x u2 x
    hX hXs hY hI hJ hU1 hU2]
  simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hXs, hY, hI, hJ, hU1, hU2]

theorem bvExtractConcat2Program_normalize
    (x xs y i j u1 u2 P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation u1 ->
    RuleProofs.eo_has_smt_translation u2 ->
    bvExtractConcat2Program x xs y i j u1 u2 P1 P2 P3 P4 ≠ Term.Stuck ->
    P1 = bvExtractConcat2PremI x i ∧
      P2 = bvExtractConcat2PremJ x j ∧
      P3 = bvExtractConcat2PremU1 x j u1 ∧
      P4 = bvExtractConcat2PremU2 x u2 ∧
      bvExtractConcat2Program x xs y i j u1 u2 P1 P2 P3 P4 =
        bvExtractConcat2ProgramBody x xs y i j u1 u2 := by
  intro hXTrans hXsTrans hYTrans hITrans hJTrans hU1Trans hU2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hU1 := RuleProofs.term_ne_stuck_of_has_smt_translation u1 hU1Trans
  have hU2 := RuleProofs.term_ne_stuck_of_has_smt_translation u2 hU2Trans
  rcases bv_extract_concat2_premise_shape x xs y i j u1 u2 P1 P2 P3 P4
      hX hXs hY hI hJ hU1 hU2 hProg with
    ⟨iRef, xRef1, jRef, xRef2, u1Ref, jRef2, xRef3, u2Ref, xRef4,
      hP1, hP2, hP3, hP4⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4] at hReq
  unfold bvExtractConcat2Program bvExtractConcat2PremI
    bvExtractConcat2PremJ bvExtractConcat2PremU1 bvExtractConcat2PremU2 at hReq
  rw [__eo_prog_bv_extract_concat_2.eq_8
    x xs y i j u1 u2 iRef xRef1 jRef xRef2 u1Ref jRef2 xRef3
    u2Ref xRef4 hX hXs hY hI hJ hU1 hU2] at hReq
  rcases bv_extract_concat2_guard_refs x xs y i j u1 u2 iRef xRef1
      jRef xRef2 u1Ref jRef2 xRef3 u2Ref xRef4 _ hReq with
    ⟨hIRef, hXRef1, hJRef, hXRef2, hU1Ref, hJRef2, hXRef3,
      hU2Ref, hXRef4⟩
  subst iRef
  subst xRef1
  subst jRef
  subst xRef2
  subst u1Ref
  subst jRef2
  subst xRef3
  subst u2Ref
  subst xRef4
  refine ⟨hP1, hP2, hP3, hP4, ?_⟩
  rw [hP1, hP2, hP3, hP4]
  exact bv_extract_concat2_program_body_canonical
    x xs y i j u1 u2 hX hXs hY hI hJ hU1 hU2

private theorem bvExtractConcat2Whole_ne_of_body_bool
    (x xs y i j u1 u2 : Term) :
    __eo_typeof (bvExtractConcat2ProgramBody x xs y i j u1 u2) = Term.Bool ->
    bvExtractConcat1Whole x y xs ≠ Term.Stuck := by
  intro hTy
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply (Term.UOp2 UserOp2.extract j i) whole
  let high := __eo_mk_apply (Term.UOp2 UserOp2.extract u1 (Term.Numeral 0))
    (bvExtractConcat4TailElim y xs)
  let low := Term.Apply (Term.UOp2 UserOp2.extract u2 i) x
  let rhs := __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) high)
    (bvConcatTerm low (Term.Binary 0 0))
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat2ProgramBody, whole, lhs, high, low, rhs,
      eqHead] using hNe
  have hEqHeadNe := (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe := (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  exact (eo_mk_apply_args_ne_stuck hLhsNe).2

private theorem bvExtractConcat2Xs_list_of_body_bool
    (x xs y i j u1 u2 : Term) :
    __eo_typeof (bvExtractConcat2ProgramBody x xs y i j u1 u2) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true := by
  intro hTy
  have hWholeNe :=
    bvExtractConcat2Whole_ne_of_body_bool x xs y i j u1 u2 hTy
  exact (bv_list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.concat) xs (bvExtractConcat1Seed x y)
    hWholeNe).1

private theorem bvExtractConcat2ProgramBody_eq_term_of_type_bool
    (x xs y i j u1 u2 : Term) :
    __eo_typeof (bvExtractConcat2ProgramBody x xs y i j u1 u2) = Term.Bool ->
    bvExtractConcat2ProgramBody x xs y i j u1 u2 =
      bvExtractConcat2Term x y xs i j u1 u2 := by
  intro hTy
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply (Term.UOp2 UserOp2.extract j i) whole
  let high := __eo_mk_apply (Term.UOp2 UserOp2.extract u1 (Term.Numeral 0))
    (bvExtractConcat4TailElim y xs)
  let low := Term.Apply (Term.UOp2 UserOp2.extract u2 i) x
  let inner := bvConcatTerm low (Term.Binary 0 0)
  let concatHead := __eo_mk_apply (Term.UOp UserOp.concat) high
  let rhs := __eo_mk_apply concatHead inner
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat2ProgramBody, whole, lhs, high, low, inner,
      concatHead, rhs, eqHead] using hNe
  have hEqHeadNe := (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe := (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hRhsNe := (eo_mk_apply_args_ne_stuck hBodyNe).2
  have hConcatHeadNe := (eo_mk_apply_args_ne_stuck hRhsNe).1
  have hHighNe := (eo_mk_apply_args_ne_stuck hConcatHeadNe).2
  have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck_local hBodyNe
  have hEqHeadEq := eo_mk_apply_eq_apply_of_ne_stuck_local hEqHeadNe
  have hLhsEq := eo_mk_apply_eq_apply_of_ne_stuck_local hLhsNe
  have hRhsEq := eo_mk_apply_eq_apply_of_ne_stuck_local hRhsNe
  have hConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck_local hConcatHeadNe
  have hHighEq := eo_mk_apply_eq_apply_of_ne_stuck_local hHighNe
  calc
    bvExtractConcat2ProgramBody x xs y i j u1 u2 =
        __eo_mk_apply eqHead rhs := by
          simp [bvExtractConcat2ProgramBody, whole, lhs, high, low,
            inner, concatHead, rhs, eqHead]
    _ = Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp2 UserOp2.extract j i) whole))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.concat)
              (Term.Apply (Term.UOp2 UserOp2.extract u1 (Term.Numeral 0))
                (bvExtractConcat4TailElim y xs)))
            inner) := by
          rw [hOuterEq]
          change Term.Apply (__eo_mk_apply (Term.UOp UserOp.eq) lhs) rhs = _
          rw [hEqHeadEq]
          simp only [lhs, rhs]
          rw [hLhsEq, hRhsEq]
          simp only [concatHead]
          rw [hConcatHeadEq]
          simp only [high]
          rw [hHighEq]
    _ = bvExtractConcat2Term x y xs i j u1 u2 := by
          simp [bvExtractConcat2Term, bvExtractConcat2Lhs,
            bvExtractConcat2Rhs, bvExtractConcat2High,
            bvExtractConcat2Low, bvExtractTerm, bvConcatTerm,
            whole, low, inner]

private theorem bvExtractConcat2PremI_smt_context
    (x i : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat2PremI x i) ->
    ∃ wx,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt i) = SmtType.Int := by
  intro hPremBool
  let cond := Term.Apply (Term.Apply (Term.UOp UserOp.lt) i)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        cond (Term.Boolean true) (by
          simpa [bvExtractConcat2PremI, cond] using hPremBool) with
      ⟨hEqTy, _hNN⟩
    exact hEqTy
  change __smtx_typeof
      (SmtTerm.lt (__eo_to_smt i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
    SmtType.Bool at hCondTy
  have hLtNN : term_has_non_none_type
      (SmtTerm.lt (__eo_to_smt i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) := by
    unfold term_has_non_none_type
    rw [hCondTy]
    intro h
    cases h
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
      (typeof_lt_eq (__eo_to_smt i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      hLtNN with hArgs | hArgs
  · rcases smt_typeof_bvsize_int_inv x hArgs.2 with ⟨wx, hXTy⟩
    exact ⟨wx, hXTy, hArgs.1⟩
  · exact False.elim (smt_typeof_bvsize_ne_real x hArgs.2)

private theorem bvExtractConcat2_body_smt_context
    (x xs y i j u1 u2 : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_bool_type (bvExtractConcat2PremI x i) ->
    __eo_typeof (bvExtractConcat2ProgramBody x xs y i j u1 u2) = Term.Bool ->
    ∃ wx wy wxs,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
  intro hYTrans hXsTrans hPremBool hBodyTy
  rcases bvExtractConcat2PremI_smt_context x i hPremBool with
    ⟨wx, hXTy, _hITy⟩
  have hBodyEq :=
    bvExtractConcat2ProgramBody_eq_term_of_type_bool x xs y i j u1 u2 hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat2Term x y xs i j u1 u2) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat2Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat2Rhs x y xs i u1 u2))
      (by exact hTermTy) with
    ⟨hLhsNe, _hRhsNe⟩
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck
      (by exact hLhsNe) with
    ⟨wWhole, hWholeEoTy⟩
  have hXsList :=
    bvExtractConcat2Xs_list_of_body_bool x xs y i j u1 u2 hBodyTy
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  rcases eo_typeof_list_concat_right_bitvec_of_result
      xs (bvExtractConcat1Seed x y) wWhole hXsList hSeedList
      (by simpa [bvExtractConcat1Whole] using hWholeEoTy) with
    ⟨wSeed, hSeedEoTy⟩
  have hSeedNe : __eo_typeof (bvExtractConcat1Seed x y) ≠ Term.Stuck := by
    rw [hSeedEoTy]
    intro h
    cases h
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local (by
      change __eo_typeof_concat (__eo_typeof y)
          (__eo_typeof (bvConcatTerm x (Term.Binary 0 0))) ≠ Term.Stuck
      exact hSeedNe) with
    ⟨wYTerm, _wInnerTerm, hYEoTy, _hInnerEoTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      y wYTerm hYTrans hYEoTy with
    ⟨wyInt, rfl, _hWy0, hYTy⟩
  let wy := native_int_to_nat wyInt
  rcases smt_typeof_concat_list_of_translation xs hXsList hXsTrans with
    ⟨wxs, hXsTy⟩
  have hWholeTy :
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
    simpa [wy] using
      smt_typeof_bv_extract_concat1_whole x y xs wx wy wxs
        hXsList hXTy hYTy hXsTy
  exact ⟨wx, wy, wxs, hXTy, by simpa [wy] using hYTy,
    hXsTy, hXsList, hWholeTy⟩

theorem typed_bv_extract_concat2_program_body
    (x xs y i j u1 u2 : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_bool_type (bvExtractConcat2PremI x i) ->
    __eo_typeof (bvExtractConcat2ProgramBody x xs y i j u1 u2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractConcat2ProgramBody x xs y i j u1 u2) := by
  intro hYTrans hXsTrans hPremBool hBodyTy
  rcases bvExtractConcat2_body_smt_context x xs y i j u1 u2
      hYTrans hXsTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hXsList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat2ProgramBody_eq_term_of_type_bool x xs y i j u1 u2 hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat2Term x y xs i j u1 u2) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    intro h
    cases h
  have hWholeTrans : RuleProofs.eo_has_smt_translation
      (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList : __eo_is_list (Term.UOp UserOp.concat) tail =
      Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tail] using smt_typeof_bv_extract_concat4_tail y xs wy wxs
      hXsList hYTy hXsTy
  have hTailElimTy : __smtx_typeof (__eo_to_smt tailElim) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy) hTailList hTailTy
  have hTailElimTrans : RuleProofs.eo_has_smt_translation tailElim := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailElimTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat2Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat2Rhs x y xs i u1 u2))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvExtractConcat1Whole x y xs) j i hWholeTrans
      (by simpa [bvExtractConcat2Lhs] using hLhsNe) with
    ⟨wLhs, jv, iv, _hWholeEoTy, hJ, hI, hwLhs0, hi0,
      hjw, hdLhs0, hWholeSmtTy⟩
  subst j
  subst i
  let high := bvExtractConcat2High y xs u1
  let low := bvExtractConcat2Low x (Term.Numeral iv) u2
  let inner := bvConcatTerm low (Term.Binary 0 0)
  have hRhsConcatNe :
      __eo_typeof_concat (__eo_typeof high) (__eo_typeof inner) ≠
        Term.Stuck := by
    exact hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsConcatNe with
    ⟨wHighEo, wInnerEo, hHighEoTy, hInnerEoTy⟩
  have hHighNe : __eo_typeof high ≠ Term.Stuck := by
    rw [hHighEoTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck tailElim u1 (Term.Numeral 0)
      hTailElimTrans (by
        simpa [high, bvExtractConcat2High, tailElim] using hHighNe) with
    ⟨wHighSrc, u1v, zv, _hTailEoTy, hU1, hZero, hwHigh0, hz0,
      hu1w, hdHigh0, hTailSmtTy⟩
  subst u1
  injection hZero with hZeroVal
  subst zv
  have hInnerNe : __eo_typeof inner ≠ Term.Stuck := by
    rw [hInnerEoTy]
    intro h
    cases h
  have hInnerConcatNe :
      __eo_typeof_concat (__eo_typeof low)
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    exact hInnerNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerConcatNe with
    ⟨wLowEo, wEmptyEo, hLowEoTy, _hEmptyEoTy⟩
  have hLowNe : __eo_typeof low ≠ Term.Stuck := by
    rw [hLowEoTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x u2 (Term.Numeral iv)
      hXTrans (by
        simpa [low, bvExtractConcat2Low] using hLowNe) with
    ⟨wLowSrc, u2v, iv2, _hXEoTy, hU2, hILow, hwLow0, hiLow0,
      hu2w, hdLow0, hXSmtTy⟩
  subst u2
  injection hILow with hIV
  subst iv2
  let dLhs := native_zplus (native_zplus jv 1) (native_zneg iv)
  let dHigh := native_zplus (native_zplus u1v 1) (native_zneg 0)
  let dLow := native_zplus (native_zplus u2v 1) (native_zneg iv)
  have hLhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractConcat2Lhs x y xs (Term.Numeral iv)
              (Term.Numeral jv))) =
        SmtType.BitVec (native_int_to_nat dLhs) := by
    simpa [bvExtractConcat2Lhs, dLhs] using
      smt_typeof_extract_of_context (bvExtractConcat1Whole x y xs)
        wLhs jv iv hWholeSmtTy hwLhs0 hi0 hjw hdLhs0
  have hHighSmtTy : __smtx_typeof (__eo_to_smt high) =
      SmtType.BitVec (native_int_to_nat dHigh) := by
    simpa [high, bvExtractConcat2High, tailElim, dHigh] using
      smt_typeof_extract_of_context tailElim wHighSrc u1v 0
        hTailSmtTy hwHigh0 hz0 hu1w hdHigh0
  have hLowSmtTy : __smtx_typeof (__eo_to_smt low) =
      SmtType.BitVec (native_int_to_nat dLow) := by
    simpa [low, bvExtractConcat2Low, dLow] using
      smt_typeof_extract_of_context x wLowSrc u2v iv hXSmtTy
        hwLow0 hiLow0 hu2w hdLow0
  have hInnerSmtTy : __smtx_typeof (__eo_to_smt inner) =
      SmtType.BitVec (native_int_to_nat dLow + 0) := by
    simpa [inner] using smt_typeof_bv_concat_eq low (Term.Binary 0 0)
      (native_int_to_nat dLow) 0 hLowSmtTy smt_typeof_concat_empty
  have hRhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractConcat2Rhs x y xs (Term.Numeral iv)
              (Term.Numeral u1v) (Term.Numeral u2v))) =
        SmtType.BitVec
          (native_int_to_nat dHigh + (native_int_to_nat dLow + 0)) := by
    simpa [bvExtractConcat2Rhs, high, low, inner] using
      smt_typeof_bv_concat_eq high inner (native_int_to_nat dHigh)
        (native_int_to_nat dLow + 0) hHighSmtTy hInnerSmtTy
  let lhs := bvExtractConcat2Lhs x y xs (Term.Numeral iv)
    (Term.Numeral jv)
  let rhs := bvExtractConcat2Rhs x y xs (Term.Numeral iv)
    (Term.Numeral u1v) (Term.Numeral u2v)
  have hLhsTrans : RuleProofs.eo_has_smt_translation lhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt lhs) =
        SmtType.BitVec (native_int_to_nat dLhs) by
      simpa [lhs] using hLhsSmtTy]
    intro h
    cases h
  have hRhsTrans : RuleProofs.eo_has_smt_translation rhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt rhs) =
        SmtType.BitVec
          (native_int_to_nat dHigh + (native_int_to_nat dLow + 0)) by
      simpa [rhs] using hRhsSmtTy]
    intro h
    cases h
  have hEOTypeEq : __eo_typeof lhs = __eo_typeof rhs := by
    apply RuleProofs.eo_typeof_eq_bool_operands_eq
    exact hTermTy
  have hLhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      lhs (__eo_typeof lhs) (__eo_to_smt lhs) rfl hLhsTrans rfl
  have hRhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      rhs (__eo_typeof rhs) (__eo_to_smt rhs) rfl hRhsTrans rfl
  have hTermBool : RuleProofs.eo_has_bool_type
      (bvExtractConcat2Term x y xs (Term.Numeral iv) (Term.Numeral jv)
        (Term.Numeral u1v) (Term.Numeral u2v)) := by
    unfold bvExtractConcat2Term
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
      (by rw [show __smtx_typeof (__eo_to_smt lhs) =
          SmtType.BitVec (native_int_to_nat dLhs) by
        simpa [lhs] using hLhsSmtTy]
          simp)
  simpa [hBodyEq] using hTermBool

private theorem bvExtractConcat3Whole_ne_of_body_bool
    (x y xs i j u l : Term) :
    __eo_typeof (bvExtractConcat3ProgramBody x y xs i j u l) = Term.Bool ->
    bvExtractConcat1Whole x y xs ≠ Term.Stuck := by
  intro hTy
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply (Term.UOp2 UserOp2.extract j i) whole
  let rhs := __eo_mk_apply (Term.UOp2 UserOp2.extract u l)
    (bvExtractConcat4TailElim y xs)
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat3ProgramBody, whole, lhs, rhs, eqHead] using hNe
  have hEqHeadNe := (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe := (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  exact (eo_mk_apply_args_ne_stuck hLhsNe).2

private theorem bvExtractConcat3Xs_list_of_body_bool
    (x y xs i j u l : Term) :
    __eo_typeof (bvExtractConcat3ProgramBody x y xs i j u l) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true := by
  intro hTy
  have hWholeNe :=
    bvExtractConcat3Whole_ne_of_body_bool x y xs i j u l hTy
  exact (bv_list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.concat) xs (bvExtractConcat1Seed x y)
    hWholeNe).1

private theorem bvExtractConcat3ProgramBody_eq_term_of_type_bool
    (x y xs i j u l : Term) :
    __eo_typeof (bvExtractConcat3ProgramBody x y xs i j u l) = Term.Bool ->
    bvExtractConcat3ProgramBody x y xs i j u l =
      bvExtractConcat3Term x y xs i j u l := by
  intro hTy
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply (Term.UOp2 UserOp2.extract j i) whole
  let rhs := __eo_mk_apply (Term.UOp2 UserOp2.extract u l)
    (bvExtractConcat4TailElim y xs)
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  have hBodyNe : __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat3ProgramBody, whole, lhs, rhs, eqHead] using hNe
  have hEqHeadNe := (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe := (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hRhsNe := (eo_mk_apply_args_ne_stuck hBodyNe).2
  have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck_local hBodyNe
  have hEqHeadEq := eo_mk_apply_eq_apply_of_ne_stuck_local hEqHeadNe
  have hLhsEq := eo_mk_apply_eq_apply_of_ne_stuck_local hLhsNe
  have hRhsEq := eo_mk_apply_eq_apply_of_ne_stuck_local hRhsNe
  calc
    bvExtractConcat3ProgramBody x y xs i j u l =
        __eo_mk_apply eqHead rhs := by
          simp [bvExtractConcat3ProgramBody, whole, lhs, rhs, eqHead]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp2 UserOp2.extract j i) whole))
          (Term.Apply (Term.UOp2 UserOp2.extract u l)
          (bvExtractConcat4TailElim y xs)) := by
          rw [hOuterEq]
          change Term.Apply (__eo_mk_apply (Term.UOp UserOp.eq) lhs) rhs = _
          rw [hEqHeadEq]
          change Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (__eo_mk_apply (Term.UOp2 UserOp2.extract j i) whole))
            (__eo_mk_apply (Term.UOp2 UserOp2.extract u l)
              (bvExtractConcat4TailElim y xs)) = _
          rw [hLhsEq, hRhsEq]
    _ = bvExtractConcat3Term x y xs i j u l := by
          simp [bvExtractConcat3Term, bvExtractConcat3Lhs,
            bvExtractConcat3Rhs, bvExtractTerm, whole]

private theorem bvExtractConcat3PremI_smt_context
    (x i : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat3PremI x i) ->
    ∃ wx,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt i) = SmtType.Int := by
  intro hPremBool
  let cond := Term.Apply (Term.Apply (Term.UOp UserOp.geq) i)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        cond (Term.Boolean true) (by
          simpa [bvExtractConcat3PremI, cond] using hPremBool) with
      ⟨hEqTy, _hNN⟩
    exact hEqTy
  change __smtx_typeof
      (SmtTerm.geq (__eo_to_smt i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
    SmtType.Bool at hCondTy
  have hGeqNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) := by
    unfold term_has_non_none_type
    rw [hCondTy]
    intro h
    cases h
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      hGeqNN with hArgs | hArgs
  · rcases smt_typeof_bvsize_int_inv x hArgs.2 with ⟨wx, hXTy⟩
    exact ⟨wx, hXTy, hArgs.1⟩
  · exact False.elim (smt_typeof_bvsize_ne_real x hArgs.2)

private theorem bvExtractConcat3_body_smt_context
    (x y xs i j u l : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_bool_type (bvExtractConcat3PremI x i) ->
    __eo_typeof (bvExtractConcat3ProgramBody x y xs i j u l) = Term.Bool ->
    ∃ wx wy wxs,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
  intro hYTrans hXsTrans hPremBool hBodyTy
  rcases bvExtractConcat3PremI_smt_context x i hPremBool with
    ⟨wx, hXTy, _hITy⟩
  have hBodyEq :=
    bvExtractConcat3ProgramBody_eq_term_of_type_bool x y xs i j u l hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat3Term x y xs i j u l) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat3Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat3Rhs y xs u l))
      (by exact hTermTy) with
    ⟨hLhsNe, _hRhsNe⟩
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck
      (by exact hLhsNe) with
    ⟨wWhole, hWholeEoTy⟩
  have hXsList :=
    bvExtractConcat3Xs_list_of_body_bool x y xs i j u l hBodyTy
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  rcases eo_typeof_list_concat_right_bitvec_of_result
      xs (bvExtractConcat1Seed x y) wWhole hXsList hSeedList
      (by simpa [bvExtractConcat1Whole] using hWholeEoTy) with
    ⟨wSeed, hSeedEoTy⟩
  have hSeedNe : __eo_typeof (bvExtractConcat1Seed x y) ≠ Term.Stuck := by
    rw [hSeedEoTy]
    intro h
    cases h
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local (by
      change __eo_typeof_concat (__eo_typeof y)
          (__eo_typeof (bvConcatTerm x (Term.Binary 0 0))) ≠ Term.Stuck
      exact hSeedNe) with
    ⟨wYTerm, _wInnerTerm, hYEoTy, _hInnerEoTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      y wYTerm hYTrans hYEoTy with
    ⟨wyInt, rfl, _hWy0, hYTy⟩
  let wy := native_int_to_nat wyInt
  rcases smt_typeof_concat_list_of_translation xs hXsList hXsTrans with
    ⟨wxs, hXsTy⟩
  have hWholeTy :
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
    simpa [wy] using
      smt_typeof_bv_extract_concat1_whole x y xs wx wy wxs
        hXsList hXTy hYTy hXsTy
  exact ⟨wx, wy, wxs, hXTy, by simpa [wy] using hYTy,
    hXsTy, hXsList, hWholeTy⟩

theorem typed_bv_extract_concat3_program_body
    (x y xs i j u l : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_bool_type (bvExtractConcat3PremI x i) ->
    __eo_typeof (bvExtractConcat3ProgramBody x y xs i j u l) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractConcat3ProgramBody x y xs i j u l) := by
  intro hYTrans hXsTrans hPremBool hBodyTy
  rcases bvExtractConcat3_body_smt_context x y xs i j u l
      hYTrans hXsTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, _hXTy, hYTy, hXsTy, hXsList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat3ProgramBody_eq_term_of_type_bool x y xs i j u l hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat3Term x y xs i j u l) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hWholeTrans : RuleProofs.eo_has_smt_translation
      (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList : __eo_is_list (Term.UOp UserOp.concat) tail =
      Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tail] using smt_typeof_bv_extract_concat4_tail y xs wy wxs
      hXsList hYTy hXsTy
  have hTailElimTy : __smtx_typeof (__eo_to_smt tailElim) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy) hTailList hTailTy
  have hTailElimTrans : RuleProofs.eo_has_smt_translation tailElim := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailElimTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat3Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat3Rhs y xs u l))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvExtractConcat1Whole x y xs) j i hWholeTrans
      (by simpa [bvExtractConcat3Lhs] using hLhsNe) with
    ⟨wLhs, hv, iv, _hWholeEoTy, hJ, hI, hwLhs0, hi0,
      hjw, hdLhs0, hWholeSmtTy⟩
  rcases bv_extract_context_of_non_stuck tailElim u l hTailElimTrans
      (by simpa [bvExtractConcat3Rhs, tailElim] using hRhsNe) with
    ⟨wRhs, uv, lv, _hTailEoTy, hU, hL, hwRhs0, hl0,
      huw, hdRhs0, hTailSmtTy⟩
  subst j
  subst i
  subst u
  subst l
  let lhs := bvExtractConcat3Lhs x y xs (Term.Numeral iv)
    (Term.Numeral hv)
  let rhs := bvExtractConcat3Rhs y xs (Term.Numeral uv)
    (Term.Numeral lv)
  let dLhs := native_zplus (native_zplus hv 1) (native_zneg iv)
  let dRhs := native_zplus (native_zplus uv 1) (native_zneg lv)
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) =
      SmtType.BitVec (native_int_to_nat dLhs) := by
    simpa [lhs, bvExtractConcat3Lhs, dLhs] using
      smt_typeof_extract_of_context (bvExtractConcat1Whole x y xs)
        wLhs hv iv hWholeSmtTy hwLhs0 hi0 hjw hdLhs0
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) =
      SmtType.BitVec (native_int_to_nat dRhs) := by
    simpa [rhs, bvExtractConcat3Rhs, tailElim, dRhs] using
      smt_typeof_extract_of_context tailElim wRhs uv lv hTailSmtTy
        hwRhs0 hl0 huw hdRhs0
  have hLhsTrans : RuleProofs.eo_has_smt_translation lhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsTy]
    intro h
    cases h
  have hRhsTrans : RuleProofs.eo_has_smt_translation rhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hRhsTy]
    intro h
    cases h
  have hEOTypeEq : __eo_typeof lhs = __eo_typeof rhs := by
    apply RuleProofs.eo_typeof_eq_bool_operands_eq
    exact hTermTy
  have hLhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      lhs (__eo_typeof lhs) (__eo_to_smt lhs) rfl hLhsTrans rfl
  have hRhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      rhs (__eo_typeof rhs) (__eo_to_smt rhs) rfl hRhsTrans rfl
  have hTermBool : RuleProofs.eo_has_bool_type
      (bvExtractConcat3Term x y xs (Term.Numeral iv)
        (Term.Numeral hv) (Term.Numeral uv) (Term.Numeral lv)) := by
    unfold bvExtractConcat3Term
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
      (by rw [hLhsTy]; simp)
  simpa [hBodyEq] using hTermBool

private theorem eval_bv_concat_assoc
    (M : SmtModel) (hM : model_wf M)
    (a b c : Term) (wa wb wc : Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec wb ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec wc ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm a (bvConcatTerm b c))) =
      __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm (bvConcatTerm a b) c)) := by
  intro hATy hBTy hCTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt a) wa
      hATy with ⟨pa, hAEval, hACan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt b) wb
      hBTy with ⟨pb, hBEval, hBCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt c) wc
      hCTy with ⟨pc, hCEval, hCCan⟩
  have hWa0 : native_zleq 0 (native_nat_to_int wa) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hWb0 : native_zleq 0 (native_nat_to_int wb) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hWc0 : native_zleq 0 (native_nat_to_int wc) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hARange := bitvec_payload_range_of_canonical hWa0 hACan
  have hBRange := bitvec_payload_range_of_canonical hWb0 hBCan
  have hCRange := bitvec_payload_range_of_canonical hWc0 hCCan
  have hpa0 : 0 ≤ pa := hARange.1
  have hpa1 : pa < (2 : Int) ^ wa := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hARange.2
  have hpb0 : 0 ≤ pb := hBRange.1
  have hpb1 : pb < (2 : Int) ^ wb := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hBRange.2
  have hpc0 : 0 ≤ pc := hCRange.1
  have hpc1 : pc < (2 : Int) ^ wc := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hCRange.2
  let ba := BitVec.ofInt wa pa
  let bb := BitVec.ofInt wb pb
  let bc := BitVec.ofInt wc pc
  have hPa : (↑ba.toNat : Int) = pa := by
    rw [show ba.toNat = pa.toNat by
      exact ofInt_toNat_canonical wa pa hpa0 hpa1]
    exact Int.toNat_of_nonneg hpa0
  have hPb : (↑bb.toNat : Int) = pb := by
    rw [show bb.toNat = pb.toNat by
      exact ofInt_toNat_canonical wb pb hpb0 hpb1]
    exact Int.toNat_of_nonneg hpb0
  have hPc : (↑bc.toNat : Int) = pc := by
    rw [show bc.toNat = pc.toNat by
      exact ofInt_toNat_canonical wc pc hpc0 hpc1]
    exact Int.toNat_of_nonneg hpc0
  have hAEval' : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (↑wa : Int) (↑ba.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hPa] using hAEval
  have hBEval' : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (↑wb : Int) (↑bb.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hPb] using hBEval
  have hCEval' : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Binary (↑wc : Int) (↑bc.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hPc] using hCEval
  change __smtx_model_eval M
      (SmtTerm.concat (__eo_to_smt a)
        (SmtTerm.concat (__eo_to_smt b) (__eo_to_smt c))) =
    __smtx_model_eval M
      (SmtTerm.concat (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b))
        (__eo_to_smt c))
  simp only [__smtx_model_eval, hAEval', hBEval', hCEval',
    concat_bitvec_values]
  have hAssoc := BitVec.append_assoc (x₁ := ba) (x₂ := bb) (x₃ := bc)
  have hNat : ((ba ++ bb) ++ bc).toNat =
      (ba ++ (bb ++ bc)).toNat := by
    rw [hAssoc, BitVec.toNat_cast]
  simp [Nat.add_assoc, hNat]

private theorem eval_bv_list_concat_rec_append
    (M : SmtModel) (hM : model_wf M) :
    (a z1 z2 x : Term) -> (wa wz wx : Nat) ->
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z1) = SmtType.BitVec (wz + wx) ->
    __smtx_typeof (__eo_to_smt z2) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_model_eval M (__eo_to_smt z1) =
      __smtx_model_eval M (__eo_to_smt (bvConcatTerm z2 x)) ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z1)) =
      __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm (__eo_list_concat_rec a z2) x)) := by
  intro a z1
  induction a, z1 using __eo_list_concat_rec.induct with
  | case1 z1 =>
      intro z2 x wa wz wx hList
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro z2 x wa wz wx hList hATy hZ1Ty
      change __smtx_typeof SmtTerm.None = SmtType.BitVec (wz + wx) at hZ1Ty
      rw [TranslationProofs.smtx_typeof_none] at hZ1Ty
      cases hZ1Ty
  | case3 g head tail z1 hZ1 ih =>
      intro z2 x wa wz wx hList hATy hZ1Ty hZ2Ty hXTy hBase
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) g head tail hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) tail = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.concat) head tail hList
      rcases smt_typeof_bv_concat_width_inv head tail wa (by
          simpa [bvConcatTerm] using hATy) with
        ⟨wh, wt, hHeadTy, hTailTy, hWa⟩
      have hZ2Ne := term_ne_stuck_of_smt_bitvec_type hZ2Ty
      have hTailZ1Ne : __eo_list_concat_rec tail z1 ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.concat) tail z1 hTailList hZ1
      have hTailZ2Ne : __eo_list_concat_rec tail z2 ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.concat) tail z2 hTailList hZ2Ne
      have hTailRecTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec tail z2)) =
            SmtType.BitVec (wt + wz) :=
        smt_typeof_list_concat_rec_bv tail z2 wt wz
          hTailList hTailTy hZ2Ty
      have hIH := ih z2 x wt wz wx hTailList hTailTy
        hZ1Ty hZ2Ty hXTy hBase
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) head tail z1 hTailZ1Ne]
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) head tail z2 hTailZ2Ne]
      have hReplace :
          __smtx_model_eval M
              (__eo_to_smt
                (bvConcatTerm head (__eo_list_concat_rec tail z1))) =
            __smtx_model_eval M
              (__eo_to_smt
                (bvConcatTerm head
                  (bvConcatTerm (__eo_list_concat_rec tail z2) x))) := by
        change __smtx_model_eval_concat
            (__smtx_model_eval M (__eo_to_smt head))
            (__smtx_model_eval M
              (__eo_to_smt (__eo_list_concat_rec tail z1))) =
          __smtx_model_eval_concat
            (__smtx_model_eval M (__eo_to_smt head))
            (__smtx_model_eval M
              (__eo_to_smt
                (bvConcatTerm (__eo_list_concat_rec tail z2) x)))
        rw [hIH]
      exact hReplace.trans
        (eval_bv_concat_assoc M hM head
          (__eo_list_concat_rec tail z2) x wh (wt + wz) wx
          hHeadTy hTailRecTy hXTy)
  | case4 nil z1 hNil hZ1 hNot =>
      intro z2 x wa wz wx hList hATy hZ1Ty hZ2Ty hXTy hBase
      have hZ2Ne := term_ne_stuck_of_smt_bitvec_type hZ2Ty
      simpa [__eo_list_concat_rec, hZ1, hZ2Ne] using hBase

private theorem eval_bv_extract_concat_seed_append
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (wx wy : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_model_eval M (__eo_to_smt (bvExtractConcat1Seed x y)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm (bvConcatTerm y (Term.Binary 0 0)) x)) := by
  intro hXTy hYTy
  have hXYTy := smt_typeof_bv_concat_eq y x wy wx hYTy hXTy
  have hAssoc := eval_bv_concat_assoc M hM y x (Term.Binary 0 0)
    wy wx 0 hYTy hXTy smt_typeof_concat_empty
  have hXYEmpty := bvConcat_right_empty_eval_eq M hM
    (bvConcatTerm y x) (wy + wx) hXYTy
  have hYEmpty := bvConcat_right_empty_eval_eq M hM y wy hYTy
  have hRight :
      __smtx_model_eval M (__eo_to_smt (bvConcatTerm y x)) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvConcatTerm (bvConcatTerm y (Term.Binary 0 0)) x)) := by
    change __smtx_model_eval_concat
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt x)) =
      __smtx_model_eval_concat
        (__smtx_model_eval M
          (__eo_to_smt (bvConcatTerm y (Term.Binary 0 0))))
        (__smtx_model_eval M (__eo_to_smt x))
    rw [hYEmpty]
  exact hAssoc.trans (hXYEmpty.trans hRight)

private theorem eval_bv_extract_concat_whole_append
    (M : SmtModel) (hM : model_wf M)
    (x y xs : Term) (wx wy wxs : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    __smtx_model_eval M
        (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm (bvExtractConcat4Tail y xs) x)) := by
  intro hXsList hXTy hYTy hXsTy
  have hSeed1List := bv_extract_concat1_seed_is_list_true x y
  have hSeed2List := bv_concat_seed_is_list_true y
  have hSeed1Ty :=
    smt_typeof_bv_extract_concat1_seed x y wx wy hXTy hYTy
  have hSeed2Ty := smt_typeof_bv_concat_seed y wy hYTy
  have hBase := eval_bv_extract_concat_seed_append M hM x y wx wy
    hXTy hYTy
  have hRec := eval_bv_list_concat_rec_append M hM xs
    (bvExtractConcat1Seed x y) (bvConcatTerm y (Term.Binary 0 0)) x
    wxs wy wx hXsList hXsTy hSeed1Ty hSeed2Ty hXTy hBase
  simpa [bvExtractConcat1Whole, bvExtractConcat4Tail,
    __eo_list_concat, hXsList, hSeed1List, hSeed2List,
    __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] using hRec

private theorem bvConcatSingletonElimEvalEq
    (M : SmtModel) (hM : model_wf M) (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hList hTy
  have hElimTy := smt_typeof_bv_singleton_elim c w hList hTy
  have hElimValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.concat) c))) =
        SmtType.BitVec w := by
    have hNN : term_has_non_none_type
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) := by
      unfold term_has_non_none_type
      rw [hElimTy]
      intro h
      cases h
    simpa [hElimTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) hNN
  have hRel := bvConcatSingletonElimEvalRel M hM c w hList hTy
  exact (RuleProofs.smt_value_rel_iff_eq _ _ (by
    rintro ⟨r1, r2, hLeft, _hRight⟩
    rw [hLeft] at hElimValueTy
    cases hElimValueTy)).mp hRel

/-! Public, concat-specific interfaces for other BV rewrite families.  The
implementation lemmas above stay local so that their generic-looking names do
not leak into every rule module importing this file. -/

theorem bvConcat_term_smt_type
    (x y : Term) (wx wy : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt (bvConcatTerm x y)) =
      SmtType.BitVec (wx + wy) :=
  smt_typeof_bv_concat_eq x y wx wy

theorem bvConcat_term_smt_type_inv
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt (bvConcatTerm x y)) = SmtType.BitVec w ->
    ∃ wx wy,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      w = wx + wy :=
  smt_typeof_bv_concat_width_inv x y w

theorem bvConcat_empty_smt_type :
    __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 :=
  smt_typeof_concat_empty

theorem bvConcat_list_concat_smt_type
    (a z : Term) (wa wz : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.concat) a z)) =
      SmtType.BitVec (wa + wz) :=
  smt_typeof_list_concat_bv a z wa wz

theorem bvConcat_singleton_elim_smt_type
    (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) =
      SmtType.BitVec w :=
  smt_typeof_bv_singleton_elim c w

theorem bvConcat_singleton_elim_eo_type_inv
    (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __eo_typeof
        (__eo_list_singleton_elim (Term.UOp UserOp.concat) c) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) ->
    __eo_typeof c =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  intro hList hTy
  change __eo_typeof
      (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
        (Term.Boolean true) (__eo_list_singleton_elim_2 c)) = _ at hTy
  rw [hList] at hTy
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hTy
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g head tail hList
          subst g
          have hTailList := eo_is_list_tail_true_of_cons_self
            (Term.UOp UserOp.concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases bv_concat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq] at hTy
          cases b
          · simpa [bvConcatTerm] using hTy
          · have hTailEq : tail = Term.Binary 0 0 := by
              cases tail <;> simp [__eo_is_list_nil] at hNil ⊢
              case Binary bw bn =>
                split at hNil <;> simp_all
            subst tail
            have hHeadTy : __eo_typeof head =
                Term.Apply (Term.UOp UserOp.BitVec)
                  (Term.Numeral (native_nat_to_int w)) := by
              simpa using hTy
            have hEmptyTy : __eo_typeof (Term.Binary 0 0) =
                Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0) := by
              rfl
            change __eo_typeof_concat (__eo_typeof head)
                (__eo_typeof (Term.Binary 0 0)) = _
            rw [hHeadTy, hEmptyTy]
            simp [__eo_typeof_concat, __eo_lit_type_Binary,
              __eo_mk_apply, __eo_add, native_nat_to_int,
              SmtEval.native_nat_to_int, SmtEval.native_zplus]
      | _ => simpa [__eo_list_singleton_elim_2] using hTy
  | _ => simpa [__eo_list_singleton_elim_2] using hTy

theorem bvConcat_list_smt_type_of_translation
    (t : Term) :
    __eo_is_list (Term.UOp UserOp.concat) t = Term.Boolean true ->
    RuleProofs.eo_has_smt_translation t ->
    ∃ w : Nat, __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w :=
  smt_typeof_concat_list_of_translation t

theorem bvConcat_list_concat_lists_of_ne_stuck
    (a b : Term) :
    __eo_list_concat (Term.UOp UserOp.concat) a b ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) b = Term.Boolean true :=
  bv_list_concat_lists_of_ne_stuck (Term.UOp UserOp.concat) a b

theorem bvConcat_eo_typeof_concat_args_bitvec
    {A B : Term}
    (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ n m,
      A = Term.Apply (Term.UOp UserOp.BitVec) n ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) m :=
  eo_typeof_concat_args_bitvec_of_ne_stuck_local h

theorem bvConcat_eo_typeof_list_concat_right_bitvec
    (a z w : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __eo_typeof (__eo_list_concat (Term.UOp UserOp.concat) a z) =
      Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ wz, __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) wz :=
  eo_typeof_list_concat_right_bitvec_of_result a z w

theorem bvConcat_list_concat_rec_eval_append
    (M : SmtModel) (hM : model_wf M)
    (a z1 z2 x : Term) (wa wz wx : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z1) = SmtType.BitVec (wz + wx) ->
    __smtx_typeof (__eo_to_smt z2) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_model_eval M (__eo_to_smt z1) =
      __smtx_model_eval M (__eo_to_smt (bvConcatTerm z2 x)) ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z1)) =
      __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm (__eo_list_concat_rec a z2) x)) :=
  eval_bv_list_concat_rec_append M hM a z1 z2 x wa wz wx

theorem bvConcat_assoc_eval
    (M : SmtModel) (hM : model_wf M)
    (a b c : Term) (wa wb wc : Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec wb ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec wc ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm a (bvConcatTerm b c))) =
      __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm (bvConcatTerm a b) c)) :=
  eval_bv_concat_assoc M hM a b c wa wb wc

theorem bvConcat_singleton_elim_eval_eq
    (M : SmtModel) (hM : model_wf M) (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) =
      __smtx_model_eval M (__eo_to_smt c) :=
  bvConcatSingletonElimEvalEq M hM c w

theorem bvConcat_eval_right_empty
    (M : SmtModel) (hM : model_wf M) (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt x) :=
  bvConcat_right_empty_eval_eq M hM x w

private theorem eval_bv_extract_concat_whole_append_elim
    (M : SmtModel) (hM : model_wf M)
    (x y xs : Term) (wx wy wxs : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    __smtx_model_eval M
        (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm (bvExtractConcat4TailElim y xs) x)) := by
  intro hXsList hXTy hYTy hXsTy
  have hWhole := eval_bv_extract_concat_whole_append M hM
    x y xs wx wy wxs hXsList hXTy hYTy hXsTy
  have hTailList := bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy := smt_typeof_bv_extract_concat4_tail y xs wy wxs
    hXsList hYTy hXsTy
  have hElim := bvConcatSingletonElimEvalEq M hM
    (bvExtractConcat4Tail y xs) (wxs + wy) hTailList hTailTy
  have hElim' :
      __smtx_model_eval M
          (__eo_to_smt (bvExtractConcat4TailElim y xs)) =
        __smtx_model_eval M
          (__eo_to_smt (bvExtractConcat4Tail y xs)) := by
    simpa [bvExtractConcat4TailElim] using hElim
  rw [hWhole]
  change __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractConcat4Tail y xs)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractConcat4TailElim y xs)))
      (__smtx_model_eval M (__eo_to_smt x))
  rw [hElim']

private theorem extractLsb'_append_high
    {x : BitVec W} {y : BitVec T} {L D : Nat}
    (hFit : L + D ≤ W) :
    (x ++ y).extractLsb' (T + L) D = x.extractLsb' L D := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [BitVec.getElem_extractLsb' hk, BitVec.getElem_extractLsb' hk]
  have hHead : L + k < W := by omega
  have hApp : T + L + k < W + T := by omega
  rw [BitVec.getLsbD_eq_getElem hApp, BitVec.getElem_append]
  have hNotTail : ¬ T + L + k < T := by omega
  have hSub : T + L + k - T = L + k := by omega
  simp [hNotTail, hSub, BitVec.getLsbD_eq_getElem hHead]

private theorem extractLsb'_append_straddle
    {x : BitVec T} {y : BitVec W} {I DH : Nat}
    (hI : I < W) (hDH : DH ≤ T) :
    (x ++ y).extractLsb' I (DH + (W - I)) =
      x.extractLsb' 0 DH ++ y.extractLsb' I (W - I) := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [BitVec.getElem_extractLsb' hk, BitVec.getElem_append]
  have hWhole : I + k < T + W := by omega
  rw [BitVec.getLsbD_eq_getElem hWhole, BitVec.getElem_append]
  by_cases hLow : k < W - I
  · have hY : I + k < W := by omega
    have hLowExtract : k < W - I := hLow
    simp [hLow, BitVec.getElem_extractLsb' hLowExtract,
      BitVec.getLsbD_eq_getElem hY]
    split <;> simp_all
  · have hHead : k - (W - I) < DH := by omega
    have hHeadX : k - (W - I) < T := by omega
    have hNotWholeLow : ¬ I + k < W := by omega
    have hShift : I + k - W = k - (W - I) := by omega
    simp [hLow, hNotWholeLow, hShift,
      BitVec.getElem_extractLsb' hHead]
    rw [BitVec.getLsbD_eq_getElem hHeadX]

private theorem extract_concat_straddle_val
    (T W I DH : Nat) (pt px j i u1 u2 : Int)
    (hpt0 : 0 ≤ pt) (hpt1 : pt < (2 : Int) ^ T)
    (hpx0 : 0 ≤ px) (hpx1 : px < (2 : Int) ^ W)
    (hi : i = ↑I)
    (hdLeft : j + 1 + -i = ↑(DH + (W - I)))
    (hdHigh : u1 + 1 + -(0 : Int) = ↑DH)
    (hdLow : u2 + 1 + -i = ↑(W - I))
    (hI : I < W) (hDH : DH ≤ T) :
    __smtx_model_eval_extract (SmtValue.Numeral j) (SmtValue.Numeral i)
        (__smtx_model_eval_concat
          (SmtValue.Binary (↑T : Int) pt)
          (SmtValue.Binary (↑W : Int) px)) =
      __smtx_model_eval_concat
        (__smtx_model_eval_extract (SmtValue.Numeral u1)
          (SmtValue.Numeral 0) (SmtValue.Binary (↑T : Int) pt))
        (__smtx_model_eval_extract (SmtValue.Numeral u2)
          (SmtValue.Numeral i) (SmtValue.Binary (↑W : Int) px)) := by
  let bt := BitVec.ofInt T pt
  let bx := BitVec.ofInt W px
  have hPt : (↑bt.toNat : Int) = pt := by
    rw [show bt.toNat = pt.toNat by
      exact ofInt_toNat_canonical T pt hpt0 hpt1]
    exact Int.toNat_of_nonneg hpt0
  have hPx : (↑bx.toNat : Int) = px := by
    rw [show bx.toNat = px.toNat by
      exact ofInt_toNat_canonical W px hpx0 hpx1]
    exact Int.toNat_of_nonneg hpx0
  rw [← hPt, ← hPx, concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(bt ++ bx).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(bt ++ bx).toNat : Int) < (2 : Int) ^ (T + W) := by
    exact_mod_cast (bt ++ bx).isLt
  have hBt0 : (0 : Int) ≤ (↑bt.toNat : Int) := Int.natCast_nonneg _
  have hBt1 : (↑bt.toNat : Int) < (2 : Int) ^ T := by
    exact_mod_cast bt.isLt
  have hBx0 : (0 : Int) ≤ (↑bx.toNat : Int) := Int.natCast_nonneg _
  have hBx1 : (↑bx.toNat : Int) < (2 : Int) ^ W := by
    exact_mod_cast bx.isLt
  rw [extract_val_bitvec_start_len (T + W) I (DH + (W - I))
    (↑(bt ++ bx).toNat : Int) j i hApp0 hApp1 hi hdLeft]
  rw [extract_val_bitvec_start_len T 0 DH (↑bt.toNat : Int)
    u1 0 hBt0 hBt1 rfl hdHigh]
  rw [extract_val_bitvec_start_len W I (W - I) (↑bx.toNat : Int)
    u2 i hBx0 hBx1 hi hdLow]
  rw [bitvec_ofInt_natCast_toNat (bt ++ bx),
    bitvec_ofInt_natCast_toNat bt, bitvec_ofInt_natCast_toNat bx,
    concat_bitvec_values]
  congr 2
  exact congrArg BitVec.toNat
    (extractLsb'_append_straddle (x := bt) (y := bx) hI hDH)

private theorem bvExtractConcat2_premises_numeric
    (M : SmtModel) (x : Term) (wx : Nat)
    (i j u1 u2 : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    eo_interprets M
      (bvExtractConcat2PremI x (Term.Numeral i)) true ->
    eo_interprets M
      (bvExtractConcat2PremJ x (Term.Numeral j)) true ->
    eo_interprets M
      (bvExtractConcat2PremU1 x (Term.Numeral j) (Term.Numeral u1)) true ->
    eo_interprets M
      (bvExtractConcat2PremU2 x (Term.Numeral u2)) true ->
    native_zlt i (native_nat_to_int wx) = true ∧
      native_zleq (native_nat_to_int wx) j = true ∧
      u1 = native_zplus j (native_zneg (native_nat_to_int wx)) ∧
      u2 = native_zplus (native_nat_to_int wx) (native_zneg 1) := by
  intro hXTy hP1 hP2 hP3 hP4
  have hSize := eval_bvsize_of_smt_bitvec_nat M x wx hXTy
  have hEq1 := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral i))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (Term.Boolean true) (by simpa [bvExtractConcat2PremI] using hP1)
  have hEq2 := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral j))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (Term.Boolean true) (by simpa [bvExtractConcat2PremJ] using hP2)
  have hEq3 := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral u1)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral j))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (by simpa [bvExtractConcat2PremU1] using hP3)
  have hEq4 := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral u2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))
      (Term.Numeral 1))
    (by simpa [bvExtractConcat2PremU2] using hP4)
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.lt (SmtTerm.Numeral i)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hEq1
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.geq (SmtTerm.Numeral j)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hEq2
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral u1))
      (__smtx_model_eval M
        (SmtTerm.neg (SmtTerm.Numeral j)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) =
    SmtValue.Boolean true at hEq3
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral u2))
      (__smtx_model_eval M
        (SmtTerm.neg
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
          (SmtTerm.Numeral 1))) = SmtValue.Boolean true at hEq4
  simp [__smtx_model_eval, __smtx_model_eval__, __smtx_model_eval_lt,
    __smtx_model_eval_geq, __smtx_model_eval_leq, hSize,
    __smtx_model_eval_eq, native_veq, SmtEval.native_zeq,
    SmtEval.native_zplus, SmtEval.native_zneg]
    at hEq1 hEq2 hEq3 hEq4
  exact ⟨hEq1, hEq2, hEq3, hEq4⟩

private theorem bvExtractConcat2_index_arithmetic
    (W I DH : Nat) (i j u1 u2 : Int)
    (hi : i = ↑I) (hDH : u1 + 1 = ↑DH)
    (hiW : i < ↑W) (hjW : ↑W ≤ j)
    (hu1 : u1 = j - ↑W) (hu2 : u2 = ↑W - 1) :
    I < W ∧
      j + 1 + -i = ↑(DH + (W - I)) ∧
      u1 + 1 + -(0 : Int) = ↑DH ∧
      u2 + 1 + -i = ↑(W - I) := by
  constructor
  · have hCast : (↑I : Int) < ↑W := by
      rw [← hi]
      exact hiW
    exact_mod_cast hCast
  constructor
  · rw [← Int.ofNat_add_ofNat]
    rw [Int.ofNat_sub (by omega : I ≤ W)]
    omega
  constructor <;> omega

private theorem bvExtractConcat2_high_length_fits
    (T DH : Nat) (u1 : Int)
    (hDH : u1 + 1 = ↑DH) (hu1T : u1 < ↑T) : DH ≤ T := by
  have hCast : (↑DH : Int) ≤ ↑T := by
    rw [← hDH]
    omega
  exact_mod_cast hCast

private theorem eval_bv_extract_concat2_rhs_no_empty
    (M : SmtModel) (hM : model_wf M)
    (x y xs i u1 u2 : Term) (dLow : Nat) :
    __smtx_typeof (__eo_to_smt (bvExtractConcat2Low x i u2)) =
      SmtType.BitVec dLow ->
    __smtx_model_eval M
        (__eo_to_smt (bvExtractConcat2Rhs x y xs i u1 u2)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm (bvExtractConcat2High y xs u1)
            (bvExtractConcat2Low x i u2))) := by
  intro hLowTy
  have hEmpty := bvConcat_right_empty_eval_eq M hM
    (bvExtractConcat2Low x i u2) dLow hLowTy
  change __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractConcat2High y xs u1)))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvConcatTerm (bvExtractConcat2Low x i u2) (Term.Binary 0 0)))) =
    __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractConcat2High y xs u1)))
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractConcat2Low x i u2)))
  rw [hEmpty]

theorem facts_bv_extract_concat2_program_body
    (M : SmtModel) (hM : model_wf M)
    (x xs y i j u1 u2 : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_bool_type (bvExtractConcat2PremI x i) ->
    __eo_typeof (bvExtractConcat2ProgramBody x xs y i j u1 u2) = Term.Bool ->
    eo_interprets M (bvExtractConcat2PremI x i) true ->
    eo_interprets M (bvExtractConcat2PremJ x j) true ->
    eo_interprets M (bvExtractConcat2PremU1 x j u1) true ->
    eo_interprets M (bvExtractConcat2PremU2 x u2) true ->
    eo_interprets M (bvExtractConcat2ProgramBody x xs y i j u1 u2) true := by
  intro hYTrans hXsTrans hPremBool hBodyTy hP1 hP2 hP3 hP4
  rcases bvExtractConcat2_body_smt_context x xs y i j u1 u2
      hYTrans hXsTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hXsList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat2ProgramBody_eq_term_of_type_bool x xs y i j u1 u2 hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat2Term x y xs i j u1 u2) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    intro h
    cases h
  have hWholeTrans : RuleProofs.eo_has_smt_translation
      (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList : __eo_is_list (Term.UOp UserOp.concat) tail =
      Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tail] using smt_typeof_bv_extract_concat4_tail y xs wy wxs
      hXsList hYTy hXsTy
  have hTailElimTy : __smtx_typeof (__eo_to_smt tailElim) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy) hTailList hTailTy
  have hTailElimTrans : RuleProofs.eo_has_smt_translation tailElim := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailElimTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat2Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat2Rhs x y xs i u1 u2))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvExtractConcat1Whole x y xs) j i hWholeTrans
      (by simpa [bvExtractConcat2Lhs] using hLhsNe) with
    ⟨wLhs, jv, iv, _hWholeEoTy, hJ, hI, hwLhs0, hi0,
      hjw, hdLhs0, hWholeSmtTy⟩
  subst j
  subst i
  let high := bvExtractConcat2High y xs u1
  let low := bvExtractConcat2Low x (Term.Numeral iv) u2
  let inner := bvConcatTerm low (Term.Binary 0 0)
  have hRhsConcatNe :
      __eo_typeof_concat (__eo_typeof high) (__eo_typeof inner) ≠
        Term.Stuck := by
    exact hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsConcatNe with
    ⟨wHighEo, wInnerEo, hHighEoTy, hInnerEoTy⟩
  have hHighNe : __eo_typeof high ≠ Term.Stuck := by
    rw [hHighEoTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck tailElim u1 (Term.Numeral 0)
      hTailElimTrans (by
        simpa [high, bvExtractConcat2High, tailElim] using hHighNe) with
    ⟨wHighSrc, u1v, zv, _hTailEoTy, hU1, hZero, hwHigh0, hz0,
      hu1w, hdHigh0, hTailSmtTy⟩
  subst u1
  injection hZero with hZeroVal
  subst zv
  have hInnerNe : __eo_typeof inner ≠ Term.Stuck := by
    rw [hInnerEoTy]
    intro h
    cases h
  have hInnerConcatNe :
      __eo_typeof_concat (__eo_typeof low)
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    exact hInnerNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerConcatNe with
    ⟨wLowEo, wEmptyEo, hLowEoTy, _hEmptyEoTy⟩
  have hLowNe : __eo_typeof low ≠ Term.Stuck := by
    rw [hLowEoTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x u2 (Term.Numeral iv)
      hXTrans (by
        simpa [low, bvExtractConcat2Low] using hLowNe) with
    ⟨wLowSrc, u2v, iv2, _hXEoTy, hU2, hILow, hwLow0, hiLow0,
      hu2w, hdLow0, hXSmtTy⟩
  subst u2
  injection hILow with hIV
  subst iv2
  rcases bvExtractConcat2_premises_numeric M x wx iv jv u1v u2v
      hXTy hP1 hP2 hP3 hP4 with ⟨hiWx, hWxJ, hu1, hu2⟩
  let I := native_int_to_nat iv
  let dHigh := native_zplus (native_zplus u1v 1) (native_zneg 0)
  let DH := native_int_to_nat dHigh
  have hIRound : (↑I : Int) = iv := by
    simpa [I, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip iv hi0
  have hdHighNonneg : native_zleq 0 dHigh = true :=
    native_zleq_of_zlt_true _ _ hdHigh0
  have hDHRound : (↑DH : Int) = dHigh := by
    simpa [DH, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip dHigh hdHighNonneg
  have hiWxInt : iv < (↑wx : Int) := by
    exact of_decide_eq_true hiWx
  have hWxJInt : (↑wx : Int) ≤ jv := by
    exact of_decide_eq_true hWxJ
  have hu1Int : u1v = jv - (↑wx : Int) := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      native_nat_to_int, SmtEval.native_nat_to_int,
      Int.sub_eq_add_neg] using hu1
  have hu2Int : u2v = (↑wx : Int) - 1 := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      native_nat_to_int, SmtEval.native_nat_to_int,
      Int.sub_eq_add_neg] using hu2
  have hDHCast : u1v + 1 = (↑DH : Int) := by
    rw [hDHRound]
    simp [dHigh, SmtEval.native_zplus, SmtEval.native_zneg]
  rcases bvExtractConcat2_index_arithmetic wx I DH iv jv u1v u2v
      hIRound.symm hDHCast hiWxInt hWxJInt hu1Int hu2Int with
    ⟨hIlt, hLeftLen, hHighLen, hLowLen⟩
  have hTailWidthEq : native_int_to_nat wHighSrc = wxs + wy := by
    rw [hTailElimTy] at hTailSmtTy
    simpa using hTailSmtTy.symm
  have hHighWidthRound := native_int_to_nat_roundtrip wHighSrc hwHigh0
  have hHighWidthInt : wHighSrc = (↑(wxs + wy) : Int) := by
    calc
      wHighSrc = native_nat_to_int (native_int_to_nat wHighSrc) := by
        simpa [native_nat_to_int, SmtEval.native_nat_to_int] using
          hHighWidthRound.symm
      _ = (↑(wxs + wy) : Int) := by
        rw [hTailWidthEq]
        rfl
  have hu1TailInt : u1v < (↑(wxs + wy) : Int) := by
    have h := (show u1v < wHighSrc by
      simpa [SmtEval.native_zlt] using hu1w)
    rw [hHighWidthInt] at h
    exact h
  have hDHFit : DH ≤ wxs + wy :=
    bvExtractConcat2_high_length_fits (wxs + wy) DH u1v
      hDHCast hu1TailInt
  let dLow := native_zplus (native_zplus u2v 1) (native_zneg iv)
  have hLowSmtTy : __smtx_typeof (__eo_to_smt low) =
      SmtType.BitVec (wx - I) := by
    have hRaw := smt_typeof_extract_of_context x wLowSrc u2v iv hXSmtTy
      hwLow0 hiLow0 hu2w hdLow0
    have hWidthNat : native_int_to_nat dLow = wx - I := by
      rw [show dLow = (↑(wx - I) : Int) by
        simpa [dLow, SmtEval.native_zplus, SmtEval.native_zneg] using hLowLen]
      simp [native_int_to_nat, SmtEval.native_int_to_nat]
    simpa [low, bvExtractConcat2Low, dLow, hWidthNat] using hRaw
  have hRhsEval := eval_bv_extract_concat2_rhs_no_empty M hM
    x y xs (Term.Numeral iv) (Term.Numeral u1v) (Term.Numeral u2v)
    (wx - I) hLowSmtTy
  have hWholeEval := eval_bv_extract_concat_whole_append_elim M hM
    x y xs wx wy wxs hXsList hXTy hYTy hXsTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt tailElim)
      (wxs + wy) hTailElimTy with ⟨pt, hTailEval, hTailCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x)
      wx hXTy with ⟨px, hXEval, hXCan⟩
  have hWt0 : native_zleq 0 (native_nat_to_int (wxs + wy)) = true := by
    have hNonneg : (0 : Int) ≤ ↑(wxs + wy) := Int.natCast_nonneg _
    exact decide_eq_true hNonneg
  have hWx0 : native_zleq 0 (native_nat_to_int wx) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hTRange := bitvec_payload_range_of_canonical hWt0 hTailCan
  have hXRange := bitvec_payload_range_of_canonical hWx0 hXCan
  have hpt0 : 0 ≤ pt := hTRange.1
  have hpt1 : pt < (2 : Int) ^ (wxs + wy) := by
    exact hTRange.2
  have hpx0 : 0 ≤ px := hXRange.1
  have hpx1 : px < (2 : Int) ^ wx := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hXRange.2
  have hTailEval' : __smtx_model_eval M (__eo_to_smt tailElim) =
      SmtValue.Binary (↑(wxs + wy) : Int) pt := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hTailEval
  have hXEval' : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (↑wx : Int) px := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hXEval
  have hBool := typed_bv_extract_concat2_program_body x xs y
    (Term.Numeral iv) (Term.Numeral jv) (Term.Numeral u1v)
    (Term.Numeral u2v) hYTrans hXsTrans (by simpa using hPremBool) hBodyTy
  rw [hBodyEq] at hBool
  rw [hBodyEq]
  unfold bvExtractConcat2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractConcat2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractConcat2Lhs x y xs (Term.Numeral iv)
            (Term.Numeral jv))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractConcat2Rhs x y xs (Term.Numeral iv)
            (Term.Numeral u1v) (Term.Numeral u2v))))
    rw [hRhsEval]
    unfold bvExtractConcat2Lhs bvExtractConcat2High bvExtractConcat2Low
    rw [eval_extract_term]
    rw [hWholeEval]
    change RuleProofs.smt_value_rel
      (__smtx_model_eval_extract (SmtValue.Numeral jv)
        (SmtValue.Numeral iv)
        (__smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt tailElim))
          (__smtx_model_eval M (__eo_to_smt x))))
      (__smtx_model_eval_concat
        (__smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm tailElim (Term.Numeral u1v) (Term.Numeral 0))))
        (__smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral u2v) (Term.Numeral iv)))))
    rw [eval_extract_term, eval_extract_term]
    change RuleProofs.smt_value_rel
      (__smtx_model_eval_extract (SmtValue.Numeral jv)
        (SmtValue.Numeral iv)
        (__smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt tailElim))
          (__smtx_model_eval M (__eo_to_smt x))))
      (__smtx_model_eval_concat
        (__smtx_model_eval_extract (SmtValue.Numeral u1v)
          (SmtValue.Numeral 0)
          (__smtx_model_eval M (__eo_to_smt tailElim)))
        (__smtx_model_eval_extract (SmtValue.Numeral u2v)
          (SmtValue.Numeral iv)
          (__smtx_model_eval M (__eo_to_smt x))))
    rw [hTailEval', hXEval']
    rw [extract_concat_straddle_val (wxs + wy) wx I DH pt px
      jv iv u1v u2v hpt0 hpt1 hpx0 hpx1 hIRound.symm
      hLeftLen hHighLen hLowLen hIlt hDHFit]
    exact RuleProofs.smt_value_rel_refl _

private theorem bvExtractConcat3_premises_numeric
    (M : SmtModel) (x : Term) (wx : Nat)
    (i j u l : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    eo_interprets M
      (bvExtractConcat3PremI x (Term.Numeral i)) true ->
    eo_interprets M
      (bvExtractConcat3PremU x (Term.Numeral j) (Term.Numeral u)) true ->
    eo_interprets M
      (bvExtractConcat3PremL x (Term.Numeral i) (Term.Numeral l)) true ->
    native_zleq (native_nat_to_int wx) i = true ∧
      u = native_zplus j (native_zneg (native_nat_to_int wx)) ∧
      l = native_zplus i (native_zneg (native_nat_to_int wx)) := by
  intro hXTy hP1 hP2 hP3
  have hSize := eval_bvsize_of_smt_bitvec_nat M x wx hXTy
  have hEq1 := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral i))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (Term.Boolean true) (by simpa [bvExtractConcat3PremI] using hP1)
  have hEq2 := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral u)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral j))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (by simpa [bvExtractConcat3PremU] using hP2)
  have hEq3 := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral l)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral i))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (by simpa [bvExtractConcat3PremL] using hP3)
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.geq (SmtTerm.Numeral i)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hEq1
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral u))
      (__smtx_model_eval M
        (SmtTerm.neg (SmtTerm.Numeral j)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) =
    SmtValue.Boolean true at hEq2
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral l))
      (__smtx_model_eval M
        (SmtTerm.neg (SmtTerm.Numeral i)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) =
    SmtValue.Boolean true at hEq3
  simp [__smtx_model_eval, __smtx_model_eval__, __smtx_model_eval_geq,
    __smtx_model_eval_leq, hSize, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq, SmtEval.native_zplus, SmtEval.native_zneg]
    at hEq1 hEq2 hEq3
  exact ⟨hEq1, hEq2, hEq3⟩

private theorem extract_concat_high_val
    (T W L D : Nat) (pt px h i u l : Int)
    (hpt0 : 0 ≤ pt) (hpt1 : pt < (2 : Int) ^ T)
    (hpx0 : 0 ≤ px) (hpx1 : px < (2 : Int) ^ W)
    (hi : i = ↑(W + L)) (hd : h + 1 + -i = ↑D)
    (hl : l = ↑L) (hdR : u + 1 + -l = ↑D)
    (hFit : L + D ≤ T) :
    __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral i)
        (__smtx_model_eval_concat
          (SmtValue.Binary (↑T : Int) pt)
          (SmtValue.Binary (↑W : Int) px)) =
      __smtx_model_eval_extract (SmtValue.Numeral u) (SmtValue.Numeral l)
        (SmtValue.Binary (↑T : Int) pt) := by
  let bt := BitVec.ofInt T pt
  let bx := BitVec.ofInt W px
  have hPt : (↑bt.toNat : Int) = pt := by
    rw [show bt.toNat = pt.toNat by
      exact ofInt_toNat_canonical T pt hpt0 hpt1]
    exact Int.toNat_of_nonneg hpt0
  have hPx : (↑bx.toNat : Int) = px := by
    rw [show bx.toNat = px.toNat by
      exact ofInt_toNat_canonical W px hpx0 hpx1]
    exact Int.toNat_of_nonneg hpx0
  rw [← hPt, ← hPx, concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(bt ++ bx).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(bt ++ bx).toNat : Int) < (2 : Int) ^ (T + W) := by
    exact_mod_cast (bt ++ bx).isLt
  have hBt0 : (0 : Int) ≤ (↑bt.toNat : Int) := Int.natCast_nonneg _
  have hBt1 : (↑bt.toNat : Int) < (2 : Int) ^ T := by
    exact_mod_cast bt.isLt
  rw [extract_val_bitvec_start_len (T + W) (W + L) D
    (↑(bt ++ bx).toNat : Int) h i hApp0 hApp1 hi hd]
  rw [extract_val_bitvec_start_len T L D (↑bt.toNat : Int)
    u l hBt0 hBt1 hl hdR]
  rw [bitvec_ofInt_natCast_toNat (bt ++ bx),
    bitvec_ofInt_natCast_toNat bt]
  congr 2
  exact congrArg BitVec.toNat
    (extractLsb'_append_high (x := bt) (y := bx) (L := L) (D := D)
      hFit)

private theorem int_sub_shift_extract
    (h i w : Int) :
    (h - w) + 1 + -(i - w) = h + 1 + -i := by
  omega

private theorem int_cancel_extract_start
    (l u : Int) :
    l + (u + 1 + -l) = u + 1 := by
  omega

theorem facts_bv_extract_concat3_program_body
    (M : SmtModel) (hM : model_wf M)
    (x y xs i j u l : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_bool_type (bvExtractConcat3PremI x i) ->
    __eo_typeof (bvExtractConcat3ProgramBody x y xs i j u l) = Term.Bool ->
    eo_interprets M (bvExtractConcat3PremI x i) true ->
    eo_interprets M (bvExtractConcat3PremU x j u) true ->
    eo_interprets M (bvExtractConcat3PremL x i l) true ->
    eo_interprets M (bvExtractConcat3ProgramBody x y xs i j u l) true := by
  intro hYTrans hXsTrans hPremBool hBodyTy hP1 hP2 hP3
  rcases bvExtractConcat3_body_smt_context x y xs i j u l
      hYTrans hXsTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hXsList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat3ProgramBody_eq_term_of_type_bool x y xs i j u l hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat3Term x y xs i j u l) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hWholeTrans : RuleProofs.eo_has_smt_translation
      (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList : __eo_is_list (Term.UOp UserOp.concat) tail =
      Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tail] using smt_typeof_bv_extract_concat4_tail y xs wy wxs
      hXsList hYTy hXsTy
  have hTailElimTy : __smtx_typeof (__eo_to_smt tailElim) =
      SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy) hTailList hTailTy
  have hTailElimTrans : RuleProofs.eo_has_smt_translation tailElim := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailElimTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat3Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat3Rhs y xs u l))
      (by exact hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvExtractConcat1Whole x y xs) j i hWholeTrans
      (by simpa [bvExtractConcat3Lhs] using hLhsNe) with
    ⟨wLhs, jv, iv, _hWholeEoTy, hJ, hI, hwLhs0, hi0,
      hjw, hdLhs0, hWholeSmtTy⟩
  rcases bv_extract_context_of_non_stuck tailElim u l hTailElimTrans
      (by simpa [bvExtractConcat3Rhs, tailElim] using hRhsNe) with
    ⟨wRhs, uv, lv, _hTailEoTy, hU, hL, hwRhs0, hl0,
      huw, hdRhs0, hTailSmtTy⟩
  subst j
  subst i
  subst u
  subst l
  rcases bvExtractConcat3_premises_numeric M x wx iv jv uv lv
      hXTy hP1 hP2 hP3 with ⟨hwxi, hu, hl⟩
  let L := native_int_to_nat lv
  let d := native_zplus (native_zplus jv 1) (native_zneg iv)
  let D := native_int_to_nat d
  have hLRound : (↑L : Int) = lv := by
    simpa [L, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip lv hl0
  have hd0 : native_zleq 0 d = true :=
    native_zleq_of_zlt_true _ _ hdLhs0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip d hd0
  have hiCast : iv = (↑(wx + L) : Int) := by
    have hlInt : lv = iv - (↑wx : Int) := by
      simpa [SmtEval.native_zplus, SmtEval.native_zneg,
        native_nat_to_int, SmtEval.native_nat_to_int,
        Int.sub_eq_add_neg] using hl
    rw [← Int.ofNat_add_ofNat, hLRound]
    calc
      iv = (iv - (↑wx : Int)) + ↑wx := (Int.sub_add_cancel iv _).symm
      _ = lv + ↑wx := by rw [hlInt]
      _ = ↑wx + lv := Int.add_comm _ _
  have hdCast : jv + 1 + -iv = (↑D : Int) := by
    rw [hDRound]
    rfl
  have huInt : uv = jv - (↑wx : Int) := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      native_nat_to_int, SmtEval.native_nat_to_int,
      Int.sub_eq_add_neg] using hu
  have hlInt : lv = iv - (↑wx : Int) := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      native_nat_to_int, SmtEval.native_nat_to_int,
      Int.sub_eq_add_neg] using hl
  have hdRCast : uv + 1 + -lv = (↑D : Int) := by
    calc
      uv + 1 + -lv = (jv - (↑wx : Int)) + 1 +
          -(iv - (↑wx : Int)) := by rw [huInt, hlInt]
      _ = jv + 1 + -iv := int_sub_shift_extract jv iv ↑wx
      _ = ↑D := hdCast
  have huwInt : uv < (↑(wxs + wy) : Int) := by
    have hWidthEq : native_int_to_nat wRhs = wxs + wy := by
      rw [hTailElimTy] at hTailSmtTy
      simpa using hTailSmtTy.symm
    have hWRound := native_int_to_nat_roundtrip wRhs hwRhs0
    have hWInt : wRhs = (↑(wxs + wy) : Int) := by
      calc
        wRhs = native_nat_to_int (native_int_to_nat wRhs) := by
          simpa [native_nat_to_int, SmtEval.native_nat_to_int] using
            hWRound.symm
        _ = (↑(wxs + wy) : Int) := by
          rw [hWidthEq]
          rfl
    have : uv < wRhs := by simpa [SmtEval.native_zlt] using huw
    rw [hWInt] at this
    exact this
  have hFitInt : (↑L : Int) + (↑D : Int) ≤
      (↑(wxs + wy) : Int) := by
    rw [hLRound, hDRound]
    have hEnd : lv + d = uv + 1 := by
      calc
        lv + d = lv + (↑D : Int) := by rw [hDRound]
        _ = lv + (uv + 1 + -lv) := by rw [hdRCast]
        _ = uv + 1 := int_cancel_extract_start lv uv
    rw [hEnd]
    exact Int.add_one_le_iff.mpr huwInt
  have hFit : L + D ≤ wxs + wy := by exact_mod_cast hFitInt
  have hWholeEval := eval_bv_extract_concat_whole_append_elim M hM
    x y xs wx wy wxs hXsList hXTy hYTy hXsTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt tailElim)
      (wxs + wy) hTailElimTy with ⟨pt, hTailEval, hTailCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x)
      wx hXTy with ⟨px, hXEval, hXCan⟩
  have hWt0 : native_zleq 0 (native_nat_to_int (wxs + wy)) = true := by
    have hNonneg : (0 : Int) ≤ ↑(wxs + wy) := Int.natCast_nonneg _
    exact decide_eq_true hNonneg
  have hWx0 : native_zleq 0 (native_nat_to_int wx) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hTRange := bitvec_payload_range_of_canonical hWt0 hTailCan
  have hXRange := bitvec_payload_range_of_canonical hWx0 hXCan
  have hpt0 : 0 ≤ pt := hTRange.1
  have hpt1 : pt < (2 : Int) ^ (wxs + wy) := by
    exact hTRange.2
  have hpx0 : 0 ≤ px := hXRange.1
  have hpx1 : px < (2 : Int) ^ wx := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hXRange.2
  have hTailEval' : __smtx_model_eval M (__eo_to_smt tailElim) =
      SmtValue.Binary (↑(wxs + wy) : Int) pt := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hTailEval
  have hXEval' : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (↑wx : Int) px := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hXEval
  have hBool := typed_bv_extract_concat3_program_body x y xs
    (Term.Numeral iv) (Term.Numeral jv) (Term.Numeral uv)
    (Term.Numeral lv) hYTrans hXsTrans (by simpa using hPremBool) hBodyTy
  rw [hBodyEq] at hBool
  rw [hBodyEq]
  unfold bvExtractConcat3Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractConcat3Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractConcat3Lhs x y xs (Term.Numeral iv)
            (Term.Numeral jv))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractConcat3Rhs y xs (Term.Numeral uv)
            (Term.Numeral lv))))
    unfold bvExtractConcat3Lhs bvExtractConcat3Rhs
    rw [eval_extract_term, eval_extract_term, hWholeEval]
    change RuleProofs.smt_value_rel
      (__smtx_model_eval_extract (SmtValue.Numeral jv)
        (SmtValue.Numeral iv)
        (__smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt tailElim))
          (__smtx_model_eval M (__eo_to_smt x))))
      (__smtx_model_eval_extract (SmtValue.Numeral uv)
        (SmtValue.Numeral lv)
        (__smtx_model_eval M (__eo_to_smt tailElim)))
    rw [hTailEval', hXEval']
    rw [extract_concat_high_val (wxs + wy) wx L D pt px jv iv uv lv
      hpt0 hpt1 hpx0 hpx1 hiCast hdCast hLRound.symm hdRCast hFit]
    exact RuleProofs.smt_value_rel_refl _

/-! Full-component projections used by the concat-pullup rules. -/

theorem bvConcat_bvsize_smt_type_inv (t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) =
      SmtType.Int ->
    ∃ w, __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w :=
  smt_typeof_bvsize_int_inv t

theorem bvConcat_bvsize_smt_type_of_non_none (t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) ≠
      SmtType.None ->
    ∃ w,
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) =
        SmtType.Int := by
  intro hNN
  change __smtx_typeof
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t)))))
        SmtTerm.None) ≠ SmtType.None at hNN
  have hInt : __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) =
        SmtType.Int := by
    change __smtx_typeof
        (native_ite
          (native_zleq 0
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t))))
          (SmtTerm._at_purify
            (SmtTerm.Numeral
              (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t)))))
          SmtTerm.None) = SmtType.Int
    generalize hT : __smtx_typeof (__eo_to_smt t) = T at hNN ⊢
    cases T <;>
      simp [__eo_to_smt_bv_size, SmtEval.native_zleq,
        SmtEval.native_zneg, native_nat_to_int,
        SmtEval.native_nat_to_int, native_ite, __smtx_typeof] at hNN ⊢
  rcases smt_typeof_bvsize_int_inv t hInt with ⟨w, hTy⟩
  exact ⟨w, hTy, hInt⟩

theorem bvConcat_smt_typeof_neg_int_args (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.neg a b) = SmtType.Int ->
    __smtx_typeof a = SmtType.Int ∧ __smtx_typeof b = SmtType.Int :=
  smt_typeof_neg_int_args a b

theorem bvConcat_eval_bvsize_of_smt_bitvec_nat
    (M : SmtModel) (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral (native_nat_to_int w) :=
  eval_bvsize_of_smt_bitvec_nat M x w

theorem bvConcat_model_eval_eq_true_of_eo_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
        SmtValue.Boolean true :=
  model_eval_eq_true_of_eo_eq_true M x y

theorem bvConcat_extract_low_full_value
    (A B : Nat) (a b : Int)
    (ha0 : 0 ≤ a) (ha1 : a < (2 : Int) ^ A)
    (hb0 : 0 ≤ b) (hb1 : b < (2 : Int) ^ B)
    (hB : 0 < B) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑(B - 1))
        (SmtValue.Numeral 0)
        (__smtx_model_eval_concat
          (SmtValue.Binary ↑A a) (SmtValue.Binary ↑B b)) =
      SmtValue.Binary ↑B b := by
  let ba : BitVec A := BitVec.ofInt A a
  let bb : BitVec B := BitVec.ofInt B b
  have hBa : (↑ba.toNat : Int) = a := by
    rw [show ba.toNat = a.toNat by
      exact ofInt_toNat_canonical A a ha0 ha1]
    exact Int.toNat_of_nonneg ha0
  have hBb : (↑bb.toNat : Int) = b := by
    rw [show bb.toNat = b.toNat by
      exact ofInt_toNat_canonical B b hb0 hb1]
    exact Int.toNat_of_nonneg hb0
  rw [← hBa, ← hBb, concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(ba ++ bb).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(ba ++ bb).toNat : Int) < (2 : Int) ^ (A + B) := by
    exact_mod_cast (ba ++ bb).isLt
  rw [extract_val_bitvec_start_len (A + B) 0 B
    (↑(ba ++ bb).toNat : Int) (↑(B - 1) : Int) 0 hApp0 hApp1
    (by rfl) (by norm_cast; omega)]
  congr 2
  rw [bitvec_ofInt_natCast_toNat (ba ++ bb),
    BitVec.extractLsb'_append_eq_right]

theorem bvConcat_extract_high_full_value
    (A B : Nat) (a b : Int)
    (ha0 : 0 ≤ a) (ha1 : a < (2 : Int) ^ A)
    (hb0 : 0 ≤ b) (hb1 : b < (2 : Int) ^ B)
    (hA : 0 < A) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑(A + B - 1))
        (SmtValue.Numeral ↑B)
        (__smtx_model_eval_concat
          (SmtValue.Binary ↑A a) (SmtValue.Binary ↑B b)) =
      SmtValue.Binary ↑A a := by
  let ba : BitVec A := BitVec.ofInt A a
  let bb : BitVec B := BitVec.ofInt B b
  have hBa : (↑ba.toNat : Int) = a := by
    rw [show ba.toNat = a.toNat by
      exact ofInt_toNat_canonical A a ha0 ha1]
    exact Int.toNat_of_nonneg ha0
  have hBb : (↑bb.toNat : Int) = b := by
    rw [show bb.toNat = b.toNat by
      exact ofInt_toNat_canonical B b hb0 hb1]
    exact Int.toNat_of_nonneg hb0
  rw [← hBa, ← hBb, concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(ba ++ bb).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(ba ++ bb).toNat : Int) < (2 : Int) ^ (A + B) := by
    exact_mod_cast (ba ++ bb).isLt
  rw [extract_val_bitvec_start_len (A + B) B A
    (↑(ba ++ bb).toNat : Int) (↑(A + B - 1) : Int) ↑B hApp0 hApp1
    (by rfl) (by norm_cast; omega)]
  congr 2
  rw [bitvec_ofInt_natCast_toNat (ba ++ bb),
    BitVec.extractLsb'_append_eq_left]

theorem bvConcat_extract_mid_three_value
    (A B C : Nat) (a b c : Int)
    (ha0 : 0 ≤ a) (ha1 : a < (2 : Int) ^ A)
    (hb0 : 0 ≤ b) (hb1 : b < (2 : Int) ^ B)
    (hc0 : 0 ≤ c) (hc1 : c < (2 : Int) ^ C)
    (hB : 0 < B) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑(B + C - 1))
        (SmtValue.Numeral ↑C)
        (__smtx_model_eval_concat (SmtValue.Binary ↑A a)
          (__smtx_model_eval_concat
            (SmtValue.Binary ↑B b) (SmtValue.Binary ↑C c))) =
      SmtValue.Binary ↑B b := by
  let ba : BitVec A := BitVec.ofInt A a
  let bb : BitVec B := BitVec.ofInt B b
  let bc : BitVec C := BitVec.ofInt C c
  have hBa : (↑ba.toNat : Int) = a := by
    rw [show ba.toNat = a.toNat by
      exact ofInt_toNat_canonical A a ha0 ha1]
    exact Int.toNat_of_nonneg ha0
  have hBb : (↑bb.toNat : Int) = b := by
    rw [show bb.toNat = b.toNat by
      exact ofInt_toNat_canonical B b hb0 hb1]
    exact Int.toNat_of_nonneg hb0
  have hBc : (↑bc.toNat : Int) = c := by
    rw [show bc.toNat = c.toNat by
      exact ofInt_toNat_canonical C c hc0 hc1]
    exact Int.toNat_of_nonneg hc0
  rw [← hBa, ← hBb, ← hBc, concat_bitvec_values,
    concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(ba ++ (bb ++ bc)).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(ba ++ (bb ++ bc)).toNat : Int) <
      (2 : Int) ^ (A + (B + C)) := by
    exact_mod_cast (ba ++ (bb ++ bc)).isLt
  rw [extract_val_bitvec_start_len (A + (B + C)) C B
    (↑(ba ++ (bb ++ bc)).toNat : Int) (↑(B + C - 1) : Int)
    (↑C : Int) hApp0 hApp1 (by rfl) (by norm_cast; omega)]
  congr 2
  rw [bitvec_ofInt_natCast_toNat (ba ++ (bb ++ bc))]
  exact congrArg BitVec.toNat ((extractLsb'_append_low
    (x := ba) (y := bb ++ bc) (L := C) (D := B) (by omega)).trans
      BitVec.extractLsb'_append_eq_left)

theorem bvConcat_extract_high_three_value
    (A B C : Nat) (a b c : Int)
    (ha0 : 0 ≤ a) (ha1 : a < (2 : Int) ^ A)
    (hb0 : 0 ≤ b) (hb1 : b < (2 : Int) ^ B)
    (hc0 : 0 ≤ c) (hc1 : c < (2 : Int) ^ C)
    (hA : 0 < A) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑(A + B + C - 1))
        (SmtValue.Numeral ↑(B + C))
        (__smtx_model_eval_concat (SmtValue.Binary ↑A a)
          (__smtx_model_eval_concat
            (SmtValue.Binary ↑B b) (SmtValue.Binary ↑C c))) =
      SmtValue.Binary ↑A a := by
  let ba : BitVec A := BitVec.ofInt A a
  let bb : BitVec B := BitVec.ofInt B b
  let bc : BitVec C := BitVec.ofInt C c
  have hBa : (↑ba.toNat : Int) = a := by
    rw [show ba.toNat = a.toNat by
      exact ofInt_toNat_canonical A a ha0 ha1]
    exact Int.toNat_of_nonneg ha0
  have hBb : (↑bb.toNat : Int) = b := by
    rw [show bb.toNat = b.toNat by
      exact ofInt_toNat_canonical B b hb0 hb1]
    exact Int.toNat_of_nonneg hb0
  have hBc : (↑bc.toNat : Int) = c := by
    rw [show bc.toNat = c.toNat by
      exact ofInt_toNat_canonical C c hc0 hc1]
    exact Int.toNat_of_nonneg hc0
  rw [← hBa, ← hBb, ← hBc, concat_bitvec_values,
    concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(ba ++ (bb ++ bc)).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(ba ++ (bb ++ bc)).toNat : Int) <
      (2 : Int) ^ (A + (B + C)) := by
    exact_mod_cast (ba ++ (bb ++ bc)).isLt
  rw [extract_val_bitvec_start_len (A + (B + C)) (B + C) A
    (↑(ba ++ (bb ++ bc)).toNat : Int) (↑(A + B + C - 1) : Int)
    (↑(B + C) : Int) hApp0 hApp1 (by rfl) (by norm_cast; omega)]
  congr 2
  rw [bitvec_ofInt_natCast_toNat (ba ++ (bb ++ bc))]
  exact congrArg BitVec.toNat BitVec.extractLsb'_append_eq_left

theorem bvConcat_extract_low_three_value
    (A B C : Nat) (a b c : Int)
    (ha0 : 0 ≤ a) (ha1 : a < (2 : Int) ^ A)
    (hb0 : 0 ≤ b) (hb1 : b < (2 : Int) ^ B)
    (hc0 : 0 ≤ c) (hc1 : c < (2 : Int) ^ C)
    (hC : 0 < C) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑(C - 1))
        (SmtValue.Numeral 0)
        (__smtx_model_eval_concat (SmtValue.Binary ↑A a)
          (__smtx_model_eval_concat
            (SmtValue.Binary ↑B b) (SmtValue.Binary ↑C c))) =
      SmtValue.Binary ↑C c := by
  let ba : BitVec A := BitVec.ofInt A a
  let bb : BitVec B := BitVec.ofInt B b
  let bc : BitVec C := BitVec.ofInt C c
  have hBa : (↑ba.toNat : Int) = a := by
    rw [show ba.toNat = a.toNat by
      exact ofInt_toNat_canonical A a ha0 ha1]
    exact Int.toNat_of_nonneg ha0
  have hBb : (↑bb.toNat : Int) = b := by
    rw [show bb.toNat = b.toNat by
      exact ofInt_toNat_canonical B b hb0 hb1]
    exact Int.toNat_of_nonneg hb0
  have hBc : (↑bc.toNat : Int) = c := by
    rw [show bc.toNat = c.toNat by
      exact ofInt_toNat_canonical C c hc0 hc1]
    exact Int.toNat_of_nonneg hc0
  rw [← hBa, ← hBb, ← hBc, concat_bitvec_values,
    concat_bitvec_values]
  have hApp0 : (0 : Int) ≤ (↑(ba ++ (bb ++ bc)).toNat : Int) :=
    Int.natCast_nonneg _
  have hApp1 : (↑(ba ++ (bb ++ bc)).toNat : Int) <
      (2 : Int) ^ (A + (B + C)) := by
    exact_mod_cast (ba ++ (bb ++ bc)).isLt
  rw [extract_val_bitvec_start_len (A + (B + C)) 0 C
    (↑(ba ++ (bb ++ bc)).toNat : Int) (↑(C - 1) : Int) 0
    hApp0 hApp1 (by rfl) (by norm_cast; omega)]
  congr 2
  rw [bitvec_ofInt_natCast_toNat (ba ++ (bb ++ bc))]
  have hOuter := extractLsb'_append_low
    (x := ba) (y := bb ++ bc) (L := 0) (D := C) (by omega)
  have hInner : (bb ++ bc).extractLsb' 0 C = bc :=
    BitVec.extractLsb'_append_eq_right
  exact congrArg BitVec.toNat (hOuter.trans hInner)
