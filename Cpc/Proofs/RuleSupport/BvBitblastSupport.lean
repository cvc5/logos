module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude
import Cpc.Proofs.RuleSupport.BvNaryAndSupport
import Cpc.Proofs.RuleSupport.BvNaryOrSupport
import Cpc.Proofs.RuleSupport.BvNaryXorSupport
import Cpc.Proofs.RuleSupport.BvBitwiseElimSupport
import Cpc.Proofs.RuleSupport.BvNaryAddSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

namespace BvBitblast

private theorem term_ne_stuck_of_eval_boolean
    {M : SmtModel} {t : Term} {b : Bool}
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  cases h

private theorem mk_apply_eq
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem mk_apply_arg_ne_stuck
    {f x : Term} (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem mk_apply_fun_ne_stuck
    {f x : Term} (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem pair_second_arg_ne_stuck
    {p : Term} (h : __pair_second p ≠ Term.Stuck) :
    p ≠ Term.Stuck := by
  cases p <;> simp_all [__pair_second]

private theorem singleton_elim_arg_ne_stuck {f c : Term}
    (h : __eo_list_singleton_elim f c ≠ Term.Stuck) :
    c ≠ Term.Stuck := by
  intro hc
  subst c
  cases f <;>
    simp_all [__eo_list_singleton_elim, __eo_is_list, __eo_requires,
      native_ite, native_teq]

private theorem mk_from_bools_eq
    {head tail : Term} (hh : head ≠ Term.Stuck) (ht : tail ≠ Term.Stuck) :
    __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp._at_from_bools) head) tail =
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail := by
  rw [mk_apply_eq (by intro h; cases h) hh]
  exact mk_apply_eq (by intro h; cases h) ht

private theorem requires_refl (t result : Term) (ht : t ≠ Term.Stuck) :
    __eo_requires t t result = result := by
  simp [__eo_requires, native_teq, native_ite, native_not, ht]

private theorem requires_result_ne_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    z ≠ Term.Stuck := by
  intro hz
  subst z
  cases x <;> cases y <;>
    simp_all [__eo_requires, native_ite, native_teq]

private theorem eval_eq_is_boolean (x y : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq x y = SmtValue.Boolean b := by
  cases x <;> cases y <;> exact ⟨_, rfl⟩

/--
The natural-number value of CPC's little-endian Boolean list. Its head is the
least-significant bit; this is why `@from_bools b tail` translates to
`concat tail (ite b #b1 #b0)`.
-/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsValue bs + b.toNat

def bitsEq : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x == y) && bitsEq xs ys
  | _, _ => false

inductive BitListSyntax : Term → Prop
  | nil : BitListSyntax (Term.Binary 0 0)
  | cons (bit tail : Term) (ht : BitListSyntax tail) :
      BitListSyntax
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)

theorem BitListSyntax.ne_stuck {t : Term} (h : BitListSyntax t) :
    t ≠ Term.Stuck := by
  cases h <;> intro hh <;> cases hh

private theorem bitlist_syntax_of_get_nil (f a : Term)
    (hf : f = Term.UOp UserOp._at_from_bools)
    (h : __eo_get_nil_rec f a ≠ Term.Stuck) :
    BitListSyntax a := by
  fun_induction __eo_get_nil_rec f a <;>
    simp_all
  case case3 f g x y ih =>
    have hfg := support_eo_requires_cond_eq_of_non_stuck h
    subst g
    apply BitListSyntax.cons
    apply ih
    exact requires_result_ne_stuck h
  case case4 f nil hnilNe hnotApp =>
    have hnil := support_eo_requires_cond_eq_of_non_stuck h
    cases nil <;> simp_all [__eo_is_list_nil]
    split at hnil <;> simp_all
    exact BitListSyntax.nil

theorem bitlist_syntax_of_is_list (a : Term)
    (h : __eo_is_list (Term.UOp UserOp._at_from_bools) a =
      Term.Boolean true) :
    BitListSyntax a := by
  have hget :
      __eo_get_nil_rec (Term.UOp UserOp._at_from_bools) a ≠
        Term.Stuck := by
    have haNe : a ≠ Term.Stuck := by
      intro ha
      subst a
      cases h
    have his :
        __eo_is_list (Term.UOp UserOp._at_from_bools) a =
          __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) a) := by
      cases a <;> simp_all [__eo_is_list]
    rw [his] at h
    intro hg
    rw [hg] at h
    cases h
  exact bitlist_syntax_of_get_nil _ a rfl hget

inductive BitListsSameLength : Term → Term → Prop
  | nil : BitListsSameLength (Term.Binary 0 0) (Term.Binary 0 0)
  | cons (abit atail bbit btail : Term)
      (ht : BitListsSameLength atail btail) :
      BitListsSameLength
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) abit) atail)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bbit) btail)

theorem bitsEq_eq_true_iff {xs ys : List Bool} :
    bitsEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [bitsEq]
  | cons x xs ih =>
      cases ys with
      | nil => simp [bitsEq]
      | cons y ys =>
          simp [bitsEq, ih]

theorem bitsValue_lt : ∀ bs : List Bool, bitsValue bs < 2 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
      simp only [bitsValue, List.length_cons, Nat.pow_succ]
      have hb : b.toNat ≤ 1 := Bool.toNat_le b
      omega

theorem bitsValue_inj_of_length {xs ys : List Bool}
    (hlen : xs.length = ys.length)
    (hval : bitsValue xs = bitsValue ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          cases x <;> cases y <;> simp [bitsValue] at hval ⊢
          all_goals try omega
          all_goals
            congr 1
            apply ih htail
            omega

theorem ofBoolListLE_toNat (bs : List Bool) :
    (BitVec.ofBoolListLE bs).toNat = bitsValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [BitVec.ofBoolListLE, bitsValue, ih, BitVec.toNat_concat,
        Nat.add_comm, Nat.mul_comm]

theorem ofInt_bitsValue (bs : List Bool) :
    BitVec.ofInt bs.length (bitsValue bs : Int) =
      BitVec.ofBoolListLE bs := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, ofBoolListLE_toNat]
  norm_cast
  exact Nat.mod_eq_of_lt (bitsValue_lt bs)

private theorem native_int_pow2_nat (n : Nat) :
    native_int_pow2 (n : Int) = ((2 ^ n : Nat) : Int) := by
  have hn : ¬ ((n : Int) < 0) := by omega
  simp [native_int_pow2, native_zexp_total, hn]

private theorem bv_toInt_emod (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = (x.toNat : Int) := by
  have hc : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by
    norm_cast
  rw [hc, BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
    exact_mod_cast x.isLt)

theorem ofBoolListLE_zipWith_and :
    ∀ (xs ys : List Bool) (hlen : xs.length = ys.length),
      BitVec.cast (by simp [List.length_zipWith, hlen])
          (BitVec.ofBoolListLE (List.zipWith (· && ·) xs ys)) =
        BitVec.ofBoolListLE xs &&&
          BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  intro xs ys hlen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    BitVec.getLsbD_and]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem ofBoolListLE_zipWith_or :
    ∀ (xs ys : List Bool) (hlen : xs.length = ys.length),
      BitVec.cast (by simp [List.length_zipWith, hlen])
          (BitVec.ofBoolListLE (List.zipWith (· || ·) xs ys)) =
        BitVec.ofBoolListLE xs |||
          BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  intro xs ys hlen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    BitVec.getLsbD_or]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem ofBoolListLE_zipWith_xor :
    ∀ (xs ys : List Bool) (hlen : xs.length = ys.length),
      BitVec.cast (by simp [List.length_zipWith, hlen])
          (BitVec.ofBoolListLE (List.zipWith (· != ·) xs ys)) =
        BitVec.ofBoolListLE xs ^^^
          BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  intro xs ys hlen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    BitVec.getLsbD_xor]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem bitsValue_zipWith_and (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    bitsValue (List.zipWith (· && ·) xs ys) =
      bitsValue xs &&& bitsValue ys := by
  have h := congrArg BitVec.toNat
    (ofBoolListLE_zipWith_and xs ys hlen)
  simpa [ofBoolListLE_toNat] using h

theorem bitsValue_zipWith_or (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    bitsValue (List.zipWith (· || ·) xs ys) =
      bitsValue xs ||| bitsValue ys := by
  have h := congrArg BitVec.toNat
    (ofBoolListLE_zipWith_or xs ys hlen)
  simpa [ofBoolListLE_toNat] using h

theorem bitsValue_zipWith_xor (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    bitsValue (List.zipWith (· != ·) xs ys) =
      bitsValue xs ^^^ bitsValue ys := by
  have h := congrArg BitVec.toNat
    (ofBoolListLE_zipWith_xor xs ys hlen)
  simpa [ofBoolListLE_toNat] using h

private theorem ofInt_bitsValue_width (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    BitVec.ofInt xs.length (bitsValue ys : Int) =
      BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  apply BitVec.eq_of_toNat_eq
  simp [ofBoolListLE_toNat]
  exact Nat.mod_eq_of_lt (by simpa [hlen] using bitsValue_lt ys)

private theorem native_and_bits (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    native_mod_total
        (native_binary_and (xs.length : Int)
          (bitsValue xs : Int) (bitsValue ys : Int))
        (native_int_pow2 (xs.length : Int)) =
      (bitsValue (List.zipWith (· && ·) xs ys) : Int) := by
  by_cases hw : xs.length = 0
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero hw
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    subst ys
    rfl
  · rw [native_int_pow2_nat]
    simp only [native_binary_and, native_zeq, native_ite, decide_eq_true_eq]
    rw [if_neg (by exact_mod_cast hw)]
    change
      ((BitVec.ofInt xs.length (bitsValue xs : Int) &&&
          BitVec.ofInt xs.length (bitsValue ys : Int)).toInt %
        ((2 ^ xs.length : Nat) : Int)) =
          (bitsValue (List.zipWith (· && ·) xs ys) : Int)
    rw [show ((2 ^ xs.length : Nat) : Int) =
      (2 : Int) ^ xs.length by norm_cast]
    rw [bv_toInt_emod, ofInt_bitsValue,
      ofInt_bitsValue_width xs ys hlen, BitVec.toNat_and,
      BitVec.toNat_cast, ofBoolListLE_toNat, ofBoolListLE_toNat,
      bitsValue_zipWith_and xs ys hlen]

private theorem native_or_bits (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    native_mod_total
        (native_binary_or (xs.length : Int)
          (bitsValue xs : Int) (bitsValue ys : Int))
        (native_int_pow2 (xs.length : Int)) =
      (bitsValue (List.zipWith (· || ·) xs ys) : Int) := by
  by_cases hw : xs.length = 0
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero hw
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    subst ys
    rfl
  · rw [native_int_pow2_nat]
    simp only [native_binary_or, native_zeq, native_ite, decide_eq_true_eq]
    rw [if_neg (by exact_mod_cast hw)]
    change
      ((BitVec.ofInt xs.length (bitsValue xs : Int) |||
          BitVec.ofInt xs.length (bitsValue ys : Int)).toInt %
        ((2 ^ xs.length : Nat) : Int)) =
          (bitsValue (List.zipWith (· || ·) xs ys) : Int)
    rw [show ((2 ^ xs.length : Nat) : Int) =
      (2 : Int) ^ xs.length by norm_cast]
    rw [bv_toInt_emod, ofInt_bitsValue,
      ofInt_bitsValue_width xs ys hlen, BitVec.toNat_or,
      BitVec.toNat_cast, ofBoolListLE_toNat, ofBoolListLE_toNat,
      bitsValue_zipWith_or xs ys hlen]

private theorem native_xor_bits (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    native_mod_total
        (native_binary_xor (xs.length : Int)
          (bitsValue xs : Int) (bitsValue ys : Int))
        (native_int_pow2 (xs.length : Int)) =
      (bitsValue (List.zipWith (· != ·) xs ys) : Int) := by
  by_cases hw : xs.length = 0
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero hw
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    subst ys
    rfl
  · rw [native_int_pow2_nat]
    simp only [native_binary_xor, native_zeq, native_ite,
      decide_eq_true_eq]
    rw [if_neg (by exact_mod_cast hw)]
    change
      ((BitVec.ofInt xs.length (bitsValue xs : Int) ^^^
          BitVec.ofInt xs.length (bitsValue ys : Int)).toInt %
        ((2 ^ xs.length : Nat) : Int)) =
          (bitsValue (List.zipWith (· != ·) xs ys) : Int)
    rw [show ((2 ^ xs.length : Nat) : Int) =
      (2 : Int) ^ xs.length by norm_cast]
    rw [bv_toInt_emod, ofInt_bitsValue,
      ofInt_bitsValue_width xs ys hlen, BitVec.toNat_xor,
      BitVec.toNat_cast, ofBoolListLE_toNat, ofBoolListLE_toNat,
      bitsValue_zipWith_xor xs ys hlen]

/--
`BitListEval M t bs` says that `t` is a CPC `@from_bools` spine ending in the
empty bit-vector and that its Boolean heads evaluate, least-significant first,
to `bs`.
-/
inductive BitListEval (M : SmtModel) : Term → List Bool → Prop
  | nil : BitListEval M (Term.Binary 0 0) []
  | cons (b tail : Term) (v : Bool) (vs : List Bool)
      (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean v)
      (ht : BitListEval M tail vs) :
      BitListEval M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) b) tail)
        (v :: vs)

theorem BitListEval.ne_stuck {M : SmtModel} {t : Term} {bs : List Bool}
    (h : BitListEval M t bs) : t ≠ Term.Stuck := by
  cases h <;> intro ht <;> cases ht

theorem BitListEval.eval {M : SmtModel} {t : Term} {bs : List Bool}
    (h : BitListEval M t bs) :
    __smtx_model_eval M (__eo_to_smt t) =
      SmtValue.Binary (bs.length : Int) (bitsValue bs : Int) := by
  induction h with
  | nil => rfl
  | cons b tail v vs hb ht ih =>
      change
        __smtx_model_eval_concat
            (__smtx_model_eval M (__eo_to_smt tail))
            (__smtx_model_eval_ite
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)) =
          SmtValue.Binary ((v :: vs).length : Int)
            (bitsValue (v :: vs) : Int)
      rw [hb, ih]
      have hpowOne : native_int_pow2 1 = 2 := by rfl
      have hpowSucc :
          native_int_pow2 ((vs.length : Int) + 1) =
            ((2 ^ (vs.length + 1) : Nat) : Int) := by
        rw [show (vs.length : Int) + 1 = ((vs.length + 1 : Nat) : Int) by omega]
        exact native_int_pow2_nat (vs.length + 1)
      have hlt := bitsValue_lt vs
      cases v <;>
        simp [__smtx_model_eval_ite, __smtx_model_eval_concat,
          bitsValue, native_zplus, native_mod_total, native_binary_concat,
          native_zmult]
      · rw [hpowOne, hpowSucc, Int.emod_eq_of_lt]
        · rw [Int.mul_comm]
        · exact Int.mul_nonneg (Int.natCast_nonneg _) (by decide)
        · exact_mod_cast (show bitsValue vs * 2 < 2 ^ (vs.length + 1) by
            rw [Nat.pow_succ]
            omega)
      · rw [hpowOne, hpowSucc, Int.emod_eq_of_lt]
        · rw [Int.mul_comm]
        · have hn := Int.natCast_nonneg (bitsValue vs)
          omega
        · exact_mod_cast (show bitsValue vs * 2 + 1 < 2 ^ (vs.length + 1) by
            rw [Nat.pow_succ]
            omega)

private theorem wrap_bool_eval {M : SmtModel} {c : Term} {b : Bool}
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean b) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools) c)
            (Term.Binary 0 0))) =
      SmtValue.Binary 1 (if b then 1 else 0) := by
  have hcNe : c ≠ Term.Stuck := by
    intro h
    subst c
    cases hc
  rw [mk_apply_eq (by intro h; cases h) hcNe]
  rw [mk_apply_eq (by intro h; cases h)
    (by intro h; cases h)]
  have hout :=
    BitListEval.cons c (Term.Binary 0 0) b [] hc
      (BitListEval.nil (M := M))
  rw [hout.eval]
  cases b <;> rfl

theorem BitListSyntax.eval {M : SmtModel} (hM : model_wf M)
    {t : Term} (hs : BitListSyntax t)
    (hnn : term_has_non_none_type (__eo_to_smt t)) :
    ∃ bs : List Bool, BitListEval M t bs := by
  induction hs with
  | nil =>
      exact ⟨[], BitListEval.nil⟩
  | cons bit tail htail ih =>
      let bitSmt :=
        SmtTerm.ite (__eo_to_smt bit)
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
      have hconcat :
          __eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail) =
            SmtTerm.concat (__eo_to_smt tail) bitSmt := by
        rfl
      have hconcatNN :
          term_has_non_none_type
            (SmtTerm.concat (__eo_to_smt tail) bitSmt) := by
        simpa [hconcat] using hnn
      rcases bv_concat_args_of_non_none hconcatNN with
        ⟨wtail, wbit, htailTy, hbitTy⟩
      have htailNN :
          term_has_non_none_type (__eo_to_smt tail) := by
        unfold term_has_non_none_type
        rw [htailTy]
        simp
      have hbitNN : term_has_non_none_type bitSmt := by
        unfold term_has_non_none_type
        rw [hbitTy]
        simp
      rcases ite_args_of_non_none hbitNN with
        ⟨T, hcondTy, _hthenTy, _helseTy, _hT⟩
      have hcondNN :
          term_has_non_none_type (__eo_to_smt bit) := by
        unfold term_has_non_none_type
        rw [hcondTy]
        simp
      have hpres :=
        type_preservation M hM (__eo_to_smt bit) hcondNN
      rw [hcondTy] at hpres
      rcases bool_value_canonical hpres with ⟨b, hb⟩
      rcases ih htailNN with ⟨bs, hbs⟩
      exact ⟨b :: bs, BitListEval.cons bit tail b bs hb hbs⟩

theorem BitListsSameLength.syntax_left {a b : Term}
    (h : BitListsSameLength a b) : BitListSyntax a := by
  induction h with
  | nil => exact BitListSyntax.nil
  | cons abit atail bbit btail ht ih =>
      exact BitListSyntax.cons abit atail ih

theorem BitListsSameLength.syntax_right {a b : Term}
    (h : BitListsSameLength a b) : BitListSyntax b := by
  induction h with
  | nil => exact BitListSyntax.nil
  | cons abit atail bbit btail ht ih =>
      exact BitListSyntax.cons bbit btail ih

theorem BitListsSameLength.eval_length {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (hs : BitListsSameLength a b)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys) :
    xs.length = ys.length := by
  induction hs generalizing xs ys with
  | nil =>
      cases ha
      cases hb
      rfl
  | cons abit atail bbit btail ht ih =>
      cases ha with
      | cons _ _ _ xs _ hat =>
          cases hb with
          | cons _ _ _ ys _ hbt =>
              simpa using congrArg Nat.succ (ih hat hbt)

theorem bitblast_apply_unary_syntax (f a : Term)
    (h : __bv_bitblast_apply_unary f a ≠ Term.Stuck) :
    BitListSyntax a := by
  fun_induction __bv_bitblast_apply_unary f a <;> simp_all
  · exact BitListSyntax.nil
  · apply BitListSyntax.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

theorem bitblast_apply_binary_same_length (f a b : Term)
    (h : __bv_bitblast_apply_binary f a b ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_bitblast_apply_binary f a b <;> simp_all
  · exact BitListsSameLength.nil
  · apply BitListsSameLength.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

theorem bitblast_ult_rec_same_length (a b previous : Term)
    (h : __bv_bitblast_ult_rec a b previous ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_bitblast_ult_rec a b previous <;> simp_all
  · exact BitListsSameLength.nil
  · exact BitListsSameLength.cons _ _ _ _ (by apply_assumption)

theorem bitblast_ult_shape (a b orEqual : Term)
    (h : __bv_bitblast_ult a b orEqual ≠ Term.Stuck) :
    ∃ x xtail y ytail,
      a =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail ∧
      b =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail ∧
      BitListsSameLength xtail ytail := by
  unfold __bv_bitblast_ult at h
  split at h <;> simp_all
  refine ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, ?_⟩
  exact bitblast_ult_rec_same_length _ _ _ h

private theorem bitlist_rev_is_list (a : Term)
    (h : __eo_list_rev (Term.UOp UserOp._at_from_bools) a ≠
      Term.Stuck) :
    __eo_is_list (Term.UOp UserOp._at_from_bools) a =
      Term.Boolean true := by
  have hReq :
      __eo_requires
          (__eo_is_list (Term.UOp UserOp._at_from_bools) a)
          (Term.Boolean true)
          (__eo_list_rev_rec a
            (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) a)) ≠
        Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact support_eo_requires_cond_eq_of_non_stuck hReq

theorem bitlist_rev_syntax (a : Term)
    (h : __eo_list_rev (Term.UOp UserOp._at_from_bools) a ≠
      Term.Stuck) :
    BitListSyntax a :=
  bitlist_syntax_of_is_list a (bitlist_rev_is_list a h)

theorem bitblast_slt_args_ne_stuck (a b orEqual : Term)
    (h : __bv_bitblast_slt_impl a b orEqual ≠ Term.Stuck) :
    a ≠ Term.Stuck ∧ b ≠ Term.Stuck := by
  unfold __bv_bitblast_slt_impl at h
  split at h <;> simp_all [__eo_mk_apply]

theorem ripple_carry_same_length (a b carry res : Term)
    (h : __bv_ripple_carry_adder_2 a b carry res ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_ripple_carry_adder_2 a b carry res <;> simp_all
  · apply BitListsSameLength.cons
    apply_assumption
  · exact BitListsSameLength.nil

private theorem bitblast_step_ite_shape (c a b : Term)
    (h : __bv_mk_bitblast_step_ite c a b ≠ Term.Stuck) :
    ∃ bit : Term,
      c = Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bit)
          (Term.Binary 0 0) ∧
      BitListsSameLength a b := by
  fun_induction __bv_mk_bitblast_step_ite c a b <;>
    simp_all [__eo_mk_apply]
  · apply BitListsSameLength.cons
    apply_assumption
    intro hrec
    simp [hrec] at h
  · exact BitListsSameLength.nil

theorem BitListEval.apply_not {M : SmtModel} {t : Term} {bs : List Bool}
    (h : BitListEval M t bs) :
    BitListEval M
      (__bv_bitblast_apply_unary (Term.UOp UserOp.not) t)
      (bs.map (!·)) := by
  induction h with
  | nil =>
      exact BitListEval.nil
  | cons b tail v vs hb ht ih =>
      have hh :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) b)) =
            SmtValue.Boolean (!v) := by
        change
          __smtx_model_eval_not (__smtx_model_eval M (__eo_to_smt b)) =
            SmtValue.Boolean (!v)
        rw [hb]
        cases v <;> rfl
      simp only [__bv_bitblast_apply_unary]
      rw [mk_apply_eq (by intro h; cases h) (BitListEval.ne_stuck ih)]
      exact
        BitListEval.cons (Term.Apply (Term.UOp UserOp.not) b)
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) tail)
          (!v) (vs.map (!·)) hh ih

private theorem binary_app_and_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.and) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.and) a)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) b)
          (Term.Boolean true)) := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem binary_app_or_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.or) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) a)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) b)
          (Term.Boolean false)) := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem binary_app_xor_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.xor) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem binary_app_eq_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.eq) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem eval_binary_and {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.and) a b)) =
      SmtValue.Boolean (x && y) := by
  rw [binary_app_and_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_and
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean true)) =
      SmtValue.Boolean (x && y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

private theorem eval_binary_or {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.or) a b)) =
      SmtValue.Boolean (x || y) := by
  rw [binary_app_or_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_or
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval_or
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean false)) =
      SmtValue.Boolean (x || y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

private theorem eval_binary_xor {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.xor) a b)) =
      SmtValue.Boolean (x != y) := by
  rw [binary_app_xor_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_xor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean (x != y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

private theorem eval_binary_eq {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.eq) a b)) =
      SmtValue.Boolean (x == y) := by
  rw [binary_app_eq_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean (x == y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

theorem BitListEval.apply_and {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)
      (List.zipWith (· && ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_and hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.and) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.and) atail btail)
              (x && y) (List.zipWith (· && ·) xs ys)
              (eval_binary_and hax hby) (ih hbt htail)

theorem BitListEval.apply_or {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)
      (List.zipWith (· || ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_or hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.or) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.or) atail btail)
              (x || y) (List.zipWith (· || ·) xs ys)
              (eval_binary_or hax hby) (ih hbt htail)

theorem BitListEval.apply_xor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)
      (List.zipWith (· != ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_xor hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.xor) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) atail btail)
              (x != y) (List.zipWith (· != ·) xs ys)
              (eval_binary_xor hax hby) (ih hbt htail)

theorem BitListEval.apply_eq {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)
      (List.zipWith (· == ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_eq hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.eq) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) atail btail)
              (x == y) (List.zipWith (· == ·) xs ys)
              (eval_binary_eq hax hby) (ih hbt htail)

theorem BitListEval.eval_bvand {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have hout := (ha.apply_and hb hlen).eval
  rw [hout, ha.eval, hb.eval]
  simp only [__smtx_model_eval_bvand]
  rw [native_and_bits xs ys hlen]
  simp [List.length_zipWith, hlen]

theorem BitListEval.eval_bvor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have hout := (ha.apply_or hb hlen).eval
  rw [hout, ha.eval, hb.eval]
  simp only [__smtx_model_eval_bvor]
  rw [native_or_bits xs ys hlen]
  simp [List.length_zipWith, hlen]

theorem BitListEval.eval_bvxor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have hout := (ha.apply_xor hb hlen).eval
  rw [hout, ha.eval, hb.eval]
  simp only [__smtx_model_eval_bvxor]
  rw [native_xor_bits xs ys hlen]
  simp [List.length_zipWith, hlen]

private theorem zipWith_eq_eq_map_not_xor :
    ∀ (xs ys : List Bool),
      List.zipWith (· == ·) xs ys =
        (List.zipWith (· != ·) xs ys).map (!·) := by
  intro xs
  induction xs with
  | nil => intro ys; rfl
  | cons x xs ih =>
      intro ys
      cases ys with
      | nil => rfl
      | cons y ys =>
          cases x <;> cases y <;>
            simp [ih ys]

theorem BitListEval.apply_ite {M : SmtModel}
    {c a b : Term} {cv : Bool} {xs ys : List Bool}
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean cv)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_ite c a b)
      (List.zipWith (fun x y => if cv then x else y) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil =>
          rw [__bv_bitblast_apply_ite.eq_2 c
            (term_ne_stuck_of_eval_boolean hc)]
          exact BitListEval.nil
      | cons =>
          simp at hlen
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have hhead :
              __smtx_model_eval_ite
                  (__smtx_model_eval M (__eo_to_smt c))
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) =
                SmtValue.Boolean (if cv then x else y) := by
            rw [hc, hax, hby]
            cases cv <;> rfl
          have htail : xs.length = ys.length := by simpa using hlen
          have hheadNe :
              Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b ≠
                Term.Stuck := by intro h; cases h
          rw [__bv_bitblast_apply_ite.eq_3 _ _ _ _ _
            (term_ne_stuck_of_eval_boolean hc)]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b)
              (__bv_bitblast_apply_ite c atail btail)
              (if cv then x else y)
              (List.zipWith (fun x y => if cv then x else y) xs ys)
              hhead (ih hbt htail)

private theorem eval_ite_bit {M : SmtModel}
    {c x y : Term} {cb xb yb : Bool}
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean cb)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.or)
                  (Term.Apply (Term.UOp UserOp.not) c))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.or) x)
                  (Term.Boolean false))))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.or) c)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.or) y)
                    (Term.Boolean false))))
              (Term.Boolean true)))) =
      SmtValue.Boolean (if cb then xb else yb) := by
  change
    __smtx_model_eval_and
      (__smtx_model_eval_or
        (__smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt c)))
        (__smtx_model_eval_or
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Boolean false)))
      (__smtx_model_eval_and
        (__smtx_model_eval_or
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval_or
            (__smtx_model_eval M (__eo_to_smt y))
            (SmtValue.Boolean false)))
        (SmtValue.Boolean true)) =
      SmtValue.Boolean (if cb then xb else yb)
  rw [hc, hx, hy]
  cases cb <;> cases xb <;> cases yb <;> rfl

private theorem bitblast_step_ite_eval {M : SmtModel}
    {cbit a b : Term} {cb : Bool} {xs ys : List Bool}
    (hc : __smtx_model_eval M (__eo_to_smt cbit) =
      SmtValue.Boolean cb)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_mk_bitblast_step_ite
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
          (Term.Binary 0 0))
        a b)
      (List.zipWith (fun x y => if cb then x else y) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil => exact BitListEval.nil
      | cons => simp at hlen
  | cons x xtail xb xs hx hxt ih =>
      cases hb with
      | nil => simp at hlen
      | cons y ytail yb ys hy hyt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_mk_bitblast_step_ite.eq_1]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hyt htail))]
          exact BitListEval.cons _ _ _ _
            (eval_ite_bit hc hx hy) (ih hyt htail)

private theorem zipWith_left_of_length {α β : Type}
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    List.zipWith (fun x _ => x) xs ys = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.cons.injEq, true_and]
          apply ih
          simpa using h

private theorem zipWith_right_of_length {α β : Type}
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    List.zipWith (fun _ y => y) xs ys = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.cons.injEq, true_and]
          apply ih
          simpa using h

theorem BitListEval.concat {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys) :
    BitListEval M (__bv_bitblast_concat a b) (xs ++ ys) := by
  induction ha with
  | nil =>
      rw [__bv_bitblast_concat.eq_3 b (BitListEval.ne_stuck hb)]
      exact hb
  | cons head tail x xs hhead htail ih =>
      rw [__bv_bitblast_concat.eq_2 b head tail
        (BitListEval.ne_stuck hb)]
      rw [mk_apply_eq (by intro h; cases h) (BitListEval.ne_stuck ih)]
      simpa using BitListEval.cons head (__bv_bitblast_concat tail b)
        x (xs ++ ys) hhead ih

private theorem list_rev_rec_nil (acc : Term) (hacc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Binary 0 0) acc = acc := by
  cases acc <;> simp_all [__eo_list_rev_rec]

private theorem list_rev_rec_cons
    (head tail acc : Term) (hacc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail)
        acc =
      __eo_list_rev_rec tail
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) head) acc) := by
  cases acc <;> simp_all [__eo_list_rev_rec]

private theorem BitListEval.rev_rec {M : SmtModel}
    {t acc : Term} {xs ys : List Bool}
    (ht : BitListEval M t xs) (ha : BitListEval M acc ys) :
    BitListEval M (__eo_list_rev_rec t acc) (xs.reverse ++ ys) := by
  induction ht generalizing acc ys with
  | nil =>
      rw [list_rev_rec_nil acc (BitListEval.ne_stuck ha)]
      simpa using ha
  | cons head tail x xs hhead htail ih =>
      rw [list_rev_rec_cons head tail acc (BitListEval.ne_stuck ha)]
      have hcons := BitListEval.cons head acc x ys hhead ha
      have hrec := ih hcons
      simpa [List.reverse_cons, List.append_assoc] using hrec

private theorem BitListEval.get_nil {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    __eo_get_nil_rec (Term.UOp UserOp._at_from_bools) t =
      Term.Binary 0 0 := by
  induction h with
  | nil =>
      exact requires_refl _ _ (by intro hh; cases hh)
  | cons head tail x xs hhead htail ih =>
      show
        __eo_requires (Term.UOp UserOp._at_from_bools)
            (Term.UOp UserOp._at_from_bools)
            (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) tail) =
          Term.Binary 0 0
      rw [requires_refl _ _ (by intro hh; cases hh)]
      exact ih

private theorem BitListEval.is_list {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    __eo_is_list (Term.UOp UserOp._at_from_bools) t =
      Term.Boolean true := by
  have hnil := h.get_nil
  have hne := h.ne_stuck
  cases t <;>
    simp_all [__eo_is_list, __eo_is_ok, native_not, native_teq,
      reduceCtorEq]

theorem BitListEval.rev {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    BitListEval M
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) t)
      xs.reverse := by
  change
    BitListEval M
      (__eo_requires
        (__eo_is_list (Term.UOp UserOp._at_from_bools) t)
        (Term.Boolean true)
        (__eo_list_rev_rec t
          (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) t)))
      xs.reverse
  rw [h.is_list, h.get_nil,
    requires_refl _ _ (by intro hh; cases hh)]
  simpa using h.rev_rec (BitListEval.nil (M := M))

theorem BitListEval.eq_rec_eval {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_eq_rec a b)) =
      SmtValue.Boolean (bitsEq xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil => rfl
      | cons => simp at hlen
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil => simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := ih hbt htail
          rw [__bv_mk_bitblast_step_eq_rec.eq_2]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hrec)]
          change
            __smtx_model_eval_and
                (__smtx_model_eval_eq
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)))
                (__smtx_model_eval M
                  (__eo_to_smt (__bv_mk_bitblast_step_eq_rec atail btail))) =
              SmtValue.Boolean (bitsEq (x :: xs) (y :: ys))
          rw [hax, hby, hrec]
          cases x <;> cases y <;>
            simp [bitsEq, __smtx_model_eval_eq, native_veq,
              __smtx_model_eval_and, SmtEval.native_and]

private theorem eq_rec_same_length (a b : Term)
    (h : __bv_mk_bitblast_step_eq_rec a b ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_mk_bitblast_step_eq_rec a b <;>
    simp_all [__eo_mk_apply]
  · exact BitListsSameLength.nil
  · apply BitListsSameLength.cons
    apply_assumption
    intro hrec
    simp [hrec] at h

private theorem BitListEval.eq_rec_get_nil {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __eo_get_nil_rec (Term.UOp UserOp.and)
        (__bv_mk_bitblast_step_eq_rec a b) =
      Term.Boolean true := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil => rfl
      | cons => simp at hlen
  | cons abit atail x xs hax hat ih =>
      cases hb with
      | nil => simp at hlen
      | cons bbit btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := hat.eq_rec_eval hbt htail
          rw [__bv_mk_bitblast_step_eq_rec.eq_2]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hrec)]
          change
            __eo_requires (Term.UOp UserOp.and) (Term.UOp UserOp.and)
                (__eo_get_nil_rec (Term.UOp UserOp.and)
                  (__bv_mk_bitblast_step_eq_rec atail btail)) =
              Term.Boolean true
          rw [requires_refl _ _ (by intro h; cases h)]
          exact ih hbt htail

private theorem BitListEval.eq_rec_is_list {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __eo_is_list (Term.UOp UserOp.and)
        (__bv_mk_bitblast_step_eq_rec a b) =
      Term.Boolean true := by
  have hnil := ha.eq_rec_get_nil hb hlen
  have hne :=
    term_ne_stuck_of_eval_boolean (ha.eq_rec_eval hb hlen)
  generalize hc :
      __bv_mk_bitblast_step_eq_rec a b = c at hnil hne ⊢
  cases c <;>
    simp_all [__eo_is_list, __eo_is_ok, native_not, native_teq,
      reduceCtorEq]

theorem BitListEval.eq_step_eval {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__bv_mk_bitblast_step_eq_rec a b))) =
      SmtValue.Boolean (bitsEq xs ys) := by
  rw [__eo_list_singleton_elim, ha.eq_rec_is_list hb hlen,
    requires_refl _ _ (by intro h; cases h)]
  cases ha with
  | nil =>
      cases hb with
      | nil => rfl
      | cons => simp at hlen
  | cons abit atail x xs hax hat =>
      cases hb with
      | nil => simp at hlen
      | cons bbit btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := hat.eq_rec_eval hbt htail
          rw [__bv_mk_bitblast_step_eq_rec.eq_2]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hrec)]
          cases hat with
          | nil =>
              cases hbt with
              | nil =>
                  change
                    __smtx_model_eval M
                        (__eo_to_smt
                          (__eo_ite (Term.Boolean true)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.eq) abit) bbit)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.and)
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.eq) abit)
                                  bbit))
                              (Term.Boolean true)))) =
                      SmtValue.Boolean (bitsEq [x] [y])
                  rw [show
                    __eo_ite (Term.Boolean true)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.eq) abit) bbit)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.and)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.eq) abit)
                              bbit))
                          (Term.Boolean true)) =
                      Term.Apply
                        (Term.Apply (Term.UOp UserOp.eq) abit) bbit by
                    rfl]
                  have heq := eval_binary_eq hax hby
                  rw [binary_app_eq_eq
                    (term_ne_stuck_of_eval_boolean hax)
                    (term_ne_stuck_of_eval_boolean hby)] at heq
                  simpa [bitsEq] using heq
              | cons => simp at htail
          | cons tailHead tailTail xv xvs hth htt =>
              cases hbt with
              | nil => simp at htail
              | cons otherHead otherTail yv yvs hoh hot =>
                  have htailtail : xvs.length = yvs.length := by
                    simpa using htail
                  have htailEval := htt.eq_rec_eval hot htailtail
                  have htailNotNil :
                      __eo_is_list_nil (Term.UOp UserOp.and)
                          (__bv_mk_bitblast_step_eq_rec
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at_from_bools)
                                tailHead) tailTail)
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at_from_bools)
                                otherHead) otherTail)) =
                        Term.Boolean false := by
                    rw [__bv_mk_bitblast_step_eq_rec.eq_2]
                    rw [mk_apply_eq (by intro h; cases h)
                      (term_ne_stuck_of_eval_boolean htailEval)]
                    rfl
                  have hfull :=
                    (BitListEval.cons abit
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp._at_from_bools)
                          tailHead) tailTail)
                      x (xv :: xvs) hax
                      (BitListEval.cons tailHead tailTail xv xvs hth htt)).eq_rec_eval
                      (BitListEval.cons bbit
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp._at_from_bools)
                            otherHead) otherTail)
                        y (yv :: yvs) hby
                        (BitListEval.cons otherHead otherTail yv yvs hoh hot))
                      hlen
                  rw [__bv_mk_bitblast_step_eq_rec.eq_2,
                    mk_apply_eq (by intro h; cases h)
                      (term_ne_stuck_of_eval_boolean hrec)] at hfull
                  rw [__eo_list_singleton_elim_2, htailNotNil]
                  simp [__eo_ite, native_ite, native_teq]
                  exact hfull

def fullSum (x y carry : Bool) : Bool :=
  (x != y) != carry

def fullCarry (x y carry : Bool) : Bool :=
  (x && y) || ((x != y) && carry)

def addBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | x :: xs, y :: ys, carry =>
      fullSum x y carry :: addBits xs ys (fullCarry x y carry)
  | _, _, _ => []

def addCarry : List Bool → List Bool → Bool → Bool
  | [], [], carry => carry
  | x :: xs, y :: ys, carry =>
      addCarry xs ys (fullCarry x y carry)
  | _, _, carry => carry

private def sumTerm (x y carry : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.xor)
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
    carry

private def carryTerm (x y carry : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.or)
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
          (Term.Boolean true))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) carry)
            (Term.Boolean true))))
      (Term.Boolean false))

private theorem eval_sumTerm {M : SmtModel}
    {x y carry : Term} {xb yb cb : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb)
    (hc : __smtx_model_eval M (__eo_to_smt carry) = SmtValue.Boolean cb) :
    __smtx_model_eval M (__eo_to_smt (sumTerm x y carry)) =
      SmtValue.Boolean (fullSum xb yb cb) := by
  change
    __smtx_model_eval_xor
      (__smtx_model_eval_xor
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)))
      (__smtx_model_eval M (__eo_to_smt carry)) =
      SmtValue.Boolean (fullSum xb yb cb)
  rw [hx, hy, hc]
  cases xb <;> cases yb <;> cases cb <;> rfl

private theorem eval_carryTerm {M : SmtModel}
    {x y carry : Term} {xb yb cb : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb)
    (hc : __smtx_model_eval M (__eo_to_smt carry) = SmtValue.Boolean cb) :
    __smtx_model_eval M (__eo_to_smt (carryTerm x y carry)) =
      SmtValue.Boolean (fullCarry xb yb cb) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_and
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt y))
          (SmtValue.Boolean true)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval_xor
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt y)))
          (__smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt carry))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      SmtValue.Boolean (fullCarry xb yb cb)
  rw [hx, hy, hc]
  cases xb <;> cases yb <;> cases cb <;> rfl

inductive BitPairEval (M : SmtModel) : Term → Bool → List Bool → Prop
  | intro (carryTerm bitsTerm : Term) (carry : Bool) (bits : List Bool)
      (carry_eval :
        __smtx_model_eval M (__eo_to_smt carryTerm) =
          SmtValue.Boolean carry)
      (bits_eval : BitListEval M bitsTerm bits) :
      BitPairEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair) carryTerm) bitsTerm)
        carry bits

theorem BitPairEval.first_eval {M : SmtModel} {t : Term}
    {carry : Bool} {bits : List Bool} (h : BitPairEval M t carry bits) :
    __smtx_model_eval M (__eo_to_smt (__pair_first t)) =
      SmtValue.Boolean carry := by
  rcases h with ⟨ct, bt, carry, bits, hc, hb⟩
  exact hc

theorem BitPairEval.second {M : SmtModel} {t : Term}
    {carry : Bool} {bits : List Bool} (h : BitPairEval M t carry bits) :
    BitListEval M (__pair_second t) bits := by
  rcases h with ⟨ct, bt, carry, bits, hc, hb⟩
  exact hb

private theorem ripple_carry_eval_acc {M : SmtModel}
    {a b carry res : Term} {xs ys rs : List Bool} {cb : Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hc :
      __smtx_model_eval M (__eo_to_smt carry) =
        SmtValue.Boolean cb)
    (hr : BitListEval M res rs)
    (hlen : xs.length = ys.length) :
    BitPairEval M
      (__bv_ripple_carry_adder_2 a b carry res)
      (addCarry xs ys cb)
      (rs.reverse ++ addBits xs ys cb) := by
  induction ha generalizing b ys carry res rs cb with
  | nil =>
      cases hb with
      | nil =>
          rw [__bv_ripple_carry_adder_2.eq_4 carry res
            (term_ne_stuck_of_eval_boolean hc) hr.ne_stuck]
          have hrev := hr.rev
          rw [mk_apply_eq (by intro h; cases h) hrev.ne_stuck]
          simpa [addCarry, addBits] using
            BitPairEval.intro carry
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) res)
              cb rs.reverse hc (by simpa using hrev)
      | cons => simp at hlen
  | cons x xtail xb xs hx hxtail ih =>
      cases hb with
      | nil => simp at hlen
      | cons y ytail yb ys hy hytail =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hsum := eval_sumTerm hx hy hc
          have hcarry := eval_carryTerm hx hy hc
          have hnewRes :
              BitListEval M
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_from_bools)
                    (sumTerm x y carry))
                  res)
                (fullSum xb yb cb :: rs) :=
            BitListEval.cons (sumTerm x y carry) res
              (fullSum xb yb cb) rs hsum hr
          rw [__bv_ripple_carry_adder_2.eq_3 carry res x xtail y ytail
            (term_ne_stuck_of_eval_boolean hc) hr.ne_stuck]
          have hrec :=
            ih hytail hcarry hnewRes htail
          have hsimpa := hrec
          try simp [addBits, addCarry, List.reverse_cons, List.append_assoc] at hsimpa ⊢
          exact hsimpa

theorem ripple_carry_eval {M : SmtModel}
    {a b carry : Term} {xs ys : List Bool} {cb : Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hc :
      __smtx_model_eval M (__eo_to_smt carry) =
        SmtValue.Boolean cb)
    (hlen : xs.length = ys.length) :
    BitPairEval M
      (__bv_ripple_carry_adder_2 a b carry (Term.Binary 0 0))
      (addCarry xs ys cb)
      (addBits xs ys cb) := by
  simpa using ripple_carry_eval_acc ha hb hc
    (BitListEval.nil (M := M)) hlen

def shiftAddStepBits :
    Bool → List Bool → Nat → List Bool → Bool → List Bool
  | _, _, _, [], _ => []
  | b, y :: ys, 0, r :: rs, carry =>
      fullSum r (b && y) carry ::
        shiftAddStepBits b ys 0 rs (fullCarry r (b && y) carry)
  | b, ys, k + 1, r :: rs, carry =>
      r :: shiftAddStepBits b ys k rs carry
  | _, [], 0, _ :: _, _ => []

private theorem shift_add_step_eval {M : SmtModel}
    {b1 a2 res carry : Term} {b : Bool} {ys rs : List Bool}
    {cb : Bool} (k : Nat)
    (hb : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Boolean b)
    (ha2 : BitListEval M a2 ys)
    (hres : BitListEval M res rs)
    (hc : __smtx_model_eval M (__eo_to_smt carry) = SmtValue.Boolean cb)
    (hk : k ≤ rs.length)
    (hlen : rs.length ≤ k + ys.length) :
    BitListEval M
      (__bv_shift_add_multiplier_rec_step b1 a2
        (Term.Numeral (k : Int)) res carry)
      (shiftAddStepBits b ys k rs cb) := by
  induction hres generalizing k a2 ys carry cb with
  | nil =>
      have hk0 : k = 0 := by simpa using hk
      subst k
      have hz : (↑(0 : Nat) : Int) = 0 := rfl
      rw [hz]
      rw [shiftAddStepBits]
      rw [__bv_shift_add_multiplier_rec_step.eq_5 b1 a2 carry
        (term_ne_stuck_of_eval_boolean hb) ha2.ne_stuck
        (term_ne_stuck_of_eval_boolean hc)]
      exact BitListEval.nil
  | cons r rt rb rs hr hrt ih =>
      cases k with
      | zero =>
          cases ha2 with
          | nil => simp at hlen
          | cons y yt yb ys hy hyt =>
              let p :=
                Term.Apply (Term.Apply (Term.UOp UserOp.and) b1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
                    (Term.Boolean true))
              have hp :
                  __smtx_model_eval M (__eo_to_smt p) =
                    SmtValue.Boolean (b && yb) := by
                have hp0 := eval_binary_and hb hy
                rw [binary_app_and_eq
                  (term_ne_stuck_of_eval_boolean hb)
                  (term_ne_stuck_of_eval_boolean hy)] at hp0
                exact hp0
              have hsum := eval_sumTerm hr hp hc
              have hcarry := eval_carryTerm hr hp hc
              have hrec := ih 0 hyt hcarry
                (by omega) (by simpa using hlen)
              have hz : (↑(0 : Nat) : Int) = 0 := rfl
              rw [hz] at hrec ⊢
              rw [shiftAddStepBits]
              rw [__bv_shift_add_multiplier_rec_step.eq_6 b1 carry
                y yt r rt (term_ne_stuck_of_eval_boolean hb)
                (term_ne_stuck_of_eval_boolean hc)]
              dsimp [p, sumTerm, carryTerm] at hsum hrec ⊢
              rw [mk_apply_eq
                (by intro h; cases h)
                hrec.ne_stuck]
              exact BitListEval.cons _ _ _ _ hsum hrec
      | succ k =>
          simp only [List.length_cons] at hk hlen
          have hrec := ih k ha2 hc (by omega) (by omega)
          rw [__bv_shift_add_multiplier_rec_step.eq_7 b1 a2
            (Term.Numeral (↑(k + 1) : Int)) carry r rt
            (term_ne_stuck_of_eval_boolean hb) ha2.ne_stuck
            (by intro h; cases h)
            (by
              intro b2 a2tail haShape hzero
              have hz : (↑(k + 1) : Int) = 0 := by
                injection hzero
              omega)
            (term_ne_stuck_of_eval_boolean hc)]
          simp only [__eo_add, native_zplus]
          have hkInt : (↑(k + 1) : Int) + -1 = ↑k := by omega
          rw [hkInt]
          have hks : k + 1 = Nat.succ k := by omega
          rw [hks, shiftAddStepBits]
          change
            BitListEval M
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp._at_from_bools) r)
                (__bv_shift_add_multiplier_rec_step b1 a2
                  (Term.Numeral (k : Int)) rt carry))
              (rb :: shiftAddStepBits b ys k rs cb)
          rw [mk_apply_eq
            (by intro h; cases h)
            hrec.ne_stuck]
          exact BitListEval.cons _ _ _ _ hr hrec

private theorem shiftAddStepBits_eq :
    ∀ (b : Bool) (ys : List Bool) (k : Nat) (rs : List Bool)
      (carry : Bool),
      k ≤ rs.length →
      rs.length ≤ k + ys.length →
      shiftAddStepBits b ys k rs carry =
        rs.take k ++
          addBits (rs.drop k)
            ((ys.take (rs.length - k)).map (b && ·)) carry := by
  intro b ys k rs carry hk hlen
  induction rs generalizing k ys carry with
  | nil =>
      simp [shiftAddStepBits, addBits]
  | cons r rs ih =>
      cases k with
      | zero =>
          cases ys with
          | nil => simp at hlen
          | cons y ys =>
              simp only [List.length_cons] at hlen
              have htail : rs.length ≤ ys.length := by omega
              simp only [shiftAddStepBits, List.take_zero, List.drop_zero,
                List.nil_append, Nat.sub_zero]
              rw [ih ys 0 (fullCarry r (b && y) carry)
                (by omega) (by simpa using htail)]
              simp only [List.take_zero, List.drop_zero, List.nil_append,
                Nat.sub_zero, List.length_cons, List.take_succ_cons,
                List.map_cons, addBits]
      | succ k =>
          simp only [List.length_cons] at hk hlen
          have hk' : k ≤ rs.length := by omega
          have hlen' : rs.length ≤ k + ys.length := by omega
          rw [shiftAddStepBits]
          simp only [List.take_succ_cons, List.drop_succ_cons,
            List.cons_append]
          rw [ih ys k carry hk' hlen']
          simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]

def shiftAddRecBits :
    List Bool → Nat → List Bool → List Bool → List Bool
  | _, _, [], rs => rs
  | ys, k, b :: bs, rs =>
      shiftAddRecBits ys (k + 1) bs
        (shiftAddStepBits b ys k rs false)

private theorem shift_add_rec_res_ne
    {a1 a2 k res : Term}
    (h : __bv_shift_add_multiplier_rec a1 a2 k res ≠ Term.Stuck) :
    res ≠ Term.Stuck := by
  intro hr
  subst res
  apply h
  cases a1 <;> cases a2 <;> cases k <;>
    rfl

private theorem shift_add_rec_first_syntax
    (a1 a2 k res : Term)
    (h : __bv_shift_add_multiplier_rec a1 a2 k res ≠ Term.Stuck) :
    BitListSyntax a1 := by
  fun_induction __bv_shift_add_multiplier_rec a1 a2 k res <;>
    simp_all
  · exact BitListSyntax.nil
  · exact BitListSyntax.cons _ _ (by apply_assumption)

private theorem shift_add_multiplier_shape
    (a2 ac : Term)
    (h : __bv_shift_add_multiplier a2 ac ≠ Term.Stuck) :
    ∃ bit tail,
      ac =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail := by
  fun_cases __bv_shift_add_multiplier a2 ac
  · exfalso
    exact h rfl
  case case2 =>
    rename_i b1 a1 ha2Ne
    exact ⟨b1, a1, rfl⟩
  · exfalso
    apply h
    exact __bv_shift_add_multiplier.eq_3 _ _ (by assumption)
      (by assumption)

theorem addBits_value :
    ∀ (xs ys : List Bool) (carry : Bool),
      xs.length = ys.length →
      bitsValue (addBits xs ys carry) +
          2 ^ xs.length * (addCarry xs ys carry).toNat =
        bitsValue xs + bitsValue ys + carry.toNat := by
  intro xs
  induction xs with
  | nil =>
      intro ys carry hlen
      cases ys
      · cases carry <;> decide
      · simp at hlen
  | cons x xs ih =>
      intro ys carry hlen
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := ih ys (fullCarry x y carry) htail
          simp only [addBits, addCarry, bitsValue, List.length_cons,
            Nat.pow_succ]
          have hbit :
              (fullSum x y carry).toNat +
                  2 * (fullCarry x y carry).toNat =
                x.toNat + y.toNat + carry.toNat := by
            cases x <;> cases y <;> cases carry <;> decide
          have hmul :
              2 ^ xs.length * 2 *
                    (addCarry xs ys (fullCarry x y carry)).toNat =
                2 * (2 ^ xs.length *
                    (addCarry xs ys (fullCarry x y carry)).toNat) := by
            ac_rfl
          rw [hmul]
          omega

theorem addBits_length {xs ys : List Bool} {carry : Bool}
    (hlen : xs.length = ys.length) :
    (addBits xs ys carry).length = xs.length := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys
      · rfl
      · simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          simp only [addBits, List.length_cons]
          exact congrArg Nat.succ
            (ih (ys := ys) (carry := fullCarry x y carry) htail)

private theorem shift_add_rec_eval {M : SmtModel}
    {a1 a2 res : Term} {xs ys rs : List Bool} (k : Nat)
    (ha1 : BitListEval M a1 xs)
    (ha2 : BitListEval M a2 ys)
    (hres : BitListEval M res rs)
    (hlen : ys.length = rs.length)
    (hbound : k + xs.length ≤ rs.length) :
    BitListEval M
      (__bv_shift_add_multiplier_rec a1 a2
        (Term.Numeral (k : Int)) res)
      (shiftAddRecBits ys k xs rs) := by
  induction ha1 generalizing k res rs with
  | nil =>
      rw [shiftAddRecBits]
      rw [__bv_shift_add_multiplier_rec.eq_4 a2
        (Term.Numeral (k : Int)) res ha2.ne_stuck
        (by intro h; cases h) hres.ne_stuck]
      exact hres
  | cons bit tail b bs hb htail ih =>
      have hk : k ≤ rs.length := by
        simp only [List.length_cons] at hbound
        omega
      have hstepBound : rs.length ≤ k + ys.length := by omega
      have hstep :=
        shift_add_step_eval
          (M := M) (b1 := bit) (a2 := a2) (res := res)
          (carry := Term.Boolean false) (b := b) (ys := ys)
          (rs := rs) (cb := false)
          k hb ha2 hres rfl hk hstepBound
      have hstepEq :=
        shiftAddStepBits_eq b ys k rs false hk hstepBound
      have hdropLen :
          (rs.drop k).length =
            ((ys.take (rs.length - k)).map (b && ·)).length := by
        simp only [List.length_drop, List.length_map, List.length_take]
        rw [hlen]
        omega
      have hstepLen :
          (shiftAddStepBits b ys k rs false).length = rs.length := by
        rw [hstepEq, List.length_append,
          addBits_length hdropLen]
        simp [List.length_take, List.length_drop, hk]
      have hrec :=
        ih (k + 1) hstep
          (by omega)
          (by
            simp only [List.length_cons] at hbound
            omega)
      rw [shiftAddRecBits]
      rw [__bv_shift_add_multiplier_rec.eq_5 a2
        (Term.Numeral (k : Int)) res bit tail
        ha2.ne_stuck (by intro h; cases h) hres.ne_stuck]
      simp only [__eo_add, native_zplus]
      have hkInt : (↑k : Int) + 1 = ↑(k + 1) := by omega
      rw [hkInt]
      exact hrec

theorem addBits_value_mod {xs ys : List Bool} {carry : Bool}
    (hlen : xs.length = ys.length) :
    bitsValue (addBits xs ys carry) =
      (bitsValue xs + bitsValue ys + carry.toNat) % (2 ^ xs.length) := by
  have hval := addBits_value xs ys carry hlen
  have hlt := bitsValue_lt (addBits xs ys carry)
  rw [addBits_length hlen] at hlt
  rw [← hval]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]

theorem bitsValue_map_not :
    ∀ xs : List Bool,
      bitsValue (xs.map (!·)) = 2 ^ xs.length - 1 - bitsValue xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hlt := bitsValue_lt xs
      cases x <;>
        simp [bitsValue, ih, Nat.pow_succ]
      all_goals omega

private theorem native_mod_nat (a m : Nat) :
    native_mod_total (a : Int) (m : Int) = ((a % m : Nat) : Int) := by
  simp [native_mod_total]

theorem eval_addBits {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
              (Term.Binary 0 0)))) := by
  have hc :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by rfl
  have hadd := ripple_carry_eval ha hb hc hlen
  have hout := hadd.second
  rw [ha.eval, hb.eval, hout.eval]
  simp only [__smtx_model_eval_bvadd]
  rw [show (addBits xs ys false).length = xs.length from
    addBits_length hlen]
  rw [native_int_pow2_nat]
  simp only [native_zplus]
  have hplus :
      (↑(bitsValue xs) : Int) + ↑(bitsValue ys) =
        (↑(bitsValue xs + bitsValue ys) : Int) := by omega
  rw [hplus, native_mod_nat]
  congr 2
  norm_cast
  exact (addBits_value_mod (carry := false) hlen).symm

theorem eval_bitnot {M : SmtModel}
    {a : Term} {xs : List Bool} (ha : BitListEval M a xs) :
    __smtx_model_eval_bvnot
        (__smtx_model_eval M (__eo_to_smt a)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)) := by
  have hout := ha.apply_not
  rw [ha.eval, hout.eval]
  simp only [__smtx_model_eval_bvnot, native_binary_not,
    native_zplus, native_zneg]
  rw [native_int_pow2_nat, bitsValue_map_not]
  have hlt := bitsValue_lt xs
  have hltI :
      (↑(bitsValue xs) : Int) < (↑(2 ^ xs.length) : Int) := by
    exact_mod_cast hlt
  have hnonneg :
      0 ≤ (↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1) := by
    omega
  have hupper :
      (↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1) <
        (↑(2 ^ xs.length) : Int) := by
    have hp := Nat.two_pow_pos xs.length
    omega
  simp only [List.length_map]
  congr 1
  change
    ((↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1)) %
        (↑(2 ^ xs.length) : Int) =
      (↑(2 ^ xs.length - 1 - bitsValue xs) : Int)
  rw [Int.emod_eq_of_lt hnonneg hupper]
  norm_cast
  omega

theorem BitListEval.eval_bvxnor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)) =
      __smtx_model_eval_bvxnor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have heq := ha.apply_eq hb hlen
  have hxor := ha.apply_xor hb hlen
  have hnot := hxor.apply_not
  rw [heq.eval, zipWith_eq_eq_map_not_xor]
  rw [← hnot.eval]
  rw [← eval_bitnot hxor]
  rw [ha.eval_bvxor hb hlen]
  rfl

private theorem list_repeat_rec_from_bools {M : SmtModel}
    {bit : Term} {b : Bool}
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) =
        SmtValue.Boolean b)
    (hty : __eo_typeof bit ≠ Term.Stuck) :
    ∀ n : Nat,
      BitListEval M
        (__eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit n)
        (List.replicate n b) := by
  intro n
  induction n with
  | zero =>
      rw [__eo_list_repeat_rec.eq_4 _ _ 0
        (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hb)
        (by intro k hk; cases hk)]
      have hnil :
          __eo_nil (Term.UOp UserOp._at_from_bools) (__eo_typeof bit) =
            Term.Binary 0 0 := by
        cases ht : __eo_typeof bit <;> simp_all [__eo_nil]
      rw [hnil]
      exact BitListEval.nil
  | succ n ih =>
      rw [__eo_list_repeat_rec.eq_3 _ _ n
        (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hb)]
      rw [mk_apply_eq (by intro h; cases h) ih.ne_stuck]
      simpa [List.replicate_succ] using
        BitListEval.cons bit
          (__eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit n)
          b (List.replicate n b) hb ih

theorem list_repeat_from_bools {M : SmtModel}
    {bit : Term} {b : Bool}
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) =
        SmtValue.Boolean b)
    (hty : __eo_typeof bit ≠ Term.Stuck)
    (n : Nat) :
    BitListEval M
      (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
        (Term.Numeral (n : Int)))
      (List.replicate n b) := by
  rw [__eo_list_repeat.eq_3 _ _ _ (by intro h; cases h)
    (term_ne_stuck_of_eval_boolean hb)]
  rw [show native_zlt (n : Int) 0 = false by
    simp [native_zlt]]
  simp only [native_ite, Bool.false_eq_true, if_false]
  rw [show native_int_to_nat (n : Int) = n by
    simp [native_int_to_nat]]
  exact list_repeat_rec_from_bools hb hty n

theorem bitsValue_replicate_false (n : Nat) :
    bitsValue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bitsValue, ih]

theorem bitsValue_replicate_true (n : Nat) :
    bitsValue (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, bitsValue, ih, Nat.pow_succ]
      simp only [Bool.toNat_true]
      have hp := Nat.two_pow_pos n
      omega

def ultStep (x y previous : Bool) : Bool :=
  (x == y && previous) || (!x && y)

def ultBits : List Bool → List Bool → Bool → Bool
  | [], [], previous => previous
  | x :: xs, y :: ys, previous =>
      ultBits xs ys (ultStep x y previous)
  | _, _, _ => false

private def ultStepTerm (x y previous : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.or)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) previous)
          (Term.Boolean true))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.UOp UserOp.not) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
            (Term.Boolean true))))
      (Term.Boolean false))

private theorem eval_ultStepTerm {M : SmtModel}
    {x y previous : Term} {xb yb pb : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb)
    (hp :
      __smtx_model_eval M (__eo_to_smt previous) =
        SmtValue.Boolean pb) :
    __smtx_model_eval M (__eo_to_smt (ultStepTerm x y previous)) =
      SmtValue.Boolean (ultStep xb yb pb) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt previous))
          (SmtValue.Boolean true)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval M (__eo_to_smt x)))
          (__smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt y))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      SmtValue.Boolean (ultStep xb yb pb)
  rw [hx, hy, hp]
  cases xb <;> cases yb <;> cases pb <;> rfl

private theorem bitblast_ult_rec_eval {M : SmtModel}
    {a b previous : Term} {xs ys : List Bool} {pb : Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hp :
      __smtx_model_eval M (__eo_to_smt previous) =
        SmtValue.Boolean pb)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_ult_rec a b previous)) =
      SmtValue.Boolean (ultBits xs ys pb) := by
  induction ha generalizing b ys previous pb with
  | nil =>
      cases hb with
      | nil =>
          rw [__bv_bitblast_ult_rec.eq_2 previous
            (term_ne_stuck_of_eval_boolean hp)]
          simpa [ultBits] using hp
      | cons => simp at hlen
  | cons x xtail xb xs hx hxtail ih =>
      cases hb with
      | nil => simp at hlen
      | cons y ytail yb ys hy hytail =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hstep := eval_ultStepTerm hx hy hp
          rw [__bv_bitblast_ult_rec.eq_3 previous x xtail y ytail
            (term_ne_stuck_of_eval_boolean hp)]
          have hsimpa := ih hytail hstep htail
          try simp [ultBits] at hsimpa ⊢
          exact hsimpa

private theorem eval_ult_initial {M : SmtModel}
    {x y : Term} {xb yb orEqual : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_ite (Term.Boolean orEqual)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.or)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not) x))
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
                    (Term.Boolean true))))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.or)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
                (Term.Boolean false)))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.UOp UserOp.not) x))
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
                (Term.Boolean true))))) =
      SmtValue.Boolean (ultStep xb yb orEqual) := by
  cases orEqual with
  | false =>
    simp only [__eo_ite, native_teq, native_ite,
     ]
    change
      __smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt x)))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt y))
          (SmtValue.Boolean true)) =
        SmtValue.Boolean (ultStep xb yb false)
    rw [hx, hy]
    cases xb <;> cases yb <;> rfl
  | true =>
    simp only [__eo_ite, native_teq, native_ite]
    change
      __smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval M (__eo_to_smt x)))
          (__smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt y))
            (SmtValue.Boolean true)))
        (__smtx_model_eval_or
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt y)))
          (SmtValue.Boolean false)) =
        SmtValue.Boolean (ultStep xb yb true)
    rw [hx, hy]
    cases xb <;> cases yb <;> rfl

theorem bitblast_ult_eval {M : SmtModel}
    {a b x y xtail ytail : Term} {xb yb orEqual : Bool}
    {xs ys : List Bool}
    (ha :
      BitListEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)
        (xb :: xs))
    (hb :
      BitListEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)
        (yb :: ys))
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_ult
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)
            (Term.Boolean orEqual))) =
      SmtValue.Boolean
        (ultBits (xb :: xs) (yb :: ys) orEqual) := by
  cases ha with
  | cons _ _ _ _ hx hxt =>
      cases hb with
      | cons _ _ _ _ hy hyt =>
          rw [__bv_bitblast_ult.eq_2 _ x xtail y ytail
            (by intro h; cases h)]
          have hinit := eval_ult_initial
            (orEqual := orEqual) hx hy
          simpa [ultBits] using
            bitblast_ult_rec_eval hxt hyt hinit hlen

theorem ultBits_spec :
    ∀ (xs ys : List Bool) (previous : Bool),
      xs.length = ys.length →
      ultBits xs ys previous =
        decide
          (bitsValue xs < bitsValue ys ∨
            (bitsValue xs = bitsValue ys ∧ previous = true)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys previous hlen
      cases ys
      · cases previous <;> decide
      · simp at hlen
  | cons x xs ih =>
      intro ys previous hlen
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hxle : x.toNat ≤ 1 := Bool.toNat_le x
          have hyle : y.toNat ≤ 1 := Bool.toNat_le y
          rw [ultBits, ih ys (ultStep x y previous) htail]
          by_cases hxy : bitsValue xs < bitsValue ys
          · have hall :
                bitsValue (x :: xs) < bitsValue (y :: ys) := by
              simp only [bitsValue]
              omega
            simp [hxy, hall]
          · by_cases hyx : bitsValue ys < bitsValue xs
            · have hnall :
                  ¬ bitsValue (x :: xs) < bitsValue (y :: ys) := by
                simp only [bitsValue]
                omega
              have hne : bitsValue xs ≠ bitsValue ys := by omega
              have hneall :
                  bitsValue (x :: xs) ≠ bitsValue (y :: ys) := by
                simp only [bitsValue]
                omega
              simp [hxy, hne, hnall, hneall]
            · have heq : bitsValue xs = bitsValue ys := by omega
              cases x <;> cases y <;> cases previous <;>
                simp [ultStep, bitsValue, heq]

theorem ultBits_false_lt {xs ys : List Bool}
    (hlen : xs.length = ys.length) :
    ultBits xs ys false = decide (bitsValue xs < bitsValue ys) := by
  rw [ultBits_spec xs ys false hlen]
  simp

theorem ultBits_true_le {xs ys : List Bool}
    (hlen : xs.length = ys.length) :
    ultBits xs ys true = decide (bitsValue xs ≤ bitsValue ys) := by
  rw [ultBits_spec xs ys true hlen]
  by_cases hlt : bitsValue xs < bitsValue ys
  · have hle : bitsValue xs ≤ bitsValue ys := Nat.le_of_lt hlt
    simp [hle]
    exact Or.inl hlt
  · by_cases heq : bitsValue xs = bitsValue ys
    · have hle : bitsValue xs ≤ bitsValue ys := by omega
      simp [heq]
    · have hnle : ¬ bitsValue xs ≤ bitsValue ys := by omega
      simp [hlt, heq, hnle]

theorem bitsValue_append_singleton (xs : List Bool) (s : Bool) :
    bitsValue (xs ++ [s]) =
      bitsValue xs + 2 ^ xs.length * s.toNat := by
  induction xs with
  | nil => cases s <;> rfl
  | cons x xs ih =>
      cases x <;> cases s <;>
        simp [bitsValue, ih, Nat.pow_succ] <;> omega

private theorem msb_ofBoolListLE_append_singleton
    (xs : List Bool) (s : Bool) :
    (BitVec.ofBoolListLE (xs ++ [s])).msb = s := by
  cases s with
  | false =>
      apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
      rw [ofBoolListLE_toNat, bitsValue_append_singleton]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
        List.length_append, List.length_singleton, Nat.pow_succ]
      have h := bitsValue_lt xs
      omega
  | true =>
      apply BitVec.msb_eq_true_iff_two_mul_ge.mpr
      rw [ofBoolListLE_toNat, bitsValue_append_singleton]
      simp only [Bool.toNat_true, Nat.mul_one, List.length_append,
        List.length_singleton, Nat.pow_succ]
      omega

private theorem toInt_ofBoolListLE_append_singleton
    (xs : List Bool) (s : Bool) :
    (BitVec.ofBoolListLE (xs ++ [s])).toInt =
      if s then (bitsValue xs : Int) - (2 ^ xs.length : Nat)
      else (bitsValue xs : Int) := by
  rw [BitVec.toInt_eq_msb_cond,
    msb_ofBoolListLE_append_singleton,
    ofBoolListLE_toNat, bitsValue_append_singleton]
  cases s <;>
    simp [Nat.pow_succ]
  omega

private theorem bitvec_toInt_cast {w v : Nat} (h : w = v)
    (x : BitVec w) :
    (BitVec.cast h x).toInt = x.toInt := by
  rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond,
    BitVec.msb_cast, BitVec.toNat_cast]
  subst v
  rfl

theorem ofBoolListLE_slt_append_singleton
    (xs ys : List Bool) (sx sy : Bool)
    (hlen : xs.length = ys.length) :
    (BitVec.ofBoolListLE (xs ++ [sx])).slt
        (BitVec.cast (by simp [hlen])
          (BitVec.ofBoolListLE (ys ++ [sy]))) =
      (((sx == sy) && decide (bitsValue xs < bitsValue ys)) ||
        (sx && !sy)) := by
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.slt_iff_toInt_lt]
  rw [bitvec_toInt_cast, toInt_ofBoolListLE_append_singleton,
    toInt_ofBoolListLE_append_singleton]
  cases sx <;> cases sy <;> simp
  all_goals
    have hx := bitsValue_lt xs
    have hy := bitsValue_lt ys
    have hp : (2 ^ xs.length : Nat) = 2 ^ ys.length :=
      congrArg (2 ^ ·) hlen
    have hxI : (bitsValue xs : Int) < (2 ^ xs.length : Nat) := by
      exact_mod_cast hx
    have hyI : (bitsValue ys : Int) < (2 ^ ys.length : Nat) := by
      exact_mod_cast hy
    have hpI :
        ((2 ^ xs.length : Nat) : Int) =
          ((2 ^ ys.length : Nat) : Int) := by
      exact_mod_cast hp
    have hpowCastX :
        (2 : Int) ^ xs.length = ((2 ^ xs.length : Nat) : Int) := by
      norm_cast
    have hpowCastY :
        (2 : Int) ^ ys.length = ((2 ^ ys.length : Nat) : Int) := by
      norm_cast
    omega

theorem ofBoolListLE_sle_append_singleton
    (xs ys : List Bool) (sx sy : Bool)
    (hlen : xs.length = ys.length) :
    (BitVec.ofBoolListLE (xs ++ [sx])).sle
        (BitVec.cast (by simp [hlen])
          (BitVec.ofBoolListLE (ys ++ [sy]))) =
      (((sx == sy) && decide (bitsValue xs ≤ bitsValue ys)) ||
        (sx && !sy)) := by
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.sle_iff_toInt_le]
  rw [bitvec_toInt_cast, toInt_ofBoolListLE_append_singleton,
    toInt_ofBoolListLE_append_singleton]
  cases sx <;> cases sy <;> simp
  all_goals
    have hx := bitsValue_lt xs
    have hy := bitsValue_lt ys
    have hp : (2 ^ xs.length : Nat) = 2 ^ ys.length :=
      congrArg (2 ^ ·) hlen
    have hxI : (bitsValue xs : Int) < (2 ^ xs.length : Nat) := by
      exact_mod_cast hx
    have hyI : (bitsValue ys : Int) < (2 ^ ys.length : Nat) := by
      exact_mod_cast hy
    have hpI :
        ((2 ^ xs.length : Nat) : Int) =
          ((2 ^ ys.length : Nat) : Int) := by
      exact_mod_cast hp
    have hpowCastX :
        (2 : Int) ^ xs.length = ((2 ^ xs.length : Nat) : Int) := by
      norm_cast
    have hpowCastY :
        (2 : Int) ^ ys.length = ((2 ^ ys.length : Nat) : Int) := by
      norm_cast
    omega

private theorem native_int_pow2_native_nat (n : Nat) :
    native_int_pow2 (native_nat_to_int n) =
      ((2 ^ n : Nat) : Int) := by
  have hn : ¬ ((n : Int) < 0) := by omega
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, hn]

theorem bvslt_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvslt
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.slt y) := by
  have hW0 : native_zleq 0 (W : Int) = true := by
    simp [SmtEval.native_zleq]
  have hWCast : (W : Int) = native_nat_to_int W := by
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hXCanon : native_zeq (x.toNat : Int)
      (native_mod_total (x.toNat : Int)
        (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_native_nat W]
    have hMod : (x.toNat : Int) % (2 ^ W : Nat) = x.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast x.isLt)
    have hsimpa := hMod.symm
    try simp [SmtEval.native_zeq, SmtEval.native_mod_total] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hYCanon : native_zeq (y.toNat : Int)
      (native_mod_total (y.toNat : Int)
        (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_native_nat W]
    have hMod : (y.toNat : Int) % (2 ^ W : Nat) = y.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast y.isLt)
    have hsimpa := hMod.symm
    try simp [SmtEval.native_zeq, SmtEval.native_mod_total] at hsimpa ⊢
    exact decide_eq_true hsimpa
  unfold __smtx_model_eval_bvslt
  rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts
    hW0 hYCanon hXCanon]
  rw [native_binary_uts_eq_bitvec_toInt W (x.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt),
    native_binary_uts_eq_bitvec_toInt W (y.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast y.isLt)]
  rw [bitvec_ofInt_natCast_toNat, bitvec_ofInt_natCast_toNat]
  rfl

private theorem eval_bvsle_not_bvslt_swap_binary
    (w x y : native_Int) :
    __smtx_model_eval_bvsle
        (SmtValue.Binary w x) (SmtValue.Binary w y) =
      __smtx_model_eval_not
        (__smtx_model_eval_bvslt
          (SmtValue.Binary w y) (SmtValue.Binary w x)) := by
  have hWExpr : w + -1 + 1 + -(w + -1) = 1 := by
    grind
  simp [__smtx_model_eval_bvsle, __smtx_model_eval_bvsge,
    __smtx_model_eval_bvslt, __smtx_model_eval_bvsgt,
    __smtx_model_eval_bvugt, __smtx_model_eval_eq,
    __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_extract,
    __smtx_model_eval__, __smtx_bv_sizeof_value,
    native_binary_extract, native_zlt, native_veq, native_not,
    native_and, native_or, native_zplus, native_zneg, hWExpr]
  generalize hsx :
      decide
        (native_mod_total
          (native_div_total x (native_int_pow2 (w + -1)))
          (native_int_pow2 1) = 1) = sx
  generalize hsy :
      decide
        (native_mod_total
          (native_div_total y (native_int_pow2 (w + -1)))
          (native_int_pow2 1) = 1) = sy
  cases sx <;> cases sy <;>
    by_cases hxy : x < y <;>
    by_cases hyx : y < x <;>
    simp [hxy, hyx, Int.ne_of_lt, Int.ne_of_gt] <;> grind

theorem bvsle_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvsle
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.sle y) := by
  rw [eval_bvsle_not_bvslt_swap_binary, bvslt_bitvec_values]
  change SmtValue.Boolean (!(y.slt x)) =
    SmtValue.Boolean (x.sle y)
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.sle_iff_toInt_le]
  rw [Bool.not_eq_true']
  change y.slt x = false ↔ x.toInt ≤ y.toInt
  simp [BitVec.slt_eq_decide]

theorem bitListEval_cons_shape {M : SmtModel}
    {t : Term} {b : Bool} {bs : List Bool}
    (h : BitListEval M t (b :: bs)) :
    ∃ head tail,
      t =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail ∧
      __smtx_model_eval M (__eo_to_smt head) =
        SmtValue.Boolean b ∧
      BitListEval M tail bs := by
  cases h
  exact ⟨_, _, rfl, ‹_›, ‹_›⟩

private theorem eval_signed_sign_bit {M : SmtModel}
    {x y : Term} {sx sy : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Boolean sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Boolean sy) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.UOp UserOp.not) y))
              (Term.Boolean true)))) =
      SmtValue.Boolean (sx && !sy) := by
  change
    __smtx_model_eval_and
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt y)))
        (SmtValue.Boolean true)) =
      _
  rw [hx, hy]
  cases sx <;> cases sy <;> rfl

private theorem eval_signed_formula {M : SmtModel}
    {x y mag : Term} {sx sy m : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Boolean sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Boolean sy)
    (hm : __smtx_model_eval M (__eo_to_smt mag) =
      SmtValue.Boolean m) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.or)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.and)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.eq) x) y))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.and) mag)
                  (Term.Boolean true))))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.or)
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not) y))
                    (Term.Boolean true))))
              (Term.Boolean false)))) =
      SmtValue.Boolean
        (((sx == sy) && m) || (sx && !sy)) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt mag))
          (SmtValue.Boolean true)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval M (__eo_to_smt y)))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      _
  rw [hx, hy, hm]
  cases sx <;> cases sy <;> cases m <;> rfl

private theorem eval_single_signed_formula {M : SmtModel}
    {x y : Term} {sx sy : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Boolean sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Boolean sy) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.or)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.or)
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not) y))
                    (Term.Boolean true))))
              (Term.Boolean false)))) =
      SmtValue.Boolean ((sx == sy) || (sx && !sy)) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval M (__eo_to_smt y)))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      _
  rw [hx, hy]
  cases sx <;> cases sy <;> rfl

theorem bitblast_slt_impl_eval {M : SmtModel}
    {x xt y yt : Term} {sx sy orEqual : Bool}
    {xs ys : List Bool}
    (ha : BitListEval M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) x) xt)
      (sx :: xs))
    (hb : BitListEval M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) y) yt)
      (sy :: ys))
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) x) xt)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) y) yt)
            (Term.Boolean orEqual))) =
      SmtValue.Boolean
        (((sx == sy) && ultBits xs.reverse ys.reverse orEqual) ||
          (sx && !sy)) := by
  cases ha with
  | cons _ _ _ _ hx hxt =>
    cases hb with
    | cons _ _ _ _ hy hyt =>
      cases hxt with
      | nil =>
        cases hyt with
        | nil =>
          rw [__bv_bitblast_slt_impl.eq_2
            (Term.Boolean orEqual) x y (by intro h; cases h)]
          cases orEqual <;>
            simp only [__eo_ite, native_ite, native_teq,
             ]
          · simpa [ultBits] using eval_signed_sign_bit hx hy
          · simpa [ultBits] using eval_single_signed_formula hx hy
        | cons =>
          simp at hlen
      | cons x2 xt2 sx2 xs2 hx2 hxt2 =>
        cases hyt with
        | nil =>
          simp at hlen
        | cons y2 yt2 sy2 ys2 hy2 hyt2 =>
          have hxtEval :
              BitListEval M
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) x2) xt2)
                (sx2 :: xs2) :=
            BitListEval.cons x2 xt2 sx2 xs2 hx2 hxt2
          have hytEval :
              BitListEval M
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) y2) yt2)
                (sy2 :: ys2) :=
            BitListEval.cons y2 yt2 sy2 ys2 hy2 hyt2
          have hxr := hxtEval.rev
          have hyr := hytEval.rev
          have hxrNe : (sx2 :: xs2).reverse ≠ [] := by simp
          have hyrNe : (sy2 :: ys2).reverse ≠ [] := by simp
          rcases List.exists_cons_of_ne_nil hxrNe with
            ⟨xrb, xrs, hxrList⟩
          rcases List.exists_cons_of_ne_nil hyrNe with
            ⟨yrb, yrs, hyrList⟩
          rw [hxrList] at hxr
          rw [hyrList] at hyr
          rcases bitListEval_cons_shape hxr with
            ⟨xr, xrt, hxrTerm, hxrHead, hxrTail⟩
          rcases bitListEval_cons_shape hyr with
            ⟨yr, yrt, hyrTerm, hyrHead, hyrTail⟩
          have hult :=
            bitblast_ult_eval
              (a := __eo_list_rev
                (Term.UOp UserOp._at_from_bools)
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) x2) xt2))
              (b := __eo_list_rev
                (Term.UOp UserOp._at_from_bools)
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) y2) yt2))
              (orEqual := orEqual)
              (BitListEval.cons xr xrt xrb xrs hxrHead hxrTail)
              (BitListEval.cons yr yrt yrb yrs hyrHead hyrTail)
              (by
                have hrlen :
                    (sx2 :: xs2).reverse.length =
                      (sy2 :: ys2).reverse.length := by
                  simpa using hlen
                simpa [hxrList, hyrList] using hrlen)
          rw [← hxrTerm] at hult
          rw [← hyrTerm] at hult
          rw [← hxrList, ← hyrList] at hult
          have hultNe := term_ne_stuck_of_eval_boolean hult
          rw [__bv_bitblast_slt_impl.eq_3
            (Term.Boolean orEqual) x
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_from_bools) x2) xt2)
              y
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_from_bools) y2) yt2)
            (by intro h; cases h)
            (by intro h; cases h)]
          simp only [__eo_mk_apply]
          exact eval_signed_formula hx hy hult

private def reifyBits (p i : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => p.testBit i :: reifyBits p (i + 1) n

@[simp] private theorem reifyBits_length (p i n : Nat) :
    (reifyBits p i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [reifyBits, ih]

private theorem reifyBits_getD (p i n j : Nat) (hj : j < n) :
    (reifyBits p i n).getD j false = p.testBit (i + j) := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [reifyBits]
    | succ j =>
      simp only [reifyBits, List.getD_cons_succ]
      rw [ih (i := i + 1) (j := j) (by omega)]
      congr 1
      omega

private theorem bitsValue_reifyBits (p W : Nat) (hp : p < 2 ^ W) :
    bitsValue (reifyBits p 0 W) = p := by
  let lhs : BitVec W :=
    BitVec.cast (reifyBits_length p 0 W)
      (BitVec.ofBoolListLE (reifyBits p 0 W))
  let rhs := BitVec.ofNat W p
  have heq : lhs = rhs := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [lhs, rhs, BitVec.getLsbD_cast,
      BitVec.getLsbD_ofBoolListLE, BitVec.getLsbD_ofNat]
    rw [reifyBits_getD p 0 W i hi]
    simp [hi]
  have hnat := congrArg BitVec.toNat heq
  simpa [lhs, rhs, BitVec.toNat_cast, ofBoolListLE_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using hnat

private theorem eval_at_bit
    (M : SmtModel) (a : Term) (W i : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (ha :
      __smtx_model_eval M (__eo_to_smt a) =
        SmtValue.Binary (W : Int) p) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.UOp1 UserOp1._at_bit (Term.Numeral (i : Int))) a)) =
      SmtValue.Boolean ((BitVec.ofInt W p).getLsbD i) := by
  change
    __smtx_model_eval_eq
      (__smtx_model_eval_extract
        (__smtx_model_eval M (SmtTerm.Numeral (i : Int)))
        (__smtx_model_eval M (SmtTerm.Numeral (i : Int)))
        (__smtx_model_eval M (__eo_to_smt a)))
      (SmtValue.Binary 1 1) =
    _
  rw [ha]
  rw [show __smtx_model_eval M (SmtTerm.Numeral (i : Int)) =
      SmtValue.Numeral (i : Int) by
    rw [__smtx_model_eval.eq_def] <;> simp only]
  have hi0 : ¬ ((i : Int) < 0) := by omega
  have hone : (i : Int) + 1 + -(i : Int) = 1 := by omega
  simp [__smtx_model_eval_extract, __smtx_model_eval_eq,
    native_binary_extract, native_int_pow2, native_zexp_total,
    native_div_total, native_mod_total, native_veq,
    native_zplus, native_zneg, BitVec.getLsbD, BitVec.toNat_ofInt,
    hp0, hp1, hi0, hone, Int.emod_eq_of_lt,
    Nat.testBit_eq_decide_div_mod_eq]
  have hpcast : (p.toNat : Int) = p := by omega
  rw [← hpcast]
  norm_cast

theorem eval_step_bvnot (M : SmtModel) (hM : model_wf M)
    (a : Term)
    (hExpanded :
      __bv_bitblast_apply_unary (Term.UOp UserOp.not) a ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) a))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) a)) := by
  have hs := bitblast_apply_unary_syntax _ _ hExpanded
  change
    term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt a)) at hnn
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvnot)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  rcases hs.eval hM haNN with ⟨xs, ha⟩
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval M (__eo_to_smt a))
  exact (eval_bitnot ha).symm

theorem eval_step_bvand (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.and) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvand hb hlen

theorem eval_step_bvor (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.or) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvor)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvor hb hlen

theorem eval_step_bvxor (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxor)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvxor hb hlen

theorem eval_step_bvxnor (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvxnor (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxnor)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)) =
      __smtx_model_eval_bvxnor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvxnor hb hlen

theorem eval_ripple_bvadd (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __pair_second
          (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
            (Term.Binary 0 0)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
              (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b)) := by
  have hRipple := pair_second_arg_ne_stuck hExpanded
  have hs := ripple_carry_same_length _ _ _ _ hRipple
  change
    term_has_non_none_type
      (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvadd)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
              (Term.Binary 0 0)))) =
      __smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact (eval_addBits ha hb hlen).symm

theorem eval_step_bvult (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_ult a b (Term.Boolean false) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_ult a b (Term.Boolean false))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b)) := by
  rcases bitblast_ult_shape a b (Term.Boolean false) hExpanded with
    ⟨x, xtail, y, ytail, rfl, rfl, hs⟩
  change
    term_has_non_none_type
      (SmtTerm.bvult
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail))
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail))) at hnn
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvult) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  have hsFull := BitListsSameLength.cons x xtail y ytail hs
  rcases hsFull.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hsFull.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  cases ha with
  | cons _ _ xb xbs hx hxt =>
      cases hb with
      | cons _ _ yb ybs hy hyt =>
          have htail := hs.eval_length hxt hyt
          have hout := bitblast_ult_eval
            (a := Term.Stuck) (b := Term.Stuck)
            (orEqual := false)
            (BitListEval.cons x xtail xb xbs hx hxt)
            (BitListEval.cons y ytail yb ybs hy hyt) htail
          rw [hout]
          change
            SmtValue.Boolean (ultBits (xb :: xbs) (yb :: ybs) false) =
              __smtx_model_eval_bvult
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) x)
                      xtail)))
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) y)
                      ytail)))
          rw [(BitListEval.cons x xtail xb xbs hx hxt).eval,
            (BitListEval.cons y ytail yb ybs hy hyt).eval]
          rw [ultBits_false_lt (by simpa using htail)]
          simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
            native_zlt]

theorem eval_step_bvule (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_ult a b (Term.Boolean true) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_ult a b (Term.Boolean true))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b)) := by
  rcases bitblast_ult_shape a b (Term.Boolean true) hExpanded with
    ⟨x, xtail, y, ytail, rfl, rfl, hs⟩
  change
    term_has_non_none_type
      (SmtTerm.bvule
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail))
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail))) at hnn
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvule) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  have hsFull := BitListsSameLength.cons x xtail y ytail hs
  rcases hsFull.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hsFull.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  cases ha with
  | cons _ _ xb xbs hx hxt =>
      cases hb with
      | cons _ _ yb ybs hy hyt =>
          have htail := hs.eval_length hxt hyt
          have hout := bitblast_ult_eval
            (a := Term.Stuck) (b := Term.Stuck)
            (orEqual := true)
            (BitListEval.cons x xtail xb xbs hx hxt)
            (BitListEval.cons y ytail yb ybs hy hyt) htail
          rw [hout]
          change
            SmtValue.Boolean (ultBits (xb :: xbs) (yb :: ybs) true) =
              __smtx_model_eval_bvule
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) x)
                      xtail)))
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) y)
                      ytail)))
          rw [(BitListEval.cons x xtail xb xbs hx hxt).eval,
            (BitListEval.cons y ytail yb ybs hy hyt).eval]
          rw [ultBits_true_le (by simpa using htail)]
          simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
            __smtx_model_eval_bvugt, __smtx_model_eval_or,
            __smtx_model_eval_eq, native_zlt, native_veq, native_or]
          by_cases hlt :
              bitsValue (xb :: xbs) < bitsValue (yb :: ybs)
          · have hle :
                bitsValue (xb :: xbs) ≤ bitsValue (yb :: ybs) :=
              Nat.le_of_lt hlt
            simp [hlt, hle]
          · by_cases heq :
                bitsValue (xb :: xbs) = bitsValue (yb :: ybs)
            · simp [heq, htail]
            · have hnle :
                  ¬ bitsValue (xb :: xbs) ≤ bitsValue (yb :: ybs) := by
                omega
              have hneI :
                  ¬ (bitsValue (yb :: ybs) : Int) =
                    (bitsValue (xb :: xbs) : Int) := by
                intro h
                apply heq
                exact_mod_cast h.symm
              simp [hlt, hnle, htail, hneI]

theorem eval_step_eq (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __eo_list_singleton_elim (Term.UOp UserOp.and)
          (__bv_mk_bitblast_step_eq_rec a b) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__bv_mk_bitblast_step_eq_rec a b))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) := by
  have hrec := singleton_elim_arg_ne_stuck hExpanded
  have hs := eq_rec_same_length a b hrec
  change
    __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
        (__smtx_typeof (__eo_to_smt b)) ≠
      SmtType.None at hnn
  simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
    native_Teq] at hnn
  rcases hnn with ⟨haNN, hsame⟩
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [← hsame]
    exact haNN
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  rw [ha.eq_step_eval hb hlen]
  change
    SmtValue.Boolean (bitsEq xs ys) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  rw [ha.eval, hb.eval]
  by_cases hxy : xs = ys
  · subst ys
    rw [(bitsEq_eq_true_iff).2 rfl]
    simp [__smtx_model_eval_eq, native_veq]
  · have hbits : bitsEq xs ys = false := by
      apply Bool.eq_false_iff.mpr
      simpa [bitsEq_eq_true_iff]
    have hval : bitsValue xs ≠ bitsValue ys := by
      intro hv
      exact hxy (bitsValue_inj_of_length hlen hv)
    have hvalI :
        (bitsValue xs : Int) ≠ (bitsValue ys : Int) := by
      exact_mod_cast hval
    rw [hbits]
    simp [__smtx_model_eval_eq, native_veq, hlen, hvalI]

theorem eval_step_bvsub (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __pair_second
          (__bv_ripple_carry_adder_2 a
            (__bv_bitblast_apply_unary (Term.UOp UserOp.not) b)
            (Term.Boolean true) (Term.Binary 0 0)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a
              (__bv_bitblast_apply_unary (Term.UOp UserOp.not) b)
              (Term.Boolean true) (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b)) := by
  have hRipple := pair_second_arg_ne_stuck hExpanded
  have hs := ripple_carry_same_length _ _ _ _ hRipple
  have hnotNe := hs.syntax_right.ne_stuck
  have hbSyntax := bitblast_apply_unary_syntax _ _ hnotNe
  change
    term_has_non_none_type
      (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvsub)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hbSyntax.eval hM hbNN with ⟨ys, hb⟩
  have hbnot := hb.apply_not
  have hlen := hs.eval_length ha hbnot
  have hout :=
    (ripple_carry_eval
      (carry := Term.Boolean true) (cb := true)
      ha hbnot (by rfl) hlen).second
  rw [hout.eval]
  change
    SmtValue.Binary ((addBits xs (ys.map (!·)) true).length : Int)
        (bitsValue (addBits xs (ys.map (!·)) true) : Int) =
      __smtx_model_eval_bvsub
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  rw [ha.eval, hb.eval]
  rw [addBits_length hlen, addBits_value_mod hlen,
    bitsValue_map_not]
  have hlists : xs.length = ys.length := by simpa using hlen
  rw [show ys.length = xs.length by omega]
  simp only [__smtx_model_eval_bvsub, __smtx_model_eval_bvneg,
    __smtx_model_eval_bvadd, native_zneg, native_zplus]
  rw [native_int_pow2_nat]
  simp [native_mod_total]
  have hylt : bitsValue ys < 2 ^ xs.length := by
    simpa [hlists] using bitsValue_lt ys
  have hyle : bitsValue ys ≤ 2 ^ xs.length - 1 := by omega
  have hOne : 1 ≤ 2 ^ xs.length := by
    have := Nat.two_pow_pos xs.length
    omega
  calc
    (↑(bitsValue xs) + ↑(2 ^ xs.length - 1 - bitsValue ys) + 1) %
        (2 ^ xs.length : Int) =
        ((bitsValue xs : Int) - bitsValue ys +
          (2 ^ xs.length : Nat)) % (2 ^ xs.length : Int) := by
            congr 1
            rw [Int.ofNat_sub hyle, Int.ofNat_sub hOne]
            omega
    _ = ((bitsValue xs : Int) - bitsValue ys) %
          (2 ^ xs.length : Int) := by
            rw [Int.add_emod]
            simp
    _ = ((bitsValue xs : Int) + -(bitsValue ys : Int)) %
          (2 ^ xs.length : Int) := by rfl

theorem eval_step_bvneg (M : SmtModel) (hM : model_wf M)
    (a : Term)
    (hExpanded :
      __pair_second
          (__bv_ripple_carry_adder_2
            (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              (Term.Boolean false) (__bv_bitwidth (__eo_typeof a)))
            (Term.Boolean true) (Term.Binary 0 0)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) a))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2
              (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)
              (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
                (Term.Boolean false) (__bv_bitwidth (__eo_typeof a)))
              (Term.Boolean true) (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) a)) := by
  have hRipple := pair_second_arg_ne_stuck hExpanded
  have hs := ripple_carry_same_length _ _ _ _ hRipple
  have hnotNe := hs.syntax_left.ne_stuck
  have haSyntax := bitblast_apply_unary_syntax _ _ hnotNe
  change
    term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt a)) at hnn
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvneg)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
  have haTrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [haTy]
    intro h
    cases h
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a haTrans
  have hEoSmt :
      __eo_to_smt_type (__eo_typeof a) = SmtType.BitVec w := by
    rw [← hMatch, haTy]
  have hEoTy :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hEoSmt
  have hWidth :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (native_nat_to_int w) := by
    rw [hEoTy]
    rfl
  have hzero :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) (__bv_bitwidth (__eo_typeof a)))
        (List.replicate w false) := by
    rw [hWidth]
    simpa [native_nat_to_int] using
      (list_repeat_from_bools (M := M) (bit := Term.Boolean false)
        (b := false) (by rfl) (by intro h; cases h) w)
  have hanot := ha.apply_not
  have hlen := hs.eval_length hanot hzero
  have hout :=
    (ripple_carry_eval
      (carry := Term.Boolean true) (cb := true)
      hanot hzero (by rfl) hlen).second
  rw [hout.eval]
  change
    SmtValue.Binary
        ((addBits (xs.map (!·)) (List.replicate w false) true).length : Int)
        (bitsValue
          (addBits (xs.map (!·)) (List.replicate w false) true) : Int) =
      __smtx_model_eval_bvneg
        (__smtx_model_eval M (__eo_to_smt a))
  rw [ha.eval]
  rw [addBits_length hlen, addBits_value_mod hlen,
    bitsValue_map_not, bitsValue_replicate_false]
  have hlists : xs.length = w := by simpa using hlen
  simp only [List.length_map]
  simp only [__smtx_model_eval_bvneg, native_zneg]
  rw [native_int_pow2_nat]
  simp [native_mod_total]
  have hxlt := bitsValue_lt xs
  have hxle : bitsValue xs ≤ 2 ^ xs.length - 1 := by omega
  have hOne : 1 ≤ 2 ^ xs.length := by
    have := Nat.two_pow_pos xs.length
    omega
  calc
    (↑(2 ^ xs.length - 1 - bitsValue xs) + 0 + 1) %
        (2 ^ xs.length : Int) =
        ((-(bitsValue xs : Int)) +
          (2 ^ xs.length : Nat)) % (2 ^ xs.length : Int) := by
            congr 1
            rw [Int.ofNat_sub hxle, Int.ofNat_sub hOne]
            omega
    _ = (-(bitsValue xs : Int)) %
          (2 ^ xs.length : Int) := by
            rw [Int.add_emod]
            simp

theorem eval_step_bvite (M : SmtModel) (hM : model_wf M)
    (c a b : Term)
    (hExpanded : __bv_mk_bitblast_step_ite c a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_ite c a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) a) b)) := by
  rcases bitblast_step_ite_shape c a b hExpanded with ⟨cbit, rfl, hs⟩
  change
    term_has_non_none_type
      (SmtTerm.ite
        (SmtTerm.eq
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
              (Term.Binary 0 0)))
          (SmtTerm.Binary 1 1))
        (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases ite_args_of_non_none hnn with
    ⟨T, hcTy, haTy, hbTy, hT⟩
  change
    __smtx_typeof_eq
        (__smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
              (Term.Binary 0 0))))
        (SmtType.BitVec 1) =
      SmtType.Bool at hcTy
  rcases (RuleProofs.smtx_typeof_eq_bool_iff _ _).mp hcTy with
    ⟨hcSame, hcNN⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    exact hT
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    exact hT
  have hcSyntax :
      BitListSyntax
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
          (Term.Binary 0 0)) :=
    BitListSyntax.cons cbit (Term.Binary 0 0) BitListSyntax.nil
  rcases hcSyntax.eval hM hcNN with ⟨cs, hc⟩
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  cases hc with
  | cons _ _ cb cbs hcbit hctail =>
      cases hctail with
      | nil =>
          have hlen := hs.eval_length ha hb
          have hout := bitblast_step_ite_eval hcbit ha hb hlen
          rw [hout.eval]
          change
            SmtValue.Binary
                ((List.zipWith
                  (fun x y => if cb then x else y) xs ys).length : Int)
                (bitsValue
                  (List.zipWith
                    (fun x y => if cb then x else y) xs ys) : Int) =
              __smtx_model_eval_ite
                (__smtx_model_eval_eq
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply
                          (Term.UOp UserOp._at_from_bools) cbit)
                        (Term.Binary 0 0))))
                  (SmtValue.Binary 1 1))
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b))
          rw [(BitListEval.cons cbit (Term.Binary 0 0) cb [] hcbit
            (BitListEval.nil (M := M))).eval, ha.eval, hb.eval]
          cases cb
          · simp only [Bool.false_eq_true, if_false]
            rw [zipWith_right_of_length xs ys hlen]
            rfl
          · simp only [if_true]
            rw [zipWith_left_of_length xs ys hlen]
            rfl

theorem eval_step_bvcomp (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
            (__eo_list_singleton_elim (Term.UOp UserOp.and)
              (__bv_mk_bitblast_step_eq_rec a b)))
          (Term.Binary 0 0) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
              (__eo_list_singleton_elim (Term.UOp UserOp.and)
                (__bv_mk_bitblast_step_eq_rec a b)))
            (Term.Binary 0 0))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) a) b)) := by
  let c :=
    __eo_list_singleton_elim (Term.UOp UserOp.and)
      (__bv_mk_bitblast_step_eq_rec a b)
  have hinner :
      __eo_mk_apply (Term.UOp UserOp._at_from_bools) c ≠ Term.Stuck :=
    mk_apply_fun_ne_stuck hExpanded
  have hcNe : c ≠ Term.Stuck :=
    mk_apply_arg_ne_stuck hinner
  change
    term_has_non_none_type
      (SmtTerm.bvcomp (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have heqNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) := by
    change
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
          (__smtx_typeof (__eo_to_smt b)) ≠
        SmtType.None
    rw [haTy, hbTy]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  have hcEq := eval_step_eq M hM a b hcNe heqNN
  change
    __smtx_model_eval M (__eo_to_smt c) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) at hcEq
  rcases eval_eq_is_boolean
      (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) with ⟨cb, heq⟩
  have hc : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Boolean cb := hcEq.trans heq
  rw [wrap_bool_eval hc]
  change
    SmtValue.Binary 1 (if cb then 1 else 0) =
      __smtx_model_eval_bvcomp
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  unfold __smtx_model_eval_bvcomp
  rw [heq]
  cases cb <;> rfl

private theorem eval_step_bvslt_or_le_aux
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (orEqual : Bool) (w : Nat)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean orEqual) ≠ Term.Stuck)
    (haTy :
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w)
    (hbTy :
      __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean orEqual))) =
      if orEqual then
        __smtx_model_eval_bvsle
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b))
      else
        __smtx_model_eval_bvslt
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)) := by
  have hargs := bitblast_slt_args_ne_stuck _ _ _ hExpanded
  have hsa := bitlist_rev_syntax a hargs.1
  have hsb := bitlist_rev_syntax b hargs.2
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hsa.eval hM haNN with ⟨as, ha⟩
  rcases hsb.eval hM hbNN with ⟨bs, hb⟩
  have hpresA := type_preservation M hM (__eo_to_smt a) haNN
  have hpresB := type_preservation M hM (__eo_to_smt b) hbNN
  rw [haTy, ha.eval] at hpresA
  rw [hbTy, hb.eval] at hpresB
  have hlen : as.length = bs.length := by
    have hwa := bitvec_width_nonneg hpresA
    have hca := bitvec_payload_canonical hpresA
    have hwb := bitvec_width_nonneg hpresB
    have hcb := bitvec_payload_canonical hpresB
    rw [typeof_value_binary_of_nonneg _ _ hwa hca] at hpresA
    rw [typeof_value_binary_of_nonneg _ _ hwb hcb] at hpresB
    injection hpresA with hla
    injection hpresB with hlb
    have hsimpa := hla.trans hlb.symm
    try simp at hsimpa ⊢
    exact hsimpa
  have hasNe : as ≠ [] := by
    intro has
    subst as
    cases ha
    have hrev :
        __eo_list_rev (Term.UOp UserOp._at_from_bools)
            (Term.Binary 0 0) =
          Term.Binary 0 0 := by native_decide
    rw [hrev] at hExpanded
    simp [__bv_bitblast_slt_impl] at hExpanded
  have hbsNe : bs ≠ [] := by
    intro hbs
    subst bs
    cases hb
    have hrev :
        __eo_list_rev (Term.UOp UserOp._at_from_bools)
            (Term.Binary 0 0) =
          Term.Binary 0 0 := by native_decide
    rw [hrev] at hExpanded
    simp [__bv_bitblast_slt_impl] at hExpanded
  have har := ha.rev
  have hbr := hb.rev
  rcases List.exists_cons_of_ne_nil
      (show as.reverse ≠ [] by simpa using hasNe) with
    ⟨sa, ars, harList⟩
  rcases List.exists_cons_of_ne_nil
      (show bs.reverse ≠ [] by simpa using hbsNe) with
    ⟨sb, brs, hbrList⟩
  rw [harList] at har
  rw [hbrList] at hbr
  rcases bitListEval_cons_shape har with
    ⟨atop, atail, harTerm, hatop, hatail⟩
  rcases bitListEval_cons_shape hbr with
    ⟨btop, btail, hbrTerm, hbtop, hbtail⟩
  have htailLen : ars.length = brs.length := by
    have hrlen : as.reverse.length = bs.reverse.length := by
      simpa using hlen
    simpa [harList, hbrList] using hrlen
  have hcircuit :=
    bitblast_slt_impl_eval
      (orEqual := orEqual)
      (BitListEval.cons atop atail sa ars hatop hatail)
      (BitListEval.cons btop btail sb brs hbtop hbtail)
      htailLen
  rw [← harTerm, ← hbrTerm] at hcircuit
  rw [hcircuit]
  change
    SmtValue.Boolean
        (sa == sb &&
            ultBits ars.reverse brs.reverse orEqual ||
          sa && !sb) =
      _
  rw [ha.eval, hb.eval]
  have haDecomp : as = ars.reverse ++ [sa] := by
    have h := congrArg List.reverse harList
    simpa using h
  have hbDecomp : bs = brs.reverse ++ [sb] := by
    have h := congrArg List.reverse hbrList
    simpa using h
  subst as
  subst bs
  simp only [List.length_append, List.length_reverse,
    List.length_singleton]
  rw [← htailLen]
  let xv := BitVec.ofBoolListLE (ars.reverse ++ [sa])
  let yv : BitVec (ars.reverse ++ [sa]).length :=
    BitVec.cast (by simp [htailLen])
      (BitVec.ofBoolListLE (brs.reverse ++ [sb]))
  have hxnat : xv.toNat =
      bitsValue (ars.reverse ++ [sa]) := by
    simp [xv, ofBoolListLE_toNat]
  have hynat : yv.toNat =
      bitsValue (brs.reverse ++ [sb]) := by
    simp [yv, BitVec.toNat_cast, ofBoolListLE_toNat]
  rw [← hxnat, ← hynat]
  cases orEqual with
  | false =>
    rw [ultBits_false_lt (by simpa using htailLen)]
    have hev :
        __smtx_model_eval_bvslt
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (xv.toNat : Int))
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (yv.toNat : Int)) =
          SmtValue.Boolean (xv.slt yv) := by
      simpa only [List.length_append, List.length_reverse,
        List.length_singleton] using bvslt_bitvec_values xv yv
    rw [hev]
    congr 1
    exact (ofBoolListLE_slt_append_singleton
      ars.reverse brs.reverse sa sb
      (by simpa using htailLen)).symm
  | true =>
    rw [ultBits_true_le (by simpa using htailLen)]
    have hev :
        __smtx_model_eval_bvsle
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (xv.toNat : Int))
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (yv.toNat : Int)) =
          SmtValue.Boolean (xv.sle yv) := by
      simpa only [List.length_append, List.length_reverse,
        List.length_singleton] using bvsle_bitvec_values xv yv
    rw [hev]
    congr 1
    exact (ofBoolListLE_sle_append_singleton
      ars.reverse brs.reverse sa sb
      (by simpa using htailLen)).symm

theorem eval_step_bvslt_or_le
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (orEqual : Bool)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean orEqual) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.UOp
                (if orEqual then UserOp.bvsle else UserOp.bvslt)) a)
            b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean orEqual))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.UOp
                (if orEqual then UserOp.bvsle else UserOp.bvslt)) a)
            b)) := by
  cases orEqual with
  | false =>
    change
      term_has_non_none_type
        (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) at hnn
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvslt) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
      ⟨w, haTy, hbTy⟩
    exact eval_step_bvslt_or_le_aux
      M hM a b false w hExpanded haTy hbTy
  | true =>
    change
      term_has_non_none_type
        (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)) at hnn
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvsle) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
      ⟨w, haTy, hbTy⟩
    exact eval_step_bvslt_or_le_aux
      M hM a b true w hExpanded haTy hbTy

theorem eval_step_bvslt (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean false) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean false))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b)) :=
  eval_step_bvslt_or_le M hM a b false hExpanded hnn

theorem eval_step_bvsle (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean true) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean true))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b)) :=
  eval_step_bvslt_or_le M hM a b true hExpanded hnn

theorem eval_step_bvultbv (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
            (__bv_bitblast_ult a b (Term.Boolean false)))
          (Term.Binary 0 0) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
              (__bv_bitblast_ult a b (Term.Boolean false)))
            (Term.Binary 0 0))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) a) b)) := by
  let c := __bv_bitblast_ult a b (Term.Boolean false)
  have hinner :
      __eo_mk_apply (Term.UOp UserOp._at_from_bools) c ≠ Term.Stuck :=
    mk_apply_fun_ne_stuck hExpanded
  have hcNe : c ≠ Term.Stuck :=
    mk_apply_arg_ne_stuck hinner
  change
    term_has_non_none_type
      (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) at hnn
  rcases ite_args_of_non_none hnn with
    ⟨T, hcTy, hthenTy, helseTy, hT⟩
  have hultNN :
      term_has_non_none_type
        (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hcTy]
    simp
  have hcEq := eval_step_bvult M hM a b hcNe hultNN
  change
    __smtx_model_eval M (__eo_to_smt c) =
      __smtx_model_eval_bvult
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) at hcEq
  rcases smt_model_eval_bool_is_boolean M hM
      (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) hcTy with
    ⟨cb, hpred⟩
  change
    __smtx_model_eval_bvult
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean cb at hpred
  have hc : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Boolean cb := hcEq.trans hpred
  rw [wrap_bool_eval hc]
  change
    SmtValue.Binary 1 (if cb then 1 else 0) =
      __smtx_model_eval_ite
        (__smtx_model_eval_bvult
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)))
        (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)
  rw [hpred]
  cases cb <;> rfl

theorem eval_step_bvsltbv (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hExpanded :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
            (__bv_bitblast_slt_impl
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
              (Term.Boolean false)))
          (Term.Binary 0 0) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
              (__bv_bitblast_slt_impl
                (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
                (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
                (Term.Boolean false)))
            (Term.Binary 0 0))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) a) b)) := by
  let c :=
    __bv_bitblast_slt_impl
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
      (Term.Boolean false)
  have hinner :
      __eo_mk_apply (Term.UOp UserOp._at_from_bools) c ≠ Term.Stuck :=
    mk_apply_fun_ne_stuck hExpanded
  have hcNe : c ≠ Term.Stuck :=
    mk_apply_arg_ne_stuck hinner
  change
    term_has_non_none_type
      (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) at hnn
  rcases ite_args_of_non_none hnn with
    ⟨T, hcTy, hthenTy, helseTy, hT⟩
  have hsltNN :
      term_has_non_none_type
        (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hcTy]
    simp
  have hcEq := eval_step_bvslt M hM a b hcNe hsltNN
  change
    __smtx_model_eval M (__eo_to_smt c) =
      __smtx_model_eval_bvslt
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) at hcEq
  rcases smt_model_eval_bool_is_boolean M hM
      (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) hcTy with
    ⟨cb, hpred⟩
  change
    __smtx_model_eval_bvslt
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean cb at hpred
  have hc : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Boolean cb := hcEq.trans hpred
  rw [wrap_bool_eval hc]
  change
    SmtValue.Binary 1 (if cb then 1 else 0) =
      __smtx_model_eval_ite
        (__smtx_model_eval_bvslt
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)))
        (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)
  rw [hpred]
  cases cb <;> rfl





private theorem fold_acc_ne {bf f rest acc : Term}
    (h : __bv_mk_bitblast_step_bitwise bf f rest acc ≠ Term.Stuck) :
    acc ≠ Term.Stuck := by
  intro ha
  subst acc
  by_cases hbf : bf = Term.Stuck
  · subst bf
    rw [__bv_mk_bitblast_step_bitwise.eq_1] at h
    exact h rfl
  by_cases hf : f = Term.Stuck
  · subst f
    rw [__bv_mk_bitblast_step_bitwise.eq_2 bf rest Term.Stuck hbf] at h
    exact h rfl
  by_cases hr : rest = Term.Stuck
  · subst rest
    rw [__bv_mk_bitblast_step_bitwise.eq_3 bf f Term.Stuck hbf hf] at h
    exact h rfl
  rw [__bv_mk_bitblast_step_bitwise.eq_4 bf f rest hbf hf hr] at h
  exact h rfl

private theorem req_refl (t result : Term) (ht : t ≠ Term.Stuck) :
    __eo_requires t t result = result := by
  simp [__eo_requires, native_teq, native_ite, native_not, ht]

private theorem smt_typeof_bitsValue (xs : List Bool) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Binary (xs.length : Int)
            (BvBitblast.bitsValue xs : Int))) =
      SmtType.BitVec xs.length := by
  have hW0 : native_zleq 0 (xs.length : Int) = true := by
    simp [SmtEval.native_zleq]
  have hCanon :
      native_zeq (BvBitblast.bitsValue xs : Int)
          (native_mod_total (BvBitblast.bitsValue xs : Int)
            (native_int_pow2 (xs.length : Int))) =
        true := by
    have hWCast :
        (xs.length : Int) = native_nat_to_int xs.length := by
      simp [native_nat_to_int, Smtm.native_nat_to_int]
    rw [hWCast]
    rw [BvBitblast.native_int_pow2_native_nat xs.length]
    have hMod :
        (BvBitblast.bitsValue xs : Int) % (2 ^ xs.length : Nat) =
          BvBitblast.bitsValue xs := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast BvBitblast.bitsValue_lt xs)
    have hsimpa := hMod.symm
    try simp [SmtEval.native_zeq, SmtEval.native_mod_total] at hsimpa ⊢
    exact decide_eq_true hsimpa
  change
    __smtx_typeof
        (SmtTerm.Binary (xs.length : Int)
          (BvBitblast.bitsValue xs : Int)) =
      SmtType.BitVec xs.length
  simp [__smtx_typeof, native_and, hW0, hCanon, native_ite,
    native_int_to_nat]

private theorem bitListEval_length_eq_smt_type
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (xs : List Bool) (W : Nat)
    (h : BvBitblast.BitListEval M t xs)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec W) :
    xs.length = W := by
  have hnn : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hpres := type_preservation M hM (__eo_to_smt t) hnn
  rw [hTy, h.eval] at hpres
  have hw := bitvec_width_nonneg hpres
  have hc := bitvec_payload_canonical hpres
  rw [typeof_value_binary_of_nonneg _ _ hw hc] at hpres
  injection hpres

private theorem band_assoc_values
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (W : Nat) (xs ys : List Bool)
    (hx : BvBitblast.BitListEval M x xs)
    (hy : BvBitblast.BitListEval M y ys)
    (hxW : xs.length = W) (hyW : ys.length = W)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y)) z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) y) z))) := by
  let xc := Term.Binary (W : Int) (BvBitblast.bitsValue xs : Int)
  let yc := Term.Binary (W : Int) (BvBitblast.bitsValue ys : Int)
  have hxcTy : __smtx_typeof (__eo_to_smt xc) = SmtType.BitVec W := by
    simpa [xc, hxW] using smt_typeof_bitsValue xs
  have hycTy : __smtx_typeof (__eo_to_smt yc) = SmtType.BitVec W := by
    simpa [yc, hyW] using smt_typeof_bitsValue ys
  have hassoc :=
    BvNaryAndSupport.evalAssoc M hM xc yc z W hxcTy hycTy hzTy
  change
    __smtx_model_eval_bvand
        (__smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval M (__eo_to_smt z)) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt z)))
  rw [hx.eval, hy.eval, hxW, hyW]
  have hsimpa := hassoc
  try simp [xc, yc] at hsimpa ⊢
  exact hsimpa

private theorem testBitsBand
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term) (W : Nat) (xs : List Bool)
    (hacc : BvBitblast.BitListEval M acc xs)
    (hxW : xs.length = W)
    (hrestTy : __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W)
    (hne :
      __bv_mk_bitblast_step_bitwise
          (Term.UOp UserOp.bvand) (Term.UOp UserOp.and) rest acc ≠
        Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_mk_bitblast_step_bitwise
            (Term.UOp UserOp.bvand) (Term.UOp UserOp.and) rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) acc) rest)) := by
  generalize hbf : Term.UOp UserOp.bvand = bf at hne ⊢
  generalize hf : Term.UOp UserOp.and = f at hne ⊢
  revert hacc hxW hrestTy hne hbf hf
  fun_cases __bv_mk_bitblast_step_bitwise bf f rest acc <;>
    subst_vars <;> simp_all
  case case5 head tail hbfNe hfNe haccNe =>
    intro hacc hxW hrestTy hbf hf hne
    subst_vars
    rename_i g
    by_cases hg : g = Term.UOp UserOp.bvand
    · subst g
      simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne ⊢
      have hnewNe := fold_acc_ne hne
      have hs :=
        BvBitblast.bitblast_apply_binary_same_length
          (Term.UOp UserOp.and) acc head hnewNe
      have hparts :=
        BvNaryAndSupport.binaryArgsSmtType head tail xs.length hrestTy
      have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hparts.1]
        simp
      rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
      have hlen := hs.eval_length hacc hhead
      have hnew := hacc.apply_and hhead hlen
      have hnewLen :
          (List.zipWith (· && ·) xs ys).length = xs.length := by
        simp [List.length_zipWith, hlen]
      have hrec :=
        testBitsBand M hM tail
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) acc head)
          xs.length (List.zipWith (· && ·) xs ys)
          hnew hnewLen hparts.2 hne
      have hnewEval := hacc.eval_bvand hhead hlen
      calc
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_mk_bitblast_step_bitwise
                (Term.UOp UserOp.bvand) (Term.UOp UserOp.and) tail
                (__bv_bitblast_apply_binary
                  (Term.UOp UserOp.and) acc head))) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvand)
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.and) acc head)) tail)) := hrec
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvand)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.bvand) acc) head))
                  tail)) := by
            change __smtx_model_eval_bvand
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.and) acc head)))
                (__smtx_model_eval M (__eo_to_smt tail)) =
              __smtx_model_eval_bvand
                (__smtx_model_eval_bvand
                  (__smtx_model_eval M (__eo_to_smt acc))
                  (__smtx_model_eval M (__eo_to_smt head)))
                (__smtx_model_eval M (__eo_to_smt tail))
            rw [hnewEval]
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) acc)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.bvand) head) tail))) :=
            band_assoc_values M hM acc head tail xs.length xs ys
              hacc hhead rfl hlen.symm hparts.2
    · by_cases hgStuck : g = Term.Stuck
      · subst g
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne
      have heqFalse :
          __eo_eq (Term.UOp UserOp.bvand) g = Term.Boolean false := by
        cases g <;> simp_all [__eo_eq, native_teq]
      have hfallback :
          __eo_l_1___bv_mk_bitblast_step_bitwise
              (Term.UOp UserOp.bvand) (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply g head) tail) acc ≠
            Term.Stuck := by
        simpa [heqFalse, __eo_ite, native_teq, native_ite] using hne
      have haccNe := hacc.ne_stuck
      simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hfallback
      have hsame :=
        support_eo_requires_cond_eq_of_non_stuck hfallback
      have hrestEoTy :=
        EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
          (Term.Apply (Term.Apply g head) tail) xs.length hrestTy
      rw [hrestEoTy] at hsame
      have hnilNe :
          __eo_nil
              (Term.UOp UserOp.bvand)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int xs.length))) ≠
            Term.Stuck := by
        intro hs
        rw [hs] at hsame
        cases hsame
      have hnilEq :=
        bvand_generated_nil_eq_allOnes xs.length hnilNe
      rw [hnilEq] at hsame
      cases hsame
  case case6 hnotApp haccNe =>
    intro hacc hxW hrestTy hbf hf hne
    subst_vars
    simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hne ⊢
    have hnil := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires rest
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof rest)) acc =
          acc := by
      rw [← hnil]
      exact req_refl _ _ (by assumption)
    rw [hreq]
    let xc :=
      Term.Binary (xs.length : Int) (BvBitblast.bitsValue xs : Int)
    have hxcTy :
        __smtx_typeof (__eo_to_smt xc) =
          SmtType.BitVec xs.length := by
      exact smt_typeof_bitsValue xs
    have hrestEoTy :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
        rest xs.length hrestTy
    have hrestEq :
        rest =
          __eo_nil (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int xs.length))) := by
      simpa [hrestEoTy] using hnil
    have hnilNe :
        __eo_nil (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int xs.length))) ≠
          Term.Stuck := by
      have hrestNe : rest ≠ Term.Stuck := by
        intro hs
        rw [hs] at hrestTy
        change __smtx_typeof SmtTerm.None = SmtType.BitVec xs.length at hrestTy
        rw [TranslationProofs.smtx_typeof_none] at hrestTy
        cases hrestTy
      rw [← hrestEq]
      exact hrestNe
    have hmarker :=
      bvand_generated_nil_marker xs.length hnilNe
    have hid :=
      BvNaryAndSupport.evalRightNil M hM xc rest xs.length
        (by simpa [hrestEq] using hmarker)
        hxcTy hrestTy
    change
      __smtx_model_eval M (__eo_to_smt acc) =
        __smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt acc))
          (__smtx_model_eval M (__eo_to_smt rest))
    rw [hacc.eval]
    have hsimpa := hid.symm
    try simp [xc] at hsimpa ⊢
    exact hsimpa
termination_by sizeOf rest

theorem eval_step_bvand_fold
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term)
    (hne :
      __bv_mk_bitblast_step_bitwise
          (Term.UOp UserOp.bvand) (Term.UOp UserOp.and) rest acc ≠
        Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) acc) rest))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_mk_bitblast_step_bitwise
            (Term.UOp UserOp.bvand) (Term.UOp UserOp.and) rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) acc) rest)) := by
  change term_has_non_none_type
      (SmtTerm.bvand (__eo_to_smt acc) (__eo_to_smt rest)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand)
      (t1 := __eo_to_smt acc) (t2 := __eo_to_smt rest)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haccTy, hrestTy⟩
  have hargs :
      __smtx_typeof (__eo_to_smt acc) = SmtType.BitVec W ∧
        __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W :=
    ⟨haccTy, hrestTy⟩
  generalize hbf : Term.UOp UserOp.bvand = bf at hne ⊢
  generalize hf : Term.UOp UserOp.and = f at hne ⊢
  revert hne hbf hf
  fun_cases __bv_mk_bitblast_step_bitwise bf f rest acc <;>
    subst_vars <;> simp_all
  case case5 head tail hbfNe hfNe haccNe =>
    intro hbf hf hne
    subst_vars
    rename_i g
    by_cases hg : g = Term.UOp UserOp.bvand
    · subst g
      simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne ⊢
      have hnewNe := fold_acc_ne hne
      have hs :=
        BvBitblast.bitblast_apply_binary_same_length
          (Term.UOp UserOp.and) acc head hnewNe
      have hparts :=
        BvNaryAndSupport.binaryArgsSmtType head tail W hargs.2
      have haccNN : term_has_non_none_type (__eo_to_smt acc) := by
        unfold term_has_non_none_type
        rw [hargs.1]
        simp
      have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hparts.1]
        simp
      rcases hs.syntax_left.eval hM haccNN with ⟨xs, hacc⟩
      rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
      have hlen := hs.eval_length hacc hhead
      have hnew := hacc.apply_and hhead hlen
      have hnewLen :
          (List.zipWith (· && ·) xs ys).length = xs.length := by
        simp [List.length_zipWith, hlen]
      have hxW :=
        bitListEval_length_eq_smt_type M hM acc xs W hacc hargs.1
      have hrec :=
        testBitsBand M hM tail
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) acc head)
          xs.length (List.zipWith (· && ·) xs ys)
          hnew hnewLen (by simpa [hxW] using hparts.2) hne
      have hnewEval := hacc.eval_bvand hhead hlen
      calc
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_mk_bitblast_step_bitwise
                (Term.UOp UserOp.bvand) (Term.UOp UserOp.and) tail
                (__bv_bitblast_apply_binary
                  (Term.UOp UserOp.and) acc head))) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvand)
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.and) acc head)) tail)) := hrec
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvand)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.bvand) acc) head))
                  tail)) := by
            change __smtx_model_eval_bvand
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.and) acc head)))
                (__smtx_model_eval M (__eo_to_smt tail)) =
              __smtx_model_eval_bvand
                (__smtx_model_eval_bvand
                  (__smtx_model_eval M (__eo_to_smt acc))
                  (__smtx_model_eval M (__eo_to_smt head)))
                (__smtx_model_eval M (__eo_to_smt tail))
            rw [hnewEval]
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) acc)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.bvand) head) tail))) :=
            BvNaryAndSupport.evalAssoc M hM acc head tail W
              hargs.1 hparts.1 hparts.2
    · by_cases hgStuck : g = Term.Stuck
      · subst g
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne
      have heqFalse :
          __eo_eq (Term.UOp UserOp.bvand) g = Term.Boolean false := by
        cases g <;> simp_all [__eo_eq, native_teq]
      have hfallback :
          __eo_l_1___bv_mk_bitblast_step_bitwise
              (Term.UOp UserOp.bvand) (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply g head) tail) acc ≠
            Term.Stuck := by
        simpa [heqFalse, __eo_ite, native_teq, native_ite] using hne
      simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hfallback
      have hsame :=
        support_eo_requires_cond_eq_of_non_stuck hfallback
      have hrestEoTy :=
        EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
          (Term.Apply (Term.Apply g head) tail) W hargs.2
      rw [hrestEoTy] at hsame
      have hnilNe :
          __eo_nil
              (Term.UOp UserOp.bvand)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int W))) ≠
            Term.Stuck := by
        intro hs
        rw [hs] at hsame
        cases hsame
      have hnilEq :=
        bvand_generated_nil_eq_allOnes W hnilNe
      rw [hnilEq] at hsame
      cases hsame
  case case6 hnotApp haccNe =>
    intro hbf hf hne
    subst_vars
    simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hne ⊢
    have hnil := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires rest
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof rest)) acc =
          acc := by
      rw [← hnil]
      exact req_refl _ _ (by assumption)
    rw [hreq]
    have hrestEoTy :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
        rest W hargs.2
    have hrestEq :
        rest =
          __eo_nil (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int W))) := by
      simpa [hrestEoTy] using hnil
    have hrestNe : rest ≠ Term.Stuck := by
      intro hs
      have h := hargs.2
      rw [hs] at h
      change __smtx_typeof SmtTerm.None = SmtType.BitVec W at h
      rw [TranslationProofs.smtx_typeof_none] at h
      cases h
    have hnilNe :
        __eo_nil (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int W))) ≠
          Term.Stuck := by
      rw [← hrestEq]
      exact hrestNe
    have hmarker :=
      bvand_generated_nil_marker W hnilNe
    exact (BvNaryAndSupport.evalRightNil M hM acc rest W
      (by simpa [hrestEq] using hmarker) hargs.1 hargs.2).symm

private theorem bor_assoc_values
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (W : Nat) (xs ys : List Bool)
    (hx : BvBitblast.BitListEval M x xs)
    (hy : BvBitblast.BitListEval M y ys)
    (hxW : xs.length = W) (hyW : ys.length = W)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y)) z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) y) z))) := by
  let xc := Term.Binary (W : Int) (BvBitblast.bitsValue xs : Int)
  let yc := Term.Binary (W : Int) (BvBitblast.bitsValue ys : Int)
  have hxcTy : __smtx_typeof (__eo_to_smt xc) = SmtType.BitVec W := by
    simpa [xc, hxW] using smt_typeof_bitsValue xs
  have hycTy : __smtx_typeof (__eo_to_smt yc) = SmtType.BitVec W := by
    simpa [yc, hyW] using smt_typeof_bitsValue ys
  have hassoc :=
    BvNaryOrSupport.evalAssoc M hM xc yc z W hxcTy hycTy hzTy
  change
    __smtx_model_eval_bvor
        (__smtx_model_eval_bvor
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval M (__eo_to_smt z)) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_bvor
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt z)))
  rw [hx.eval, hy.eval, hxW, hyW]
  have hsimpa := hassoc
  try simp [xc, yc] at hsimpa ⊢
  exact hsimpa

private theorem testBitsOr
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term) (W : Nat) (xs : List Bool)
    (hacc : BvBitblast.BitListEval M acc xs)
    (hxW : xs.length = W)
    (hrestTy : __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W)
    (hne :
      __bv_mk_bitblast_step_bitwise
          (Term.UOp UserOp.bvor) (Term.UOp UserOp.or) rest acc ≠
        Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_mk_bitblast_step_bitwise
            (Term.UOp UserOp.bvor) (Term.UOp UserOp.or) rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) acc) rest)) := by
  generalize hbf : Term.UOp UserOp.bvor = bf at hne ⊢
  generalize hf : Term.UOp UserOp.or = f at hne ⊢
  revert hacc hxW hrestTy hne hbf hf
  fun_cases __bv_mk_bitblast_step_bitwise bf f rest acc <;>
    subst_vars <;> simp_all
  case case5 head tail hbfNe hfNe haccNe =>
    intro hacc hxW hrestTy hbf hf hne
    subst_vars
    rename_i g
    by_cases hg : g = Term.UOp UserOp.bvor
    · subst g
      simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne ⊢
      have hnewNe := fold_acc_ne hne
      have hs :=
        BvBitblast.bitblast_apply_binary_same_length
          (Term.UOp UserOp.or) acc head hnewNe
      have hparts :=
        BvNaryOrSupport.binaryArgsSmtType head tail xs.length hrestTy
      have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hparts.1]
        simp
      rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
      have hlen := hs.eval_length hacc hhead
      have hnew := hacc.apply_or hhead hlen
      have hnewLen :
          (List.zipWith (· || ·) xs ys).length = xs.length := by
        simp [List.length_zipWith, hlen]
      have hrec :=
        testBitsOr M hM tail
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) acc head)
          xs.length (List.zipWith (· || ·) xs ys)
          hnew hnewLen hparts.2 hne
      have hnewEval := hacc.eval_bvor hhead hlen
      calc
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_mk_bitblast_step_bitwise
                (Term.UOp UserOp.bvor) (Term.UOp UserOp.or) tail
                (__bv_bitblast_apply_binary
                  (Term.UOp UserOp.or) acc head))) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvor)
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.or) acc head)) tail)) := hrec
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvor)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.bvor) acc) head))
                  tail)) := by
            change __smtx_model_eval_bvor
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.or) acc head)))
                (__smtx_model_eval M (__eo_to_smt tail)) =
              __smtx_model_eval_bvor
                (__smtx_model_eval_bvor
                  (__smtx_model_eval M (__eo_to_smt acc))
                  (__smtx_model_eval M (__eo_to_smt head)))
                (__smtx_model_eval M (__eo_to_smt tail))
            rw [hnewEval]
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) acc)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.bvor) head) tail))) :=
            bor_assoc_values M hM acc head tail xs.length xs ys
              hacc hhead rfl hlen.symm hparts.2
    · by_cases hgStuck : g = Term.Stuck
      · subst g
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne
      have heqFalse :
          __eo_eq (Term.UOp UserOp.bvor) g = Term.Boolean false := by
        cases g <;> simp_all [__eo_eq, native_teq]
      have hfallback :
          __eo_l_1___bv_mk_bitblast_step_bitwise
              (Term.UOp UserOp.bvor) (Term.UOp UserOp.or)
              (Term.Apply (Term.Apply g head) tail) acc ≠
            Term.Stuck := by
        simpa [heqFalse, __eo_ite, native_teq, native_ite] using hne
      have haccNe := hacc.ne_stuck
      simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hfallback
      have hsame :=
        support_eo_requires_cond_eq_of_non_stuck hfallback
      have hrestEoTy :=
        EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
          (Term.Apply (Term.Apply g head) tail) xs.length hrestTy
      rw [hrestEoTy] at hsame
      have hnilNe :
          __eo_nil
              (Term.UOp UserOp.bvor)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int xs.length))) ≠
            Term.Stuck := by
        intro hs
        rw [hs] at hsame
        cases hsame
      have hnilEq :=
        bvor_generated_nil_eq_zero xs.length hnilNe
      rw [hnilEq] at hsame
      cases hsame
  case case6 hnotApp haccNe =>
    intro hacc hxW hrestTy hbf hf hne
    subst_vars
    simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hne ⊢
    have hnil := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires rest
            (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof rest)) acc =
          acc := by
      rw [← hnil]
      exact req_refl _ _ (by assumption)
    rw [hreq]
    let xc :=
      Term.Binary (xs.length : Int) (BvBitblast.bitsValue xs : Int)
    have hxcTy :
        __smtx_typeof (__eo_to_smt xc) =
          SmtType.BitVec xs.length := by
      exact smt_typeof_bitsValue xs
    have hrestEoTy :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
        rest xs.length hrestTy
    have hrestEq :
        rest =
          __eo_nil (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int xs.length))) := by
      simpa [hrestEoTy] using hnil
    have hnilNe :
        __eo_nil (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int xs.length))) ≠
          Term.Stuck := by
      have hrestNe : rest ≠ Term.Stuck := by
        intro hs
        rw [hs] at hrestTy
        change __smtx_typeof SmtTerm.None = SmtType.BitVec xs.length at hrestTy
        rw [TranslationProofs.smtx_typeof_none] at hrestTy
        cases hrestTy
      rw [← hrestEq]
      exact hrestNe
    have hmarker :=
      bvor_generated_nil_marker xs.length hnilNe
    have hid :=
      BvNaryOrSupport.evalRightNil M hM xc rest xs.length
        (by simpa [hrestEq] using hmarker)
        hxcTy hrestTy
    change
      __smtx_model_eval M (__eo_to_smt acc) =
        __smtx_model_eval_bvor
          (__smtx_model_eval M (__eo_to_smt acc))
          (__smtx_model_eval M (__eo_to_smt rest))
    rw [hacc.eval]
    have hsimpa := hid.symm
    try simp [xc] at hsimpa ⊢
    exact hsimpa
termination_by sizeOf rest

theorem eval_step_bvor_fold
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term)
    (hne :
      __bv_mk_bitblast_step_bitwise
          (Term.UOp UserOp.bvor) (Term.UOp UserOp.or) rest acc ≠
        Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) acc) rest))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_mk_bitblast_step_bitwise
            (Term.UOp UserOp.bvor) (Term.UOp UserOp.or) rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) acc) rest)) := by
  change term_has_non_none_type
      (SmtTerm.bvand (__eo_to_smt acc) (__eo_to_smt rest)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand)
      (t1 := __eo_to_smt acc) (t2 := __eo_to_smt rest)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haccTy, hrestTy⟩
  have hargs :
      __smtx_typeof (__eo_to_smt acc) = SmtType.BitVec W ∧
        __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W :=
    ⟨haccTy, hrestTy⟩
  generalize hbf : Term.UOp UserOp.bvor = bf at hne ⊢
  generalize hf : Term.UOp UserOp.or = f at hne ⊢
  revert hne hbf hf
  fun_cases __bv_mk_bitblast_step_bitwise bf f rest acc <;>
    subst_vars <;> simp_all
  case case5 head tail hbfNe hfNe haccNe =>
    intro hbf hf hne
    subst_vars
    rename_i g
    by_cases hg : g = Term.UOp UserOp.bvor
    · subst g
      simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne ⊢
      have hnewNe := fold_acc_ne hne
      have hs :=
        BvBitblast.bitblast_apply_binary_same_length
          (Term.UOp UserOp.or) acc head hnewNe
      have hparts :=
        BvNaryOrSupport.binaryArgsSmtType head tail W hargs.2
      have haccNN : term_has_non_none_type (__eo_to_smt acc) := by
        unfold term_has_non_none_type
        rw [hargs.1]
        simp
      have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hparts.1]
        simp
      rcases hs.syntax_left.eval hM haccNN with ⟨xs, hacc⟩
      rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
      have hlen := hs.eval_length hacc hhead
      have hnew := hacc.apply_or hhead hlen
      have hnewLen :
          (List.zipWith (· || ·) xs ys).length = xs.length := by
        simp [List.length_zipWith, hlen]
      have hxW :=
        bitListEval_length_eq_smt_type M hM acc xs W hacc hargs.1
      have hrec :=
        testBitsOr M hM tail
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) acc head)
          xs.length (List.zipWith (· || ·) xs ys)
          hnew hnewLen (by simpa [hxW] using hparts.2) hne
      have hnewEval := hacc.eval_bvor hhead hlen
      calc
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_mk_bitblast_step_bitwise
                (Term.UOp UserOp.bvor) (Term.UOp UserOp.or) tail
                (__bv_bitblast_apply_binary
                  (Term.UOp UserOp.or) acc head))) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvor)
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.or) acc head)) tail)) := hrec
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvor)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.bvor) acc) head))
                  tail)) := by
            change __smtx_model_eval_bvor
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.or) acc head)))
                (__smtx_model_eval M (__eo_to_smt tail)) =
              __smtx_model_eval_bvor
                (__smtx_model_eval_bvor
                  (__smtx_model_eval M (__eo_to_smt acc))
                  (__smtx_model_eval M (__eo_to_smt head)))
                (__smtx_model_eval M (__eo_to_smt tail))
            rw [hnewEval]
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) acc)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.bvor) head) tail))) :=
            BvNaryOrSupport.evalAssoc M hM acc head tail W
              hargs.1 hparts.1 hparts.2
    · by_cases hgStuck : g = Term.Stuck
      · subst g
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne
      have heqFalse :
          __eo_eq (Term.UOp UserOp.bvor) g = Term.Boolean false := by
        cases g <;> simp_all [__eo_eq, native_teq]
      have hfallback :
          __eo_l_1___bv_mk_bitblast_step_bitwise
              (Term.UOp UserOp.bvor) (Term.UOp UserOp.or)
              (Term.Apply (Term.Apply g head) tail) acc ≠
            Term.Stuck := by
        simpa [heqFalse, __eo_ite, native_teq, native_ite] using hne
      simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hfallback
      have hsame :=
        support_eo_requires_cond_eq_of_non_stuck hfallback
      have hrestEoTy :=
        EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
          (Term.Apply (Term.Apply g head) tail) W hargs.2
      rw [hrestEoTy] at hsame
      have hnilNe :
          __eo_nil
              (Term.UOp UserOp.bvor)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int W))) ≠
            Term.Stuck := by
        intro hs
        rw [hs] at hsame
        cases hsame
      have hnilEq :=
        bvor_generated_nil_eq_zero W hnilNe
      rw [hnilEq] at hsame
      cases hsame
  case case6 hnotApp haccNe =>
    intro hbf hf hne
    subst_vars
    simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hne ⊢
    have hnil := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires rest
            (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof rest)) acc =
          acc := by
      rw [← hnil]
      exact req_refl _ _ (by assumption)
    rw [hreq]
    have hrestEoTy :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
        rest W hargs.2
    have hrestEq :
        rest =
          __eo_nil (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int W))) := by
      simpa [hrestEoTy] using hnil
    have hrestNe : rest ≠ Term.Stuck := by
      intro hs
      have h := hargs.2
      rw [hs] at h
      change __smtx_typeof SmtTerm.None = SmtType.BitVec W at h
      rw [TranslationProofs.smtx_typeof_none] at h
      cases h
    have hnilNe :
        __eo_nil (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int W))) ≠
          Term.Stuck := by
      rw [← hrestEq]
      exact hrestNe
    have hmarker :=
      bvor_generated_nil_marker W hnilNe
    exact (BvNaryOrSupport.evalRightNil M hM acc rest W
      (by simpa [hrestEq] using hmarker) hargs.1 hargs.2).symm

private theorem bxor_assoc_values
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (W : Nat) (xs ys : List Bool)
    (hx : BvBitblast.BitListEval M x xs)
    (hy : BvBitblast.BitListEval M y ys)
    (hxW : xs.length = W) (hyW : ys.length = W)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) z))) := by
  let xc := Term.Binary (W : Int) (BvBitblast.bitsValue xs : Int)
  let yc := Term.Binary (W : Int) (BvBitblast.bitsValue ys : Int)
  have hxcTy : __smtx_typeof (__eo_to_smt xc) = SmtType.BitVec W := by
    simpa [xc, hxW] using smt_typeof_bitsValue xs
  have hycTy : __smtx_typeof (__eo_to_smt yc) = SmtType.BitVec W := by
    simpa [yc, hyW] using smt_typeof_bitsValue ys
  have hassoc :=
    BvNaryXorSupport.evalAssoc M hM xc yc z W hxcTy hycTy hzTy
  change
    __smtx_model_eval_bvxor
        (__smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval M (__eo_to_smt z)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt z)))
  rw [hx.eval, hy.eval, hxW, hyW]
  have hsimpa := hassoc
  try simp [xc, yc] at hsimpa ⊢
  exact hsimpa

private theorem testBitsXor
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term) (W : Nat) (xs : List Bool)
    (hacc : BvBitblast.BitListEval M acc xs)
    (hxW : xs.length = W)
    (hrestTy : __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W)
    (hne :
      __bv_mk_bitblast_step_bitwise
          (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor) rest acc ≠
        Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_mk_bitblast_step_bitwise
            (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor) rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) acc) rest)) := by
  generalize hbf : Term.UOp UserOp.bvxor = bf at hne ⊢
  generalize hf : Term.UOp UserOp.xor = f at hne ⊢
  revert hacc hxW hrestTy hne hbf hf
  fun_cases __bv_mk_bitblast_step_bitwise bf f rest acc <;>
    subst_vars <;> simp_all
  case case5 head tail hbfNe hfNe haccNe =>
    intro hacc hxW hrestTy hbf hf hne
    subst_vars
    rename_i g
    by_cases hg : g = Term.UOp UserOp.bvxor
    · subst g
      simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne ⊢
      have hnewNe := fold_acc_ne hne
      have hs :=
        BvBitblast.bitblast_apply_binary_same_length
          (Term.UOp UserOp.xor) acc head hnewNe
      have hparts :=
        BvNaryXorSupport.binaryArgsSmtType head tail xs.length hrestTy
      have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hparts.1]
        simp
      rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
      have hlen := hs.eval_length hacc hhead
      have hnew := hacc.apply_xor hhead hlen
      have hnewLen :
          (List.zipWith (· != ·) xs ys).length = xs.length := by
        simp [List.length_zipWith, hlen]
      have hrec :=
        testBitsXor M hM tail
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) acc head)
          xs.length (List.zipWith (· != ·) xs ys)
          hnew hnewLen hparts.2 hne
      have hnewEval := hacc.eval_bvxor hhead hlen
      calc
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_mk_bitblast_step_bitwise
                (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor) tail
                (__bv_bitblast_apply_binary
                  (Term.UOp UserOp.xor) acc head))) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvxor)
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.xor) acc head)) tail)) := hrec
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvxor)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.bvxor) acc) head))
                  tail)) := by
            change __smtx_model_eval_bvxor
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.xor) acc head)))
                (__smtx_model_eval M (__eo_to_smt tail)) =
              __smtx_model_eval_bvxor
                (__smtx_model_eval_bvxor
                  (__smtx_model_eval M (__eo_to_smt acc))
                  (__smtx_model_eval M (__eo_to_smt head)))
                (__smtx_model_eval M (__eo_to_smt tail))
            rw [hnewEval]
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) acc)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.bvxor) head) tail))) :=
            bxor_assoc_values M hM acc head tail xs.length xs ys
              hacc hhead rfl hlen.symm hparts.2
    · by_cases hgStuck : g = Term.Stuck
      · subst g
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne
      have heqFalse :
          __eo_eq (Term.UOp UserOp.bvxor) g = Term.Boolean false := by
        cases g <;> simp_all [__eo_eq, native_teq]
      have hfallback :
          __eo_l_1___bv_mk_bitblast_step_bitwise
              (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor)
              (Term.Apply (Term.Apply g head) tail) acc ≠
            Term.Stuck := by
        simpa [heqFalse, __eo_ite, native_teq, native_ite] using hne
      have haccNe := hacc.ne_stuck
      simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hfallback
      have hsame :=
        support_eo_requires_cond_eq_of_non_stuck hfallback
      have hrestEoTy :=
        EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
          (Term.Apply (Term.Apply g head) tail) xs.length hrestTy
      rw [hrestEoTy] at hsame
      have hnilNe :
          __eo_nil
              (Term.UOp UserOp.bvxor)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int xs.length))) ≠
            Term.Stuck := by
        intro hs
        rw [hs] at hsame
        cases hsame
      have hnilEq :=
        bvxor_generated_nil_eq_zero xs.length hnilNe
      rw [hnilEq] at hsame
      cases hsame
  case case6 hnotApp haccNe =>
    intro hacc hxW hrestTy hbf hf hne
    subst_vars
    simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hne ⊢
    have hnil := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires rest
            (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof rest)) acc =
          acc := by
      rw [← hnil]
      exact req_refl _ _ (by assumption)
    rw [hreq]
    let xc :=
      Term.Binary (xs.length : Int) (BvBitblast.bitsValue xs : Int)
    have hxcTy :
        __smtx_typeof (__eo_to_smt xc) =
          SmtType.BitVec xs.length := by
      exact smt_typeof_bitsValue xs
    have hrestEoTy :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
        rest xs.length hrestTy
    have hrestEq :
        rest =
          __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int xs.length))) := by
      simpa [hrestEoTy] using hnil
    have hnilNe :
        __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int xs.length))) ≠
          Term.Stuck := by
      have hrestNe : rest ≠ Term.Stuck := by
        intro hs
        rw [hs] at hrestTy
        change __smtx_typeof SmtTerm.None = SmtType.BitVec xs.length at hrestTy
        rw [TranslationProofs.smtx_typeof_none] at hrestTy
        cases hrestTy
      rw [← hrestEq]
      exact hrestNe
    have hmarker :=
      bvxor_generated_nil_marker xs.length hnilNe
    have hid :=
      BvNaryXorSupport.evalRightNil M hM xc rest xs.length
        (by simpa [hrestEq] using hmarker)
        hxcTy hrestTy
    change
      __smtx_model_eval M (__eo_to_smt acc) =
        __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt acc))
          (__smtx_model_eval M (__eo_to_smt rest))
    rw [hacc.eval]
    have hsimpa := hid.symm
    try simp [xc] at hsimpa ⊢
    exact hsimpa
termination_by sizeOf rest

theorem eval_step_bvxor_fold
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term)
    (hne :
      __bv_mk_bitblast_step_bitwise
          (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor) rest acc ≠
        Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) acc) rest))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_mk_bitblast_step_bitwise
            (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor) rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) acc) rest)) := by
  change term_has_non_none_type
      (SmtTerm.bvand (__eo_to_smt acc) (__eo_to_smt rest)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand)
      (t1 := __eo_to_smt acc) (t2 := __eo_to_smt rest)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haccTy, hrestTy⟩
  have hargs :
      __smtx_typeof (__eo_to_smt acc) = SmtType.BitVec W ∧
        __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W :=
    ⟨haccTy, hrestTy⟩
  generalize hbf : Term.UOp UserOp.bvxor = bf at hne ⊢
  generalize hf : Term.UOp UserOp.xor = f at hne ⊢
  revert hne hbf hf
  fun_cases __bv_mk_bitblast_step_bitwise bf f rest acc <;>
    subst_vars <;> simp_all
  case case5 head tail hbfNe hfNe haccNe =>
    intro hbf hf hne
    subst_vars
    rename_i g
    by_cases hg : g = Term.UOp UserOp.bvxor
    · subst g
      simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne ⊢
      have hnewNe := fold_acc_ne hne
      have hs :=
        BvBitblast.bitblast_apply_binary_same_length
          (Term.UOp UserOp.xor) acc head hnewNe
      have hparts :=
        BvNaryXorSupport.binaryArgsSmtType head tail W hargs.2
      have haccNN : term_has_non_none_type (__eo_to_smt acc) := by
        unfold term_has_non_none_type
        rw [hargs.1]
        simp
      have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hparts.1]
        simp
      rcases hs.syntax_left.eval hM haccNN with ⟨xs, hacc⟩
      rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
      have hlen := hs.eval_length hacc hhead
      have hnew := hacc.apply_xor hhead hlen
      have hnewLen :
          (List.zipWith (· != ·) xs ys).length = xs.length := by
        simp [List.length_zipWith, hlen]
      have hxW :=
        bitListEval_length_eq_smt_type M hM acc xs W hacc hargs.1
      have hrec :=
        testBitsXor M hM tail
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) acc head)
          xs.length (List.zipWith (· != ·) xs ys)
          hnew hnewLen (by simpa [hxW] using hparts.2) hne
      have hnewEval := hacc.eval_bvxor hhead hlen
      calc
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_mk_bitblast_step_bitwise
                (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor) tail
                (__bv_bitblast_apply_binary
                  (Term.UOp UserOp.xor) acc head))) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvxor)
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.xor) acc head)) tail)) := hrec
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvxor)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.bvxor) acc) head))
                  tail)) := by
            change __smtx_model_eval_bvxor
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__bv_bitblast_apply_binary
                      (Term.UOp UserOp.xor) acc head)))
                (__smtx_model_eval M (__eo_to_smt tail)) =
              __smtx_model_eval_bvxor
                (__smtx_model_eval_bvxor
                  (__smtx_model_eval M (__eo_to_smt acc))
                  (__smtx_model_eval M (__eo_to_smt head)))
                (__smtx_model_eval M (__eo_to_smt tail))
            rw [hnewEval]
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) acc)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.bvxor) head) tail))) :=
            BvNaryXorSupport.evalAssoc M hM acc head tail W
              hargs.1 hparts.1 hparts.2
    · by_cases hgStuck : g = Term.Stuck
      · subst g
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hne
      have heqFalse :
          __eo_eq (Term.UOp UserOp.bvxor) g = Term.Boolean false := by
        cases g <;> simp_all [__eo_eq, native_teq]
      have hfallback :
          __eo_l_1___bv_mk_bitblast_step_bitwise
              (Term.UOp UserOp.bvxor) (Term.UOp UserOp.xor)
              (Term.Apply (Term.Apply g head) tail) acc ≠
            Term.Stuck := by
        simpa [heqFalse, __eo_ite, native_teq, native_ite] using hne
      simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hfallback
      have hsame :=
        support_eo_requires_cond_eq_of_non_stuck hfallback
      have hrestEoTy :=
        EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
          (Term.Apply (Term.Apply g head) tail) W hargs.2
      rw [hrestEoTy] at hsame
      have hnilNe :
          __eo_nil
              (Term.UOp UserOp.bvxor)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int W))) ≠
            Term.Stuck := by
        intro hs
        rw [hs] at hsame
        cases hsame
      have hnilEq :=
        bvxor_generated_nil_eq_zero W hnilNe
      rw [hnilEq] at hsame
      cases hsame
  case case6 hnotApp haccNe =>
    intro hbf hf hne
    subst_vars
    simp [__eo_l_1___bv_mk_bitblast_step_bitwise] at hne ⊢
    have hnil := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires rest
            (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof rest)) acc =
          acc := by
      rw [← hnil]
      exact req_refl _ _ (by assumption)
    rw [hreq]
    have hrestEoTy :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
        rest W hargs.2
    have hrestEq :
        rest =
          __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int W))) := by
      simpa [hrestEoTy] using hnil
    have hrestNe : rest ≠ Term.Stuck := by
      intro hs
      have h := hargs.2
      rw [hs] at h
      change __smtx_typeof SmtTerm.None = SmtType.BitVec W at h
      rw [TranslationProofs.smtx_typeof_none] at h
      cases h
    have hnilNe :
        __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int W))) ≠
          Term.Stuck := by
      rw [← hrestEq]
      exact hrestNe
    have hmarker :=
      bvxor_generated_nil_marker W hnilNe
    exact (BvNaryXorSupport.evalRightNil M hM acc rest W
      (by simpa [hrestEq] using hmarker) hargs.1 hargs.2).symm


private theorem add_acc_ne {rest acc : Term}
    (h : __bv_mk_bitblast_step_add rest acc ≠ Term.Stuck) :
    acc ≠ Term.Stuck := by
  intro ha
  subst acc
  apply h
  cases rest <;> rfl

private theorem add_smt_typeof_bitsValue (xs : List Bool) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Binary (xs.length : Int)
            (BvBitblast.bitsValue xs : Int))) =
      SmtType.BitVec xs.length := by
  have hW0 : native_zleq 0 (xs.length : Int) = true := by
    simp [SmtEval.native_zleq]
  have hCanon :
      native_zeq (BvBitblast.bitsValue xs : Int)
          (native_mod_total (BvBitblast.bitsValue xs : Int)
            (native_int_pow2 (xs.length : Int))) = true := by
    have hWCast :
        (xs.length : Int) = native_nat_to_int xs.length := by
      simp [native_nat_to_int, Smtm.native_nat_to_int]
    rw [hWCast, BvBitblast.native_int_pow2_native_nat xs.length]
    have hMod :
        (BvBitblast.bitsValue xs : Int) % (2 ^ xs.length : Nat) =
          BvBitblast.bitsValue xs := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast BvBitblast.bitsValue_lt xs)
    have hsimpa := hMod.symm
    try simp [SmtEval.native_zeq, SmtEval.native_mod_total] at hsimpa ⊢
    exact decide_eq_true hsimpa
  change
    __smtx_typeof
        (SmtTerm.Binary (xs.length : Int)
          (BvBitblast.bitsValue xs : Int)) =
      SmtType.BitVec xs.length
  simp [__smtx_typeof, native_and, hW0, hCanon, native_ite,
    native_int_to_nat]

private theorem add_assoc_values
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (W : Nat) (xs ys : List Bool)
    (hx : BvBitblast.BitListEval M x xs)
    (hy : BvBitblast.BitListEval M y ys)
    (hxW : xs.length = W) (hyW : ys.length = W)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt
          (BvNaryAddSupport.add (BvNaryAddSupport.add x y) z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (BvNaryAddSupport.add x (BvNaryAddSupport.add y z))) := by
  simp only [BvNaryAddSupport.add_eq]
  let xc := Term.Binary (W : Int) (BvBitblast.bitsValue xs : Int)
  let yc := Term.Binary (W : Int) (BvBitblast.bitsValue ys : Int)
  have hxcTy : __smtx_typeof (__eo_to_smt xc) = SmtType.BitVec W := by
    simpa [xc, hxW] using add_smt_typeof_bitsValue xs
  have hycTy : __smtx_typeof (__eo_to_smt yc) = SmtType.BitVec W := by
    simpa [yc, hyW] using add_smt_typeof_bitsValue ys
  have hassoc :=
    BvNaryAddSupport.addAssocEval M hM xc yc z W hxcTy hycTy hzTy
  change
    __smtx_model_eval_bvadd
        (__smtx_model_eval_bvadd
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval M (__eo_to_smt z)) =
      __smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_bvadd
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt z)))
  rw [hx.eval, hy.eval, hxW, hyW]
  have hsimpa := hassoc
  try simp [xc, yc] at hsimpa ⊢
  exact hsimpa

private theorem testBitsAdd
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term) (W : Nat) (xs : List Bool)
    (hacc : BvBitblast.BitListEval M acc xs)
    (hxW : xs.length = W)
    (hrestTy : __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W)
    (hne : __bv_mk_bitblast_step_add rest acc ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_add rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) acc) rest)) := by
  revert hacc hxW hrestTy hne
  fun_cases __bv_mk_bitblast_step_add rest acc <;>
    subst_vars <;> simp_all
  case case3 head tail haccNe =>
    intro hacc hxW hrestTy hne
    have hnewNe := add_acc_ne hne
    have hripple := BvBitblast.pair_second_arg_ne_stuck hnewNe
    have hs := BvBitblast.ripple_carry_same_length
      acc head (Term.Boolean false) (Term.Binary 0 0) hripple
    have hparts :=
      BvNaryAddSupport.addArgsOfBitvecType head tail xs.length
        (by simpa [BvNaryAddSupport.add_eq, hxW] using hrestTy)
    have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
      unfold term_has_non_none_type
      rw [hparts.1]
      simp
    rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
    have hlen := hs.eval_length hacc hhead
    have hc :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := rfl
    have hp := BvBitblast.ripple_carry_eval hacc hhead hc hlen
    have hnew := hp.second
    have hnewLen : (BvBitblast.addBits xs ys false).length = xs.length :=
      BvBitblast.addBits_length hlen
    have hrec :=
      testBitsAdd M hM tail
        (__pair_second
          (__bv_ripple_carry_adder_2 acc head (Term.Boolean false)
            (Term.Binary 0 0)))
        xs.length (BvBitblast.addBits xs ys false)
        hnew hnewLen hparts.2 hne
    have hnewEval := BvBitblast.eval_addBits hacc hhead hlen
    calc
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_mk_bitblast_step_add tail
              (__pair_second
                (__bv_ripple_carry_adder_2 acc head
                  (Term.Boolean false) (Term.Binary 0 0))))) =
          __smtx_model_eval M
            (__eo_to_smt
              (BvNaryAddSupport.add
                (__pair_second
                  (__bv_ripple_carry_adder_2 acc head
                    (Term.Boolean false) (Term.Binary 0 0)))
                tail)) := by
          simpa only [BvNaryAddSupport.add_eq] using hrec
      _ = __smtx_model_eval M
            (__eo_to_smt
              (BvNaryAddSupport.add
                (BvNaryAddSupport.add acc head) tail)) := by
          simp only [BvNaryAddSupport.add_eq]
          change __smtx_model_eval_bvadd
              (__smtx_model_eval M
                (__eo_to_smt
                  (__pair_second
                    (__bv_ripple_carry_adder_2 acc head
                      (Term.Boolean false) (Term.Binary 0 0)))))
              (__smtx_model_eval M (__eo_to_smt tail)) =
            __smtx_model_eval_bvadd
              (__smtx_model_eval_bvadd
                (__smtx_model_eval M (__eo_to_smt acc))
                (__smtx_model_eval M (__eo_to_smt head)))
              (__smtx_model_eval M (__eo_to_smt tail))
          rw [← hnewEval]
      _ = __smtx_model_eval M
            (__eo_to_smt
              (BvNaryAddSupport.add acc
                (BvNaryAddSupport.add head tail))) :=
          by
            simpa only [BvNaryAddSupport.add_eq] using
              add_assoc_values M hM acc head tail xs.length xs ys
                hacc hhead rfl hlen.symm hparts.2
  case case4 hnot =>
    intro hacc hxW hrestTy hne
    have hz := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires (__eo_to_z rest) (Term.Numeral 0) acc = acc := by
      rw [hz]
      simp [__eo_requires, native_ite, native_teq, native_not]
    rw [hreq]
    have hnil :
        __eo_is_list_nil (Term.UOp UserOp.bvadd) rest =
          Term.Boolean true := by
      cases rest <;>
        simp_all [__eo_to_z, __eo_is_list_nil, __eo_is_list_nil_bvadd,
          __eo_is_eq, native_and, native_not, native_teq, native_zeq]
    let xc :=
      Term.Binary (xs.length : Int) (BvBitblast.bitsValue xs : Int)
    have hxcTy :
        __smtx_typeof (__eo_to_smt xc) =
          SmtType.BitVec xs.length := add_smt_typeof_bitsValue xs
    have hid :=
      BvNaryAddSupport.evalRightZero M hM xc rest xs.length
        hxcTy (by simpa [hxW] using hrestTy) hnil
    change
      __smtx_model_eval M (__eo_to_smt acc) =
        __smtx_model_eval_bvadd
          (__smtx_model_eval M (__eo_to_smt acc))
          (__smtx_model_eval M (__eo_to_smt rest))
    rw [hacc.eval]
    have hsimpa := hid.symm
    try simp [xc, BvNaryAddSupport.add_eq] at hsimpa ⊢
    exact hsimpa
termination_by sizeOf rest

theorem eval_step_bvadd_fold
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term)
    (hne : __bv_mk_bitblast_step_add rest acc ≠ Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) acc) rest))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_add rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) acc) rest)) := by
  change term_has_non_none_type
      (SmtTerm.bvadd (__eo_to_smt acc) (__eo_to_smt rest)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvadd)
      (t1 := __eo_to_smt acc) (t2 := __eo_to_smt rest)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haccTy, hrestTy⟩
  revert hne
  fun_cases __bv_mk_bitblast_step_add rest acc <;>
    subst_vars <;> simp_all
  case case3 head tail haccNe =>
    intro hne
    have hnewNe := add_acc_ne hne
    have hripple := BvBitblast.pair_second_arg_ne_stuck hnewNe
    have hs := BvBitblast.ripple_carry_same_length
      acc head (Term.Boolean false) (Term.Binary 0 0) hripple
    have hparts :=
      BvNaryAddSupport.addArgsOfBitvecType head tail W
        (by simpa [BvNaryAddSupport.add_eq] using hrestTy)
    have haccNN : term_has_non_none_type (__eo_to_smt acc) := by
      unfold term_has_non_none_type
      rw [haccTy]
      simp
    have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
      unfold term_has_non_none_type
      rw [hparts.1]
      simp
    rcases hs.syntax_left.eval hM haccNN with ⟨xs, hacc⟩
    rcases hs.syntax_right.eval hM hheadNN with ⟨ys, hhead⟩
    have hlen := hs.eval_length hacc hhead
    have hc :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := rfl
    have hp := BvBitblast.ripple_carry_eval hacc hhead hc hlen
    have hnew := hp.second
    have hnewLen : (BvBitblast.addBits xs ys false).length = xs.length :=
      BvBitblast.addBits_length hlen
    have hxW :=
      BvBitblast.bitListEval_length_eq_smt_type
        M hM acc xs W hacc haccTy
    have hrec :=
      testBitsAdd M hM tail
        (__pair_second
          (__bv_ripple_carry_adder_2 acc head (Term.Boolean false)
            (Term.Binary 0 0)))
        xs.length (BvBitblast.addBits xs ys false)
        hnew hnewLen (by simpa [hxW] using hparts.2) hne
    have hnewEval := BvBitblast.eval_addBits hacc hhead hlen
    calc
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_mk_bitblast_step_add tail
              (__pair_second
                (__bv_ripple_carry_adder_2 acc head
                  (Term.Boolean false) (Term.Binary 0 0))))) =
          __smtx_model_eval M
            (__eo_to_smt
              (BvNaryAddSupport.add
                (__pair_second
                  (__bv_ripple_carry_adder_2 acc head
                    (Term.Boolean false) (Term.Binary 0 0)))
                tail)) := by
          simpa only [BvNaryAddSupport.add_eq] using hrec
      _ = __smtx_model_eval M
            (__eo_to_smt
              (BvNaryAddSupport.add
                (BvNaryAddSupport.add acc head) tail)) := by
          simp only [BvNaryAddSupport.add_eq]
          change __smtx_model_eval_bvadd
              (__smtx_model_eval M
                (__eo_to_smt
                  (__pair_second
                    (__bv_ripple_carry_adder_2 acc head
                      (Term.Boolean false) (Term.Binary 0 0)))))
              (__smtx_model_eval M (__eo_to_smt tail)) =
            __smtx_model_eval_bvadd
              (__smtx_model_eval_bvadd
                (__smtx_model_eval M (__eo_to_smt acc))
                (__smtx_model_eval M (__eo_to_smt head)))
              (__smtx_model_eval M (__eo_to_smt tail))
          rw [← hnewEval]
      _ = __smtx_model_eval M
            (__eo_to_smt
              (BvNaryAddSupport.add acc
                (BvNaryAddSupport.add head tail))) :=
          by
            simpa only [BvNaryAddSupport.add_eq] using
              BvNaryAddSupport.addAssocEval M hM acc head tail W
                haccTy hparts.1 hparts.2
  case case4 hnot =>
    intro hne
    have hz := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires (__eo_to_z rest) (Term.Numeral 0) acc = acc := by
      rw [hz]
      simp [__eo_requires, native_ite, native_teq, native_not]
    rw [hreq]
    have hnil :
        __eo_is_list_nil (Term.UOp UserOp.bvadd) rest =
          Term.Boolean true := by
      cases rest <;>
        simp_all [__eo_to_z, __eo_is_list_nil, __eo_is_list_nil_bvadd,
          __eo_is_eq, native_and, native_not, native_teq, native_zeq]
    simpa only [BvNaryAddSupport.add_eq] using
      (BvNaryAddSupport.evalRightZero M hM acc rest W
        haccTy hrestTy hnil).symm

private theorem bitCons_type_info
    {b tail : Term} {W : Nat}
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) b) tail)) =
        SmtType.BitVec W) :
    ∃ wt : Nat,
      W = wt + 1 ∧
        __smtx_typeof (__eo_to_smt tail) = SmtType.BitVec wt ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
  let bit :=
    SmtTerm.ite (__eo_to_smt b) (SmtTerm.Binary 1 1)
      (SmtTerm.Binary 1 0)
  have hConcatTy :
      __smtx_typeof (SmtTerm.concat (__eo_to_smt tail) bit) =
        SmtType.BitVec W := by
    have hsimpa := hTy
    try simp [bit] at hsimpa ⊢
    exact hsimpa
  have hConcatNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt tail) bit) := by
    unfold term_has_non_none_type
    rw [hConcatTy]
    simp
  rcases bv_concat_args_of_non_none hConcatNN with
    ⟨wt, wb, htailTy, hbitTy⟩
  have hbitNN : term_has_non_none_type bit := by
    unfold term_has_non_none_type
    rw [hbitTy]
    simp
  rcases ite_args_of_non_none hbitNN with
    ⟨T, hbTy, honeTy, _hzeroTy, _hT⟩
  have hT : T = SmtType.BitVec 1 := by
    have hsimpa := honeTy.symm
    try simp [__smtx_typeof] at hsimpa ⊢
    exact hsimpa
  have hwb : wb = 1 := by
    rw [typeof_ite_eq, hbTy] at hbitTy
    simp [__smtx_typeof_ite, native_ite] at hbitTy
    exact SmtType.BitVec.inj hbitTy.symm
  have hW : W = wt + wb := by
    rw [typeof_concat_eq, htailTy, hbitTy] at hConcatTy
    simp [__smtx_typeof_concat,
      SmtEval.native_zplus, native_nat_to_int,
      Smtm.native_nat_to_int, native_int_to_nat,
      SmtEval.native_int_to_nat] at hConcatTy
    have hsimpa := hConcatTy.symm
    try simp at hsimpa ⊢
    exact hsimpa
  exact ⟨wt, by simpa [hwb] using hW, htailTy, hbTy⟩

private theorem eval_bool_of_type
    (M : SmtModel) (hM : model_wf M) (b : Term)
    (hTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool) :
    ∃ v : Bool,
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean v := by
  have hnn : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hp := type_preservation M hM (__eo_to_smt b) hnn
  rcases bool_value_canonical (by simpa [hTy] using hp) with ⟨v, hv⟩
  exact ⟨v, hv⟩

private theorem concat_bool_bitvec_value
    (x : BitVec W) (b : Bool) :
    __smtx_model_eval_concat
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary 1 (b.toNat : Int)) =
      SmtValue.Binary ((W + 1 : Nat) : Int)
        ((x.concat b).toNat : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  rw [show (W : Int) + 1 = ((W + 1 : Nat) : Int) by simp]
  rw [show (1 : Int) = native_nat_to_int 1 by rfl,
    native_int_pow2_native_nat 1]
  rw [show ((W + 1 : Nat) : Int) =
      native_nat_to_int (W + 1) by rfl,
    native_int_pow2_native_nat (W + 1)]
  simp only [Nat.pow_one]
  rw [show ((2 : Nat) : Int) = 2 by rfl]
  have hFormula :
      (x.toNat : Int) * 2 + (b.toNat : Int) =
        ((x.concat b).toNat : Int) := by
    norm_cast
    exact (BitVec.toNat_concat x b).symm
  rw [hFormula]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (by exact_mod_cast (x.concat b).isLt)]

private theorem eval_bitvec_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term) (W : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec W) :
    ∃ x : BitVec W,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (W : Int) (x.toNat : Int) := by
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt t) W hTy with
    ⟨p, hp, hcan⟩
  have hWidth0 :
      native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hrange := bitvec_payload_range_of_canonical hWidth0 hcan
  have hp0 : (0 : Int) ≤ p := hrange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hrange.2
  let x := BitVec.ofInt W p
  have hx : (x.toNat : Int) = p := by
    rw [show x.toNat = p.toNat by
      exact ofInt_toNat_canonical W p hp0 hp1]
    exact Int.toNat_of_nonneg hp0
  exact ⟨x, by simpa [hx, native_nat_to_int,
    Smtm.native_nat_to_int] using hp⟩

private theorem eval_bit_ite
    (M : SmtModel) (b : Term) (v : Bool)
    (hb :
      __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Boolean v) :
    __smtx_model_eval M
        (SmtTerm.ite (__eo_to_smt b)
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
      SmtValue.Binary 1 (v.toNat : Int) := by
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hb]
  cases v <;> rfl

private theorem eval_bit_cons
    (M : SmtModel) (b tail : Term) (v : Bool) (x : BitVec W)
    (hb :
      __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Boolean v)
    (htail :
      __smtx_model_eval M (__eo_to_smt tail) =
        SmtValue.Binary (W : Int) (x.toNat : Int)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) b) tail)) =
      SmtValue.Binary ((W + 1 : Nat) : Int)
        ((x.concat v).toNat : Int) := by
  change __smtx_model_eval M
      (SmtTerm.concat (__eo_to_smt tail)
        (SmtTerm.ite (__eo_to_smt b)
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))) = _
  rw [smtx_eval_concat_term_eq, htail, eval_bit_ite M b v hb,
    concat_bool_bitvec_value]

private theorem extractLsb'_concat_prefix
    (x : BitVec W) (b : Bool) (n : Nat) (hfit : n ≤ W) :
    (x.concat b).extractLsb' 0 (n + 1) =
      (x.extractLsb' 0 n).concat b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_concat]
  simp only [hi, decide_true, Nat.zero_add]
  by_cases hi0 : i = 0
  · simp [hi0]
  · rw [BitVec.getLsbD_concat]
    simp only [hi0, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb']
    have him1 : i - 1 < n := by omega
    simp [him1]

private theorem extractLsb'_concat_succ
    (x : BitVec W) (b : Bool) (l d : Nat) :
    (x.concat b).extractLsb' (l + 1) d =
      x.extractLsb' l d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp only [hi, decide_true]
  rw [BitVec.getLsbD_concat]
  have hne : l + 1 + i ≠ 0 := by omega
  simp

private theorem prefix_eval_typed
    (M : SmtModel) (hM : model_wf M)
    (a : Term) (n W : Nat)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec W)
    (hfit : n ≤ W)
    (hne :
      __bv_bitblast_prefix (Term.Numeral (n : Int)) a ≠
        Term.Stuck) :
    ∃ x : BitVec W,
      __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (W : Int) (x.toNat : Int) ∧
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_bitblast_prefix (Term.Numeral (n : Int)) a)) =
          SmtValue.Binary (n : Int)
            ((x.extractLsb' 0 n).toNat : Int) := by
  induction n generalizing a W with
  | zero =>
      rcases eval_bitvec_of_type M hM a W hTy with ⟨x, hx⟩
      refine ⟨x, hx, ?_⟩
      have haNe : a ≠ Term.Stuck := by
        intro ha
        subst a
        simp [__bv_bitblast_prefix] at hne
      have hprefix :
          __bv_bitblast_prefix
              (Term.Numeral ((0 : Nat) : Int)) a =
            Term.Binary 0 0 := by
        simpa using __bv_bitblast_prefix.eq_3 a haNe
      rw [hprefix]
      have hsimpa := smtx_eval_binary_term_eq M 0 0
      try simp at hsimpa ⊢
      exact hsimpa
  | succ n ih =>
      generalize hlen :
          Term.Numeral ((n + 1 : Nat) : Int) = len at hne ⊢
      revert hTy hfit hne hlen
      fun_cases __bv_bitblast_prefix len a <;>
        subst_vars <;> simp_all
      case case3 =>
        intro _ _ hzero
        injection hzero with hzero
        exact False.elim (Nat.noConfusion hzero)
      case case4 =>
        intro hTy hfit hlen
        have hW0 : W = 0 := by
          change __smtx_typeof (SmtTerm.Binary 0 0) =
            SmtType.BitVec W at hTy
          simpa [__smtx_typeof, SmtEval.native_and, native_ite,
            SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
            native_mod_total, native_int_to_nat,
            SmtEval.native_int_to_nat] using
              (SmtType.BitVec.inj hTy).symm
        omega
      case case5 =>
        rename_i b tail hLenNe hLenZero
        intro hTy hfit hlen hne
        subst len
        have hsub :
            __eo_add
                (Term.Numeral ((n : Int) + 1))
                (Term.Numeral (-1 : Int)) =
              Term.Numeral (n : Int) := by
          simp [__eo_add, native_zplus]
          simp [Int.add_assoc]
        rw [hsub] at hne ⊢
        rcases bitCons_type_info hTy with
          ⟨wt, hW, htailTy, hbTy⟩
        subst W
        have hfit' : n ≤ wt := by omega
        have hrecNe :
            __bv_bitblast_prefix (Term.Numeral (n : Int)) tail ≠
              Term.Stuck :=
          eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hne
        rcases ih tail wt htailTy hfit' hrecNe with
          ⟨x, hx, hprefix⟩
        rcases eval_bool_of_type M hM b hbTy with ⟨v, hv⟩
        refine ⟨x.concat v, ?_, ?_⟩
        · exact eval_bit_cons M b tail v x hv hx
        · rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hne]
          change _ =
            SmtValue.Binary ((n + 1 : Nat) : Int)
              (((x.concat v).extractLsb' 0 (n + 1)).toNat : Int)
          rw [extractLsb'_concat_prefix x v n hfit']
          exact eval_bit_cons M b
            (__bv_bitblast_prefix (Term.Numeral (n : Int)) tail)
            v (x.extractLsb' 0 n) hv hprefix

private theorem subsequence_eval_typed
    (M : SmtModel) (hM : model_wf M)
    (a : Term) (l d W : Nat)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec W)
    (hfit : l + (d + 1) ≤ W)
    (hne :
      __bv_bitblast_subsequence
          (Term.Numeral (l : Int))
          (Term.Numeral ((l + d : Nat) : Int)) a ≠
        Term.Stuck) :
    ∃ x : BitVec W,
      __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (W : Int) (x.toNat : Int) ∧
        __smtx_model_eval M
            (__eo_to_smt
              (__bv_bitblast_subsequence
                (Term.Numeral (l : Int))
                (Term.Numeral ((l + d : Nat) : Int)) a)) =
          SmtValue.Binary ((d + 1 : Nat) : Int)
            ((x.extractLsb' l (d + 1)).toNat : Int) := by
  induction l generalizing a W with
  | zero =>
      have haNe : a ≠ Term.Stuck := by
        intro ha
        subst a
        simp [__bv_bitblast_subsequence] at hne
      have haZero : a ≠ Term.Binary 0 0 := by
        intro ha
        subst a
        have hW0 : W = 0 := by
          change __smtx_typeof (SmtTerm.Binary 0 0) =
            SmtType.BitVec W at hTy
          simpa [__smtx_typeof, SmtEval.native_and, native_ite,
            SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
            native_mod_total, native_int_to_nat,
            SmtEval.native_int_to_nat] using
              (SmtType.BitVec.inj hTy).symm
        omega
      have hseq :
          __bv_bitblast_subsequence
              (Term.Numeral ((0 : Nat) : Int))
              (Term.Numeral (d : Int)) a =
            __bv_bitblast_prefix
              (__eo_add (Term.Numeral (d : Int))
                (Term.Numeral 1)) a := by
        simpa using __bv_bitblast_subsequence.eq_5
          (Term.Numeral (d : Int)) a
          (by intro h; cases h) haNe haZero
      simp only [Nat.zero_add] at hne ⊢
      rw [hseq] at hne ⊢
      have hadd :
          __eo_add (Term.Numeral (d : Int)) (Term.Numeral 1) =
            Term.Numeral ((d + 1 : Nat) : Int) := by
        simp [__eo_add, native_zplus]
      rw [hadd] at hne ⊢
      simpa using
        prefix_eval_typed M hM a (d + 1) W hTy (by omega) hne
  | succ l ih =>
      generalize hl :
          Term.Numeral ((l + 1 : Nat) : Int) = lower at hne ⊢
      generalize hu :
          Term.Numeral (((l + 1) + d : Nat) : Int) = upper at hne ⊢
      revert hTy hfit hne hl hu
      fun_cases __bv_bitblast_subsequence lower upper a <;>
        subst_vars <;> simp_all
      case case4 =>
        intro hTy hfit _ _
        have hW0 : W = 0 := by
          change __smtx_typeof (SmtTerm.Binary 0 0) =
            SmtType.BitVec W at hTy
          simpa [__smtx_typeof, SmtEval.native_and, native_ite,
            SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
            native_mod_total, native_int_to_nat,
            SmtEval.native_int_to_nat] using
              (SmtType.BitVec.inj hTy).symm
        omega
      case case5 =>
        intro _ _ hzero _ _
        have hpos : (0 : Int) < (l : Int) + 1 := by omega
        exact False.elim ((Int.ne_of_gt hpos) hzero)
      case case6 =>
        rename_i b tail hLowerNe hLowerZero hUpperNe
        intro hTy hfit hl hu hne
        subst lower
        subst upper
        have hlsub :
            __eo_add
                (Term.Numeral ((l : Int) + 1))
                (Term.Numeral (-1 : Int)) =
              Term.Numeral (l : Int) := by
          simp [__eo_add, native_zplus, Int.add_assoc]
        have husub :
            __eo_add
                (Term.Numeral ((l : Int) + 1 + (d : Int)))
                (Term.Numeral (-1 : Int)) =
              Term.Numeral ((l + d : Nat) : Int) := by
          simp [__eo_add, native_zplus]
          simp [Int.add_assoc, Int.add_left_comm]
        rw [hlsub, husub] at hne ⊢
        rcases bitCons_type_info hTy with
          ⟨wt, hW, htailTy, hbTy⟩
        subst W
        have hfit' : l + (d + 1) ≤ wt := by omega
        rcases ih tail wt htailTy hfit' hne with
          ⟨x, hx, hout⟩
        rcases eval_bool_of_type M hM b hbTy with ⟨v, hv⟩
        refine ⟨x.concat v, ?_, ?_⟩
        · exact eval_bit_cons M b tail v x hv hx
        · change _ =
            SmtValue.Binary ((d + 1 : Nat) : Int)
              (((x.concat v).extractLsb' (l + 1) (d + 1)).toNat : Int)
          rw [extractLsb'_concat_succ x v l (d + 1)]
          exact hout

private theorem eval_step_extract
    (M : SmtModel) (hM : model_wf M)
    (u l a : Term)
    (hne : __bv_bitblast_subsequence l u a ≠ Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract u l) a))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_subsequence l u a)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract u l) a)) := by
  change term_has_non_none_type
      (SmtTerm.extract (__eo_to_smt u) (__eo_to_smt l) (__eo_to_smt a))
    at hnn
  rcases extract_args_of_non_none hnn with
    ⟨ui, li, W, hu, hl, haTy, hli0, hwidth, huiW⟩
  have huTerm : u = Term.Numeral ui :=
    TranslationProofs.eo_to_smt_eq_numeral u ui hu
  have hlTerm : l = Term.Numeral li :=
    TranslationProofs.eo_to_smt_eq_numeral l li hl
  subst u
  subst l
  have hli : (0 : Int) ≤ li := by
    simpa [SmtEval.native_zleq] using hli0
  have hwidth' : (0 : Int) < ui + 1 + -li := by
    have hsimpa := hwidth
    try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact of_decide_eq_true hsimpa
  have hliui : li ≤ ui := by
    apply Int.le_of_lt_add_one
    omega
  have hui0 : (0 : Int) ≤ ui := Int.le_trans hli hliui
  have huiW' : ui < (W : Int) := by
    have hsimpa := huiW
    try simp [SmtEval.native_zlt, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact of_decide_eq_true hsimpa
  let L : Nat := li.toNat
  let U : Nat := ui.toNat
  have hL : (L : Int) = li := by
    simp [L, Int.toNat_of_nonneg hli]
  have hU : (U : Int) = ui := by
    simp [U, Int.toNat_of_nonneg hui0]
  have hLU : L ≤ U := by
    simpa [L, U] using Int.toNat_le_toNat hliui
  have hUW : U < W := by
    have hUWInt : (U : Int) < (W : Int) := by
      rw [hU]
      exact huiW'
    exact_mod_cast hUWInt
  have hLower :
      (L : Int) = li := hL
  have hUpper :
      (((L + (U - L) : Nat) : Int)) = ui := by
    rw [show L + (U - L) = U by omega, hU]
  have hne' :
      __bv_bitblast_subsequence
          (Term.Numeral (L : Int))
          (Term.Numeral ((L + (U - L) : Nat) : Int)) a ≠
        Term.Stuck := by
    rw [hLower, hUpper]
    exact hne
  rcases subsequence_eval_typed M hM a L (U - L) W
      haTy (by omega) hne' with
    ⟨x, hx, hout⟩
  have hout' :
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_bitblast_subsequence
              (Term.Numeral li) (Term.Numeral ui) a)) =
        SmtValue.Binary (((U - L) + 1 : Nat) : Int)
          ((x.extractLsb' L ((U - L) + 1)).toNat : Int) := by
    rw [← hLower, ← hUpper]
    exact hout
  rw [hout']
  change
    SmtValue.Binary (((U - L) + 1 : Nat) : Int)
        ((x.extractLsb' L ((U - L) + 1)).toNat : Int) =
      __smtx_model_eval M
        (SmtTerm.extract (SmtTerm.Numeral ui)
          (SmtTerm.Numeral li) (__eo_to_smt a))
  rw [smtx_eval_extract_term_eq, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_2, hx]
  have hp0 : (0 : Int) ≤ (x.toNat : Int) := Int.natCast_nonneg _
  have hp1 : (x.toNat : Int) < (2 : Int) ^ W := by
    exact_mod_cast x.isLt
  have hd :
      ui + 1 + -li = (((U - L) + 1 : Nat) : Int) := by
    rw [← hU, ← hL]
    rw [show U = L + (U - L) by omega]
    simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
    clear hout hout' hx hp0 hp1 x
    calc
      (L : Int) + ((U - L : Nat) + (-(L : Int) + 1)) =
          ((L : Int) + -(L : Int)) + ((U - L : Nat) + 1) := by
        simp [Int.add_assoc, Int.add_left_comm]
      _ = (U - L : Nat) + 1 := by
        rw [show (L : Int) + -(L : Int) = 0 by
          simpa using Int.add_neg_cancel_left (L : Int) 0]
        exact Int.zero_add _
  rw [extract_val_bitvec_start_len W L ((U - L) + 1)
    (x.toNat : Int) ui li hp0 hp1 hL.symm hd]
  rw [bitvec_ofInt_natCast_toNat]

private theorem bitCons_type
    {b tail : Term} {W : Nat}
    (htail :
      __smtx_typeof (__eo_to_smt tail) = SmtType.BitVec W)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Bool) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) b) tail)) =
      SmtType.BitVec (W + 1) := by
  change __smtx_typeof
      (SmtTerm.concat (__eo_to_smt tail)
        (SmtTerm.ite (__eo_to_smt b)
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))) =
    SmtType.BitVec (W + 1)
  have hite :
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt b)
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.BitVec 1 := by
    rw [typeof_ite_eq, hb]
    rfl
  rw [typeof_concat_eq, htail, hite]
  simp [__smtx_typeof_concat,
    SmtEval.native_zplus, native_nat_to_int,
    Smtm.native_nat_to_int, native_int_to_nat,
    SmtEval.native_int_to_nat]

private theorem bitblast_concat_type
    (a b : Term) (wa wb : Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec wb)
    (hne : __bv_bitblast_concat a b ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__bv_bitblast_concat a b)) =
      SmtType.BitVec (wb + wa) := by
  revert wa wb haTy hbTy hne
  fun_induction __bv_bitblast_concat a b <;> simp_all
  case case2 bit tail b hbNe ih =>
    intro wa wb haTy hbTy hne
    rcases bitCons_type_info haTy with
      ⟨wt, hwa, htailTy, hbitTy⟩
    subst wa
    have hrecNe :
        __bv_bitblast_concat tail b ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hne
    have hrecTy := ih wt wb htailTy hbTy hrecNe
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hne]
    simpa [Nat.add_assoc] using bitCons_type hrecTy hbitTy
  case case3 b hbNe =>
    intro wa wb haTy hbTy
    change __smtx_typeof (SmtTerm.Binary 0 0) =
      SmtType.BitVec wa at haTy
    have hwa : wa = 0 := by
      simpa [__smtx_typeof, SmtEval.native_and, native_ite,
        SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
        native_mod_total, native_int_to_nat,
        SmtEval.native_int_to_nat] using
          (SmtType.BitVec.inj haTy).symm
    exact hwa

private theorem bitblast_concat_left_ne
    {a b : Term} (h : __bv_bitblast_concat a b ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  cases b <;> simp_all [__bv_bitblast_concat]

private theorem concat_bitvec_value_general
    (x : BitVec A) (y : BitVec B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (A : Int) (x.toNat : Int))
        (SmtValue.Binary (B : Int) (y.toNat : Int)) =
      SmtValue.Binary ((A + B : Nat) : Int)
        ((x ++ y).toNat : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hWidth : (A : Int) + (B : Int) = ((A + B : Nat) : Int) := by
    norm_cast
  rw [hWidth]
  rw [show (B : Int) = native_nat_to_int B by rfl,
    native_int_pow2_native_nat B]
  rw [show ((A + B : Nat) : Int) =
      native_nat_to_int (A + B) by rfl,
    native_int_pow2_native_nat (A + B)]
  have hFormula :
      (x.toNat : Int) * (2 ^ B : Nat) + (y.toNat : Int) =
        ((x ++ y).toNat : Int) := by
    norm_cast
    have hyLt : y.toNat < 2 ^ B := y.isLt
    have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hyLt x.toNat
    rw [BitVec.toNat_append, ← hShiftOr, Nat.shiftLeft_eq]
  rw [hFormula]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (by exact_mod_cast (x ++ y).isLt)]

private theorem toNat_append_concat
    (x : BitVec A) (y : BitVec B) (b : Bool) :
    ((x ++ y).concat b).toNat =
      (x ++ y.concat b).toNat := by
  have h := congrArg BitVec.toNat
    (BitVec.append_assoc (x₁ := x) (x₂ := y)
      (x₃ := BitVec.ofBool b))
  simpa [BitVec.concat, BitVec.toNat_cast] using h

private theorem bitblast_concat_eval
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (wa wb : Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec wb)
    (hne : __bv_bitblast_concat a b ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_concat a b)) =
      __smtx_model_eval_concat
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt a)) := by
  revert wa wb haTy hbTy hne
  fun_induction __bv_bitblast_concat a b <;> simp_all
  case case2 bit tail b hbNe ih =>
    intro wa wb haTy hbTy hne
    rcases bitCons_type_info haTy with
      ⟨wt, hwa, htailTy, hbitTy⟩
    subst wa
    have hrecNe :
        __bv_bitblast_concat tail b ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hne
    rcases eval_bitvec_of_type M hM tail wt htailTy with
      ⟨xt, htailEval⟩
    rcases eval_bitvec_of_type M hM b wb hbTy with
      ⟨xb, hbEval⟩
    rcases eval_bool_of_type M hM bit hbitTy with
      ⟨v, hbitEval⟩
    have hrecEval :
        __smtx_model_eval M
            (__eo_to_smt (__bv_bitblast_concat tail b)) =
          SmtValue.Binary ((wb + wt : Nat) : Int)
            ((xb ++ xt).toNat : Int) := by
      calc
        _ = __smtx_model_eval_concat
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt tail)) :=
            ih wt wb htailTy hbTy hrecNe
        _ = _ := by
          rw [hbEval, htailEval, concat_bitvec_value_general]
    have haEval := eval_bit_cons M bit tail v xt hbitEval htailEval
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hne]
    rw [eval_bit_cons M bit
      (__bv_bitblast_concat tail b) v (xb ++ xt)
      hbitEval hrecEval]
    rw [hbEval, haEval, concat_bitvec_value_general]
    congr 1
    norm_cast
    exact toNat_append_concat xb xt v
  case case3 b hbNe =>
    intro wa wb haTy hbTy
    rcases eval_bitvec_of_type M hM b wb hbTy with ⟨x, hx⟩
    rw [hx]
    change SmtValue.Binary (wb : Int) (x.toNat : Int) =
      __smtx_model_eval_concat
        (SmtValue.Binary (wb : Int) (x.toNat : Int))
        (SmtValue.Binary 0 0)
    simpa [BitVec.toNat_append] using
      (concat_bitvec_value_general x (0#0)).symm

private theorem mk_step_concat_type_eval
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (W : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec W)
    (hne : __bv_mk_bitblast_step_concat t ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__bv_mk_bitblast_step_concat t)) =
        SmtType.BitVec W ∧
      __smtx_model_eval M
          (__eo_to_smt (__bv_mk_bitblast_step_concat t)) =
        __smtx_model_eval M (__eo_to_smt t) := by
  revert W hTy hne
  fun_induction __bv_mk_bitblast_step_concat t <;> simp_all
  case case2 a1 a2 ih =>
    intro W hTy hne
    have hnn :
        term_has_non_none_type
          (SmtTerm.concat (__eo_to_smt a1) (__eo_to_smt a2)) := by
      unfold term_has_non_none_type
      simpa using hTy ▸ (by simp : SmtType.BitVec W ≠ SmtType.None)
    rcases bv_concat_args_of_non_none hnn with
      ⟨w1, w2, h1Ty, h2Ty⟩
    have hSourceTy :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.concat) a1) a2)) =
          SmtType.BitVec (w1 + w2) := by
      change __smtx_typeof
          (SmtTerm.concat (__eo_to_smt a1) (__eo_to_smt a2)) =
        SmtType.BitVec (w1 + w2)
      rw [typeof_concat_eq, h1Ty, h2Ty]
      simp only [__smtx_typeof_concat, SmtEval.native_zplus,
        native_nat_to_int, Smtm.native_nat_to_int,
        native_int_to_nat, SmtEval.native_int_to_nat]
      congr 1
    have hW : W = w1 + w2 := by
      -- `hTy` now carries the unfolded `__eo_to_smt` spine, so `rw [hSourceTy]`
      -- no longer matches; the two sides are still defeq, so compose directly
      exact (SmtType.BitVec.inj (hSourceTy.symm.trans hTy)).symm
    have hrecNe :
        __bv_mk_bitblast_step_concat a2 ≠ Term.Stuck := by
      exact bitblast_concat_left_ne hne
    rcases ih w2 h2Ty hrecNe with ⟨hrecTy, hrecEval⟩
    have houtTy :=
      bitblast_concat_type
        (__bv_mk_bitblast_step_concat a2) a1 w2 w1
        hrecTy h1Ty hne
    constructor
    · simpa [hW] using houtTy
    · calc
        _ = __smtx_model_eval_concat
              (__smtx_model_eval M (__eo_to_smt a1))
              (__smtx_model_eval M
                (__eo_to_smt (__bv_mk_bitblast_step_concat a2))) :=
            bitblast_concat_eval M hM
              (__bv_mk_bitblast_step_concat a2) a1 w2 w1
              hrecTy h1Ty hne
        _ = __smtx_model_eval_concat
              (__smtx_model_eval M (__eo_to_smt a1))
              (__smtx_model_eval M (__eo_to_smt a2)) := by
            rw [hrecEval]
        _ = _ := by
          symm
          apply smtx_eval_concat_term_eq

private theorem eval_step_concat
    (M : SmtModel) (hM : model_wf M)
    (a1 a2 : Term)
    (hne :
      __bv_bitblast_concat (__bv_mk_bitblast_step_concat a2) a1 ≠
        Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a1) a2))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_concat
            (__bv_mk_bitblast_step_concat a2) a1)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a1) a2)) := by
  change term_has_non_none_type
      (SmtTerm.concat (__eo_to_smt a1) (__eo_to_smt a2)) at hnn
  rcases bv_concat_args_of_non_none hnn with
    ⟨w1, w2, h1Ty, h2Ty⟩
  have hrecNe :
      __bv_mk_bitblast_step_concat a2 ≠ Term.Stuck :=
    bitblast_concat_left_ne hne
  rcases mk_step_concat_type_eval M hM a2 w2 h2Ty hrecNe with
    ⟨hrecTy, hrecEval⟩
  calc
    _ = __smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt a1))
          (__smtx_model_eval M
            (__eo_to_smt (__bv_mk_bitblast_step_concat a2))) :=
        bitblast_concat_eval M hM
          (__bv_mk_bitblast_step_concat a2) a1 w2 w1
          hrecTy h1Ty hne
    _ = __smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt a1))
          (__smtx_model_eval M (__eo_to_smt a2)) := by
        rw [hrecEval]
    _ = _ := by
      symm
      apply smtx_eval_concat_term_eq

private theorem bitblast_concat_syntax_left
    (a b : Term) (h : __bv_bitblast_concat a b ≠ Term.Stuck) :
    BitListSyntax a := by
  fun_induction __bv_bitblast_concat a b <;> simp_all
  case case2 bit tail b hbNe ih =>
    apply BitListSyntax.cons
    exact ih (eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h)
  case case3 =>
    exact BitListSyntax.nil

private theorem bitblast_concat_right_ne
    {a b : Term} (h : __bv_bitblast_concat a b ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> simp_all [__bv_bitblast_concat]

private theorem list_repeat_from_bools_context
    (bit n : Term)
    (h :
      __eo_list_repeat (Term.UOp UserOp._at_from_bools) bit n ≠
        Term.Stuck) :
    ∃ k : Nat, n = Term.Numeral (k : Int) ∧ bit ≠ Term.Stuck := by
  have hbit : bit ≠ Term.Stuck := by
    intro hb
    subst bit
    exact h (__eo_list_repeat.eq_2 _ _
      (by intro hh; cases hh))
  cases n with
  | Numeral i =>
    rw [__eo_list_repeat.eq_3 _ _ i
      (by intro hh; cases hh) hbit] at h
    by_cases hi : i < 0
    · simp [native_ite, native_zlt, hi] at h
    · refine ⟨i.toNat, ?_, hbit⟩
      congr 1
      exact (Int.toNat_of_nonneg (Int.le_of_not_gt hi)).symm
  | _ =>
    exfalso
    apply h
    exact __eo_list_repeat.eq_4 _ _ _
      (by intro hh; cases hh) hbit
      (by intro i hi; cases hi)

private theorem list_repeat_rec_from_bools_bit_ne
    {bit : Term} {n : Nat}
    (h :
      __eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit n ≠
        Term.Stuck) :
    bit ≠ Term.Stuck := by
  intro hb
  subst bit
  exact h (__eo_list_repeat_rec.eq_2 _ n
    (by intro hh; cases hh))

private theorem list_repeat_rec_from_bools_type_ne
    {bit : Term} {n : Nat}
    (h :
      __eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit n ≠
        Term.Stuck) :
    __eo_typeof bit ≠ Term.Stuck := by
  have hbit := list_repeat_rec_from_bools_bit_ne h
  induction n with
  | zero =>
    rw [__eo_list_repeat_rec.eq_4 _ _ 0
      (by intro hh; cases hh) hbit
      (by intro k hk; cases hk)] at h
    intro hty
    rw [hty] at h
    exact h rfl
  | succ n ih =>
    rw [__eo_list_repeat_rec.eq_3 _ _ n
      (by intro hh; cases hh) hbit] at h
    apply ih
    exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h

private theorem BitListEval.head {M : SmtModel}
    {t : Term} {b : Bool} {bs : List Bool}
    (h : BitListEval M t (b :: bs)) :
    __smtx_model_eval M (__eo_to_smt (__bv_bitblast_head t)) =
      SmtValue.Boolean b := by
  cases h
  assumption

private theorem BitListEval.eq_nil {M : SmtModel}
    {t : Term} (h : BitListEval M t []) :
    t = Term.Binary 0 0 := by
  cases h
  rfl

private theorem bitsValue_append (xs ys : List Bool) :
    bitsValue (xs ++ ys) =
      bitsValue xs + 2 ^ xs.length * bitsValue ys := by
  induction xs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    simp [bitsValue, ih, Nat.pow_succ, Nat.mul_add,
      Nat.mul_assoc, Nat.mul_comm]
    omega

private theorem bitsValue_take_drop
    (xs : List Bool) (k : Nat) (hk : k ≤ xs.length) :
    bitsValue xs =
      bitsValue (xs.take k) + 2 ^ k * bitsValue (xs.drop k) := by
  induction k generalizing xs with
  | zero => simp [bitsValue]
  | succ k ih =>
      cases xs with
      | nil => simp at hk
      | cons x xs =>
          have hk' : k ≤ xs.length := by simpa using hk
          simp only [List.take_succ_cons, List.drop_succ_cons, bitsValue,
            Nat.pow_succ]
          rw [ih xs hk']
          rw [Nat.mul_add]
          ac_rfl

private theorem bitsValue_take_mod
    (xs : List Bool) (k : Nat) (hk : k ≤ xs.length) :
    bitsValue (xs.take k) = bitsValue xs % 2 ^ k := by
  rw [bitsValue_take_drop xs k hk]
  rw [Nat.add_mul_mod_self_left]
  rw [Nat.mod_eq_of_lt]
  have hlen : (xs.take k).length = k := List.length_take_of_le hk
  simpa [hlen] using bitsValue_lt (xs.take k)

private theorem bitsValue_map_and (b : Bool) (xs : List Bool) :
    bitsValue (xs.map (b && ·)) = b.toNat * bitsValue xs := by
  induction xs with
  | nil => simp [bitsValue]
  | cons x xs ih =>
      cases b <;> cases x <;> simp_all [bitsValue]

private theorem mod_mul_replace (a p q x : Nat) :
    (a + p * (x % q)) % (p * q) =
      (a + p * x) % (p * q) := by
  have hx :
      a + p * x =
        (a + p * (x % q)) + (p * q) * (x / q) := by
    calc
      a + p * x =
          a + p * (x % q + q * (x / q)) := by
            exact congrArg (fun z => a + p * z)
              (Nat.mod_add_div x q).symm
      _ = (a + p * (x % q)) + (p * q) * (x / q) := by
            rw [Nat.mul_add]
            ac_rfl
  rw [hx, Nat.add_mul_mod_self_left]

private theorem add_mul_mod_right (a b x q : Nat) :
    (a + b * (x % q)) % q = (a + b * x) % q := by
  have hx :
      a + b * x =
        (a + b * (x % q)) + q * (b * (x / q)) := by
    calc
      a + b * x =
          a + b * (x % q + q * (x / q)) := by
            exact congrArg (fun z => a + b * z)
              (Nat.mod_add_div x q).symm
      _ = (a + b * (x % q)) + q * (b * (x / q)) := by
            rw [Nat.mul_add]
            ac_rfl
  rw [hx, Nat.add_mul_mod_self_left]

private theorem mod_add_replace_left (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  have ha :
      a + b = (a % m + b) + m * (a / m) := by
    calc
      a + b = (a % m + m * (a / m)) + b := by
        rw [Nat.mod_add_div]
      _ = (a % m + b) + m * (a / m) := by ac_rfl
  rw [ha, Nat.add_mul_mod_self_left]

private theorem shiftAddStepBits_value
    (b : Bool) (ys : List Bool) (k : Nat) (rs : List Bool)
    (hk : k ≤ rs.length)
    (hlen : rs.length ≤ k + ys.length) :
    bitsValue (shiftAddStepBits b ys k rs false) =
      (bitsValue rs + b.toNat * bitsValue ys * 2 ^ k) %
        2 ^ rs.length := by
  let n := rs.length - k
  have hW : rs.length = k + n := by
    simp [n, hk]
  have hnY : n ≤ ys.length := by
    simp [n]
    omega
  have htakeK : (rs.take k).length = k :=
    List.length_take_of_le hk
  have hdropK : (rs.drop k).length = n := by
    simp [n]
  have htakeN : (ys.take n).length = n :=
    List.length_take_of_le hnY
  have hmapN :
      ((ys.take n).map (b && ·)).length = n := by
    rw [List.length_map, htakeN]
  have hlenAdd :
      (rs.drop k).length =
        ((ys.take n).map (b && ·)).length := by
    rw [hdropK, hmapN]
  have houtLen :
      (shiftAddStepBits b ys k rs false).length = rs.length := by
    rw [shiftAddStepBits_eq b ys k rs false hk hlen]
    rw [List.length_append, htakeK,
      addBits_length hlenAdd, hdropK, hW]
  have houtLt := bitsValue_lt (shiftAddStepBits b ys k rs false)
  rw [houtLen] at houtLt
  rw [shiftAddStepBits_eq b ys k rs false hk hlen]
  rw [bitsValue_append, htakeK]
  rw [addBits_value_mod (carry := false) hlenAdd]
  rw [bitsValue_map_and]
  rw [bitsValue_take_mod ys n hnY]
  rw [hdropK]
  simp only [Bool.toNat_false, Nat.add_zero]
  rw [add_mul_mod_right]
  have hsmall :
      bitsValue (rs.take k) +
          2 ^ k *
            ((bitsValue (rs.drop k) + b.toNat * bitsValue ys) %
              2 ^ n) <
        2 ^ rs.length := by
    rw [shiftAddStepBits_eq b ys k rs false hk hlen,
      bitsValue_append, htakeK,
      addBits_value_mod (carry := false) hlenAdd,
      bitsValue_map_and, bitsValue_take_mod ys n hnY,
      hdropK] at houtLt
    simp only [Bool.toNat_false, Nat.add_zero] at houtLt
    rw [add_mul_mod_right] at houtLt
    exact houtLt
  rw [← Nat.mod_eq_of_lt hsmall]
  rw [hW, Nat.pow_add]
  rw [mod_mul_replace]
  congr 1
  rw [bitsValue_take_drop rs k hk, Nat.mul_add]
  ac_rfl

private theorem shiftAddStepBits_length
    (b : Bool) (ys : List Bool) (k : Nat) (rs : List Bool)
    (hk : k ≤ rs.length)
    (hlen : rs.length ≤ k + ys.length) :
    (shiftAddStepBits b ys k rs false).length = rs.length := by
  have hEq := shiftAddStepBits_eq b ys k rs false hk hlen
  have hdropLen :
      (rs.drop k).length =
        ((ys.take (rs.length - k)).map (b && ·)).length := by
    simp only [List.length_drop, List.length_map, List.length_take]
    omega
  rw [hEq, List.length_append, addBits_length hdropLen]
  simp [List.length_take, List.length_drop, hk]

private theorem shiftAddRecBits_value :
    ∀ (ys : List Bool) (k : Nat) (xs rs : List Bool),
      ys.length = rs.length →
      k + xs.length ≤ rs.length →
      bitsValue (shiftAddRecBits ys k xs rs) =
        (bitsValue rs +
            bitsValue ys * bitsValue xs * 2 ^ k) %
          2 ^ rs.length := by
  intro ys k xs
  induction xs generalizing k with
  | nil =>
      intro rs hlen hbound
      rw [shiftAddRecBits]
      simp only [bitsValue, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (bitsValue_lt rs)).symm
  | cons b bs ih =>
      intro rs hlen hbound
      have hk : k ≤ rs.length := by
        simp only [List.length_cons] at hbound
        omega
      have hstepBound : rs.length ≤ k + ys.length := by omega
      let next := shiftAddStepBits b ys k rs false
      have hnextLen : next.length = rs.length :=
        shiftAddStepBits_length b ys k rs hk hstepBound
      rw [shiftAddRecBits]
      rw [ih (k + 1) next
        (by simpa [hnextLen] using hlen)
        (by
          simp only [List.length_cons] at hbound
          simp [hnextLen]
          omega)]
      rw [shiftAddStepBits_value b ys k rs hk hstepBound]
      rw [hnextLen]
      rw [mod_add_replace_left]
      congr 1
      simp only [bitsValue, Nat.pow_succ]
      rw [Nat.mul_add]
      simp only [Nat.add_mul]
      ac_rfl

private theorem shiftAddRecBits_length :
    ∀ (ys : List Bool) (k : Nat) (xs rs : List Bool),
      ys.length = rs.length →
      k + xs.length ≤ rs.length →
      (shiftAddRecBits ys k xs rs).length = rs.length := by
  intro ys k xs
  induction xs generalizing k with
  | nil =>
      intro rs hlen hbound
      rfl
  | cons b bs ih =>
      intro rs hlen hbound
      have hk : k ≤ rs.length := by
        simp only [List.length_cons] at hbound
        omega
      have hstepBound : rs.length ≤ k + ys.length := by omega
      have hnextLen :=
        shiftAddStepBits_length b ys k rs hk hstepBound
      rw [shiftAddRecBits]
      rw [ih (k + 1) (shiftAddStepBits b ys k rs false)
        (by omega)
        (by
          simp only [List.length_cons] at hbound
          omega)]
      exact hnextLen

private theorem zipWith_replicate_and
    (b : Bool) (ys : List Bool) :
    List.zipWith (· && ·) (List.replicate ys.length b) ys =
      ys.map (b && ·) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      simp [List.replicate_succ, ih]

private theorem shift_add_multiplier_eval_bits
    (M : SmtModel) (hM : model_wf M)
    (ac a2 : Term) (W : Nat) {acBits ys : List Bool}
    (hExpanded : __bv_shift_add_multiplier a2 ac ≠ Term.Stuck)
    (hac : BitListEval M ac acBits)
    (ha2 : BitListEval M a2 ys)
    (hAcLen : acBits.length = W)
    (hYLen : ys.length = W) :
    ∃ out,
      BitListEval M (__bv_shift_add_multiplier a2 ac) out ∧
        out.length = W ∧
          __smtx_model_eval M
              (__eo_to_smt (__bv_shift_add_multiplier a2 ac)) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvmul) ac) a2)) := by
  rcases shift_add_multiplier_shape a2 ac hExpanded with
    ⟨bit, tail, rfl⟩
  have hacParts :
      ∃ b xs,
        acBits = b :: xs ∧
          __smtx_model_eval M (__eo_to_smt bit) =
            SmtValue.Boolean b ∧
          BitListEval M tail xs := by
    cases hac
    exact ⟨_, _, rfl, by assumption, by assumption⟩
  rcases hacParts with ⟨b, xs, rfl, hb, htail⟩
  have ha2Ne : a2 ≠ Term.Stuck := ha2.ne_stuck
  have hMulEq :=
    __bv_shift_add_multiplier.eq_2 a2 bit tail ha2Ne
  have hrecNe :
      __bv_shift_add_multiplier_rec tail a2 (Term.Numeral 1)
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
              (__bv_bitwidth (__eo_typeof a2))) a2) ≠
        Term.Stuck := by
    rw [← hMulEq]
    exact hExpanded
  have hinitNe :=
    shift_add_rec_res_ne hrecNe
  have hsame :=
    bitblast_apply_binary_same_length _ _ _ hinitNe
  have hrepeatNe :
      __eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
          (__bv_bitwidth (__eo_typeof a2)) ≠
        Term.Stuck :=
    hsame.syntax_left.ne_stuck
  rcases list_repeat_from_bools_context bit
      (__bv_bitwidth (__eo_typeof a2)) hrepeatNe with
    ⟨K, hWidth, hbitNe⟩
  have hrepeatRecNe :
      __eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit K ≠
        Term.Stuck := by
    have h := hrepeatNe
    rw [hWidth] at h
    rw [__eo_list_repeat.eq_3 _ _ (K : Int)
      (by intro hh; cases hh) hbitNe] at h
    rw [show native_zlt (K : Int) 0 = false by
      simp [native_zlt]] at h
    simpa [native_ite, native_int_to_nat, native_nat_to_int] using h
  have hbitTyNe : __eo_typeof bit ≠ Term.Stuck :=
    list_repeat_rec_from_bools_type_ne hrepeatRecNe
  have hrepK :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
          (__bv_bitwidth (__eo_typeof a2)))
        (List.replicate K b) := by
    rw [hWidth]
    simpa using
      (list_repeat_from_bools (M := M) (bit := bit) (b := b)
        hb hbitTyNe K)
  have hKW : K = W := by
    have hlen := hsame.eval_length hrepK ha2
    simp only [List.length_replicate] at hlen
    omega
  subst K
  have hrep :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
          (__bv_bitwidth (__eo_typeof a2)))
        (List.replicate W b) := by
    rw [hWidth]
    simpa [native_nat_to_int] using
      (list_repeat_from_bools (M := M) (bit := bit) (b := b)
        hb hbitTyNe W)
  have hrepLen : (List.replicate W b).length = ys.length := by
    simp [hYLen]
  let initBits :=
    List.zipWith (· && ·) (List.replicate W b) ys
  have hinit :
      BitListEval M
        (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
          (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
            (__bv_bitwidth (__eo_typeof a2))) a2)
        initBits := by
    simpa [initBits] using hrep.apply_and ha2 hrepLen
  have hinitLen : initBits.length = W := by
    simp [initBits, hYLen]
  have hrec :=
    shift_add_rec_eval 1 htail ha2 hinit
      (by simp [hYLen, hinitLen])
      (by
        simp only [List.length_cons] at hAcLen
        omega)
  have houtLen :=
    shiftAddRecBits_length ys 1 xs initBits
      (by simp [hYLen, hinitLen])
      (by
        simp only [List.length_cons] at hAcLen
        omega)
  have hinitVal :
      bitsValue initBits = b.toNat * bitsValue ys := by
    rw [show initBits = ys.map (b && ·) by
      simpa [initBits, hYLen] using zipWith_replicate_and b ys]
    exact bitsValue_map_and b ys
  have houtVal :=
    shiftAddRecBits_value ys 1 xs initBits
      (by simp [hYLen, hinitLen])
      (by
        simp only [List.length_cons] at hAcLen
        omega)
  have hrecEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_shift_add_multiplier_rec tail a2
              (Term.Numeral 1)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
                (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
                  (__bv_bitwidth (__eo_typeof a2))) a2))) =
        SmtValue.Binary
          ((shiftAddRecBits ys 1 xs initBits).length : Int)
          (bitsValue (shiftAddRecBits ys 1 xs initBits) : Int) := by
    simpa using hrec.eval
  have hout :
      BitListEval M
        (__bv_shift_add_multiplier a2
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail))
        (shiftAddRecBits ys 1 xs initBits) := by
    rw [hMulEq]
    simpa using hrec
  refine ⟨shiftAddRecBits ys 1 xs initBits, hout, ?_, ?_⟩
  · rw [houtLen, hinitLen]
  · rw [hMulEq, hrecEval]
    change
      SmtValue.Binary
          ((shiftAddRecBits ys 1 xs initBits).length : Int)
          (bitsValue (shiftAddRecBits ys 1 xs initBits) : Int) =
        __smtx_model_eval_bvmul
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)))
          (__smtx_model_eval M (__eo_to_smt a2))
    rw [(BitListEval.cons bit tail b xs hb htail).eval, ha2.eval,
      houtLen, hYLen, hAcLen, houtVal, hinitVal]
    simp only [__smtx_model_eval_bvmul, native_zmult]
    rw [native_int_pow2_nat]
    congr 1
    norm_cast
    simp only [bitsValue, Nat.pow_one]
    rw [hinitLen]
    unfold native_mod_total
    simp only []
    congr 1
    rw [Nat.add_mul]
    ac_rfl

private theorem eval_shift_add_multiplier
    (M : SmtModel) (hM : model_wf M)
    (ac a2 : Term) (W : Nat)
    (hExpanded : __bv_shift_add_multiplier a2 ac ≠ Term.Stuck)
    (hacTy : __smtx_typeof (__eo_to_smt ac) = SmtType.BitVec W)
    (ha2Ty : __smtx_typeof (__eo_to_smt a2) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_shift_add_multiplier a2 ac)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) ac) a2)) := by
  rcases shift_add_multiplier_shape a2 ac hExpanded with
    ⟨bit, tail, rfl⟩
  have ha2Trans : RuleProofs.eo_has_smt_translation a2 := by
    unfold RuleProofs.eo_has_smt_translation
    rw [ha2Ty]
    intro h
    cases h
  have ha2Ne : a2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a2 ha2Trans
  have hMulEq :=
    __bv_shift_add_multiplier.eq_2 a2 bit tail ha2Ne
  have hrecNe :
      __bv_shift_add_multiplier_rec tail a2 (Term.Numeral 1)
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
              (__bv_bitwidth (__eo_typeof a2))) a2) ≠
        Term.Stuck := by
    rw [← hMulEq]
    exact hExpanded
  have hinitNe := shift_add_rec_res_ne hrecNe
  have hsame :=
    bitblast_apply_binary_same_length _ _ _ hinitNe
  have htailSyntax :=
    shift_add_rec_first_syntax tail a2 (Term.Numeral 1)
      (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
          (__bv_bitwidth (__eo_typeof a2))) a2) hrecNe
  have hacSyntax : BitListSyntax
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail) :=
    BitListSyntax.cons bit tail htailSyntax
  have hacNN : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)) := by
    unfold term_has_non_none_type
    rw [hacTy]
    simp
  have ha2NN : term_has_non_none_type (__eo_to_smt a2) := by
    unfold term_has_non_none_type
    rw [ha2Ty]
    simp
  rcases hacSyntax.eval hM hacNN with ⟨acBits, hac⟩
  rcases hsame.syntax_right.eval hM ha2NN with ⟨ys, ha2⟩
  have hAcLen :=
    bitListEval_length_eq_smt_type M hM _ acBits W hac hacTy
  have hYLen :=
    bitListEval_length_eq_smt_type M hM a2 ys W ha2 ha2Ty
  rcases shift_add_multiplier_eval_bits M hM
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
      a2 W hExpanded hac ha2 hAcLen hYLen with
    ⟨out, hout, houtLen, heval⟩
  exact heval

private theorem mul_acc_ne {rest acc : Term}
    (h : __bv_mk_bitblast_step_mul rest acc ≠ Term.Stuck) :
    acc ≠ Term.Stuck := by
  intro ha
  subst acc
  apply h
  cases rest <;> rfl

private theorem bvmul_args_of_bitvec_type
    (x y : Term) (W : Nat)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y)) =
        SmtType.BitVec W) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
  have hTy' :
      __smtx_typeof
          (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.BitVec W := by
    have hsimpa := hTy
    try simp at hsimpa ⊢
    exact hsimpa
  have hNN : term_has_non_none_type
      (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvmul)
      (show
        __smtx_typeof (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt y)) by
        rw [__smtx_typeof.eq_def] <;> simp only) hNN with
    ⟨W', hxTy, hyTy⟩
  have hW : W' = W := by
    have hResult : SmtType.BitVec W' = SmtType.BitVec W := by
      rw [show
        __smtx_typeof (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt y)) by
        rw [__smtx_typeof.eq_def] <;> simp only] at hTy'
      simpa [__smtx_typeof_bv_op_2, hxTy, hyTy, native_ite,
        native_nateq, Smtm.native_nateq] using hTy'
    cases hResult
    rfl
  subst W'
  exact ⟨hxTy, hyTy⟩

private theorem shift_add_multiplier_right_syntax
    (a2 ac : Term)
    (h : __bv_shift_add_multiplier a2 ac ≠ Term.Stuck) :
    BitListSyntax a2 := by
  rcases shift_add_multiplier_shape a2 ac h with ⟨bit, tail, rfl⟩
  have ha2Ne : a2 ≠ Term.Stuck := by
    intro ha2
    subst a2
    exact h rfl
  have hMulEq :=
    __bv_shift_add_multiplier.eq_2 a2 bit tail ha2Ne
  have hrecNe :
      __bv_shift_add_multiplier_rec tail a2 (Term.Numeral 1)
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
              (__bv_bitwidth (__eo_typeof a2))) a2) ≠
        Term.Stuck := by
    rw [← hMulEq]
    exact h
  exact
    (bitblast_apply_binary_same_length _ _ _
      (shift_add_rec_res_ne hrecNe)).syntax_right

private theorem shift_add_multiplier_left_syntax
    (a2 ac : Term)
    (h : __bv_shift_add_multiplier a2 ac ≠ Term.Stuck) :
    BitListSyntax ac := by
  rcases shift_add_multiplier_shape a2 ac h with ⟨bit, tail, rfl⟩
  have ha2Ne : a2 ≠ Term.Stuck := by
    intro ha2
    subst a2
    exact h rfl
  have hMulEq :=
    __bv_shift_add_multiplier.eq_2 a2 bit tail ha2Ne
  have hrecNe :
      __bv_shift_add_multiplier_rec tail a2 (Term.Numeral 1)
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
              (__bv_bitwidth (__eo_typeof a2))) a2) ≠
        Term.Stuck := by
    rw [← hMulEq]
    exact h
  exact BitListSyntax.cons bit tail
    (shift_add_rec_first_syntax tail a2 (Term.Numeral 1)
      (__bv_bitblast_apply_binary (Term.UOp UserOp.and)
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
          (__bv_bitwidth (__eo_typeof a2))) a2) hrecNe)

private theorem bvmul_assoc_typed
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (W : Nat)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvmul)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvmul) x) y))
            z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvmul) x)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul) y) z))) := by
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt x) W hxTy with ⟨nx, hx, _⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt y) W hyTy with ⟨ny, hy, _⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt z) W hzTy with ⟨nz, hz, _⟩
  change
    __smtx_model_eval_bvmul
        (__smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval M (__eo_to_smt z)) =
      __smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt z)))
  rw [hx, hy, hz]
  simp only [__smtx_model_eval_bvmul, native_zmult]
  congr 1
  simp only [native_mod_total]
  have emodLeft (a b m : Int) :
      ((a % m) * b) % m = (a * b) % m := by
    rw [Int.mul_emod, Int.emod_emod]
    exact (Int.mul_emod a b m).symm
  have emodRight (a b m : Int) :
      (a * (b % m)) % m = (a * b) % m := by
    rw [Int.mul_comm a, Int.mul_comm a]
    exact emodLeft b a m
  calc
    (((nx * ny) % native_int_pow2 (native_nat_to_int W)) * nz) %
          native_int_pow2 (native_nat_to_int W) =
        ((nx * ny) * nz) %
          native_int_pow2 (native_nat_to_int W) :=
      emodLeft _ _ _
    _ = (nx * (ny * nz)) %
          native_int_pow2 (native_nat_to_int W) := by
      rw [Int.mul_assoc]
    _ = (nx *
          ((ny * nz) % native_int_pow2 (native_nat_to_int W))) %
          native_int_pow2 (native_nat_to_int W) :=
      (emodRight _ _ _).symm

private theorem bvmul_assoc_values
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (W : Nat) (xs ys : List Bool)
    (hx : BitListEval M x xs)
    (hy : BitListEval M y ys)
    (hxW : xs.length = W) (hyW : ys.length = W)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvmul)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvmul) x) y))
            z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvmul) x)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul) y) z))) := by
  let xc := Term.Binary (W : Int) (bitsValue xs : Int)
  let yc := Term.Binary (W : Int) (bitsValue ys : Int)
  have hxcTy : __smtx_typeof (__eo_to_smt xc) = SmtType.BitVec W := by
    simpa [xc, hxW] using add_smt_typeof_bitsValue xs
  have hycTy : __smtx_typeof (__eo_to_smt yc) = SmtType.BitVec W := by
    simpa [yc, hyW] using add_smt_typeof_bitsValue ys
  have hassoc := bvmul_assoc_typed M hM xc yc z W hxcTy hycTy hzTy
  change
    __smtx_model_eval_bvmul
        (__smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval M (__eo_to_smt z)) =
      __smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval M (__eo_to_smt z)))
  rw [hx.eval, hy.eval, hxW, hyW]
  have hsimpa := hassoc
  try simp [xc, yc] at hsimpa ⊢
  exact hsimpa

private theorem bvmul_comm_values
    (M : SmtModel) (x y : Term) (xs ys : List Bool)
    (hx : BitListEval M x xs)
    (hy : BitListEval M y ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) := by
  change
    __smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) =
      __smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt x))
  rw [hx.eval, hy.eval, hlen]
  simp [__smtx_model_eval_bvmul, native_zmult, Int.mul_comm]

private theorem to_z_one_payload
    (M : SmtModel) (t : Term) (W : Nat) (n : Int)
    (hone : __eo_to_z t = Term.Numeral 1)
    (heval :
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int W) n) :
    n = 1 := by
  cases t <;> simp [__eo_to_z, native_ite] at hone
  case Numeral z =>
    rw [show __eo_to_smt (Term.Numeral z) = SmtTerm.Numeral z by rfl]
      at heval
    rw [__smtx_model_eval] at heval
    cases heval
  case Rational q =>
    rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
      at heval
    rw [__smtx_model_eval] at heval
    cases heval
  case String s =>
    rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
      at heval
    rw [__smtx_model_eval] at heval
    cases heval
  case Binary w z =>
    rw [show __eo_to_smt (Term.Binary w z) = SmtTerm.Binary w z by rfl]
      at heval
    rw [__smtx_model_eval] at heval
    injection heval with _ hn
    subst n
    exact hone

private theorem eval_bvmul_right_to_z_one
    (M : SmtModel) (hM : model_wf M)
    (x one : Term) (W : Nat)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W)
    (honeTy : __smtx_typeof (__eo_to_smt one) = SmtType.BitVec W)
    (hone : __eo_to_z one = Term.Numeral 1) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) one)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt x) W hxTy with ⟨nx, hx, hxCanon⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt one) W honeTy with ⟨no, ho, _⟩
  have hno := to_z_one_payload M one W no hone ho
  subst no
  have hmod :
      native_mod_total nx (native_int_pow2 (native_nat_to_int W)) = nx := by
    have hcanon :
        nx =
          native_mod_total nx
            (native_int_pow2 (native_nat_to_int W)) := by
      simpa [native_zeq] using hxCanon
    exact hcanon.symm
  change
    __smtx_model_eval_bvmul
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt one)) =
      __smtx_model_eval M (__eo_to_smt x)
  rw [hx, ho]
  simp [__smtx_model_eval_bvmul, native_zmult, hmod]

private def shlStepBits
    (current original : List Bool) (k : Nat) (select : Bool) :
    List Bool :=
  if select then
    List.replicate (min k current.length) false ++
      original.take (current.length - k)
  else current

private theorem eval_plain_ite_bool {M : SmtModel}
    {c x y : Term} {cb xb yb : Bool}
    (hc :
      __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean cb)
    (hx :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy :
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) =
      SmtValue.Boolean (if cb then xb else yb) := by
  change
    __smtx_model_eval_ite
        (__smtx_model_eval M (__eo_to_smt c))
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) =
      SmtValue.Boolean (if cb then xb else yb)
  rw [hc, hx, hy]
  cases cb <;> rfl

private theorem shl_rec_step_eval {M : SmtModel}
    {a original bit : Term} {current source : List Bool} {b : Bool}
    (ha : BitListEval M a current)
    (horiginal : BitListEval M original source)
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) = SmtValue.Boolean b)
    (k : Nat)
    (hk : k ≤ current.length)
    (hlen : current.length ≤ source.length) :
    BitListEval M
      (__bv_mk_bitblast_step_shl_rec_step a original
        (Term.Numeral (k : Int)) bit)
      (shlStepBits current source k b) := by
  induction ha generalizing original source k with
  | nil =>
      rw [__bv_mk_bitblast_step_shl_rec_step.eq_4 original
        (Term.Numeral (k : Int)) bit horiginal.ne_stuck
        (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hb)]
      simpa [shlStepBits] using (BitListEval.nil (M := M))
  | cons x xtail xb xs hx hxtail ih =>
      cases k with
      | zero =>
          cases horiginal with
          | nil => simp at hlen
          | cons y ytail yb ys hy hytail =>
              have htailLen : xs.length ≤ ys.length := by
                simpa using hlen
              have hhead := eval_plain_ite_bool hb hy hx
              have htail := ih hytail 0 (by simp) htailLen
              have htail0 :
                  BitListEval M
                    (__bv_mk_bitblast_step_shl_rec_step xtail ytail
                      (Term.Numeral 0) bit)
                    (shlStepBits xs ys 0 b) := by
                simpa using htail
              have hout :
                  BitListEval M
                    (__bv_mk_bitblast_step_shl_rec_step
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp._at_from_bools) x)
                        xtail)
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp._at_from_bools) y)
                        ytail)
                      (Term.Numeral 0) bit)
                    (shlStepBits (xb :: xs) (yb :: ys) 0 b) := by
                rw [__bv_mk_bitblast_step_shl_rec_step.eq_5 bit
                  x xtail y ytail (term_ne_stuck_of_eval_boolean hb)]
                rw [mk_apply_eq (by intro h; cases h) htail0.ne_stuck]
                cases b <;>
                  simpa [shlStepBits] using
                    BitListEval.cons _ _ _ _ hhead htail0
              simpa using hout
      | succ k =>
          have hk' : k ≤ xs.length := by
            simpa using hk
          have htailLen : xs.length ≤ source.length := by
            simp only [List.length_cons] at hlen
            omega
          have hfalse :
              __smtx_model_eval M
                  (__eo_to_smt (Term.Boolean false)) =
                SmtValue.Boolean false := rfl
          have hhead := eval_plain_ite_bool hb hfalse hx
          have htail := ih horiginal k hk' htailLen
          rw [__bv_mk_bitblast_step_shl_rec_step.eq_6 original
            (Term.Numeral ((k + 1 : Nat) : Int)) bit x xtail
            horiginal.ne_stuck (by intro h; cases h)
            (by
              intro y ytail _ hi
              have hpos : (0 : Int) < (k : Int) + 1 :=
                Int.add_pos_of_nonneg_of_pos (Int.natCast_nonneg k)
                  (by decide)
              injection hi with hi'
              exact (Int.ne_of_gt hpos) hi')
            (term_ne_stuck_of_eval_boolean hb)]
          simp only [__eo_add, native_zplus]
          rw [show (↑(k + 1) : Int) + -1 = (k : Int) by omega]
          rw [mk_apply_eq (by intro h; cases h) htail.ne_stuck]
          cases b <;>
            simpa [shlStepBits, List.replicate_succ] using
              BitListEval.cons _ _ _ _ hhead htail

private def shrMergeBits
    (current source : List Bool) (select sign : Bool) : List Bool :=
  if select then
    source ++ List.replicate (current.length - source.length) sign
  else current

private def shrStepBits
    (current source : List Bool) (k : Nat)
    (select sign : Bool) : List Bool :=
  shrMergeBits current (source.drop k) select sign

private theorem eval_plain_not_bool {M : SmtModel}
    {b : Term} {v : Bool}
    (hb :
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean v) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) b)) =
      SmtValue.Boolean (!v) := by
  change
    __smtx_model_eval_not
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean (!v)
  rw [hb]
  cases v <;> rfl

private theorem shr_rec_step_zero_eval {M : SmtModel}
    {a source bit sign : Term} {current shifted : List Bool}
    {b sb : Bool}
    (ha : BitListEval M a current)
    (hsource : BitListEval M source shifted)
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) = SmtValue.Boolean b)
    (hsign :
      __smtx_model_eval M (__eo_to_smt sign) = SmtValue.Boolean sb)
    (hlen : shifted.length ≤ current.length) :
    BitListEval M
      (__bv_mk_bitblast_step_shr_rec_step a source
        (Term.Numeral 0) bit sign)
      (shrMergeBits current shifted b sb) := by
  induction ha generalizing source shifted with
  | nil =>
      have hnil : shifted = [] := by
        cases shifted <;> simp_all
      subst shifted
      have hsourceEq := hsource.eq_nil
      subst source
      rw [__bv_mk_bitblast_step_shr_rec_step.eq_6
        (Term.Binary 0 0) (Term.Numeral 0) bit sign
        (by intro h; cases h) (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hb)
        (term_ne_stuck_of_eval_boolean hsign)]
      simpa [shrMergeBits] using (BitListEval.nil (M := M))
  | cons x xtail xb xs hx hxtail ih =>
      cases hsource with
      | nil =>
          have hhead := eval_plain_ite_bool hb hsign hx
          have htail := ih (BitListEval.nil (M := M)) (by simp)
          have htail0 :
              BitListEval M
                (__bv_mk_bitblast_step_shr_rec_step xtail
                  (Term.Binary 0 0) (Term.Numeral 0) bit sign)
                (shrMergeBits xs [] b sb) := by
            simpa using htail
          rw [__bv_mk_bitblast_step_shr_rec_step.eq_8 bit sign
            x xtail (term_ne_stuck_of_eval_boolean hb)
            (term_ne_stuck_of_eval_boolean hsign)]
          rw [mk_apply_eq (by intro h; cases h) htail0.ne_stuck]
          cases b <;>
            simpa [shrMergeBits, List.replicate_succ] using
              BitListEval.cons _ _ _ _ hhead htail0
      | cons y ytail yb ys hy hytail =>
          have htailLen : ys.length ≤ xs.length := by
            simpa using hlen
          have hnot := eval_plain_not_bool hb
          have hhead := eval_plain_ite_bool hnot hx hy
          have htail := ih hytail htailLen
          have htail0 :
              BitListEval M
                (__bv_mk_bitblast_step_shr_rec_step xtail ytail
                  (Term.Numeral 0) bit sign)
                (shrMergeBits xs ys b sb) := by
            simpa using htail
          rw [__bv_mk_bitblast_step_shr_rec_step.eq_7 bit sign
            x xtail y ytail
            (term_ne_stuck_of_eval_boolean hb)
            (term_ne_stuck_of_eval_boolean hsign)]
          rw [mk_apply_eq (by intro h; cases h) htail0.ne_stuck]
          cases b <;>
            simpa [shrMergeBits] using
              BitListEval.cons _ _ _ _ hhead htail0

private theorem shr_rec_step_eval {M : SmtModel}
    {a source bit sign : Term} {current shifted : List Bool}
    {b sb : Bool}
    (ha : BitListEval M a current)
    (hsource : BitListEval M source shifted)
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) = SmtValue.Boolean b)
    (hsign :
      __smtx_model_eval M (__eo_to_smt sign) = SmtValue.Boolean sb)
    (k : Nat)
    (hk : k ≤ shifted.length)
    (hlen : shifted.length ≤ current.length) :
    BitListEval M
      (__bv_mk_bitblast_step_shr_rec_step a source
        (Term.Numeral (k : Int)) bit sign)
      (shrStepBits current shifted k b sb) := by
  induction k generalizing source shifted with
  | zero =>
      simpa [shrStepBits] using
        shr_rec_step_zero_eval ha hsource hb hsign (by omega)
  | succ k ih =>
      cases ha with
      | nil =>
          have hshifted : shifted = [] := by
            cases shifted <;> simp_all
          subst shifted
          simp at hk
      | cons x xtail xb xs hx hxtail =>
          cases hsource with
          | nil => simp at hk
          | cons y ytail yb ys hy hytail =>
              have hk' : k ≤ ys.length := by simpa using hk
              have hlen' : ys.length ≤ (xb :: xs).length := by
                simp only [List.length_cons] at hlen ⊢
                omega
              have hrec := ih hytail hk' hlen'
              rw [__bv_mk_bitblast_step_shr_rec_step.eq_9
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)
                (Term.Numeral ((k + 1 : Nat) : Int)) bit sign y ytail
                (by intro h; cases h)
                (by intro h; cases h)
                (by intro h; cases h)
                (by
                  intro z ztail _ hi
                  have hpos : (0 : Int) < (k : Int) + 1 :=
                    Int.add_pos_of_nonneg_of_pos (Int.natCast_nonneg k)
                      (by decide)
                  injection hi with hi'
                  exact (Int.ne_of_gt hpos) hi')
                (term_ne_stuck_of_eval_boolean hb)
                (term_ne_stuck_of_eval_boolean hsign)]
              simp only [__eo_add, native_zplus]
              rw [show (↑(k + 1) : Int) + -1 = (k : Int) by omega]
              simpa [shrStepBits] using hrec

private def shlBarrelBits :
    List Bool → Nat → List Bool → Nat → List Bool
  | current, _, _, 0 => current
  | current, _, [], _ + 1 => current
  | current, s, b :: bs, n + 1 =>
      shlBarrelBits
        (shlStepBits current current (2 ^ s) b) (s + 1) bs n

private def shrBarrelBits :
    List Bool → Nat → List Bool → Nat → Bool → List Bool
  | current, _, _, 0, _ => current
  | current, _, [], _ + 1, _ => current
  | current, s, b :: bs, n + 1, sign =>
      shrBarrelBits
        (shrStepBits current current (2 ^ s) b sign)
        (s + 1) bs n sign

private theorem shlStepBits_length
    (current original : List Bool) (k : Nat) (b : Bool)
    (hk : k ≤ current.length)
    (hlen : original.length = current.length) :
    (shlStepBits current original k b).length = current.length := by
  cases b with
  | false => simp [shlStepBits]
  | true =>
      simp only [shlStepBits, ↓reduceIte, List.length_append,
        List.length_replicate, List.length_take]
      rw [Nat.min_eq_left hk]
      rw [Nat.min_eq_left
        (by omega : current.length - k ≤ original.length)]
      omega

private theorem shrMergeBits_length
    (current source : List Bool) (b sign : Bool)
    (hlen : source.length ≤ current.length) :
    (shrMergeBits current source b sign).length = current.length := by
  cases b <;> simp [shrMergeBits] <;> omega

private theorem shrStepBits_length
    (current source : List Bool) (k : Nat) (b sign : Bool)
    (hlen : source.length ≤ current.length) :
    (shrStepBits current source k b sign).length = current.length := by
  apply shrMergeBits_length
  simp only [List.length_drop]
  omega

private theorem shlBarrelBits_length
    (current controls : List Bool) (s n W : Nat)
    (hcurrent : current.length = W)
    (hn : n ≤ controls.length)
    (hpow : ∀ j < n, 2 ^ (s + j) ≤ W) :
    (shlBarrelBits current s controls n).length = W := by
  induction n generalizing current controls s with
  | zero => simpa [shlBarrelBits]
  | succ n ih =>
      cases controls with
      | nil => simp at hn
      | cons b bs =>
          have hk : 2 ^ s ≤ current.length := by
            rw [hcurrent]
            simpa using hpow 0 (by omega)
          have hstep :
              (shlStepBits current current (2 ^ s) b).length = W := by
            rw [shlStepBits_length current current (2 ^ s) b hk rfl,
              hcurrent]
          simp only [shlBarrelBits]
          apply ih
            (shlStepBits current current (2 ^ s) b) bs (s + 1)
            hstep (by simpa using hn)
          intro j hj
          simpa [Nat.add_assoc, Nat.add_comm 1 j,
            Nat.add_left_comm 1 j] using hpow (j + 1) (by omega)

private theorem shrBarrelBits_length
    (current controls : List Bool) (s n W : Nat) (sign : Bool)
    (hcurrent : current.length = W)
    (hn : n ≤ controls.length) :
    (shrBarrelBits current s controls n sign).length = W := by
  induction n generalizing current controls s with
  | zero => simpa [shrBarrelBits]
  | succ n ih =>
      cases controls with
      | nil => simp at hn
      | cons b bs =>
          have hstep :
              (shrStepBits current current (2 ^ s) b sign).length = W := by
            rw [shrStepBits_length current current (2 ^ s) b sign
              (by omega), hcurrent]
          simp only [shrBarrelBits]
          exact ih
            (shrStepBits current current (2 ^ s) b sign) bs (s + 1)
            hstep (by simpa using hn)

private theorem shl_rec_eval {M : SmtModel}
    {currentTerm controlTerm : Term}
    {current controls : List Bool}
    (hcurrent : BitListEval M currentTerm current)
    (hcontrols : BitListEval M controlTerm controls)
    (s n W : Nat)
    (hcurrentLen : current.length = W)
    (hn : n ≤ controls.length)
    (hpow : ∀ j < n, 2 ^ (s + j) ≤ W) :
    BitListEval M
      (__bv_mk_bitblast_step_shl_rec currentTerm controlTerm
        (Term.Numeral (s : Int)) (Term.Numeral ((s + n : Nat) : Int)))
      (shlBarrelBits current s controls n) := by
  induction n generalizing currentTerm controlTerm current controls s with
  | zero =>
      simp only [Nat.add_zero, shlBarrelBits]
      rw [__bv_mk_bitblast_step_shl_rec.eq_5 currentTerm controlTerm
        (Term.Numeral (s : Int)) (Term.Numeral (s : Int))
        hcurrent.ne_stuck hcontrols.ne_stuck
        (by intro h; cases h) (by intro h; cases h)]
      rw [show
        __eo_eq (Term.Numeral (s : Int)) (Term.Numeral (s : Int)) =
          Term.Boolean true by
        simp [__eo_eq, native_teq]]
      simpa [__eo_ite, native_teq, native_ite] using hcurrent
  | succ n ih =>
      cases hcontrols with
      | nil => simp at hn
      | cons bit tail b bs hbit htail =>
          have hk : 2 ^ s ≤ current.length := by
            rw [hcurrentLen]
            simpa using hpow 0 (by omega)
          have hstep :=
            shl_rec_step_eval hcurrent hcurrent hbit (2 ^ s) hk (by omega)
          have hstepLen :
              (shlStepBits current current (2 ^ s) b).length = W := by
            rw [shlStepBits_length current current (2 ^ s) b hk rfl,
              hcurrentLen]
          have hpow' :
              ∀ j < n, 2 ^ ((s + 1) + j) ≤ W := by
            intro j hj
            simpa [Nat.add_assoc, Nat.add_comm 1 j,
              Nat.add_left_comm 1 j] using hpow (j + 1) (by omega)
          have hrec :=
            ih hstep htail (s + 1) hstepLen
              (by simpa using hn) hpow'
          have hsum : s + 1 + n = s + (n + 1) := by omega
          rw [hsum] at hrec
          rw [__bv_mk_bitblast_step_shl_rec.eq_5 currentTerm
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
            (Term.Numeral (s : Int))
            (Term.Numeral ((s + (n + 1) : Nat) : Int))
            hcurrent.ne_stuck
            (BitListEval.cons bit tail b bs hbit htail).ne_stuck
            (by intro h; cases h) (by intro h; cases h)]
          rw [show
            __eo_eq (Term.Numeral (s : Int))
                (Term.Numeral ((s + (n + 1) : Nat) : Int)) =
              Term.Boolean false by
            have hlt :
                (s : Int) < ((s + (n + 1) : Nat) : Int) := by
              exact_mod_cast (show s < s + (n + 1) by omega)
            have hterm :
                Term.Numeral ((s + (n + 1) : Nat) : Int) ≠
                  Term.Numeral (s : Int) := by
              intro h
              injection h with hi
              exact (Int.ne_of_gt hlt) hi
            simp only [__eo_eq]
            rw [show
              native_teq
                  (Term.Numeral ((s + (n + 1) : Nat) : Int))
                  (Term.Numeral (s : Int)) = false by
              exact decide_eq_false hterm]]
          simp only [__eo_ite, native_teq, native_ite,
           ]
          rw [__eo_l_1___bv_mk_bitblast_step_shl_rec.eq_4
            currentTerm (Term.Numeral (s : Int))
            (Term.Numeral ((s + (n + 1) : Nat) : Int)) bit tail
            hcurrent.ne_stuck (by intro h; cases h)
            (by intro h; cases h)]
          rw [show
            __eo_ite (__eo_is_z (Term.Numeral (s : Int)))
                (__eo_ite (__eo_is_neg (Term.Numeral (s : Int)))
                  (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2)
                    (Term.Numeral (s : Int))))
                (Term.Apply (Term.UOp UserOp.int_pow2)
                  (Term.Numeral (s : Int))) =
              Term.Numeral ((2 ^ s : Nat) : Int) by
            have hs : ¬ ((s : Int) < 0) := by omega
            simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
              __eo_ite, native_teq, native_not, native_and,
              native_zlt, native_ite, native_zexp_total, hs]]
          simp only [__eo_add, native_zplus]
          rw [show (s : Int) + 1 = ((s + 1 : Nat) : Int) by omega]
          simpa [shlBarrelBits, Nat.add_assoc] using hrec

private theorem shr_rec_eval {M : SmtModel}
    {currentTerm controlTerm signTerm : Term}
    {current controls : List Bool} {sign : Bool}
    (hcurrent : BitListEval M currentTerm current)
    (hcontrols : BitListEval M controlTerm controls)
    (hsign :
      __smtx_model_eval M (__eo_to_smt signTerm) =
        SmtValue.Boolean sign)
    (s n W : Nat)
    (hcurrentLen : current.length = W)
    (hn : n ≤ controls.length)
    (hpow : ∀ j < n, 2 ^ (s + j) ≤ W) :
    BitListEval M
      (__bv_mk_bitblast_step_shr_rec currentTerm controlTerm
        (Term.Numeral (s : Int)) (Term.Numeral ((s + n : Nat) : Int))
        signTerm)
      (shrBarrelBits current s controls n sign) := by
  induction n generalizing currentTerm controlTerm current controls s with
  | zero =>
      simp only [Nat.add_zero, shrBarrelBits]
      rw [__bv_mk_bitblast_step_shr_rec.eq_6 currentTerm controlTerm
        (Term.Numeral (s : Int)) (Term.Numeral (s : Int)) signTerm
        hcurrent.ne_stuck hcontrols.ne_stuck
        (by intro h; cases h) (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hsign)]
      rw [show
        __eo_eq (Term.Numeral (s : Int)) (Term.Numeral (s : Int)) =
          Term.Boolean true by
        simp [__eo_eq, native_teq]]
      simpa [__eo_ite, native_teq, native_ite] using hcurrent
  | succ n ih =>
      cases hcontrols with
      | nil => simp at hn
      | cons bit tail b bs hbit htail =>
          have hk : 2 ^ s ≤ current.length := by
            rw [hcurrentLen]
            simpa using hpow 0 (by omega)
          have hstep :=
            shr_rec_step_eval hcurrent hcurrent hbit hsign
              (2 ^ s) hk (by omega)
          have hstepLen :
              (shrStepBits current current (2 ^ s) b sign).length = W := by
            rw [shrStepBits_length current current (2 ^ s) b sign
              (by omega), hcurrentLen]
          have hpow' :
              ∀ j < n, 2 ^ ((s + 1) + j) ≤ W := by
            intro j hj
            simpa [Nat.add_assoc, Nat.add_comm 1 j,
              Nat.add_left_comm 1 j] using hpow (j + 1) (by omega)
          have hrec :=
            ih hstep htail (s + 1) hstepLen
              (by simpa using hn) hpow'
          have hsum : s + 1 + n = s + (n + 1) := by omega
          rw [hsum] at hrec
          rw [__bv_mk_bitblast_step_shr_rec.eq_6 currentTerm
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
            (Term.Numeral (s : Int))
            (Term.Numeral ((s + (n + 1) : Nat) : Int)) signTerm
            hcurrent.ne_stuck
            (BitListEval.cons bit tail b bs hbit htail).ne_stuck
            (by intro h; cases h) (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hsign)]
          rw [show
            __eo_eq (Term.Numeral (s : Int))
                (Term.Numeral ((s + (n + 1) : Nat) : Int)) =
              Term.Boolean false by
            have hlt :
                (s : Int) < ((s + (n + 1) : Nat) : Int) := by
              exact_mod_cast (show s < s + (n + 1) by omega)
            have hterm :
                Term.Numeral ((s + (n + 1) : Nat) : Int) ≠
                  Term.Numeral (s : Int) := by
              intro h
              injection h with hi
              exact (Int.ne_of_gt hlt) hi
            simp only [__eo_eq]
            rw [show
              native_teq
                  (Term.Numeral ((s + (n + 1) : Nat) : Int))
                  (Term.Numeral (s : Int)) = false by
              exact decide_eq_false hterm]]
          simp only [__eo_ite, native_teq, native_ite,
           ]
          rw [__eo_l_1___bv_mk_bitblast_step_shr_rec.eq_5
            currentTerm (Term.Numeral (s : Int))
            (Term.Numeral ((s + (n + 1) : Nat) : Int)) signTerm bit tail
            hcurrent.ne_stuck (by intro h; cases h)
            (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hsign)]
          rw [show
            __eo_ite (__eo_is_z (Term.Numeral (s : Int)))
                (__eo_ite (__eo_is_neg (Term.Numeral (s : Int)))
                  (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2)
                    (Term.Numeral (s : Int))))
                (Term.Apply (Term.UOp UserOp.int_pow2)
                  (Term.Numeral (s : Int))) =
              Term.Numeral ((2 ^ s : Nat) : Int) by
            have hs : ¬ ((s : Int) < 0) := by omega
            simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
              __eo_ite, native_teq, native_not, native_and,
              native_zlt, native_ite, native_zexp_total, hs]]
          simp only [__eo_add, native_zplus]
          rw [show (s : Int) + 1 = ((s + 1 : Nat) : Int) by omega]
          simpa [shrBarrelBits, Nat.add_assoc] using hrec

private theorem shlStepBits_value
    (current : List Bool) (k : Nat) (b : Bool)
    (hk : k ≤ current.length) :
    bitsValue (shlStepBits current current k b) =
      if b then
        (bitsValue current * 2 ^ k) % 2 ^ current.length
      else bitsValue current := by
  cases b with
  | false => simp [shlStepBits]
  | true =>
      simp only [shlStepBits, ↓reduceIte, bitsValue_append,
        List.length_replicate, bitsValue_replicate_false, Nat.zero_add]
      rw [Nat.min_eq_left hk]
      rw [bitsValue_take_mod current (current.length - k) (by omega)]
      calc
        2 ^ k * (bitsValue current % 2 ^ (current.length - k)) =
            (bitsValue current % 2 ^ (current.length - k)) * 2 ^ k := by
              ac_rfl
        _ = (bitsValue current * 2 ^ k) %
              (2 ^ (current.length - k) * 2 ^ k) :=
            (Nat.mul_mod_mul_right (2 ^ k) (bitsValue current)
              (2 ^ (current.length - k))).symm
        _ = (bitsValue current * 2 ^ k) % 2 ^ current.length := by
            rw [← Nat.pow_add]
            congr 2
            omega

private theorem bitsValue_drop_div
    (xs : List Bool) (k : Nat) (hk : k ≤ xs.length) :
    bitsValue (xs.drop k) = bitsValue xs / 2 ^ k := by
  have hsplit := bitsValue_take_drop xs k hk
  have hlow : bitsValue (xs.take k) < 2 ^ k := by
    have hlen : (xs.take k).length = k := List.length_take_of_le hk
    simpa [hlen] using bitsValue_lt (xs.take k)
  rw [hsplit]
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))]
  rw [Nat.div_eq_of_lt hlow, Nat.zero_add]

private theorem shrStepBits_false_value
    (current : List Bool) (k : Nat) (b : Bool)
    (hk : k ≤ current.length) :
    bitsValue (shrStepBits current current k b false) =
      if b then bitsValue current / 2 ^ k else bitsValue current := by
  cases b with
  | false => simp [shrStepBits, shrMergeBits]
  | true =>
      simp only [shrStepBits, shrMergeBits, ↓reduceIte, bitsValue_append,
        List.length_drop, bitsValue_replicate_false, Nat.mul_zero,
        Nat.add_zero]
      exact bitsValue_drop_div current k hk

private theorem mod_shift_comp (x a b m : Nat) :
    (((x * 2 ^ a) % m) * 2 ^ b) % m =
      (x * 2 ^ (a + b)) % m := by
  rw [Nat.mod_mul_mod]
  rw [Nat.pow_add]
  congr 1
  ac_rfl

private theorem shlBarrelBits_value
    (current controls : List Bool) (s n W : Nat)
    (hcurrent : current.length = W)
    (hn : n ≤ controls.length)
    (hpow : ∀ j < n, 2 ^ (s + j) ≤ W) :
    bitsValue (shlBarrelBits current s controls n) =
      (bitsValue current *
          2 ^ (2 ^ s * bitsValue (controls.take n))) % 2 ^ W := by
  induction n generalizing current controls s with
  | zero =>
      simp only [shlBarrelBits, List.take_zero, bitsValue, Nat.mul_zero,
        Nat.pow_zero, Nat.mul_one]
      rw [Nat.mod_eq_of_lt]
      simpa [hcurrent] using bitsValue_lt current
  | succ n ih =>
      cases controls with
      | nil => simp at hn
      | cons b bs =>
          have hk : 2 ^ s ≤ current.length := by
            rw [hcurrent]
            simpa using hpow 0 (by omega)
          have hstepLen :
              (shlStepBits current current (2 ^ s) b).length = W := by
            rw [shlStepBits_length current current (2 ^ s) b hk rfl,
              hcurrent]
          have hpow' :
              ∀ j < n, 2 ^ ((s + 1) + j) ≤ W := by
            intro j hj
            simpa [Nat.add_assoc, Nat.add_comm 1 j,
              Nat.add_left_comm 1 j] using hpow (j + 1) (by omega)
          have hrec :=
            ih (shlStepBits current current (2 ^ s) b) bs (s + 1)
              hstepLen (by simpa using hn) hpow'
          have hstep := shlStepBits_value current (2 ^ s) b hk
          cases b with
          | false =>
              simp [shlStepBits] at hrec
              change
                bitsValue (shlBarrelBits current (s + 1) bs n) = _
              rw [hrec]
              have hexp :
                  2 ^ (s + 1) * bitsValue (bs.take n) =
                    2 ^ s *
                      bitsValue ((false :: bs).take (n + 1)) := by
                simp only [List.take_succ_cons, bitsValue, Bool.toNat_false,
                  Nat.add_zero, Nat.pow_succ]
                ac_rfl
              rw [hexp]
          | true =>
              simp at hstep
              rw [hstep] at hrec
              rw [hcurrent] at hrec
              change
                bitsValue
                    (shlBarrelBits
                      (shlStepBits current current (2 ^ s) true)
                      (s + 1) bs n) = _
              rw [hrec]
              rw [mod_shift_comp]
              have hexp :
                  2 ^ s +
                      2 ^ (s + 1) * bitsValue (bs.take n) =
                    2 ^ s *
                      bitsValue ((true :: bs).take (n + 1)) := by
                simp only [List.take_succ_cons, bitsValue, Bool.toNat_true,
                  Nat.pow_succ]
                rw [Nat.mul_add, Nat.mul_one]
                ac_rfl
              rw [hexp]

private theorem shrBarrelBits_false_value
    (current controls : List Bool) (s n W : Nat)
    (hcurrent : current.length = W)
    (hn : n ≤ controls.length)
    (hpow : ∀ j < n, 2 ^ (s + j) ≤ W) :
    bitsValue (shrBarrelBits current s controls n false) =
      bitsValue current /
        2 ^ (2 ^ s * bitsValue (controls.take n)) := by
  induction n generalizing current controls s with
  | zero => simp [shrBarrelBits, bitsValue]
  | succ n ih =>
      cases controls with
      | nil => simp at hn
      | cons b bs =>
          have hk : 2 ^ s ≤ current.length := by
            rw [hcurrent]
            simpa using hpow 0 (by omega)
          have hstepLen :
              (shrStepBits current current (2 ^ s) b false).length = W := by
            rw [shrStepBits_length current current (2 ^ s) b false
              (by omega), hcurrent]
          have hpow' :
              ∀ j < n, 2 ^ ((s + 1) + j) ≤ W := by
            intro j hj
            simpa [Nat.add_assoc, Nat.add_comm 1 j,
              Nat.add_left_comm 1 j] using hpow (j + 1) (by omega)
          have hrec :=
            ih (shrStepBits current current (2 ^ s) b false) bs
              (s + 1) hstepLen (by simpa using hn) hpow'
          have hstep := shrStepBits_false_value current (2 ^ s) b hk
          cases b with
          | false =>
              simp [shrStepBits, shrMergeBits] at hrec
              change
                bitsValue (shrBarrelBits current (s + 1) bs n false) = _
              rw [hrec]
              have hexp :
                  2 ^ (s + 1) * bitsValue (bs.take n) =
                    2 ^ s *
                      bitsValue ((false :: bs).take (n + 1)) := by
                simp only [List.take_succ_cons, bitsValue, Bool.toNat_false,
                  Nat.add_zero, Nat.pow_succ]
                ac_rfl
              rw [hexp]
          | true =>
              simp at hstep
              rw [hstep] at hrec
              change
                bitsValue
                    (shrBarrelBits
                      (shrStepBits current current (2 ^ s) true false)
                      (s + 1) bs n false) = _
              rw [hrec, Nat.div_div_eq_div_mul, ← Nat.pow_add]
              have hexp :
                  2 ^ s +
                      2 ^ (s + 1) * bitsValue (bs.take n) =
                    2 ^ s *
                      bitsValue ((true :: bs).take (n + 1)) := by
                simp only [List.take_succ_cons, bitsValue, Bool.toNat_true,
                  Nat.pow_succ]
                rw [Nat.mul_add, Nat.mul_one]
                ac_rfl
              rw [hexp]

private theorem map_not_not (xs : List Bool) :
    (xs.map (!·)).map (!·) = xs := by
  induction xs with
  | nil => rfl
  | cons b bs =>
      cases b <;> simp [*]

private theorem map_not_not_comp (xs : List Bool) :
    xs.map ((fun x : Bool => !x) ∘ fun x : Bool => !x) = xs := by
  induction xs with
  | nil => rfl
  | cons b bs =>
      cases b <;> simp [Function.comp_def, *]

private theorem shrStepBits_complement
    (current : List Bool) (k : Nat) (b : Bool) :
    shrStepBits current current k b true =
      (shrStepBits (current.map (!·)) (current.map (!·))
        k b false).map (!·) := by
  cases b <;>
    simp [shrStepBits, shrMergeBits, List.map_append,
      List.map_drop, map_not_not_comp]

private theorem shrBarrelBits_complement
    (current controls : List Bool) (s n : Nat) :
    shrBarrelBits current s controls n true =
      (shrBarrelBits (current.map (!·)) s controls n false).map (!·) := by
  induction n generalizing current controls s with
  | zero => simp [shrBarrelBits, map_not_not_comp]
  | succ n ih =>
      cases controls with
      | nil => simp [shrBarrelBits, map_not_not_comp]
      | cons b bs =>
          simp only [shrBarrelBits]
          rw [ih
            (shrStepBits current current (2 ^ s) b true) bs (s + 1)]
          rw [shrStepBits_complement]
          simp [map_not_not_comp]

private theorem bitblast_apply_ite_same_length
    (c a b : Term)
    (h : __bv_bitblast_apply_ite c a b ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_bitblast_apply_ite c a b <;> simp_all
  · exact BitListsSameLength.nil
  · apply BitListsSameLength.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

private theorem bitblast_apply_ite_cond_ne
    (c a b : Term)
    (h : __bv_bitblast_apply_ite c a b ≠ Term.Stuck) :
    c ≠ Term.Stuck := by
  fun_induction __bv_bitblast_apply_ite c a b <;> simp_all

private theorem const_rec_const_ne
    (c indices : Term)
    (h : __bv_const_to_bitlist_rec c indices ≠ Term.Stuck) :
    c ≠ Term.Stuck := by
  fun_induction __bv_const_to_bitlist_rec c indices <;> simp_all

private theorem shl_rec_current_ne
    (current control s lsz : Term)
    (h :
      __bv_mk_bitblast_step_shl_rec current control s lsz ≠
        Term.Stuck) :
    current ≠ Term.Stuck := by
  intro hc
  subst current
  exact h (__bv_mk_bitblast_step_shl_rec.eq_1 control s lsz)

private theorem shr_rec_current_ne
    (current control s lsz sign : Term)
    (h :
      __bv_mk_bitblast_step_shr_rec current control s lsz sign ≠
        Term.Stuck) :
    current ≠ Term.Stuck := by
  intro hc
  subst current
  exact h (__bv_mk_bitblast_step_shr_rec.eq_1 control s lsz sign)

private theorem shl_rec_step_current_syntax
    (current original k bit : Term)
    (h :
      __bv_mk_bitblast_step_shl_rec_step current original k bit ≠
        Term.Stuck) :
    BitListSyntax current := by
  fun_induction
      __bv_mk_bitblast_step_shl_rec_step current original k bit <;>
    simp_all
  · exact BitListSyntax.nil
  · apply BitListSyntax.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h
  · apply BitListSyntax.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

private theorem shr_rec_step_current_syntax
    (current original k bit sign : Term)
    (h :
      __bv_mk_bitblast_step_shr_rec_step
          current original k bit sign ≠
        Term.Stuck) :
    BitListSyntax current := by
  fun_induction
      __bv_mk_bitblast_step_shr_rec_step
        current original k bit sign <;>
    simp_all
  · exact BitListSyntax.nil
  · apply BitListSyntax.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h
  · apply BitListSyntax.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

private theorem shl_rec_zero_current_syntax
    (current control : Term) (L : Nat) (hL : 0 < L)
    (hcontrol : control ≠ Term.Stuck)
    (hcontrolShape :
      ∃ bit tail,
        control =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
    (h :
      __bv_mk_bitblast_step_shl_rec current control
          (Term.Numeral 0) (Term.Numeral (L : Int)) ≠
        Term.Stuck) :
    BitListSyntax current := by
  rw [__bv_mk_bitblast_step_shl_rec.eq_5 current control
    (Term.Numeral 0) (Term.Numeral (L : Int))
    (shl_rec_current_ne _ _ _ _ h)
    hcontrol
    (by intro hs; cases hs) (by intro hs; cases hs)] at h
  rw [show
    __eo_eq (Term.Numeral 0) (Term.Numeral (L : Int)) =
      Term.Boolean false by
    have hne : Term.Numeral (L : Int) ≠ Term.Numeral 0 := by
      intro hh
      injection hh with hi
      have : L = 0 := by exact_mod_cast hi
      omega
    simp [__eo_eq, native_teq, hne]] at h
  simp [__eo_ite, native_teq, native_ite] at h
  rcases hcontrolShape with ⟨bit, tail, rfl⟩
  rw [__eo_l_1___bv_mk_bitblast_step_shl_rec.eq_4
    current (Term.Numeral 0) (Term.Numeral (L : Int)) bit tail
    (by
      intro hc
      subst current
      exact h
        (__eo_l_1___bv_mk_bitblast_step_shl_rec.eq_1
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
          (Term.Numeral 0) (Term.Numeral (L : Int)))
    )
    (by intro hs; cases hs) (by intro hs; cases hs)] at h
  apply shl_rec_step_current_syntax
  exact shl_rec_current_ne _ _ _ _ h

private theorem shr_rec_zero_current_syntax
    (current control sign : Term) (L : Nat) (hL : 0 < L)
    (hcontrol : control ≠ Term.Stuck)
    (hsign : sign ≠ Term.Stuck)
    (hcontrolShape :
      ∃ bit tail,
        control =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
    (h :
      __bv_mk_bitblast_step_shr_rec current control
          (Term.Numeral 0) (Term.Numeral (L : Int)) sign ≠
        Term.Stuck) :
    BitListSyntax current := by
  rw [__bv_mk_bitblast_step_shr_rec.eq_6 current control
    (Term.Numeral 0) (Term.Numeral (L : Int)) sign
    (shr_rec_current_ne _ _ _ _ _ h)
    hcontrol
    (by intro hs; cases hs) (by intro hs; cases hs)
    hsign] at h
  rw [show
    __eo_eq (Term.Numeral 0) (Term.Numeral (L : Int)) =
      Term.Boolean false by
    have hne : Term.Numeral (L : Int) ≠ Term.Numeral 0 := by
      intro hh
      injection hh with hi
      have : L = 0 := by exact_mod_cast hi
      omega
    simp [__eo_eq, native_teq, hne]] at h
  simp [__eo_ite, native_teq, native_ite] at h
  rcases hcontrolShape with ⟨bit, tail, rfl⟩
  rw [__eo_l_1___bv_mk_bitblast_step_shr_rec.eq_5
    current (Term.Numeral 0) (Term.Numeral (L : Int)) sign bit tail
    (by
      intro hc
      subst current
      exact h
        (__eo_l_1___bv_mk_bitblast_step_shr_rec.eq_1
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
          (Term.Numeral 0) (Term.Numeral (L : Int)) sign)
    )
    (by intro hs; cases hs) (by intro hs; cases hs) hsign] at h
  apply shr_rec_step_current_syntax
  exact shr_rec_current_ne _ _ _ _ _ h

private def shiftLogTerm (width : Term) : Term :=
  __eo_ite (__eo_is_z width)
    (__eo_ite (__eo_is_neg width) (Term.Numeral 0)
      (__eo_log (Term.Numeral 2) width))
    (__eo_mk_apply (Term.UOp UserOp.int_log2) width)

private def shiftLszTerm (width : Term) : Term :=
  __eo_ite
    (__eo_ite (__eo_is_z width)
      (__eo_ite (__eo_is_neg width) (Term.Boolean false)
        (__eo_eq width
          (__eo_pow (Term.Numeral 2) (shiftLogTerm width))))
      (__eo_mk_apply (Term.UOp UserOp.int_ispow2) width))
    (shiftLogTerm width)
    (__eo_add (shiftLogTerm width) (Term.Numeral 1))

private def barrelWidth (W : Nat) : Nat :=
  if W = 2 ^ W.log2 then W.log2 else W.log2 + 1

private theorem shiftLogTerm_numeral (W : Nat) :
    shiftLogTerm (Term.Numeral (W : Int)) =
      Term.Numeral (W.log2 : Int) := by
  have hnonneg : ¬ ((W : Int) < 0) := by omega
  simp [shiftLogTerm, __eo_ite, __eo_is_z, __eo_is_z_internal,
    __eo_is_neg, __eo_log, native_teq, native_not, native_and,
    native_zlt, native_ite, hnonneg,
    EvaluateProofInternal.native_int_log_two_eq_log2,
    native_int_log2]

private theorem shiftLszTerm_numeral (W : Nat) :
    shiftLszTerm (Term.Numeral (W : Int)) =
      Term.Numeral (barrelWidth W : Int) := by
  unfold shiftLszTerm
  simp only [shiftLogTerm_numeral]
  have hWnonneg : ¬ ((W : Int) < 0) := by omega
  have hlognonneg : ¬ ((W.log2 : Int) < 0) := by omega
  simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
    __eo_eq, __eo_ite, __eo_add, native_teq, native_not, native_and,
    native_zlt, native_ite, native_zexp_total, hWnonneg, hlognonneg,
    barrelWidth]
  by_cases hp : W = 2 ^ W.log2
  · have hpI : (2 : Int) ^ W.log2 = (W : Int) := by
      exact_mod_cast hp.symm
    rw [if_pos hpI]
    rw [if_pos hp]
  · have hpI : (2 : Int) ^ W.log2 ≠ (W : Int) := by
      intro heq
      apply hp
      exact_mod_cast heq.symm
    rw [if_neg hpI, if_neg hpI]
    rw [if_neg hp]
    congr 2

private theorem barrelWidth_le (W : Nat) (hW : 0 < W) :
    barrelWidth W ≤ W := by
  unfold barrelWidth
  split
  · exact Nat.log2_le_self W
  · rename_i hnot
    by_cases hW1 : W = 1
    · subst W
      exact (hnot (by decide)).elim
    · have hloglt : W.log2 < W := by
        apply (Nat.log2_lt (by omega)).2
        exact Nat.lt_two_pow_self
      omega

private theorem barrelWidth_pow_le
    (W : Nat) (hW : 0 < W) :
    ∀ j < barrelWidth W, 2 ^ j ≤ W := by
  intro j hj
  have hjlog : j ≤ W.log2 := by
    unfold barrelWidth at hj
    split at hj <;> omega
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hjlog)
    (Nat.log2_self_le (by omega))

private theorem le_pow_barrelWidth (W : Nat) (hW : 0 < W) :
    W ≤ 2 ^ barrelWidth W := by
  unfold barrelWidth
  split
  · rename_i hpow
    omega
  · rename_i hnot
    exact Nat.le_of_lt
      (((Nat.log2_eq_iff (by omega)).mp rfl).2)

private theorem testBitsMul
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term) (W : Nat) (xs : List Bool)
    (hacc : BitListEval M acc xs)
    (hxW : xs.length = W)
    (hrestTy : __smtx_typeof (__eo_to_smt rest) = SmtType.BitVec W)
    (hne : __bv_mk_bitblast_step_mul rest acc ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_mul rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) acc) rest)) := by
  revert hacc hxW hrestTy hne
  fun_cases __bv_mk_bitblast_step_mul rest acc <;>
    subst_vars <;> simp_all
  case case3 head tail haccNe =>
    intro hacc hxW hrestTy hne
    have hnewNe := mul_acc_ne hne
    have hparts :=
      bvmul_args_of_bitvec_type head tail W hrestTy
    have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
      unfold term_has_non_none_type
      rw [hparts.1]
      simp
    rcases (shift_add_multiplier_left_syntax acc head hnewNe).eval
        hM hheadNN with ⟨ys, hhead⟩
    have hyW :=
      bitListEval_length_eq_smt_type M hM head ys W hhead hparts.1
    rcases shift_add_multiplier_eval_bits M hM head acc W
        hnewNe hhead hacc hyW hxW with
      ⟨zs, hnew, hzW, hnewEval⟩
    have hnewEval' :
        __smtx_model_eval M
            (__eo_to_smt (__bv_shift_add_multiplier acc head)) =
          __smtx_model_eval M
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvmul) acc) head)) := by
      calc
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvmul) head) acc)) :=
            hnewEval
        _ = _ := bvmul_comm_values M head acc ys xs
          hhead hacc (by omega)
    have hrec :=
      testBitsMul M hM tail
        (__bv_shift_add_multiplier acc head) W zs
        hnew hzW hparts.2 hne
    calc
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_mk_bitblast_step_mul tail
              (__bv_shift_add_multiplier acc head))) =
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul)
                (__bv_shift_add_multiplier acc head))
              tail)) := hrec
      _ = __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvmul) acc) head))
              tail)) := by
        change
          __smtx_model_eval_bvmul
              (__smtx_model_eval M
                (__eo_to_smt (__bv_shift_add_multiplier acc head)))
              (__smtx_model_eval M (__eo_to_smt tail)) =
            __smtx_model_eval_bvmul
              (__smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt acc))
                (__smtx_model_eval M (__eo_to_smt head)))
              (__smtx_model_eval M (__eo_to_smt tail))
        rw [hnewEval']
        rfl
      _ = __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul) acc)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvmul) head) tail))) :=
        bvmul_assoc_values M hM acc head tail W xs ys
          hacc hhead hxW hyW hparts.2
  case case4 hnot =>
    intro hacc hxW hrestTy hne
    have hone := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires (__eo_to_z rest) (Term.Numeral 1) acc = acc := by
      rw [hone]
      simp [__eo_requires, native_ite, native_teq, native_not]
    rw [hreq]
    let xc := Term.Binary (W : Int) (bitsValue xs : Int)
    have hxcTy :
        __smtx_typeof (__eo_to_smt xc) = SmtType.BitVec W := by
      simpa [xc, hxW] using add_smt_typeof_bitsValue xs
    have hid :=
      eval_bvmul_right_to_z_one M hM xc rest W hxcTy hrestTy hone
    change
      __smtx_model_eval M (__eo_to_smt acc) =
        __smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt acc))
          (__smtx_model_eval M (__eo_to_smt rest))
    rw [hacc.eval, hxW]
    have hsimpa := hid.symm
    try simp [xc] at hsimpa ⊢
    exact hsimpa
termination_by sizeOf rest

private theorem eval_step_bvmul_fold
    (M : SmtModel) (hM : model_wf M)
    (rest acc : Term)
    (hne : __bv_mk_bitblast_step_mul rest acc ≠ Term.Stuck)
    (hnn : term_has_non_none_type
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) acc) rest))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_mul rest acc)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) acc) rest)) := by
  change term_has_non_none_type
      (SmtTerm.bvmul (__eo_to_smt acc) (__eo_to_smt rest)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvmul)
      (t1 := __eo_to_smt acc) (t2 := __eo_to_smt rest)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haccTy, hrestTy⟩
  revert hne
  fun_cases __bv_mk_bitblast_step_mul rest acc <;>
    subst_vars <;> simp_all
  case case3 head tail haccNe =>
    intro hne
    have hnewNe := mul_acc_ne hne
    have hparts :=
      bvmul_args_of_bitvec_type head tail W hrestTy
    have haccNN : term_has_non_none_type (__eo_to_smt acc) := by
      unfold term_has_non_none_type
      rw [haccTy]
      simp
    have hheadNN : term_has_non_none_type (__eo_to_smt head) := by
      unfold term_has_non_none_type
      rw [hparts.1]
      simp
    rcases (shift_add_multiplier_right_syntax acc head hnewNe).eval
        hM haccNN with ⟨xs, hacc⟩
    rcases (shift_add_multiplier_left_syntax acc head hnewNe).eval
        hM hheadNN with ⟨ys, hhead⟩
    have hxW :=
      bitListEval_length_eq_smt_type M hM acc xs W hacc haccTy
    have hyW :=
      bitListEval_length_eq_smt_type M hM head ys W hhead hparts.1
    rcases shift_add_multiplier_eval_bits M hM head acc W
        hnewNe hhead hacc hyW hxW with
      ⟨zs, hnew, hzW, hnewEval⟩
    have hnewEval' :
        __smtx_model_eval M
            (__eo_to_smt (__bv_shift_add_multiplier acc head)) =
          __smtx_model_eval M
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvmul) acc) head)) := by
      calc
        _ = __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvmul) head) acc)) :=
            hnewEval
        _ = _ := bvmul_comm_values M head acc ys xs
          hhead hacc (by omega)
    have hrec :=
      testBitsMul M hM tail
        (__bv_shift_add_multiplier acc head) W zs
        hnew hzW hparts.2 hne
    calc
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_mk_bitblast_step_mul tail
              (__bv_shift_add_multiplier acc head))) =
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul)
                (__bv_shift_add_multiplier acc head))
              tail)) := hrec
      _ = __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvmul) acc) head))
              tail)) := by
        change
          __smtx_model_eval_bvmul
              (__smtx_model_eval M
                (__eo_to_smt (__bv_shift_add_multiplier acc head)))
              (__smtx_model_eval M (__eo_to_smt tail)) =
            __smtx_model_eval_bvmul
              (__smtx_model_eval_bvmul
                (__smtx_model_eval M (__eo_to_smt acc))
                (__smtx_model_eval M (__eo_to_smt head)))
              (__smtx_model_eval M (__eo_to_smt tail))
        rw [hnewEval']
        rfl
      _ = __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvmul) acc)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvmul) head) tail))) :=
        bvmul_assoc_typed M hM acc head tail W
          haccTy hparts.1 hparts.2
  case case4 hnot =>
    intro hne
    have hone := support_eo_requires_cond_eq_of_non_stuck hne
    have hreq :
        __eo_requires (__eo_to_z rest) (Term.Numeral 1) acc = acc := by
      rw [hone]
      simp [__eo_requires, native_ite, native_teq, native_not]
    rw [hreq]
    exact
      (eval_bvmul_right_to_z_one M hM acc rest W
        haccTy hrestTy hone).symm

private theorem bitsValue_sign_extend
    (ys : List Bool) (s : Bool) (K : Nat) :
    bitsValue ((ys ++ [s]) ++ List.replicate K s) =
      ((BitVec.ofBoolListLE (ys ++ [s])).signExtend
        (K + (ys ++ [s]).length)).toNat := by
  rw [BitVec.toNat_signExtend]
  rw [BitVec.toNat_setWidth_of_le (by omega)]
  rw [msb_ofBoolListLE_append_singleton]
  rw [ofBoolListLE_toNat]
  rw [bitsValue_append]
  cases s with
  | false =>
    simp [bitsValue_replicate_false]
  | true =>
    simp only [↓reduceIte, bitsValue_replicate_true,
      List.length_append, List.length_singleton]
    rw [Nat.add_comm K (ys.length + 1), Nat.pow_add]
    rw [Nat.mul_sub_one]
    rw [show ys.length + 1 + K = (ys.length + 1) + K by omega,
      Nat.pow_add]
    simp [Nat.pow_succ, Nat.mul_assoc]

private inductive BitIndexList : Term → Nat → Nat → Prop
  | nil (start : Nat) :
      BitIndexList
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
          (Term.UOp UserOp.Int))
        start 0
  | cons (start : Nat) (tail : Term) (n : Nat)
      (h : BitIndexList tail (start + 1) n) :
      BitIndexList
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (start : Int)))
          tail)
        start (n + 1)

private theorem bitIndexList_ne_stuck
    {t : Term} {start n : Nat} (h : BitIndexList t start n) :
    t ≠ Term.Stuck := by
  cases h <;> intro ht <;> cases ht

private theorem BitIndexList.eq_nil
    {t : Term} {start : Nat} (h : BitIndexList t start 0) :
    t =
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int) := by
  cases h
  rfl

private theorem typed_list_repeat_rec_ne_stuck (k : Nat) :
    __eo_list_repeat_rec
        (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) k ≠
      Term.Stuck := by
  induction k with
  | zero =>
    intro h
    cases h
  | succ k ih =>
    rw [__eo_list_repeat_rec.eq_3 _ _ k
      (by intro h; cases h) (by intro h; cases h)]
    rw [mk_apply_eq (by intro h; cases h) ih]
    intro h
    cases h

private theorem iota_repeat_bitIndexList :
    ∀ (k start : Nat),
      BitIndexList
        (__iota_rec
          (__eo_list_repeat_rec
            (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) k)
          (Term.Numeral (start : Int)))
        start k := by
  intro k
  induction k with
  | zero =>
    intro start
    exact BitIndexList.nil start
  | succ k ih =>
    intro start
    rw [__eo_list_repeat_rec.eq_3 _ _ k
      (by intro h; cases h) (by intro h; cases h)]
    rw [mk_apply_eq (by intro h; cases h)
      (typed_list_repeat_rec_ne_stuck k)]
    change
      BitIndexList
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (start : Int)))
          (__iota_rec
            (__eo_list_repeat_rec
              (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) k)
            (__eo_add (Term.Numeral (start : Int))
              (Term.Numeral 1))))
        start (k + 1)
    rw [show
      __eo_add (Term.Numeral (start : Int)) (Term.Numeral 1) =
        Term.Numeral ((start + 1 : Nat) : Int) by
      congr 1]
    rw [mk_apply_eq (by intro h; cases h)
      (bitIndexList_ne_stuck (ih (start + 1)))]
    exact BitIndexList.cons start _ k (ih (start + 1))

private theorem generated_bit_indices (W : Nat) :
    BitIndexList
      (__eo_requires (__eo_is_neg (Term.Numeral (W : Int)))
        (Term.Boolean false)
        (__iota_rec
          (__eo_list_repeat
            (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) (Term.Numeral (W : Int)))
          (Term.Numeral 0)))
      0 W := by
  rw [show __eo_is_neg (Term.Numeral (W : Int)) =
      Term.Boolean false by
    simp [__eo_is_neg, native_zlt]]
  rw [req_refl _ _ (by intro h; cases h)]
  rw [__eo_list_repeat.eq_3 _ _ (W : Int)
    (by intro h; cases h) (by intro h; cases h)]
  rw [show native_zlt (W : Int) 0 = false by
    simp [native_zlt]]
  simp only [native_ite, Bool.false_eq_true, if_false]
  rw [show native_int_to_nat (W : Int) = W by
    simp [native_int_to_nat]]
  exact iota_repeat_bitIndexList W 0

private theorem BitListEval.list_len_rec {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    __eo_list_len_rec t = Term.Numeral (xs.length : Int) := by
  induction h with
  | nil => rfl
  | cons bit tail b bs hbit htail ih =>
      change
        __eo_add (Term.Numeral 1) (__eo_list_len_rec tail) =
          Term.Numeral ((b :: bs).length : Int)
      rw [ih]
      simp only [__eo_add, native_zplus]
      congr 1
      exact Int.add_comm 1 (bs.length : Int)

private theorem BitListEval.list_len {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    __eo_list_len (Term.UOp UserOp._at_from_bools) t =
      Term.Numeral (xs.length : Int) := by
  change
    __eo_requires
        (__eo_is_list (Term.UOp UserOp._at_from_bools) t)
        (Term.Boolean true) (__eo_list_len_rec t) =
      Term.Numeral (xs.length : Int)
  rw [h.is_list, requires_refl _ _ (by intro hh; cases hh)]
  exact h.list_len_rec

private theorem BitListEval.prefix {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) (n : Nat) :
    BitListEval M
      (__bv_bitblast_prefix (Term.Numeral (n : Int)) t)
      (xs.take n) := by
  induction h generalizing n with
  | nil =>
      cases n <;>
        simp [__bv_bitblast_prefix] <;>
        exact BitListEval.nil (M := M)
  | cons bit tail b bs hbit htail ih =>
      cases n with
      | zero =>
          simpa [__bv_bitblast_prefix] using
            (BitListEval.nil (M := M))
      | succ n =>
          have hrec := ih n
          have hout :=
            BitListEval.cons bit
              (__bv_bitblast_prefix (Term.Numeral (n : Int)) tail)
              b (bs.take n) hbit hrec
          rw [__bv_bitblast_prefix.eq_5
            (Term.Numeral ((n + 1 : Nat) : Int)) bit tail
            (by intro hh; cases hh)
            (by
              intro hh
              injection hh with hh
              exact
                (Int.ofNat_ne_zero.mpr
                  (Nat.add_one_ne_zero n)) hh)]
          rw [show
            __eo_add (Term.Numeral ((n + 1 : Nat) : Int))
                (Term.Numeral (-1)) =
              Term.Numeral (n : Int) by
            simp only [__eo_add, native_zplus]
            congr 1
            rw [show n + 1 = n.succ by rfl, Int.natCast_succ]
            exact Int.add_neg_cancel_right (n : Int) 1]
          rw [mk_apply_eq (by intro hh; cases hh) hrec.ne_stuck]
          exact hout

private theorem BitListEval.subsequence_zero {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) (n : Nat) :
    __bv_bitblast_subsequence (Term.Numeral 0)
        (Term.Numeral (n : Int)) t =
      __bv_bitblast_prefix (Term.Numeral ((n + 1 : Nat) : Int)) t := by
  cases h with
  | nil =>
      rfl
  | cons bit tail b bs hbit htail =>
      rw [__bv_bitblast_subsequence.eq_5
        (Term.Numeral (n : Int))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
        (by intro hh; cases hh)
        (by intro hh; cases hh)
        (by intro hh; cases hh)]
      congr 1

private theorem BitListEval.subsequence_zero_int {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs)
    (u : Int) :
    __bv_bitblast_subsequence (Term.Numeral 0) (Term.Numeral u) t =
      __bv_bitblast_prefix
        (__eo_add (Term.Numeral u) (Term.Numeral 1)) t := by
  cases h with
  | nil =>
      change
        Term.Binary 0 0 =
          __bv_bitblast_prefix (Term.Numeral (u + 1))
            (Term.Binary 0 0)
      by_cases hz : u + 1 = 0
      · rw [hz]
        rfl
      · rw [__bv_bitblast_prefix.eq_4
          (Term.Numeral (u + 1))
          (by intro hh; cases hh)
          (by
            intro hh
            injection hh with hh
            exact hz hh)]
  | cons bit tail b bs hbit htail =>
      exact __bv_bitblast_subsequence.eq_5 (Term.Numeral u)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)
        (by intro hh; cases hh) (by intro hh; cases hh)
        (by intro hh; cases hh)

private def falseBitList : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at_from_bools)
      (Term.Boolean false))
    (Term.Binary 0 0)

private theorem falseBitList_eval (M : SmtModel) :
    BitListEval M falseBitList [false] :=
  BitListEval.cons (Term.Boolean false) (Term.Binary 0 0)
    false [] rfl BitListEval.nil

private theorem BitListEval.div_shift {M : SmtModel}
    {t : Term} {b : Bool} {bs : List Bool}
    (h : BitListEval M t (b :: bs)) :
    BitListEval M
      (__bv_bitblast_concat
        (__bv_bitblast_subsequence (Term.Numeral 1)
          (__eo_list_len (Term.UOp UserOp._at_from_bools) t) t)
        falseBitList)
      (bs ++ [false]) := by
  cases h with
  | cons bit tail b bs hbit htail =>
      rw [(BitListEval.cons bit tail b bs hbit htail).list_len]
      rw [__bv_bitblast_subsequence.eq_6
        (Term.Numeral 1)
        (Term.Numeral ((b :: bs).length : Int))
        bit tail
        (by intro hh; cases hh)
        (by intro hh; cases hh)
        (by intro hh; cases hh)]
      rw [show
        __eo_add (Term.Numeral 1) (Term.Numeral (-1)) =
          Term.Numeral 0 by rfl]
      rw [show
        __eo_add (Term.Numeral ((b :: bs).length : Int))
            (Term.Numeral (-1)) =
          Term.Numeral (bs.length : Int) by
        simp only [__eo_add, native_zplus, List.length_cons]
        congr 1
        rw [Int.natCast_succ]
        rw [Int.add_neg_cancel_right]]
      rw [htail.subsequence_zero bs.length]
      have hpre := htail.prefix (bs.length + 1)
      rw [List.take_of_length_le (by omega)] at hpre
      have hout := hpre.concat (falseBitList_eval M)
      simpa using hout

private def divDoubleTerm (t : Term) : Term :=
  __bv_bitblast_concat falseBitList
    (__bv_bitblast_subsequence (Term.Numeral 0)
      (__eo_add
        (__eo_add
          (__eo_list_len (Term.UOp UserOp._at_from_bools) t)
          (Term.Numeral (-1)))
        (Term.Numeral (-1)))
      t)

private def divDoubleBits (xs : List Bool) : List Bool :=
  false :: xs.take (xs.length - 1)

private theorem BitListEval.div_double {M : SmtModel}
    {t : Term} {xs : List Bool}
    (h : BitListEval M t xs) (hpos : 0 < xs.length) :
    BitListEval M (divDoubleTerm t) (divDoubleBits xs) := by
  unfold divDoubleTerm divDoubleBits
  rw [h.list_len]
  rw [show
    __eo_add
        (__eo_add (Term.Numeral (xs.length : Int))
          (Term.Numeral (-1)))
        (Term.Numeral (-1)) =
      Term.Numeral ((xs.length : Int) + (-1) + (-1)) by rfl]
  rw [h.subsequence_zero_int
    ((xs.length : Int) + (-1) + (-1))]
  rw [show
    __eo_add
        (Term.Numeral ((xs.length : Int) + (-1) + (-1)))
        (Term.Numeral 1) =
      Term.Numeral ((xs.length - 1 : Nat) : Int) by
    simp only [__eo_add, native_zplus]
    congr 1
    rw [Int.natCast_sub (by omega : 1 ≤ xs.length)]
    simp only [Int.natCast_one, Int.sub_eq_add_neg]
    calc
      (xs.length : Int) + -1 + -1 + 1 =
          ((xs.length : Int) + -1) + (-1 + 1) :=
        Int.add_assoc ((xs.length : Int) + -1) (-1) 1
      _ = (xs.length : Int) + -1 := by
        rw [show (-1 : Int) + 1 = 0 by decide, Int.add_zero]]
  simpa using
    (falseBitList_eval M).concat (h.prefix (xs.length - 1))

private theorem divDoubleBits_length (xs : List Bool)
    (hpos : 0 < xs.length) :
    (divDoubleBits xs).length = xs.length := by
  simp only [divDoubleBits, List.length_cons, List.length_take]
  rw [Nat.min_eq_left (Nat.sub_le _ _)]
  exact Nat.sub_add_cancel (by omega)

private theorem bitsValue_divDoubleBits
    (xs : List Bool) (hpos : 0 < xs.length)
    (hbound : bitsValue xs < 2 ^ (xs.length - 1)) :
    bitsValue (divDoubleBits xs) = 2 * bitsValue xs := by
  have hle : xs.length - 1 ≤ xs.length := Nat.sub_le _ _
  rw [divDoubleBits, bitsValue]
  simp only [Bool.toNat_false, Nat.add_zero]
  rw [bitsValue_take_mod xs (xs.length - 1) hle,
    Nat.mod_eq_of_lt hbound]

private theorem addCarry_sub_eq {xs ys : List Bool}
    (hlen : xs.length = ys.length) :
    addCarry xs (ys.map (!·)) true =
      decide (bitsValue ys ≤ bitsValue xs) := by
  have hmapLen : xs.length = (ys.map (!·)).length := by
    simpa using hlen
  have hval := addBits_value xs (ys.map (!·)) true hmapLen
  rw [bitsValue_map_not] at hval
  rw [← hlen] at hval
  have hx := bitsValue_lt xs
  have hy := bitsValue_lt ys
  have hz := bitsValue_lt (addBits xs (ys.map (!·)) true)
  rw [addBits_length hmapLen] at hz
  have hcomp :
      2 ^ xs.length - 1 - bitsValue ys + 1 =
        2 ^ xs.length - bitsValue ys := by
    rw [hlen]
    omega
  by_cases hle : bitsValue ys ≤ bitsValue xs
  · cases hc : addCarry xs (ys.map (!·)) true with
    | false =>
      rw [hc] at hval
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
        Bool.toNat_true] at hval
      rw [Nat.add_assoc, hcomp] at hval
      omega
    | true =>
      simp [hle]
  · cases hc : addCarry xs (ys.map (!·)) true with
    | false =>
      simp [hle]
    | true =>
      rw [hc] at hval
      simp only [Bool.toNat_true, Nat.mul_one] at hval
      rw [Nat.add_assoc, hcomp] at hval
      omega

private theorem addBits_sub_value_of_le {xs ys : List Bool}
    (hlen : xs.length = ys.length)
    (hle : bitsValue ys ≤ bitsValue xs) :
    bitsValue (addBits xs (ys.map (!·)) true) =
      bitsValue xs - bitsValue ys := by
  have hmapLen : xs.length = (ys.map (!·)).length := by
    simpa using hlen
  have hval := addBits_value xs (ys.map (!·)) true hmapLen
  rw [bitsValue_map_not, addCarry_sub_eq hlen] at hval
  rw [← hlen] at hval
  simp only [hle, decide_true, Bool.toNat_true, Nat.mul_one] at hval
  have hy := bitsValue_lt ys
  have hcomp :
      2 ^ xs.length - 1 - bitsValue ys + 1 =
        2 ^ xs.length - bitsValue ys := by
    rw [hlen]
    omega
  rw [Nat.add_assoc, hcomp] at hval
  omega

private theorem BitListEval.unique {M : SmtModel}
    {t : Term} {xs ys : List Bool}
    (hx : BitListEval M t xs) (hy : BitListEval M t ys) :
    xs = ys := by
  induction hx generalizing ys with
  | nil =>
      cases hy
      rfl
  | cons bit tail b bs hbit htail ih =>
      cases hy with
      | cons _ _ b' bs' hbit' htail' =>
          have hb : b = b' := by
            rw [hbit] at hbit'
            injection hbit'
          subst b'
          exact congrArg (List.cons b) (ih htail')

private theorem BitListEval.tail {M : SmtModel}
    {t : Term} {b : Bool} {bs : List Bool}
    (h : BitListEval M t (b :: bs)) :
    BitListEval M (__bv_bitblast_tail t) bs := by
  cases h
  assumption

private theorem BitListEval.apply_ite_choose {M : SmtModel}
    {c a b : Term} {cv : Bool} {xs ys : List Bool}
    (hc :
      __smtx_model_eval M (__eo_to_smt c) =
        SmtValue.Boolean cv)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M (__bv_bitblast_apply_ite c a b)
      (if cv then xs else ys) := by
  have hout := ha.apply_ite hc hb hlen
  cases cv with
  | false =>
      simpa [zipWith_right_of_length xs ys hlen] using hout
  | true =>
      simpa [zipWith_left_of_length xs ys hlen] using hout

private theorem bitsValue_divShift (b : Bool) (bs : List Bool) :
    bitsValue (bs ++ [false]) = bitsValue (b :: bs) / 2 := by
  rw [bitsValue_append_singleton]
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, bitsValue]
  cases b <;> simp <;> omega

private inductive DivPairEval (M : SmtModel) :
    Term → List Bool → List Bool → Prop
  | intro (qTerm rTerm : Term) (qs rs : List Bool)
      (qeval : BitListEval M qTerm qs)
      (reval : BitListEval M rTerm rs) :
      DivPairEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair) qTerm) rTerm)
        qs rs

private theorem DivPairEval.first {M : SmtModel}
    {t : Term} {qs rs : List Bool}
    (h : DivPairEval M t qs rs) :
    BitListEval M (__pair_first t) qs := by
  cases h
  assumption

private theorem DivPairEval.second {M : SmtModel}
    {t : Term} {qs rs : List Bool}
    (h : DivPairEval M t qs rs) :
    BitListEval M (__pair_second t) rs := by
  cases h
  assumption

private theorem DivPairEval.ne_stuck {M : SmtModel}
    {t : Term} {qs rs : List Bool}
    (h : DivPairEval M t qs rs) : t ≠ Term.Stuck := by
  cases h
  intro hh
  cases hh

private theorem pair_first_arg_ne_stuck
    {p : Term} (h : __pair_first p ≠ Term.Stuck) :
    p ≠ Term.Stuck := by
  cases p <;> simp_all [__pair_first]

private theorem mk_pair_first_ne_components
    {q r : Term}
    (h :
      __pair_first
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at__at_pair) q) r) ≠
        Term.Stuck) :
    q ≠ Term.Stuck ∧ r ≠ Term.Stuck := by
  cases q <;> cases r <;>
    simp_all [__eo_mk_apply, __pair_first]

private def divLowBitTerm (a : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.ite)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.eq)
            (__bv_bitblast_head a))
          (Term.Boolean true)))
      (Term.Boolean true))
    (Term.Boolean false)

private theorem divLowBitTerm_eval {M : SmtModel}
    {a : Term} {b : Bool} {bs : List Bool}
    (h : BitListEval M a (b :: bs)) :
    __smtx_model_eval M (__eo_to_smt (divLowBitTerm a)) =
      SmtValue.Boolean b := by
  have hhead := h.head
  have hheadNe := term_ne_stuck_of_eval_boolean hhead
  have heq : divLowBitTerm a =
      Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (__bv_bitblast_head a))
              (Term.Boolean true)))
          (Term.Boolean true))
        (Term.Boolean false) := by
    unfold divLowBitTerm
    rw [mk_apply_eq (f := Term.UOp UserOp.eq)
      (x := __bv_bitblast_head a) (by intro hh; cases hh) hheadNe]
    rw [mk_apply_eq
      (f := Term.Apply (Term.UOp UserOp.eq) (__bv_bitblast_head a))
      (x := Term.Boolean true)
      (by intro hh; cases hh) (by intro hh; cases hh)]
    rw [mk_apply_eq (f := Term.UOp UserOp.ite)
      (by intro hh; cases hh) (by intro hh; cases hh)]
    rw [mk_apply_eq
      (f := Term.Apply (Term.UOp UserOp.ite)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (__bv_bitblast_head a))
          (Term.Boolean true)))
      (by intro hh; cases hh) (by intro hh; cases hh)]
    rw [mk_apply_eq
      (by intro hh; cases hh) (by intro hh; cases hh)]
  rw [heq]
  change
    __smtx_model_eval_ite
        (__smtx_model_eval_eq
          (__smtx_model_eval M
            (__eo_to_smt (__bv_bitblast_head a)))
          (SmtValue.Boolean true))
        (SmtValue.Boolean true) (SmtValue.Boolean false) =
      SmtValue.Boolean b
  rw [hhead]
  cases b <;> rfl

private def divQuotientBitTerm (c shiftedQ : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.ite) c)
      (__bv_bitblast_head shiftedQ))
    (Term.Boolean true)

private def divQuotientBitsTerm (c shiftedQ : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
      (divQuotientBitTerm c shiftedQ))
    (__bv_bitblast_tail shiftedQ)

private theorem divQuotientBitsTerm_eval {M : SmtModel}
    {c shiftedQ : Term} {cv : Bool} {bs : List Bool}
    (hc :
      __smtx_model_eval M (__eo_to_smt c) =
        SmtValue.Boolean cv)
    (hq : BitListEval M shiftedQ (false :: bs)) :
    BitListEval M (divQuotientBitsTerm c shiftedQ)
      ((!cv) :: bs) := by
  have hhead := hq.head
  have htail := hq.tail
  have hcNe := term_ne_stuck_of_eval_boolean hc
  have hheadNe := term_ne_stuck_of_eval_boolean hhead
  have hbitEq : divQuotientBitTerm c shiftedQ =
      Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite) c)
          (__bv_bitblast_head shiftedQ))
        (Term.Boolean true) := by
    unfold divQuotientBitTerm
    rw [mk_apply_eq (f := Term.UOp UserOp.ite) (x := c)
      (by intro hh; cases hh) hcNe]
    rw [mk_apply_eq
      (f := Term.Apply (Term.UOp UserOp.ite) c)
      (x := __bv_bitblast_head shiftedQ)
      (by intro hh; cases hh) hheadNe]
    rw [mk_apply_eq
      (by intro hh; cases hh) (by intro hh; cases hh)]
  have hbit :
      __smtx_model_eval M
          (__eo_to_smt (divQuotientBitTerm c shiftedQ)) =
        SmtValue.Boolean (!cv) := by
    rw [hbitEq]
    change
      __smtx_model_eval_ite
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M
            (__eo_to_smt (__bv_bitblast_head shiftedQ)))
          (SmtValue.Boolean true) =
        SmtValue.Boolean (!cv)
    rw [hc, hhead]
    cases cv <;> rfl
  unfold divQuotientBitsTerm
  rw [mk_apply_eq
    (f := Term.UOp UserOp._at_from_bools)
    (x := divQuotientBitTerm c shiftedQ)
    (by intro hh; cases hh)
    (term_ne_stuck_of_eval_boolean hbit)]
  rw [mk_apply_eq (by intro hh; cases hh) htail.ne_stuck]
  exact BitListEval.cons _ _ _ _ hbit htail

private theorem eo_eq_self_nonstuck (t : Term)
    (ht : t ≠ Term.Stuck) :
    __eo_eq t t = Term.Boolean true := by
  cases t <;> simp_all [__eo_eq, native_teq]

private theorem eo_eq_false_of_ne {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck)
    (hne : a ≠ b) :
    __eo_eq a b = Term.Boolean false := by
  have hne' : b ≠ a := fun h => hne h.symm
  cases a <;> cases b <;>
    simp_all [__eo_eq, native_teq]

private theorem div_mod_impl_input_syntax
    {a divisor zero indices : Term} {start n : Nat}
    (hzero : BitListSyntax zero)
    (hindices : BitIndexList indices start (n + 1))
    (h :
      __pair_first
          (__bv_div_mod_impl a divisor zero indices) ≠
        Term.Stuck) :
    BitListSyntax a := by
  have haNe : a ≠ Term.Stuck := by
    intro ha
    subst a
    rw [__bv_div_mod_impl.eq_1] at h
    exact h rfl
  have hbNe : divisor ≠ Term.Stuck := by
    intro hb
    subst divisor
    rw [__bv_div_mod_impl.eq_2 a zero indices haNe] at h
    exact h rfl
  have hzNe := hzero.ne_stuck
  cases hindices with
  | cons start tail n htail =>
      rw [__bv_div_mod_impl.eq_6 a divisor zero
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (start : Int)))
          tail)
        haNe hbNe hzNe
        (bitIndexList_ne_stuck
          (BitIndexList.cons start tail n htail))
        (by intro hh; cases hh)] at h
      by_cases haz : a = zero
      · subst a
        exact hzero
      · rw [eo_eq_false_of_ne haNe hzNe haz] at h
        simp only [__eo_ite, native_teq, native_ite,
         ] at h
        rw [__eo_l_1___bv_div_mod_impl.eq_4 a divisor zero
          (Term.Numeral (start : Int)) tail haNe hbNe hzNe] at h
        have hparts := mk_pair_first_ne_components h
        have hcond :=
          bitblast_apply_ite_cond_ne _ _ _ hparts.1
        have hfirst := mk_apply_arg_ne_stuck hcond
        have hripple := pair_first_arg_ne_stuck hfirst
        exact
          (ripple_carry_same_length _ _ _ _ hripple).syntax_left

private theorem nat_div_mod_unique {x y q r : Nat}
    (hy : 0 < y) (heq : x = y * q + r) (hr : r < y) :
    q = x / y ∧ r = x % y := by
  have hlo : q * y ≤ x := by
    rw [heq, Nat.mul_comm q y]
    omega
  have hhi : x < (q + 1) * y := by
    rw [heq, Nat.add_mul, Nat.mul_comm q y]
    omega
  have hdiv : x / y = q :=
    Nat.div_eq_of_lt_le hlo hhi
  have hmod := Nat.mod_add_div x y
  rw [hdiv] at hmod
  have hmodEq :
      x % y + y * q = y * q + r :=
    hmod.trans heq
  have hmod' :
      y * q + x % y = y * q + r := by
    simpa [Nat.add_comm] using hmodEq
  exact ⟨hdiv.symm, (Nat.add_left_cancel hmod').symm⟩

private theorem native_div_nat (a b : Nat) :
    native_div_total (a : Int) (b : Int) =
      ((a / b : Nat) : Int) := by
  simp [native_div_total]

private theorem bvurem_binary_values
    (xs ys : List Bool) :
    __smtx_model_eval_bvurem
        (SmtValue.Binary (xs.length : Int) (bitsValue xs : Int))
        (SmtValue.Binary (ys.length : Int) (bitsValue ys : Int)) =
      SmtValue.Binary (xs.length : Int)
        ((if bitsValue ys = 0 then
            bitsValue xs
          else bitsValue xs % bitsValue ys : Nat) : Int) := by
  simp only [__smtx_model_eval_bvurem]
  by_cases hy : bitsValue ys = 0
  · have hyI : (bitsValue ys : Int) = 0 := by
      exact_mod_cast hy
    simp [native_zeq, native_ite, hy,
      native_int_pow2_nat]
    simp only [native_mod_total]
    change
      (bitsValue xs : Int) % (2 ^ xs.length : Nat) =
        (bitsValue xs : Int)
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast bitsValue_lt xs)
  · have hyI : ¬(bitsValue ys : Int) = 0 := by
      exact_mod_cast hy
    simp [native_zeq, native_ite, hy,
      native_int_pow2_nat]
    simp only [native_mod_total]
    have hinner :
        (bitsValue xs : Int) % (bitsValue ys : Int) =
          ((bitsValue xs % bitsValue ys : Nat) : Int) := by
      simp
    rw [hinner]
    change
      (bitsValue xs % bitsValue ys : Int) %
          (2 ^ xs.length : Nat) =
        (bitsValue xs % bitsValue ys : Int)
    have hlt :
        bitsValue xs % bitsValue ys < 2 ^ xs.length :=
      Nat.lt_of_le_of_lt
        (Nat.mod_le (bitsValue xs) (bitsValue ys))
        (bitsValue_lt xs)
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast hlt)

private theorem bvudiv_binary_values
    (xs ys : List Bool) :
    __smtx_model_eval_bvudiv
        (SmtValue.Binary (xs.length : Int) (bitsValue xs : Int))
        (SmtValue.Binary (ys.length : Int) (bitsValue ys : Int)) =
      SmtValue.Binary (xs.length : Int)
        ((if bitsValue ys = 0 then
            2 ^ xs.length - 1
          else bitsValue xs / bitsValue ys : Nat) : Int) := by
  simp only [__smtx_model_eval_bvudiv]
  by_cases hy : bitsValue ys = 0
  · have hyI : (bitsValue ys : Int) = 0 := by
      exact_mod_cast hy
    simp [native_zeq, native_ite, hy]
    rw [native_int_pow2_nat]
    have hp : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
    rw [show
      native_binary_max (xs.length : Int) =
        ((2 ^ xs.length - 1 : Nat) : Int) by
      simp only [native_binary_max, native_zplus, native_zneg]
      rw [native_int_pow2_nat, Int.ofNat_sub hp]
      rw [Int.sub_eq_add_neg, Int.natCast_one]]
    simp only [native_mod_total]
    change
      ((2 ^ xs.length - 1 : Nat) : Int) %
          (2 ^ xs.length : Nat) =
        ((2 ^ xs.length - 1 : Nat) : Int)
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast (by omega :
        2 ^ xs.length - 1 < 2 ^ xs.length))
  · have hyI : ¬(bitsValue ys : Int) = 0 := by
      exact_mod_cast hy
    simp [native_zeq, native_ite, hy,
      native_int_pow2_nat]
    simp only [native_div_total, native_mod_total]
    have hinner :
        (bitsValue xs : Int) / (bitsValue ys : Int) =
          ((bitsValue xs / bitsValue ys : Nat) : Int) := by
      simp
    rw [hinner]
    change
      (bitsValue xs / bitsValue ys : Int) %
          (2 ^ xs.length : Nat) =
        (bitsValue xs / bitsValue ys : Int)
    have hlt :
        bitsValue xs / bitsValue ys < 2 ^ xs.length :=
      Nat.lt_of_le_of_lt
        (Nat.div_le_self (bitsValue xs) (bitsValue ys))
        (bitsValue_lt xs)
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast hlt)

private theorem div_mod_impl_eval {M : SmtModel}
    {a divisor zero indices : Term}
    {xs ys : List Bool} {W start n : Nat}
    (ha : BitListEval M a xs)
    (hb : BitListEval M divisor ys)
    (hz : BitListEval M zero (List.replicate W false))
    (hxs : xs.length = W)
    (hys : ys.length = W)
    (hindices : BitIndexList indices start n)
    (hbound : bitsValue xs < 2 ^ n) :
    ∃ qs rs,
      DivPairEval M
        (__bv_div_mod_impl a divisor zero indices) qs rs ∧
      qs.length = W ∧ rs.length = W ∧
      (0 < bitsValue ys →
        bitsValue qs = bitsValue xs / bitsValue ys ∧
        bitsValue rs = bitsValue xs % bitsValue ys) := by
  induction hindices generalizing a xs with
  | nil start =>
      rw [__bv_div_mod_impl.eq_5 a divisor zero
        ha.ne_stuck hb.ne_stuck hz.ne_stuck]
      refine
        ⟨List.replicate W false, List.replicate W false,
          DivPairEval.intro zero zero _ _ hz hz,
          List.length_replicate, List.length_replicate, ?_⟩
      intro hypos
      have hxzero : bitsValue xs = 0 := by
        simp only [Nat.pow_zero] at hbound
        omega
      rw [bitsValue_replicate_false, hxzero]
      simp
  | cons start tail n htail ih =>
      rw [__bv_div_mod_impl.eq_6 a divisor zero
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (start : Int)))
          tail)
        ha.ne_stuck hb.ne_stuck hz.ne_stuck
        (bitIndexList_ne_stuck (BitIndexList.cons start tail n htail))
        (by intro hh; cases hh)]
      by_cases haz : a = zero
      · subst a
        rw [eo_eq_self_nonstuck zero hz.ne_stuck]
        simp only [__eo_ite, native_teq, native_ite,
         ]
        have hxeq :
            xs = List.replicate W false := ha.unique hz
        subst xs
        refine
          ⟨List.replicate W false, List.replicate W false,
            DivPairEval.intro zero zero _ _ hz hz,
            List.length_replicate, List.length_replicate, ?_⟩
        intro hypos
        rw [bitsValue_replicate_false]
        simp
      · have heqFalse :
            __eo_eq a zero = Term.Boolean false := by
          exact eo_eq_false_of_ne ha.ne_stuck hz.ne_stuck haz
        rw [heqFalse]
        simp only [__eo_ite, native_teq, native_ite,
         ]
        cases xs with
        | nil =>
            have hWzero : W = 0 := by simpa using hxs.symm
            have hzeroNil : BitListEval M zero [] := by
              simpa [hWzero] using hz
            exact
              (haz (ha.eq_nil.trans hzeroNil.eq_nil.symm)).elim
        | cons b bs =>
          let shiftedA :=
            __bv_bitblast_concat
              (__bv_bitblast_subsequence (Term.Numeral 1)
                (__eo_list_len
                  (Term.UOp UserOp._at_from_bools) a) a)
              falseBitList
          have hshift :
              BitListEval M shiftedA (bs ++ [false]) := by
            exact ha.div_shift
          have hshiftLen : (bs ++ [false]).length = W := by
            simpa using hxs
          have hshiftBound :
              bitsValue (bs ++ [false]) < 2 ^ n := by
            rw [bitsValue_divShift b bs]
            exact
              (Nat.div_lt_iff_lt_mul
                (k := 2) (x := bitsValue (b :: bs))
                (y := 2 ^ n) (by decide)).2
                (by
                  simpa [Nat.pow_succ, Nat.mul_comm] using hbound)
          rcases ih hshift hshiftLen hshiftBound with
            ⟨qs, rs, hrec, hqsLen, hrsLen, hrecVal⟩
          have hWpos : 0 < W := by
            rw [← hxs]
            simp
          let recTerm :=
            __bv_div_mod_impl shiftedA divisor zero tail
          have hq : BitListEval M (__pair_first recTerm) qs := by
            exact hrec.first
          have hr : BitListEval M (__pair_second recTerm) rs := by
            exact hrec.second
          have hnotDivisor :
              BitListEval M
                (__bv_bitblast_apply_unary
                  (Term.UOp UserOp.not) divisor)
                (ys.map (!·)) :=
            hb.apply_not
          have hrsPos : 0 < rs.length := by
            rw [hrsLen]
            exact hWpos
          have hqPos : 0 < qs.length := by
            rw [hqsLen]
            exact hWpos
          have hdoubleR :
              BitListEval M
                (divDoubleTerm (__pair_second recTerm))
                (divDoubleBits rs) :=
            hr.div_double hrsPos
          have hlow := divLowBitTerm_eval ha
          have hdoubleRLen :
              (divDoubleBits rs).length =
                (List.replicate W false).length := by
            rw [divDoubleBits_length rs hrsPos, hrsLen,
              List.length_replicate]
          have hcandPair :=
            ripple_carry_eval hdoubleR hz hlow hdoubleRLen
          let candTerm :=
            __pair_second
              (__bv_ripple_carry_adder_2
                (divDoubleTerm (__pair_second recTerm))
                zero (divLowBitTerm a) (Term.Binary 0 0))
          let candBits :=
            addBits (divDoubleBits rs)
              (List.replicate W false) b
          have hcand :
              BitListEval M candTerm candBits := by
            exact hcandPair.second
          have hcandLen : candBits.length = W := by
            unfold candBits
            rw [addBits_length hdoubleRLen,
              divDoubleBits_length rs hrsPos, hrsLen]
          have hcandSubPair :=
            ripple_carry_eval
              (carry := Term.Boolean true) (cb := true)
              hcand hnotDivisor rfl
              (by simpa [List.length_map] using
                (show candBits.length = ys.length by
                  omega))
          let candCarry :=
            addCarry candBits (ys.map (!·)) true
          let candSubTerm :=
            __pair_second
              (__bv_ripple_carry_adder_2 candTerm
                (__bv_bitblast_apply_unary
                  (Term.UOp UserOp.not) divisor)
                (Term.Boolean true) (Term.Binary 0 0))
          let candSubBits :=
            addBits candBits (ys.map (!·)) true
          have hcandSub :
              BitListEval M candSubTerm candSubBits := by
            exact hcandSubPair.second
          have hcandCarry :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__pair_first
                      (__bv_ripple_carry_adder_2 candTerm
                        (__bv_bitblast_apply_unary
                          (Term.UOp UserOp.not) divisor)
                        (Term.Boolean true) (Term.Binary 0 0)))) =
                SmtValue.Boolean candCarry := by
            exact hcandSubPair.first_eval
          let candCondTerm :=
            __eo_mk_apply (Term.UOp UserOp.not)
              (__pair_first
                (__bv_ripple_carry_adder_2 candTerm
                  (__bv_bitblast_apply_unary
                    (Term.UOp UserOp.not) divisor)
                  (Term.Boolean true) (Term.Binary 0 0)))
          have hcandCond :
              __smtx_model_eval M (__eo_to_smt candCondTerm) =
                SmtValue.Boolean (!candCarry) := by
            unfold candCondTerm
            rw [mk_apply_eq (by intro hh; cases hh)
              (term_ne_stuck_of_eval_boolean hcandCarry)]
            exact eval_plain_not_bool hcandCarry
          have hxSubPair :=
            ripple_carry_eval
              (carry := Term.Boolean true) (cb := true)
              ha hnotDivisor rfl
              (by simpa [List.length_map] using
                (show (b :: bs).length = ys.length by omega))
          let xCarry :=
            addCarry (b :: bs) (ys.map (!·)) true
          have hxCarry :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__pair_first
                      (__bv_ripple_carry_adder_2 a
                        (__bv_bitblast_apply_unary
                          (Term.UOp UserOp.not) divisor)
                        (Term.Boolean true) (Term.Binary 0 0)))) =
                SmtValue.Boolean xCarry := by
            exact hxSubPair.first_eval
          let xCondTerm :=
            __eo_mk_apply (Term.UOp UserOp.not)
              (__pair_first
                (__bv_ripple_carry_adder_2 a
                  (__bv_bitblast_apply_unary
                    (Term.UOp UserOp.not) divisor)
                  (Term.Boolean true) (Term.Binary 0 0)))
          have hxCond :
              __smtx_model_eval M (__eo_to_smt xCondTerm) =
                SmtValue.Boolean (!xCarry) := by
            unfold xCondTerm
            rw [mk_apply_eq (by intro hh; cases hh)
              (term_ne_stuck_of_eval_boolean hxCarry)]
            exact eval_plain_not_bool hxCarry
          have hdoubleQ :
              BitListEval M
                (divDoubleTerm (__pair_first recTerm))
                (divDoubleBits qs) :=
            hq.div_double hqPos
          have hqnew :=
            divQuotientBitsTerm_eval hcandCond hdoubleQ
          let qNewTerm :=
            divQuotientBitsTerm candCondTerm
              (divDoubleTerm (__pair_first recTerm))
          let qNewBits :=
            (!(!candCarry)) :: (divDoubleBits qs).tail
          have hqNew :
              BitListEval M qNewTerm qNewBits := by
            have hsimpa := hqnew
            try simp [qNewTerm, qNewBits] at hsimpa ⊢
            exact hsimpa
          have hqNewLen : qNewBits.length = W := by
            have hdlen :=
              divDoubleBits_length qs hqPos
            unfold qNewBits
            simp only [List.length_cons, List.length_tail]
            omega
          let qOutTerm :=
            __bv_bitblast_apply_ite xCondTerm zero qNewTerm
          let qOutBits :=
            if !xCarry then List.replicate W false else qNewBits
          have hqOut :
              BitListEval M qOutTerm qOutBits := by
            exact hz.apply_ite_choose hxCond hqNew
              (by rw [List.length_replicate, hqNewLen])
          let rInnerTerm :=
            __bv_bitblast_apply_ite candCondTerm candTerm candSubTerm
          let rInnerBits :=
            if !candCarry then candBits else candSubBits
          have hcandSubLen : candSubBits.length = W := by
            unfold candSubBits
            rw [addBits_length]
            · exact hcandLen
            · simpa [List.length_map] using
                (show candBits.length = ys.length by omega)
          have hrInner :
              BitListEval M rInnerTerm rInnerBits := by
            exact hcand.apply_ite_choose hcandCond hcandSub
              (by omega)
          have hrInnerLen : rInnerBits.length = W := by
            unfold rInnerBits
            split <;> omega
          let rOutTerm :=
            __bv_bitblast_apply_ite xCondTerm a rInnerTerm
          let rOutBits :=
            if !xCarry then (b :: bs) else rInnerBits
          have hrOut :
              BitListEval M rOutTerm rOutBits := by
            exact ha.apply_ite_choose hxCond hrInner
              (by omega)
          have hqOutLen : qOutBits.length = W := by
            unfold qOutBits
            split <;> simp_all
          have hrOutLen : rOutBits.length = W := by
            unfold rOutBits
            split <;> omega
          refine ⟨qOutBits, rOutBits, ?_, hqOutLen, hrOutLen, ?_⟩
          · rw [__eo_l_1___bv_div_mod_impl.eq_4 a divisor zero
              (Term.Numeral (start : Int)) tail
              ha.ne_stuck hb.ne_stuck hz.ne_stuck]
            change
              DivPairEval M
                (__eo_mk_apply
                  (__eo_mk_apply
                    (Term.UOp UserOp._at__at_pair) qOutTerm)
                  rOutTerm)
                qOutBits rOutBits
            rw [mk_apply_eq
              (f := Term.UOp UserOp._at__at_pair)
              (x := qOutTerm)
              (by intro hh; cases hh) hqOut.ne_stuck]
            rw [mk_apply_eq
              (by intro hh; cases hh) hrOut.ne_stuck]
            exact DivPairEval.intro qOutTerm rOutTerm
              qOutBits rOutBits hqOut hrOut
          · intro hypos
            simp only [List.length_cons] at hxs
            have hrecSem := hrecVal hypos
            have hshiftBs :
                bitsValue (bs ++ [false]) = bitsValue bs := by
              rw [bitsValue_append_singleton]
              simp
            have hdecomp :
                bitsValue rs +
                    bitsValue ys * bitsValue qs =
                  bitsValue (bs ++ [false]) := by
              rw [hrecSem.1, hrecSem.2]
              exact Nat.mod_add_div
                (bitsValue (bs ++ [false])) (bitsValue ys)
            rw [hshiftBs] at hdecomp
            have hrlt : bitsValue rs < bitsValue ys := by
              rw [hrecSem.2]
              exact Nat.mod_lt _ hypos
            have hrLeBs : bitsValue rs ≤ bitsValue bs := by
              omega
            have hqLeBs : bitsValue qs ≤ bitsValue bs := by
              rw [hrecSem.1, hshiftBs]
              exact Nat.div_le_self (bitsValue bs) (bitsValue ys)
            have hbsBound := bitsValue_lt bs
            have hrsExp : rs.length - 1 = bs.length := by
              omega
            have hqsExp : qs.length - 1 = bs.length := by
              omega
            have hrWidthBound :
                bitsValue rs < 2 ^ (rs.length - 1) := by
              rw [hrsExp]
              omega
            have hqWidthBound :
                bitsValue qs < 2 ^ (qs.length - 1) := by
              rw [hqsExp]
              omega
            have hdoubleRVal :=
              bitsValue_divDoubleBits rs hrsPos hrWidthBound
            have hdoubleQVal :=
              bitsValue_divDoubleBits qs hqPos hqWidthBound
            have hcandBound :
                2 * bitsValue rs + b.toNat < 2 ^ W := by
              have hbLe := Bool.toNat_le b
              rw [← hxs, Nat.pow_succ]
              rw [hrsExp] at hrWidthBound
              omega
            have hcandVal :
                bitsValue candBits =
                  2 * bitsValue rs + b.toNat := by
              unfold candBits
              rw [addBits_value_mod hdoubleRLen,
                hdoubleRVal, bitsValue_replicate_false]
              simp only [Nat.add_zero]
              rw [divDoubleBits_length rs hrsPos, hrsLen,
                Nat.mod_eq_of_lt hcandBound]
            have hcandCarryEq :
                candCarry =
                  decide (bitsValue ys ≤ bitsValue candBits) := by
              unfold candCarry
              exact addCarry_sub_eq
                (by
                  simpa only [List.length_map] using
                    (show candBits.length = ys.length by omega))
            have hxCarryEq :
                xCarry =
                  decide (bitsValue ys ≤ bitsValue (b :: bs)) := by
              unfold xCarry
              exact addCarry_sub_eq
                (by
                  simpa only [List.length_map] using
                    (show (b :: bs).length = ys.length by
                      simp only [List.length_cons]
                      omega))
            have hqNewVal :
                bitsValue qNewBits =
                  2 * bitsValue qs + candCarry.toNat := by
              unfold qNewBits divDoubleBits
              simp only [List.tail_cons, bitsValue, Bool.not_not]
              rw [bitsValue_take_mod qs (qs.length - 1)
                (Nat.sub_le _ _),
                Nat.mod_eq_of_lt hqWidthBound]
            have hbaseEq :
                bitsValue (b :: bs) =
                  bitsValue ys * (2 * bitsValue qs) +
                    bitsValue candBits := by
              calc
                bitsValue (b :: bs) =
                    2 * bitsValue bs + b.toNat := rfl
                _ =
                    2 * (bitsValue rs +
                      bitsValue ys * bitsValue qs) + b.toNat := by
                      rw [hdecomp]
                _ =
                    2 * bitsValue rs +
                      2 * (bitsValue ys * bitsValue qs) +
                        b.toNat := by
                      rw [Nat.mul_add]
                _ =
                    bitsValue ys * (2 * bitsValue qs) +
                      (2 * bitsValue rs + b.toNat) := by
                      have hm :
                          2 * (bitsValue ys * bitsValue qs) =
                            bitsValue ys * (2 * bitsValue qs) := by
                        ac_rfl
                      rw [hm]
                      omega
                _ =
                    bitsValue ys * (2 * bitsValue qs) +
                      bitsValue candBits := by
                      rw [hcandVal]
            by_cases hxlt :
                bitsValue (b :: bs) < bitsValue ys
            · have hxCarryFalse : xCarry = false := by
                rw [hxCarryEq]
                simp [show
                  ¬bitsValue ys ≤ bitsValue (b :: bs) by omega]
              simp [qOutBits, rOutBits, hxCarryFalse,
                bitsValue_replicate_false,
                Nat.div_eq_of_lt hxlt, Nat.mod_eq_of_lt hxlt]
            · have hyx :
                  bitsValue ys ≤ bitsValue (b :: bs) := by
                omega
              have hxCarryTrue : xCarry = true := by
                rw [hxCarryEq]
                simp [hyx]
              by_cases hclt :
                  bitsValue candBits < bitsValue ys
              · have hcCarryFalse : candCarry = false := by
                  rw [hcandCarryEq]
                  simp [show
                    ¬bitsValue ys ≤ bitsValue candBits by omega]
                have huniq :=
                  nat_div_mod_unique hypos hbaseEq hclt
                simpa [qOutBits, rOutBits, rInnerBits,
                  hxCarryTrue, hcCarryFalse, hqNewVal] using huniq
              · have hyc :
                    bitsValue ys ≤ bitsValue candBits := by
                  omega
                have hcCarryTrue : candCarry = true := by
                  rw [hcandCarryEq]
                  simp [hyc]
                have hcandSubVal :
                    bitsValue candSubBits =
                      bitsValue candBits - bitsValue ys := by
                  unfold candSubBits
                  exact addBits_sub_value_of_le
                    (by
                      simpa only [List.length_map] using
                        (show candBits.length = ys.length by omega))
                    hyc
                have hcandLtTwice :
                    bitsValue candBits < 2 * bitsValue ys := by
                  rw [hcandVal]
                  have hbLe := Bool.toNat_le b
                  omega
                have hsubLt :
                    bitsValue candBits - bitsValue ys <
                      bitsValue ys := by
                  omega
                have hbaseSub :
                    bitsValue (b :: bs) =
                      bitsValue ys * (2 * bitsValue qs + 1) +
                        (bitsValue candBits - bitsValue ys) := by
                  rw [hbaseEq, Nat.mul_add]
                  simp only [Nat.mul_one]
                  omega
                have huniq :=
                  nat_div_mod_unique hypos hbaseSub hsubLt
                simpa [qOutBits, rOutBits, rInnerBits,
                  hxCarryTrue, hcCarryTrue, hqNewVal,
                  hcandSubVal] using huniq

private theorem eval_step_bvurem
    (M : SmtModel) (hM : model_wf M)
    (a divisor : Term)
    (hExpanded :
      let width := __bv_bitwidth (__eo_typeof a)
      let zero :=
        __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) width
      __bv_bitblast_apply_ite
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__bv_mk_bitblast_step_eq_rec divisor zero))
          a
          (__pair_second
            (__bv_div_mod_impl a divisor zero
              (__eo_requires (__eo_is_neg width)
                (Term.Boolean false)
                (__iota_rec
                  (__eo_list_repeat
                    (Term.UOp UserOp._at__at_TypedList_cons)
                    (Term.Numeral 0) width)
                  (Term.Numeral 0))))) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvurem) a) divisor))) :
    __smtx_model_eval M
        (__eo_to_smt
          (let width := __bv_bitwidth (__eo_typeof a)
           let zero :=
             __eo_list_repeat (Term.UOp UserOp._at_from_bools)
               (Term.Boolean false) width
           __bv_bitblast_apply_ite
             (__eo_list_singleton_elim (Term.UOp UserOp.and)
               (__bv_mk_bitblast_step_eq_rec divisor zero))
             a
             (__pair_second
               (__bv_div_mod_impl a divisor zero
                 (__eo_requires (__eo_is_neg width)
                   (Term.Boolean false)
                   (__iota_rec
                     (__eo_list_repeat
                       (Term.UOp UserOp._at__at_TypedList_cons)
                       (Term.Numeral 0) width)
                     (Term.Numeral 0))))))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvurem) a) divisor)) := by
  let width := __bv_bitwidth (__eo_typeof a)
  let zero :=
    __eo_list_repeat (Term.UOp UserOp._at_from_bools)
      (Term.Boolean false) width
  let indices :=
    __eo_requires (__eo_is_neg width) (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat
          (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) width)
        (Term.Numeral 0))
  let divResult := __bv_div_mod_impl a divisor zero indices
  let guard :=
    __eo_list_singleton_elim (Term.UOp UserOp.and)
      (__bv_mk_bitblast_step_eq_rec divisor zero)
  change
    __bv_bitblast_apply_ite guard a
        (__pair_second divResult) ≠
      Term.Stuck at hExpanded
  have hsame :=
    bitblast_apply_ite_same_length guard a
      (__pair_second divResult) hExpanded
  have hguardNe :=
    bitblast_apply_ite_cond_ne guard a
      (__pair_second divResult) hExpanded
  have heqRecNe :
      __bv_mk_bitblast_step_eq_rec divisor zero ≠
        Term.Stuck := by
    exact singleton_elim_arg_ne_stuck hguardNe
  have heqSame := eq_rec_same_length divisor zero heqRecNe
  have hzeroNe : zero ≠ Term.Stuck :=
    heqSame.syntax_right.ne_stuck
  rcases list_repeat_from_bools_context
      (Term.Boolean false) width hzeroNe with
    ⟨W, hwidth, _⟩
  have hwidth' :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (W : Int) := hwidth
  change
    term_has_non_none_type
      (SmtTerm.bvurem (__eo_to_smt a)
        (__eo_to_smt divisor)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvurem)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt divisor) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hsame.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases heqSame.syntax_left.eval hM hbNN with ⟨ys, hb⟩
  have hz :
      BitListEval M zero (List.replicate W false) := by
    unfold zero width
    rw [hwidth']
    exact list_repeat_from_bools rfl
      (by intro hh; cases hh) W
  have hxsWType :=
    bitListEval_length_eq_smt_type M hM a xs w ha haTy
  have hysWType :=
    bitListEval_length_eq_smt_type M hM divisor ys w hb hbTy
  have hysW0 := heqSame.eval_length hb hz
  have hysW : ys.length = W := by
    simpa using hysW0
  have hWw : W = w := by omega
  have hxsW : xs.length = W := by omega
  have hindices :
      BitIndexList indices 0 W := by
    unfold indices width
    rw [hwidth']
    exact generated_bit_indices W
  have hbound : bitsValue xs < 2 ^ W := by
    rw [← hxsW]
    exact bitsValue_lt xs
  rcases div_mod_impl_eval ha hb hz hxsW hysW
      hindices hbound with
    ⟨qs, rs, hdiv, hqsLen, hrsLen, hdivVal⟩
  have hrem : BitListEval M (__pair_second divResult) rs := by
    exact hdiv.second
  have hguard :
      __smtx_model_eval M (__eo_to_smt guard) =
        SmtValue.Boolean
          (bitsEq ys (List.replicate W false)) := by
    exact hb.eq_step_eval hz hysW0
  have hout :=
    ha.apply_ite_choose hguard hrem (by omega)
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_ite guard a
            (__pair_second divResult))) =
      __smtx_model_eval_bvurem
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt divisor))
  rw [hout.eval, ha.eval, hb.eval, bvurem_binary_values]
  by_cases hyzero : bitsValue ys = 0
  · have hysZero : ys = List.replicate W false := by
      apply bitsValue_inj_of_length hysW0
      rw [bitsValue_replicate_false]
      exact hyzero
    have hbits :
        bitsEq ys (List.replicate W false) = true :=
      bitsEq_eq_true_iff.mpr hysZero
    simp [hbits, hyzero, hxsW]
  · have hbits :
        bitsEq ys (List.replicate W false) = false := by
      cases h : bitsEq ys (List.replicate W false) with
      | false => rfl
      | true =>
          exfalso
          apply hyzero
          have hysZero := bitsEq_eq_true_iff.mp h
          rw [hysZero, bitsValue_replicate_false]
    have hpositive : 0 < bitsValue ys :=
      Nat.pos_of_ne_zero hyzero
    have hremVal := (hdivVal hpositive).2
    simp [hbits, hyzero, hrsLen, hremVal, hxsW]

private theorem eval_step_bvudiv
    (M : SmtModel) (hM : model_wf M)
    (a divisor : Term)
    (hExpanded :
      let width := __bv_bitwidth (__eo_typeof a)
      let zero :=
        __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) width
      __bv_bitblast_apply_ite
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__bv_mk_bitblast_step_eq_rec divisor zero))
          (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
            (Term.Boolean true) width)
          (__pair_first
            (__bv_div_mod_impl a divisor zero
              (__eo_requires (__eo_is_neg width)
                (Term.Boolean false)
                (__iota_rec
                  (__eo_list_repeat
                    (Term.UOp UserOp._at__at_TypedList_cons)
                    (Term.Numeral 0) width)
                  (Term.Numeral 0))))) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvudiv) a) divisor))) :
    __smtx_model_eval M
        (__eo_to_smt
          (let width := __bv_bitwidth (__eo_typeof a)
           let zero :=
             __eo_list_repeat (Term.UOp UserOp._at_from_bools)
               (Term.Boolean false) width
           __bv_bitblast_apply_ite
             (__eo_list_singleton_elim (Term.UOp UserOp.and)
               (__bv_mk_bitblast_step_eq_rec divisor zero))
             (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
               (Term.Boolean true) width)
             (__pair_first
               (__bv_div_mod_impl a divisor zero
                 (__eo_requires (__eo_is_neg width)
                   (Term.Boolean false)
                   (__iota_rec
                     (__eo_list_repeat
                       (Term.UOp UserOp._at__at_TypedList_cons)
                       (Term.Numeral 0) width)
                     (Term.Numeral 0))))))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvudiv) a) divisor)) := by
  let width := __bv_bitwidth (__eo_typeof a)
  let zero :=
    __eo_list_repeat (Term.UOp UserOp._at_from_bools)
      (Term.Boolean false) width
  let ones :=
    __eo_list_repeat (Term.UOp UserOp._at_from_bools)
      (Term.Boolean true) width
  let indices :=
    __eo_requires (__eo_is_neg width) (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat
          (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) width)
        (Term.Numeral 0))
  let divResult := __bv_div_mod_impl a divisor zero indices
  let guard :=
    __eo_list_singleton_elim (Term.UOp UserOp.and)
      (__bv_mk_bitblast_step_eq_rec divisor zero)
  change
    __bv_bitblast_apply_ite guard ones
        (__pair_first divResult) ≠
      Term.Stuck at hExpanded
  have hsame :=
    bitblast_apply_ite_same_length guard ones
      (__pair_first divResult) hExpanded
  have hguardNe :=
    bitblast_apply_ite_cond_ne guard ones
      (__pair_first divResult) hExpanded
  have heqRecNe :
      __bv_mk_bitblast_step_eq_rec divisor zero ≠
        Term.Stuck :=
    singleton_elim_arg_ne_stuck hguardNe
  have heqSame := eq_rec_same_length divisor zero heqRecNe
  have hzeroNe : zero ≠ Term.Stuck :=
    heqSame.syntax_right.ne_stuck
  rcases list_repeat_from_bools_context
      (Term.Boolean false) width hzeroNe with
    ⟨W, hwidth, _⟩
  have hwidth' :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (W : Int) := hwidth
  change
    term_has_non_none_type
      (SmtTerm.bvudiv (__eo_to_smt a)
        (__eo_to_smt divisor)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvudiv)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have hbNN : term_has_non_none_type (__eo_to_smt divisor) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases heqSame.syntax_left.eval hM hbNN with ⟨ys, hb⟩
  have hz :
      BitListEval M zero (List.replicate W false) := by
    unfold zero width
    rw [hwidth']
    exact list_repeat_from_bools rfl
      (by intro hh; cases hh) W
  have hones :
      BitListEval M ones (List.replicate W true) := by
    unfold ones width
    rw [hwidth']
    exact list_repeat_from_bools rfl
      (by intro hh; cases hh) W
  have hysWType :=
    bitListEval_length_eq_smt_type M hM divisor ys w hb hbTy
  have hysW0 := heqSame.eval_length hb hz
  have hysW : ys.length = W := by
    simpa using hysW0
  have hWw : W = w := by omega
  have hindices :
      BitIndexList indices 0 W := by
    unfold indices width
    rw [hwidth']
    exact generated_bit_indices W
  have hguard :
      __smtx_model_eval M (__eo_to_smt guard) =
        SmtValue.Boolean
          (bitsEq ys (List.replicate W false)) :=
    hb.eq_step_eval hz hysW0
  by_cases hWzero : W = 0
  · have hwzero : w = 0 :=
      hWw.symm.trans hWzero
    have haNe : a ≠ Term.Stuck := by
      intro ha
      subst a
      cases haTy
    have hindices0 : BitIndexList indices 0 0 := by
      simpa [hWzero] using hindices
    have hindicesNil := hindices0.eq_nil
    have hq :
        BitListEval M (__pair_first divResult) [] := by
      unfold divResult
      rw [hindicesNil]
      rw [__bv_div_mod_impl.eq_5 a divisor zero
        haNe hb.ne_stuck hz.ne_stuck]
      have hsimpa := hz
      try simp [hWzero] at hsimpa ⊢
      exact hsimpa
    have hout :=
      hones.apply_ite_choose hguard hq (by simp [hWzero])
    rcases eval_bitvec_of_type M hM a 0 (by
        simpa [hwzero] using haTy) with
      ⟨x, hx⟩
    have hxzero : x.toNat = 0 := by
      have hxlt := x.isLt
      simp at hxlt
      omega
    change
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_bitblast_apply_ite guard ones
              (__pair_first divResult))) =
        __smtx_model_eval_bvudiv
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt divisor))
    rw [hout.eval, hx, hb.eval]
    rw [hxzero]
    change
      SmtValue.Binary
          ((if bitsEq ys (List.replicate W false) = true then
              List.replicate W true else []).length : Int)
          (bitsValue
            (if bitsEq ys (List.replicate W false) = true then
              List.replicate W true else []) : Int) =
        __smtx_model_eval_bvudiv
          (SmtValue.Binary (([] : List Bool).length : Int)
            (bitsValue ([] : List Bool) : Int))
          (SmtValue.Binary (ys.length : Int)
            (bitsValue ys : Int))
    rw [bvudiv_binary_values ([] : List Bool) ys]
    have hyzero : bitsValue ys = 0 := by
      have hylt := bitsValue_lt ys
      rw [hysW, hWzero] at hylt
      simp at hylt
      omega
    simp [hyzero, hWzero]
    rfl
  · have hWpos : 0 < W := Nat.pos_of_ne_zero hWzero
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hWzero
    have haSyntax :=
      div_mod_impl_input_syntax heqSame.syntax_right
        hindices hsame.syntax_right.ne_stuck
    have haNN : term_has_non_none_type (__eo_to_smt a) := by
      unfold term_has_non_none_type
      rw [haTy]
      simp
    rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
    have hxsWType :=
      bitListEval_length_eq_smt_type M hM a xs w ha haTy
    have hxsW : xs.length = k + 1 := by omega
    have hbound : bitsValue xs < 2 ^ (k + 1) := by
      rw [← hxsW]
      exact bitsValue_lt xs
    rcases div_mod_impl_eval ha hb hz hxsW hysW
        hindices hbound with
      ⟨qs, rs, hdiv, hqsLen, hrsLen, hdivVal⟩
    have hquot :
        BitListEval M (__pair_first divResult) qs :=
      hdiv.first
    have hout :=
      hones.apply_ite_choose hguard hquot
        (by simpa using hqsLen.symm)
    change
      __smtx_model_eval M
          (__eo_to_smt
            (__bv_bitblast_apply_ite guard ones
              (__pair_first divResult))) =
        __smtx_model_eval_bvudiv
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt divisor))
    rw [hout.eval, ha.eval, hb.eval, bvudiv_binary_values]
    by_cases hyzero : bitsValue ys = 0
    · have hysZero : ys = List.replicate (k + 1) false := by
        apply bitsValue_inj_of_length hysW0
        rw [bitsValue_replicate_false]
        exact hyzero
      have hbits :
          bitsEq ys (List.replicate (k + 1) false) = true :=
        bitsEq_eq_true_iff.mpr hysZero
      simp [hbits, hyzero, bitsValue_replicate_true, hxsW]
    · have hbits :
          bitsEq ys (List.replicate (k + 1) false) = false := by
        cases h : bitsEq ys (List.replicate (k + 1) false) with
        | false => rfl
        | true =>
            exfalso
            apply hyzero
            have hysZero := bitsEq_eq_true_iff.mp h
            rw [hysZero, bitsValue_replicate_false]
      have hpositive : 0 < bitsValue ys :=
        Nat.pos_of_ne_zero hyzero
      have hquotVal := (hdivVal hpositive).1
      simp [hbits, hyzero, hqsLen, hquotVal, hxsW]

private theorem getLsbD_ofInt_canonical
    (W i : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    (BitVec.ofInt W p).getLsbD i = p.toNat.testBit i := by
  simp [BitVec.getLsbD, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt hp0 hp1]

private theorem const_bit_term_eq
    (W i : Nat) (p : Int) (hp0 : 0 ≤ p) :
    __eo_eq
        (__eo_extract (Term.Binary (W : Int) p)
          (Term.Numeral (i : Int)) (Term.Numeral (i : Int)))
        (Term.Binary 1 1) =
      Term.Boolean (p.toNat.testBit i) := by
  have hext :
      __eo_extract (Term.Binary (W : Int) p)
          (Term.Numeral (i : Int)) (Term.Numeral (i : Int)) =
        __eo_mk_binary 1
          (native_binary_extract (W : Int) p (i : Int) (i : Int)) := by
    simp only [__eo_extract]
    have hi0 : ¬ ((i : Int) < 0) := by omega
    simp only [native_zlt, native_or, native_zplus, native_zneg]
    rw [show decide ((i : Int) < 0) = false by simp [hi0]]
    simp only [Bool.false_or, native_ite]
    simp [show (i : Int) + -(i : Int) = 0 by omega]
  rw [hext]
  rw [show
    __eo_mk_binary 1
        (native_binary_extract (W : Int) p (i : Int) (i : Int)) =
      Term.Binary 1
        (native_mod_total
          (native_binary_extract (W : Int) p (i : Int) (i : Int))
          (native_int_pow2 1)) by
    rfl]
  have hsem := extract_bit_binary_eval (W : Int) p i hp0
  have heq := congrArg
    (fun v => __smtx_model_eval_eq v (SmtValue.Binary 1 1)) hsem
  try dsimp only at heq
  rw [bv1_eq_one] at heq
  simp only [__smtx_model_eval_extract, native_zplus, native_zneg,
    native_nat_to_int] at heq
  have hone : Int.ofNat i + 1 + -Int.ofNat i = 1 := by omega
  simp only [hone] at heq
  simpa [__eo_eq, __smtx_model_eval_eq, native_veq, native_teq,
    eq_comm] using heq

private theorem const_rec_eval
    (M : SmtModel) (W : Nat) (p : Int) (hp0 : 0 ≤ p)
    {indices : Term} {start n : Nat}
    (hindices : BitIndexList indices start n) :
    BitListEval M
      (__bv_const_to_bitlist_rec (Term.Binary (W : Int) p) indices)
      (reifyBits p.toNat start n) := by
  induction hindices with
  | nil start =>
    rw [__bv_const_to_bitlist_rec.eq_2 _
      (by intro h; cases h)]
    exact BitListEval.nil
  | cons start tail n htail ih =>
    rw [__bv_const_to_bitlist_rec.eq_3 _
      (Term.Numeral (start : Int)) tail
      (by intro h; cases h)]
    let bit :=
      __eo_eq
        (__eo_extract (Term.Binary (W : Int) p)
          (Term.Numeral (start : Int))
          (Term.Numeral (start : Int)))
        (Term.Binary 1 1)
    have hbitEq :
        bit = Term.Boolean (p.toNat.testBit start) :=
      const_bit_term_eq W start p hp0
    have hbitEval :
        __smtx_model_eval M (__eo_to_smt bit) =
          SmtValue.Boolean (p.toNat.testBit start) := by
      rw [hbitEq]
      rfl
    rw [mk_apply_eq (by intro h; cases h)
      (term_ne_stuck_of_eval_boolean hbitEval)]
    rw [mk_apply_eq (by intro h; cases h)
      (BitListEval.ne_stuck ih)]
    simpa [bit, reifyBits] using
      BitListEval.cons bit
        (__bv_const_to_bitlist_rec (Term.Binary (W : Int) p) tail)
        (p.toNat.testBit start)
        (reifyBits p.toNat (start + 1) n)
        hbitEval ih

private theorem var_rec_eval
    (M : SmtModel) (a : Term) (W : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (ha :
      __smtx_model_eval M (__eo_to_smt a) =
        SmtValue.Binary (W : Int) p)
    {indices : Term} {start n : Nat}
    (hindices : BitIndexList indices start n) :
    BitListEval M
      (__bv_mk_bitblast_step_var_rec a indices)
      (reifyBits p.toNat start n) := by
  have haNe : a ≠ Term.Stuck := by
    intro h
    subst a
    cases ha
  induction hindices with
  | nil start =>
    rw [__bv_mk_bitblast_step_var_rec.eq_2 a haNe]
    exact BitListEval.nil
  | cons start tail n htail ih =>
    rw [__bv_mk_bitblast_step_var_rec.eq_3 a
      (Term.Numeral (start : Int)) tail haNe]
    have hbit := eval_at_bit M a W start p hp0 hp1 ha
    rw [getLsbD_ofInt_canonical W start p hp0 hp1] at hbit
    rw [mk_apply_eq (by intro h; cases h)
      (BitListEval.ne_stuck ih)]
    simpa [reifyBits] using
      BitListEval.cons
        (Term.Apply
          (Term.UOp1 UserOp1._at_bit
            (Term.Numeral (start : Int))) a)
        (__bv_mk_bitblast_step_var_rec a tail)
        (p.toNat.testBit start)
        (reifyBits p.toNat (start + 1) n)
        hbit ih

private theorem var_rec_indices_ne_stuck
    {a indices : Term}
    (h : __bv_mk_bitblast_step_var_rec a indices ≠ Term.Stuck) :
    indices ≠ Term.Stuck := by
  intro hi
  subst indices
  cases a <;> simp_all [__bv_mk_bitblast_step_var_rec]

private theorem iota_indices_ne_stuck
    {indices start : Term}
    (h : __iota_rec indices start ≠ Term.Stuck) :
    indices ≠ Term.Stuck := by
  intro hi
  subst indices
  cases start <;> simp_all [__iota_rec]

private theorem bitwidth_context
    {ty : Term} (h : __bv_bitwidth ty ≠ Term.Stuck) :
    ∃ width, ty =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  by_cases hform :
      ∃ width, ty =
        Term.Apply (Term.UOp UserOp.BitVec) width
  · exact hform
  · exfalso
    apply h
    exact __bv_bitwidth.eq_2 ty (by
      intro width hw
      exact hform ⟨width, hw⟩)

private theorem typed_list_repeat_context
    (n : Term)
    (h :
      __eo_list_repeat
          (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) n ≠
        Term.Stuck) :
    ∃ W : Nat, n = Term.Numeral (W : Int) := by
  cases n with
  | Numeral i =>
    rw [__eo_list_repeat.eq_3 _ _ i
      (by intro hh; cases hh) (by intro hh; cases hh)] at h
    by_cases hi : i < 0
    · simp [native_ite, native_zlt, hi] at h
    · refine ⟨i.toNat, ?_⟩
      congr 1
      exact (Int.toNat_of_nonneg (Int.le_of_not_gt hi)).symm
  | _ =>
    exfalso
    apply h
    exact __eo_list_repeat.eq_4 _ _ _
      (by intro hh; cases hh) (by intro hh; cases hh)
      (by intro i hi; cases hi)

private theorem eo_is_bin_cases {a : Term} (ha : a ≠ Term.Stuck) :
    __eo_is_bin a = Term.Boolean true ∨
      __eo_is_bin a = Term.Boolean false := by
  cases a <;>
    simp_all [__eo_is_bin, __eo_is_bin_internal,
      SmtEval.native_and, native_not, native_teq, reduceCtorEq]

private theorem eo_is_bin_eq_true {a : Term}
    (h : __eo_is_bin a = Term.Boolean true) :
    ∃ w p, a = Term.Binary w p := by
  cases a <;>
    simp_all [__eo_is_bin, __eo_is_bin_internal,
      SmtEval.native_and, native_not, native_teq, reduceCtorEq]

private theorem eo_ite_boolean_true (x y : Term) :
    __eo_ite (Term.Boolean true) x y = x := by
  simp [__eo_ite, native_teq, native_ite]

private theorem eo_ite_boolean_false (x y : Term) :
    __eo_ite (Term.Boolean false) x y = y := by
  simp [__eo_ite, native_teq, native_ite]

private theorem eval_step_default_var
    (M : SmtModel) (hM : model_wf M)
    (a : Term)
    (hbin : __eo_is_bin a = Term.Boolean false)
    (hne :
      (let width := __bv_bitwidth (__eo_typeof a)
       let len := __eo_len a
       __eo_ite (__eo_is_bin a)
         (__bv_const_to_bitlist_rec a
           (__eo_requires (__eo_is_neg len) (Term.Boolean false)
             (__iota_rec
               (__eo_list_repeat
                 (Term.UOp UserOp._at__at_TypedList_cons)
                 (Term.Numeral 0) len)
               (Term.Numeral 0))))
         (__bv_mk_bitblast_step_var_rec a
           (__eo_requires (__eo_is_neg width) (Term.Boolean false)
             (__iota_rec
               (__eo_list_repeat
                 (Term.UOp UserOp._at__at_TypedList_cons)
                 (Term.Numeral 0) width)
               (Term.Numeral 0))))) ≠
        Term.Stuck)
    (hnn : term_has_non_none_type (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (let width := __bv_bitwidth (__eo_typeof a)
           let len := __eo_len a
           __eo_ite (__eo_is_bin a)
             (__bv_const_to_bitlist_rec a
               (__eo_requires (__eo_is_neg len) (Term.Boolean false)
                 (__iota_rec
                   (__eo_list_repeat
                     (Term.UOp UserOp._at__at_TypedList_cons)
                     (Term.Numeral 0) len)
                   (Term.Numeral 0))))
             (__bv_mk_bitblast_step_var_rec a
               (__eo_requires (__eo_is_neg width)
                 (Term.Boolean false)
                 (__iota_rec
                   (__eo_list_repeat
                     (Term.UOp UserOp._at__at_TypedList_cons)
                     (Term.Numeral 0) width)
                   (Term.Numeral 0)))))) =
      __smtx_model_eval M (__eo_to_smt a) := by
  simp only at hne ⊢
  rw [hbin, eo_ite_boolean_false] at hne ⊢
  let width := __bv_bitwidth (__eo_typeof a)
  let indices :=
    __eo_requires (__eo_is_neg width) (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat
          (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) width)
        (Term.Numeral 0))
  have hindicesNe : indices ≠ Term.Stuck :=
    var_rec_indices_ne_stuck hne
  have hiotaNe :
      __iota_rec
          (__eo_list_repeat
            (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) width)
          (Term.Numeral 0) ≠
        Term.Stuck :=
    requires_result_ne_stuck hindicesNe
  have hrepeatNe :
      __eo_list_repeat
          (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) width ≠
        Term.Stuck :=
    iota_indices_ne_stuck hiotaNe
  rcases typed_list_repeat_context width hrepeatNe with
    ⟨W, hwidth⟩
  have hbitwidthNe :
      __bv_bitwidth (__eo_typeof a) ≠ Term.Stuck := by
    change width ≠ Term.Stuck
    rw [hwidth]
    intro h
    cases h
  rcases bitwidth_context hbitwidthNe with
    ⟨widthTerm, haEoTy⟩
  have hwidthTerm :
      widthTerm = Term.Numeral (W : Int) := by
    change __bv_bitwidth (__eo_typeof a) =
      Term.Numeral (W : Int) at hwidth
    rw [haEoTy] at hwidth
    exact hwidth
  rw [hwidthTerm] at haEoTy
  have haTy :
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec W := by
    calc
      _ = __eo_to_smt_type (__eo_typeof a) :=
        TranslationProofs.eo_to_smt_typeof_matches_translation a hnn
      _ = _ := by
        rw [haEoTy]
        rfl
  rcases eval_bitvec_of_type M hM a W haTy with ⟨x, hx⟩
  have hout :=
    var_rec_eval M a W (x.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)
      hx (generated_bit_indices W)
  change
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_var_rec a indices)) =
      __smtx_model_eval M (__eo_to_smt a)
  rw [show indices =
      __eo_requires (__eo_is_neg (Term.Numeral (W : Int)))
        (Term.Boolean false)
        (__iota_rec
          (__eo_list_repeat
            (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) (Term.Numeral (W : Int)))
          (Term.Numeral 0)) by
    simp only [indices, width]
    change __bv_bitwidth (__eo_typeof a) =
      Term.Numeral (W : Int) at hwidth
    rw [hwidth]]
  rw [hout.eval, hx]
  simp [bitsValue_reifyBits x.toNat W x.isLt]

private theorem eval_step_default_const
    (M : SmtModel) (w p : Int)
    (hne :
      (let width :=
        __bv_bitwidth (__eo_typeof (Term.Binary w p))
       let len := __eo_len (Term.Binary w p)
       __eo_ite (__eo_is_bin (Term.Binary w p))
         (__bv_const_to_bitlist_rec (Term.Binary w p)
           (__eo_requires (__eo_is_neg len) (Term.Boolean false)
             (__iota_rec
               (__eo_list_repeat
                 (Term.UOp UserOp._at__at_TypedList_cons)
                 (Term.Numeral 0) len)
               (Term.Numeral 0))))
         (__bv_mk_bitblast_step_var_rec (Term.Binary w p)
           (__eo_requires (__eo_is_neg width) (Term.Boolean false)
             (__iota_rec
               (__eo_list_repeat
                 (Term.UOp UserOp._at__at_TypedList_cons)
                 (Term.Numeral 0) width)
               (Term.Numeral 0))))) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt (Term.Binary w p))) :
    __smtx_model_eval M
        (__eo_to_smt
          (let width :=
            __bv_bitwidth (__eo_typeof (Term.Binary w p))
           let len := __eo_len (Term.Binary w p)
           __eo_ite (__eo_is_bin (Term.Binary w p))
             (__bv_const_to_bitlist_rec (Term.Binary w p)
               (__eo_requires (__eo_is_neg len)
                 (Term.Boolean false)
                 (__iota_rec
                   (__eo_list_repeat
                     (Term.UOp UserOp._at__at_TypedList_cons)
                     (Term.Numeral 0) len)
                   (Term.Numeral 0))))
             (__bv_mk_bitblast_step_var_rec (Term.Binary w p)
               (__eo_requires (__eo_is_neg width)
                 (Term.Boolean false)
                 (__iota_rec
                   (__eo_list_repeat
                     (Term.UOp UserOp._at__at_TypedList_cons)
                     (Term.Numeral 0) width)
                   (Term.Numeral 0)))))) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Binary w p)) := by
  have hwell :=
    TranslationProofs.smtx_binary_well_formed_of_non_none w p hnn
  have hw0 : 0 ≤ w := by
    simpa [native_zleq] using hwell.1
  let W := w.toNat
  have hw : (W : Int) = w := by
    exact Int.toNat_of_nonneg hw0
  have hpow :
      native_int_pow2 w = ((2 ^ W : Nat) : Int) := by
    rw [← hw]
    exact native_int_pow2_nat W
  have hcanon :
      p = native_mod_total p (native_int_pow2 w) := by
    simpa [native_zeq] using hwell.2
  have hpowPos : (0 : Int) < native_int_pow2 w := by
    rw [hpow]
    exact_mod_cast Nat.two_pow_pos W
  have hp0 : 0 ≤ p := by
    rw [hcanon]
    exact Int.emod_nonneg _ (Int.ne_of_gt hpowPos)
  have hp1 : p < (2 : Int) ^ W := by
    rw [hcanon, hpow]
    have hlt :=
      Int.emod_lt_of_pos p
        (by exact_mod_cast Nat.two_pow_pos W :
          (0 : Int) < (2 ^ W : Nat))
    exact_mod_cast hlt
  have hout :=
    const_rec_eval M W p hp0 (generated_bit_indices W)
  simp only at hne ⊢
  rw [show __eo_is_bin (Term.Binary w p) =
      Term.Boolean true by
    simp [__eo_is_bin, __eo_is_bin_internal,
      SmtEval.native_and, native_not, native_teq, reduceCtorEq]]
  rw [eo_ite_boolean_true]
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_const_to_bitlist_rec (Term.Binary w p)
            (__eo_requires (__eo_is_neg (Term.Numeral w))
              (Term.Boolean false)
              (__iota_rec
                (__eo_list_repeat
                  (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral 0) (Term.Numeral w))
                (Term.Numeral 0))))) =
      __smtx_model_eval M (__eo_to_smt (Term.Binary w p))
  rw [← hw]
  rw [hout.eval]
  change
    SmtValue.Binary
        ((reifyBits p.toNat 0 W).length : Int)
        (bitsValue (reifyBits p.toNat 0 W) : Int) =
      SmtValue.Binary (W : Int) p
  rw [reifyBits_length, bitsValue_reifyBits p.toNat W
    (by
      have hpcast : (p.toNat : Int) = p :=
        Int.toNat_of_nonneg hp0
      rw [← hpcast] at hp1
      exact_mod_cast hp1)]
  congr 1
  exact Int.toNat_of_nonneg hp0

private theorem eval_step_default
    (M : SmtModel) (hM : model_wf M)
    (a : Term)
    (hne :
      (let width := __bv_bitwidth (__eo_typeof a)
       let len := __eo_len a
       __eo_ite (__eo_is_bin a)
         (__bv_const_to_bitlist_rec a
           (__eo_requires (__eo_is_neg len) (Term.Boolean false)
             (__iota_rec
               (__eo_list_repeat
                 (Term.UOp UserOp._at__at_TypedList_cons)
                 (Term.Numeral 0) len)
               (Term.Numeral 0))))
         (__bv_mk_bitblast_step_var_rec a
           (__eo_requires (__eo_is_neg width) (Term.Boolean false)
             (__iota_rec
               (__eo_list_repeat
                 (Term.UOp UserOp._at__at_TypedList_cons)
                 (Term.Numeral 0) width)
               (Term.Numeral 0))))) ≠
        Term.Stuck)
    (hnn : term_has_non_none_type (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (let width := __bv_bitwidth (__eo_typeof a)
           let len := __eo_len a
           __eo_ite (__eo_is_bin a)
             (__bv_const_to_bitlist_rec a
               (__eo_requires (__eo_is_neg len)
                 (Term.Boolean false)
                 (__iota_rec
                   (__eo_list_repeat
                     (Term.UOp UserOp._at__at_TypedList_cons)
                     (Term.Numeral 0) len)
                   (Term.Numeral 0))))
             (__bv_mk_bitblast_step_var_rec a
               (__eo_requires (__eo_is_neg width)
                 (Term.Boolean false)
                 (__iota_rec
                   (__eo_list_repeat
                     (Term.UOp UserOp._at__at_TypedList_cons)
                     (Term.Numeral 0) width)
                   (Term.Numeral 0)))))) =
      __smtx_model_eval M (__eo_to_smt a) := by
  have haNe : a ≠ Term.Stuck := by
    intro ha
    subst a
    exact hne rfl
  rcases eo_is_bin_cases haNe with hbin | hbin
  · rcases eo_is_bin_eq_true hbin with ⟨w, p, ha⟩
    subst a
    exact eval_step_default_const M w p hne hnn
  · exact eval_step_default_var M hM a hbin hne hnn

private def shiftConstBits (width : Term) : Term :=
  let c := __eo_to_bin width width
  let len := __eo_len c
  __bv_const_to_bitlist_rec c
    (__eo_requires (__eo_is_neg len) (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat
          (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) len)
        (Term.Numeral 0)))

private def shiftGuard (amount width : Term) : Term :=
  __bv_bitblast_ult amount (shiftConstBits width) (Term.Boolean false)

private def shlBlast (a amount width : Term) : Term :=
  __bv_bitblast_apply_ite (shiftGuard amount width)
    (__bv_mk_bitblast_step_shl_rec a amount (Term.Numeral 0)
      (shiftLszTerm width))
    (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
      (Term.Boolean false) width)

private def shrBlast (a amount width sign : Term) : Term :=
  __bv_bitblast_apply_ite (shiftGuard amount width)
    (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
      (shiftLszTerm width) sign)
    (__eo_list_repeat (Term.UOp UserOp._at_from_bools) sign width)

private theorem to_bin_width_self_eq
    (W : Nat)
    (h :
      __eo_to_bin (Term.Numeral (W : Int))
          (Term.Numeral (W : Int)) ≠
        Term.Stuck) :
    __eo_to_bin (Term.Numeral (W : Int))
        (Term.Numeral (W : Int)) =
      Term.Binary (W : Int) (W : Int) := by
  have hbound : (W : Int) ≤ 4294967296 := by
    by_cases hb : (W : Int) ≤ 4294967296
    · exact hb
    · exfalso
      apply h
      simp [__eo_to_bin, native_zleq, native_ite, hb]
  have hmod :
      native_mod_total (W : Int)
          (native_int_pow2 (W : Int)) =
        (W : Int) := by
    rw [native_int_pow2_nat]
    change
      (W : Int) % ((2 ^ W : Nat) : Int) = (W : Int)
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg W
    · exact_mod_cast Nat.lt_two_pow_self
  unfold __eo_to_bin
  simp only [native_zleq]
  rw [show decide ((W : Int) ≤ 4294967296) = true by
    exact decide_eq_true hbound]
  simp [__eo_mk_binary, native_zleq, native_ite, hmod]

private theorem shiftConstBits_eval
    (M : SmtModel) (W : Nat)
    (hne :
      shiftConstBits (Term.Numeral (W : Int)) ≠ Term.Stuck) :
    BitListEval M
      (shiftConstBits (Term.Numeral (W : Int)))
      (reifyBits W 0 W) := by
  have hbinNe :
      __eo_to_bin (Term.Numeral (W : Int))
          (Term.Numeral (W : Int)) ≠
        Term.Stuck := by
    apply const_rec_const_ne
      (indices :=
        __eo_requires
          (__eo_is_neg
            (__eo_len
              (__eo_to_bin (Term.Numeral (W : Int))
                (Term.Numeral (W : Int)))))
          (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat
              (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0)
              (__eo_len
                (__eo_to_bin (Term.Numeral (W : Int))
                  (Term.Numeral (W : Int)))))
            (Term.Numeral 0)))
    simpa [shiftConstBits] using hne
  have hbin := to_bin_width_self_eq W hbinNe
  have hout :=
    const_rec_eval M W (W : Int) (Int.natCast_nonneg W)
      (generated_bit_indices W)
  have hsimpa := hout
  try simp [shiftConstBits, hbin] at hsimpa ⊢
  exact hsimpa

private theorem eval_step_bvshl
    (M : SmtModel) (hM : model_wf M)
    (a amount : Term)
    (hne :
      shlBlast a amount (__bv_bitwidth (__eo_typeof a)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) amount))) :
    __smtx_model_eval M
        (__eo_to_smt
          (shlBlast a amount (__bv_bitwidth (__eo_typeof a)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) amount)) := by
  change term_has_non_none_type
      (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt amount)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvshl)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt amount)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haTy, hamountTy⟩
  let width := __bv_bitwidth (__eo_typeof a)
  change shlBlast a amount width ≠ Term.Stuck at hne
  change
    __smtx_model_eval M (__eo_to_smt (shlBlast a amount width)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) amount))
  have hsame :
      BitListsSameLength
        (__bv_mk_bitblast_step_shl_rec a amount (Term.Numeral 0)
          (shiftLszTerm width))
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) width) := by
    apply bitblast_apply_ite_same_length
    simpa [shlBlast, width] using hne
  have hzeroNe :
      __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) width ≠
        Term.Stuck :=
    hsame.syntax_right.ne_stuck
  rcases list_repeat_from_bools_context
      (Term.Boolean false) width hzeroNe with
    ⟨K, hwidth, _⟩
  have hwidthNe : __bv_bitwidth (__eo_typeof a) ≠ Term.Stuck := by
    change width ≠ Term.Stuck
    rw [hwidth]
    intro h
    cases h
  rcases bitwidth_context hwidthNe with ⟨widthTerm, haEoTy⟩
  have hwidthTerm : widthTerm = Term.Numeral (K : Int) := by
    change __bv_bitwidth (__eo_typeof a) =
      Term.Numeral (K : Int) at hwidth
    rw [haEoTy] at hwidth
    exact hwidth
  rw [hwidthTerm] at haEoTy
  have haTyK :
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec K := by
    calc
      _ = __eo_to_smt_type (__eo_typeof a) :=
        TranslationProofs.eo_to_smt_typeof_matches_translation a
          (by
            rw [haTy]
            simp)
      _ = _ := by
        rw [haEoTy]
        simp [__eo_to_smt_type, native_zleq, native_ite,
          native_int_to_nat]
  have hKW : K = W := by
    rw [haTy] at haTyK
    injection haTyK with h
    exact h.symm
  subst K
  change width = Term.Numeral (W : Int) at hwidth
  rw [hwidth] at hne hsame hzeroNe ⊢
  let L := barrelWidth W
  have hlsz :
      shiftLszTerm (Term.Numeral (W : Int)) =
        Term.Numeral (L : Int) := by
    exact shiftLszTerm_numeral W
  let const := shiftConstBits (Term.Numeral (W : Int))
  have hcondNe :
      shiftGuard amount (Term.Numeral (W : Int)) ≠ Term.Stuck := by
    apply bitblast_apply_ite_cond_ne
      (a :=
        __bv_mk_bitblast_step_shl_rec a amount (Term.Numeral 0)
          (shiftLszTerm (Term.Numeral (W : Int))))
      (b :=
        __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) (Term.Numeral (W : Int)))
    simpa [shlBlast] using hne
  have hultNe :
      __bv_bitblast_ult amount const (Term.Boolean false) ≠
        Term.Stuck := by
    simpa [shiftGuard, const] using hcondNe
  rcases bitblast_ult_shape amount const (Term.Boolean false) hultNe with
    ⟨abit, atail, cbit, ctail, hamountShape, hconstShape, htails⟩
  have hamountSyntax : BitListSyntax amount := by
    rw [hamountShape]
    exact BitListSyntax.cons abit atail htails.syntax_left
  have hconstSyntax : BitListSyntax const := by
    rw [hconstShape]
    exact BitListSyntax.cons cbit ctail htails.syntax_right
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hamountNN : term_has_non_none_type (__eo_to_smt amount) := by
    unfold term_has_non_none_type
    rw [hamountTy]
    simp
  have haSyntax : BitListSyntax a := by
    have htrueSyntax := hsame.syntax_left
    rw [hlsz] at htrueSyntax
    by_cases hL0 : L = 0
    ·
      rw [hL0] at htrueSyntax
      change
        BitListSyntax
          (__bv_mk_bitblast_step_shl_rec a amount
            (Term.Numeral 0) (Term.Numeral 0)) at htrueSyntax
      have haNe : a ≠ Term.Stuck :=
        shl_rec_current_ne a amount (Term.Numeral 0)
          (Term.Numeral 0) htrueSyntax.ne_stuck
      have hrecEq :
          __bv_mk_bitblast_step_shl_rec a amount
              (Term.Numeral 0) (Term.Numeral 0) =
            a := by
        rw [__bv_mk_bitblast_step_shl_rec.eq_5 a amount
          (Term.Numeral 0) (Term.Numeral 0)
          haNe
          hamountSyntax.ne_stuck
          (by intro hs; cases hs) (by intro hs; cases hs)]
        simp [__eo_eq, native_teq, __eo_ite, native_ite]
      rw [hrecEq] at htrueSyntax
      exact htrueSyntax
    · apply shl_rec_zero_current_syntax a amount L (by omega)
        hamountSyntax.ne_stuck
        ⟨abit, atail, hamountShape⟩
      exact htrueSyntax.ne_stuck
  rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
  rcases hamountSyntax.eval hM hamountNN with ⟨ys, hamount⟩
  have hxW := bitListEval_length_eq_smt_type M hM a xs W ha haTy
  have hyW :=
    bitListEval_length_eq_smt_type M hM amount ys W hamount hamountTy
  have hW : 0 < W := by
    have hyPos : 0 < ys.length := by
      rw [hamountShape] at hamount
      cases hamount
      simp
    rw [← hyW]
    exact hyPos
  have hconst :
      BitListEval M const (reifyBits W 0 W) :=
    shiftConstBits_eval M W hconstSyntax.ne_stuck
  have hconstLen : (reifyBits W 0 W).length = W :=
    reifyBits_length W 0 W
  have hconstValue : bitsValue (reifyBits W 0 W) = W :=
    bitsValue_reifyBits W W Nat.lt_two_pow_self
  have htailLen :
      ys.tail.length = (reifyBits W 0 W).tail.length := by
    simp only [List.length_tail]
    omega
  have hguard :
      __smtx_model_eval M
          (__eo_to_smt
            (shiftGuard amount (Term.Numeral (W : Int)))) =
        SmtValue.Boolean (decide (bitsValue ys < W)) := by
    rw [hamountShape] at hamount
    rw [hconstShape] at hconst
    have hyNonempty : ys ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hyW]
      exact hW
    have hcNonempty : reifyBits W 0 W ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hconstLen]
      exact hW
    rw [← List.cons_head_tail hyNonempty] at hamount
    rw [← List.cons_head_tail hcNonempty] at hconst
    have hg :=
      bitblast_ult_eval (a := amount) (b := const)
        (orEqual := false) hamount hconst htailLen
    rw [List.cons_head_tail hyNonempty,
      List.cons_head_tail hcNonempty] at hg
    have hfullLen : ys.length = (reifyBits W 0 W).length := by
      rw [hyW, hconstLen]
    rw [ultBits_spec _ _ false hfullLen, hconstValue] at hg
    rw [← hamountShape, ← hconstShape] at hg
    simpa [shiftGuard, const] using hg
  have hzero :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) (Term.Numeral (W : Int)))
        (List.replicate W false) := by
    exact list_repeat_from_bools rfl (by intro h; cases h) W
  have htrue :
      BitListEval M
        (__bv_mk_bitblast_step_shl_rec a amount (Term.Numeral 0)
          (shiftLszTerm (Term.Numeral (W : Int))))
        (shlBarrelBits xs 0 ys L) := by
    rw [hlsz]
    have hsimpa :=
      shl_rec_eval ha hamount 0 L W hxW
        (by rw [hyW]; exact barrelWidth_le W hW)
        (by
          intro j hj
          simpa using barrelWidth_pow_le W hW j hj)
    try simp only [Nat.zero_add] at hsimpa ⊢
    exact hsimpa
  have htrueLen : (shlBarrelBits xs 0 ys L).length = W :=
    shlBarrelBits_length xs ys 0 L W hxW
      (by rw [hyW]; exact barrelWidth_le W hW)
      (by
        intro j hj
        simpa using barrelWidth_pow_le W hW j hj)
  have hout :=
    htrue.apply_ite hguard hzero (by simp [htrueLen])
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_ite
            (shiftGuard amount (Term.Numeral (W : Int)))
            (__bv_mk_bitblast_step_shl_rec a amount (Term.Numeral 0)
              (shiftLszTerm (Term.Numeral (W : Int))))
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              (Term.Boolean false) (Term.Numeral (W : Int))))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) amount))
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_ite
            (shiftGuard amount (Term.Numeral (W : Int)))
            (__bv_mk_bitblast_step_shl_rec a amount (Term.Numeral 0)
              (shiftLszTerm (Term.Numeral (W : Int))))
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              (Term.Boolean false) (Term.Numeral (W : Int))))) =
      __smtx_model_eval_bvshl
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt amount))
  by_cases hy : bitsValue ys < W
  · have htake : bitsValue (ys.take L) = bitsValue ys := by
      rw [bitsValue_take_mod ys L (by rw [hyW]; exact barrelWidth_le W hW)]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy
        (le_pow_barrelWidth W hW))]
    have hval := shlBarrelBits_value xs ys 0 L W hxW
      (by rw [hyW]; exact barrelWidth_le W hW)
      (by
        intro j hj
        simpa using barrelWidth_pow_le W hW j hj)
    simp [htake] at hval
    have hselected :
        List.zipWith
            (fun x y =>
              if decide (bitsValue ys < W) = true then x else y)
            (shlBarrelBits xs 0 ys L) (List.replicate W false) =
          shlBarrelBits xs 0 ys L := by
      rw [show decide (bitsValue ys < W) = true by
        exact decide_eq_true hy]
      simp only [if_true]
      exact zipWith_left_of_length _ _
        (by simp [htrueLen])
    have hpayload :
        native_mod_total
            (native_zmult (bitsValue xs : Int)
              (native_int_pow2 (bitsValue ys : Int)))
            (native_int_pow2 (xs.length : Int)) =
          (bitsValue (shlBarrelBits xs 0 ys L) : Int) := by
      rw [native_int_pow2_nat, native_int_pow2_nat]
      simp only [native_zmult]
      rw [show
        (bitsValue xs : Int) * ((2 ^ bitsValue ys : Nat) : Int) =
          ((bitsValue xs * 2 ^ bitsValue ys : Nat) : Int) by
        norm_cast]
      rw [native_mod_nat, hxW, hval]
    have hpayloadW :
        native_mod_total
            (native_zmult (bitsValue xs : Int)
              (native_int_pow2 (bitsValue ys : Int)))
            (native_int_pow2 (W : Int)) =
          (bitsValue (shlBarrelBits xs 0 ys L) : Int) := by
      simpa only [hxW] using hpayload
    rw [hout.eval, ha.eval, hamount.eval]
    simp only [__smtx_model_eval_bvshl]
    rw [hselected, htrueLen, hxW, hpayloadW]
  · have hval : bitsValue (List.replicate W false) = 0 :=
      bitsValue_replicate_false W
    have hdvd : 2 ^ W ∣ bitsValue xs * 2 ^ bitsValue ys := by
      exact Nat.dvd_mul_left_of_dvd
        (Nat.pow_dvd_pow 2 (by omega)) (bitsValue xs)
    have hselected :
        List.zipWith
            (fun x y =>
              if decide (bitsValue ys < W) = true then x else y)
            (shlBarrelBits xs 0 ys L) (List.replicate W false) =
          List.replicate W false := by
      rw [show decide (bitsValue ys < W) = false by
        exact decide_eq_false hy]
      simp only [Bool.false_eq_true, if_false]
      exact zipWith_right_of_length _ _
        (by simp [htrueLen])
    have hpayload :
        native_mod_total
            (native_zmult (bitsValue xs : Int)
              (native_int_pow2 (bitsValue ys : Int)))
            (native_int_pow2 (xs.length : Int)) =
          0 := by
      rw [native_int_pow2_nat, native_int_pow2_nat]
      simp only [native_zmult]
      rw [show
        (bitsValue xs : Int) * ((2 ^ bitsValue ys : Nat) : Int) =
          ((bitsValue xs * 2 ^ bitsValue ys : Nat) : Int) by
        norm_cast]
      rw [native_mod_nat, hxW, Nat.mod_eq_zero_of_dvd hdvd]
      change (0 : Int) = 0
      rfl
    have hpayloadW :
        native_mod_total
            (native_zmult (bitsValue xs : Int)
              (native_int_pow2 (bitsValue ys : Int)))
            (native_int_pow2 (W : Int)) =
          0 := by
      simpa only [hxW] using hpayload
    rw [hout.eval, ha.eval, hamount.eval]
    simp only [__smtx_model_eval_bvshl]
    rw [hselected, List.length_replicate, hxW, hval, hpayloadW]
    rfl

private theorem bvlshr_binary_values (xs ys : List Bool) :
    __smtx_model_eval_bvlshr
        (SmtValue.Binary (xs.length : Int) (bitsValue xs : Int))
        (SmtValue.Binary (ys.length : Int) (bitsValue ys : Int)) =
      SmtValue.Binary (xs.length : Int)
        (bitsValue xs / 2 ^ bitsValue ys : Nat) := by
  simp only [__smtx_model_eval_bvlshr, SmtEval.native_mod_total,
    SmtEval.native_div_total]
  rw [native_int_pow2_nat, native_int_pow2_nat]
  norm_cast
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bitsValue_lt xs)

private theorem bvnot_binary_values (xs : List Bool) :
    __smtx_model_eval_bvnot
        (SmtValue.Binary (xs.length : Int) (bitsValue xs : Int)) =
      SmtValue.Binary (xs.length : Int)
        (bitsValue (xs.map (!·)) : Int) := by
  simp only [__smtx_model_eval_bvnot, native_binary_not,
    native_zplus, native_zneg]
  rw [native_int_pow2_nat, bitsValue_map_not]
  have hlt := bitsValue_lt xs
  have hltI :
      (↑(bitsValue xs) : Int) < (↑(2 ^ xs.length) : Int) := by
    exact_mod_cast hlt
  have hnonneg :
      0 ≤ (↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1) := by
    omega
  have hupper :
      (↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1) <
        (↑(2 ^ xs.length) : Int) := by
    have hp := Nat.two_pow_pos xs.length
    omega
  congr 1
  change
    ((↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1)) %
        (↑(2 ^ xs.length) : Int) =
      (↑(2 ^ xs.length - 1 - bitsValue xs) : Int)
  rw [Int.emod_eq_of_lt hnonneg hupper]
  norm_cast
  omega

private theorem extractLsb_sign_bit_bitblast
    {W : Nat} {x : BitVec W} (hW : 0 < W) :
    x.extractLsb' (W - 1) 1 = BitVec.fill 1 x.msb := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  rw [BitVec.getElem_extractLsb', BitVec.getElem_fill]
  simp only [Nat.add_zero]
  exact (BitVec.msb_eq_getLsbD_last x).symm

private theorem eval_extract_msb_bitvec_bitblast
    {W : Nat} (x : BitVec W) (hW : 0 < W) :
    __smtx_model_eval_extract
        (SmtValue.Numeral (↑(W - 1) : Int))
        (SmtValue.Numeral (↑(W - 1) : Int))
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int)) =
      SmtValue.Binary 1 (↑x.msb.toNat : Int) := by
  rw [extract_val_bitvec_start_len W (W - 1) 1 (↑x.toNat : Int)
    (↑(W - 1) : Int) (↑(W - 1) : Int)
    (by exact Int.natCast_nonneg _)
    (by norm_cast; exact x.isLt) rfl (by push_cast; omega)]
  rw [bitvec_ofInt_natCast_toNat,
    extractLsb_sign_bit_bitblast hW]
  cases x.msb <;> native_decide

private theorem bvashr_binary_branch
    (pre : List Bool) (s : Bool) (amount : List Bool) :
    __smtx_model_eval_bvashr
        (SmtValue.Binary ((pre ++ [s]).length : Int)
          (bitsValue (pre ++ [s]) : Int))
        (SmtValue.Binary (amount.length : Int)
          (bitsValue amount : Int)) =
      if s then
        __smtx_model_eval_bvnot
          (__smtx_model_eval_bvlshr
            (__smtx_model_eval_bvnot
              (SmtValue.Binary ((pre ++ [s]).length : Int)
                (bitsValue (pre ++ [s]) : Int)))
            (SmtValue.Binary (amount.length : Int)
              (bitsValue amount : Int)))
      else
        __smtx_model_eval_bvlshr
          (SmtValue.Binary ((pre ++ [s]).length : Int)
            (bitsValue (pre ++ [s]) : Int))
          (SmtValue.Binary (amount.length : Int)
            (bitsValue amount : Int)) := by
  rw [← ofBoolListLE_toNat (pre ++ [s])]
  unfold __smtx_model_eval_bvashr
  simp only [__smtx_bv_sizeof_value, __smtx_model_eval__,
    SmtEval.native_zplus, SmtEval.native_zneg]
  have hW : 0 < (pre ++ [s]).length := by simp
  have hSub :
      (↑(pre ++ [s]).length : Int) + -1 =
        (↑((pre ++ [s]).length - 1) : Int) := by
    omega
  rw [hSub,
    eval_extract_msb_bitvec_bitblast
      (BitVec.ofBoolListLE (pre ++ [s])) hW,
    msb_ofBoolListLE_append_singleton]
  cases s <;>
    simp [__smtx_model_eval_eq, native_veq,
      __smtx_model_eval_ite]

private theorem eval_step_bvlshr
    (M : SmtModel) (hM : model_wf M)
    (a amount : Term)
    (hne :
      shrBlast a amount (__bv_bitwidth (__eo_typeof a))
          (Term.Boolean false) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvlshr) a) amount))) :
    __smtx_model_eval M
        (__eo_to_smt
          (shrBlast a amount (__bv_bitwidth (__eo_typeof a))
            (Term.Boolean false))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvlshr) a) amount)) := by
  change term_has_non_none_type
      (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt amount)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvlshr)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt amount)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haTy, hamountTy⟩
  let width := __bv_bitwidth (__eo_typeof a)
  change
    shrBlast a amount width (Term.Boolean false) ≠ Term.Stuck at hne
  change
    __smtx_model_eval M
        (__eo_to_smt
          (shrBlast a amount width (Term.Boolean false))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvlshr) a) amount))
  have hsame :
      BitListsSameLength
        (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
          (shiftLszTerm width) (Term.Boolean false))
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) width) := by
    exact bitblast_apply_ite_same_length _ _ _
      (by simpa [shrBlast] using hne)
  have hzeroNe :
      __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) width ≠
        Term.Stuck :=
    hsame.syntax_right.ne_stuck
  rcases list_repeat_from_bools_context
      (Term.Boolean false) width hzeroNe with
    ⟨K, hwidth, _⟩
  have hwidthNe : __bv_bitwidth (__eo_typeof a) ≠ Term.Stuck := by
    change width ≠ Term.Stuck
    rw [hwidth]
    intro h
    cases h
  rcases bitwidth_context hwidthNe with ⟨widthTerm, haEoTy⟩
  have hwidthTerm : widthTerm = Term.Numeral (K : Int) := by
    change __bv_bitwidth (__eo_typeof a) =
      Term.Numeral (K : Int) at hwidth
    rw [haEoTy] at hwidth
    exact hwidth
  rw [hwidthTerm] at haEoTy
  have haTyK :
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec K := by
    calc
      _ = __eo_to_smt_type (__eo_typeof a) :=
        TranslationProofs.eo_to_smt_typeof_matches_translation a
          (by
            rw [haTy]
            simp)
      _ = _ := by
        rw [haEoTy]
        simp [__eo_to_smt_type, native_zleq, native_ite,
          native_int_to_nat]
  have hKW : K = W := by
    rw [haTy] at haTyK
    injection haTyK with h
    exact h.symm
  subst K
  change width = Term.Numeral (W : Int) at hwidth
  rw [hwidth] at hne hsame hzeroNe ⊢
  let L := barrelWidth W
  have hlsz :
      shiftLszTerm (Term.Numeral (W : Int)) =
        Term.Numeral (L : Int) :=
    shiftLszTerm_numeral W
  let const := shiftConstBits (Term.Numeral (W : Int))
  have hcondNe :
      shiftGuard amount (Term.Numeral (W : Int)) ≠ Term.Stuck := by
    apply bitblast_apply_ite_cond_ne
      (a :=
        __bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
          (shiftLszTerm (Term.Numeral (W : Int)))
          (Term.Boolean false))
      (b :=
        __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) (Term.Numeral (W : Int)))
    simpa [shrBlast] using hne
  have hultNe :
      __bv_bitblast_ult amount const (Term.Boolean false) ≠
        Term.Stuck := by
    simpa [shiftGuard, const] using hcondNe
  rcases bitblast_ult_shape amount const (Term.Boolean false) hultNe with
    ⟨abit, atail, cbit, ctail, hamountShape, hconstShape, htails⟩
  have hamountSyntax : BitListSyntax amount := by
    rw [hamountShape]
    exact BitListSyntax.cons abit atail htails.syntax_left
  have hconstSyntax : BitListSyntax const := by
    rw [hconstShape]
    exact BitListSyntax.cons cbit ctail htails.syntax_right
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hamountNN : term_has_non_none_type (__eo_to_smt amount) := by
    unfold term_has_non_none_type
    rw [hamountTy]
    simp
  have haSyntax : BitListSyntax a := by
    have htrueSyntax := hsame.syntax_left
    rw [hlsz] at htrueSyntax
    by_cases hL0 : L = 0
    · rw [hL0] at htrueSyntax
      change
        BitListSyntax
          (__bv_mk_bitblast_step_shr_rec a amount
            (Term.Numeral 0) (Term.Numeral 0)
            (Term.Boolean false)) at htrueSyntax
      have haNe : a ≠ Term.Stuck :=
        shr_rec_current_ne a amount (Term.Numeral 0)
          (Term.Numeral 0) (Term.Boolean false)
          htrueSyntax.ne_stuck
      have hrecEq :
          __bv_mk_bitblast_step_shr_rec a amount
              (Term.Numeral 0) (Term.Numeral 0)
              (Term.Boolean false) =
            a := by
        rw [__bv_mk_bitblast_step_shr_rec.eq_6 a amount
          (Term.Numeral 0) (Term.Numeral 0)
          (Term.Boolean false) haNe hamountSyntax.ne_stuck
          (by intro hs; cases hs) (by intro hs; cases hs)
          (by intro hs; cases hs)]
        simp [__eo_eq, native_teq, __eo_ite, native_ite]
      rw [hrecEq] at htrueSyntax
      exact htrueSyntax
    · apply shr_rec_zero_current_syntax a amount
        (Term.Boolean false) L (by omega)
        hamountSyntax.ne_stuck (by intro hs; cases hs)
        ⟨abit, atail, hamountShape⟩
      exact htrueSyntax.ne_stuck
  rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
  rcases hamountSyntax.eval hM hamountNN with ⟨ys, hamount⟩
  have hxW := bitListEval_length_eq_smt_type M hM a xs W ha haTy
  have hyW :=
    bitListEval_length_eq_smt_type M hM amount ys W hamount hamountTy
  have hW : 0 < W := by
    have hyPos : 0 < ys.length := by
      rw [hamountShape] at hamount
      cases hamount
      simp
    rw [← hyW]
    exact hyPos
  have hconst :
      BitListEval M const (reifyBits W 0 W) :=
    shiftConstBits_eval M W hconstSyntax.ne_stuck
  have hconstLen : (reifyBits W 0 W).length = W :=
    reifyBits_length W 0 W
  have hconstValue : bitsValue (reifyBits W 0 W) = W :=
    bitsValue_reifyBits W W Nat.lt_two_pow_self
  have htailLen :
      ys.tail.length = (reifyBits W 0 W).tail.length := by
    simp only [List.length_tail]
    omega
  have hguard :
      __smtx_model_eval M
          (__eo_to_smt
            (shiftGuard amount (Term.Numeral (W : Int)))) =
        SmtValue.Boolean (decide (bitsValue ys < W)) := by
    rw [hamountShape] at hamount
    rw [hconstShape] at hconst
    have hyNonempty : ys ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hyW]
      exact hW
    have hcNonempty : reifyBits W 0 W ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hconstLen]
      exact hW
    rw [← List.cons_head_tail hyNonempty] at hamount
    rw [← List.cons_head_tail hcNonempty] at hconst
    have hg :=
      bitblast_ult_eval (a := amount) (b := const)
        (orEqual := false) hamount hconst htailLen
    rw [List.cons_head_tail hyNonempty,
      List.cons_head_tail hcNonempty] at hg
    have hfullLen : ys.length = (reifyBits W 0 W).length := by
      rw [hyW, hconstLen]
    rw [ultBits_spec _ _ false hfullLen, hconstValue] at hg
    rw [← hamountShape, ← hconstShape] at hg
    simpa [shiftGuard, const] using hg
  have hzero :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) (Term.Numeral (W : Int)))
        (List.replicate W false) := by
    exact list_repeat_from_bools rfl (by intro h; cases h) W
  have htrue :
      BitListEval M
        (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
          (shiftLszTerm (Term.Numeral (W : Int)))
          (Term.Boolean false))
        (shrBarrelBits xs 0 ys L false) := by
    rw [hlsz]
    have hsimpa :=
      shr_rec_eval ha hamount
        (signTerm := Term.Boolean false) (sign := false) rfl 0 L W hxW
        (by rw [hyW]; exact barrelWidth_le W hW)
        (by
          intro j hj
          simpa using barrelWidth_pow_le W hW j hj)
    try simp only [Nat.zero_add] at hsimpa ⊢
    exact hsimpa
  have htrueLen : (shrBarrelBits xs 0 ys L false).length = W :=
    shrBarrelBits_length xs ys 0 L W false hxW
      (by rw [hyW]; exact barrelWidth_le W hW)
  have hout :=
    htrue.apply_ite hguard hzero (by simp [htrueLen])
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_ite
            (shiftGuard amount (Term.Numeral (W : Int)))
            (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
              (shiftLszTerm (Term.Numeral (W : Int)))
              (Term.Boolean false))
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              (Term.Boolean false) (Term.Numeral (W : Int))))) =
      __smtx_model_eval_bvlshr
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt amount))
  by_cases hy : bitsValue ys < W
  · have htake : bitsValue (ys.take L) = bitsValue ys := by
      rw [bitsValue_take_mod ys L
        (by rw [hyW]; exact barrelWidth_le W hW)]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy
        (le_pow_barrelWidth W hW))]
    have hval := shrBarrelBits_false_value xs ys 0 L W hxW
      (by rw [hyW]; exact barrelWidth_le W hW)
      (by
        intro j hj
        simpa using barrelWidth_pow_le W hW j hj)
    simp [htake] at hval
    have hselected :
        List.zipWith
            (fun x y =>
              if decide (bitsValue ys < W) = true then x else y)
            (shrBarrelBits xs 0 ys L false)
            (List.replicate W false) =
          shrBarrelBits xs 0 ys L false := by
      rw [show decide (bitsValue ys < W) = true by
        exact decide_eq_true hy]
      simp only [if_true]
      exact zipWith_left_of_length _ _
        (by simp [htrueLen])
    rw [hout.eval, ha.eval, hamount.eval, bvlshr_binary_values]
    rw [hselected, htrueLen, hxW, hval]
  · have hselected :
        List.zipWith
            (fun x y =>
              if decide (bitsValue ys < W) = true then x else y)
            (shrBarrelBits xs 0 ys L false)
            (List.replicate W false) =
          List.replicate W false := by
      rw [show decide (bitsValue ys < W) = false by
        exact decide_eq_false hy]
      simp only [Bool.false_eq_true, if_false]
      exact zipWith_right_of_length _ _
        (by simp [htrueLen])
    have hdiv : bitsValue xs / 2 ^ bitsValue ys = 0 := by
      apply Nat.div_eq_of_lt
      have hxlt : bitsValue xs < 2 ^ W := by
        rw [← hxW]
        exact bitsValue_lt xs
      have hpow : 2 ^ W ≤ 2 ^ bitsValue ys :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [hout.eval, ha.eval, hamount.eval, bvlshr_binary_values]
    rw [hselected, List.length_replicate, hxW,
      bitsValue_replicate_false, hdiv]

private theorem eval_step_bvashr
    (M : SmtModel) (hM : model_wf M)
    (a amount : Term)
    (hne :
      shrBlast a amount (__bv_bitwidth (__eo_typeof a))
          (__bv_bitblast_head
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvashr) a) amount))) :
    __smtx_model_eval M
        (__eo_to_smt
          (shrBlast a amount (__bv_bitwidth (__eo_typeof a))
            (__bv_bitblast_head
              (__eo_list_rev
                (Term.UOp UserOp._at_from_bools) a)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvashr) a) amount)) := by
  change term_has_non_none_type
      (SmtTerm.bvashr (__eo_to_smt a) (__eo_to_smt amount)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvashr)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt amount)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨W, haTy, hamountTy⟩
  let width := __bv_bitwidth (__eo_typeof a)
  let sign :=
    __bv_bitblast_head
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
  change shrBlast a amount width sign ≠ Term.Stuck at hne
  change
    __smtx_model_eval M
        (__eo_to_smt (shrBlast a amount width sign)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvashr) a) amount))
  have hsame :
      BitListsSameLength
        (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
          (shiftLszTerm width) sign)
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          sign width) := by
    exact bitblast_apply_ite_same_length _ _ _
      (by simpa [shrBlast] using hne)
  have hfillNe :
      __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          sign width ≠
        Term.Stuck :=
    hsame.syntax_right.ne_stuck
  rcases list_repeat_from_bools_context sign width hfillNe with
    ⟨K, hwidth, hsignNe⟩
  have hwidthNe : __bv_bitwidth (__eo_typeof a) ≠ Term.Stuck := by
    change width ≠ Term.Stuck
    rw [hwidth]
    intro h
    cases h
  rcases bitwidth_context hwidthNe with ⟨widthTerm, haEoTy⟩
  have hwidthTerm : widthTerm = Term.Numeral (K : Int) := by
    change __bv_bitwidth (__eo_typeof a) =
      Term.Numeral (K : Int) at hwidth
    rw [haEoTy] at hwidth
    exact hwidth
  rw [hwidthTerm] at haEoTy
  have haTyK :
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec K := by
    calc
      _ = __eo_to_smt_type (__eo_typeof a) :=
        TranslationProofs.eo_to_smt_typeof_matches_translation a
          (by
            rw [haTy]
            simp)
      _ = _ := by
        rw [haEoTy]
        simp [__eo_to_smt_type, native_zleq, native_ite,
          native_int_to_nat]
  have hKW : K = W := by
    rw [haTy] at haTyK
    injection haTyK with h
    exact h.symm
  subst K
  change width = Term.Numeral (W : Int) at hwidth
  rw [hwidth] at hne hsame hfillNe ⊢
  let L := barrelWidth W
  have hlsz :
      shiftLszTerm (Term.Numeral (W : Int)) =
        Term.Numeral (L : Int) :=
    shiftLszTerm_numeral W
  let const := shiftConstBits (Term.Numeral (W : Int))
  have hcondNe :
      shiftGuard amount (Term.Numeral (W : Int)) ≠ Term.Stuck := by
    apply bitblast_apply_ite_cond_ne
      (a :=
        __bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
          (shiftLszTerm (Term.Numeral (W : Int))) sign)
      (b :=
        __eo_list_repeat (Term.UOp UserOp._at_from_bools)
          sign (Term.Numeral (W : Int)))
    simpa [shrBlast] using hne
  have hultNe :
      __bv_bitblast_ult amount const (Term.Boolean false) ≠
        Term.Stuck := by
    simpa [shiftGuard, const] using hcondNe
  rcases bitblast_ult_shape amount const (Term.Boolean false) hultNe with
    ⟨abit, atail, cbit, ctail, hamountShape, hconstShape, htails⟩
  have hamountSyntax : BitListSyntax amount := by
    rw [hamountShape]
    exact BitListSyntax.cons abit atail htails.syntax_left
  have hconstSyntax : BitListSyntax const := by
    rw [hconstShape]
    exact BitListSyntax.cons cbit ctail htails.syntax_right
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hamountNN : term_has_non_none_type (__eo_to_smt amount) := by
    unfold term_has_non_none_type
    rw [hamountTy]
    simp
  have haSyntax : BitListSyntax a := by
    have htrueSyntax := hsame.syntax_left
    rw [hlsz] at htrueSyntax
    by_cases hL0 : L = 0
    · rw [hL0] at htrueSyntax
      change
        BitListSyntax
          (__bv_mk_bitblast_step_shr_rec a amount
            (Term.Numeral 0) (Term.Numeral 0) sign) at htrueSyntax
      have haNe : a ≠ Term.Stuck :=
        shr_rec_current_ne a amount (Term.Numeral 0)
          (Term.Numeral 0) sign htrueSyntax.ne_stuck
      have hrecEq :
          __bv_mk_bitblast_step_shr_rec a amount
              (Term.Numeral 0) (Term.Numeral 0) sign =
            a := by
        rw [__bv_mk_bitblast_step_shr_rec.eq_6 a amount
          (Term.Numeral 0) (Term.Numeral 0) sign
          haNe hamountSyntax.ne_stuck
          (by intro hs; cases hs) (by intro hs; cases hs)
          hsignNe]
        simp [__eo_eq, native_teq, __eo_ite, native_ite]
      rw [hrecEq] at htrueSyntax
      exact htrueSyntax
    · apply shr_rec_zero_current_syntax a amount sign L (by omega)
        hamountSyntax.ne_stuck hsignNe
        ⟨abit, atail, hamountShape⟩
      exact htrueSyntax.ne_stuck
  rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
  rcases hamountSyntax.eval hM hamountNN with ⟨ys, hamount⟩
  have hxW := bitListEval_length_eq_smt_type M hM a xs W ha haTy
  have hyW :=
    bitListEval_length_eq_smt_type M hM amount ys W hamount hamountTy
  have hW : 0 < W := by
    have hyPos : 0 < ys.length := by
      rw [hamountShape] at hamount
      cases hamount
      simp
    rw [← hyW]
    exact hyPos
  have hsignData :
      ∃ s ss,
        xs.reverse = s :: ss ∧
        __smtx_model_eval M (__eo_to_smt sign) =
          SmtValue.Boolean s := by
    have hrev := ha.rev
    cases hrevXs : xs.reverse with
    | nil =>
        have hrev' :
            BitListEval M
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
              [] := by
          rw [← hrevXs]
          exact hrev
        have hsignStuck : sign = Term.Stuck := by
          change
            __bv_bitblast_head
                (__eo_list_rev (Term.UOp UserOp._at_from_bools) a) =
              Term.Stuck
          rw [hrev'.eq_nil]
          rfl
        exact (hsignNe hsignStuck).elim
    | cons s ss =>
        have hrev' :
            BitListEval M
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
              (s :: ss) := by
          rw [← hrevXs]
          exact hrev
        exact ⟨s, ss, rfl, hrev'.head⟩
  rcases hsignData with ⟨s, ss, hrevXs, hsign⟩
  have hxs : xs = ss.reverse ++ [s] := by
    have h := congrArg List.reverse hrevXs
    simpa using h
  have hrepeatRecNe :
      __eo_list_repeat_rec (Term.UOp UserOp._at_from_bools)
          sign W ≠
        Term.Stuck := by
    change
      __eo_list_repeat (Term.UOp UserOp._at_from_bools) sign
          (Term.Numeral (W : Int)) ≠
        Term.Stuck at hfillNe
    rw [__eo_list_repeat.eq_3 _ _ (W : Int)
      (by intro hh; cases hh) hsignNe] at hfillNe
    rw [show native_zlt (W : Int) 0 = false by
      simp [native_zlt]] at hfillNe
    have hsimpa := hfillNe
    try simp [native_ite] at hsimpa ⊢
    exact hsimpa
  have hsignTy : __eo_typeof sign ≠ Term.Stuck :=
    list_repeat_rec_from_bools_type_ne hrepeatRecNe
  have hconst :
      BitListEval M const (reifyBits W 0 W) :=
    shiftConstBits_eval M W hconstSyntax.ne_stuck
  have hconstLen : (reifyBits W 0 W).length = W :=
    reifyBits_length W 0 W
  have hconstValue : bitsValue (reifyBits W 0 W) = W :=
    bitsValue_reifyBits W W Nat.lt_two_pow_self
  have htailLen :
      ys.tail.length = (reifyBits W 0 W).tail.length := by
    simp only [List.length_tail]
    omega
  have hguard :
      __smtx_model_eval M
          (__eo_to_smt
            (shiftGuard amount (Term.Numeral (W : Int)))) =
        SmtValue.Boolean (decide (bitsValue ys < W)) := by
    rw [hamountShape] at hamount
    rw [hconstShape] at hconst
    have hyNonempty : ys ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hyW]
      exact hW
    have hcNonempty : reifyBits W 0 W ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [hconstLen]
      exact hW
    rw [← List.cons_head_tail hyNonempty] at hamount
    rw [← List.cons_head_tail hcNonempty] at hconst
    have hg :=
      bitblast_ult_eval (a := amount) (b := const)
        (orEqual := false) hamount hconst htailLen
    rw [List.cons_head_tail hyNonempty,
      List.cons_head_tail hcNonempty] at hg
    have hfullLen : ys.length = (reifyBits W 0 W).length := by
      rw [hyW, hconstLen]
    rw [ultBits_spec _ _ false hfullLen, hconstValue] at hg
    rw [← hamountShape, ← hconstShape] at hg
    simpa [shiftGuard, const] using hg
  have hfill :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          sign (Term.Numeral (W : Int)))
        (List.replicate W s) :=
    list_repeat_from_bools hsign hsignTy W
  have htrue :
      BitListEval M
        (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
          (shiftLszTerm (Term.Numeral (W : Int))) sign)
        (shrBarrelBits xs 0 ys L s) := by
    rw [hlsz]
    have hsimpa :=
      shr_rec_eval ha hamount hsign 0 L W hxW
        (by rw [hyW]; exact barrelWidth_le W hW)
        (by
          intro j hj
          simpa using barrelWidth_pow_le W hW j hj)
    try simp only [Nat.zero_add] at hsimpa ⊢
    exact hsimpa
  have htrueLen : (shrBarrelBits xs 0 ys L s).length = W :=
    shrBarrelBits_length xs ys 0 L W s hxW
      (by rw [hyW]; exact barrelWidth_le W hW)
  have hout :=
    htrue.apply_ite hguard hfill (by simp [htrueLen])
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_ite
            (shiftGuard amount (Term.Numeral (W : Int)))
            (__bv_mk_bitblast_step_shr_rec a amount (Term.Numeral 0)
              (shiftLszTerm (Term.Numeral (W : Int))) sign)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              sign (Term.Numeral (W : Int))))) =
      __smtx_model_eval_bvashr
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt amount))
  have hash := bvashr_binary_branch ss.reverse s ys
  rw [← hxs] at hash
  cases s with
  | false =>
      simp at hash
      by_cases hy : bitsValue ys < W
      · have htake : bitsValue (ys.take L) = bitsValue ys := by
          rw [bitsValue_take_mod ys L
            (by rw [hyW]; exact barrelWidth_le W hW)]
          rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy
            (le_pow_barrelWidth W hW))]
        have hval := shrBarrelBits_false_value xs ys 0 L W hxW
          (by rw [hyW]; exact barrelWidth_le W hW)
          (by
            intro j hj
            simpa using barrelWidth_pow_le W hW j hj)
        simp [htake] at hval
        have hselected :
            List.zipWith
                (fun x y =>
                  if decide (bitsValue ys < W) = true then x else y)
                (shrBarrelBits xs 0 ys L false)
                (List.replicate W false) =
              shrBarrelBits xs 0 ys L false := by
          rw [show decide (bitsValue ys < W) = true by
            exact decide_eq_true hy]
          simp only [if_true]
          exact zipWith_left_of_length _ _ (by simp [htrueLen])
        rw [hout.eval, ha.eval, hamount.eval, hash]
        rw [bvlshr_binary_values, hselected, htrueLen, hxW, hval]
      · have hselected :
            List.zipWith
                (fun x y =>
                  if decide (bitsValue ys < W) = true then x else y)
                (shrBarrelBits xs 0 ys L false)
                (List.replicate W false) =
              List.replicate W false := by
          rw [show decide (bitsValue ys < W) = false by
            exact decide_eq_false hy]
          simp only [Bool.false_eq_true, if_false]
          exact zipWith_right_of_length _ _ (by simp [htrueLen])
        have hdiv : bitsValue xs / 2 ^ bitsValue ys = 0 := by
          apply Nat.div_eq_of_lt
          have hxlt : bitsValue xs < 2 ^ W := by
            rw [← hxW]
            exact bitsValue_lt xs
          have hpow : 2 ^ W ≤ 2 ^ bitsValue ys :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
        rw [hout.eval, ha.eval, hamount.eval, hash]
        rw [bvlshr_binary_values, hselected, List.length_replicate,
          hxW, bitsValue_replicate_false, hdiv]
  | true =>
      simp at hash
      have hnotLen : (xs.map (!·)).length = W := by
        rw [List.length_map, hxW]
      by_cases hy : bitsValue ys < W
      · have htake : bitsValue (ys.take L) = bitsValue ys := by
          rw [bitsValue_take_mod ys L
            (by rw [hyW]; exact barrelWidth_le W hW)]
          rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy
            (le_pow_barrelWidth W hW))]
        let zs := shrBarrelBits (xs.map (!·)) 0 ys L false
        have hzLen : zs.length = W :=
          shrBarrelBits_length (xs.map (!·)) ys 0 L W false
            hnotLen
            (by rw [hyW]; exact barrelWidth_le W hW)
        have hvalZ :=
          shrBarrelBits_false_value (xs.map (!·)) ys 0 L W hnotLen
            (by rw [hyW]; exact barrelWidth_le W hW)
            (by
              intro j hj
              simpa using barrelWidth_pow_le W hW j hj)
        simp [htake] at hvalZ
        have hcomp :
            shrBarrelBits xs 0 ys L true = zs.map (!·) := by
          exact shrBarrelBits_complement xs ys 0 L
        have hselected :
            List.zipWith
                (fun x y =>
                  if decide (bitsValue ys < W) = true then x else y)
                (shrBarrelBits xs 0 ys L true)
                (List.replicate W true) =
              shrBarrelBits xs 0 ys L true := by
          rw [show decide (bitsValue ys < W) = true by
            exact decide_eq_true hy]
          simp only [if_true]
          exact zipWith_left_of_length _ _ (by simp [htrueLen])
        have hinner :
            __smtx_model_eval_bvlshr
                (__smtx_model_eval_bvnot
                  (SmtValue.Binary (xs.length : Int)
                    (bitsValue xs : Int)))
                (SmtValue.Binary (ys.length : Int)
                  (bitsValue ys : Int)) =
              SmtValue.Binary (W : Int) (bitsValue zs : Int) := by
          rw [bvnot_binary_values]
          have hlenMap :
              (xs.map (!·)).length = xs.length := by simp
          rw [← hlenMap]
          rw [bvlshr_binary_values]
          rw [List.length_map, hxW, hvalZ]
        have houter :
            __smtx_model_eval_bvnot
                (SmtValue.Binary (W : Int) (bitsValue zs : Int)) =
              SmtValue.Binary (W : Int)
                (bitsValue (zs.map (!·)) : Int) := by
          simpa only [hzLen] using bvnot_binary_values zs
        rw [hout.eval, ha.eval, hamount.eval, hash]
        rw [hinner, houter, hselected, htrueLen, hcomp]
      · have hselected :
            List.zipWith
                (fun x y =>
                  if decide (bitsValue ys < W) = true then x else y)
                (shrBarrelBits xs 0 ys L true)
                (List.replicate W true) =
              List.replicate W true := by
          rw [show decide (bitsValue ys < W) = false by
            exact decide_eq_false hy]
          simp only [Bool.false_eq_true, if_false]
          exact zipWith_right_of_length _ _ (by simp [htrueLen])
        have hdiv :
            bitsValue (xs.map (!·)) / 2 ^ bitsValue ys = 0 := by
          apply Nat.div_eq_of_lt
          have hxlt : bitsValue (xs.map (!·)) < 2 ^ W := by
            rw [← hnotLen]
            exact bitsValue_lt _
          have hpow : 2 ^ W ≤ 2 ^ bitsValue ys :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have hinner :
            __smtx_model_eval_bvlshr
                (__smtx_model_eval_bvnot
                  (SmtValue.Binary (xs.length : Int)
                    (bitsValue xs : Int)))
                (SmtValue.Binary (ys.length : Int)
                  (bitsValue ys : Int)) =
              SmtValue.Binary (W : Int) 0 := by
          rw [bvnot_binary_values]
          have hlenMap :
              (xs.map (!·)).length = xs.length := by simp
          rw [← hlenMap]
          rw [bvlshr_binary_values]
          rw [List.length_map, hxW, hdiv]
          rfl
        have houter :
            __smtx_model_eval_bvnot (SmtValue.Binary (W : Int) 0) =
              SmtValue.Binary (W : Int)
                (bitsValue (List.replicate W true) : Int) := by
          have hb := bvnot_binary_values (List.replicate W false)
          simpa [bitsValue_replicate_false] using hb
        rw [hout.eval, ha.eval, hamount.eval, hash]
        rw [hinner, houter, hselected, List.length_replicate]

private theorem eval_step_sign_extend
    (M : SmtModel) (hM : model_wf M)
    (n a : Term)
    (hne :
      __bv_bitblast_concat a
          (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
            (__bv_bitblast_head
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) a))
            n) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend n) a))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_concat a
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              (__bv_bitblast_head
                (__eo_list_rev (Term.UOp UserOp._at_from_bools) a))
              n))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend n) a)) := by
  let sign :=
    __bv_bitblast_head
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
  let repeated :=
    __eo_list_repeat (Term.UOp UserOp._at_from_bools) sign n
  have haSyntax : BitListSyntax a :=
    bitblast_concat_syntax_left a repeated hne
  change term_has_non_none_type
      (SmtTerm.sign_extend (__eo_to_smt n) (__eo_to_smt a)) at hnn
  rcases sign_extend_args_of_non_none hnn with
    ⟨i, W, hnSmt, haTy, hi⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
  have hlen :=
    bitListEval_length_eq_smt_type M hM a xs W ha haTy
  subst W
  have hrepeatNe : repeated ≠ Term.Stuck :=
    bitblast_concat_right_ne hne
  rcases list_repeat_from_bools_context sign n hrepeatNe with
    ⟨K, hn, hsignNe⟩
  subst n
  have hrepeatRecNe :
      __eo_list_repeat_rec (Term.UOp UserOp._at_from_bools)
          sign K ≠
        Term.Stuck := by
    change
      __eo_list_repeat (Term.UOp UserOp._at_from_bools) sign
          (Term.Numeral (K : Int)) ≠
        Term.Stuck at hrepeatNe
    rw [__eo_list_repeat.eq_3 _ _ (K : Int)
      (by intro hh; cases hh) hsignNe] at hrepeatNe
    rw [show native_zlt (K : Int) 0 = false by
      simp [native_zlt]] at hrepeatNe
    have hsimpa := hrepeatNe
    try simp [native_ite] at hsimpa ⊢
    exact hsimpa
  have hsignTy : __eo_typeof sign ≠ Term.Stuck :=
    list_repeat_rec_from_bools_type_ne hrepeatRecNe
  have hrev := ha.rev
  cases hrevXs : xs.reverse with
  | nil =>
    have hrev' :
        BitListEval M
          (__eo_list_rev (Term.UOp UserOp._at_from_bools) a) [] := by
      rw [← hrevXs]
      exact hrev
    have hsignStuck : sign = Term.Stuck := by
      change
        __bv_bitblast_head
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a) =
          Term.Stuck
      rw [hrev'.eq_nil]
      rfl
    exact (hsignNe hsignStuck).elim
  | cons s ss =>
    have hrev' :
        BitListEval M
          (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
          (s :: ss) := by
      rw [← hrevXs]
      exact hrev
    have hsignEval :
        __smtx_model_eval M (__eo_to_smt sign) =
          SmtValue.Boolean s := by
      exact hrev'.head
    have hrep :
        BitListEval M repeated (List.replicate K s) := by
      change
        BitListEval M
          (__eo_list_repeat (Term.UOp UserOp._at_from_bools) sign
            (Term.Numeral (K : Int)))
          (List.replicate K s)
      exact list_repeat_from_bools hsignEval hsignTy K
    have hout :
        BitListEval M
          (__bv_bitblast_concat a repeated)
          (xs ++ List.replicate K s) :=
      ha.concat hrep
    have hxs : xs = ss.reverse ++ [s] := by
      have h := congrArg List.reverse hrevXs
      simpa using h
    rw [hout.eval]
    rw [eval_sign_extend_term, ha.eval]
    rw [sign_extend_val_bitvec xs.length K
      (bitsValue xs : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast bitsValue_lt xs)]
    rw [ofInt_bitsValue]
    congr 2
    · norm_cast
      simp [Nat.add_comm]
    · norm_cast
      rw [hxs]
      exact bitsValue_sign_extend ss.reverse s K

theorem eval_bv_mk_bitblast_step
    (M : SmtModel) (hM : model_wf M) (lhs : Term)
    (hne : __bv_mk_bitblast_step lhs ≠ Term.Stuck)
    (hnn : term_has_non_none_type (__eo_to_smt lhs)) :
    __smtx_model_eval M (__eo_to_smt (__bv_mk_bitblast_step lhs)) =
      __smtx_model_eval M (__eo_to_smt lhs) := by
  unfold __bv_mk_bitblast_step at hne ⊢
  split at * <;> simp_all
  case h_2 => exact eval_step_bvnot M hM _ hne hnn
  case h_3 => exact eval_step_eq M hM _ _ hne hnn
  case h_4 => exact eval_step_bvult M hM _ _ hne hnn
  case h_5 => exact eval_step_bvule M hM _ _ hne hnn
  case h_6 => exact eval_step_bvslt M hM _ _ hne hnn
  case h_7 => exact eval_step_bvsle M hM _ _ hne hnn
  case h_8 => exact eval_step_extract M hM _ _ _ hne hnn
  case h_9 => exact eval_step_concat M hM _ _ hne hnn
  case h_10 => exact eval_step_bvor_fold M hM _ _ hne hnn
  case h_11 => exact eval_step_bvand_fold M hM _ _ hne hnn
  case h_12 => exact eval_step_bvxor_fold M hM _ _ hne hnn
  case h_13 => exact eval_step_bvxnor M hM _ _ hne hnn
  case h_14 => exact eval_step_bvadd_fold M hM _ _ hne hnn
  case h_15 => exact eval_step_bvmul_fold M hM _ _ hne hnn
  case h_16 => exact eval_step_bvudiv M hM _ _ hne hnn
  case h_17 => exact eval_step_bvurem M hM _ _ hne hnn
  case h_18 => exact eval_step_bvsub M hM _ _ hne hnn
  case h_19 => exact eval_step_bvneg M hM _ hne hnn
  case h_20 => exact eval_step_bvite M hM _ _ _ hne hnn
  case h_21 => exact eval_step_bvashr M hM _ _ hne hnn
  case h_22 => exact eval_step_bvlshr M hM _ _ hne hnn
  case h_23 => exact eval_step_bvshl M hM _ _ hne hnn
  case h_24 => exact eval_step_bvcomp M hM _ _ hne hnn
  case h_25 => exact eval_step_bvultbv M hM _ _ hne hnn
  case h_26 => exact eval_step_bvsltbv M hM _ _ hne hnn
  case h_27 => exact eval_step_sign_extend M hM _ _ hne hnn
  case h_28 => exact eval_step_default M hM _ hne hnn

end BvBitblast
