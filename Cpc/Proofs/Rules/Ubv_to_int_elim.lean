module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_requires_left_ne_stuck_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro hReq hx
  have hStuck : __eo_requires x y z = Term.Stuck := by
    subst x
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
  exact hReq hStuck

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_typeof_ne_stuck_of_smt_bitvec
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    __eo_typeof a ≠ Term.Stuck := by
  have hNN : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [haTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation a hNN
  intro hStuck
  rw [hStuck] at hMatch
  rw [haTy] at hMatch
  cases hMatch

private theorem term_ne_stuck_of_smt_bitvec
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    a ≠ Term.Stuck := by
  intro h
  subst a
  exact (eo_typeof_ne_stuck_of_smt_bitvec Term.Stuck w haTy) rfl

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ ((w : Int) < 0) := by omega
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private def typedIntNil : Term :=
  Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)

private def typedIntCons (i ns : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) i) ns

private def ubvZeroList : Nat -> Term
  | 0 => typedIntNil
  | len + 1 => typedIntCons (Term.Numeral 0) (ubvZeroList len)

private def ubvIotaList : Nat -> Nat -> Term
  | _start, 0 => typedIntNil
  | start, Nat.succ len =>
      typedIntCons (Term.Numeral (native_nat_to_int start))
        (ubvIotaList (Nat.succ start) len)

private theorem ubvZeroList_ne_stuck (len : Nat) :
    ubvZeroList len ≠ Term.Stuck := by
  cases len <;> simp [ubvZeroList, typedIntNil, typedIntCons]

private theorem ubvIotaList_ne_stuck (start len : Nat) :
    ubvIotaList start len ≠ Term.Stuck := by
  cases len <;> simp [ubvIotaList, typedIntNil, typedIntCons]

private theorem cons_zero_head_ne_stuck :
    Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0) ≠
      Term.Stuck := by
  intro h
  cases h

private theorem cons_head_ne_stuck (start : Nat) :
    Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
      (Term.Numeral (native_nat_to_int start)) ≠ Term.Stuck := by
  intro h
  cases h

private theorem ubv_list_repeat_rec_zero_eq (len : Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
      (Term.Numeral 0) len = ubvZeroList len := by
  induction len with
  | zero => rfl
  | succ len ih =>
      change __eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0))
          (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) len) =
        typedIntCons (Term.Numeral 0) (ubvZeroList len)
      rw [ih]
      rw [eo_mk_apply_of_ne_stuck cons_zero_head_ne_stuck
        (ubvZeroList_ne_stuck len)]
      rfl

private theorem ubv_iota_zeroList_eq (start len : Nat) :
    __iota_rec (ubvZeroList len) (Term.Numeral (native_nat_to_int start)) =
      ubvIotaList start len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      change __eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (native_nat_to_int start)))
          (__iota_rec (ubvZeroList len)
            (__eo_add (Term.Numeral (native_nat_to_int start)) (Term.Numeral 1))) =
        typedIntCons (Term.Numeral (native_nat_to_int start))
          (ubvIotaList (start + 1) len)
      have hAdd :
          __eo_add (Term.Numeral (native_nat_to_int start)) (Term.Numeral 1) =
            Term.Numeral (native_nat_to_int (start + 1)) := by
        simp [__eo_add, native_zplus, native_nat_to_int]
      rw [hAdd, ih]
      rw [eo_mk_apply_of_ne_stuck (cons_head_ne_stuck start)
        (ubvIotaList_ne_stuck (start + 1) len)]
      rfl

private theorem ubv_iota_repeat_rec_eq (start len : Nat) :
    __iota_rec
        (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) len)
        (Term.Numeral (native_nat_to_int start)) =
      ubvIotaList start len := by
  rw [ubv_list_repeat_rec_zero_eq, ubv_iota_zeroList_eq]

private theorem ubv_list_repeat_zero_eq (len : Nat) :
    __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0)
      (Term.Numeral (native_nat_to_int len)) =
    __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
      (Term.Numeral 0) len := by
  have hnot : ¬ ((len : Int) < 0) := by omega
  simp [__eo_list_repeat, native_zlt, native_int_to_nat, native_nat_to_int,
    native_ite, hnot]

private theorem ubv_mul_pow_two (start : Nat) :
    __eo_mul
        (Term.Numeral (native_int_pow2 (native_nat_to_int start)))
        (Term.Numeral 2) =
      Term.Numeral (native_int_pow2 (native_nat_to_int (start + 1))) := by
  simp [__eo_mul, native_zmult, native_int_pow2_nat]
  exact (Int.pow_succ (2 : Int) start).symm

private def ubvBitAddend (b : Term) (start : Nat) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.ite)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int start))
                (Term.Numeral (native_nat_to_int start))) b))
          (Term.Binary 1 1)))
      (Term.Numeral (native_int_pow2 (native_nat_to_int start))))
    (Term.Numeral 0)

private def ubvRawExpansion : Term -> Nat -> Nat -> Term
  | b, start, 0 => Term.Numeral 0
  | b, start, Nat.succ len =>
      Term.Apply (Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start))
        (ubvRawExpansion b (Nat.succ start) len)

private theorem plus_head_ne_stuck (b : Term) (start : Nat) :
    Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start) ≠ Term.Stuck := by
  intro h
  cases h

private theorem ubvRawExpansion_ne_stuck (b : Term) (start len : Nat) :
    ubvRawExpansion b start len ≠ Term.Stuck := by
  cases len <;> simp [ubvRawExpansion]

private theorem ubv_abconv_iota_succ_pow_eq
    (b : Term) (hb : b ≠ Term.Stuck) (start len : Nat) :
    __abconv_ubv_to_int_elim b
        (ubvIotaList start (Nat.succ len))
        (Term.Numeral (native_int_pow2 (native_nat_to_int start))) =
      __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start))
        (__abconv_ubv_to_int_elim b (ubvIotaList (Nat.succ start) len)
          (Term.Numeral (native_int_pow2 (native_nat_to_int (start + 1))))) := by
  cases b <;>
    simp [ubvIotaList, typedIntCons, ubvBitAddend, __abconv_ubv_to_int_elim,
      ubv_mul_pow_two] at hb ⊢

private theorem ubv_abconv_iota_eq
    (b : Term) (hb : b ≠ Term.Stuck) :
    ∀ start len : Nat,
      __abconv_ubv_to_int_elim b (ubvIotaList start len)
        (Term.Numeral (native_int_pow2 (native_nat_to_int start))) =
      ubvRawExpansion b start len := by
  intro start len
  induction len generalizing start with
  | zero =>
      cases b <;>
        simp [ubvIotaList, ubvRawExpansion, typedIntNil,
          __abconv_ubv_to_int_elim] at hb ⊢
  | succ len ih =>
      rw [ubv_abconv_iota_succ_pow_eq b hb start len]
      rw [ih (Nat.succ start)]
      change __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start))
          (ubvRawExpansion b (Nat.succ start) len) =
        Term.Apply (Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start))
          (ubvRawExpansion b (Nat.succ start) len)
      rw [eo_mk_apply_of_ne_stuck (plus_head_ne_stuck b start)
        (ubvRawExpansion_ne_stuck b (Nat.succ start) len)]

private theorem ubv_generated_expansion_eq_raw
    (b : Term) (w : native_Nat)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w) :
    __abconv_ubv_to_int_elim b
        (__eo_requires (__eo_is_neg (__bv_bitwidth (__eo_typeof b)))
          (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) (__bv_bitwidth (__eo_typeof b)))
            (Term.Numeral 0)))
        (Term.Numeral 1) =
      ubvRawExpansion b 0 w := by
  have hbTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hbTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation b hbTrans
  have hEoSmt : __eo_to_smt_type (__eo_typeof b) = SmtType.BitVec w := by
    rw [← hMatch, hbTy]
  have hEoTy :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hEoSmt
  have hWidth :
      __bv_bitwidth (__eo_typeof b) = Term.Numeral (native_nat_to_int w) := by
    rw [hEoTy]
    rfl
  have hIndices :
      __eo_requires (__eo_is_neg (__bv_bitwidth (__eo_typeof b)))
          (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) (__bv_bitwidth (__eo_typeof b)))
            (Term.Numeral 0)) =
        ubvIotaList 0 w := by
    have hnot : ¬ ((w : Int) < 0) := by omega
    rw [hWidth]
    rw [ubv_list_repeat_zero_eq]
    change __eo_requires (__eo_is_neg (Term.Numeral (native_nat_to_int w)))
        (Term.Boolean false)
        (__iota_rec
          (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) w)
          (Term.Numeral (native_nat_to_int 0))) =
      ubvIotaList 0 w
    rw [ubv_iota_repeat_rec_eq]
    simp [__eo_is_neg, __eo_requires, native_zlt, native_teq, native_not,
      SmtEval.native_not, native_ite, native_nat_to_int, hnot]
  rw [hIndices]
  exact ubv_abconv_iota_eq b (term_ne_stuck_of_smt_bitvec b w hbTy) 0 w

private def natScaledBitSum (n start : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => (if n.testBit start then 2 ^ start else 0) +
      natScaledBitSum n (start + 1) k

private theorem nat_mod_two_pow_succ_low_decomp (q k : Nat) :
    q % (2 ^ (k + 1)) = q % 2 + 2 * (q / 2 % (2 ^ k)) := by
  let p := 2 ^ k
  have hpow : 2 ^ (k + 1) = 2 * p := by
    simp [p, Nat.pow_succ]
    rw [Nat.mul_comm]
  have h := Nat.mod_add_div (q % (2 * p)) 2
  have hmod : (q % (2 * p)) % 2 = q % 2 := by
    rw [Nat.mod_mod_of_dvd]
    exact Nat.dvd_mul_right 2 p
  have hdiv : (q % (2 * p)) / 2 = q / 2 % p := by
    exact Nat.mod_mul_right_div_self q 2 p
  rw [hmod, hdiv] at h
  rw [hpow]
  exact h.symm

private theorem nat_div_pow_succ (n start : Nat) :
    n / 2 ^ (start + 1) = n / 2 ^ start / 2 := by
  rw [Nat.div_div_eq_div_mul]
  simp [Nat.pow_succ]

private theorem natScaledBitSum_eq (n start len : Nat) :
    natScaledBitSum n start len =
      2 ^ start * ((n / 2 ^ start) % (2 ^ len)) := by
  induction len generalizing start with
  | zero =>
      simp [natScaledBitSum, Nat.mod_one]
  | succ k ih =>
      have hbit :
          (if n.testBit start then 2 ^ start else 0) =
            2 ^ start * ((n / 2 ^ start) % 2) := by
        have htb : n.testBit start = decide (n / (2 ^ start) % 2 = 1) := by
          rw [← Nat.shiftRight_eq_div_pow]
          simp [Nat.testBit]
        rcases Nat.mod_two_eq_zero_or_one (n / (2 ^ start)) with h0 | h1
        · simp [htb, h0]
        · simp [htb, h1]
      rw [natScaledBitSum, ih, hbit]
      rw [nat_div_pow_succ]
      rw [nat_mod_two_pow_succ_low_decomp]
      have hpowSucc : 2 ^ (start + 1) = 2 ^ start * 2 := by
        simp [Nat.pow_succ]
      rw [hpowSucc]
      rw [Nat.mul_assoc]
      rw [← Nat.mul_add]

private theorem ubv_bit_mod_eq_nat (n : Int) (start : Nat) (hn : 0 <= n) :
    native_mod_total (native_div_total n (native_int_pow2 (native_nat_to_int start))) 2 =
      ((n.toNat / 2 ^ start % 2 : Nat) : Int) := by
  have hDiv : native_div_total n (native_int_pow2 (native_nat_to_int start)) =
      ((n.toNat / 2 ^ start : Nat) : Int) := by
    rw [native_div_total, native_int_pow2_nat]
    rw [← Int.toNat_of_nonneg hn]
    exact (Int.natCast_ediv n.toNat (2 ^ start)).symm
  rw [hDiv, native_mod_total]
  exact (Int.natCast_emod (n.toNat / 2 ^ start) 2).symm

private theorem ubvBitAddend_eval
    (M : SmtModel) (b : Term) (w n : Int) (start : Nat)
    (hEvalB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Binary w n)
    (hn : 0 <= n) :
    __smtx_model_eval M (__eo_to_smt (ubvBitAddend b start)) =
      SmtValue.Numeral (if n.toNat.testBit start then (2 ^ start : Int) else 0) := by
  have hBit :
      native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (native_nat_to_int start))) 2)
          1 =
        n.toNat.testBit start := by
    have htb : n.toNat.testBit start =
        decide (n.toNat / (2 ^ start) % 2 = 1) := by
      rw [← Nat.shiftRight_eq_div_pow]
      simp [Nat.testBit]
    rw [ubv_bit_mod_eq_nat n start hn, htb]
    rcases Nat.mod_two_eq_zero_or_one (n.toNat / 2 ^ start) with h0 | h1
    · simp [native_zeq, h0]
    · simp [native_zeq, h1]
  have hBitDec :
      decide (native_mod_total (native_div_total n (2 ^ start)) 2 = 1) =
        n.toNat.testBit start := by
    simpa [native_zeq, native_int_pow2_nat] using hBit
  rw [ubvBitAddend]
  change __smtx_model_eval M
      (SmtTerm.ite
        (SmtTerm.eq
          (SmtTerm.extract (SmtTerm.Numeral (native_nat_to_int start))
            (SmtTerm.Numeral (native_nat_to_int start)) (__eo_to_smt b))
          (SmtTerm.Binary 1 1))
        (SmtTerm.Numeral (native_int_pow2 (native_nat_to_int start)))
        (SmtTerm.Numeral 0)) =
      SmtValue.Numeral (if n.toNat.testBit start then (2 ^ start : Int) else 0)
  rw [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq,
    __smtx_model_eval.eq_37, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_2, hEvalB, __smtx_model_eval.eq_5,
    __smtx_model_eval.eq_2]
  have hWidth :
      native_zplus (native_zplus (native_nat_to_int start) 1)
        (native_zneg (native_nat_to_int start)) = 1 := by
    change ((start : Int) + 1 + -(start : Int)) = 1
    omega
  have hPow1 : native_int_pow2 1 = 2 := by native_decide
  simp [__smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_ite, native_veq, native_binary_extract,
    hWidth, hPow1, native_int_pow2_nat]
  rw [hBitDec]
  cases n.toNat.testBit start <;> rfl

private theorem ubvRawExpansion_eval (M : SmtModel) (b : Term) (w n : Int)
    (hEvalB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Binary w n)
    (hn : 0 <= n) :
    ∀ (start len : Nat),
      __smtx_model_eval M (__eo_to_smt (ubvRawExpansion b start len)) =
        SmtValue.Numeral ((natScaledBitSum n.toNat start len : Nat) : Int) := by
  intro start len
  induction len generalizing start with
  | zero =>
      change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
      rw [__smtx_model_eval.eq_2]
  | succ len ih =>
      rw [ubvRawExpansion]
      change __smtx_model_eval M
          (SmtTerm.plus (__eo_to_smt (ubvBitAddend b start))
            (__eo_to_smt (ubvRawExpansion b (start + 1) len))) =
        SmtValue.Numeral ((natScaledBitSum n.toNat start (len + 1) : Nat) : Int)
      rw [__smtx_model_eval.eq_14,
        ubvBitAddend_eval M b w n start hEvalB hn, ih (start + 1)]
      cases h : n.toNat.testBit start <;>
        simp [natScaledBitSum, h, __smtx_model_eval_plus, native_zplus]

private theorem eo_is_list_true_of_get_nil_eq
    {f x nil : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck)
    (hNil : __eo_get_nil_rec f x = nil)
    (hNilNe : nil ≠ Term.Stuck) :
    __eo_is_list f x = Term.Boolean true := by
  have hGetNe : __eo_get_nil_rec f x ≠ Term.Stuck := by
    intro hGet
    rw [hGet] at hNil
    exact hNilNe hNil.symm
  cases f <;> cases x <;>
    simp [__eo_is_list, __eo_is_ok, native_teq, native_not,
      SmtEval.native_not, hGetNe] at hf hx hNil hNilNe ⊢

private theorem plus_ne_stuck :
    Term.UOp UserOp.plus ≠ Term.Stuck := by
  intro h
  cases h

private theorem numeral_zero_ne_stuck :
    Term.Numeral 0 ≠ Term.Stuck := by
  intro h
  cases h

private theorem ubvRawExpansion_get_nil (b : Term) :
    ∀ start len : Nat,
      __eo_get_nil_rec (Term.UOp UserOp.plus)
        (ubvRawExpansion b start len) = Term.Numeral 0 := by
  intro start len
  induction len generalizing start with
  | zero =>
      simp [ubvRawExpansion, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq, __eo_requires,
        native_teq, native_and, native_not, SmtEval.native_not, native_ite,
        native_to_real, native_mk_rational]
  | succ len ih =>
      simp [ubvRawExpansion, __eo_get_nil_rec, __eo_requires, native_teq,
        native_not, SmtEval.native_not, native_ite, ih]

private theorem ubvRawExpansion_is_list (b : Term) (start len : Nat) :
    __eo_is_list (Term.UOp UserOp.plus) (ubvRawExpansion b start len) =
      Term.Boolean true := by
  exact eo_is_list_true_of_get_nil_eq plus_ne_stuck
    (ubvRawExpansion_ne_stuck b start len)
    (ubvRawExpansion_get_nil b start len) numeral_zero_ne_stuck

private theorem ubvRawExpansion_succ_not_nil
    (b : Term) (start len : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.plus)
      (ubvRawExpansion b start (Nat.succ len)) =
      Term.Boolean false := by
  simp [ubvRawExpansion, __eo_is_list_nil, __eo_is_list_nil_plus,
    __eo_to_q, __eo_is_eq, native_teq, native_and, native_not,
    SmtEval.native_not, native_mk_rational]

private theorem ubvRawExpansion_singleton_eval (M : SmtModel)
    (b : Term) (w n : Int)
    (hEvalB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Binary w n)
    (hn : 0 <= n) :
    ∀ (start len : Nat),
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.plus)
              (ubvRawExpansion b start len))) =
        SmtValue.Numeral ((natScaledBitSum n.toNat start len : Nat) : Int) := by
  intro start len
  cases len with
  | zero =>
      have hIsList := ubvRawExpansion_is_list b start 0
      change __smtx_model_eval M
          (__eo_to_smt
            (__eo_requires
              (__eo_is_list (Term.UOp UserOp.plus) (ubvRawExpansion b start 0))
              (Term.Boolean true)
              (__eo_list_singleton_elim_2 (ubvRawExpansion b start 0)))) =
        SmtValue.Numeral ((natScaledBitSum n.toNat start 0 : Nat) : Int)
      rw [hIsList]
      simp [ubvRawExpansion, natScaledBitSum, __eo_requires,
        __eo_list_singleton_elim_2, native_teq, native_not,
        SmtEval.native_not, native_ite]
      change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
      rw [__smtx_model_eval.eq_2]
  | succ len =>
      cases len with
      | zero =>
          have hIsList := ubvRawExpansion_is_list b start 1
          change __smtx_model_eval M
              (__eo_to_smt
                (__eo_requires
                  (__eo_is_list (Term.UOp UserOp.plus)
                    (ubvRawExpansion b start 1))
                  (Term.Boolean true)
                  (__eo_list_singleton_elim_2 (ubvRawExpansion b start 1)))) =
            SmtValue.Numeral ((natScaledBitSum n.toNat start 1 : Nat) : Int)
          rw [hIsList]
          simp [ubvRawExpansion, __eo_requires, __eo_list_singleton_elim_2,
            __eo_is_list_nil, __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq,
            native_teq, native_and, native_not, SmtEval.native_not,
            native_ite, __eo_ite, native_to_real, native_mk_rational]
          rw [ubvBitAddend_eval M b w n start hEvalB hn]
          cases h : n.toNat.testBit start <;>
            simp [natScaledBitSum, h]
      | succ len =>
          have hIsList :=
            ubvRawExpansion_is_list b start (Nat.succ (Nat.succ len))
          have hTailNotNil :=
            ubvRawExpansion_succ_not_nil b (Nat.succ start) len
          have hSingleton :
              __eo_list_singleton_elim (Term.UOp UserOp.plus)
                  (ubvRawExpansion b start (Nat.succ (Nat.succ len))) =
                ubvRawExpansion b start (Nat.succ (Nat.succ len)) := by
            change __eo_requires
                (__eo_is_list (Term.UOp UserOp.plus)
                  (ubvRawExpansion b start (Nat.succ (Nat.succ len))))
                (Term.Boolean true)
                (__eo_list_singleton_elim_2
                  (ubvRawExpansion b start (Nat.succ (Nat.succ len)))) =
              ubvRawExpansion b start (Nat.succ (Nat.succ len))
            rw [hIsList]
            simp [__eo_requires, native_teq, native_not, SmtEval.native_not,
              native_ite]
            change __eo_list_singleton_elim_2
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start))
                  (ubvRawExpansion b (Nat.succ start) (Nat.succ len))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.plus) (ubvBitAddend b start))
                (ubvRawExpansion b (Nat.succ start) (Nat.succ len))
            simp [__eo_list_singleton_elim_2, hTailNotNil, __eo_ite,
              native_teq, native_ite]
          rw [hSingleton]
          exact
            ubvRawExpansion_eval M b w n hEvalB hn start
              (Nat.succ (Nat.succ len))

private theorem ubv_to_int_expansion_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (b : Term) (w : native_Nat)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.plus)
            (__abconv_ubv_to_int_elim b
              (__eo_requires (__eo_is_neg (__bv_bitwidth (__eo_typeof b)))
                (Term.Boolean false)
                (__iota_rec
                  (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                    (Term.Numeral 0) (__bv_bitwidth (__eo_typeof b)))
                  (Term.Numeral 0)))
              (Term.Numeral 1)))))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) b))) := by
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    intro h
    cases h
  have hEvalTy := type_preservation M hM (__eo_to_smt b) hbNN
  rw [hbTy] at hEvalTy
  rcases bitvec_value_canonical hEvalTy with ⟨n, hEvalB⟩
  have hValueTy :
      __smtx_typeof_value (SmtValue.Binary (native_nat_to_int w) n) =
        SmtType.BitVec w := by
    simpa [hEvalB] using hEvalTy
  have hWidthNonneg := bitvec_width_nonneg hValueTy
  have hPayloadMod := bitvec_payload_canonical hValueTy
  have hRange := bitvec_payload_range_of_canonical hWidthNonneg hPayloadMod
  have hnNonneg : 0 <= n := hRange.1
  have hRawEq :=
    ubv_generated_expansion_eq_raw b w hbTy
  have hEvalExpanded :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.plus)
              (__abconv_ubv_to_int_elim b
                (__eo_requires (__eo_is_neg (__bv_bitwidth (__eo_typeof b)))
                  (Term.Boolean false)
                  (__iota_rec
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0) (__bv_bitwidth (__eo_typeof b)))
                    (Term.Numeral 0)))
                (Term.Numeral 1)))) =
        SmtValue.Numeral n := by
    rw [hRawEq]
    have hEval :=
      ubvRawExpansion_singleton_eval M b (native_nat_to_int w) n
        hEvalB hnNonneg 0 w
    rw [hEval]
    have hNatLt : n.toNat < 2 ^ w := by
      have hltInt :
          ((n.toNat : Nat) : Int) < ((2 ^ w : Nat) : Int) := by
        simpa [Int.toNat_of_nonneg hnNonneg, native_int_pow2_nat] using
          hRange.2
      exact_mod_cast hltInt
    have hSum :
        ((natScaledBitSum n.toNat 0 w : Nat) : Int) = n := by
      rw [natScaledBitSum_eq]
      simp [Nat.mod_eq_of_lt hNatLt, Int.toNat_of_nonneg hnNonneg]
    exact congrArg SmtValue.Numeral hSum
  have hEvalOrig :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) b)) =
        SmtValue.Numeral n := by
    change __smtx_model_eval M (SmtTerm.ubv_to_int (__eo_to_smt b)) =
      SmtValue.Numeral n
    rw [smtx_eval_ubv_to_int_term_eq, hEvalB]
    rfl
  rw [hEvalExpanded, hEvalOrig]
  exact RuleProofs.smt_value_rel_refl _

private theorem ubv_to_int_elim_shape_of_ne_stuck (A : Term) :
    __eo_prog_ubv_to_int_elim A ≠ Term.Stuck ->
    ∃ b m,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.ubv_to_int) b)) m := by
  intro h
  by_cases hShape :
      ∃ b m,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) b)) m
  · exact hShape
  · have hStuck : __eo_prog_ubv_to_int_elim A = Term.Stuck := by
      rw [__eo_prog_ubv_to_int_elim.eq_2]
      intro b m hEq
      exact hShape ⟨b, m, hEq⟩
    exact False.elim (h hStuck)

public theorem cmd_step_ubv_to_int_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ubv_to_int_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ubv_to_int_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ubv_to_int_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.ubv_to_int_elim args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons A2 argsRest =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons n rest =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_ubv_to_int_elim A)
              change __eo_typeof (__eo_prog_ubv_to_int_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_ubv_to_int_elim A ≠ Term.Stuck := by
                exact hProgNe
              rcases ubv_to_int_elim_shape_of_ne_stuck A hProgNe' with
                ⟨b, m, hShape⟩
              subst A
              let lhs := Term.Apply (Term.UOp UserOp.ubv_to_int) b
              let width := __bv_bitwidth (__eo_typeof b)
              let indices :=
                __eo_requires (__eo_is_neg width) (Term.Boolean false)
                  (__iota_rec
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0) width)
                    (Term.Numeral 0))
              let expanded :=
                __eo_list_singleton_elim (Term.UOp UserOp.plus)
                  (__abconv_ubv_to_int_elim b indices (Term.Numeral 1))
              let orig :=
                Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) m
              have hReqNe :
                  __eo_requires expanded m orig ≠ Term.Stuck := by
                simpa [__eo_prog_ubv_to_int_elim, lhs, width, indices,
                  expanded, orig] using hProgNe'
              have hExpandedEq : expanded = m :=
                eo_requires_arg_eq_of_ne_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hMNe : m ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_ubv_to_int_elim
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) m) =
                    orig := by
                rw [__eo_prog_ubv_to_int_elim.eq_1]
                change __eo_requires expanded m orig = orig
                simp [__eo_requires, hExpandedEq, hMNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig, lhs] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    lhs m hOrigBool with
                ⟨_hSameTy, hLhsNN⟩
              have hUbvNN :
                  term_has_non_none_type
                    (SmtTerm.ubv_to_int (__eo_to_smt b)) := by
                unfold term_has_non_none_type
                exact hLhsNN
              rcases
                  bv_unop_ret_arg_of_non_none
                    (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
                    (by rw [smtx_typeof_ubv_to_int_term_eq]) hUbvNN with
                ⟨w, hbTy⟩
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt lhs)) := by
                simpa [expanded, indices, width, lhs] using
                  ubv_to_int_expansion_eval_rel M hM b w hbTy
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt lhs))
                    (__smtx_model_eval M (__eo_to_smt m)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_ubv_to_int_elim orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M lhs m hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
