module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.Core
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.Core
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCode
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCode
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCase
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCase
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReverse
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReverse

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.native_str_to_int_rev_acc :
    native_String -> native_Int -> native_Int -> native_Int
  | [], _e, n => n
  | c :: cs, e, n =>
      let d := native_zplus (c : native_Int) (-48 : native_Int)
      match native_and (native_zlt d 10) (native_not (native_zlt d 0)) with
      | true =>
          EvaluateProofInternal.native_str_to_int_rev_acc cs (native_zmult e 10)
            (native_zplus (native_zmult d e) n)
      | false => -1

def EvaluateProofInternal.native_decimal_digits_lsb : native_String -> native_Nat
  | [] => 0
  | c :: cs => (c - 48) + 10 * EvaluateProofInternal.native_decimal_digits_lsb cs

theorem EvaluateProofInternal.str_to_int_guard_eq_digit (c : native_Char) :
    native_and
        (native_zlt (native_zplus (c : native_Int) (-48 : native_Int)) 10)
        (native_not
          (native_zlt (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
      impl_native_char_is_digit c := by
  unfold impl_native_char_is_digit native_zplus native_zlt native_not native_and
  by_cases h48 : 48 ≤ c
  · by_cases h57 : c ≤ 57
    · have h48i : (48 : Int) ≤ (c : Int) := Int.ofNat_le.mpr h48
      have h57i : (c : Int) ≤ (57 : Int) := Int.ofNat_le.mpr h57
      have hLt : (c : Int) + (-48 : Int) < 10 := by omega
      have hNotNeg : ¬(c : Int) + (-48 : Int) < 0 := by omega
      simp [h48, h57, hLt, hNotNeg]
    · have h57lt : 57 < c := Nat.lt_of_not_ge h57
      have h57lti : (57 : Int) < (c : Int) := Int.ofNat_lt.mpr h57lt
      have hNotLt : ¬(c : Int) + (-48 : Int) < 10 := by omega
      simp [h48, h57, hNotLt]
  · have h48lt : c < 48 := Nat.lt_of_not_ge h48
    have h48lti : (c : Int) < (48 : Int) := Int.ofNat_lt.mpr h48lt
    have hNeg : (c : Int) + (-48 : Int) < 0 := by omega
    simp [h48, hNeg]

theorem EvaluateProofInternal.str_to_int_eval_rec_strCharChain :
    ∀ (xs : native_String) (e n : native_Int),
      native_string_valid xs = true ->
        __str_to_int_eval_rec (EvaluateProofInternal.strCharChain xs)
            (Term.Numeral e) (Term.Numeral n) =
          Term.Numeral (EvaluateProofInternal.native_str_to_int_rev_acc xs e n)
  | [], _e, _n, _hValid => by
      rfl
  | c :: cs, e, n, hValid => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hValid with
        ⟨hcValid, hcsValid⟩
      unfold EvaluateProofInternal.strCharChain
      unfold __str_to_int_eval_rec
      rw [EvaluateProofInternal.eo_to_z_singleton hcValid]
      dsimp [__eo_add, __eo_mul]
      let d := native_zplus (c : native_Int) (-48 : native_Int)
      have hGuardTerm :
          __eo_and (__eo_gt (Term.Numeral 10) (Term.Numeral d))
              (__eo_not (__eo_is_neg (Term.Numeral d))) =
            Term.Boolean
              (native_and (native_zlt d 10) (native_not (native_zlt d 0))) := by
        simp [__eo_gt, __eo_is_neg, __eo_not, __eo_and, d]
      rw [hGuardTerm]
      cases hGuard :
          native_and (native_zlt d 10) (native_not (native_zlt d 0))
      · simp [eo_ite_false, EvaluateProofInternal.native_str_to_int_rev_acc, d, hGuard]
      · rw [eo_ite_true]
        simp [EvaluateProofInternal.native_str_to_int_rev_acc, d, hGuard]
        exact EvaluateProofInternal.str_to_int_eval_rec_strCharChain cs
          (native_zmult e 10)
          (native_zplus (native_zmult d e) n) hcsValid

theorem EvaluateProofInternal.native_str_to_int_rev_acc_all_digits :
    ∀ (xs : native_String) (e n : native_Int),
      xs.all impl_native_char_is_digit = true ->
        EvaluateProofInternal.native_str_to_int_rev_acc xs e n =
          native_zplus n
            (native_zmult e (Int.ofNat (EvaluateProofInternal.native_decimal_digits_lsb xs)))
  | [], e, n, _hDigits => by
      simp [EvaluateProofInternal.native_str_to_int_rev_acc, EvaluateProofInternal.native_decimal_digits_lsb,
        native_zplus, native_zmult]
  | c :: cs, e, n, hDigits => by
      have hDigitParts :
          impl_native_char_is_digit c = true ∧
            cs.all impl_native_char_is_digit = true := by
        simpa using hDigits
      have hDigit : impl_native_char_is_digit c = true := hDigitParts.1
      have hTailDigits : cs.all impl_native_char_is_digit = true := hDigitParts.2
      have hGuard :
          native_and
              (native_zlt
                (native_zplus (c : native_Int) (-48 : native_Int)) 10)
              (native_not
                (native_zlt
                  (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
            true :=
        (EvaluateProofInternal.str_to_int_guard_eq_digit c).trans hDigit
      simp [EvaluateProofInternal.native_str_to_int_rev_acc, hGuard]
      have hTail :=
        EvaluateProofInternal.native_str_to_int_rev_acc_all_digits cs
          (native_zmult e 10)
          (native_zplus
            (native_zmult
              (native_zplus (c : native_Int) (-48 : native_Int)) e) n)
          hTailDigits
      rw [hTail]
      unfold EvaluateProofInternal.native_decimal_digits_lsb native_zplus native_zmult
      have hRange : 48 ≤ c ∧ c ≤ 57 := by
        unfold impl_native_char_is_digit at hDigit
        simpa using hDigit
      have hCast :
          ((c - 48 : Nat) : Int) = (c : Int) + (-48 : Int) := by
        rw [Int.ofNat_sub hRange.1]
        rfl
      rw [Int.natCast_add, Int.natCast_mul]
      rw [hCast]
      cases cs <;>
        simp [EvaluateProofInternal.native_decimal_digits_lsb, Int.mul_add,
          Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.mul_assoc,
          Int.mul_comm, Int.mul_left_comm]

theorem EvaluateProofInternal.native_str_to_int_rev_acc_not_all_digits :
    ∀ (xs : native_String) (e n : native_Int),
      xs.all impl_native_char_is_digit ≠ true ->
        EvaluateProofInternal.native_str_to_int_rev_acc xs e n = (-1 : native_Int)
  | [], _e, _n, hDigits => by
      simp at hDigits
  | c :: cs, e, n, hDigits => by
      by_cases hDigit : impl_native_char_is_digit c = true
      · have hTailNot : cs.all impl_native_char_is_digit ≠ true := by
          intro hTail
          apply hDigits
          simp [hDigit, hTail]
        have hGuard :
            native_and
                (native_zlt
                  (native_zplus (c : native_Int) (-48 : native_Int)) 10)
                (native_not
                  (native_zlt
                    (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
              true :=
          (EvaluateProofInternal.str_to_int_guard_eq_digit c).trans hDigit
        simp [EvaluateProofInternal.native_str_to_int_rev_acc, hGuard]
        exact EvaluateProofInternal.native_str_to_int_rev_acc_not_all_digits cs
          (native_zmult e 10)
          (native_zplus
            (native_zmult
              (native_zplus (c : native_Int) (-48 : native_Int)) e) n)
          hTailNot
      · have hGuard := EvaluateProofInternal.str_to_int_guard_eq_digit c
        have hGuardFalse :
            native_and
                (native_zlt
                  (native_zplus (c : native_Int) (-48 : native_Int)) 10)
                (native_not
                  (native_zlt
                    (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
              false := by
          rw [hGuard]
          cases h : impl_native_char_is_digit c <;> simp [h] at hDigit ⊢
        simp [EvaluateProofInternal.native_str_to_int_rev_acc, hGuardFalse]

theorem EvaluateProofInternal.native_decimal_digits_lsb_append_singleton :
    ∀ (xs : native_String) (c : native_Char),
      EvaluateProofInternal.native_decimal_digits_lsb (xs ++ [c]) =
        EvaluateProofInternal.native_decimal_digits_lsb xs + (c - 48) * 10 ^ xs.length
  | [], c => by
      simp [EvaluateProofInternal.native_decimal_digits_lsb]
  | x :: xs, c => by
      rw [show (x :: xs) ++ [c] = x :: (xs ++ [c]) by rfl]
      change
        (x - 48) + 10 * EvaluateProofInternal.native_decimal_digits_lsb (xs ++ [c]) =
          (x - 48) + 10 * EvaluateProofInternal.native_decimal_digits_lsb xs +
            (c - 48) * 10 ^ (xs.length + 1)
      rw [EvaluateProofInternal.native_decimal_digits_lsb_append_singleton xs c]
      simp [Nat.pow_succ, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc,
        Nat.mul_comm]

theorem EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc :
    ∀ (xs : native_String) (acc : native_Nat),
      xs.foldl (fun acc c => 10 * acc + (c - 48)) acc =
        acc * 10 ^ xs.length + impl_native_decimal_digits_to_nat xs
  | [], acc => by
      simp [impl_native_decimal_digits_to_nat]
  | c :: cs, acc => by
      rw [show
          (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) acc =
            cs.foldl (fun acc c => 10 * acc + (c - 48))
              (10 * acc + (c - 48)) by
        rfl]
      rw [EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc cs
        (10 * acc + (c - 48))]
      rw [show impl_native_decimal_digits_to_nat (c :: cs) =
          (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 by
        rfl]
      rw [show
          (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 =
            cs.foldl (fun acc c => 10 * acc + (c - 48)) (c - 48) by
        simp]
      rw [EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc cs (c - 48)]
      simp [Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc,
        Nat.mul_comm]

theorem EvaluateProofInternal.native_decimal_digits_to_nat_cons
    (c : native_Char) (cs : native_String) :
    impl_native_decimal_digits_to_nat (c :: cs) =
      (c - 48) * 10 ^ cs.length + impl_native_decimal_digits_to_nat cs := by
  rw [show impl_native_decimal_digits_to_nat (c :: cs) =
      (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 by
    rfl]
  rw [show
      (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 =
        cs.foldl (fun acc c => 10 * acc + (c - 48)) (c - 48) by
    simp]
  exact EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc cs (c - 48)

theorem EvaluateProofInternal.native_decimal_digits_lsb_reverse_eq :
    ∀ s : native_String,
      EvaluateProofInternal.native_decimal_digits_lsb s.reverse = impl_native_decimal_digits_to_nat s
  | [] => by
      rfl
  | c :: cs => by
      rw [List.reverse_cons]
      rw [EvaluateProofInternal.native_decimal_digits_lsb_append_singleton cs.reverse c]
      rw [EvaluateProofInternal.native_decimal_digits_lsb_reverse_eq cs]
      rw [EvaluateProofInternal.native_decimal_digits_to_nat_cons c cs]
      simp [List.length_reverse, Nat.add_comm]

theorem EvaluateProofInternal.list_all_reverse_eq {α : Type} (p : α -> Bool) :
    ∀ xs : List α, xs.reverse.all p = xs.all p
  | [] => by
      rfl
  | x :: xs => by
      rw [List.reverse_cons, List.all_append]
      rw [EvaluateProofInternal.list_all_reverse_eq p xs]
      cases hp : p x <;> cases hx : xs.all p <;> simp [hp, hx]

theorem EvaluateProofInternal.str_to_int_result_string
    {str : native_String}
    (hValid : native_string_valid str = true) :
    __eo_ite (__eo_is_str (Term.String str))
        (__eo_ite (__eo_eq (Term.String str) (Term.String []))
          (Term.Numeral (-1 : native_Int))
          (__str_to_int_eval_rec
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro (Term.String str))))
            (Term.Numeral 1) (Term.Numeral 0)))
        (__eo_mk_apply (Term.UOp UserOp.str_to_int) (Term.String str)) =
      Term.Numeral (native_str_to_int str) := by
  have hIsStr :
      __eo_is_str (Term.String str) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  cases str with
  | nil =>
      simp [__eo_eq, __eo_ite, native_teq, native_ite, native_str_to_int]
  | cons c cs =>
      rw [show __eo_eq (Term.String (c :: cs)) (Term.String []) =
          Term.Boolean false by
        simp [__eo_eq, native_teq]]
      rw [eo_ite_false]
      rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
      rw [EvaluateProofInternal.eo_list_rev_strCharChain]
      have hRevValid :
          native_string_valid (c :: cs).reverse = true := by
        unfold native_string_valid at hValid ⊢
        rw [EvaluateProofInternal.list_all_reverse_eq native_char_valid, hValid]
      rw [EvaluateProofInternal.str_to_int_eval_rec_strCharChain (c :: cs).reverse 1 0
        hRevValid]
      by_cases hDigits : (c :: cs).all impl_native_char_is_digit = true
      · have hRevDigits :
            (c :: cs).reverse.all impl_native_char_is_digit = true := by
          rw [EvaluateProofInternal.list_all_reverse_eq impl_native_char_is_digit, hDigits]
        rw [EvaluateProofInternal.native_str_to_int_rev_acc_all_digits (c :: cs).reverse 1 0
          hRevDigits]
        rw [EvaluateProofInternal.native_decimal_digits_lsb_reverse_eq (c :: cs)]
        simp [native_str_to_int, hDigits, native_zplus, native_zmult]
      · have hRevDigits :
            (c :: cs).reverse.all impl_native_char_is_digit ≠ true := by
          intro hRev
          apply hDigits
          rwa [EvaluateProofInternal.list_all_reverse_eq impl_native_char_is_digit] at hRev
        rw [EvaluateProofInternal.native_str_to_int_rev_acc_not_all_digits (c :: cs).reverse 1 0
          hRevDigits]
        simp [native_str_to_int, hDigits]

theorem EvaluateProofInternal.str_to_int_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__eo_ite (__eo_eq t (Term.String []))
          (Term.Numeral (-1 : native_Int))
          (__str_to_int_eval_rec
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))
            (Term.Numeral 1) (Term.Numeral 0)))
        (__eo_mk_apply (Term.UOp UserOp.str_to_int) t) =
      Term.Apply (Term.UOp UserOp.str_to_int) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.native_string_valid_reverse_local
    {str : native_String}
    (hValid : native_string_valid str = true) :
    native_string_valid str.reverse = true := by
  rw [native_string_valid, List.all_eq_true] at hValid ⊢
  intro c hc
  exact hValid c (by simpa using List.mem_reverse.mp hc)

theorem EvaluateProofInternal.native_string_valid_append_local
    {xs ys : native_String}
    (hxs : native_string_valid xs = true)
    (hys : native_string_valid ys = true) :
    native_string_valid (xs ++ ys) = true := by
  rw [native_string_valid, List.all_eq_true] at hxs hys ⊢
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hxs c hc
  · exact hys c hc

theorem EvaluateProofInternal.native_string_valid_substr_local
    {str : native_String} (i n : native_Int)
    (hValid : native_string_valid str = true) :
    native_string_valid (native_str_substr str i n) = true := by
  unfold native_str_substr
  by_cases hGuard :
      (decide (i < 0) || decide (n ≤ 0) ||
          decide (i ≥ native_str_len str)) = true
  · simp [hGuard, native_string_valid]
  ·
    simp [hGuard]
    exact native_string_valid_take _
      (native_string_valid_drop (Int.toNat i) hValid)

theorem EvaluateProofInternal.eo_eq_true_eq_local
    (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    x = y := by
  intro h
  have hyx : y = x := by
    cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢ <;>
      assumption
  exact hyx.symm

theorem EvaluateProofInternal.eo_requires_arg_eq_of_ne_stuck_local
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem EvaluateProofInternal.eo_requires_result_ne_stuck_of_ne_stuck_local
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      z ≠ Term.Stuck := by
  intro h hz
  have hxy : x = y := EvaluateProofInternal.eo_requires_arg_eq_of_ne_stuck_local h
  subst y
  subst z
  simp [__eo_requires, native_ite, native_not, native_teq] at h

