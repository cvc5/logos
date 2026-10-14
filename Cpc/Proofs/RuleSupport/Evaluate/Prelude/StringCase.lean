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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCode
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCode

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.str_case_lower_guard_singleton
    (c : native_Char) :
    __eo_and
        (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
        (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
      Term.Boolean ((decide (65 ≤ c)) && (decide (c ≤ 90))) := by
  have hUpper : native_zlt (c : Int) 91 = decide (c ≤ 90) := by
    by_cases h : c ≤ 90
    · have hNat : c < 91 := Nat.lt_succ_of_le h
      have hInt : (c : Int) < (91 : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt (c : Int) 91 = true by
        change decide ((c : Int) < (91 : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (c ≤ 90) = true by exact decide_eq_true h]
    · have hInt : ¬ (c : Int) < (91 : Int) := by
        intro hInt
        have hNat : c < 91 := Int.ofNat_lt.mp hInt
        exact h (Nat.le_of_lt_succ hNat)
      rw [show native_zlt (c : Int) 91 = false by
        change decide ((c : Int) < (91 : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (c ≤ 90) = false by exact decide_eq_false h]
  have hLower : native_zlt 64 (c : Int) = decide (65 ≤ c) := by
    by_cases h : 65 ≤ c
    · have hNat : 64 < c := Nat.lt_of_lt_of_le (by decide : 64 < 65) h
      have hInt : (64 : Int) < (c : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt 64 (c : Int) = true by
        change decide ((64 : Int) < (c : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (65 ≤ c) = true by exact decide_eq_true h]
    · have hInt : ¬ (64 : Int) < (c : Int) := by
        intro hInt
        have hNat : 64 < c := Int.ofNat_lt.mp hInt
        exact h (Nat.succ_le_of_lt hNat)
      rw [show native_zlt 64 (c : Int) = false by
        change decide ((64 : Int) < (c : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (65 ≤ c) = false by exact decide_eq_false h]
  change Term.Boolean (native_and (native_zlt (c : Int) 91)
    (native_zlt 64 (c : Int))) = _
  rw [hUpper, hLower]
  cases decide (65 ≤ c) <;> cases decide (c ≤ 90) <;> rfl

theorem EvaluateProofInternal.str_case_upper_guard_singleton
    (c : native_Char) :
    __eo_and
        (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
        (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
      Term.Boolean ((decide (97 ≤ c)) && (decide (c ≤ 122))) := by
  have hUpper : native_zlt (c : Int) 123 = decide (c ≤ 122) := by
    by_cases h : c ≤ 122
    · have hNat : c < 123 := Nat.lt_succ_of_le h
      have hInt : (c : Int) < (123 : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt (c : Int) 123 = true by
        change decide ((c : Int) < (123 : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (c ≤ 122) = true by exact decide_eq_true h]
    · have hInt : ¬ (c : Int) < (123 : Int) := by
        intro hInt
        have hNat : c < 123 := Int.ofNat_lt.mp hInt
        exact h (Nat.le_of_lt_succ hNat)
      rw [show native_zlt (c : Int) 123 = false by
        change decide ((c : Int) < (123 : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (c ≤ 122) = false by exact decide_eq_false h]
  have hLower : native_zlt 96 (c : Int) = decide (97 ≤ c) := by
    by_cases h : 97 ≤ c
    · have hNat : 96 < c := Nat.lt_of_lt_of_le (by decide : 96 < 97) h
      have hInt : (96 : Int) < (c : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt 96 (c : Int) = true by
        change decide ((96 : Int) < (c : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (97 ≤ c) = true by exact decide_eq_true h]
    · have hInt : ¬ (96 : Int) < (c : Int) := by
        intro hInt
        have hNat : 96 < c := Int.ofNat_lt.mp hInt
        exact h (Nat.succ_le_of_lt hNat)
      rw [show native_zlt 96 (c : Int) = false by
        change decide ((96 : Int) < (c : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (97 ≤ c) = false by exact decide_eq_false h]
  change Term.Boolean (native_and (native_zlt (c : Int) 123)
    (native_zlt 96 (c : Int))) = _
  rw [hUpper, hLower]
  cases decide (97 ≤ c) <;> cases decide (c ≤ 122) <;> rfl

theorem EvaluateProofInternal.str_case_conv_rec_lower_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (Term.String []))
        (Term.Boolean true) =
      Term.String [impl_native_char_to_lower c] := by
  cases hRange : ((decide (65 ≤ c)) && (decide (c ≤ 90)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardFalse]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 0)))
      (Term.String []) = Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl
  · have h90 : c ≤ 90 := by
      cases h65d : decide (65 ≤ c) <;> cases h90d : decide (c ≤ 90) <;>
        simp [h65d, h90d] at hRange
      exact of_decide_eq_true h90d
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hValidLower : native_char_valid (c + 32) = true := by
      change decide (c + 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.add_le_add_right h90 32) (by decide))
    have hCast : (c : Int) + 32 = ((c + 32 : Nat) : Int) := by
      rw [Int.natCast_add]
      rfl
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardTrue]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 32)))
      (Term.String []) = Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidLower]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_case_conv_rec_upper_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (Term.String []))
        (Term.Boolean false) =
      Term.String [impl_native_char_to_upper c] := by
  cases hRange : ((decide (97 ≤ c)) && (decide (c ≤ 122)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardFalse]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 0)))
      (Term.String []) = Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl
  · have h97 : 97 ≤ c := by
      cases h97d : decide (97 ≤ c) <;> cases h122d : decide (c ≤ 122) <;>
        simp [h97d, h122d] at hRange
      exact of_decide_eq_true h97d
    have h32 : 32 ≤ c := Nat.le_trans (by decide) h97
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hValidUpper : native_char_valid (c - 32) = true := by
      change decide (c - 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.sub_le c 32) (EvaluateProofInternal.native_char_valid_lt hc))
    have hCast : (c : Int) + (-32 : Int) = ((c - 32 : Nat) : Int) := by
      rw [Int.ofNat_sub h32]
      rfl
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardTrue]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + (-32 : Int))))
      (Term.String []) = Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidUpper]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_flatten_nary_intro_singleton
    (c : native_Char) :
    __str_flatten (__str_nary_intro (Term.String [c])) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (Term.String []) := by
  rfl

theorem EvaluateProofInternal.str_case_conv_rec_flatten_lower_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String [c])))
        (Term.Boolean true) =
      Term.String [impl_native_char_to_lower c] := by
  rw [EvaluateProofInternal.str_flatten_nary_intro_singleton c]
  exact EvaluateProofInternal.str_case_conv_rec_lower_singleton hc

theorem EvaluateProofInternal.str_case_conv_rec_flatten_upper_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String [c])))
        (Term.Boolean false) =
      Term.String [impl_native_char_to_upper c] := by
  rw [EvaluateProofInternal.str_flatten_nary_intro_singleton c]
  exact EvaluateProofInternal.str_case_conv_rec_upper_singleton hc

def EvaluateProofInternal.strCharChain : native_String -> Term
  | [] => Term.String []
  | c :: cs =>
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (EvaluateProofInternal.strCharChain cs)

theorem EvaluateProofInternal.native_string_valid_cons_parts_local
    {c : native_Char} {cs : native_String}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simp [native_string_valid] at h
  constructor
  · exact h.1
  · rw [native_string_valid, List.all_eq_true]
    intro x hx
    exact h.2 x hx

theorem EvaluateProofInternal.str_case_conv_lower_head_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str
        (__eo_add (__eo_to_z (Term.String [c]))
          (__eo_ite
            (__eo_and
              (__eo_gt (Term.Numeral 91) (__eo_to_z (Term.String [c])))
              (__eo_gt (__eo_to_z (Term.String [c])) (Term.Numeral 64)))
            (Term.Numeral 32) (Term.Numeral 0))) =
      Term.String [impl_native_char_to_lower c] := by
  cases hRange : ((decide (65 ≤ c)) && (decide (c ≤ 90)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardFalse]
    change __eo_to_str (Term.Numeral ((c : Int) + 0)) =
      Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl
  · have h90 : c ≤ 90 := by
      cases h65d : decide (65 ≤ c) <;> cases h90d : decide (c ≤ 90) <;>
        simp [h65d, h90d] at hRange
      exact of_decide_eq_true h90d
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hValidLower : native_char_valid (c + 32) = true := by
      change decide (c + 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.add_le_add_right h90 32) (by decide))
    have hCast : (c : Int) + 32 = ((c + 32 : Nat) : Int) := by
      rw [Int.natCast_add]
      rfl
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardTrue]
    change __eo_to_str (Term.Numeral ((c : Int) + 32)) =
      Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidLower]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_case_conv_upper_head_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str
        (__eo_add (__eo_to_z (Term.String [c]))
          (__eo_ite
            (__eo_and
              (__eo_gt (Term.Numeral 123) (__eo_to_z (Term.String [c])))
              (__eo_gt (__eo_to_z (Term.String [c])) (Term.Numeral 96)))
            (Term.Numeral (-32 : native_Int)) (Term.Numeral 0))) =
      Term.String [impl_native_char_to_upper c] := by
  cases hRange : ((decide (97 ≤ c)) && (decide (c ≤ 122)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardFalse]
    change __eo_to_str (Term.Numeral ((c : Int) + 0)) =
      Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl
  · have h97 : 97 ≤ c := by
      cases h97d : decide (97 ≤ c) <;> cases h122d : decide (c ≤ 122) <;>
        simp [h97d, h122d] at hRange
      exact of_decide_eq_true h97d
    have h32 : 32 ≤ c := Nat.le_trans (by decide) h97
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hValidUpper : native_char_valid (c - 32) = true := by
      change decide (c - 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.sub_le c 32) (EvaluateProofInternal.native_char_valid_lt hc))
    have hCast : (c : Int) + (-32 : Int) = ((c - 32 : Nat) : Int) := by
      rw [Int.ofNat_sub h32]
      rfl
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardTrue]
    change __eo_to_str (Term.Numeral ((c : Int) + (-32 : Int))) =
      Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidUpper]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_case_conv_rec_lower_char_chain :
    ∀ s : native_String,
      native_string_valid s = true ->
        __str_case_conv_rec (EvaluateProofInternal.strCharChain s) (Term.Boolean true) =
          Term.String (native_str_to_lower s)
  | [], _hs => by
      rfl
  | c :: cs, hs => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      have hTail := EvaluateProofInternal.str_case_conv_rec_lower_char_chain cs hcs
      unfold EvaluateProofInternal.strCharChain
      unfold __str_case_conv_rec
      dsimp
      rw [EvaluateProofInternal.str_case_conv_lower_head_singleton hc, hTail]
      rfl

theorem EvaluateProofInternal.str_case_conv_rec_upper_char_chain :
    ∀ s : native_String,
      native_string_valid s = true ->
        __str_case_conv_rec (EvaluateProofInternal.strCharChain s) (Term.Boolean false) =
          Term.String (native_str_to_upper s)
  | [], _hs => by
      rfl
  | c :: cs, hs => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      have hTail := EvaluateProofInternal.str_case_conv_rec_upper_char_chain cs hcs
      unfold EvaluateProofInternal.strCharChain
      unfold __str_case_conv_rec
      dsimp
      rw [EvaluateProofInternal.str_case_conv_upper_head_singleton hc, hTail]
      rfl

theorem EvaluateProofInternal.substrWord_zero_eq_strCharChain :
    ∀ s : native_String,
      RuleProofs.substrWord s 0 s.length = EvaluateProofInternal.strCharChain s
  | [] => by
      rfl
  | c :: cs => by
      rw [show (c :: cs).length = cs.length + 1 from rfl]
      change
        Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String (RuleProofs.extractString (c :: cs) 0)))
            (RuleProofs.substrWord (c :: cs) (0 + 1) cs.length) =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
            (EvaluateProofInternal.strCharChain cs)
      rw [RuleProofs.extractString_zero_cons c cs]
      rw [show (0 : native_Int) + 1 = 1 by rfl]
      rw [RuleProofs.substrWord_cons_tail c cs]
      rw [EvaluateProofInternal.substrWord_zero_eq_strCharChain cs]

theorem EvaluateProofInternal.str_flatten_nary_intro_string_char_chain
    (s : native_String) :
    __str_flatten (__str_nary_intro (Term.String s)) = EvaluateProofInternal.strCharChain s := by
  cases s with
  | nil =>
      rw [RuleProofs.str_flatten_nary_intro_empty]
      rfl
  | cons c cs =>
      rw [RuleProofs.str_flatten_nary_intro_cons c cs]
      exact EvaluateProofInternal.substrWord_zero_eq_strCharChain (c :: cs)

theorem EvaluateProofInternal.str_is_prefix_flat_strCharChain :
    ∀ s pat : native_String,
      __str_is_prefix_flat (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain pat) =
        Term.Boolean (native_string_prefix_eq pat s)
  | [], [] => by
      rfl
  | _c :: _cs, [] => by
      rfl
  | [], _p :: _ps => by
      simp [EvaluateProofInternal.strCharChain, native_string_prefix_eq, __str_is_prefix_flat,
        __eo_l_1___str_is_prefix_flat]
  | c :: cs, d :: ds => by
      by_cases hcd : c = d
      · subst d
        simp [EvaluateProofInternal.strCharChain, native_string_prefix_eq, __str_is_prefix_flat,
          __eo_eq, native_teq, native_ite,
          EvaluateProofInternal.str_is_prefix_flat_strCharChain cs ds]
      · have hdc : d ≠ c := by
          intro h
          exact hcd h.symm
        simp [EvaluateProofInternal.strCharChain, native_string_prefix_eq, __str_is_prefix_flat,
          __eo_l_1___str_is_prefix_flat, __eo_eq, native_teq, native_ite,
          hdc]

