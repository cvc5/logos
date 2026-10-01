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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringFromInt
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringFromInt
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCase
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCase
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReverse
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReverse
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithEvaluation
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithEvaluation

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_len_typeof_int_of_ne_stuck
    (x : Term)
    (hNe : __eo_len x ≠ Term.Stuck) :
    __eo_typeof (__eo_len x) = Term.UOp UserOp.Int := by
  cases x <;> simp [__eo_len] at hNe ⊢
  all_goals
    change __eo_lit_type_Numeral (Term.Numeral _) =
      Term.UOp UserOp.Int
    rfl

theorem EvaluateProofInternal.eo_to_z_typeof_int_of_ne_stuck
    (x : Term)
    (hNe : __eo_to_z x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_z x) = Term.UOp UserOp.Int := by
  cases x <;> simp [__eo_to_z] at hNe ⊢
  case String s =>
    cases hLen : native_zeq 1 (native_str_len s) <;>
      simp [hLen, native_ite] at hNe ⊢
    change __eo_lit_type_Numeral
        (Term.Numeral (native_str_to_code s)) =
      Term.UOp UserOp.Int
    rfl
  all_goals
    first
    | change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl

theorem EvaluateProofInternal.eo_str_to_code_body_typeof_int
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      (let len := __eo_len x
       __eo_ite (__eo_eq len (Term.Numeral 1)) (__eo_to_z x)
        (__eo_ite (__eo_is_z len) (Term.Numeral (-1 : native_Int))
          (__eo_mk_apply (Term.UOp UserOp.str_to_code) x))) ≠
        Term.Stuck) :
    __eo_typeof
        (let len := __eo_len x
         __eo_ite (__eo_eq len (Term.Numeral 1)) (__eo_to_z x)
          (__eo_ite (__eo_is_z len) (Term.Numeral (-1 : native_Int))
            (__eo_mk_apply (Term.UOp UserOp.str_to_code) x))) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_len, __eo_eq, __eo_ite, __eo_is_z,
      __eo_is_z_internal, __eo_to_z, __eo_mk_apply, native_ite,
      native_teq, native_not, native_and] at hTy hNe ⊢
  case String s =>
    by_cases hLen : (1 : native_Int) = native_str_len s
    · simp [hLen, native_zeq] at hNe ⊢
      change __eo_lit_type_Numeral
          (Term.Numeral (native_str_to_code s)) =
        Term.UOp UserOp.Int
      rfl
    · simp [hLen] at hNe ⊢
      change __eo_lit_type_Numeral
          (Term.Numeral (-1 : native_Int)) =
        Term.UOp UserOp.Int
      rfl
  all_goals
    first
    | split <;> simp at hNe ⊢
      change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl
    | change __eo_typeof_str_to_code (__eo_typeof _) =
        Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl
    | cases hTy

theorem EvaluateProofInternal.eo_to_str_typeof_seq_char_of_ne_stuck
    (x : Term)
    (hNe : __eo_to_str x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_str x) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases x <;> simp [__eo_to_str] at hNe ⊢
  case Numeral n =>
    cases hGuard : native_and (native_zleq 0 n) (native_zlt n 196608) <;>
      simp [hGuard, native_ite] at hNe ⊢
    change __eo_lit_type_String
        (Term.String (native_str_from_code n)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rfl
  case String s =>
    rfl

theorem EvaluateProofInternal.eo_concat_typeof_seq_char_of_left_seq_char_and_ne_stuck
    (a b : Term)
    (hA :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe : __eo_concat a b ≠ Term.Stuck) :
    __eo_typeof (__eo_concat a b) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases a <;> cases b <;> simp [__eo_concat] at hA hNe ⊢
  case String.String s t =>
    rfl
  all_goals
    cases hA

theorem EvaluateProofInternal.str_case_conv_rec_strCharChain_typeof_seq_char_of_ne_stuck :
    ∀ (s : native_String) (isLower : native_Bool),
      __str_case_conv_rec (EvaluateProofInternal.strCharChain s) (Term.Boolean isLower) ≠
        Term.Stuck ->
      __eo_typeof
          (__str_case_conv_rec (EvaluateProofInternal.strCharChain s)
            (Term.Boolean isLower)) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  | [], _isLower, _hNe => by
      simp [EvaluateProofInternal.strCharChain, __str_case_conv_rec]
      change __eo_lit_type_String (Term.String []) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rfl
  | c :: cs, true, hNe => by
      unfold EvaluateProofInternal.strCharChain
      change
        __eo_typeof
            (__eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 91)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 64)))
                    (Term.Numeral 32)
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean true))) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      have hConcatNe :
          __eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 91)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 64)))
                    (Term.Numeral 32)
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean true)) ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.strCharChain, __str_case_conv_rec] using hNe
      have hHeadNe :
          __eo_to_str
              (__eo_add (__eo_to_z (Term.String [c]))
                (__eo_ite
                  (__eo_and (__eo_gt (Term.Numeral 91)
                    (__eo_to_z (Term.String [c])))
                    (__eo_gt (__eo_to_z (Term.String [c]))
                      (Term.Numeral 64)))
                  (Term.Numeral 32)
                  (Term.Numeral 0))) ≠ Term.Stuck := by
        intro hHead
        apply hConcatNe
        rw [hHead]
        rfl
      have hHeadTy :=
        EvaluateProofInternal.eo_to_str_typeof_seq_char_of_ne_stuck _ hHeadNe
      exact
        EvaluateProofInternal.eo_concat_typeof_seq_char_of_left_seq_char_and_ne_stuck
          _ _ hHeadTy hConcatNe
  | c :: cs, false, hNe => by
      unfold EvaluateProofInternal.strCharChain
      change
        __eo_typeof
            (__eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 123)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 96)))
                    (Term.Numeral (-32 : native_Int))
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean false))) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      have hConcatNe :
          __eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 123)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 96)))
                    (Term.Numeral (-32 : native_Int))
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean false)) ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.strCharChain, __str_case_conv_rec] using hNe
      have hHeadNe :
          __eo_to_str
              (__eo_add (__eo_to_z (Term.String [c]))
                (__eo_ite
                  (__eo_and (__eo_gt (Term.Numeral 123)
                    (__eo_to_z (Term.String [c])))
                    (__eo_gt (__eo_to_z (Term.String [c]))
                      (Term.Numeral 96)))
                  (Term.Numeral (-32 : native_Int))
                  (Term.Numeral 0))) ≠ Term.Stuck := by
        intro hHead
        apply hConcatNe
        rw [hHead]
        rfl
      have hHeadTy :=
        EvaluateProofInternal.eo_to_str_typeof_seq_char_of_ne_stuck _ hHeadNe
      exact
        EvaluateProofInternal.eo_concat_typeof_seq_char_of_left_seq_char_and_ne_stuck
          _ _ hHeadTy hConcatNe

theorem EvaluateProofInternal.eo_str_to_lower_body_typeof_seq_char
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_is_str x)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
            (Term.Boolean true))
          (__eo_mk_apply (Term.UOp UserOp.str_to_lower) x)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, native_and, native_not]
      at hTy hNe ⊢
  case String s =>
    rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
    exact EvaluateProofInternal.str_case_conv_rec_strCharChain_typeof_seq_char_of_ne_stuck
      s true (by
        simpa [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain] using hNe)
  all_goals
    first
    | change __eo_typeof_str_to_lower (__eo_typeof _) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rw [hTy]
      rfl
    | cases hTy

theorem EvaluateProofInternal.eo_str_to_upper_body_typeof_seq_char
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_is_str x)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
            (Term.Boolean false))
          (__eo_mk_apply (Term.UOp UserOp.str_to_upper) x)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, native_and, native_not]
      at hTy hNe ⊢
  case String s =>
    rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
    exact EvaluateProofInternal.str_case_conv_rec_strCharChain_typeof_seq_char_of_ne_stuck
      s false (by
        simpa [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain] using hNe)
  all_goals
    first
    | change __eo_typeof_str_to_lower (__eo_typeof _) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rw [hTy]
      rfl
    | cases hTy

theorem EvaluateProofInternal.str_to_int_eval_rec_strCharChain_typeof_int_of_ne_stuck :
    ∀ (xs : native_String) (e n : native_Int),
      __str_to_int_eval_rec (EvaluateProofInternal.strCharChain xs)
          (Term.Numeral e) (Term.Numeral n) ≠ Term.Stuck ->
        __eo_typeof
            (__str_to_int_eval_rec (EvaluateProofInternal.strCharChain xs)
              (Term.Numeral e) (Term.Numeral n)) =
          Term.UOp UserOp.Int
  | [], _e, _n, _hNe => by
      change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl
  | c :: cs, e, n, hNe => by
      let d := native_zplus (native_str_to_code [c]) (-48 : native_Int)
      by_cases hGuard :
          native_zlt d 10 = true ∧ native_zlt d 0 = false
      · have hTailNe :
            __str_to_int_eval_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Numeral (native_zmult e 10))
                (Term.Numeral (native_zplus (native_zmult d e) n)) ≠
              Term.Stuck := by
          intro hTail
          apply hNe
          unfold EvaluateProofInternal.strCharChain
          unfold __str_to_int_eval_rec
          simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
            __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
            native_and, native_not, native_str_len, native_zeq, d,
            hGuard.1, hGuard.2, hTail]
        unfold EvaluateProofInternal.strCharChain
        unfold __str_to_int_eval_rec
        simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
          __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
          native_and, native_not, native_str_len, native_zeq, d,
          hGuard.1, hGuard.2]
        exact EvaluateProofInternal.str_to_int_eval_rec_strCharChain_typeof_int_of_ne_stuck
          cs (native_zmult e 10)
          (native_zplus (native_zmult d e) n) hTailNe
      · have hBad :
            native_zlt d 10 = false ∨ native_zlt d 0 = true := by
          cases h10 : native_zlt d 10 <;>
            cases h0 : native_zlt d 0 <;>
            simp [h10, h0] at hGuard ⊢
        rcases hBad with h10 | h0
        · unfold EvaluateProofInternal.strCharChain
          unfold __str_to_int_eval_rec
          simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
            __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
            native_and, native_not, native_str_len, native_zeq, d, h10]
          change __eo_lit_type_Numeral (Term.Numeral _) =
            Term.UOp UserOp.Int
          rfl
        · unfold EvaluateProofInternal.strCharChain
          unfold __str_to_int_eval_rec
          simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
            __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
            native_and, native_not, native_str_len, native_zeq, d, h0]
          change __eo_lit_type_Numeral (Term.Numeral _) =
            Term.UOp UserOp.Int
          rfl

theorem EvaluateProofInternal.eo_str_to_int_body_typeof_int
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_is_str x)
        (__eo_ite (__eo_eq x (Term.String []))
          (Term.Numeral (-1 : native_Int))
          (__str_to_int_eval_rec
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro x)))
            (Term.Numeral 1) (Term.Numeral 0)))
        (__eo_mk_apply (Term.UOp UserOp.str_to_int) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__eo_ite (__eo_eq x (Term.String []))
            (Term.Numeral (-1 : native_Int))
            (__str_to_int_eval_rec
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro x)))
              (Term.Numeral 1) (Term.Numeral 0)))
          (__eo_mk_apply (Term.UOp UserOp.str_to_int) x)) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_eq, __eo_mk_apply, native_ite, native_teq, native_and,
      native_not] at hTy hNe ⊢
  case String s =>
    cases s with
    | nil =>
        change __eo_lit_type_Numeral (Term.Numeral _) =
          Term.UOp UserOp.Int
        rfl
    | cons c cs =>
        rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
        rw [EvaluateProofInternal.eo_list_rev_strCharChain]
        exact EvaluateProofInternal.str_to_int_eval_rec_strCharChain_typeof_int_of_ne_stuck
          (c :: cs).reverse 1 0 (by
            simpa [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain,
              EvaluateProofInternal.eo_list_rev_strCharChain] using hNe)
  all_goals
    first
    | change __eo_typeof_str_to_code (__eo_typeof _) = Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | cases hTy

theorem EvaluateProofInternal.eo_str_rev_body_typeof_seq
    (x U : Term)
    (hTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe :
      __eo_ite (__eo_is_str x)
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro x)))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) x) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__str_nary_elim
            (__str_collect
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro x)))))
          (__eo_mk_apply (Term.UOp UserOp.str_rev) x)) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  cases x
  case String s =>
    rw [EvaluateProofInternal.str_rev_result_string]
    cases hTy
    rfl
  all_goals
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, native_and, native_not]
      at hTy hNe ⊢
  all_goals
    change __eo_typeof_str_rev (__eo_typeof _) =
      Term.Apply (Term.UOp UserOp.Seq) U
    rw [hTy]
    rfl

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_typeof_seq_char
    (x : Term)
    (hRunTy : __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int) :
    __eo_typeof (EvaluateProofInternal.eo_eval_str_from_int_rhs x) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases hRunX : __run_evaluate x
  case Numeral n =>
    rw [EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral (x := x) (n := n) hRunX]
    rfl
  all_goals
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunTy
      change Term.Stuck = Term.UOp UserOp.Int at hRunTy
      cases hRunTy
    have hNotNumeral :
        ∀ n : native_Int, __run_evaluate x ≠ Term.Numeral n := by
      intro n hNum
      rw [hRunX] at hNum
      cases hNum
    rw [EvaluateProofInternal.eo_eval_str_from_int_rhs_run_non_numeral
      (x := x) (t := __run_evaluate x) rfl hNotNumeral hRunXNe]
    change __eo_typeof_str_from_code (__eo_typeof (__run_evaluate x)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rw [hRunTy]
    rfl

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_typeof_seq_char
    (x : Term)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (hActive :
      EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠
        Term.Apply (Term.UOp UserOp.str_from_code) x) :
    __eo_typeof (EvaluateProofInternal.eo_eval_str_from_code_rhs x) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases hRunX : __run_evaluate x
  case Numeral n =>
    rw [EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_of_active
      (x := x) (n := n) hRunX hXEoInt hRunFromNe hActive]
    rfl
  all_goals
    exfalso
    apply hActive
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRunX]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z,
      __eo_is_z_internal, native_and, native_not]

theorem EvaluateProofInternal.int_ispow2_numeral_to_smt_type_bool
    (n : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (let isNeg := __eo_is_neg (Term.Numeral n)
           let isZ := __eo_is_z (Term.Numeral n)
           __eo_ite isZ
            (__eo_ite isNeg (Term.Boolean false)
              (__eo_eq (Term.Numeral n)
                (__eo_pow (Term.Numeral 2)
                  (__eo_ite isZ
                    (__eo_ite isNeg (Term.Numeral 0)
                      (__eo_log (Term.Numeral 2) (Term.Numeral n)))
                    (__eo_mk_apply (Term.UOp UserOp.int_log2)
                      (Term.Numeral n))))))
            (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
              (Term.Numeral n)))) =
      SmtType.Bool := by
  by_cases hNeg : n < 0
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_and, native_not, native_zlt, hNeg]
    rw [__smtx_typeof.eq_1]
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_eq, __eo_pow, __eo_log, native_ite, native_teq, native_and,
      native_not, native_zlt, hNeg, EvaluateProofInternal.native_int_log_two_eq_log2,
      eq_comm]
    rw [__smtx_typeof.eq_1]

theorem EvaluateProofInternal.int_ispow2_numeral_eval_rel
    (M : SmtModel) (n : native_Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.geq (SmtTerm.Numeral n) (SmtTerm.Numeral 0))
          (SmtTerm.eq (SmtTerm.Numeral n)
            (SmtTerm.int_pow2 (SmtTerm.int_log2 (SmtTerm.Numeral n))))))
      (__smtx_model_eval M
        (__eo_to_smt
          (let isNeg := __eo_is_neg (Term.Numeral n)
           let isZ := __eo_is_z (Term.Numeral n)
           __eo_ite isZ
            (__eo_ite isNeg (Term.Boolean false)
              (__eo_eq (Term.Numeral n)
                (__eo_pow (Term.Numeral 2)
                  (__eo_ite isZ
                    (__eo_ite isNeg (Term.Numeral 0)
                      (__eo_log (Term.Numeral 2) (Term.Numeral n)))
                    (__eo_mk_apply (Term.UOp UserOp.int_log2)
                      (Term.Numeral n))))))
            (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
              (Term.Numeral n))))) := by
  by_cases hNeg : n < 0
  · have hGeq : native_zleq 0 n = false := by
      unfold native_zleq
      rw [decide_eq_false_iff_not]
      exact Int.not_le.mpr hNeg
    simp [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_eq, __smtx_model_eval_and,
      __smtx_model_eval_int_pow2, __smtx_model_eval_int_log2,
      __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_and, native_not,
      native_veq, native_zlt, hNeg, hGeq, RuleProofs.smt_value_rel]
  · have hGeq : native_zleq 0 n = true := by
      unfold native_zleq
      rw [decide_eq_true_eq]
      exact Int.le_of_not_gt hNeg
    simp [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_eq, __smtx_model_eval_and,
      __smtx_model_eval_int_pow2, __smtx_model_eval_int_log2,
      __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite, __eo_eq,
      __eo_pow, __eo_log, native_ite, native_teq, native_and, native_not,
      native_veq, native_zlt, hGeq, hNeg, EvaluateProofInternal.native_int_log_two_eq_log2,
      native_int_pow2, RuleProofs.smt_value_rel, eq_comm]

