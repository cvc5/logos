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

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.strCharChain_get_nil :
    ∀ s : native_String,
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (EvaluateProofInternal.strCharChain s) = Term.String []
  | [] => by
      simp [EvaluateProofInternal.strCharChain, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
        native_ite, native_teq, native_not]
  | _c :: cs => by
      simp [EvaluateProofInternal.strCharChain, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not]
      exact EvaluateProofInternal.strCharChain_get_nil cs

theorem EvaluateProofInternal.strCharChain_ne_stuck :
    ∀ s : native_String, EvaluateProofInternal.strCharChain s ≠ Term.Stuck
  | [] => by
      intro h
      cases h
  | _ :: _ => by
      intro h
      cases h

theorem EvaluateProofInternal.strCharChain_is_list :
    ∀ s : native_String,
      __eo_is_list (Term.UOp UserOp.str_concat)
        (EvaluateProofInternal.strCharChain s) = Term.Boolean true
  | [] => by
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) (Term.String [])) =
          Term.Boolean true
      rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.String []) = Term.String [] by
        exact EvaluateProofInternal.strCharChain_get_nil []]
      exact eo_is_ok_true_of_ne_stuck _ (by intro h; cases h)
  | c :: cs => by
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (EvaluateProofInternal.strCharChain cs))) =
          Term.Boolean true
      rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
            (EvaluateProofInternal.strCharChain cs)) = Term.String [] by
        exact EvaluateProofInternal.strCharChain_get_nil (c :: cs)]
      exact eo_is_ok_true_of_ne_stuck _ (by intro h; cases h)

theorem EvaluateProofInternal.eo_list_rev_rec_strCharChain :
    ∀ s t : native_String,
      __eo_list_rev_rec (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain t) =
        EvaluateProofInternal.strCharChain (s.reverse ++ t)
  | [], t => by
      cases t <;> rfl
  | c :: cs, t => by
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat)
        (Term.String [c]) (EvaluateProofInternal.strCharChain cs) (EvaluateProofInternal.strCharChain t)
        (EvaluateProofInternal.strCharChain_ne_stuck t)]
      rw [show
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.String [c])) (EvaluateProofInternal.strCharChain t) =
          EvaluateProofInternal.strCharChain (c :: t) by
        rfl]
      rw [EvaluateProofInternal.eo_list_rev_rec_strCharChain cs (c :: t)]
      simp [List.reverse_cons, List.append_assoc]

theorem EvaluateProofInternal.eo_list_rev_strCharChain :
    ∀ s : native_String,
      __eo_list_rev (Term.UOp UserOp.str_concat) (EvaluateProofInternal.strCharChain s) =
        EvaluateProofInternal.strCharChain s.reverse
  | s => by
      change
        __eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) (EvaluateProofInternal.strCharChain s))
          (Term.Boolean true)
          (__eo_list_rev_rec (EvaluateProofInternal.strCharChain s)
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (EvaluateProofInternal.strCharChain s))) =
        EvaluateProofInternal.strCharChain s.reverse
      rw [EvaluateProofInternal.strCharChain_is_list s]
      simp [__eo_requires, native_ite, native_teq, native_not]
      rw [EvaluateProofInternal.strCharChain_get_nil s]
      simpa [EvaluateProofInternal.strCharChain, List.append_nil] using
        EvaluateProofInternal.eo_list_rev_rec_strCharChain s []

theorem EvaluateProofInternal.str_collect_strCharChain :
    ∀ s : native_String,
      __str_collect (EvaluateProofInternal.strCharChain s) =
        match s with
        | [] => Term.String []
        | _ =>
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String s))
              (Term.String [])
  | [] => by
      change
        __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String []
      change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
        Term.String []
      exact eo_requires_self_eq_of_ne_stuck _ _
        (by intro h; cases h)
  | c :: cs => by
      have hLen :
          __eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1) =
            Term.Boolean true := by
        rfl
      cases cs with
      | nil =>
          change
            __eo_ite
                (__eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1))
                (__str_collect_merge (Term.String [c])
                  (__str_collect (Term.String [])))
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (__str_collect (Term.String []))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (Term.String [])
          rw [hLen, eo_ite_true]
          have hCollectEmpty :
              __str_collect (Term.String []) = Term.String [] := by
            change
              __eo_requires (Term.String [])
                (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
              Term.String []
            change
              __eo_requires (Term.String []) (Term.String []) (Term.String []) =
              Term.String []
            exact eo_requires_self_eq_of_ne_stuck _ _
              (by intro h; cases h)
          rw [hCollectEmpty]
          rfl
      | cons d ds =>
          change
            __eo_ite
                (__eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1))
                (__str_collect_merge (Term.String [c])
                  (__str_collect (EvaluateProofInternal.strCharChain (d :: ds))))
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (__str_collect (EvaluateProofInternal.strCharChain (d :: ds)))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String (c :: d :: ds)))
                (Term.String [])
          rw [hLen, eo_ite_true]
          rw [EvaluateProofInternal.str_collect_strCharChain (d :: ds)]
          change
            __eo_ite (__eo_is_str (Term.String (d :: ds)))
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.str_concat)
                    (__eo_concat (Term.String [c]) (Term.String (d :: ds))))
                  (Term.String []))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat)
                      (Term.String (d :: ds)))
                    (Term.String []))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String (c :: d :: ds)))
                (Term.String [])
          rw [show __eo_is_str (Term.String (d :: ds)) = Term.Boolean true by
            rfl]
          rw [eo_ite_true]
          rfl

theorem EvaluateProofInternal.str_collect_elim_strCharChain :
    ∀ s : native_String,
      __str_nary_elim (__str_collect (EvaluateProofInternal.strCharChain s)) =
        Term.String s
  | [] => by
      rw [EvaluateProofInternal.str_collect_strCharChain []]
      change
        __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String []
      change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
        Term.String []
      exact eo_requires_self_eq_of_ne_stuck _ _
        (by intro h; cases h)
  | c :: cs => by
      rw [EvaluateProofInternal.str_collect_strCharChain (c :: cs)]
      change
        __eo_ite
            (__eo_eq (Term.String [])
              (__seq_empty (__eo_typeof (Term.String (c :: cs)))))
            (Term.String (c :: cs))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.String (c :: cs)))
              (Term.String [])) =
          Term.String (c :: cs)
      have hEq :
          __eo_eq (Term.String [])
              (__seq_empty (__eo_typeof (Term.String (c :: cs)))) =
            Term.Boolean true := by
        rfl
      rw [hEq, eo_ite_true]

theorem EvaluateProofInternal.str_rev_string_char_chain :
    ∀ s : native_String,
      __str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (EvaluateProofInternal.strCharChain s))) =
        Term.String s.reverse
  | s => by
      rw [EvaluateProofInternal.eo_list_rev_strCharChain s]
      exact EvaluateProofInternal.str_collect_elim_strCharChain s.reverse

theorem EvaluateProofInternal.str_leq_eval_rec_strCharChain :
    ∀ s t : native_String,
      native_string_valid s = true ->
      native_string_valid t = true ->
        __str_leq_eval_rec (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain t) =
          Term.Boolean (native_or (decide (s = t)) (native_str_lt s t))
  | [], [], _hs, _ht => by
      rfl
  | [], _d :: _ds, _hs, _ht => by
      rfl
  | _c :: _cs, [], _hs, _ht => by
      rfl
  | c :: cs, d :: ds, hs, ht => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local ht with ⟨hd, hds⟩
      have hTail := EvaluateProofInternal.str_leq_eval_rec_strCharChain cs ds hcs hds
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      rw [show EvaluateProofInternal.strCharChain (d :: ds) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [d]))
          (EvaluateProofInternal.strCharChain ds) by
        rfl]
      unfold __str_leq_eval_rec
      rw [EvaluateProofInternal.eo_to_z_singleton hc, EvaluateProofInternal.eo_to_z_singleton hd]
      by_cases hcd : c = d
      · subst d
        simp [__eo_eq, native_teq, native_ite, native_or, native_str_lt,
          hTail]
      · have hdcNe : ¬ d = c := by
          intro h
          exact hcd h.symm
        have hNeList : c :: cs ≠ d :: ds := by
          intro h
          exact hcd (List.cons.inj h).1
        by_cases hlt : c < d
        · have hltInt : (c : Int) < (d : Int) := Int.ofNat_lt.mpr hlt
          simp [__eo_eq, __eo_gt, native_teq, native_ite, native_or,
            native_str_lt, List.cons_lt_cons_iff, hcd, hdcNe, hNeList,
            hlt]
          change decide ((c : Int) < (d : Int)) = true
          exact decide_eq_true hltInt
        · have hdc : d < c := by
            rcases Nat.lt_trichotomy c d with h | h | h
            · exact False.elim (hlt h)
            · exact False.elim (hcd h)
            · exact h
          have hnotInt : ¬ (c : Int) < (d : Int) := by
            intro hInt
            exact hlt (Int.ofNat_lt.mp hInt)
          simp [__eo_eq, __eo_gt, native_teq, native_ite, native_or,
            native_str_lt, List.cons_lt_cons_iff, hcd, hdcNe, hNeList,
            hlt]
          change decide ((c : Int) < (d : Int)) = false
          exact decide_eq_false hnotInt

theorem EvaluateProofInternal.eo_is_str_false_of_not_string
    (t : Term)
    (hNotString : ∀ s : native_String, t ≠ Term.String s) :
    __eo_is_str t = Term.Boolean false := by
  cases t <;>
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not] at hNotString ⊢

theorem EvaluateProofInternal.str_rev_result_string
    {s : native_String} :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro (Term.String s))))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) (Term.String s)) =
      Term.String s.reverse := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    rfl
  rw [hIsStr, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
  exact EvaluateProofInternal.str_rev_string_char_chain s

theorem EvaluateProofInternal.str_rev_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) t) =
      Term.Apply (Term.UOp UserOp.str_rev) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.str_leq_result_strings
    {s t : native_String}
    (hs : native_string_valid s = true)
    (ht : native_string_valid t = true) :
    __eo_ite
        (__eo_and (__eo_is_str (Term.String s))
          (__eo_is_str (Term.String t)))
        (__str_leq_eval_rec
          (__str_flatten (__str_nary_intro (Term.String s)))
          (__str_flatten (__str_nary_intro (Term.String t))))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_leq) (Term.String s))
          (Term.String t)) =
      Term.Boolean (native_or (decide (s = t)) (native_str_lt s t)) := by
  have hGuard :
      __eo_and (__eo_is_str (Term.String s))
          (__eo_is_str (Term.String t)) =
        Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, __eo_and, native_teq,
      native_and, native_not]
  rw [hGuard, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain s]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain t]
  exact EvaluateProofInternal.str_leq_eval_rec_strCharChain s t hs ht

theorem EvaluateProofInternal.str_leq_result_non_strings
    {s t : Term}
    (hNotBoth :
      ¬ ∃ sx sy : native_String, s = Term.String sx ∧ t = Term.String sy)
    (hsNe : s ≠ Term.Stuck)
    (htNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_and (__eo_is_str s) (__eo_is_str t))
        (__str_leq_eval_rec (__str_flatten (__str_nary_intro s))
          (__str_flatten (__str_nary_intro t)))
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) s) t) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) s) t := by
  have hGuard :
      __eo_and (__eo_is_str s) (__eo_is_str t) =
        Term.Boolean false := by
    cases s <;> cases t <;>
      simp [__eo_is_str, __eo_is_str_internal, __eo_and, native_teq,
        native_and, native_not] at hNotBoth hsNe htNe ⊢
  rw [hGuard, eo_ite_false]
  rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck
    (Term.UOp UserOp.str_leq) s (by intro h; cases h) hsNe]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck
    (Term.Apply (Term.UOp UserOp.str_leq) s) t
    (by intro h; cases h) htNe

theorem EvaluateProofInternal.eo_str_rev_result_arg_typeof_seq
    (t U : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_nary_elim
            (__str_collect
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro t)))))
          (__eo_mk_apply (Term.UOp UserOp.str_rev) t)) =
      Term.Apply (Term.UOp UserOp.Seq) U ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  cases t
  case String s =>
    rw [EvaluateProofInternal.str_rev_result_string] at h
    exact h
  all_goals
    apply EvaluateProofInternal.eo_typeof_apply_str_rev_eq_seq_arg
    have hsimpa := h
    try simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite, native_teq, native_and, native_not] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.str_to_lower_result_string
    {s : native_String}
    (hValid : native_string_valid s = true) :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String s)))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) (Term.String s)) =
      Term.String (native_str_to_lower s) := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
  exact EvaluateProofInternal.str_case_conv_rec_lower_char_chain s hValid

theorem EvaluateProofInternal.str_to_upper_result_string
    {s : native_String}
    (hValid : native_string_valid s = true) :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String s)))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) (Term.String s)) =
      Term.String (native_str_to_upper s) := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
  exact EvaluateProofInternal.str_case_conv_rec_upper_char_chain s hValid

theorem EvaluateProofInternal.str_to_lower_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) t) =
      Term.Apply (Term.UOp UserOp.str_to_lower) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.str_to_upper_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) t) =
      Term.Apply (Term.UOp UserOp.str_to_upper) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

