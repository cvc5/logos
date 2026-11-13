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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCase
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCase

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.native_str_replace_all_chain (pat repl : native_String) :
    Nat -> native_String -> native_String
  | _, [] => []
  | 0, c :: cs =>
      if native_string_prefix_eq pat (c :: cs) then
        repl ++ EvaluateProofInternal.native_str_replace_all_chain pat repl (pat.length - 1) cs
      else
        c :: EvaluateProofInternal.native_str_replace_all_chain pat repl 0 cs
  | skip + 1, _ :: cs =>
      EvaluateProofInternal.native_str_replace_all_chain pat repl skip cs

theorem EvaluateProofInternal.native_str_replace_all_chain_skip_eq_drop
    (pat repl : native_String) :
    ∀ (skip : Nat) (s : native_String),
      EvaluateProofInternal.native_str_replace_all_chain pat repl skip s =
        EvaluateProofInternal.native_str_replace_all_chain pat repl 0 (s.drop skip) := by
  intro skip
  induction skip with
  | zero =>
      intro s
      simp
  | succ skip ih =>
      intro s
      cases s with
      | nil =>
          simp [EvaluateProofInternal.native_str_replace_all_chain]
      | cons _c cs =>
          simpa [EvaluateProofInternal.native_str_replace_all_chain] using ih cs

theorem EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons
    (p : native_Char) (ps repl : native_String) :
    ∀ (s : native_String) (skip : Nat),
      __str_eval_replace_all_rec (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain (p :: ps))
          (Term.String repl) (Term.Numeral (skip : native_Int))
          (Term.Numeral ((p :: ps).length : native_Int)) =
        Term.String (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl skip s)
  | [], _skip => by
      simp [EvaluateProofInternal.strCharChain, EvaluateProofInternal.native_str_replace_all_chain,
        __str_eval_replace_all_rec]
  | c :: cs, 0 => by
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      change
        __eo_ite
            (__str_is_prefix_flat
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (EvaluateProofInternal.strCharChain cs))
              (EvaluateProofInternal.strCharChain (p :: ps)))
            (__eo_concat (Term.String repl)
              (__str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
                (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
                (__eo_add
                  (Term.Numeral ((p :: ps).length : native_Int))
                  (Term.Numeral (-1 : native_Int)))
                (Term.Numeral ((p :: ps).length : native_Int))))
            (__eo_concat (Term.String [c])
              (__str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
                (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
                (Term.Numeral 0)
                (Term.Numeral ((p :: ps).length : native_Int)))) =
          Term.String (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 (c :: cs))
      rw [show
          __str_is_prefix_flat
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (EvaluateProofInternal.strCharChain cs))
              (EvaluateProofInternal.strCharChain (p :: ps)) =
            __str_is_prefix_flat (EvaluateProofInternal.strCharChain (c :: cs))
              (EvaluateProofInternal.strCharChain (p :: ps)) by
        rfl]
      rw [EvaluateProofInternal.str_is_prefix_flat_strCharChain (c :: cs) (p :: ps)]
      by_cases hPref : native_string_prefix_eq (p :: ps) (c :: cs) = true
      · rw [hPref]
        rw [eo_ite_true]
        have hLenSub :
            (ps.length : native_Int) + 1 + (-1 : native_Int) =
              (ps.length : native_Int) := by
          rw [Int.add_assoc]
          simp
        rw [show
            __eo_add (Term.Numeral ((p :: ps).length : native_Int))
                (Term.Numeral (-1 : native_Int)) =
              Term.Numeral (((p :: ps).length - 1 : Nat) : native_Int) by
          simp [__eo_add, native_zplus, hLenSub]]
        rw [EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl cs
          ((p :: ps).length - 1)]
        simp [EvaluateProofInternal.native_str_replace_all_chain, hPref, __eo_concat,
          native_str_concat]
      · have hPrefFalse :
            native_string_prefix_eq (p :: ps) (c :: cs) = false :=
          by
            cases hp : native_string_prefix_eq (p :: ps) (c :: cs) <;>
              simp [hp] at hPref ⊢
        rw [hPrefFalse]
        rw [eo_ite_false]
        rw [show
            __str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
                (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
                (Term.Numeral 0)
                (Term.Numeral ((p :: ps).length : native_Int)) =
              Term.String
                (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 cs) by
          simpa using
            EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl cs 0]
        simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse, __eo_concat,
          native_str_concat]
  | c :: cs, skip + 1 => by
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      change
        __str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
            (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
            (__eo_add
              (Term.Numeral ((skip + 1 : Nat) : native_Int))
              (Term.Numeral (-1 : native_Int)))
            (Term.Numeral ((p :: ps).length : native_Int)) =
          Term.String
            (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl (skip + 1) (c :: cs))
      have hSkipSub :
          (skip : native_Int) + 1 + (-1 : native_Int) =
            (skip : native_Int) := by
        rw [Int.add_assoc]
        simp
      rw [show
          __eo_add (Term.Numeral ((skip + 1 : Nat) : native_Int))
              (Term.Numeral (-1 : native_Int)) =
            Term.Numeral (skip : native_Int) by
        simp [__eo_add, native_zplus, hSkipSub]]
      simpa [EvaluateProofInternal.native_str_replace_all_chain] using
        EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl cs skip

theorem EvaluateProofInternal.str_replace_all_result_strings_empty
    (s repl : native_String) :
    __eo_ite
        (__eo_and
          (__eo_and (__eo_is_str (Term.String s))
            (__eo_is_str (Term.String [])))
          (__eo_is_str (Term.String repl)))
        (__eo_ite (__eo_eq (Term.String []) (Term.String []))
          (Term.String s)
          (__str_eval_replace_all_rec
            (__str_flatten (__str_nary_intro (Term.String s)))
            (__str_flatten (__str_nary_intro (Term.String [])))
            (Term.String repl) (Term.Numeral 0)
            (__eo_len (Term.String []))))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_all) (Term.String s))
            (Term.String []))
          (Term.String repl)) =
      Term.String s := by
  simp [__eo_is_str, __eo_is_str_internal, __eo_and, __eo_eq, __eo_ite,
    native_and, native_teq, native_not, native_ite]

theorem EvaluateProofInternal.str_replace_all_result_strings_cons
    (s repl : native_String) (p : native_Char) (ps : native_String) :
    __eo_ite
        (__eo_and
          (__eo_and (__eo_is_str (Term.String s))
            (__eo_is_str (Term.String (p :: ps))))
          (__eo_is_str (Term.String repl)))
        (__eo_ite (__eo_eq (Term.String (p :: ps)) (Term.String []))
          (Term.String s)
          (__str_eval_replace_all_rec
            (__str_flatten (__str_nary_intro (Term.String s)))
            (__str_flatten (__str_nary_intro (Term.String (p :: ps))))
            (Term.String repl) (Term.Numeral 0)
            (__eo_len (Term.String (p :: ps)))))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_all) (Term.String s))
            (Term.String (p :: ps)))
          (Term.String repl)) =
      Term.String (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 s) := by
  have hGuard :
      __eo_and
          (__eo_and (__eo_is_str (Term.String s))
            (__eo_is_str (Term.String (p :: ps))))
          (__eo_is_str (Term.String repl)) =
        Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, __eo_and, native_and,
      native_teq, native_not]
  rw [hGuard, eo_ite_true]
  have hPatNe :
      __eo_eq (Term.String (p :: ps)) (Term.String []) =
        Term.Boolean false := by
    simp [__eo_eq, native_teq]
  rw [hPatNe, eo_ite_false]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain s]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain (p :: ps)]
  simpa [__eo_len, native_str_len] using
    EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl s 0

theorem EvaluateProofInternal.run_evaluate_typeof_eq_str_replace_all
    (b y x : Term) :
    __eo_typeof
        (__run_evaluate
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_replace_all) b) y) x)) =
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_all) b) y) x) := by
  cases b
  case String sb =>
    cases y
    case String sy =>
      cases x
      case String sx =>
        cases sy with
        | nil =>
          change
            __eo_typeof
                (__eo_ite
                  (__eo_and
                    (__eo_and (__eo_is_str (Term.String sb))
                      (__eo_is_str (Term.String [])))
                    (__eo_is_str (Term.String sx)))
                  (__eo_ite (__eo_eq (Term.String []) (Term.String []))
                    (Term.String sb)
                    (__str_eval_replace_all_rec
                      (__str_flatten (__str_nary_intro (Term.String sb)))
                      (__str_flatten (__str_nary_intro (Term.String [])))
                      (Term.String sx) (Term.Numeral 0)
                      (__eo_len (Term.String []))))
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_replace_all)
                        (Term.String sb))
                      (Term.String []))
                    (Term.String sx))) =
              __eo_typeof
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_replace_all)
                      (Term.String sb))
                    (Term.String []))
                  (Term.String sx))
          conv =>
            lhs
            rw [EvaluateProofInternal.str_replace_all_result_strings_empty sb sx]
          change
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
              __eo_typeof_str_replace
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
          simp [__eo_typeof_str_replace, __eo_requires, __eo_and, __eo_eq,
            native_and, native_ite, native_teq, native_not]
        | cons p ps =>
          change
            __eo_typeof
                (__eo_ite
                  (__eo_and
                    (__eo_and (__eo_is_str (Term.String sb))
                      (__eo_is_str (Term.String (p :: ps))))
                    (__eo_is_str (Term.String sx)))
                  (__eo_ite (__eo_eq (Term.String (p :: ps))
                      (Term.String []))
                    (Term.String sb)
                    (__str_eval_replace_all_rec
                      (__str_flatten (__str_nary_intro (Term.String sb)))
                      (__str_flatten
                        (__str_nary_intro (Term.String (p :: ps))))
                      (Term.String sx) (Term.Numeral 0)
                      (__eo_len (Term.String (p :: ps)))))
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_replace_all)
                        (Term.String sb))
                      (Term.String (p :: ps)))
                    (Term.String sx))) =
              __eo_typeof
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_replace_all)
                      (Term.String sb))
                    (Term.String (p :: ps)))
                  (Term.String sx))
          conv =>
            lhs
            rw [EvaluateProofInternal.str_replace_all_result_strings_cons sb sx p ps]
          change
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
              __eo_typeof_str_replace
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
          simp [__eo_typeof_str_replace, __eo_requires, __eo_and, __eo_eq,
            native_and, native_ite, native_teq, native_not]
      all_goals
        simp [__run_evaluate, __eo_is_str, __eo_is_str_internal,
          __eo_and, __eo_ite, __eo_eq, __eo_typeof_str_replace,
          __eo_requires, native_and, native_ite, native_teq, native_not]
    all_goals
      simp [__run_evaluate, __eo_is_str, __eo_is_str_internal,
        __eo_and, __eo_ite, __eo_eq, __eo_typeof_str_replace,
        __eo_requires, native_and, native_ite, native_teq, native_not]
  all_goals
    simp [__run_evaluate, __eo_is_str, __eo_is_str_internal,
      __eo_and, __eo_ite, __eo_eq, __eo_typeof_str_replace,
      __eo_requires, native_and, native_ite, native_teq, native_not]

theorem EvaluateProofInternal.native_string_valid_replace_all_chain
    (pat repl : native_String) :
    ∀ (s : native_String) (skip : Nat),
      native_string_valid s = true ->
      native_string_valid repl = true ->
        native_string_valid
          (EvaluateProofInternal.native_str_replace_all_chain pat repl skip s) = true
  | [], _skip, _hs, _hrepl => by
      rfl
  | c :: cs, 0, hs, hrepl => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      by_cases hPref : native_string_prefix_eq pat (c :: cs) = true
      · simp [EvaluateProofInternal.native_str_replace_all_chain, hPref]
        exact native_string_valid_append hrepl
          (EvaluateProofInternal.native_string_valid_replace_all_chain pat repl cs
            (pat.length - 1) hcs hrepl)
      · have hPrefFalse :
            native_string_prefix_eq pat (c :: cs) = false := by
          cases hp : native_string_prefix_eq pat (c :: cs) <;>
            simp [hp] at hPref ⊢
        have hTail :
            native_string_valid
              (EvaluateProofInternal.native_str_replace_all_chain pat repl 0 cs) = true :=
          EvaluateProofInternal.native_string_valid_replace_all_chain pat repl cs 0 hcs hrepl
        rw [native_string_valid, List.all_eq_true] at hTail
        simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse, native_string_valid,
          hc]
        exact hTail
  | c :: cs, skip + 1, hs, hrepl => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨_hc, hcs⟩
      simpa [EvaluateProofInternal.native_str_replace_all_chain] using
        EvaluateProofInternal.native_string_valid_replace_all_chain pat repl cs skip hcs hrepl

theorem EvaluateProofInternal.smtx_typeof_eo_string_seq_char_valid
    (s : native_String) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String s)) =
      SmtType.Seq T) :
    T = SmtType.Char ∧ native_string_valid s = true := by
  change __smtx_typeof (SmtTerm.String s) = SmtType.Seq T at hTy
  cases hValid : native_string_valid s
  · simp [__smtx_typeof, hValid, native_ite] at hTy
  · simp [__smtx_typeof, hValid, native_ite] at hTy
    cases hTy
    exact ⟨rfl, rfl⟩

