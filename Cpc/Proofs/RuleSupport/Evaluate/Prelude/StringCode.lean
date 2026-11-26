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

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_typeof_str_to_lower_eq_seq_char_arg
    {T : Term} :
    __eo_typeof_str_to_lower T =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases T <;> simp [__eo_typeof_str_to_lower] at h ⊢
  case Apply f x =>
    cases f <;> cases x <;> simp at h ⊢
    case UOp.UOp op arg =>
      cases op <;> cases arg <;> simp at h ⊢

theorem EvaluateProofInternal.eo_typeof_apply_str_to_lower_eq_seq_char_arg
    (t : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  change __eo_typeof_str_to_lower (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  exact EvaluateProofInternal.eo_typeof_str_to_lower_eq_seq_char_arg h

theorem EvaluateProofInternal.eo_typeof_apply_str_to_upper_eq_seq_char_arg
    (t : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  change __eo_typeof_str_to_lower (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  exact EvaluateProofInternal.eo_typeof_str_to_lower_eq_seq_char_arg h

theorem EvaluateProofInternal.eo_str_to_lower_result_arg_typeof_seq_char
    (t : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
            (Term.Boolean true))
          (__eo_mk_apply (Term.UOp UserOp.str_to_lower) t)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases t
  case String s =>
    rfl
  all_goals
    apply EvaluateProofInternal.eo_typeof_apply_str_to_lower_eq_seq_char_arg
    have hsimpa := h
    try simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite, native_teq, native_and, native_not] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.eo_str_to_upper_result_arg_typeof_seq_char
    (t : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
            (Term.Boolean false))
          (__eo_mk_apply (Term.UOp UserOp.str_to_upper) t)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases t
  case String s =>
    rfl
  all_goals
    apply EvaluateProofInternal.eo_typeof_apply_str_to_upper_eq_seq_char_arg
    have hsimpa := h
    try simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite, native_teq, native_and, native_not] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_seq_char
    (hMatch.symm.trans hTy)

theorem EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ U : Term,
      __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U ∧
        __eo_to_smt_type U = T := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_seq (hMatch.symm.trans hTy)

theorem EvaluateProofInternal.eo_typeof_str_rev_eq_seq_arg
    {T U : Term} :
    __eo_typeof_str_rev T = Term.Apply (Term.UOp UserOp.Seq) U ->
    T = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  cases T <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      assumption

theorem EvaluateProofInternal.eo_typeof_apply_str_rev_eq_seq_arg
    (t U : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) t) =
      Term.Apply (Term.UOp UserOp.Seq) U ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  change __eo_typeof_str_rev (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) U at h
  exact EvaluateProofInternal.eo_typeof_str_rev_eq_seq_arg h

theorem EvaluateProofInternal.native_char_valid_lt
    {c : native_Char} (hc : native_char_valid c = true) :
    c < 196608 := by
  have h : (c : Int) ≤ native_z_max_code_point := by
    unfold native_char_valid at hc
    exact of_decide_eq_true hc
  rw [Smtm.le_native_z_max_code_point_iff] at h
  exact_mod_cast h

theorem EvaluateProofInternal.native_str_to_code_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_str_to_code [c] = (c : Int) := by
  unfold native_str_to_code
  change (if native_char_valid c = true then (c : Int) else -1) = (c : Int)
  rw [hc]
  rfl

theorem EvaluateProofInternal.eo_to_z_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_z (Term.String [c]) = Term.Numeral (c : Int) := by
  have hLen : native_zeq 1 (native_str_len [c]) = true := by
    change decide ((1 : Int) = Int.ofNat [c].length) = true
    rfl
  change (if native_zeq 1 (native_str_len [c]) = true then
        Term.Numeral (native_str_to_code [c]) else Term.Stuck) =
      Term.Numeral (c : Int)
  rw [hLen]
  exact congrArg Term.Numeral (EvaluateProofInternal.native_str_to_code_singleton hc)

theorem EvaluateProofInternal.native_str_from_code_of_valid_nat
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_str_from_code (c : Int) = [c] := by
  have hNonneg : decide ((0 : Int) ≤ (c : Int)) = true :=
    decide_eq_true (Int.natCast_nonneg c)
  have hValid : native_char_valid (Int.toNat (c : Int)) = true := by
    change native_char_valid c = true
    exact hc
  have hCond : ((decide ((0 : Int) ≤ (c : Int))) &&
      native_char_valid (Int.toNat (c : Int))) = true := by
    rw [hNonneg, hValid]
    rfl
  unfold native_str_from_code
  rw [hCond]
  rfl

theorem EvaluateProofInternal.eo_to_str_of_valid_nat
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str (Term.Numeral (c : Int)) = Term.String [c] := by
  have hcLtNat : c < 196608 := EvaluateProofInternal.native_char_valid_lt hc
  have hcLtInt : (c : Int) < 196608 := Int.ofNat_lt.mpr hcLtNat
  have hNonneg : native_zleq 0 (c : Int) = true := by
    change decide ((0 : Int) ≤ (c : Int)) = true
    exact decide_eq_true (Int.natCast_nonneg c)
  have hLt : native_zleq (c : Int) native_z_max_code_point = true := by
    change decide ((c : Int) ≤ native_z_max_code_point) = true
    exact decide_eq_true ((Smtm.le_native_z_max_code_point_iff _).mpr hcLtInt)
  have hCond : native_and (native_zleq 0 (c : Int))
      (native_zleq (c : Int) native_z_max_code_point) = true := by
    change (native_zleq 0 (c : Int) &&
      native_zleq (c : Int) native_z_max_code_point) = true
    rw [hNonneg, hLt]
    rfl
  change (if native_and (native_zleq 0 (c : Int))
      (native_zleq (c : Int) native_z_max_code_point) = true then
        Term.String (native_str_from_code (c : Int)) else Term.Stuck) =
      Term.String [c]
  rw [hCond]
  exact congrArg Term.String (EvaluateProofInternal.native_str_from_code_of_valid_nat hc)

theorem EvaluateProofInternal.native_str_from_code_invalid
    {n : native_Int}
    (hBad : ¬ (0 ≤ n ∧ n < 196608)) :
    native_str_from_code n = [] := by
  unfold native_str_from_code
  by_cases hn0 : 0 ≤ n
  · have hGuard :
        (decide (0 ≤ n) && native_char_valid (Int.toNat n)) = false := by
      simp [hn0, native_char_valid]
      exact Int.not_lt.mp fun hnHi => hBad ⟨hn0, hnHi⟩
    rw [hGuard]
    rfl
  · have hGuard :
        (decide (0 ≤ n) && native_char_valid (Int.toNat n)) = false := by
      simp [hn0]
    rw [hGuard]
    rfl

def EvaluateProofInternal.eo_eval_str_from_code_rhs (n : Term) : Term :=
  let _v0 := __run_evaluate n
  let _v1 := __eo_is_z _v0
  __eo_ite _v1
    (__eo_ite
      (__eo_ite _v1
      (__eo_ite
        (__eo_ite (__eo_eq (Term.Numeral 196607) _v0)
          (Term.Boolean true) (__eo_gt (Term.Numeral 196607) _v0))
        (__eo_not (__eo_is_neg _v0)) (Term.Boolean false))
      (Term.Boolean false))
      (__eo_to_str n) (Term.String []))
    (Term.Apply (Term.UOp UserOp.str_from_code) n)

/-- The code point guard of `str.from_code`, `196607 >= n`, is `n < 196608`. -/
theorem EvaluateProofInternal.eo_eval_str_from_code_guard (n : native_Int) :
    __eo_ite (__eo_eq (Term.Numeral 196607) (Term.Numeral n))
        (Term.Boolean true) (__eo_gt (Term.Numeral 196607) (Term.Numeral n)) =
      Term.Boolean (decide (n < 196608)) := by
  by_cases h : n = 196607
  · subst h
    simp [__eo_ite, __eo_eq, native_teq, native_ite]
  · have hLt : decide (n < 196607) = decide (n < 196608) := by
      by_cases hl : n < 196607
      · have hl' : n < 196608 := Int.lt_trans hl (by decide)
        simp [hl, hl']
      · have hl' : ¬ n < 196608 := fun hn =>
          h (Int.le_antisymm (Int.lt_add_one_iff.mp hn) (Int.not_lt.mp hl))
        simp [hl, hl']
    simp [__eo_ite, __eo_eq, __eo_gt, native_teq, native_ite, native_zlt, h,
      ← hLt]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      if 0 ≤ n ∧ n < 196608 then __eo_to_str x else Term.String [] := by
  dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
  rw [hRun, EvaluateProofInternal.eo_eval_str_from_code_guard]
  by_cases h0 : 0 ≤ n <;> by_cases hl : n < 196608 <;>
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_is_z_internal,
      __eo_is_neg, __eo_not, native_and, native_not, native_zlt, h0, hl]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_invalid
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hBad : ¬ (0 ≤ n ∧ n < 196608)) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  rw [EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral hRun,
    ite_eq_right hBad, EvaluateProofInternal.native_str_from_code_invalid hBad]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_valid
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (h0 : 0 ≤ n)
    (hlt : n < 196608) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  have hRhs := EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral hRun
  rw [ite_eq_left ⟨h0, hlt⟩] at hRhs
  rw [hRhs]
  rw [hRhs] at hRunFromNe
  cases x
  case Numeral m =>
    change Term.Numeral m = Term.Numeral n at hRun
    cases hRun
    simp [__eo_to_str, native_ite, native_and, native_zleq, native_zlt, h0, hlt]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.UOp UserOp.Int at hXEoInt
    cases hXEoInt
  all_goals
    exfalso
    exact hRunFromNe (by simp [__eo_to_str])

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  by_cases hGuard : 0 ≤ n ∧ n < 196608
  · exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_valid
      hRun hXEoInt hRunFromNe hGuard.1 hGuard.2
  · exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_invalid
      hRun hGuard

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_of_active
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (hActive :
      EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠
        Term.Apply (Term.UOp UserOp.str_from_code) x) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq
    hRun hXEoInt hRunFromNe

