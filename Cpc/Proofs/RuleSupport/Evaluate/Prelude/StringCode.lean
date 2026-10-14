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
  change decide (c < 196608) = true at hc
  exact of_decide_eq_true hc

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
  have hLt : native_zlt (c : Int) 196608 = true := by
    change decide ((c : Int) < (196608 : Int)) = true
    exact decide_eq_true hcLtInt
  have hCond : native_and (native_zleq 0 (c : Int))
      (native_zlt (c : Int) 196608) = true := by
    change (native_zleq 0 (c : Int) &&
      native_zlt (c : Int) 196608) = true
    rw [hNonneg, hLt]
    rfl
  change (if native_and (native_zleq 0 (c : Int))
      (native_zlt (c : Int) 196608) = true then
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
  · have hNatLtFalse : ¬ Int.toNat n < 196608 := by
      intro hNatLt
      have hnHi : n < 196608 := (Int.toNat_lt hn0).mp hNatLt
      exact hBad ⟨hn0, hnHi⟩
    have hGuard :
        (decide (0 ≤ n) && native_char_valid (Int.toNat n)) = false := by
      simp [hn0, native_char_valid, hNatLtFalse]
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
        (__eo_ite (__eo_eq (Term.Numeral 196608) _v0)
          (Term.Boolean true) (__eo_gt (Term.Numeral 196608) _v0))
        (__eo_not (__eo_is_neg _v0)) (Term.Boolean false))
      (Term.Boolean false))
      (__eo_to_str n) (Term.String []))
    (Term.Apply (Term.UOp UserOp.str_from_code) n)

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_numeral_valid
    {n : native_Int}
    (h0 : 0 ≤ n)
    (hlt : n < 196608) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs (Term.Numeral n) =
      Term.String (native_str_from_code n) := by
  have hNotNeg : native_zlt n 0 = false := by
    rw [show native_zlt n 0 = decide (n < 0) by rfl]
    exact decide_eq_false (Int.not_lt.mpr h0)
  have hLt : native_zlt n 196608 = true := by
    rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
    exact decide_eq_true hlt
  have hNonneg : native_zleq 0 n = true := by
    rw [show native_zleq 0 n = decide (0 ≤ n) by rfl]
    exact decide_eq_true h0
  have hNe : n ≠ 196608 := by
    intro hEq
    have hSelf : (196608 : Int) < 196608 := by
      simpa [hEq] using hlt
    have hNotSelf : ¬ (196608 : Int) < 196608 := by
      decide
    exact hNotSelf hSelf
  have hNeSymm : (196608 : Int) ≠ n := by
    intro hEq
    exact hNe hEq.symm
  dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
  rw [show __run_evaluate (Term.Numeral n) = Term.Numeral n by rfl]
  simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
    __eo_to_str, __eo_is_neg, __eo_not, __eo_is_z_internal,
    native_and, native_not, hNotNeg, hLt, hNonneg, hNe]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_numeral_invalid_guard
    {n : native_Int}
    (hBad : ¬ (0 ≤ n ∧ n ≤ 196608)) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs (Term.Numeral n) =
      Term.String (native_str_from_code n) := by
  have hBadLt : ¬ (0 ≤ n ∧ n < 196608) := by
    intro h
    exact hBad ⟨h.1, Int.le_of_lt h.2⟩
  rw [EvaluateProofInternal.native_str_from_code_invalid hBadLt]
  by_cases h0 : 0 ≤ n
  · have hNotNeg : native_zlt n 0 = false := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_false (Int.not_lt.mpr h0)
    have hGt : native_zlt n 196608 = false := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_false (by
        intro hlt
        exact hBad ⟨h0, Int.le_of_lt hlt⟩)
    have hEq : native_zeq 196608 n = false := by
      rw [show native_zeq 196608 n = decide ((196608 : Int) = n) by rfl]
      exact decide_eq_false (by
        intro hEq
        have hnle : n ≤ 196608 := by
          rw [← hEq]
          exact Int.le_refl 196608
        exact hBad ⟨h0, hnle⟩)
    have hNe : n ≠ 196608 := by
      intro hn
      exact hBad ⟨h0, by rw [hn]; exact Int.le_refl 196608⟩
    have hNeSymm : (196608 : Int) ≠ n := by
      intro hn
      exact hNe hn.symm
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [show __run_evaluate (Term.Numeral n) = Term.Numeral n by rfl]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_z_internal, native_and, native_not, hGt, hNe]
  · have hNeg : native_zlt n 0 = true := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_true (Int.lt_of_not_ge h0)
    have hLt : native_zlt n 196608 = true := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_true (by
        exact Int.lt_trans (Int.lt_of_not_ge h0) (by decide))
    have hNe : n ≠ 196608 := by
      intro hn
      exact h0 (by rw [hn]; decide)
    have hNeSymm : (196608 : Int) ≠ n := by
      intro hn
      exact hNe hn.symm
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [show __run_evaluate (Term.Numeral n) = Term.Numeral n by rfl]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      hNeg, hLt, hNe]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_invalid_guard
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hBad : ¬ (0 ≤ n ∧ n ≤ 196608)) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  have hBadLt : ¬ (0 ≤ n ∧ n < 196608) := by
    intro h
    exact hBad ⟨h.1, Int.le_of_lt h.2⟩
  rw [EvaluateProofInternal.native_str_from_code_invalid hBadLt]
  by_cases h0 : 0 ≤ n
  · have hNotNeg : native_zlt n 0 = false := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_false (Int.not_lt.mpr h0)
    have hGt : native_zlt n 196608 = false := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_false (by
        intro hlt
        exact hBad ⟨h0, Int.le_of_lt hlt⟩)
    have hEq : native_zeq 196608 n = false := by
      rw [show native_zeq 196608 n = decide ((196608 : Int) = n) by rfl]
      exact decide_eq_false (by
        intro hEq
        have hnle : n ≤ 196608 := by
          rw [← hEq]
          exact Int.le_refl 196608
        exact hBad ⟨h0, hnle⟩)
    have hNe : n ≠ 196608 := by
      intro hn
      exact hBad ⟨h0, by rw [hn]; exact Int.le_refl 196608⟩
    have hNeSymm : (196608 : Int) ≠ n := by
      intro hn
      exact hNe hn.symm
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_z_internal, native_and, native_not, hGt, hNe]
  · have hNeg : native_zlt n 0 = true := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_true (Int.lt_of_not_ge h0)
    have hLt : native_zlt n 196608 = true := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_true (Int.lt_trans (Int.lt_of_not_ge h0) (by decide))
    have hNe : (196608 : Int) ≠ n := by
      intro hn
      exact h0 (by rw [← hn]; decide)
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      hNeg, hLt]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_valid
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (h0 : 0 ≤ n)
    (hlt : n < 196608) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  have hNotNeg : native_zlt n 0 = false := by
    rw [show native_zlt n 0 = decide (n < 0) by rfl]
    exact decide_eq_false (Int.not_lt.mpr h0)
  have hLt : native_zlt n 196608 = true := by
    rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
    exact decide_eq_true hlt
  have hNonneg : native_zleq 0 n = true := by
    rw [show native_zleq 0 n = decide (0 ≤ n) by rfl]
    exact decide_eq_true h0
  have hNe : n ≠ 196608 := by
    intro hEq
    have hSelf : (196608 : Int) < 196608 := by
      simpa [hEq] using hlt
    exact (by decide : ¬ (196608 : Int) < 196608) hSelf
  have hNeSymm : (196608 : Int) ≠ n := by
    intro hEq
    exact hNe hEq.symm
  cases x
  case Numeral m =>
    change Term.Numeral m = Term.Numeral n at hRun
    cases hRun
    exact EvaluateProofInternal.eo_eval_str_from_code_rhs_numeral_valid h0 hlt
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.UOp UserOp.Int at hXEoInt
    cases hXEoInt
  all_goals
    exfalso
    apply hRunFromNe
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      __eo_to_str, hNotNeg, hLt, hNe]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_max_false
    {x : Term}
    (hRun : __run_evaluate x = Term.Numeral 196608)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck) :
    False := by
  have hNotNeg : native_zlt (196608 : Int) 0 = false := by
    rw [show native_zlt (196608 : Int) 0 =
      decide ((196608 : Int) < 0) by rfl]
    exact decide_eq_false (by decide)
  have hLtFalse : native_zlt (196608 : Int) 196608 = false := by
    rw [show native_zlt (196608 : Int) 196608 =
      decide ((196608 : Int) < 196608) by rfl]
    exact decide_eq_false (by decide)
  have hNonneg : native_zleq 0 (196608 : Int) = true := by
    rw [show native_zleq 0 (196608 : Int) =
      decide (0 ≤ (196608 : Int)) by rfl]
    exact decide_eq_true (by decide)
  cases x
  case Numeral m =>
    change Term.Numeral m = Term.Numeral 196608 at hRun
    cases hRun
    apply hRunFromNe
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [show __run_evaluate (Term.Numeral (196608 : Int)) =
      Term.Numeral 196608 by rfl]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      __eo_to_str, hNotNeg, hLtFalse, hNonneg]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.UOp UserOp.Int at hXEoInt
    cases hXEoInt
  all_goals
    apply hRunFromNe
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      __eo_to_str, hNotNeg]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  by_cases hGuard : 0 ≤ n ∧ n ≤ 196608
  · rcases hGuard with ⟨h0, hnLe⟩
    by_cases hlt : n < 196608
    · exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_valid
        hRun hXEoInt hRunFromNe h0 hlt
    · have hGe : (196608 : Int) ≤ n := Int.le_of_not_gt hlt
      have hEq : n = 196608 := Int.le_antisymm hnLe hGe
      subst n
      exact False.elim
        (EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_max_false
          hRun hXEoInt hRunFromNe)
  · exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_invalid_guard hRun hGuard

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

