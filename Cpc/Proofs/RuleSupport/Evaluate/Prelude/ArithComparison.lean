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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithOperands

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.native_zsub_lt_zero_eq_eval
    (n1 n2 : native_Int) :
    native_zlt (native_zplus n1 (native_zneg n2)) 0 =
      native_zlt n1 n2 := by
  exact native_zsub_lt_zero_eq n1 n2

theorem EvaluateProofInternal.native_qsub_lt_zero_eq_eval
    (q1 q2 : native_Rat) :
    native_qlt (native_qplus q1 (native_qneg q2))
        (native_mk_rational 0 1) =
      native_qlt q1 q2 := by
  exact native_qsub_lt_zero_eq q1 q2

theorem EvaluateProofInternal.eo_leq_int_result_eq
    (n1 n2 : native_Int) :
    __eo_or
        (__eo_is_neg
          (__eo_add (Term.Numeral n1) (__eo_neg (Term.Numeral n2))))
        (__eo_eq
          (__eo_to_q
            (__eo_add (Term.Numeral n1) (__eo_neg (Term.Numeral n2))))
          (Term.Rational (native_mk_rational 0 1))) =
      Term.Boolean (native_zleq n1 n2) := by
  unfold __eo_neg __eo_add __eo_is_neg __eo_to_q __eo_eq __eo_or
  simp only [native_teq, native_or]
  rw [native_zsub_lt_zero_eq]
  have hEq :
      decide
          (Term.Rational (native_mk_rational 0 1) =
            Term.Rational
              (native_to_real (native_zplus n1 (native_zneg n2)))) =
        native_zeq n1 n2 := by
    rw [show
        decide
            (Term.Rational (native_mk_rational 0 1) =
              Term.Rational
                (native_to_real (native_zplus n1 (native_zneg n2)))) =
          native_qeq
            (native_to_real (native_zplus n1 (native_zneg n2)))
            (native_mk_rational 0 1) by
      unfold native_qeq
      by_cases h :
          native_mk_rational 0 1 =
            native_to_real (native_zplus n1 (native_zneg n2))
      · have h' :
            native_to_real (native_zplus n1 (native_zneg n2)) =
              native_mk_rational 0 1 := h.symm
        have hTerm :
            Term.Rational (native_mk_rational 0 1) =
              Term.Rational
                (native_to_real (native_zplus n1 (native_zneg n2))) := by
          rw [h]
        simp only [hTerm, h', decide_true]
      · have h' :
            ¬ native_to_real (native_zplus n1 (native_zneg n2)) =
              native_mk_rational 0 1 := fun h' => h h'.symm
        have hTerm :
            ¬ Term.Rational (native_mk_rational 0 1) =
              Term.Rational
                (native_to_real (native_zplus n1 (native_zneg n2))) := by
          intro hTerm
          injection hTerm with hRat
          exact h hRat
        simp only [hTerm, h', decide_false]]
    rw [native_to_real_eq_zero_eq, native_zsub_eq_zero_eq]
  rw [hEq]
  unfold native_zlt native_zeq native_zleq
  by_cases hlt : n1 < n2
  · have hle : n1 ≤ n2 := by grind
    simp [hlt, hle]
  · by_cases heq : n1 = n2
    · have hle : n1 ≤ n2 := by grind
      simp [heq]
    · have hle : ¬ n1 ≤ n2 := by grind
      simp [hlt, heq, hle]

theorem EvaluateProofInternal.eo_leq_real_result_eq
    (q1 q2 : native_Rat) :
    __eo_or
        (__eo_is_neg
          (__eo_add (Term.Rational q1) (__eo_neg (Term.Rational q2))))
        (__eo_eq
          (__eo_to_q
            (__eo_add (Term.Rational q1) (__eo_neg (Term.Rational q2))))
          (Term.Rational (native_mk_rational 0 1))) =
      Term.Boolean (native_qleq q1 q2) := by
  unfold __eo_neg __eo_add __eo_is_neg __eo_to_q __eo_eq __eo_or
  simp only [native_teq, native_or]
  rw [native_qsub_lt_zero_eq]
  have hEq :
      decide
          (Term.Rational (native_mk_rational 0 1) =
            Term.Rational (native_qplus q1 (native_qneg q2))) =
        native_qeq q1 q2 := by
    rw [show
        decide
            (Term.Rational (native_mk_rational 0 1) =
              Term.Rational (native_qplus q1 (native_qneg q2))) =
          native_qeq (native_qplus q1 (native_qneg q2))
            (native_mk_rational 0 1) by
      unfold native_qeq
      by_cases h :
          native_mk_rational 0 1 =
            native_qplus q1 (native_qneg q2)
      · have h' :
            native_qplus q1 (native_qneg q2) =
              native_mk_rational 0 1 := h.symm
        have hTerm :
            Term.Rational (native_mk_rational 0 1) =
              Term.Rational (native_qplus q1 (native_qneg q2)) := by
          rw [h]
        simp only [hTerm, h', decide_true]
      · have h' :
            ¬ native_qplus q1 (native_qneg q2) =
              native_mk_rational 0 1 := fun h' => h h'.symm
        have hTerm :
            ¬ Term.Rational (native_mk_rational 0 1) =
              Term.Rational (native_qplus q1 (native_qneg q2)) := by
          intro hTerm
          injection hTerm with hRat
          exact h hRat
        simp only [hTerm, h', decide_false]]
    rw [native_qsub_eq_zero_eq]
  rw [hEq]
  unfold native_qlt native_qeq native_qleq
  by_cases hlt : q1 < q2
  · have hle : q1 ≤ q2 := by grind
    simp [hlt, hle]
  · by_cases heq : q1 = q2
    · have hle : q1 ≤ q2 := by grind
      simp [heq]
    · have hle : ¬ q1 ≤ q2 := by
        grind
      simp [hlt, heq, hle]

theorem EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    ∃ n : native_Int, x = Term.Numeral n := by
  cases x <;> try simp [__eo_to_q] at hNe
  case Numeral n =>
    exact ⟨n, rfl⟩
  case Rational q =>
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy

theorem EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> try simp [__eo_to_q] at hNe
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy
  case Rational q =>
    exact ⟨q, rfl⟩

theorem EvaluateProofInternal.eo_to_z_real_arg_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hNe : __eo_to_z x ≠ Term.Stuck) :
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> try simp [__eo_to_z] at hNe
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy
  case Rational q =>
    exact ⟨q, rfl⟩
  case String s =>
    change __smtx_typeof (SmtTerm.String s) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_4] at hxTy
    cases hValid : native_string_valid s <;>
      simp [native_ite, hValid] at hxTy
  case Binary w n =>
    change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_is_int_result_rel
    (M : SmtModel) (q : native_Rat) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_is_int (SmtValue.Rational q))
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_eq (__eo_to_q (__eo_to_z (Term.Rational q)))
            (__eo_to_q (Term.Rational q))))) := by
  by_cases hWhole : native_to_real (native_to_int q) = q
  · simp [RuleProofs.smt_value_rel, __smtx_model_eval_is_int,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_eq, native_veq, __eo_to_z, __eo_to_q,
      __eo_eq, native_teq, hWhole]
    rw [__smtx_model_eval.eq_1]
  · have hWhole' : q ≠ native_to_real (native_to_int q) := by
      intro h
      exact hWhole h.symm
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_is_int,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_eq, native_veq, __eo_to_z, __eo_to_q,
      __eo_eq, native_teq, hWhole, hWhole']
    rw [__smtx_model_eval.eq_1]

theorem EvaluateProofInternal.eo_lt_int_run_args_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hNe : __eo_is_neg (__eo_add x (__eo_neg y)) ≠ Term.Stuck) :
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  rcases EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck
      (__eo_add x (__eo_neg y)) hNe with
    hInnerInt | hInnerReal
  · rcases hInnerInt with ⟨n, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Int := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_numeral_of_typeof_int x (__eo_neg y)
        hInnerTy with
      ⟨nx, nNegY, hx, hNegY⟩
    have hNegYTy : __eo_typeof (__eo_neg y) =
        Term.UOp UserOp.Int := by
      rw [hNegY]
      rfl
    rcases EvaluateProofInternal.eo_neg_arg_numeral_of_typeof_int y hNegYTy with
      ⟨ny, hy⟩
    exact ⟨nx, ny, hx, hy⟩
  · rcases hInnerReal with ⟨q, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Real := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_rational_of_typeof_real x (__eo_neg y)
        hInnerTy with
      ⟨qx, _qNegY, hx, _hNegY⟩
    rw [hx] at hxTy
    change __smtx_typeof (SmtTerm.Rational qx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy

theorem EvaluateProofInternal.eo_lt_real_run_args_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Real)
    (hNe : __eo_is_neg (__eo_add x (__eo_neg y)) ≠ Term.Stuck) :
    ∃ qx : native_Rat, ∃ qy : native_Rat,
      x = Term.Rational qx ∧ y = Term.Rational qy := by
  rcases EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck
      (__eo_add x (__eo_neg y)) hNe with
    hInnerInt | hInnerReal
  · rcases hInnerInt with ⟨n, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Int := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_numeral_of_typeof_int x (__eo_neg y)
        hInnerTy with
      ⟨nx, _nNegY, hx, _hNegY⟩
    rw [hx] at hxTy
    change __smtx_typeof (SmtTerm.Numeral nx) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy
  · rcases hInnerReal with ⟨q, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Real := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_rational_of_typeof_real x (__eo_neg y)
        hInnerTy with
      ⟨qx, qNegY, hx, hNegY⟩
    have hNegYTy : __eo_typeof (__eo_neg y) =
        Term.UOp UserOp.Real := by
      rw [hNegY]
      rfl
    rcases EvaluateProofInternal.eo_neg_arg_rational_of_typeof_real y hNegYTy with
      ⟨qy, hy⟩
    exact ⟨qx, qy, hx, hy⟩

theorem EvaluateProofInternal.eo_zdiv_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny ∧
        native_zeq 0 ny = false := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · exact ⟨nx, ny, rfl, rfl, hZero⟩
      · simp [hZero, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx (native_binary_max wx))
                (Term.Binary wx
                  (native_mod_total (native_div_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.UOp UserOp.Int at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            change
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
                Term.UOp UserOp.Int at h
            cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_zmod_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny ∧
        native_zeq 0 ny = false := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · exact ⟨nx, ny, rfl, rfl, hZero⟩
      · simp [hZero, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx nx)
                (Term.Binary wx
                  (native_mod_total (native_mod_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.UOp UserOp.Int at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            change
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
                Term.UOp UserOp.Int at h
            cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_zdiv_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_zdiv x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · simp [hZero, native_ite] at h
        change Term.UOp UserOp.Int =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hZero, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx (native_binary_max wx))
                (Term.Binary wx
                  (native_mod_total (native_div_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            cases h
            exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_zmod_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_zmod x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · simp [hZero, native_ite] at h
        change Term.UOp UserOp.Int =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hZero, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx nx)
                (Term.Binary wx
                  (native_mod_total (native_mod_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            cases h
            exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_zero_extend_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int) :
    __eo_typeof
        (__eo_to_bin
          (__eo_add (__bv_bitwidth (__eo_typeof x)) (Term.Numeral i))
          (__eo_to_z x)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧ w = native_zplus wx i ∧
        __eo_to_bin
            (__eo_add (__bv_bitwidth (__eo_typeof x)) (Term.Numeral i))
            (__eo_to_z x) =
          Term.Binary (native_zplus wx i)
            (native_mod_total nx (native_int_pow2 (native_zplus wx i))) := by
  cases x <;> intro h
  case Binary wx nx =>
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral (native_zplus wx i))
            (Term.Numeral nx)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change
      __eo_typeof
          (native_ite (native_zleq (native_zplus wx i) 4294967296)
            (__eo_mk_binary (native_zplus wx i) nx) Term.Stuck) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases hLeMax : native_zleq (native_zplus wx i) 4294967296
    · simp [hLeMax, native_ite] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · simp [hLeMax, native_ite, __eo_mk_binary] at h
      cases hNonneg : native_zleq 0 (native_zplus wx i)
      · simp [hNonneg] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hNonneg] at h
        cases h
        refine ⟨wx, nx, rfl, rfl, ?_⟩
        change
          __eo_to_bin (Term.Numeral (native_zplus wx i))
              (Term.Numeral nx) =
            Term.Binary (native_zplus wx i)
              (native_mod_total nx (native_int_pow2 (native_zplus wx i)))
        simp [__eo_to_bin, __eo_mk_binary, hLeMax, hNonneg, native_ite]
  all_goals
    simp [__eo_to_bin, __eo_add, __bv_bitwidth, __eo_to_z] at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

