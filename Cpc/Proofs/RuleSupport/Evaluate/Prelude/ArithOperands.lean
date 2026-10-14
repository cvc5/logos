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

theorem EvaluateProofInternal.eo_add_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_add x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
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

theorem EvaluateProofInternal.eo_add_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      exact ⟨nx, ny, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Int at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
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

theorem EvaluateProofInternal.eo_add_typeof_int_of_args_int
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_add x y ≠ Term.Stuck) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_add] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    rfl
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_add_int_args_numeral_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (_hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    __eo_add x y ≠ Term.Stuck ->
      ∃ nx ny : native_Int, x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  intro hNe
  cases x <;> cases y <;> simp only [__eo_add] at hNe
  case Numeral.Numeral nx ny =>
    exact ⟨nx, ny, rfl, rfl⟩
  case Rational.Rational rx _ry =>
    change __smtx_typeof (SmtTerm.Rational rx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy
  case Binary.Binary wx nx _wy _ny =>
    change __smtx_typeof (SmtTerm.Binary wx nx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 wx)
          (native_zeq nx (native_mod_total nx (native_int_pow2 wx))) <;>
      simp [native_ite, hValid] at hxTy
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_add_args_rational_of_typeof_real
    (x y : Term) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Real ->
    ∃ rx : native_Rat, ∃ ry : native_Rat,
      x = Term.Rational rx ∧ y = Term.Rational ry := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      exact ⟨rx, ry, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Real at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Real at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Real at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Real at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_add_typeof_real_of_args_real
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real)
    (hNe : __eo_add x y ≠ Term.Stuck) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Real := by
  cases x <;> cases y <;> simp [__eo_add] at hX hY hNe ⊢
  case Rational.Rational rx ry =>
    rfl
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_mul_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_mul x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
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

theorem EvaluateProofInternal.eo_mul_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      exact ⟨nx, ny, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Int at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
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

theorem EvaluateProofInternal.eo_mul_typeof_int_of_args_int
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_mul x y ≠ Term.Stuck) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_mul] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_mul_args_rational_of_typeof_real
    (x y : Term) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Real ->
    ∃ rx : native_Rat, ∃ ry : native_Rat,
      x = Term.Rational rx ∧ y = Term.Rational ry := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      exact ⟨rx, ry, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Real at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Real at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Real at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Real at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_mul_typeof_real_of_args_real
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real)
    (hNe : __eo_mul x y ≠ Term.Stuck) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Real := by
  cases x <;> cases y <;> simp [__eo_mul] at hX hY hNe ⊢
  case Rational.Rational rx ry =>
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_neg_arg_binary_of_eq_binary
    (x : Term) (w n : native_Int) :
    __eo_neg x = Term.Binary w n ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h <;> simp [__eo_neg] at h
  case Binary wx nx =>
    rcases h with ⟨hW, _⟩
    cases hW
    exact ⟨nx, rfl⟩

theorem EvaluateProofInternal.eo_neg_arg_numeral_of_typeof_int
    (x : Term) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, x = Term.Numeral nx := by
  cases x <;> intro h
  case Numeral nx =>
    exact ⟨nx, rfl⟩
  case Rational q =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
    cases h
  case Binary w n =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
        Term.UOp UserOp.Int at h
    cases h
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_neg_typeof_int_of_arg_int
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hNe : __eo_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Int := by
  cases x <;> simp [__eo_neg] at hX hNe ⊢
  case Numeral n =>
    rfl
  all_goals
    first
    | cases hX
    | contradiction

theorem EvaluateProofInternal.eo_neg_arg_rational_of_typeof_real
    (x : Term) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Real ->
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> intro h
  case Rational q =>
    exact ⟨q, rfl⟩
  case Numeral nx =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
    cases h
  case Binary w n =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
        Term.UOp UserOp.Real at h
    cases h
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_neg_typeof_real_of_arg_real
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hNe : __eo_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Real := by
  cases x <;> simp [__eo_neg] at hX hNe ⊢
  case Rational q =>
    rfl
  all_goals
    first
    | cases hX
    | contradiction

theorem EvaluateProofInternal.eo_is_neg_arg_arith_of_typeof_bool
    (x : Term) :
    __eo_typeof (__eo_is_neg x) = Term.Bool ->
      (∃ n : native_Int, x = Term.Numeral n) ∨
        (∃ q : native_Rat, x = Term.Rational q) := by
  cases x <;> intro h
  case Numeral n =>
    exact Or.inl ⟨n, rfl⟩
  case Rational q =>
    exact Or.inr ⟨q, rfl⟩
  all_goals
    simp only [__eo_is_neg] at h
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_int
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hNe : __eo_is_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_is_neg x) = Term.Bool := by
  cases x <;> simp [__eo_is_neg] at hX hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_real
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hNe : __eo_is_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_is_neg x) = Term.Bool := by
  cases x <;> simp [__eo_is_neg] at hX hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck
    (x : Term) :
    __eo_is_neg x ≠ Term.Stuck ->
      (∃ n : native_Int, x = Term.Numeral n) ∨
        (∃ q : native_Rat, x = Term.Rational q) := by
  cases x <;> intro h
  case Numeral n =>
    exact Or.inl ⟨n, rfl⟩
  case Rational q =>
    exact Or.inr ⟨q, rfl⟩
  all_goals
    simp only [__eo_is_neg] at h
    contradiction

theorem EvaluateProofInternal.eo_is_neg_int_arg_numeral_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_is_neg x ≠ Term.Stuck ->
      ∃ n : native_Int, x = Term.Numeral n := by
  intro hNe
  rcases EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck x hNe with
    ⟨n, hn⟩ | ⟨q, hq⟩
  · exact ⟨n, hn⟩
  · subst x
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy

theorem EvaluateProofInternal.eo_gt_int_args_numeral_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    __eo_gt x y ≠ Term.Stuck ->
      ∃ nx ny : native_Int, x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  intro hNe
  cases x <;> cases y <;> simp only [__eo_gt] at hNe
  case Numeral.Numeral nx ny =>
    exact ⟨nx, ny, rfl, rfl⟩
  case Rational.Rational qx qy =>
    change __smtx_typeof (SmtTerm.Rational qx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy
  case Binary.Binary wx nx wy ny =>
    change __smtx_typeof (SmtTerm.Binary wx nx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 wx)
          (native_zeq nx (native_mod_total nx (native_int_pow2 wx))) <;>
      simp [native_ite, hValid] at hxTy
  all_goals
    contradiction

