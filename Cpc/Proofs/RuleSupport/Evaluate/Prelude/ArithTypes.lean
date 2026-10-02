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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BoolOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.BoolOperands
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithOperands
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.IteOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.IteOperands

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_abs_arg_numeral_of_typeof_int
    (x : Term) :
    __eo_typeof (__eo_ite (__eo_is_neg x) (__eo_neg x) x) =
      Term.UOp UserOp.Int ->
    ∃ nx : native_Int, x = Term.Numeral nx := by
  cases x <;> intro h
  case Numeral nx =>
    exact ⟨nx, rfl⟩
  case Rational q =>
    cases hNeg : native_qlt q (native_mk_rational 0 1)
    · simp [__eo_is_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    · simp [__eo_is_neg, __eo_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
  all_goals
    simp [__eo_is_neg, __eo_ite, native_ite, native_teq] at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_abs_arg_rational_of_typeof_real
    (x : Term) :
    __eo_typeof (__eo_ite (__eo_is_neg x) (__eo_neg x) x) =
      Term.UOp UserOp.Real ->
    ∃ qx : native_Rat, x = Term.Rational qx := by
  cases x <;> intro h
  case Rational qx =>
    exact ⟨qx, rfl⟩
  case Numeral nx =>
    cases hNeg : native_zlt nx 0
    · simp [__eo_is_neg, __eo_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    · simp [__eo_is_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
  all_goals
    simp [__eo_is_neg, __eo_ite, native_ite, native_teq] at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_neg_arg_binary_of_typeof_bitvec
    (x : Term) (w : native_Int) :
    __eo_typeof (__eo_neg x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h
  case Numeral n =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Rational r =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Binary wx nx =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨nx, rfl⟩
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_to_q_typeof_real_of_arg_int
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_q x) = Term.UOp UserOp.Real := by
  cases x <;> simp [__eo_to_q] at hX hNe ⊢
  all_goals
    first
    | rfl
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_to_q_typeof_real_of_arg_real
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_q x) = Term.UOp UserOp.Real := by
  cases x <;> simp [__eo_to_q] at hX hNe ⊢
  all_goals
    first
    | rfl
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_eq_typeof_bool_of_args_real
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real) :
    __eo_typeof (__eo_eq x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_eq] at hX hY ⊢
  all_goals
    first
    | contradiction
    | rfl
    | cases hY
    | cases hX

theorem EvaluateProofInternal.eo_ite_typeof_of_branches_same
    (c t e T : Term)
    (hTNe : T ≠ Term.Stuck)
    (hT : __eo_typeof t = T)
    (hE : __eo_typeof e = T)
    (hNe : __eo_ite c t e ≠ Term.Stuck) :
    __eo_typeof (__eo_ite c t e) = T := by
  cases c <;>
    simp [__eo_ite, native_ite, native_teq] at hNe ⊢
  case Boolean b =>
    cases b <;> simpa [native_ite] using (by
      first
      | exact hT
      | exact hE)
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_zdiv_typeof_int_of_args_int_and_ne_stuck
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_zdiv] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    cases hZero : native_zeq 0 ny <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_zmod_typeof_int_of_args_int_and_ne_stuck
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zmod x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_zmod] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    cases hZero : native_zeq 0 ny <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_qdiv_typeof_real_of_ne_stuck
    (x y : Term)
    (hNe : __eo_qdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_qdiv x y) = Term.UOp UserOp.Real := by
  cases x <;> cases y <;> simp [__eo_qdiv] at hNe ⊢
  case Numeral.Numeral nx ny =>
    cases hZero : native_zeq 0 ny <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  case Rational.Rational qx qy =>
    cases hZero : native_qeq (native_mk_rational 0 1) qy <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_zdiv_left_ne_stuck {a b : Term} :
    __eo_zdiv a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_zdiv] at h

theorem EvaluateProofInternal.eo_zdiv_right_ne_stuck {a b : Term} :
    __eo_zdiv a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_zdiv] at h

theorem EvaluateProofInternal.eo_zmod_left_ne_stuck {a b : Term} :
    __eo_zmod a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_zmod] at h

theorem EvaluateProofInternal.eo_zmod_right_ne_stuck {a b : Term} :
    __eo_zmod a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_zmod] at h

theorem EvaluateProofInternal.eo_qdiv_left_ne_stuck {a b : Term} :
    __eo_qdiv a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_qdiv] at h

theorem EvaluateProofInternal.eo_qdiv_right_ne_stuck {a b : Term} :
    __eo_qdiv a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_qdiv] at h

theorem EvaluateProofInternal.eo_leq_body_typeof_bool_of_int_args
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe :
      (let d := __eo_add x (__eo_neg y)
       __eo_or (__eo_is_neg d)
        (__eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)))) ≠ Term.Stuck) :
    __eo_typeof
        (let d := __eo_add x (__eo_neg y)
         __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1)))) =
      Term.Bool := by
  let d := __eo_add x (__eo_neg y)
  have hOrNe :
      __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) ≠
        Term.Stuck := by
    simpa [d] using hNe
  have hIsNegNe : __eo_is_neg d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_or_left_ne_stuck hOrNe
  have hDNe : d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hIsNegNe
  have hNegYNe : __eo_neg y ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_right_ne_stuck (by simpa [d] using hDNe)
  have hNegY : __eo_typeof (__eo_neg y) = Term.UOp UserOp.Int :=
    EvaluateProofInternal.eo_neg_typeof_int_of_arg_int y hY hNegYNe
  have hD : __eo_typeof d = Term.UOp UserOp.Int := by
    dsimp [d]
    exact EvaluateProofInternal.eo_add_typeof_int_of_args_int x (__eo_neg y) hX hNegY
      (by simpa [d] using hDNe)
  have hIsNeg : __eo_typeof (__eo_is_neg d) = Term.Bool :=
    EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_int d hD hIsNegNe
  have hEqNe :
      __eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_or_right_ne_stuck hOrNe
  have hToQNe : __eo_to_q d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_eq_left_ne_stuck hEqNe
  have hToQ : __eo_typeof (__eo_to_q d) = Term.UOp UserOp.Real :=
    EvaluateProofInternal.eo_to_q_typeof_real_of_arg_int d hD hToQNe
  have hEq :
      __eo_typeof
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) =
        Term.Bool :=
    EvaluateProofInternal.eo_eq_typeof_bool_of_args_real
      (__eo_to_q d) (Term.Rational (native_mk_rational 0 1))
      hToQ rfl
  simpa [d] using
    EvaluateProofInternal.eo_or_typeof_bool_of_args_bool (__eo_is_neg d)
      (__eo_eq (__eo_to_q d)
        (Term.Rational (native_mk_rational 0 1))) hIsNeg hEq hOrNe

theorem EvaluateProofInternal.eo_leq_body_typeof_bool_of_real_args
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real)
    (hNe :
      (let d := __eo_add x (__eo_neg y)
       __eo_or (__eo_is_neg d)
        (__eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)))) ≠ Term.Stuck) :
    __eo_typeof
        (let d := __eo_add x (__eo_neg y)
         __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1)))) =
      Term.Bool := by
  let d := __eo_add x (__eo_neg y)
  have hOrNe :
      __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) ≠
        Term.Stuck := by
    simpa [d] using hNe
  have hIsNegNe : __eo_is_neg d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_or_left_ne_stuck hOrNe
  have hDNe : d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hIsNegNe
  have hNegYNe : __eo_neg y ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_right_ne_stuck (by simpa [d] using hDNe)
  have hNegY : __eo_typeof (__eo_neg y) = Term.UOp UserOp.Real :=
    EvaluateProofInternal.eo_neg_typeof_real_of_arg_real y hY hNegYNe
  have hD : __eo_typeof d = Term.UOp UserOp.Real := by
    dsimp [d]
    exact EvaluateProofInternal.eo_add_typeof_real_of_args_real x (__eo_neg y) hX hNegY
      (by simpa [d] using hDNe)
  have hIsNeg : __eo_typeof (__eo_is_neg d) = Term.Bool :=
    EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_real d hD hIsNegNe
  have hEqNe :
      __eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_or_right_ne_stuck hOrNe
  have hToQNe : __eo_to_q d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_eq_left_ne_stuck hEqNe
  have hToQ : __eo_typeof (__eo_to_q d) = Term.UOp UserOp.Real :=
    EvaluateProofInternal.eo_to_q_typeof_real_of_arg_real d hD hToQNe
  have hEq :
      __eo_typeof
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) =
        Term.Bool :=
    EvaluateProofInternal.eo_eq_typeof_bool_of_args_real
      (__eo_to_q d) (Term.Rational (native_mk_rational 0 1))
      hToQ rfl
  simpa [d] using
    EvaluateProofInternal.eo_or_typeof_bool_of_args_bool (__eo_is_neg d)
      (__eo_eq (__eo_to_q d)
        (Term.Rational (native_mk_rational 0 1))) hIsNeg hEq hOrNe

theorem EvaluateProofInternal.eo_zdiv_typeof_int_of_right_int_and_ne_stuck
    (x y : Term)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
  cases y <;> simp [__eo_zdiv] at hY hNe ⊢
  case Numeral ny =>
    cases x <;> simp [__eo_zdiv] at hNe ⊢
    case Numeral nx =>
      cases hZero : native_zeq 0 ny <;>
        simp [hZero, native_ite] at hNe ⊢
      rfl
    all_goals
      contradiction
  all_goals
    cases hY

theorem EvaluateProofInternal.eo_zmod_typeof_int_of_right_int_and_ne_stuck
    (x y : Term)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zmod x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
  cases y <;> simp [__eo_zmod] at hY hNe ⊢
  case Numeral ny =>
    cases x <;> simp [__eo_zmod] at hNe ⊢
    case Numeral nx =>
      cases hZero : native_zeq 0 ny <;>
        simp [hZero, native_ite] at hNe ⊢
      rfl
    all_goals
      contradiction
  all_goals
    cases hY

theorem EvaluateProofInternal.eo_div_total_body_typeof_int_of_right_int
    (x y : Term)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe :
      __eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y)) =
      Term.UOp UserOp.Int := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_eq y (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv x y) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · have hDivTy :
        __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_zdiv_typeof_int_of_right_int_and_ne_stuck x y hY hSel
    rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hDivTy
  · rw [hCond]
    rfl

theorem EvaluateProofInternal.eo_mod_total_body_typeof_int_of_args_int
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe :
      __eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y)) =
      Term.UOp UserOp.Int := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_eq y (Term.Numeral 0))
      x (__eo_zmod x y) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · have hModTy :
        __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_zmod_typeof_int_of_right_int_and_ne_stuck x y hY hSel
    rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hModTy
  · rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hX

theorem EvaluateProofInternal.eo_qdiv_total_body_typeof_real_of_ne_stuck
    (x y : Term)
    (hNe :
      __eo_ite
          (__eo_eq y (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))
          (__eo_qdiv x y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite
          (__eo_eq y (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))
          (__eo_qdiv x y)) =
      Term.UOp UserOp.Real := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_eq y (Term.Rational (native_mk_rational 0 1)))
      (Term.Rational (native_mk_rational 0 1))
      (__eo_qdiv x y) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · have hQDivTy :
        __eo_typeof (__eo_qdiv x y) = Term.UOp UserOp.Real :=
      EvaluateProofInternal.eo_qdiv_typeof_real_of_ne_stuck x y hSel
    rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hQDivTy
  · rw [hCond]
    rfl

theorem EvaluateProofInternal.eo_mod_total_left_ne_stuck {x y : Term} :
    __eo_ite (__eo_eq y (Term.Numeral 0)) x (__eo_zmod x y) ≠
        Term.Stuck ->
      x ≠ Term.Stuck := by
  intro h hx
  rw [hx] at h
  -- every branch of the guard chain is `Term.Stuck`, so the whole chain is
  -- `Term.Stuck` and contradicts `h`; `simp` no longer collapses it itself
  cases y <;> simp [__eo_eq, __eo_ite, __eo_zmod, native_ite] at h
  -- what simp leaves is a guard chain whose every branch is `Term.Stuck`,
  -- so the chain equals `Term.Stuck` and contradicts `h`
  all_goals
    first
      | exact h rfl
      | exact h (by split <;> (try split) <;> rfl)
      | exact h (by simp [native_teq, native_ite, ite_self])
      | exact h (by simp only [native_teq]; split <;> (try split) <;> rfl)

