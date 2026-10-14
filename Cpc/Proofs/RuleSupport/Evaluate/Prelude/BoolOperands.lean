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

theorem EvaluateProofInternal.has_bool_type_not_of_has_translation
    (b : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.not) b) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) ≠ SmtType.None := by
    have hsimpa := hTrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.not (__eo_to_smt b)) = SmtType.Bool
  rw [typeof_not_eq]
  rw [typeof_not_eq] at hTrans'
  cases hTy : __smtx_typeof (__eo_to_smt b) <;>
    simp [hTy, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_and_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_and_eq]
  rw [typeof_and_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_or_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_or_eq]
  rw [typeof_or_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_xor_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    have hsimpa := hTrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_xor_eq]
  rw [typeof_xor_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_imp_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    have hsimpa := hTrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_imp_eq]
  rw [typeof_imp_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_imp_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

theorem EvaluateProofInternal.has_bool_type_imp_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

theorem EvaluateProofInternal.has_bool_type_xor_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

theorem EvaluateProofInternal.has_bool_type_xor_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

theorem EvaluateProofInternal.has_bool_type_or_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

theorem EvaluateProofInternal.has_bool_type_or_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

theorem EvaluateProofInternal.evaluate_eo_typeof_eq_bool_operands_eq
    (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

theorem EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
    (x y : Term)
    (h : __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact EvaluateProofInternal.evaluate_eo_typeof_eq_bool_operands_eq
    (__eo_typeof x) (__eo_typeof y) h

theorem EvaluateProofInternal.eo_not_arg_boolean_of_typeof_bool
    (t : Term) :
    __eo_typeof (__eo_not t) = Term.Bool ->
    ∃ b : Bool, t = Term.Boolean b := by
  cases t <;> intro h
  case Boolean b =>
    exact ⟨b, rfl⟩
  case Binary w n =>
    change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
      Term.Bool at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_or_typeof_bool_of_args_bool
    (x y : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hY : __eo_typeof y = Term.Bool)
    (hNe : __eo_or x y ≠ Term.Stuck) :
    __eo_typeof (__eo_or x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_or] at hX hY hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_and_typeof_bool_of_args_bool
    (x y : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hY : __eo_typeof y = Term.Bool)
    (hNe : __eo_and x y ≠ Term.Stuck) :
    __eo_typeof (__eo_and x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_and] at hX hY hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_xor_typeof_bool_of_args_bool
    (x y : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hY : __eo_typeof y = Term.Bool)
    (hNe : __eo_xor x y ≠ Term.Stuck) :
    __eo_typeof (__eo_xor x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_xor] at hX hY hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_not_typeof_bool_of_arg_bool
    (x : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hNe : __eo_not x ≠ Term.Stuck) :
    __eo_typeof (__eo_not x) = Term.Bool := by
  cases x <;> simp [__eo_not] at hX hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_not_arg_binary_of_typeof_bitvec
    (t : Term) (w : native_Int) :
    __eo_typeof (__eo_not t) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ n : native_Int, t = Term.Binary w n := by
  cases t <;> intro h
  case Binary wt n =>
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wt) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨n, rfl⟩
  case Boolean b =>
    change Term.Bool =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_and_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_and x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_and_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_and x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
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

theorem EvaluateProofInternal.eo_or_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_or x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_or_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_or x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
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

theorem EvaluateProofInternal.eo_xor_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_xor x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_xor_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_xor x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
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

