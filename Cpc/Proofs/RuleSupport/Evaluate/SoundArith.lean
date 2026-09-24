module

public import Cpc.Proofs.RuleSupport.Evaluate.Typeof
import all Cpc.Proofs.RuleSupport.Evaluate.Typeof

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.run_evaluate_sound_apply_plus_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) := by
  intro hATrans hEvalTy
  have hPlusNN :
      term_has_non_none_type
        (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases arith_binop_args_of_non_none
      (op := SmtTerm.plus) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_plus_eq (__eo_to_smt a) (__eo_to_smt b)) hPlusNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hPlusEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Int
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunAddNe :
        __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunAddNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunAddEoInt :
        __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b)
          (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hPlusEoType
    rcases EvaluateProofInternal.eo_add_args_numeral_of_typeof_int
        (__run_evaluate a) (__run_evaluate b) hRunAddEoInt with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hIntTypeNe hAEoInt hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.plus) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.plus) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_zplus runA runB))
      rw [typeof_plus_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_plus
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_14]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zplus runA runB))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_zplus runA runB)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hPlusEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunAddNe :
        __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunAddNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b))
              (__eo_add (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunAddEoReal :
        __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b)
          (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hPlusEoType
    rcases EvaluateProofInternal.eo_add_args_rational_of_typeof_real
        (__run_evaluate a) (__run_evaluate b) hRunAddEoReal with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Real := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hRealTypeNe hAEoReal hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.plus) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.plus) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qplus runA runB))
      rw [typeof_plus_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_plus
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_14]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qplus runA runB))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_qplus runA runB)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_mult_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) := by
  intro hATrans hEvalTy
  have hMultNN :
      term_has_non_none_type
        (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases arith_binop_args_of_non_none
      (op := SmtTerm.mult) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_mult_eq (__eo_to_smt a) (__eo_to_smt b)) hMultNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hMultEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Int
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunMulNe :
        __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunMulNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunMulEoInt :
        __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b)
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hMultEoType
    rcases EvaluateProofInternal.eo_mul_args_numeral_of_typeof_int
        (__run_evaluate a) (__run_evaluate b) hRunMulEoInt with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hIntTypeNe hAEoInt hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.mult) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.mult) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_zmult runA runB))
      rw [typeof_mult_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_mult
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_16]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zmult runA runB))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_zmult runA runB)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hMultEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunMulNe :
        __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunMulNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b))
              (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunMulEoReal :
        __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b)
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hMultEoType
    rcases EvaluateProofInternal.eo_mul_args_rational_of_typeof_real
        (__run_evaluate a) (__run_evaluate b) hRunMulEoReal with
      ⟨runA, runB, hRunA, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Real := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hRealTypeNe hAEoReal hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.mult) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.mult) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qmult runA runB))
      rw [typeof_mult_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_mult
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_16]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qmult runA runB))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_qmult runA runB)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_neg_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) := by
  intro hATrans hEvalTy
  have hNegNN :
      term_has_non_none_type
        (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases arith_binop_args_of_non_none
      (op := SmtTerm.neg) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_neg_eq (__eo_to_smt a) (__eo_to_smt b)) hNegNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hNegEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Int
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunSubNe :
        __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) ≠
          Term.Stuck := by
      intro hMk
      cases hRun :
          __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunSubNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunSubEoInt :
        __eo_typeof
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) =
          Term.UOp UserOp.Int := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b)
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) hEvalEqTy
      exact hEq.symm.trans hNegEoType
    rcases EvaluateProofInternal.eo_add_args_numeral_of_typeof_int
        (__run_evaluate a) (__eo_neg (__run_evaluate b)) hRunSubEoInt with
      ⟨runA, runNegB, hRunA, hRunNegB⟩
    have hRunNegBEoInt :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      rw [hRunNegB]
      rfl
    rcases EvaluateProofInternal.eo_neg_arg_numeral_of_typeof_int
        (__run_evaluate b) hRunNegBEoInt with
      ⟨runB, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
      rw [hRunB]
      rfl
    have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hIntTypeNe hAEoInt hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Int)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hIntTypeNe hBEoInt hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.neg) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.neg) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Numeral (native_zplus runA (native_zneg runB)))
      rw [typeof_neg_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval__
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_15]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zplus runA (native_zneg runB)))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_zplus runA (native_zneg runB))))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hNegEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_plus (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunSubNe :
        __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) ≠
          Term.Stuck := by
      intro hMk
      cases hRun :
          __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunSubNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b))
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunSubEoReal :
        __eo_typeof
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b))) =
          Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b)
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) hEvalEqTy
      exact hEq.symm.trans hNegEoType
    rcases EvaluateProofInternal.eo_add_args_rational_of_typeof_real
        (__run_evaluate a) (__eo_neg (__run_evaluate b))
        hRunSubEoReal with
      ⟨runA, runNegB, hRunA, hRunNegB⟩
    have hRunNegBEoReal :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      rw [hRunNegB]
      rfl
    rcases EvaluateProofInternal.eo_neg_arg_rational_of_typeof_real
        (__run_evaluate b) hRunNegBEoReal with
      ⟨runB, hRunB⟩
    have hRunAEoType :
        __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Real := by
      rw [hRunA]
      rfl
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
        hRealTypeNe hAEoReal hRunAEoType
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.neg) a b rec hATransA hAProgTy with
      ⟨_hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.neg) a) b rec hBTrans hBProgTy with
      ⟨_hBSameTy, hBRel⟩
    change
      __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_add (__run_evaluate a)
                (__eo_neg (__run_evaluate b)))))
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Rational (native_qplus runA (native_qneg runB)))
      rw [typeof_neg_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval__
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_15]]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qplus runA (native_qneg runB)))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_qplus runA (native_qneg runB))))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_lt_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) := by
  intro hATrans hEvalTy
  have hLtNN :
      term_has_non_none_type
        (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  let runLt :=
    __eo_is_neg (__eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)))
  have hRunLtNe : runLt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b))
            runLt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunAddNe :
      __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck (by simpa [runLt] using hRunLtNe)
  have hRunANe : __run_evaluate a ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunNegBNe :
        __eo_neg (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    exact EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegBNe
  rcases arith_binop_ret_bool_args_of_non_none
      (op := SmtTerm.lt) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_lt_eq (__eo_to_smt a) (__eo_to_smt b)) hLtNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int a hATransA hATyInt hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTyInt hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.lt) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.lt) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Int := by
      rw [← hASameTy]
      exact hATyInt
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int := by
      rw [← hBSameTy]
      exact hBTyInt
    rcases EvaluateProofInternal.eo_lt_int_run_args_of_nonstuck
        (__run_evaluate a) (__run_evaluate b)
        hRunASmtTy hRunBSmtTy (by simpa [runLt] using hRunLtNe) with
      ⟨runA, runB, hRunA, hRunB⟩
    change
      __smtx_typeof (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runLt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runLt))
    dsimp [runLt]
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Boolean
              (native_zlt (native_zplus runA (native_zneg runB)) 0))
      rw [typeof_lt_eq, hATyInt, hBTyInt]
      rw [EvaluateProofInternal.native_zsub_lt_zero_eq_eval]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_lt
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_zlt runA runB))
          (__smtx_model_eval M
            (SmtTerm.Boolean
              (native_zlt (native_zplus runA (native_zneg runB)) 0)))
      rw [EvaluateProofInternal.native_zsub_lt_zero_eq_eval, __smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real a hATransA hATyReal hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real b hBTrans hBTyReal hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.lt) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.lt) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Real := by
      rw [← hASameTy]
      exact hATyReal
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Real := by
      rw [← hBSameTy]
      exact hBTyReal
    rcases EvaluateProofInternal.eo_lt_real_run_args_of_nonstuck
        (__run_evaluate a) (__run_evaluate b)
        hRunASmtTy hRunBSmtTy (by simpa [runLt] using hRunLtNe) with
      ⟨runA, runB, hRunA, hRunB⟩
    change
      __smtx_typeof (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runLt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runLt))
    dsimp [runLt]
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Boolean
              (native_qlt (native_qplus runA (native_qneg runB))
                (native_mk_rational 0 1)))
      rw [typeof_lt_eq, hATyReal, hBTyReal]
      rw [EvaluateProofInternal.native_qsub_lt_zero_eq_eval]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_lt
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_qlt runA runB))
          (__smtx_model_eval M
            (SmtTerm.Boolean
              (native_qlt (native_qplus runA (native_qneg runB))
                (native_mk_rational 0 1))))
      rw [EvaluateProofInternal.native_qsub_lt_zero_eq_eval, __smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_leq_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) := by
  intro hATrans hEvalTy
  have hLeqNN :
      term_has_non_none_type
        (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  let runLeq :=
    let d := __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b))
    __eo_or (__eo_is_neg d)
      (__eo_eq (__eo_to_q d) (Term.Rational (native_mk_rational 0 1)))
  have hRunLeqNe : runLeq ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b))
            runLeq) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunNegNe :
      __eo_is_neg
          (__eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b))) ≠
        Term.Stuck := by
    intro hStuck
    apply hRunLeqNe
    dsimp [runLeq]
    rw [hStuck]
    simp [__eo_or]
  have hRunAddNe :
      __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunNegNe
  have hRunANe : __run_evaluate a ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunNegBNe :
        __eo_neg (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    exact EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegBNe
  rcases arith_binop_ret_bool_args_of_non_none
      (op := SmtTerm.leq) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_leq_eq (__eo_to_smt a) (__eo_to_smt b)) hLeqNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int a hATransA hATyInt hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTyInt hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.leq) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.leq) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Int := by
      rw [← hASameTy]
      exact hATyInt
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int := by
      rw [← hBSameTy]
      exact hBTyInt
    rcases EvaluateProofInternal.eo_lt_int_run_args_of_nonstuck
        (__run_evaluate a) (__run_evaluate b)
        hRunASmtTy hRunBSmtTy hRunNegNe with
      ⟨runA, runB, hRunA, hRunB⟩
    change
      __smtx_typeof (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runLeq) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runLeq))
    dsimp [runLeq]
    rw [hRunA, hRunB, EvaluateProofInternal.eo_leq_int_result_eq]
    constructor
    · change
        __smtx_typeof (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Boolean (native_zleq runA runB))
      rw [typeof_leq_eq, hATyInt, hBTyInt]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_leq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_zleq runA runB))
          (__smtx_model_eval M
            (SmtTerm.Boolean (native_zleq runA runB)))
      rw [__smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real a hATransA hATyReal hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real b hBTrans hBTyReal hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.leq) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.leq) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Real := by
      rw [← hASameTy]
      exact hATyReal
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Real := by
      rw [← hBSameTy]
      exact hBTyReal
    rcases EvaluateProofInternal.eo_lt_real_run_args_of_nonstuck
        (__run_evaluate a) (__run_evaluate b)
        hRunASmtTy hRunBSmtTy hRunNegNe with
      ⟨runA, runB, hRunA, hRunB⟩
    change
      __smtx_typeof (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runLeq) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runLeq))
    dsimp [runLeq]
    rw [hRunA, hRunB, EvaluateProofInternal.eo_leq_real_result_eq]
    constructor
    · change
        __smtx_typeof (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Boolean (native_qleq runA runB))
      rw [typeof_leq_eq, hATyReal, hBTyReal]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_leq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_qleq runA runB))
          (__smtx_model_eval M
            (SmtTerm.Boolean (native_qleq runA runB)))
      rw [__smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_gt_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) := by
  intro hATrans hEvalTy
  have hGtNN :
      term_has_non_none_type
        (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  let runGt :=
    __eo_is_neg (__eo_add (__run_evaluate b) (__eo_neg (__run_evaluate a)))
  have hRunGtNe : runGt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b))
            runGt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunAddNe :
      __eo_add (__run_evaluate b) (__eo_neg (__run_evaluate a)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck (by simpa [runGt] using hRunGtNe)
  have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hRunNegANe :
        __eo_neg (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    exact EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegANe
  rcases arith_binop_ret_bool_args_of_non_none
      (op := SmtTerm.gt) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_gt_eq (__eo_to_smt a) (__eo_to_smt b)) hGtNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int a hATransA hATyInt hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTyInt hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.gt) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.gt) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Int := by
      rw [← hASameTy]
      exact hATyInt
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int := by
      rw [← hBSameTy]
      exact hBTyInt
    rcases EvaluateProofInternal.eo_lt_int_run_args_of_nonstuck
        (__run_evaluate b) (__run_evaluate a)
        hRunBSmtTy hRunASmtTy (by simpa [runGt] using hRunGtNe) with
      ⟨runB, runA, hRunB, hRunA⟩
    change
      __smtx_typeof (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runGt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runGt))
    dsimp [runGt]
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Boolean
              (native_zlt (native_zplus runB (native_zneg runA)) 0))
      rw [typeof_gt_eq, hATyInt, hBTyInt]
      rw [EvaluateProofInternal.native_zsub_lt_zero_eq_eval]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_gt
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_zlt runB runA))
          (__smtx_model_eval M
            (SmtTerm.Boolean
              (native_zlt (native_zplus runB (native_zneg runA)) 0)))
      rw [EvaluateProofInternal.native_zsub_lt_zero_eq_eval, __smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real a hATransA hATyReal hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real b hBTrans hBTyReal hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.gt) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.gt) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Real := by
      rw [← hASameTy]
      exact hATyReal
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Real := by
      rw [← hBSameTy]
      exact hBTyReal
    rcases EvaluateProofInternal.eo_lt_real_run_args_of_nonstuck
        (__run_evaluate b) (__run_evaluate a)
        hRunBSmtTy hRunASmtTy (by simpa [runGt] using hRunGtNe) with
      ⟨runB, runA, hRunB, hRunA⟩
    change
      __smtx_typeof (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runGt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runGt))
    dsimp [runGt]
    rw [hRunA, hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (SmtTerm.Boolean
              (native_qlt (native_qplus runB (native_qneg runA))
                (native_mk_rational 0 1)))
      rw [typeof_gt_eq, hATyReal, hBTyReal]
      rw [EvaluateProofInternal.native_qsub_lt_zero_eq_eval]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_gt
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_qlt runB runA))
          (__smtx_model_eval M
            (SmtTerm.Boolean
              (native_qlt (native_qplus runB (native_qneg runA))
                (native_mk_rational 0 1))))
      rw [EvaluateProofInternal.native_qsub_lt_zero_eq_eval, __smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_geq_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) := by
  intro hATrans hEvalTy
  have hGeqNN :
      term_has_non_none_type
        (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  let runGeq :=
    let d := __eo_add (__run_evaluate b) (__eo_neg (__run_evaluate a))
    __eo_or (__eo_is_neg d)
      (__eo_eq (__eo_to_q d) (Term.Rational (native_mk_rational 0 1)))
  have hRunGeqNe : runGeq ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b))
            runGeq) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunNegNe :
      __eo_is_neg
          (__eo_add (__run_evaluate b) (__eo_neg (__run_evaluate a))) ≠
        Term.Stuck := by
    intro hStuck
    apply hRunGeqNe
    dsimp [runGeq]
    rw [hStuck]
    simp [__eo_or]
  have hRunAddNe :
      __eo_add (__run_evaluate b) (__eo_neg (__run_evaluate a)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunNegNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hRunNegANe :
        __eo_neg (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    exact EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegANe
  rcases arith_binop_ret_bool_args_of_non_none
      (op := SmtTerm.geq) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (typeof_geq_eq (__eo_to_smt a) (__eo_to_smt b)) hGeqNN with
    hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int a hATransA hATyInt hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTyInt hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.geq) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.geq) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Int := by
      rw [← hASameTy]
      exact hATyInt
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int := by
      rw [← hBSameTy]
      exact hBTyInt
    rcases EvaluateProofInternal.eo_lt_int_run_args_of_nonstuck
        (__run_evaluate b) (__run_evaluate a)
        hRunBSmtTy hRunASmtTy hRunNegNe with
      ⟨runB, runA, hRunB, hRunA⟩
    change
      __smtx_typeof (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runGeq) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runGeq))
    dsimp [runGeq]
    rw [hRunA, hRunB, EvaluateProofInternal.eo_leq_int_result_eq]
    constructor
    · change
        __smtx_typeof (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Boolean (native_zleq runB runA))
      rw [typeof_geq_eq, hATyInt, hBTyInt]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_geq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_zleq runB runA))
          (__smtx_model_eval M
            (SmtTerm.Boolean (native_zleq runB runA)))
      rw [__smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real a hATransA hATyReal hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real b hBTrans hBTyReal hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.geq) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.geq) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Real := by
      rw [← hASameTy]
      exact hATyReal
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Real := by
      rw [← hBSameTy]
      exact hBTyReal
    rcases EvaluateProofInternal.eo_lt_real_run_args_of_nonstuck
        (__run_evaluate b) (__run_evaluate a)
        hRunBSmtTy hRunASmtTy hRunNegNe with
      ⟨runB, runA, hRunB, hRunA⟩
    change
      __smtx_typeof (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt runGeq) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M (__eo_to_smt runGeq))
    dsimp [runGeq]
    rw [hRunA, hRunB, EvaluateProofInternal.eo_leq_real_result_eq]
    constructor
    · change
        __smtx_typeof (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Boolean (native_qleq runB runA))
      rw [typeof_geq_eq, hATyReal, hBTyReal]
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_geq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Boolean (native_qleq runB runA))
          (__smtx_model_eval M
            (SmtTerm.Boolean (native_qleq runB runA)))
      rw [__smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_div_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) := by
  intro hATrans hEvalTy
  have hDivNN :
      term_has_non_none_type
        (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases int_binop_args_of_non_none
      (op := SmtTerm.div) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_div_eq (__eo_to_smt a) (__eo_to_smt b)) hDivNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hDivEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  have hRunDivNe :
      __eo_zdiv (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
            (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
          (__eo_zdiv (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_zdiv (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunDivNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
            (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
            (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunDivEoInt :
      __eo_typeof (__eo_zdiv (__run_evaluate a) (__run_evaluate b)) =
        Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)
        (__eo_zdiv (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hDivEoType
  rcases EvaluateProofInternal.eo_zdiv_args_numeral_of_typeof_int
      (__run_evaluate a) (__run_evaluate b) hRunDivEoInt with
    ⟨runA, runB, hRunA, hRunB, hNZ⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    rw [hRunB]
    rfl
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
    rw [hRunA]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hIntTypeNe hAEoInt hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.div) a b rec hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.div) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hRunBNe : runB ≠ 0 := by
    intro hZero
    subst runB
    simp [native_zeq] at hNZ
  change
    __smtx_typeof (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_zdiv (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_zdiv (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · rw [show
        __eo_to_smt
            (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_div_total runA runB) by
      simp [__eo_zdiv, hNZ, native_ite]
      rfl]
    change
      __smtx_typeof (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Numeral (native_div_total runA runB))
    rw [typeof_div_eq, hATyInt, hBTyInt]
    rw [__smtx_typeof.eq_2]
    simp [native_ite, native_Teq]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Numeral runA) := by
      rw [hRunA] at hARel
      rw [show __eo_to_smt (Term.Numeral runA) =
          SmtTerm.Numeral runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_2] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Numeral runB) =
          SmtTerm.Numeral runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_2] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Numeral runA :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Numeral runB :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    have hDivByZeroFalse :
        __smtx_model_eval_eq
            (SmtValue.Numeral runB) (SmtValue.Numeral 0) =
          SmtValue.Boolean false := by
      have hValNe :
          SmtValue.Numeral runB ≠ SmtValue.Numeral 0 := by
        intro h
        cases h
        exact hRunBNe rfl
      simp [__smtx_model_eval_eq, native_veq, hValNe]
    rw [show
        __smtx_model_eval M
            (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_ite
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral 0))
            (__smtx_model_eval_apply M
              (native_model_lookup M native_div_by_zero_id
                (SmtType.FunType SmtType.Int SmtType.Int))
              (__smtx_model_eval M (__eo_to_smt a)))
            (__smtx_model_eval_div_total
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b))) by
      rw [__smtx_model_eval.eq_26]]
    rw [hAEval, hBEval, hDivByZeroFalse]
    rw [show
        __eo_to_smt
            (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_div_total runA runB) by
      simp [__eo_zdiv, hNZ, native_ite]
      rfl]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Numeral (native_div_total runA runB))
        (__smtx_model_eval M
          (SmtTerm.Numeral (native_div_total runA runB)))
    rw [__smtx_model_eval.eq_2]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_mod_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) := by
  intro hATrans hEvalTy
  have hModNN :
      term_has_non_none_type
        (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases int_binop_args_of_non_none
      (op := SmtTerm.mod) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt a) (__eo_to_smt b)) hModNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hModEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  have hRunModNe :
      __eo_zmod (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
            (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
          (__eo_zmod (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_zmod (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunModNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
            (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
            (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunModEoInt :
      __eo_typeof (__eo_zmod (__run_evaluate a) (__run_evaluate b)) =
        Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)
        (__eo_zmod (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hModEoType
  rcases EvaluateProofInternal.eo_zmod_args_numeral_of_typeof_int
      (__run_evaluate a) (__run_evaluate b) hRunModEoInt with
    ⟨runA, runB, hRunA, hRunB, hNZ⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    rw [hRunB]
    rfl
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
    rw [hRunA]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hIntTypeNe hAEoInt hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.mod) a b rec hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.mod) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hRunBNe : runB ≠ 0 := by
    intro hZero
    subst runB
    simp [native_zeq] at hNZ
  change
    __smtx_typeof (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_zmod (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_zmod (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · rw [show
        __eo_to_smt
            (__eo_zmod (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_mod_total runA runB) by
      simp [__eo_zmod, hNZ, native_ite]
      rfl]
    change
      __smtx_typeof (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Numeral (native_mod_total runA runB))
    rw [typeof_mod_eq, hATyInt, hBTyInt]
    rw [__smtx_typeof.eq_2]
    simp [native_ite, native_Teq]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Numeral runA) := by
      rw [hRunA] at hARel
      rw [show __eo_to_smt (Term.Numeral runA) =
          SmtTerm.Numeral runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_2] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Numeral runB) =
          SmtTerm.Numeral runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_2] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Numeral runA :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Numeral runB :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    have hModByZeroFalse :
        __smtx_model_eval_eq
            (SmtValue.Numeral runB) (SmtValue.Numeral 0) =
          SmtValue.Boolean false := by
      have hValNe :
          SmtValue.Numeral runB ≠ SmtValue.Numeral 0 := by
        intro h
        cases h
        exact hRunBNe rfl
      simp [__smtx_model_eval_eq, native_veq, hValNe]
    rw [show
        __smtx_model_eval M
            (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_ite
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral 0))
            (__smtx_model_eval_apply M
              (native_model_lookup M native_mod_by_zero_id
                (SmtType.FunType SmtType.Int SmtType.Int))
              (__smtx_model_eval M (__eo_to_smt a)))
            (__smtx_model_eval_mod_total
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b))) by
      rw [__smtx_model_eval.eq_27]]
    rw [hAEval, hBEval, hModByZeroFalse]
    rw [show
        __eo_to_smt
            (__eo_zmod (Term.Numeral runA) (Term.Numeral runB)) =
          SmtTerm.Numeral (native_mod_total runA runB) by
      simp [__eo_zmod, hNZ, native_ite]
      rfl]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Numeral (native_mod_total runA runB))
        (__smtx_model_eval M
          (SmtTerm.Numeral (native_mod_total runA runB)))
    rw [__smtx_model_eval.eq_2]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_qdiv_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) a) b) := by
  intro hATrans hEvalTy
  have hQDivNN :
      term_has_non_none_type
        (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  let runQDiv :=
    __eo_qdiv (__eo_to_q (__run_evaluate a))
      (__eo_to_q (__run_evaluate b))
  have hRunQDivNe : runQDiv ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) a) b))
            runQDiv) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  rcases EvaluateProofInternal.eo_qdiv_to_q_args_shape_of_nonstuck
      (__run_evaluate a) (__run_evaluate b)
      (by simpa [runQDiv] using hRunQDivNe) with
    ⟨qNum, qDen, hRunAToQ, hRunBToQ, hNZ⟩
  have hRunAToQNe : __eo_to_q (__run_evaluate a) ≠ Term.Stuck := by
    rw [hRunAToQ]
    intro h
    cases h
  have hRunBToQNe : __eo_to_q (__run_evaluate b) ≠ Term.Stuck := by
    rw [hRunBToQ]
    intro h
    cases h
  have hRunANe : __run_evaluate a ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunAToQNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunBToQNe
  rcases arith_binop_ret_args_of_non_none
      (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt a) (__eo_to_smt b))
      hQDivNN with hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int a hATransA hATyInt hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTyInt hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.qdiv) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.qdiv) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Int := by
      rw [← hASameTy]
      exact hATyInt
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int := by
      rw [← hBSameTy]
      exact hBTyInt
    rcases EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
        (__run_evaluate a) hRunASmtTy hRunAToQNe with
      ⟨runA, hRunA⟩
    rcases EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
        (__run_evaluate b) hRunBSmtTy hRunBToQNe with
      ⟨runB, hRunB⟩
    have hNumEq : native_to_real runA = qNum := by
      rw [hRunA] at hRunAToQ
      simpa [__eo_to_q] using hRunAToQ
    have hDenEq : native_to_real runB = qDen := by
      rw [hRunB] at hRunBToQ
      simpa [__eo_to_q] using hRunBToQ
    subst qNum
    subst qDen
    have hZeroNe :
        native_mk_rational 0 1 ≠ native_to_real runB :=
      EvaluateProofInternal.native_qeq_false_ne hNZ
    have hRunBZeroNe :
        native_to_real runB ≠ native_mk_rational 0 1 := by
      intro h
      exact hZeroNe h.symm
    have hTermNe :
        Term.Rational (native_mk_rational 0 1) ≠
          Term.Rational (native_to_real runB) := by
      intro hTerm
      injection hTerm with hRat
      exact hZeroNe hRat
    change
      __smtx_typeof (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_qdiv (__eo_to_q (__run_evaluate a))
                (__eo_to_q (__run_evaluate b)))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_qdiv (__eo_to_q (__run_evaluate a))
                (__eo_to_q (__run_evaluate b)))))
    rw [hRunA, hRunB]
    constructor
    · rw [show
          __eo_to_smt
              (__eo_qdiv (__eo_to_q (Term.Numeral runA))
                (__eo_to_q (Term.Numeral runB))) =
            SmtTerm.Rational (native_mk_rational runA runB) by
        simp [__eo_to_q, __eo_qdiv, native_ite, hNZ,
          EvaluateProofInternal.native_to_real_qdiv_total_eval]
        rfl]
      change
        __smtx_typeof (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_mk_rational runA runB))
      rw [typeof_qdiv_eq, hATyInt, hBTyInt]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2_ret]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Numeral runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Numeral runA) =
            SmtTerm.Numeral runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_2] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Numeral runB) =
            SmtTerm.Numeral runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_2] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Numeral runA :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runB :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) =
            let _v0 := __smtx_to_real_coerce
              (__smtx_model_eval M (__eo_to_smt b))
            let _v1 := __smtx_to_real_coerce
              (__smtx_model_eval M (__eo_to_smt a))
            __smtx_model_eval_ite
              (__smtx_model_eval_eq _v0
                (SmtValue.Rational (native_mk_rational 0 1)))
              (__smtx_model_eval_apply M
                (native_model_lookup M native_qdiv_by_zero_id
                  (SmtType.FunType SmtType.Real SmtType.Real)) _v1)
              (__smtx_model_eval_qdiv_total _v1 _v0) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      rw [show
          __eo_to_smt
              (__eo_qdiv (__eo_to_q (Term.Numeral runA))
                (__eo_to_q (Term.Numeral runB))) =
            SmtTerm.Rational (native_mk_rational runA runB) by
        simp [__eo_to_q, __eo_qdiv, native_ite, hNZ,
          EvaluateProofInternal.native_to_real_qdiv_total_eval]
        rfl]
      rw [__smtx_model_eval.eq_3]
      simp [__smtx_to_real_coerce, __smtx_model_eval_eq,
        __smtx_model_eval_ite, __smtx_model_eval_qdiv_total, native_veq,
        hRunBZeroNe, EvaluateProofInternal.native_to_real_qdiv_total_eval]
      exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real a hATransA hATyReal hRunANe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real b hBTrans hBTyReal hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
        (Term.UOp UserOp.qdiv) a b rec hATransA hAProgTy with
      ⟨hASameTy, hARel⟩
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.qdiv) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunASmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Real := by
      rw [← hASameTy]
      exact hATyReal
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Real := by
      rw [← hBSameTy]
      exact hBTyReal
    rcases EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
        (__run_evaluate a) hRunASmtTy hRunAToQNe with
      ⟨runA, hRunA⟩
    rcases EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
        (__run_evaluate b) hRunBSmtTy hRunBToQNe with
      ⟨runB, hRunB⟩
    have hNumEq : runA = qNum := by
      rw [hRunA] at hRunAToQ
      simpa [__eo_to_q] using hRunAToQ
    have hDenEq : runB = qDen := by
      rw [hRunB] at hRunBToQ
      simpa [__eo_to_q] using hRunBToQ
    subst qNum
    subst qDen
    have hZeroNe :
        native_mk_rational 0 1 ≠ runB :=
      EvaluateProofInternal.native_qeq_false_ne hNZ
    have hRunBZeroNe :
        runB ≠ native_mk_rational 0 1 := by
      intro h
      exact hZeroNe h.symm
    have hTermNe :
        Term.Rational (native_mk_rational 0 1) ≠
          Term.Rational runB := by
      intro hTerm
      injection hTerm with hRat
      exact hZeroNe hRat
    change
      __smtx_typeof (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_qdiv (__eo_to_q (__run_evaluate a))
                (__eo_to_q (__run_evaluate b)))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_qdiv (__eo_to_q (__run_evaluate a))
                (__eo_to_q (__run_evaluate b)))))
    rw [hRunA, hRunB]
    constructor
    · rw [show
          __eo_to_smt
              (__eo_qdiv (__eo_to_q (Term.Rational runA))
                (__eo_to_q (Term.Rational runB))) =
            SmtTerm.Rational (native_qdiv_total runA runB) by
        simp [__eo_to_q, __eo_qdiv, native_ite, hNZ]
        rfl]
      change
        __smtx_typeof (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qdiv_total runA runB))
      rw [typeof_qdiv_eq, hATyReal, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_2_ret]
    · have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Rational runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Rational runA) =
            SmtTerm.Rational runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_3] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Rational runB) =
            SmtTerm.Rational runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_3] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Rational runA :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runB :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b)) =
            let _v0 := __smtx_to_real_coerce
              (__smtx_model_eval M (__eo_to_smt b))
            let _v1 := __smtx_to_real_coerce
              (__smtx_model_eval M (__eo_to_smt a))
            __smtx_model_eval_ite
              (__smtx_model_eval_eq _v0
                (SmtValue.Rational (native_mk_rational 0 1)))
              (__smtx_model_eval_apply M
                (native_model_lookup M native_qdiv_by_zero_id
                  (SmtType.FunType SmtType.Real SmtType.Real)) _v1)
              (__smtx_model_eval_qdiv_total _v1 _v0) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hAEval, hBEval]
      rw [show
          __eo_to_smt
              (__eo_qdiv (__eo_to_q (Term.Rational runA))
                (__eo_to_q (Term.Rational runB))) =
            SmtTerm.Rational (native_qdiv_total runA runB) by
        simp [__eo_to_q, __eo_qdiv, native_ite, hNZ]
        rfl]
      rw [__smtx_model_eval.eq_3]
      simp [__smtx_to_real_coerce, __smtx_model_eval_eq,
        __smtx_model_eval_ite, __smtx_model_eval_qdiv_total, native_veq,
        hRunBZeroNe]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_qdiv_total_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) := by
  intro hATrans hEvalTy
  have hQDivTotalNN :
      term_has_non_none_type
        (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  let runBToQ := __eo_to_q (__run_evaluate b)
  let runQDivTotal :=
    __eo_ite (__eo_eq runBToQ (Term.Rational (native_mk_rational 0 1)))
      (Term.Rational (native_mk_rational 0 1))
      (__eo_qdiv (__eo_to_q (__run_evaluate a)) runBToQ)
  have hRunQDivTotalNe : runQDivTotal ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b))
            runQDivTotal) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b))
          runQDivTotal ≠ Term.Stuck := by
    intro hMk
    cases hRun : runQDivTotal <;>
      simp [__eo_mk_apply, hRun] at hMk hRunQDivTotalNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b))
            runQDivTotal) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b))
            runQDivTotal) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  rcases arith_binop_ret_args_of_non_none
      (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt a) (__eo_to_smt b))
      hQDivTotalNN with hArgsInt | hArgsReal
  · rcases hArgsInt with ⟨hATyInt, hBTyInt⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyInt]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hQDivTotalEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_qdiv (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoInt, hBEoInt]
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunQDivTotalEoReal :
        __eo_typeof runQDivTotal = Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b)
          runQDivTotal hEvalEqTy
      exact hEq.symm.trans hQDivTotalEoType
    rcases EvaluateProofInternal.eo_qdiv_total_to_q_args_shape_of_typeof_real
        (__run_evaluate a) (__run_evaluate b)
        (by simpa [runQDivTotal, runBToQ] using hRunQDivTotalNe)
        (by simpa [runQDivTotal, runBToQ] using hRunQDivTotalEoReal) with
      ⟨qDen, hRunBToQ, hRunBShape⟩
    have hRunBToQNe : __eo_to_q (__run_evaluate b) ≠ Term.Stuck := by
      rw [hRunBToQ]
      intro h
      cases h
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunBToQNe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTyInt hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.qdiv_total) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int := by
      rw [← hBSameTy]
      exact hBTyInt
    rcases EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
        (__run_evaluate b) hRunBSmtTy hRunBToQNe with
      ⟨runB, hRunB⟩
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Numeral runB) =
          SmtTerm.Numeral runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_2] at hBRel
      exact hBRel
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Numeral runB :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    change
      __smtx_typeof
          (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_ite
                (__eo_eq (__eo_to_q (__run_evaluate b))
                  (Term.Rational (native_mk_rational 0 1)))
                (Term.Rational (native_mk_rational 0 1))
                (__eo_qdiv (__eo_to_q (__run_evaluate a))
                  (__eo_to_q (__run_evaluate b))))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite
                (__eo_eq (__eo_to_q (__run_evaluate b))
                  (Term.Rational (native_mk_rational 0 1)))
                (Term.Rational (native_mk_rational 0 1))
                (__eo_qdiv (__eo_to_q (__run_evaluate a))
                  (__eo_to_q (__run_evaluate b))))))
    rw [hRunB]
    cases hRunBShape with
    | inl hDenZero =>
        have hRunBZero : runB = 0 := by
          rw [hRunB, hDenZero] at hRunBToQ
          have hToReal :
              native_to_real runB = native_mk_rational 0 1 := by
            simpa [__eo_to_q] using hRunBToQ
          exact EvaluateProofInternal.native_to_real_zero_eq hToReal
        subst runB
        constructor
        · rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q (Term.Numeral 0))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (__run_evaluate a))
                      (__eo_to_q (Term.Numeral 0)))) =
                SmtTerm.Rational (native_mk_rational 0 1) by
            simp [__eo_to_q, __eo_eq, __eo_ite, native_teq, native_ite,
              native_to_real, native_mk_rational, rat_zero_div_one]
            rfl]
          change
            __smtx_typeof
                (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1))
          rw [typeof_qdiv_total_eq, hATyInt, hBTyInt]
          rw [__smtx_typeof.eq_3]
          simp [__smtx_typeof_arith_overload_op_2_ret]
        · have hAEvalValueTy :
              __smtx_typeof_value
                  (__smtx_model_eval M (__eo_to_smt a)) =
                SmtType.Int := by
            simpa [hATyInt] using
              smt_model_eval_preserves_type_of_non_none M hM
                (__eo_to_smt a) (by
                  unfold term_has_non_none_type
                  rw [hATyInt]
                  simp)
          rcases int_value_canonical hAEvalValueTy with
            ⟨evalA, hAEval⟩
          rw [show
              __smtx_model_eval M
                  (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_model_eval_qdiv_total
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) by
            rw [__smtx_model_eval.eq_def] <;> simp only]
          rw [hAEval, hBEval]
          rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q (Term.Numeral 0))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (__run_evaluate a))
                      (__eo_to_q (Term.Numeral 0)))) =
                SmtTerm.Rational (native_mk_rational 0 1) by
            simp [__eo_to_q, __eo_eq, __eo_ite, native_teq, native_ite,
              native_to_real, native_mk_rational, rat_zero_div_one]
            rfl]
          change
            RuleProofs.smt_value_rel
              (SmtValue.Rational (native_mk_rational evalA 0))
              (__smtx_model_eval M
                (SmtTerm.Rational (native_mk_rational 0 1)))
          rw [EvaluateProofInternal.native_mk_rational_zero_den, __smtx_model_eval.eq_3]
          exact RuleProofs.smt_value_rel_refl _
    | inr hDenNonzero =>
        rcases hDenNonzero with ⟨qNum, hRunAToQ, hNZ⟩
        have hDenEq : native_to_real runB = qDen := by
          rw [hRunB] at hRunBToQ
          simpa [__eo_to_q] using hRunBToQ
        subst qDen
        have hRunAToQNe : __eo_to_q (__run_evaluate a) ≠ Term.Stuck := by
          rw [hRunAToQ]
          intro h
          cases h
        have hRunANe : __run_evaluate a ≠ Term.Stuck :=
          EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunAToQNe
        have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
          EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int a hATransA hATyInt hRunANe
        rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
            (Term.UOp UserOp.qdiv_total) a b rec hATransA hAProgTy with
          ⟨hASameTy, hARel⟩
        have hRunASmtTy :
            __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Int := by
          rw [← hASameTy]
          exact hATyInt
        rcases EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
            (__run_evaluate a) hRunASmtTy hRunAToQNe with
          ⟨runA, hRunA⟩
        have hNumEq : native_to_real runA = qNum := by
          rw [hRunA] at hRunAToQ
          simpa [__eo_to_q] using hRunAToQ
        subst qNum
        have hZeroNe :
            native_mk_rational 0 1 ≠ native_to_real runB :=
          EvaluateProofInternal.native_qeq_false_ne hNZ
        have hTermNe :
            Term.Rational (native_mk_rational 0 1) ≠
              Term.Rational (native_to_real runB) := by
          intro hTerm
          injection hTerm with hRat
          exact hZeroNe hRat
        rw [hRunA]
        constructor
        · rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q (Term.Numeral runB))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (Term.Numeral runA))
                      (__eo_to_q (Term.Numeral runB)))) =
                SmtTerm.Rational (native_mk_rational runA runB) by
            simp [__eo_to_q, __eo_eq, __eo_ite, __eo_qdiv, native_ite,
              native_teq, hTermNe, hNZ, EvaluateProofInternal.native_to_real_qdiv_total_eval]
            rfl]
          change
            __smtx_typeof
                (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof (SmtTerm.Rational (native_mk_rational runA runB))
          rw [typeof_qdiv_total_eq, hATyInt, hBTyInt]
          rw [__smtx_typeof.eq_3]
          simp [__smtx_typeof_arith_overload_op_2_ret]
        · have hARelValue :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (SmtValue.Numeral runA) := by
            rw [hRunA] at hARel
            rw [show __eo_to_smt (Term.Numeral runA) =
                SmtTerm.Numeral runA by
              rfl] at hARel
            rw [__smtx_model_eval.eq_2] at hARel
            exact hARel
          have hAEval :
              __smtx_model_eval M (__eo_to_smt a) =
                SmtValue.Numeral runA :=
            EvaluateProofInternal.smt_value_rel_numeral_eq
              (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
          rw [show
              __smtx_model_eval M
                  (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_model_eval_qdiv_total
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) by
            rw [__smtx_model_eval.eq_def] <;> simp only]
          rw [hAEval, hBEval]
          rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q (Term.Numeral runB))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (Term.Numeral runA))
                      (__eo_to_q (Term.Numeral runB)))) =
                SmtTerm.Rational (native_mk_rational runA runB) by
            simp [__eo_to_q, __eo_eq, __eo_ite, __eo_qdiv, native_ite,
              native_teq, hTermNe, hNZ, EvaluateProofInternal.native_to_real_qdiv_total_eval]
            rfl]
          change
            RuleProofs.smt_value_rel
              (SmtValue.Rational (native_mk_rational runA runB))
              (__smtx_model_eval M
                (SmtTerm.Rational (native_mk_rational runA runB)))
          rw [__smtx_model_eval.eq_3]
          exact RuleProofs.smt_value_rel_refl _
  · rcases hArgsReal with ⟨hATyReal, hBTyReal⟩
    have hATransA : RuleProofs.eo_has_smt_translation a := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hATyReal]
      simp
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hAMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hAEoReal : __eo_typeof a = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hAMatch.symm.trans hATyReal)
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hQDivTotalEoType :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_qdiv (__eo_typeof a) (__eo_typeof b) =
        Term.UOp UserOp.Real
      rw [hAEoReal, hBEoReal]
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
    have hRunQDivTotalEoReal :
        __eo_typeof runQDivTotal = Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b)
          runQDivTotal hEvalEqTy
      exact hEq.symm.trans hQDivTotalEoType
    rcases EvaluateProofInternal.eo_qdiv_total_to_q_args_shape_of_typeof_real
        (__run_evaluate a) (__run_evaluate b)
        (by simpa [runQDivTotal, runBToQ] using hRunQDivTotalNe)
        (by simpa [runQDivTotal, runBToQ] using hRunQDivTotalEoReal) with
      ⟨qDen, hRunBToQ, hRunBShape⟩
    have hRunBToQNe : __eo_to_q (__run_evaluate b) ≠ Term.Stuck := by
      rw [hRunBToQ]
      intro h
      cases h
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunBToQNe
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real b hBTrans hBTyReal hRunBNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.Apply (Term.UOp UserOp.qdiv_total) a) b rec hBTrans hBProgTy with
      ⟨hBSameTy, hBRel⟩
    have hRunBSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Real := by
      rw [← hBSameTy]
      exact hBTyReal
    rcases EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
        (__run_evaluate b) hRunBSmtTy hRunBToQNe with
      ⟨runB, hRunB⟩
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Rational runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Rational runB) =
          SmtTerm.Rational runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_3] at hBRel
      exact hBRel
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Rational runB :=
      EvaluateProofInternal.smt_value_rel_rational_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    change
      __smtx_typeof
          (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_ite
                (__eo_eq (__eo_to_q (__run_evaluate b))
                  (Term.Rational (native_mk_rational 0 1)))
                (Term.Rational (native_mk_rational 0 1))
                (__eo_qdiv (__eo_to_q (__run_evaluate a))
                  (__eo_to_q (__run_evaluate b))))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite
                (__eo_eq (__eo_to_q (__run_evaluate b))
                  (Term.Rational (native_mk_rational 0 1)))
                (Term.Rational (native_mk_rational 0 1))
                (__eo_qdiv (__eo_to_q (__run_evaluate a))
                  (__eo_to_q (__run_evaluate b))))))
    rw [hRunB]
    cases hRunBShape with
    | inl hDenZero =>
        have hRunBZero : runB = native_mk_rational 0 1 := by
          rw [hRunB] at hRunBToQ
          simpa [__eo_to_q] using hRunBToQ.trans
            (congrArg Term.Rational hDenZero)
        subst runB
        constructor
        · rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q
                        (Term.Rational (native_mk_rational 0 1)))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (__run_evaluate a))
                      (__eo_to_q
                        (Term.Rational (native_mk_rational 0 1))))) =
                SmtTerm.Rational (native_mk_rational 0 1) by
            simp [__eo_to_q, __eo_eq, __eo_ite, native_teq, native_ite]
            rfl]
          change
            __smtx_typeof
                (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1))
          rw [typeof_qdiv_total_eq, hATyReal, hBTyReal]
          rw [__smtx_typeof.eq_3]
          simp [__smtx_typeof_arith_overload_op_2_ret]
        · have hAEvalValueTy :
              __smtx_typeof_value
                  (__smtx_model_eval M (__eo_to_smt a)) =
                SmtType.Real := by
            simpa [hATyReal] using
              smt_model_eval_preserves_type_of_non_none M hM
                (__eo_to_smt a) (by
                  unfold term_has_non_none_type
                  rw [hATyReal]
                  simp)
          rcases real_value_canonical hAEvalValueTy with
            ⟨evalA, hAEval⟩
          rw [show
              __smtx_model_eval M
                  (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_model_eval_qdiv_total
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) by
            rw [__smtx_model_eval.eq_def] <;> simp only]
          rw [hAEval, hBEval]
          rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q
                        (Term.Rational (native_mk_rational 0 1)))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (__run_evaluate a))
                      (__eo_to_q
                        (Term.Rational (native_mk_rational 0 1))))) =
                SmtTerm.Rational (native_mk_rational 0 1) by
            simp [__eo_to_q, __eo_eq, __eo_ite, native_teq, native_ite]
            rfl]
          change
            RuleProofs.smt_value_rel
              (SmtValue.Rational
                (native_qdiv_total evalA (native_mk_rational 0 1)))
              (__smtx_model_eval M
                (SmtTerm.Rational (native_mk_rational 0 1)))
          rw [EvaluateProofInternal.native_qdiv_total_zero, __smtx_model_eval.eq_3]
          exact RuleProofs.smt_value_rel_refl _
    | inr hDenNonzero =>
        rcases hDenNonzero with ⟨qNum, hRunAToQ, hNZ⟩
        have hDenEq : runB = qDen := by
          rw [hRunB] at hRunBToQ
          simpa [__eo_to_q] using hRunBToQ
        subst qDen
        have hRunAToQNe : __eo_to_q (__run_evaluate a) ≠ Term.Stuck := by
          rw [hRunAToQ]
          intro h
          cases h
        have hRunANe : __run_evaluate a ≠ Term.Stuck :=
          EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunAToQNe
        have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
          EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real a hATransA hATyReal hRunANe
        rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
            (Term.UOp UserOp.qdiv_total) a b rec hATransA hAProgTy with
          ⟨hASameTy, hARel⟩
        have hRunASmtTy :
            __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.Real := by
          rw [← hASameTy]
          exact hATyReal
        rcases EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
            (__run_evaluate a) hRunASmtTy hRunAToQNe with
          ⟨runA, hRunA⟩
        have hNumEq : runA = qNum := by
          rw [hRunA] at hRunAToQ
          simpa [__eo_to_q] using hRunAToQ
        subst qNum
        have hZeroNe :
            native_mk_rational 0 1 ≠ runB :=
          EvaluateProofInternal.native_qeq_false_ne hNZ
        have hTermNe :
            Term.Rational (native_mk_rational 0 1) ≠
              Term.Rational runB := by
          intro hTerm
          injection hTerm with hRat
          exact hZeroNe hRat
        rw [hRunA]
        constructor
        · rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q (Term.Rational runB))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (Term.Rational runA))
                      (__eo_to_q (Term.Rational runB)))) =
                SmtTerm.Rational (native_qdiv_total runA runB) by
            simp [__eo_to_q, __eo_eq, __eo_ite, __eo_qdiv, native_ite,
              native_teq, hTermNe, hNZ]
            rfl]
          change
            __smtx_typeof
                (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof (SmtTerm.Rational (native_qdiv_total runA runB))
          rw [typeof_qdiv_total_eq, hATyReal, hBTyReal]
          rw [__smtx_typeof.eq_3]
          simp [__smtx_typeof_arith_overload_op_2_ret]
        · have hARelValue :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (SmtValue.Rational runA) := by
            rw [hRunA] at hARel
            rw [show __eo_to_smt (Term.Rational runA) =
                SmtTerm.Rational runA by
              rfl] at hARel
            rw [__smtx_model_eval.eq_3] at hARel
            exact hARel
          have hAEval :
              __smtx_model_eval M (__eo_to_smt a) =
                SmtValue.Rational runA :=
            EvaluateProofInternal.smt_value_rel_rational_eq
              (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
          rw [show
              __smtx_model_eval M
                  (SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_model_eval_qdiv_total
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) by
            rw [__smtx_model_eval.eq_def] <;> simp only]
          rw [hAEval, hBEval]
          rw [show
              __eo_to_smt
                  (__eo_ite
                    (__eo_eq (__eo_to_q (Term.Rational runB))
                      (Term.Rational (native_mk_rational 0 1)))
                    (Term.Rational (native_mk_rational 0 1))
                    (__eo_qdiv (__eo_to_q (Term.Rational runA))
                      (__eo_to_q (Term.Rational runB)))) =
                SmtTerm.Rational (native_qdiv_total runA runB) by
            simp [__eo_to_q, __eo_eq, __eo_ite, __eo_qdiv, native_ite,
              native_teq, hTermNe, hNZ]
            rfl]
          change
            RuleProofs.smt_value_rel
              (SmtValue.Rational (native_qdiv_total runA runB))
              (__smtx_model_eval M
                (SmtTerm.Rational (native_qdiv_total runA runB)))
          rw [__smtx_model_eval.eq_3]
          exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_div_total_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) := by
  intro hATrans hEvalTy
  have hDivTotalNN :
      term_has_non_none_type
        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases int_binop_args_of_non_none
      (op := SmtTerm.div_total)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_div_total_eq (__eo_to_smt a) (__eo_to_smt b))
      hDivTotalNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hDivTotalEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  let runBTerm := __run_evaluate b
  let runDivTotal :=
    __eo_ite (__eo_eq runBTerm (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv (__run_evaluate a) runBTerm)
  have hRunDivTotalNe : runDivTotal ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
            runDivTotal) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
          runDivTotal ≠ Term.Stuck := by
    intro hMk
    cases hRun : runDivTotal <;>
      simp [__eo_mk_apply, hRun] at hMk hRunDivTotalNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
            runDivTotal) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
            runDivTotal) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunDivTotalEoInt :
      __eo_typeof runDivTotal = Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)
        runDivTotal hEvalEqTy
    exact hEq.symm.trans hDivTotalEoType
  rcases EvaluateProofInternal.eo_div_total_args_shape_of_typeof_int
      (__run_evaluate a) runBTerm hRunDivTotalNe hRunDivTotalEoInt with
    ⟨runB, hRunB, hRunBShape⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    change __eo_typeof runBTerm = Term.UOp UserOp.Int
    rw [hRunB]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.div_total) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hBRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Numeral runB) := by
    change __run_evaluate b = Term.Numeral runB at hRunB
    rw [hRunB] at hBRel
    rw [show __eo_to_smt (Term.Numeral runB) =
        SmtTerm.Numeral runB by
      rfl] at hBRel
    rw [__smtx_model_eval.eq_2] at hBRel
    exact hBRel
  have hBEval :
      __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Numeral runB :=
    EvaluateProofInternal.smt_value_rel_numeral_eq
      (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
  change
    __smtx_typeof
        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (Term.Numeral 0)
              (__eo_zdiv (__run_evaluate a) (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (Term.Numeral 0)
              (__eo_zdiv (__run_evaluate a) (__run_evaluate b)))))
  change __run_evaluate b = Term.Numeral runB at hRunB
  rw [hRunB]
  cases hRunBShape with
  | inl hRunBZero =>
      subst runB
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (__run_evaluate a) (Term.Numeral 0))) =
              SmtTerm.Numeral 0 by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]
          rfl]
        change
          __smtx_typeof
              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof (SmtTerm.Numeral 0)
        rw [typeof_div_total_eq, hATyInt, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hAEvalValueTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt a)) =
              SmtType.Int := by
          simpa [hATyInt] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt a) (by
                unfold term_has_non_none_type
                rw [hATyInt]
                simp)
        rcases int_value_canonical hAEvalValueTy with
          ⟨evalA, hAEval⟩
        rw [show
            __smtx_model_eval M
                (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_div_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_31]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (__run_evaluate a) (Term.Numeral 0))) =
              SmtTerm.Numeral 0 by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_div_total evalA 0))
            (__smtx_model_eval M (SmtTerm.Numeral 0))
        rw [__smtx_model_eval.eq_2]
        simp [native_div_total]
        exact RuleProofs.smt_value_rel_refl _
  | inr hRunBNonzero =>
      rcases hRunBNonzero with ⟨runA, hRunA, hNZ⟩
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
        rw [hRunA]
        rfl
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.UOp UserOp.Int)
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hIntTypeNe hAEoInt hRunAEoType
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.div_total) a b rec hATransA hAProgTy with
        ⟨_hASameTy, hARel⟩
      have hRunBNe : runB ≠ 0 := by
        intro hZero
        subst runB
        simp [native_zeq] at hNZ
      have hZeroRunBNe : 0 ≠ runB := by
        intro hZero
        exact hRunBNe hZero.symm
      rw [hRunA]
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_div_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zdiv, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          __smtx_typeof
              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof (SmtTerm.Numeral (native_div_total runA runB))
        rw [typeof_div_total_eq, hATyInt, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Numeral runA) := by
          rw [hRunA] at hARel
          rw [show __eo_to_smt (Term.Numeral runA) =
              SmtTerm.Numeral runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_2] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Numeral runA :=
          EvaluateProofInternal.smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_div_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_31]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral 0)
                  (__eo_zdiv (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_div_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zdiv, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_div_total runA runB))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_div_total runA runB)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_mod_total_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) := by
  intro hATrans hEvalTy
  have hModTotalNN :
      term_has_non_none_type
        (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases int_binop_args_of_non_none
      (op := SmtTerm.mod_total)
      (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (R := SmtType.Int)
      (typeof_mod_total_eq (__eo_to_smt a) (__eo_to_smt b))
      hModTotalNN with
    ⟨hATyInt, hBTyInt⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyInt]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoInt : __eo_typeof a = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hAMatch.symm.trans hATyInt)
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hModTotalEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_div (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int
    rw [hAEoInt, hBEoInt]
    rfl
  let runATerm := __run_evaluate a
  let runBTerm := __run_evaluate b
  let runModTotal :=
    __eo_ite (__eo_eq runBTerm (Term.Numeral 0))
      runATerm (__eo_zmod runATerm runBTerm)
  have hRunModTotalNe : runModTotal ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
            runModTotal) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
          runModTotal ≠ Term.Stuck := by
    intro hMk
    cases hRun : runModTotal <;>
      simp [__eo_mk_apply, hRun] at hMk hRunModTotalNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
            runModTotal) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
            runModTotal) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunModTotalEoInt :
      __eo_typeof runModTotal = Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)
        runModTotal hEvalEqTy
    exact hEq.symm.trans hModTotalEoType
  rcases EvaluateProofInternal.eo_mod_total_args_shape_of_typeof_int
      runATerm runBTerm hRunModTotalNe hRunModTotalEoInt with
    ⟨runB, hRunB, hRunBShape⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
    change __eo_typeof runBTerm = Term.UOp UserOp.Int
    rw [hRunB]
    rfl
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.mod_total) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  have hBRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Numeral runB) := by
    change __run_evaluate b = Term.Numeral runB at hRunB
    rw [hRunB] at hBRel
    rw [show __eo_to_smt (Term.Numeral runB) =
        SmtTerm.Numeral runB by
      rfl] at hBRel
    rw [__smtx_model_eval.eq_2] at hBRel
    exact hBRel
  have hBEval :
      __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Numeral runB :=
    EvaluateProofInternal.smt_value_rel_numeral_eq
      (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
  change
    __smtx_typeof
        (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (__run_evaluate a)
              (__eo_zmod (__run_evaluate a) (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
              (__run_evaluate a)
              (__eo_zmod (__run_evaluate a) (__run_evaluate b)))))
  change __run_evaluate b = Term.Numeral runB at hRunB
  rw [hRunB]
  cases hRunBShape with
  | inl hRunBZero =>
      subst runB
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
        change
          __eo_typeof
              (__eo_ite (__eo_eq (__run_evaluate b) (Term.Numeral 0))
                (__run_evaluate a)
                (__eo_zmod (__run_evaluate a) (__run_evaluate b))) =
            Term.UOp UserOp.Int at hRunModTotalEoInt
        rw [hRunB] at hRunModTotalEoInt
        simpa [__eo_eq, __eo_ite, native_teq, native_ite]
          using hRunModTotalEoInt
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.UOp UserOp.Int)
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hIntTypeNe hAEoInt hRunAEoType
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.mod_total) a b rec hATransA hAProgTy with
        ⟨hASameTy, hARel⟩
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (__run_evaluate a)
                  (__eo_zmod (__run_evaluate a) (Term.Numeral 0))) =
              __eo_to_smt (__run_evaluate a) by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]]
        rw [typeof_mod_total_eq, hATyInt, hBTyInt]
        simp [native_ite, native_Teq]
        rw [← hASameTy, hATyInt]
      · have hAEvalValueTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt a)) =
              SmtType.Int := by
          simpa [hATyInt] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt a) (by
                unfold term_has_non_none_type
                rw [hATyInt]
                simp)
        rcases int_value_canonical hAEvalValueTy with
          ⟨evalA, hAEval⟩
        rw [show
            __smtx_model_eval M
                (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_mod_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_32]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral 0) (Term.Numeral 0))
                  (__run_evaluate a)
                  (__eo_zmod (__run_evaluate a) (Term.Numeral 0))) =
              __eo_to_smt (__run_evaluate a) by
          simp [__eo_eq, __eo_ite, native_teq, native_ite]]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_mod_total evalA 0))
            (__smtx_model_eval M (__eo_to_smt (__run_evaluate a)))
        have hModZero : native_mod_total evalA 0 = evalA := by
          simp [native_mod_total]
        rw [hModZero]
        rw [hAEval] at hARel
        exact hARel
  | inr hRunBNonzero =>
      rcases hRunBNonzero with ⟨runA, hRunA, hNZ⟩
      have hRunA' : __run_evaluate a = Term.Numeral runA := by
        simpa only [runATerm] using hRunA
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) = Term.UOp UserOp.Int := by
        rw [hRunA']
        rfl
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.UOp UserOp.Int)
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hIntTypeNe hAEoInt hRunAEoType
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.mod_total) a b rec hATransA hAProgTy with
        ⟨_hASameTy, hARel⟩
      have hRunBNe : runB ≠ 0 := by
        intro hZero
        subst runB
        simp [native_zeq] at hNZ
      have hZeroRunBNe : 0 ≠ runB := by
        intro hZero
        exact hRunBNe hZero.symm
      rw [hRunA']
      constructor
      · rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral runA)
                  (__eo_zmod (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_mod_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zmod, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          __smtx_typeof
              (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof (SmtTerm.Numeral (native_mod_total runA runB))
        rw [typeof_mod_total_eq, hATyInt, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Numeral runA) := by
          rw [hRunA'] at hARel
          rw [show __eo_to_smt (Term.Numeral runA) =
              SmtTerm.Numeral runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_2] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Numeral runA :=
          EvaluateProofInternal.smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_mod_total
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_32]]
        rw [hAEval, hBEval]
        rw [show
            __eo_to_smt
                (__eo_ite (__eo_eq (Term.Numeral runB) (Term.Numeral 0))
                  (Term.Numeral runA)
                  (__eo_zmod (Term.Numeral runA) (Term.Numeral runB))) =
              SmtTerm.Numeral (native_mod_total runA runB) by
          simp [__eo_eq, __eo_ite, __eo_zmod, hNZ, native_ite,
            native_teq, hZeroRunBNe]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_mod_total runA runB))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_mod_total runA runB)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _
