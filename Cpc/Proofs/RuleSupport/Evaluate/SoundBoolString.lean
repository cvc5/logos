module

public import Cpc.Proofs.RuleSupport.Evaluate.Typeof
import all Cpc.Proofs.RuleSupport.Evaluate.Typeof
import Cpc.Proofs.RuleSupport.StrEqReplSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.run_evaluate_sound_apply_and_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hATrans hEvalTy
  have hAndBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) :=
    EvaluateProofInternal.has_bool_type_and_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    RuleProofs.eo_has_bool_type_and_left a b hAndBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    RuleProofs.eo_has_bool_type_and_right a b hAndBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hAndEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunAndNe :
      __eo_and (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
          (__eo_and (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_and (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAndNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAndEoBool :
      __eo_typeof (__eo_and (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b)
        (__eo_and (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hAndEoBool
  rcases EvaluateProofInternal.eo_and_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunAndEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.and) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.and) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_and runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_and_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hRelAnd :=
      EvaluateProofInternal.smt_value_rel_model_eval_and_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runA))
        (__smtx_model_eval M (SmtTerm.Boolean runB))
        hARelBool hBRelBool
    simpa [__eo_and, __smtx_model_eval, __smtx_model_eval_and] using hRelAnd

theorem EvaluateProofInternal.run_evaluate_sound_apply_or_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hATrans hEvalTy
  have hOrBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) :=
    EvaluateProofInternal.has_bool_type_or_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    EvaluateProofInternal.has_bool_type_or_left a b hOrBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    EvaluateProofInternal.has_bool_type_or_right a b hOrBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hOrEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunOrNe :
      __eo_or (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
          (__eo_or (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_or (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunOrNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunOrEoBool :
      __eo_typeof (__eo_or (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b)
        (__eo_or (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hOrEoBool
  rcases EvaluateProofInternal.eo_or_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunOrEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.or) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.or) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_or runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_or_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hRelOr :=
      EvaluateProofInternal.smt_value_rel_model_eval_or_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runA))
        (__smtx_model_eval M (SmtTerm.Boolean runB))
        hARelBool hBRelBool
    simpa [__eo_or, __smtx_model_eval, __smtx_model_eval_or] using hRelOr

theorem EvaluateProofInternal.run_evaluate_sound_apply_xor_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hATrans hEvalTy
  have hXorBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) :=
    EvaluateProofInternal.has_bool_type_xor_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    EvaluateProofInternal.has_bool_type_xor_left a b hXorBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    EvaluateProofInternal.has_bool_type_xor_right a b hXorBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hXorEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunXorNe :
      __eo_xor (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
          (__eo_xor (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_xor (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunXorNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunXorEoBool :
      __eo_typeof (__eo_xor (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b)
        (__eo_xor (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hXorEoBool
  rcases EvaluateProofInternal.eo_xor_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunXorEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.xor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.xor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_not (native_iff runA runB)))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_xor_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Boolean runA) := by
      simpa [__smtx_model_eval] using hARelBool
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean runB) := by
      simpa [__smtx_model_eval] using hBRelBool
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean runA :=
      EvaluateProofInternal.smt_value_rel_boolean_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean runB :=
      EvaluateProofInternal.smt_value_rel_boolean_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_xor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __eo_to_smt
            (__eo_xor (Term.Boolean runA) (Term.Boolean runB)) =
          SmtTerm.Boolean (native_not (native_iff runA runB)) by
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Boolean (native_not (native_iff runA runB))) =
          SmtValue.Boolean (native_not (native_iff runA runB)) by
      simp [__smtx_model_eval]]
    cases runA <;> cases runB <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_xor,
        __smtx_model_eval_not, __smtx_model_eval_eq, native_iff,
        native_not, native_veq]

theorem EvaluateProofInternal.run_evaluate_sound_apply_imp_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hATrans hEvalTy
  have hImpBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) :=
    EvaluateProofInternal.has_bool_type_imp_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    EvaluateProofInternal.has_bool_type_imp_left a b hImpBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    EvaluateProofInternal.has_bool_type_imp_right a b hImpBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hImpEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunImpNe :
      __eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
          (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun :
        __eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunImpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunImpEoBool :
      __eo_typeof
          (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b)
        (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))
        hEvalEqTy
    exact hEq.symm.trans hImpEoBool
  rcases EvaluateProofInternal.eo_or_args_boolean_of_typeof_bool
      (__eo_not (__run_evaluate a)) (__run_evaluate b)
      hRunImpEoBool with
    ⟨runNotA, runB, hRunNotA, hRunB⟩
  have hRunNotAEoBool : __eo_typeof (__eo_not (__run_evaluate a)) = Term.Bool := by
    rw [hRunNotA]
    rfl
  rcases EvaluateProofInternal.eo_not_arg_boolean_of_typeof_bool
      (__run_evaluate a) hRunNotAEoBool with
    ⟨runA, hRunA⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.imp) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.imp) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_or (native_not runA) runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_imp_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Boolean runA) := by
      simpa [__smtx_model_eval] using hARelBool
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean runB) := by
      simpa [__smtx_model_eval] using hBRelBool
    have hRelImp :=
      EvaluateProofInternal.smt_value_rel_model_eval_imp_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Boolean runA)
        (SmtValue.Boolean runB)
        hARelValue hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_imp
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [show
        __eo_to_smt
            (__eo_or (__eo_not (Term.Boolean runA)) (Term.Boolean runB)) =
          SmtTerm.Boolean (native_or (native_not runA) runB) by
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Boolean (native_or (native_not runA) runB)) =
          SmtValue.Boolean (native_or (native_not runA) runB) by
      simp [__smtx_model_eval]]
    simpa [__smtx_model_eval_imp, __smtx_model_eval_not, __smtx_model_eval_or]
      using hRelImp

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_concat_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) := by
  intro hATrans hEvalTy
  have hConcatNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases EvaluateProofInternal.smt_str_concat_args_of_non_none_local a b hConcatNN with
    ⟨T, hATy, hBTy, hConcatTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hOrigMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) hATrans
  have hOrigEoSmtSeq :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b)) =
        SmtType.Seq T := by
    rw [← hOrigMatch]
    exact hConcatTy
  rcases TranslationProofs.eo_to_smt_type_eq_seq hOrigEoSmtSeq with
    ⟨U, hOrigEoSeq, _hUSmt⟩
  have hRunConcatNe :
      __eo_concat (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
          (__eo_concat (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_concat (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunConcatNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunConcatEoSeq :
      __eo_typeof (__eo_concat (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.Seq) U := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b)
        (__eo_concat (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hOrigEoSeq
  rcases EvaluateProofInternal.eo_concat_args_string_of_typeof_seq
      (__run_evaluate a) (__run_evaluate b) U hRunConcatEoSeq with
    ⟨sx, sy, hRunA, hRunB, hUChar⟩
  subst U
  have hOrigEoSeqChar :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    simpa using hOrigEoSeq
  rcases EvaluateProofInternal.eo_typeof_str_concat_args_of_seq_char a b hOrigEoSeqChar with
    ⟨hAEoSeqChar, hBEoSeqChar⟩
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoSmtChar :
      __eo_to_smt_type (__eo_typeof a) = SmtType.Seq SmtType.Char := by
    rw [hAEoSeqChar]
    simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  have hBEoSmtChar :
      __eo_to_smt_type (__eo_typeof b) = SmtType.Seq SmtType.Char := by
    rw [hBEoSeqChar]
    simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  have hATyChar :
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char :=
    hAMatch.trans hAEoSmtChar
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    hBMatch.trans hBEoSmtChar
  have hRunAEoSeqChar :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    rw [hRunA]
    rfl
  have hRunBEoSeqChar :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    rw [hRunB]
    rfl
  have hSeqCharNe :
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hSeqCharNe hAEoSeqChar hRunAEoSeqChar
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqCharNe hBEoSeqChar hRunBEoSeqChar
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_concat) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_concat) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hSxTy :
      __smtx_typeof (__eo_to_smt (Term.String sx)) =
        SmtType.Seq SmtType.Char := by
    have h := hASameTy
    rw [hRunA] at h
    exact h.symm.trans hATyChar
  have hSyTy :
      __smtx_typeof (__eo_to_smt (Term.String sy)) =
        SmtType.Seq SmtType.Char := by
    have h := hBSameTy
    rw [hRunB] at h
    exact h.symm.trans hBTyChar
  have hSxValid : native_string_valid sx = true :=
    EvaluateProofInternal.native_string_valid_of_string_type hSxTy
  have hSyValid : native_string_valid sy = true :=
    EvaluateProofInternal.native_string_valid_of_string_type hSyTy
  have hConcatValid :
      native_string_valid (native_str_concat sx sy) = true := by
    change native_string_valid (sx ++ sy) = true
    exact EvaluateProofInternal.native_string_valid_append_local hSxValid hSyValid
  change
    __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_concat (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_concat (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.String (native_str_concat sx sy))
    rw [show
        __smtx_typeof
            (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
          SmtType.Seq SmtType.Char by
      simp [__smtx_typeof, __smtx_typeof_seq_op_2, hATyChar,
        hBTyChar, native_Teq, native_ite]]
    simp [__smtx_typeof, hConcatValid, native_ite]
  · have hSxEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sx)) =
          SmtValue.Seq (native_pack_string sx) := by
      rw [show __eo_to_smt (Term.String sx) = SmtTerm.String sx by rfl]
      rw [__smtx_model_eval.eq_4]
    have hSyEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sy)) =
          SmtValue.Seq (native_pack_string sy) := by
      rw [show __eo_to_smt (Term.String sy) = SmtTerm.String sy by rfl]
      rw [__smtx_model_eval.eq_4]
    have hARelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt (Term.String sx))) := by
      simpa [hRunA] using hARel
    have hBRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String sy))) := by
      simpa [hRunB] using hBRel
    have hARelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Seq (native_pack_string sx)) := by
      simpa [hSxEval] using hARelString
    have hBRelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Seq (native_pack_string sy)) := by
      simpa [hSyEval] using hBRelString
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hARelSeq with
      ⟨sxEval, hAEval, hASeqRel⟩
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hBRelSeq with
      ⟨syEval, hBEval, hBSeqRel⟩
    have hASeqEq :
        sxEval = native_pack_string sx :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
    have hBSeqEq :
        syEval = native_pack_string sy :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_str_concat
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_81]]
    rw [hAEval, hBEval, hASeqEq, hBSeqEq]
    rw [show __eo_to_smt
          (__eo_concat (Term.String sx) (Term.String sy)) =
        SmtTerm.String (native_str_concat sx sy) by
      rfl]
    rw [__smtx_model_eval.eq_4]
    simp [__smtx_model_eval_str_concat, native_seq_concat,
      native_pack_string, native_str_concat, EvaluateProofInternal.native_unpack_pack_seq_local,
      EvaluateProofInternal.elem_typeof_pack_seq_local, List.map_append,
      RuleProofs.smtx_model_eval_eq_refl]

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_at_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) a) b) := by
  intro hATrans hEvalTy
  have hAtNN :
      term_has_non_none_type
        (SmtTerm.str_at (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases str_at_args_of_non_none hAtNN with ⟨T, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  let runA := __run_evaluate a
  let runB := __run_evaluate b
  let runAt := __eo_extract runA runB runB
  have hRunAtNe : runAt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) a) b))
            runAt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hRunANe' : runA ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [runAt] using hRunAtNe)
    simpa [runA] using hRunANe'
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunBNe' : runB ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_start_ne_stuck (by simpa [runAt] using hRunAtNe)
    simpa [runB] using hRunBNe'
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq a T hATransA hATy hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int b hBTrans hBTy hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_at) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_at) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunATy :
      __smtx_typeof (__eo_to_smt runA) = SmtType.Seq T := by
    simpa [runA] using hASameTy.symm.trans hATy
  have hRunBTy :
      __smtx_typeof (__eo_to_smt runB) = SmtType.Int := by
    simpa [runB] using hBSameTy.symm.trans hBTy
  rcases EvaluateProofInternal.eo_extract_same_seq_int_args_of_nonstuck runA runB
      hRunATy hRunBTy (by simpa [runAt] using hRunAtNe) with
    ⟨str, i, hRunA, hRunB, hValid, hTChar⟩
  subst T
  have hRunAtEq :
      runAt = Term.String (native_str_substr str i 1) := by
    dsimp [runAt]
    rw [hRunA, hRunB]
    exact EvaluateProofInternal.eo_extract_string_same_index str i
  have hSubValid :
      native_string_valid (native_str_substr str i 1) = true :=
    EvaluateProofInternal.native_string_valid_substr_local i 1 hValid
  change
    __smtx_typeof (SmtTerm.str_at (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runAt) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_at (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runAt))
  rw [hRunAtEq]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_at (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.String (native_str_substr str i 1))
    rw [typeof_str_at_eq]
    simp [__smtx_typeof_str_at, __smtx_typeof, hATy, hBTy,
      hSubValid, native_ite]
  · have hStrEval :
        __smtx_model_eval M (__eo_to_smt (Term.String str)) =
          SmtValue.Seq (native_pack_string str) := by
      rw [show __eo_to_smt (Term.String str) = SmtTerm.String str by rfl]
      rw [__smtx_model_eval.eq_4]
    have hIdxEval :
        __smtx_model_eval M (__eo_to_smt (Term.Numeral i)) =
          SmtValue.Numeral i := by
      rw [show __eo_to_smt (Term.Numeral i) = SmtTerm.Numeral i by rfl]
      rw [__smtx_model_eval.eq_2]
    have hARelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt runA)) := by
      simpa [runA] using hARel
    have hBRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runB)) := by
      simpa [runB] using hBRel
    have hARelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt (Term.String str))) := by
      simpa [hRunA] using hARelRun
    have hBRelNumeralTerm :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.Numeral i))) := by
      simpa [hRunB] using hBRelRun
    have hARelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Seq (native_pack_string str)) := by
      simpa [hStrEval] using hARelString
    have hBRelNumeral :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Numeral i) := by
      simpa [hIdxEval] using hBRelNumeralTerm
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hARelSeq with
      ⟨strEval, hAEval, hASeqRel⟩
    have hASeqEq :
        strEval = native_pack_string str :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral i :=
      EvaluateProofInternal.smt_value_rel_numeral_eq _ i hBRelNumeral
    have hSubEval :
        __smtx_model_eval M
            (__eo_to_smt (Term.String (native_str_substr str i 1))) =
          SmtValue.Seq (native_pack_string (native_str_substr str i 1)) := by
      rw [show
          __eo_to_smt (Term.String (native_str_substr str i 1)) =
            SmtTerm.String (native_str_substr str i 1) by
        rfl]
      rw [__smtx_model_eval.eq_4]
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_at (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_str_at
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hASeqEq, hBEval, hSubEval]
    simp only [__smtx_model_eval_str_at, __smtx_model_eval_str_substr]
    rw [show
        __smtx_elem_typeof_seq_value (native_pack_string str) =
          SmtType.Char by
      simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
    rw [EvaluateProofInternal.native_seq_extract_pack_string_one]
    exact RuleProofs.smtx_model_eval_eq_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_prefixof_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) a) b) := by
  intro hATrans hEvalTy
  have hPrefixNN :
      term_has_non_none_type
        (SmtTerm.str_prefixof (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_prefixof)
      (typeof_str_prefixof_eq (__eo_to_smt a) (__eo_to_smt b))
      hPrefixNN with
    ⟨T, hATyChar, hBTyChar⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyChar]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  let runA := __run_evaluate a
  let runB := __run_evaluate b
  let runLen := __eo_len runA
  let runEnd := __eo_add runLen (Term.Numeral (-1 : native_Int))
  let runSlice := __eo_extract runB (Term.Numeral 0) runEnd
  let runPrefix := __eo_eq runA runSlice
  have hRunPrefixNe : runPrefix ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) a) b))
            runPrefix) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunSliceNe : runSlice ≠ Term.Stuck := by
    intro hStuck
    apply hRunPrefixNe
    dsimp [runPrefix]
    rw [hStuck]
    cases runA <;> rfl
  have hRunLenNe : runLen ≠ Term.Stuck := by
    intro hStuck
    apply hRunSliceNe
    dsimp [runSlice, runEnd]
    rw [hStuck]
    simp [__eo_add, __eo_extract]
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hRunANe' : runA ≠ Term.Stuck :=
      EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLen] using hRunLenNe)
    simpa [runA] using hRunANe'
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunBNe' : runB ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [runSlice] using hRunSliceNe)
    simpa [runB] using hRunBNe'
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq a T
      hATransA hATyChar hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b T
      hBTrans hBTyChar hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_prefixof) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_prefixof) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunATy :
      __smtx_typeof (__eo_to_smt runA) = SmtType.Seq T := by
    simpa [runA] using hASameTy.symm.trans hATyChar
  have hRunBTy :
      __smtx_typeof (__eo_to_smt runB) = SmtType.Seq T := by
    simpa [runB] using hBSameTy.symm.trans hBTyChar
  rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runA hRunATy
      (by simpa [runLen] using hRunLenNe) with
    ⟨sx, hRunA, hSxValid, _hTChar⟩
  subst T
  have hRunSliceNeConcrete :
      __eo_extract runB (Term.Numeral 0)
          (Term.Numeral (native_zplus (native_str_len sx)
            (-1 : native_Int))) ≠ Term.Stuck := by
    simpa [runSlice, runEnd, runLen, hRunA, __eo_len, __eo_add]
      using hRunSliceNe
  rcases EvaluateProofInternal.eo_extract_seq_char_numeral_args_of_nonstuck runB 0
      (native_zplus (native_str_len sx) (-1 : native_Int))
      hRunBTy hRunSliceNeConcrete with
    ⟨sy, hRunB, hSyValid⟩
  have hRunSliceEq :
      runSlice =
        Term.String (native_str_substr sy 0 (native_str_len sx)) := by
    dsimp [runSlice, runEnd, runLen]
    rw [hRunA, hRunB]
    exact EvaluateProofInternal.eo_extract_string_zero_len_minus_one sx sy
  have hRunPrefixEq :
      runPrefix =
        Term.Boolean
          (native_teq
            (Term.String (native_str_substr sy 0 (native_str_len sx)))
            (Term.String sx)) := by
    dsimp [runPrefix]
    rw [hRunA, hRunSliceEq]
    rfl
  change
    __smtx_typeof (SmtTerm.str_prefixof (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runPrefix) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_prefixof (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runPrefix))
  rw [hRunPrefixEq]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_prefixof (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Boolean
            (native_teq
              (Term.String (native_str_substr sy 0 (native_str_len sx)))
              (Term.String sx)))
    rw [typeof_str_prefixof_eq]
    simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, hATyChar, hBTyChar,
      native_Teq, native_ite]
  · have hSxEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sx)) =
          SmtValue.Seq (native_pack_string sx) := by
      rw [show __eo_to_smt (Term.String sx) = SmtTerm.String sx by rfl]
      rw [__smtx_model_eval.eq_4]
    have hSyEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sy)) =
          SmtValue.Seq (native_pack_string sy) := by
      rw [show __eo_to_smt (Term.String sy) = SmtTerm.String sy by rfl]
      rw [__smtx_model_eval.eq_4]
    have hARelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt runA)) := by
      simpa [runA] using hARel
    have hBRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runB)) := by
      simpa [runB] using hBRel
    have hARelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt (Term.String sx))) := by
      simpa [hRunA] using hARelRun
    have hBRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String sy))) := by
      simpa [hRunB] using hBRelRun
    have hARelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Seq (native_pack_string sx)) := by
      simpa [hSxEval] using hARelString
    have hBRelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Seq (native_pack_string sy)) := by
      simpa [hSyEval] using hBRelString
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hARelSeq with
      ⟨sxEval, hAEval, hASeqRel⟩
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hBRelSeq with
      ⟨syEval, hBEval, hBSeqRel⟩
    have hASeqEq :
        sxEval = native_pack_string sx :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
    have hBSeqEq :
        syEval = native_pack_string sy :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_prefixof (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_str_prefixof
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval, hASeqEq, hBSeqEq]
    rw [show
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Boolean
              (native_teq
                (Term.String (native_str_substr sy 0 (native_str_len sx)))
                (Term.String sx)))) =
          SmtValue.Boolean
            (native_teq
              (Term.String (native_str_substr sy 0 (native_str_len sx)))
              (Term.String sx)) by
      rw [show
          __eo_to_smt
            (Term.Boolean
              (native_teq
                (Term.String (native_str_substr sy 0 (native_str_len sx)))
                (Term.String sx))) =
            SmtTerm.Boolean
              (native_teq
                (Term.String (native_str_substr sy 0 (native_str_len sx)))
                (Term.String sx)) by
        rfl]
      rw [__smtx_model_eval.eq_1]]
    simp only [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr]
    rw [show
        native_seq_len (native_unpack_seq (native_pack_string sx)) =
          native_str_len sx by
      simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local, native_seq_len,
        native_str_len]]
    rw [show
        __smtx_elem_typeof_seq_value (native_pack_string sy) =
          SmtType.Char by
      simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
    rw [EvaluateProofInternal.native_seq_extract_pack_string]
    by_cases hSubEq :
        native_str_substr sy 0 (native_str_len sx) = sx
    · rw [hSubEq]
      simp [__smtx_model_eval_eq, native_veq, native_teq]
    · have hSxSubNe :
          sx ≠ native_str_substr sy 0 (native_str_len sx) := by
        intro hEq
        exact hSubEq hEq.symm
      have hPackNe :
          native_pack_string sx ≠
            native_pack_string
              (native_str_substr sy 0 (native_str_len sx)) := by
        intro hPack
        exact hSxSubNe (EvaluateProofInternal.native_pack_string_injective hPack)
      simp [__smtx_model_eval_eq, native_veq, native_teq, hSubEq,
        hPackNe]

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_suffixof_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) a) b) := by
  intro hATrans hEvalTy
  have hSuffixNN :
      term_has_non_none_type
        (SmtTerm.str_suffixof (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_suffixof)
      (typeof_str_suffixof_eq (__eo_to_smt a) (__eo_to_smt b))
      hSuffixNN with
    ⟨T, hATyChar, hBTyChar⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyChar]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  let runA := __run_evaluate a
  let runB := __run_evaluate b
  let runLenB := __eo_len runB
  let runLenA := __eo_len runA
  let runStart := __eo_add runLenB (__eo_neg runLenA)
  let runEnd := __eo_add runLenB (Term.Numeral (-1 : native_Int))
  let runSlice := __eo_extract runB runStart runEnd
  let runSuffix := __eo_eq runA runSlice
  have hRunSuffixNe : runSuffix ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) a) b))
            runSuffix) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunSliceNe : runSlice ≠ Term.Stuck := by
    intro hStuck
    apply hRunSuffixNe
    dsimp [runSuffix]
    rw [hStuck]
    cases runA <;> rfl
  have hRunLenBNe : runLenB ≠ Term.Stuck := by
    intro hStuck
    apply hRunSliceNe
    dsimp [runSlice, runStart, runEnd]
    rw [hStuck]
    simp [__eo_add, __eo_extract]
  have hRunLenANe : runLenA ≠ Term.Stuck := by
    intro hStuck
    have hNegStuck : __eo_neg Term.Stuck = Term.Stuck := rfl
    apply hRunSliceNe
    dsimp [runSlice, runStart]
    rw [hStuck, hNegStuck]
    simp [__eo_add, __eo_extract]
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hRunANe' : runA ≠ Term.Stuck :=
      EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLenA] using hRunLenANe)
    simpa [runA] using hRunANe'
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunBNe' : runB ≠ Term.Stuck :=
      EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLenB] using hRunLenBNe)
    simpa [runB] using hRunBNe'
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq a T
      hATransA hATyChar hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b T
      hBTrans hBTyChar hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_suffixof) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_suffixof) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunATy :
      __smtx_typeof (__eo_to_smt runA) = SmtType.Seq T := by
    simpa [runA] using hASameTy.symm.trans hATyChar
  have hRunBTy :
      __smtx_typeof (__eo_to_smt runB) = SmtType.Seq T := by
    simpa [runB] using hBSameTy.symm.trans hBTyChar
  rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runB hRunBTy
      (by simpa [runLenB] using hRunLenBNe) with
    ⟨sy, hRunB, _hSyValid, _hTCharB⟩
  subst T
  rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runA hRunATy
      (by simpa [runLenA] using hRunLenANe) with
    ⟨sx, hRunA, _hSxValid, _hTCharA⟩
  have hRunSliceEq :
      runSlice =
        Term.String
          (native_str_substr sy
            (native_str_len sy + -native_str_len sx)
            (native_str_len sx)) := by
    dsimp [runSlice, runStart, runEnd, runLenA, runLenB]
    rw [hRunA, hRunB]
    exact EvaluateProofInternal.eo_extract_string_suffix_window sx sy
  have hRunSuffixEq :
      runSuffix =
        Term.Boolean
          (native_teq
            (Term.String
              (native_str_substr sy
                (native_str_len sy + -native_str_len sx)
                (native_str_len sx)))
            (Term.String sx)) := by
    dsimp [runSuffix]
    rw [hRunA, hRunSliceEq]
    rfl
  change
    __smtx_typeof (SmtTerm.str_suffixof (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runSuffix) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_suffixof (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runSuffix))
  rw [hRunSuffixEq]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_suffixof (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Boolean
            (native_teq
              (Term.String
                (native_str_substr sy
                  (native_str_len sy + -native_str_len sx)
                  (native_str_len sx)))
              (Term.String sx)))
    rw [typeof_str_suffixof_eq]
    simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, hATyChar, hBTyChar,
      native_Teq, native_ite]
  · have hSxEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sx)) =
          SmtValue.Seq (native_pack_string sx) := by
      rw [show __eo_to_smt (Term.String sx) = SmtTerm.String sx by rfl]
      rw [__smtx_model_eval.eq_4]
    have hSyEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sy)) =
          SmtValue.Seq (native_pack_string sy) := by
      rw [show __eo_to_smt (Term.String sy) = SmtTerm.String sy by rfl]
      rw [__smtx_model_eval.eq_4]
    have hARelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt runA)) := by
      simpa [runA] using hARel
    have hBRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runB)) := by
      simpa [runB] using hBRel
    have hARelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt (Term.String sx))) := by
      simpa [hRunA] using hARelRun
    have hBRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String sy))) := by
      simpa [hRunB] using hBRelRun
    have hARelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Seq (native_pack_string sx)) := by
      simpa [hSxEval] using hARelString
    have hBRelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Seq (native_pack_string sy)) := by
      simpa [hSyEval] using hBRelString
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hARelSeq with
      ⟨sxEval, hAEval, hASeqRel⟩
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hBRelSeq with
      ⟨syEval, hBEval, hBSeqRel⟩
    have hASeqEq :
        sxEval = native_pack_string sx :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
    have hBSeqEq :
        syEval = native_pack_string sy :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_suffixof (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_str_suffixof
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval, hASeqEq, hBSeqEq]
    rw [show
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Boolean
              (native_teq
                (Term.String
                  (native_str_substr sy
                    (native_str_len sy + -native_str_len sx)
                    (native_str_len sx)))
                (Term.String sx)))) =
          SmtValue.Boolean
            (native_teq
              (Term.String
                (native_str_substr sy
                  (native_str_len sy + -native_str_len sx)
                  (native_str_len sx)))
              (Term.String sx)) by
      rw [show
          __eo_to_smt
            (Term.Boolean
              (native_teq
                (Term.String
                  (native_str_substr sy
                    (native_str_len sy + -native_str_len sx)
                    (native_str_len sx)))
                (Term.String sx))) =
            SmtTerm.Boolean
              (native_teq
                (Term.String
                  (native_str_substr sy
                    (native_str_len sy + -native_str_len sx)
                    (native_str_len sx)))
                (Term.String sx)) by
        rfl]
      rw [__smtx_model_eval.eq_1]]
    simp only [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval__]
    rw [show
        native_seq_len (native_unpack_seq (native_pack_string sx)) =
          native_str_len sx by
      simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local, native_seq_len,
        native_str_len]]
    rw [show
        native_seq_len (native_unpack_seq (native_pack_string sy)) =
          native_str_len sy by
      simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local, native_seq_len,
        native_str_len]]
    rw [show
        __smtx_elem_typeof_seq_value (native_pack_string sy) =
          SmtType.Char by
      simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
    rw [EvaluateProofInternal.native_seq_extract_pack_string]
    simp only [native_zplus, native_zneg]
    by_cases hSubEq :
        native_str_substr sy
            (native_str_len sy + -native_str_len sx)
            (native_str_len sx) =
          sx
    · rw [hSubEq]
      simp [__smtx_model_eval_eq, native_veq, native_teq]
    · have hSxSubNe :
          sx ≠
            native_str_substr sy
              (native_str_len sy + -native_str_len sx)
              (native_str_len sx) := by
        intro hEq
        exact hSubEq hEq.symm
      have hPackNe :
          native_pack_string sx ≠
            native_pack_string
              (native_str_substr sy
                (native_str_len sy + -native_str_len sx)
                (native_str_len sx)) := by
        intro hPack
        exact hSxSubNe (EvaluateProofInternal.native_pack_string_injective hPack)
      simp [__smtx_model_eval_eq, native_veq, native_teq, hSubEq,
        hPackNe]

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_contains_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) a) b) := by
  intro hATrans hEvalTy
  have hContainsNN :
      term_has_non_none_type
        (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
      (typeof_str_contains_eq (__eo_to_smt a) (__eo_to_smt b))
      hContainsNN with
    ⟨T, hATySeq, hBTySeq⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATySeq]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTySeq]
    simp
  let runA := __run_evaluate a
  let runB := __run_evaluate b
  let runFind := __eo_find runA runB
  let runContains := __eo_not (__eo_is_neg runFind)
  have hRunContainsNe : runContains ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) a) b))
            runContains) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunFindNe : runFind ≠ Term.Stuck := by
    intro hStuck
    apply hRunContainsNe
    dsimp [runContains]
    rw [hStuck]
    rfl
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hRunANe' : runA ≠ Term.Stuck :=
      EvaluateProofInternal.eo_find_left_ne_stuck (by simpa [runFind] using hRunFindNe)
    simpa [runA] using hRunANe'
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunBNe' : runB ≠ Term.Stuck :=
      EvaluateProofInternal.eo_find_right_ne_stuck (by simpa [runFind] using hRunFindNe)
    simpa [runB] using hRunBNe'
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq a T hATransA hATySeq hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b T hBTrans hBTySeq hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_contains) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_contains) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunATy :
      __smtx_typeof (__eo_to_smt runA) = SmtType.Seq T := by
    simpa [runA] using hASameTy.symm.trans hATySeq
  have hRunBTy :
      __smtx_typeof (__eo_to_smt runB) = SmtType.Seq T := by
    simpa [runB] using hBSameTy.symm.trans hBTySeq
  rcases EvaluateProofInternal.eo_find_seq_args_of_nonstuck runA runB hRunATy hRunBTy
      (by simpa [runFind] using hRunFindNe) with
    ⟨sx, sy, hRunA, hRunB, _hSxValid, _hSyValid, hTChar⟩
  subst T
  have hRunContainsEq :
      runContains =
        Term.Boolean (native_not (native_zlt (native_str_indexof sx sy 0) 0)) := by
    dsimp [runContains, runFind]
    rw [hRunA, hRunB]
    simp [__eo_find, __eo_is_neg, __eo_not]
  change
    __smtx_typeof (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runContains) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runContains))
  rw [hRunContainsEq]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Boolean
            (native_not (native_zlt (native_str_indexof sx sy 0) 0)))
    rw [typeof_str_contains_eq]
    simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, hATySeq,
      hBTySeq, native_Teq, native_ite]
  · have hSxEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sx)) =
          SmtValue.Seq (native_pack_string sx) := by
      rw [show __eo_to_smt (Term.String sx) = SmtTerm.String sx by rfl]
      rw [__smtx_model_eval.eq_4]
    have hSyEval :
        __smtx_model_eval M (__eo_to_smt (Term.String sy)) =
          SmtValue.Seq (native_pack_string sy) := by
      rw [show __eo_to_smt (Term.String sy) = SmtTerm.String sy by rfl]
      rw [__smtx_model_eval.eq_4]
    have hARelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt runA)) := by
      simpa [runA] using hARel
    have hBRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runB)) := by
      simpa [runB] using hBRel
    have hARelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt (Term.String sx))) := by
      simpa [hRunA] using hARelRun
    have hBRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String sy))) := by
      simpa [hRunB] using hBRelRun
    have hARelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Seq (native_pack_string sx)) := by
      simpa [hSxEval] using hARelString
    have hBRelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Seq (native_pack_string sy)) := by
      simpa [hSyEval] using hBRelString
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hARelSeq with
      ⟨sxEval, hAEval, hASeqRel⟩
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hBRelSeq with
      ⟨syEval, hBEval, hBSeqRel⟩
    have hASeqEq :
        sxEval = native_pack_string sx :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
    have hBSeqEq :
        syEval = native_pack_string sy :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_str_contains
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval, hASeqEq, hBSeqEq]
    rw [show
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Boolean
              (native_not (native_zlt (native_str_indexof sx sy 0) 0)))) =
          SmtValue.Boolean
            (native_not (native_zlt (native_str_indexof sx sy 0) 0)) by
      rw [show
          __eo_to_smt
            (Term.Boolean
              (native_not (native_zlt (native_str_indexof sx sy 0) 0))) =
            SmtTerm.Boolean
              (native_not (native_zlt (native_str_indexof sx sy 0) 0)) by
        rfl]
      rw [__smtx_model_eval.eq_1]]
    simp only [__smtx_model_eval_str_contains]
    rw [EvaluateProofInternal.native_seq_contains_pack_string]
    exact RuleProofs.smtx_model_eval_eq_refl _

theorem EvaluateProofInternal.smt_model_eval_eo_to_smt_numeral_term
    (M : SmtModel) (i : native_Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral i)) =
      SmtValue.Numeral i := by
  change __smtx_model_eval M (SmtTerm.Numeral i) =
    SmtValue.Numeral i
  rw [__smtx_model_eval.eq_2]

theorem EvaluateProofInternal.smt_typeof_str_indexof_eq_typeof_numeral_of_arg_types
    (s pat n : Term) (T : SmtType) (i : native_Int)
    (hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hPatTySeq : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq T)
    (hNTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt pat)
          (__eo_to_smt n)) =
      __smtx_typeof (SmtTerm.Numeral i) := by
  rw [typeof_str_indexof_eq]
  simp [__smtx_typeof_str_indexof, __smtx_typeof, hSTySeq,
    hPatTySeq, hNTy, native_Teq, native_ite]

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_to_numeral_of_runs
    (M : SmtModel)
    (s pat n runS runPat runN : Term) (i : native_Int) :
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt runS)) ->
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt pat))
        (__smtx_model_eval M (__eo_to_smt runPat)) ->
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt n))
        (__smtx_model_eval M (__eo_to_smt runN)) ->
    __smtx_model_eval_str_indexof
        (__smtx_model_eval M (__eo_to_smt runS))
        (__smtx_model_eval M (__eo_to_smt runPat))
        (__smtx_model_eval M (__eo_to_smt runN)) =
      SmtValue.Numeral i ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt pat)
            (__eo_to_smt n)))
        (SmtValue.Numeral i) := by
  intro hSRel hPatRel hNRel hRunEval
  have hRel :=
    EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_of_rel
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (__eo_to_smt pat))
      (__smtx_model_eval M (__eo_to_smt n))
      (__smtx_model_eval M (__eo_to_smt runS))
      (__smtx_model_eval M (__eo_to_smt runPat))
      (__smtx_model_eval M (__eo_to_smt runN))
      hSRel hPatRel hNRel
  rw [show
      __smtx_model_eval M
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt pat)
            (__eo_to_smt n)) =
        __smtx_model_eval_str_indexof
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt pat))
          (__smtx_model_eval M (__eo_to_smt n)) by
    rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hRunEval] at hRel
  exact hRel

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_indexof_core
    (M : SmtModel) (hM : model_wf M)
    (s pat n : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) pat)
                n) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) pat)
      n) := by
  intro hATrans hEvalTy
  let whole :=
    Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) pat)
      n
  have hIndexNN :
      term_has_non_none_type
        (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt pat)
          (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation, whole] at hsimpa ⊢
    exact hsimpa
  rcases str_indexof_args_of_non_none hIndexNN with
    ⟨T, hSTySeq, hPatTySeq, hNTy⟩
  have hSTrans : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSTySeq]
    simp
  have hPatTrans : RuleProofs.eo_has_smt_translation pat := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hPatTySeq]
    simp
  have hNTrans : RuleProofs.eo_has_smt_translation n := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hNTy]
    simp
  let runS := __run_evaluate s
  let runPat := __run_evaluate pat
  let runN := __run_evaluate n
  let runLen := __eo_len runS
  let runFind :=
    __eo_find
      (__eo_to_str (__eo_extract runS n runLen))
      (__eo_to_str runPat)
  let runInner :=
    __eo_ite (__eo_is_neg runFind) runFind (__eo_add n runFind)
  let runRest :=
    __eo_ite (__eo_gt runN runLen)
      (Term.Numeral (-1 : native_Int)) runInner
  let runIndex :=
    __eo_ite (__eo_is_neg runN)
      (Term.Numeral (-1 : native_Int)) runRest
  have hRunIndexNe : runIndex ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole)
            runIndex) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg runN) (Term.Numeral (-1 : native_Int)) runRest
      hRunIndexNe with
    ⟨bTop, hRunNNegBool, hTopSelected⟩
  have hRunNNegNe : __eo_is_neg runN ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hRunNNegBool
    cases hRunNNegBool
  have hRunNNe : runN ≠ Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunNNegNe
  have hRunNOrigNe : __run_evaluate n ≠ Term.Stuck := by
    simpa [runN] using hRunNNe
  have hNProgTy : __eo_typeof (__eo_prog_evaluate n) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int n hNTrans hNTy
      hRunNOrigNe
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3 M
      (Term.UOp UserOp.str_indexof) s pat n rec) hNTrans hNProgTy with
    ⟨hNSameTy, hNRel⟩
  have hRunNTy :
      __smtx_typeof (__eo_to_smt runN) = SmtType.Int := by
    simpa [runN] using hNSameTy.symm.trans hNTy
  rcases EvaluateProofInternal.eo_is_neg_int_arg_numeral_of_nonstuck runN hRunNTy
      hRunNNegNe with
    ⟨i, hRunN⟩
  have hRunNEval :
      __smtx_model_eval M (__eo_to_smt runN) = SmtValue.Numeral i := by
    rw [hRunN]
    change __smtx_model_eval M (SmtTerm.Numeral i) =
      SmtValue.Numeral i
    rw [__smtx_model_eval.eq_2]
  have hNRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt n))
        (__smtx_model_eval M (__eo_to_smt runN)) := by
    simpa [runN] using hNRel
  change
    __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt pat)
          (__eo_to_smt n)) =
        __smtx_typeof (__eo_to_smt runIndex) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt pat)
            (__eo_to_smt n)))
        (__smtx_model_eval M (__eo_to_smt runIndex))
  by_cases hiNeg : i < 0
  · have hRunIndexEq :
        runIndex = Term.Numeral (-1 : native_Int) := by
      have hLt : native_zlt i 0 = true := by
        rw [show native_zlt i 0 = decide (i < 0) by rfl]
        exact decide_eq_true hiNeg
      dsimp [runIndex]
      rw [hRunN]
      simp [__eo_is_neg, __eo_ite, native_ite, native_teq, hLt]
    rw [hRunIndexEq]
    constructor
    · exact
        EvaluateProofInternal.smt_typeof_str_indexof_eq_typeof_numeral_of_arg_types
          s pat n T (-1 : native_Int) hSTySeq hPatTySeq hNTy
    · rcases EvaluateProofInternal.smt_model_eval_seq_of_type_local M hM (__eo_to_smt s) T
          hSTySeq with
        ⟨sSeq, hSEval⟩
      rcases EvaluateProofInternal.smt_model_eval_seq_of_type_local M hM (__eo_to_smt pat) T
          hPatTySeq with
        ⟨patSeq, hPatEval⟩
      have hEvalRunIndex :
          __smtx_model_eval_str_indexof
              (__smtx_model_eval M (__eo_to_smt s))
              (__smtx_model_eval M (__eo_to_smt pat))
              (__smtx_model_eval M (__eo_to_smt runN)) =
            SmtValue.Numeral (-1 : native_Int) := by
        rw [hSEval, hPatEval, hRunNEval]
        simp [__smtx_model_eval_str_indexof,
          EvaluateProofInternal.native_seq_indexof_neg_local _ _ hiNeg]
      rw [show
          __smtx_model_eval M (__eo_to_smt (Term.Numeral (-1 : native_Int))) =
            SmtValue.Numeral (-1 : native_Int) by
        exact EvaluateProofInternal.smt_model_eval_eo_to_smt_numeral_term M (-1 : native_Int)]
      exact
        EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_to_numeral_of_runs
          M s pat n s pat runN (-1 : native_Int)
          (RuleProofs.smt_value_rel_refl _)
          (RuleProofs.smt_value_rel_refl _)
          hNRelRun hEvalRunIndex
  · have hRunNNegFalse : __eo_is_neg runN = Term.Boolean false := by
      have hLt : native_zlt i 0 = false := by
        rw [show native_zlt i 0 = decide (i < 0) by rfl]
        exact decide_eq_false hiNeg
      rw [hRunN]
      simp [__eo_is_neg, hLt]
    have hbTop : bTop = false := by
      rw [hRunNNegFalse] at hRunNNegBool
      cases hRunNNegBool
      rfl
    have hRunRestNe : runRest ≠ Term.Stuck := by
      simpa [hbTop] using hTopSelected
    rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
        (__eo_gt runN runLen) (Term.Numeral (-1 : native_Int)) runInner
        hRunRestNe with
      ⟨bGt, hGtBool, hGtSelected⟩
    have hGtNe : __eo_gt runN runLen ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hGtBool
      cases hGtBool
    have hRunLenNe : runLen ≠ Term.Stuck := by
      intro hStuck
      apply hGtNe
      rw [hRunN, hStuck]
      simp [__eo_gt]
    have hRunSNe : runS ≠ Term.Stuck :=
      EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLen] using hRunLenNe)
    have hRunSOrigNe : __run_evaluate s ≠ Term.Stuck := by
      simpa [runS] using hRunSNe
    have hSProgTy : __eo_typeof (__eo_prog_evaluate s) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq s T hSTrans hSTySeq
        hRunSOrigNe
    rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg1 M
        (Term.UOp UserOp.str_indexof) s pat n rec) hSTrans hSProgTy with
      ⟨hSSameTy, hSRel⟩
    have hRunSTy :
        __smtx_typeof (__eo_to_smt runS) = SmtType.Seq T := by
      simpa [runS] using hSSameTy.symm.trans hSTySeq
    have hSRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt runS)) := by
      simpa [runS] using hSRel
    rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runS hRunSTy
        (by simpa [runLen] using hRunLenNe) with
      ⟨str, hRunS, hStrValid, hTChar⟩
    subst T
    have hRunLenEq :
        runLen = Term.Numeral (native_str_len str) := by
      dsimp [runLen]
      rw [hRunS]
      rfl
    by_cases hGt : native_str_len str < i
    · have hRunIndexEq :
          runIndex = Term.Numeral (-1 : native_Int) := by
        have hLt : native_zlt i 0 = false := by
          rw [show native_zlt i 0 = decide (i < 0) by rfl]
          exact decide_eq_false hiNeg
        have hGtLt : native_zlt (native_str_len str) i = true := by
          rw [show
              native_zlt (native_str_len str) i =
                decide (native_str_len str < i) by
            rfl]
          exact decide_eq_true hGt
        dsimp [runIndex, runRest, runLen]
        rw [hRunN, hRunS]
        simp [__eo_is_neg, __eo_gt, __eo_len, __eo_ite, native_ite,
          native_teq, hLt, hGtLt]
      rw [hRunIndexEq]
      constructor
      · exact
          EvaluateProofInternal.smt_typeof_str_indexof_eq_typeof_numeral_of_arg_types
            s pat n SmtType.Char (-1 : native_Int) (by simpa using hSTySeq)
            (by simpa using hPatTySeq) hNTy
      · have hRunSEval :
            __smtx_model_eval M (__eo_to_smt runS) =
              SmtValue.Seq (native_pack_string str) := by
          rw [hRunS]
          change __smtx_model_eval M (SmtTerm.String str) =
            SmtValue.Seq (native_pack_string str)
          rw [__smtx_model_eval.eq_4]
        rcases EvaluateProofInternal.smt_model_eval_seq_of_type_local M hM (__eo_to_smt pat)
            SmtType.Char (by simpa using hPatTySeq) with
          ⟨patSeq, hPatEval⟩
        have hSeqLen :
            Int.ofNat
                (native_unpack_seq (native_pack_string str)).length < i := by
          simpa [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local,
            native_str_len] using hGt
        have hValuesLen :
            Int.ofNat (impl_native_string_to_values str).length < i := by
          simpa [impl_native_string_to_values, native_pack_string,
            EvaluateProofInternal.native_unpack_pack_seq_local] using hSeqLen
        have hEvalRunIndex :
            __smtx_model_eval_str_indexof
                (__smtx_model_eval M (__eo_to_smt runS))
                (__smtx_model_eval M (__eo_to_smt pat))
                (__smtx_model_eval M (__eo_to_smt runN)) =
              SmtValue.Numeral (-1 : native_Int) := by
          rw [hRunSEval, hPatEval, hRunNEval]
          simp only [__smtx_model_eval_str_indexof]
          rw [show native_unpack_seq (native_pack_string str) =
              impl_native_string_to_values str by
            simp [impl_native_string_to_values, native_pack_string,
              EvaluateProofInternal.native_unpack_pack_seq_local]]
          rw [EvaluateProofInternal.native_seq_indexof_gt_len_local
            _ _ hValuesLen]
        rw [show
            __smtx_model_eval M
                (__eo_to_smt (Term.Numeral (-1 : native_Int))) =
              SmtValue.Numeral (-1 : native_Int) by
          exact EvaluateProofInternal.smt_model_eval_eo_to_smt_numeral_term M (-1 : native_Int)]
        exact
          EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_to_numeral_of_runs
            M s pat n runS pat runN (-1 : native_Int)
            hSRelRun (RuleProofs.smt_value_rel_refl _)
            hNRelRun hEvalRunIndex
    · have hGtFalse : __eo_gt runN runLen = Term.Boolean false := by
        have hGtLt : native_zlt (native_str_len str) i = false := by
          rw [show
              native_zlt (native_str_len str) i =
                decide (native_str_len str < i) by
            rfl]
          exact decide_eq_false hGt
        rw [hRunN, hRunLenEq]
        simp [__eo_gt, hGtLt]
      have hbGt : bGt = false := by
        rw [hGtFalse] at hGtBool
        cases hGtBool
        rfl
      have hRunInnerNe : runInner ≠ Term.Stuck := by
        simpa [hbGt] using hGtSelected
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          (__eo_is_neg runFind) runFind (__eo_add n runFind)
          hRunInnerNe with
        ⟨_bFind, hFindNegBool, _hFindSelected⟩
      have hFindNegNe : __eo_is_neg runFind ≠ Term.Stuck := by
        intro hStuck
        rw [hStuck] at hFindNegBool
        cases hFindNegBool
      have hRunFindNe : runFind ≠ Term.Stuck := by
        intro hStuck
        apply hFindNegNe
        rw [hStuck]
        simp [__eo_is_neg]
      have hRunPatNe : runPat ≠ Term.Stuck :=
        EvaluateProofInternal.eo_to_str_arg_ne_stuck
          (EvaluateProofInternal.eo_find_right_ne_stuck (by simpa [runFind] using hRunFindNe))
      have hRunPatOrigNe : __run_evaluate pat ≠ Term.Stuck := by
        simpa [runPat] using hRunPatNe
      have hPatProgTy :
          __eo_typeof (__eo_prog_evaluate pat) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq pat SmtType.Char
          hPatTrans (by simpa using hPatTySeq) hRunPatOrigNe
      rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg2 M
          (Term.UOp UserOp.str_indexof) s pat n rec) hPatTrans
          hPatProgTy with
        ⟨hPatSameTy, hPatRel⟩
      have hRunPatTy :
          __smtx_typeof (__eo_to_smt runPat) =
            SmtType.Seq SmtType.Char := by
        simpa [runPat] using hPatSameTy.symm.trans
          (by simpa using hPatTySeq)
      have hPatRelRun :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt pat))
            (__smtx_model_eval M (__eo_to_smt runPat)) := by
        simpa [runPat] using hPatRel
      have hExtractNe : __eo_extract runS n runLen ≠ Term.Stuck := by
        intro hStuck
        apply hRunFindNe
        dsimp [runFind]
        rw [hStuck]
        simp [__eo_to_str, __eo_find]
      rcases EvaluateProofInternal.eo_extract_seq_args_of_nonstuck runS n runLen hRunSTy
          (by simpa using hExtractNe) with
        ⟨str', start, stop, hRunS', hNShape, hRunLenShape,
          _hStrValid', _hTChar'⟩
      have hStrEq : str' = str := by
        rw [hRunS] at hRunS'
        cases hRunS'
        rfl
      subst str'
      have hStartEq : start = i := by
        dsimp [runN] at hRunN
        rw [hNShape] at hRunN
        change Term.Numeral start = Term.Numeral i at hRunN
        cases hRunN
        rfl
      have hNShapeI : n = Term.Numeral i := by
        rw [hNShape, hStartEq]
      have hStopEq : stop = native_str_len str := by
        rw [hRunLenEq] at hRunLenShape
        cases hRunLenShape
        rfl
      let suffixLen :=
        native_zplus
          (native_zplus (native_str_len str) (native_zneg i)) 1
      let suffix := native_str_substr str i suffixLen
      have hSuffixValid : native_string_valid suffix = true :=
        EvaluateProofInternal.native_string_valid_substr_local i suffixLen hStrValid
      have hExtractEq :
          __eo_extract runS n runLen = Term.String suffix := by
        dsimp [suffix, suffixLen, runLen]
        rw [hRunS, hNShapeI]
        rfl
      have hExtractTy :
          __smtx_typeof
              (__eo_to_smt (__eo_extract runS n runLen)) =
            SmtType.Seq SmtType.Char := by
        rw [hExtractEq]
        change __smtx_typeof (SmtTerm.String suffix) =
          SmtType.Seq SmtType.Char
        simp [__smtx_typeof, hSuffixValid, native_ite]
      have hRunPatTyChar :
          __smtx_typeof (__eo_to_smt runPat) =
            SmtType.Seq SmtType.Char := by
        simpa using hRunPatTy
      rcases EvaluateProofInternal.eo_find_to_str_seq_args_of_nonstuck
          (__eo_extract runS n runLen) runPat hExtractTy
          hRunPatTyChar (by simpa [runFind] using hRunFindNe) with
        ⟨_suffix, patStr, _hExtractString, hRunPat,
          _hSuffixValid, _hPatValid, _hTChar⟩
      have hRunIndexEq :
          runIndex = Term.Numeral (native_str_indexof str patStr i) := by
        dsimp [runIndex, runRest, runInner, runFind, runLen]
        rw [hRunS, hRunPat, hRunN]
        exact EvaluateProofInternal.str_indexof_result_strings_of_index_numeral
          str patStr n i hNShapeI
      rw [hRunIndexEq]
      constructor
      · exact
          EvaluateProofInternal.smt_typeof_str_indexof_eq_typeof_numeral_of_arg_types
            s pat n SmtType.Char (native_str_indexof str patStr i)
            (by simpa using hSTySeq) (by simpa using hPatTySeq) hNTy
      · have hRunSEval :
            __smtx_model_eval M (__eo_to_smt runS) =
              SmtValue.Seq (native_pack_string str) := by
          rw [hRunS]
          change __smtx_model_eval M (SmtTerm.String str) =
            SmtValue.Seq (native_pack_string str)
          rw [__smtx_model_eval.eq_4]
        have hRunPatEval :
            __smtx_model_eval M (__eo_to_smt runPat) =
              SmtValue.Seq (native_pack_string patStr) := by
          rw [hRunPat]
          change __smtx_model_eval M (SmtTerm.String patStr) =
            SmtValue.Seq (native_pack_string patStr)
          rw [__smtx_model_eval.eq_4]
        have hEvalRunIndex :
            __smtx_model_eval_str_indexof
                (__smtx_model_eval M (__eo_to_smt runS))
                (__smtx_model_eval M (__eo_to_smt runPat))
                (__smtx_model_eval M (__eo_to_smt runN)) =
              SmtValue.Numeral (native_str_indexof str patStr i) := by
          rw [hRunSEval, hRunPatEval, hRunNEval]
          exact EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string str patStr i
        rw [show
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Numeral (native_str_indexof str patStr i))) =
              SmtValue.Numeral (native_str_indexof str patStr i) by
          exact EvaluateProofInternal.smt_model_eval_eo_to_smt_numeral_term M
            (native_str_indexof str patStr i)]
        exact
          EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_to_numeral_of_runs
            M s pat n runS runPat runN
            (native_str_indexof str patStr i)
            hSRelRun hPatRelRun hNRelRun hEvalRunIndex

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_update_core
    (M : SmtModel) (hM : model_wf M)
    (s n repl : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) n)
                repl) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) n)
      repl) := by
  intro hATrans hEvalTy
  let whole :=
    Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) n)
      repl
  have hUpdateNN :
      term_has_non_none_type
        (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt repl)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation, whole] at hsimpa ⊢
    exact hsimpa
  rcases str_update_args_of_non_none hUpdateNN with
    ⟨T, hSTySeq, hNTy, hReplTySeq⟩
  have hSTrans : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSTySeq]
    simp
  have hNTrans : RuleProofs.eo_has_smt_translation n := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hNTy]
    simp
  have hReplTrans : RuleProofs.eo_has_smt_translation repl := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hReplTySeq]
    simp
  let runS := __run_evaluate s
  let runLen := __eo_len runS
  let runRepl := __run_evaluate repl
  let runN := __run_evaluate n
  let runGuard :=
    __eo_or (__eo_gt (Term.Numeral 0) runN) (__eo_gt runN runLen)
  let runBody :=
    __eo_concat
      (__eo_concat
        (__eo_extract runS (Term.Numeral 0)
          (__eo_add runN (Term.Numeral (-1 : native_Int))))
        (__eo_extract runRepl (Term.Numeral 0)
          (__eo_add (__eo_add (__eo_neg runN) runLen)
            (Term.Numeral (-1 : native_Int)))))
      (__eo_extract runS (__eo_add runN (__eo_len runRepl)) runLen)
  let runUpdate := __eo_ite runGuard runS runBody
  have hRunUpdateNe : runUpdate ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runUpdate) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunGuardNe : runGuard ≠ Term.Stuck :=
    EvaluateProofInternal.eo_ite_cond_ne_stuck (by simpa [runUpdate] using hRunUpdateNe)
  have hNegGtNe0 : __eo_gt (Term.Numeral 0) runN ≠ Term.Stuck :=
    EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runGuard] using hRunGuardNe)
  have hGtLenNe0 : __eo_gt runN runLen ≠ Term.Stuck :=
    EvaluateProofInternal.eo_or_right_ne_stuck (by simpa [runGuard] using hRunGuardNe)
  have hRunNNe : runN ≠ Term.Stuck :=
    EvaluateProofInternal.eo_gt_right_ne_stuck hNegGtNe0
  have hRunLenNe0 : runLen ≠ Term.Stuck :=
    EvaluateProofInternal.eo_gt_right_ne_stuck hGtLenNe0
  have hRunSNe : runS ≠ Term.Stuck :=
    EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLen] using hRunLenNe0)
  have hRunSOrigNe : __run_evaluate s ≠ Term.Stuck := by
    simpa [runS] using hRunSNe
  have hRunNOrigNe : __run_evaluate n ≠ Term.Stuck := by
    simpa [runN] using hRunNNe
  have hSProgTy : __eo_typeof (__eo_prog_evaluate s) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq s T hSTrans hSTySeq
      hRunSOrigNe
  have hNProgTy : __eo_typeof (__eo_prog_evaluate n) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int n hNTrans hNTy
      hRunNOrigNe
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg1 M
      (Term.UOp UserOp.str_update) s n repl rec) hSTrans hSProgTy with
    ⟨hSSameTy, hSRel⟩
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg2 M
      (Term.UOp UserOp.str_update) s n repl rec) hNTrans hNProgTy with
    ⟨hNSameTy, hNRel⟩
  have hRunSTy :
      __smtx_typeof (__eo_to_smt runS) = SmtType.Seq T := by
    simpa [runS] using hSSameTy.symm.trans hSTySeq
  have hRunNTy :
      __smtx_typeof (__eo_to_smt runN) = SmtType.Int := by
    simpa [runN] using hNSameTy.symm.trans hNTy
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck runGuard runS runBody
      hRunUpdateNe with
    ⟨bGuard, hGuardBool, hSelected⟩
  rcases EvaluateProofInternal.eo_or_bool_args_of_bool
      (__eo_gt (Term.Numeral 0) runN) (__eo_gt runN runLen)
      bGuard hGuardBool with
    ⟨bNeg, bGtLen, hNegBool, hGtLenBool, _hGuardOr⟩
  have hNegGtNe : __eo_gt (Term.Numeral 0) runN ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hNegBool
    cases hNegBool
  rcases EvaluateProofInternal.eo_gt_int_args_numeral_of_nonstuck (Term.Numeral 0) runN
      (by
        change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
        rw [__smtx_typeof.eq_2])
      hRunNTy hNegGtNe with
    ⟨zero, i, hZero, hRunN⟩
  cases hZero
  have hRunNEval :
      __smtx_model_eval M (__eo_to_smt runN) = SmtValue.Numeral i := by
    rw [hRunN]
    change __smtx_model_eval M (SmtTerm.Numeral i) =
      SmtValue.Numeral i
    rw [__smtx_model_eval.eq_2]
  have hGtLenNe : __eo_gt runN runLen ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hGtLenBool
    cases hGtLenBool
  have hRunLenNe : runLen ≠ Term.Stuck := by
    intro hStuck
    apply hGtLenNe
    rw [hRunN, hStuck]
    simp [__eo_gt]
  rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runS hRunSTy
      (by simpa [runLen] using hRunLenNe) with
    ⟨str, hRunS, hStrValid, hTChar⟩
  subst T
  have hRunLenEq :
      runLen = Term.Numeral (native_str_len str) := by
    dsimp [runLen]
    rw [hRunS]
    rfl
  have hRunSEval :
      __smtx_model_eval M (__eo_to_smt runS) =
        SmtValue.Seq (native_pack_string str) := by
    rw [hRunS]
    change __smtx_model_eval M (SmtTerm.String str) =
      SmtValue.Seq (native_pack_string str)
    rw [__smtx_model_eval.eq_4]
  have hSRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt runS)) := by
    simpa [runS] using hSRel
  have hNRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt n))
        (__smtx_model_eval M (__eo_to_smt runN)) := by
    simpa [runN] using hNRel
  change
    __smtx_typeof
        (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt repl)) =
        __smtx_typeof (__eo_to_smt runUpdate) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt repl)))
        (__smtx_model_eval M (__eo_to_smt runUpdate))
  by_cases hiNeg : i < 0
  · have hRunUpdateEq : runUpdate = Term.String str := by
      have hLt : native_zlt i 0 = true := by
        rw [show native_zlt i 0 = decide (i < 0) by rfl]
        exact decide_eq_true hiNeg
      dsimp [runUpdate, runGuard, runBody, runLen]
      rw [hRunN, hRunS]
      simp [__eo_len, __eo_gt, __eo_or, __eo_ite, native_ite,
        native_teq, native_or, hLt]
    rw [hRunUpdateEq]
    constructor
    · exact
        EvaluateProofInternal.smt_typeof_str_update_eq_typeof_string_of_arg_types
          s n repl str (by simpa using hSTySeq) hNTy
          (by simpa using hReplTySeq) hStrValid
    · rcases EvaluateProofInternal.smt_model_eval_seq_of_type_local M hM (__eo_to_smt repl)
          SmtType.Char (by simpa using hReplTySeq) with
        ⟨replSeq, hReplEval⟩
      have hEvalRunUpdate :
          __smtx_model_eval_str_update
              (__smtx_model_eval M (__eo_to_smt runS))
              (__smtx_model_eval M (__eo_to_smt runN))
              (__smtx_model_eval M (__eo_to_smt repl)) =
            SmtValue.Seq (native_pack_string str) := by
        rw [hRunSEval, hRunNEval, hReplEval]
        change
          SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value
                  (native_pack_string str))
                (native_seq_update
                  (native_unpack_seq (native_pack_string str)) i
                  (native_unpack_seq replSeq))) =
            SmtValue.Seq (native_pack_string str)
        rw [EvaluateProofInternal.native_seq_update_eq_self_of_neg _ _ _ hiNeg]
        simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local,
          EvaluateProofInternal.elem_typeof_pack_seq_local]
      rw [show
          __smtx_model_eval M (__eo_to_smt (Term.String str)) =
            SmtValue.Seq (native_pack_string str) by
        change __smtx_model_eval M (SmtTerm.String str) =
          SmtValue.Seq (native_pack_string str)
        rw [__smtx_model_eval.eq_4]]
      exact
        EvaluateProofInternal.smt_value_rel_model_eval_str_update_to_string_of_runs
          M s n repl runS runN repl str
          hSRelRun hNRelRun (RuleProofs.smt_value_rel_refl _)
          hEvalRunUpdate
  · by_cases hLenLt : native_str_len str < i
    · have hRunUpdateEq : runUpdate = Term.String str := by
        have hLt : native_zlt i 0 = false := by
          rw [show native_zlt i 0 = decide (i < 0) by rfl]
          exact decide_eq_false hiNeg
        have hGtLt : native_zlt (native_str_len str) i = true := by
          rw [show native_zlt (native_str_len str) i =
              decide (native_str_len str < i) by rfl]
          exact decide_eq_true hLenLt
        dsimp [runUpdate, runGuard, runBody, runLen]
        rw [hRunN, hRunS]
        simp [__eo_len, __eo_gt, __eo_or, __eo_ite, native_ite,
          native_teq, native_or, hLt, hGtLt]
      rw [hRunUpdateEq]
      constructor
      · exact
          EvaluateProofInternal.smt_typeof_str_update_eq_typeof_string_of_arg_types
            s n repl str (by simpa using hSTySeq) hNTy
            (by simpa using hReplTySeq) hStrValid
      · rcases EvaluateProofInternal.smt_model_eval_seq_of_type_local M hM
            (__eo_to_smt repl) SmtType.Char (by simpa using hReplTySeq) with
          ⟨replSeq, hReplEval⟩
        have hLenLe : Int.ofNat str.length ≤ i := by
          rw [native_str_len] at hLenLt
          exact Int.le_of_lt hLenLt
        have hEvalRunUpdate :
            __smtx_model_eval_str_update
                (__smtx_model_eval M (__eo_to_smt runS))
                (__smtx_model_eval M (__eo_to_smt runN))
                (__smtx_model_eval M (__eo_to_smt repl)) =
              SmtValue.Seq (native_pack_string str) := by
          rw [hRunSEval, hRunNEval, hReplEval]
          change
            SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value
                    (native_pack_string str))
                  (native_seq_update
                    (native_unpack_seq (native_pack_string str)) i
                    (native_unpack_seq replSeq))) =
              SmtValue.Seq (native_pack_string str)
          have hUnpackLen :
              Int.ofNat (native_unpack_seq (native_pack_string str)).length <=
                i := by
            simpa [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local,
              List.length_map] using hLenLe
          rw [EvaluateProofInternal.native_seq_update_eq_self_of_len_le _ _ _ hUnpackLen]
          simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local,
            EvaluateProofInternal.elem_typeof_pack_seq_local]
        rw [show
            __smtx_model_eval M (__eo_to_smt (Term.String str)) =
              SmtValue.Seq (native_pack_string str) by
          change __smtx_model_eval M (SmtTerm.String str) =
            SmtValue.Seq (native_pack_string str)
          rw [__smtx_model_eval.eq_4]]
        exact
          EvaluateProofInternal.smt_value_rel_model_eval_str_update_to_string_of_runs
            M s n repl runS runN repl str
            hSRelRun hNRelRun (RuleProofs.smt_value_rel_refl _)
            hEvalRunUpdate
    · have hNegFalse :
          __eo_gt (Term.Numeral 0) runN = Term.Boolean false := by
        have hLt : native_zlt i 0 = false := by
          rw [show native_zlt i 0 = decide (i < 0) by rfl]
          exact decide_eq_false hiNeg
        rw [hRunN]
        simp [__eo_gt, hLt]
      have hLenGtFalse :
          __eo_gt runN runLen = Term.Boolean false := by
        have hGtLt : native_zlt (native_str_len str) i = false := by
          rw [show native_zlt (native_str_len str) i =
              decide (native_str_len str < i) by rfl]
          exact decide_eq_false hLenLt
        rw [hRunN, hRunLenEq]
        simp [__eo_gt, hGtLt]
      have hGuardFalse : runGuard = Term.Boolean false := by
        dsimp [runGuard]
        rw [hNegFalse, hLenGtFalse]
        simp [__eo_or, native_or]
      have hbGuard : bGuard = false := by
        rw [hGuardFalse] at hGuardBool
        cases hGuardBool
        rfl
      have hBodyNe : runBody ≠ Term.Stuck := by
        simpa [hbGuard] using hSelected
      have hRunReplNe : runRepl ≠ Term.Stuck := by
        have hOuterLeftNe :
            __eo_concat
                (__eo_concat
                  (__eo_extract runS (Term.Numeral 0)
                    (__eo_add runN (Term.Numeral (-1 : native_Int))))
                  (__eo_extract runRepl (Term.Numeral 0)
                    (__eo_add (__eo_add (__eo_neg runN) runLen)
                      (Term.Numeral (-1 : native_Int)))))
                (__eo_extract runS (__eo_add runN (__eo_len runRepl))
                  runLen) ≠ Term.Stuck := by
          simpa [runBody] using hBodyNe
        have hInnerNe :=
          EvaluateProofInternal.eo_concat_left_ne_stuck hOuterLeftNe
        have hReplExtractNe :=
          EvaluateProofInternal.eo_concat_right_ne_stuck hInnerNe
        exact EvaluateProofInternal.eo_extract_target_ne_stuck hReplExtractNe
      have hRunReplOrigNe : __run_evaluate repl ≠ Term.Stuck := by
        simpa [runRepl] using hRunReplNe
      have hReplProgTy :
          __eo_typeof (__eo_prog_evaluate repl) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq repl SmtType.Char
          hReplTrans (by simpa using hReplTySeq) hRunReplOrigNe
      rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3 M
          (Term.UOp UserOp.str_update) s n repl rec) hReplTrans
          hReplProgTy with
        ⟨hReplSameTy, hReplRel⟩
      have hRunReplTyChar :
          __smtx_typeof (__eo_to_smt runRepl) =
            SmtType.Seq SmtType.Char := by
        simpa [runRepl] using hReplSameTy.symm.trans
          (by simpa using hReplTySeq)
      have hReplRelRun :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt repl))
            (__smtx_model_eval M (__eo_to_smt runRepl)) := by
        simpa [runRepl] using hReplRel
      rcases EvaluateProofInternal.str_update_run_repl_string_of_body_nonstuck str runRepl i
          hRunReplTyChar
          (by
            simpa [runBody, runLen, hRunS, hRunN, __eo_len] using hBodyNe) with
        ⟨replStr, hRunRepl, hReplValid⟩
      have hRunReplEval :
          __smtx_model_eval M (__eo_to_smt runRepl) =
            SmtValue.Seq (native_pack_string replStr) := by
        rw [hRunRepl]
        change __smtx_model_eval M (SmtTerm.String replStr) =
          SmtValue.Seq (native_pack_string replStr)
        rw [__smtx_model_eval.eq_4]
      have hRunUpdateEq :
          runUpdate =
            Term.String (EvaluateProofInternal.native_seq_update_string_result str i replStr) := by
        dsimp [runUpdate, runGuard, runBody, runLen]
        rw [hRunS, hRunN, hRunRepl]
        exact EvaluateProofInternal.str_update_result_strings str replStr i
      rw [hRunUpdateEq]
      constructor
      · have hResultValid :
            native_string_valid
                (EvaluateProofInternal.native_seq_update_string_result str i replStr) = true :=
          EvaluateProofInternal.native_string_valid_seq_update_string_result str replStr i
            hStrValid hReplValid
        exact
          EvaluateProofInternal.smt_typeof_str_update_eq_typeof_string_of_arg_types
            s n repl
            (EvaluateProofInternal.native_seq_update_string_result str i replStr)
            (by simpa using hSTySeq) hNTy
            (by simpa using hReplTySeq) hResultValid
      · have hEvalRunUpdate :
            __smtx_model_eval_str_update
                (__smtx_model_eval M (__eo_to_smt runS))
                (__smtx_model_eval M (__eo_to_smt runN))
                (__smtx_model_eval M (__eo_to_smt runRepl)) =
              SmtValue.Seq
                (native_pack_string
                  (EvaluateProofInternal.native_seq_update_string_result str i replStr)) := by
          rw [hRunSEval, hRunNEval, hRunReplEval]
          exact EvaluateProofInternal.smtx_model_eval_str_update_pack_string str replStr i
        rw [show
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.String
                    (EvaluateProofInternal.native_seq_update_string_result str i replStr))) =
              SmtValue.Seq
                (native_pack_string
                  (EvaluateProofInternal.native_seq_update_string_result str i replStr)) by
          change
            __smtx_model_eval M
                (SmtTerm.String
                  (EvaluateProofInternal.native_seq_update_string_result str i replStr)) =
              SmtValue.Seq
                (native_pack_string
                  (EvaluateProofInternal.native_seq_update_string_result str i replStr))
          rw [__smtx_model_eval.eq_4]]
        exact
          EvaluateProofInternal.smt_value_rel_model_eval_str_update_to_string_of_runs
            M s n repl runS runN runRepl
            (EvaluateProofInternal.native_seq_update_string_result str i replStr)
            hSRelRun hNRelRun hReplRelRun hEvalRunUpdate

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_leq_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) a) b) := by
  intro hATrans hEvalTy
  have hLeqNN :
      term_has_non_none_type
        (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_char_binop_args_of_non_none (op := SmtTerm.str_leq)
      (typeof_str_leq_eq (__eo_to_smt a) (__eo_to_smt b))
      hLeqNN with
    ⟨hATyChar, hBTyChar⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATyChar]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  let runA := __run_evaluate a
  let runB := __run_evaluate b
  let runLeq :=
    __eo_ite (__eo_and (__eo_is_str runA) (__eo_is_str runB))
      (__str_leq_eval_rec (__str_flatten (__str_nary_intro runA))
        (__str_flatten (__str_nary_intro runB)))
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) runA)
        runB)
  have hRunLeqNe : runLeq ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) a) b))
            runLeq) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunANe : runA ≠ Term.Stuck := by
    intro hStuck
    apply hRunLeqNe
    dsimp [runLeq]
    rw [hStuck]
    cases runB <;>
      simp [__eo_is_str, __eo_is_str_internal, __eo_and, __eo_ite,
        __eo_mk_apply, native_and, native_not, native_ite, native_teq]
  have hRunBNe : runB ≠ Term.Stuck := by
    intro hStuck
    apply hRunLeqNe
    dsimp [runLeq]
    rw [hStuck]
    cases runA <;>
      simp [__eo_is_str, __eo_is_str_internal, __eo_and, __eo_ite,
        __eo_mk_apply, native_and, native_not, native_ite, native_teq]
  have hRunAOrigNe : __run_evaluate a ≠ Term.Stuck := by
    simpa [runA] using hRunANe
  have hRunBOrigNe : __run_evaluate b ≠ Term.Stuck := by
    simpa [runB] using hRunBNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq a SmtType.Char
      hATransA hATyChar hRunAOrigNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b SmtType.Char
      hBTrans hBTyChar hRunBOrigNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.str_leq) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.str_leq) a) b rec
      hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunATy :
      __smtx_typeof (__eo_to_smt runA) =
        SmtType.Seq SmtType.Char := by
    simpa [runA] using hASameTy.symm.trans hATyChar
  have hRunBTy :
      __smtx_typeof (__eo_to_smt runB) =
        SmtType.Seq SmtType.Char := by
    simpa [runB] using hBSameTy.symm.trans hBTyChar
  have hARelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt runA)) := by
    simpa [runA] using hARel
  have hBRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runB)) := by
    simpa [runB] using hBRel
  change
    __smtx_typeof (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runLeq) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runLeq))
  by_cases hStrings :
      ∃ sx sy : native_String,
        runA = Term.String sx ∧ runB = Term.String sy
  · rcases hStrings with ⟨sx, sy, hRunA, hRunB⟩
    have hRunStringATy :
        __smtx_typeof (__eo_to_smt (Term.String sx)) =
          SmtType.Seq SmtType.Char := by
      rw [← hRunA]
      exact hRunATy
    have hRunStringBTy :
        __smtx_typeof (__eo_to_smt (Term.String sy)) =
          SmtType.Seq SmtType.Char := by
      rw [← hRunB]
      exact hRunBTy
    have hSxValid : native_string_valid sx = true :=
      EvaluateProofInternal.native_string_valid_of_string_type hRunStringATy
    have hSyValid : native_string_valid sy = true :=
      EvaluateProofInternal.native_string_valid_of_string_type hRunStringBTy
    let leqBool := native_or (decide (sx = sy)) (native_str_lt sx sy)
    have hRunLeqEq :
        runLeq = Term.Boolean leqBool := by
      dsimp [runLeq, leqBool]
      rw [hRunA, hRunB]
      exact EvaluateProofInternal.str_leq_result_strings hSxValid hSyValid
    rw [hRunLeqEq]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Boolean leqBool)
      rw [typeof_str_leq_eq]
      simp [__smtx_typeof, hATyChar, hBTyChar, native_Teq,
        native_ite]
    · have hSxEval :
          __smtx_model_eval M (__eo_to_smt (Term.String sx)) =
            SmtValue.Seq (native_pack_string sx) := by
        rw [show __eo_to_smt (Term.String sx) = SmtTerm.String sx by rfl]
        rw [__smtx_model_eval.eq_4]
      have hSyEval :
          __smtx_model_eval M (__eo_to_smt (Term.String sy)) =
            SmtValue.Seq (native_pack_string sy) := by
        rw [show __eo_to_smt (Term.String sy) = SmtTerm.String sy by rfl]
        rw [__smtx_model_eval.eq_4]
      have hARelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt (Term.String sx))) := by
        simpa [hRunA] using hARelRun
      have hBRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String sy))) := by
        simpa [hRunB] using hBRelRun
      have hARelSeq :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Seq (native_pack_string sx)) := by
        simpa [hSxEval] using hARelString
      have hBRelSeq :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Seq (native_pack_string sy)) := by
        simpa [hSyEval] using hBRelString
      rcases EvaluateProofInternal.smt_value_rel_seq_right_local hARelSeq with
        ⟨sxEval, hAEval, hASeqRel⟩
      rcases EvaluateProofInternal.smt_value_rel_seq_right_local hBRelSeq with
        ⟨syEval, hBEval, hBSeqRel⟩
      have hASeqEq :
          sxEval = native_pack_string sx :=
        (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
      have hBSeqEq :
          syEval = native_pack_string sy :=
        (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
      unfold RuleProofs.smt_value_rel
      rw [show
          __smtx_model_eval M
              (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_str_leq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        simp [__smtx_model_eval]]
      rw [hAEval, hBEval, hASeqEq, hBSeqEq]
      rw [show
          __smtx_model_eval M (__eo_to_smt (Term.Boolean leqBool)) =
            SmtValue.Boolean leqBool by
        rw [show __eo_to_smt (Term.Boolean leqBool) =
          SmtTerm.Boolean leqBool by
          rfl]
        rw [__smtx_model_eval.eq_1]]
      dsimp [leqBool]
      rw [EvaluateProofInternal.smtx_model_eval_str_leq_pack_string sx sy]
      exact RuleProofs.smtx_model_eval_eq_refl _
  · have hRunLeqEq :
        runLeq =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) runA) runB := by
      dsimp [runLeq]
      exact EvaluateProofInternal.str_leq_result_non_strings hStrings hRunANe hRunBNe
    rw [hRunLeqEq]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_leq (__eo_to_smt runA)
            (__eo_to_smt runB))
      rw [typeof_str_leq_eq, typeof_str_leq_eq]
      simp [hATyChar, hBTyChar, hRunATy, hRunBTy, native_Teq,
        native_ite]
    · have hRelLeq :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_leq_of_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runA))
          (__smtx_model_eval M (__eo_to_smt runB))
          hARelRun hBRelRun
      have hEvalLeqAB :
          __smtx_model_eval M
              (SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_str_leq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) := by
        simp [__smtx_model_eval]
      have hEvalLeqRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_leq) runA) runB)) =
            __smtx_model_eval_str_leq
              (__smtx_model_eval M (__eo_to_smt runA))
              (__smtx_model_eval M (__eo_to_smt runB)) := by
        change
          __smtx_model_eval M
              (SmtTerm.str_leq (__eo_to_smt runA) (__eo_to_smt runB)) =
            __smtx_model_eval_str_leq
              (__smtx_model_eval M (__eo_to_smt runA))
              (__smtx_model_eval M (__eo_to_smt runB))
        simp [__smtx_model_eval]
      rw [hEvalLeqAB, hEvalLeqRun]
      exact hRelLeq

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_replace_core
    (M : SmtModel) (hM : model_wf M)
    (s pat repl : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) pat)
                repl) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) pat)
      repl) := by
  intro hATrans hEvalTy
  let whole :=
    Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) pat)
      repl
  have hReplaceNN :
      term_has_non_none_type
        (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
          (__eo_to_smt repl)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation, whole] at hsimpa ⊢
    exact hsimpa
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
      (typeof_str_replace_eq (__eo_to_smt s) (__eo_to_smt pat)
        (__eo_to_smt repl)) hReplaceNN with
    ⟨T, hSTySeq, hPatTySeq, hReplTySeq⟩
  have hSTrans : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSTySeq]
    simp
  have hPatTrans : RuleProofs.eo_has_smt_translation pat := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hPatTySeq]
    simp
  have hReplTrans : RuleProofs.eo_has_smt_translation repl := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hReplTySeq]
    simp
  let runS := __run_evaluate s
  let runPat := __run_evaluate pat
  let runRepl := __run_evaluate repl
  let runIdx := __eo_find (__eo_to_str runS) (__eo_to_str runPat)
  let runBody :=
      (__eo_concat
        (__eo_concat
          (__eo_extract runS (Term.Numeral 0)
            (__eo_add runIdx (Term.Numeral (-1 : native_Int))))
          runRepl)
        (__eo_extract runS (__eo_add runIdx (__eo_len runPat))
          (__eo_len runS)))
  let runReplace :=
    __eo_ite (__eo_is_neg runIdx) runS runBody
  have hRunReplaceNe : runReplace ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runReplace) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg runIdx) runS runBody hRunReplaceNe with
    ⟨bIdx, hIdxBool, hIdxSelected⟩
  have hIdxCondNe : __eo_is_neg runIdx ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hIdxBool
    cases hIdxBool
  have hRunIdxNe : runIdx ≠ Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hIdxCondNe
  have hRunSNe : runS ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_str_arg_ne_stuck
      (EvaluateProofInternal.eo_find_left_ne_stuck (by simpa [runIdx] using hRunIdxNe))
  have hRunPatNe : runPat ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_str_arg_ne_stuck
      (EvaluateProofInternal.eo_find_right_ne_stuck (by simpa [runIdx] using hRunIdxNe))
  have hRunSOrigNe : __run_evaluate s ≠ Term.Stuck := by
    simpa [runS] using hRunSNe
  have hRunPatOrigNe : __run_evaluate pat ≠ Term.Stuck := by
    simpa [runPat] using hRunPatNe
  have hSProgTy : __eo_typeof (__eo_prog_evaluate s) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq s T hSTrans hSTySeq
      hRunSOrigNe
  have hPatProgTy : __eo_typeof (__eo_prog_evaluate pat) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq pat T hPatTrans hPatTySeq
      hRunPatOrigNe
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg1 M
      (Term.UOp UserOp.str_replace) s pat repl rec) hSTrans hSProgTy with
    ⟨hSSameTy, hSRel⟩
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg2 M
      (Term.UOp UserOp.str_replace) s pat repl rec) hPatTrans hPatProgTy with
    ⟨hPatSameTy, hPatRel⟩
  have hRunSTy :
      __smtx_typeof (__eo_to_smt runS) = SmtType.Seq T := by
    simpa [runS] using hSSameTy.symm.trans hSTySeq
  have hRunPatTy :
      __smtx_typeof (__eo_to_smt runPat) = SmtType.Seq T := by
    simpa [runPat] using hPatSameTy.symm.trans hPatTySeq
  rcases EvaluateProofInternal.eo_find_to_str_seq_args_of_nonstuck runS runPat hRunSTy
      hRunPatTy (by simpa [runIdx] using hRunIdxNe) with
    ⟨str, patStr, hRunS, hRunPat, hStrValid, hPatValid, hTChar⟩
  subst T
  have hSRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt runS)) := by
    simpa [runS] using hSRel
  have hPatRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt pat))
        (__smtx_model_eval M (__eo_to_smt runPat)) := by
    simpa [runPat] using hPatRel
  change
    __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
          (__eo_to_smt repl)) =
        __smtx_typeof (__eo_to_smt runReplace) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
            (__eo_to_smt repl)))
        (__smtx_model_eval M (__eo_to_smt runReplace))
  by_cases hIdxNeg : native_str_indexof str patStr 0 < 0
  · have hRunReplaceEq : runReplace = Term.String str := by
      dsimp [runReplace, runIdx]
      rw [hRunS, hRunPat]
      have hLt : native_zlt (native_str_indexof str patStr 0) 0 = true := by
        rw [show native_zlt (native_str_indexof str patStr 0) 0 =
          decide (native_str_indexof str patStr 0 < 0) by rfl]
        exact decide_eq_true hIdxNeg
      simp [__eo_find, __eo_to_str, __eo_is_neg, __eo_ite, native_ite,
        native_teq, hLt]
    rw [hRunReplaceEq]
    constructor
    · change
        __smtx_typeof
            (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
              (__eo_to_smt repl)) =
          __smtx_typeof (SmtTerm.String str)
      rw [typeof_str_replace_eq]
      simp [__smtx_typeof, __smtx_typeof_seq_op_3, hSTySeq, hPatTySeq,
        hReplTySeq, native_Teq, native_ite, hStrValid]
    · have hRelReplace :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_replace_of_rel
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt pat))
          (__smtx_model_eval M (__eo_to_smt repl))
          (__smtx_model_eval M (__eo_to_smt runS))
          (__smtx_model_eval M (__eo_to_smt runPat))
          (__smtx_model_eval M (__eo_to_smt repl))
          hSRelRun hPatRelRun (RuleProofs.smt_value_rel_refl _)
      have hRunSEval :
          __smtx_model_eval M (__eo_to_smt runS) =
            SmtValue.Seq (native_pack_string str) := by
        rw [hRunS]
        change __smtx_model_eval M (SmtTerm.String str) =
          SmtValue.Seq (native_pack_string str)
        rw [__smtx_model_eval.eq_4]
      have hRunPatEval :
          __smtx_model_eval M (__eo_to_smt runPat) =
            SmtValue.Seq (native_pack_string patStr) := by
        rw [hRunPat]
        change __smtx_model_eval M (SmtTerm.String patStr) =
          SmtValue.Seq (native_pack_string patStr)
        rw [__smtx_model_eval.eq_4]
      rcases EvaluateProofInternal.smt_model_eval_seq_of_type_local M hM (__eo_to_smt repl)
          SmtType.Char (by simpa using hReplTySeq) with
        ⟨replSeq, hReplEval⟩
      have hEvalRunReplace :
          __smtx_model_eval_str_replace
              (__smtx_model_eval M (__eo_to_smt runS))
              (__smtx_model_eval M (__eo_to_smt runPat))
              (__smtx_model_eval M (__eo_to_smt repl)) =
            __smtx_model_eval M (__eo_to_smt (Term.String str)) := by
        rw [hRunSEval, hRunPatEval, hReplEval]
        change
          __smtx_model_eval_str_replace
              (SmtValue.Seq (native_pack_string str))
              (SmtValue.Seq (native_pack_string patStr))
              (SmtValue.Seq replSeq) =
            __smtx_model_eval M (SmtTerm.String str)
        rw [__smtx_model_eval.eq_4]
        cases patStr with
        | nil =>
            simp [native_str_indexof, impl_native_str_indexof_rec,
              native_string_prefix_eq, native_str_len] at hIdxNeg
        | cons p ps =>
            simp only [__smtx_model_eval_str_replace]
            rw [show
                __smtx_elem_typeof_seq_value (native_pack_string str) =
                  SmtType.Char by
              simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
            rw [show native_unpack_seq (native_pack_string str) =
                str.map SmtValue.Char by
              simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
            rw [show native_unpack_seq (native_pack_string (p :: ps)) =
                (p :: ps).map SmtValue.Char by
              simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
            rw [StrEqReplSupport.native_seq_replace_eq_indexof]
            rw [EvaluateProofInternal.native_seq_indexof_map_char_zero str (p :: ps)]
            simp [hIdxNeg, native_pack_string]
      have hEvalReplace :
          __smtx_model_eval M
              (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
                (__eo_to_smt repl)) =
            __smtx_model_eval_str_replace
              (__smtx_model_eval M (__eo_to_smt s))
              (__smtx_model_eval M (__eo_to_smt pat))
              (__smtx_model_eval M (__eo_to_smt repl)) := by
        simp [__smtx_model_eval]
      rw [hEvalReplace]
      rw [hEvalRunReplace] at hRelReplace
      exact hRelReplace
  · rcases EvaluateProofInternal.str_replace_run_repl_string_of_nonneg str patStr runRepl
        (by
          have hIdxCondFalse :
              __eo_is_neg runIdx = Term.Boolean false := by
            dsimp [runIdx]
            rw [hRunS, hRunPat]
            have hLt :
                native_zlt (native_str_indexof str patStr 0) 0 = false := by
              rw [show native_zlt (native_str_indexof str patStr 0) 0 =
                decide (native_str_indexof str patStr 0 < 0) by rfl]
              exact decide_eq_false hIdxNeg
            simp [__eo_find, __eo_to_str, __eo_is_neg, hLt]
          have hbIdx : bIdx = false := by
            rw [hIdxCondFalse] at hIdxBool
            cases hIdxBool
            rfl
          have hBodyNe : runBody ≠ Term.Stuck := by
            simpa [hbIdx] using hIdxSelected
          have hRunReplNe : runRepl ≠ Term.Stuck := by
            have hOuterLeftNe :
                __eo_concat
                    (__eo_concat
                      (__eo_extract runS (Term.Numeral 0)
                        (__eo_add runIdx (Term.Numeral (-1 : native_Int))))
                      runRepl)
                    (__eo_extract runS
                      (__eo_add runIdx (__eo_len runPat))
                      (__eo_len runS)) ≠ Term.Stuck := by
              simpa [runBody] using hBodyNe
            exact EvaluateProofInternal.eo_concat_right_ne_stuck
              (EvaluateProofInternal.eo_concat_left_ne_stuck hOuterLeftNe)
          have hRunReplOrigNe : __run_evaluate repl ≠ Term.Stuck := by
            simpa [runRepl] using hRunReplNe
          have hReplProgTy :
              __eo_typeof (__eo_prog_evaluate repl) = Term.Bool :=
            EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq repl
              SmtType.Char hReplTrans (by simpa using hReplTySeq)
              hRunReplOrigNe
          rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3 M
              (Term.UOp UserOp.str_replace) s pat repl rec) hReplTrans
              hReplProgTy with
            ⟨hReplSameTy, _hReplRel⟩
          have hRunReplTyChar :
              __smtx_typeof (__eo_to_smt runRepl) =
                SmtType.Seq SmtType.Char := by
            simpa [runRepl] using hReplSameTy.symm.trans
              (by simpa using hReplTySeq)
          exact hRunReplTyChar)
        hIdxNeg (by
          dsimp [runReplace, runBody, runIdx] at hRunReplaceNe
          rw [hRunS, hRunPat] at hRunReplaceNe
          simpa [__eo_find, __eo_to_str] using hRunReplaceNe) with
      ⟨replStr, hRunRepl, hReplValid⟩
    have hRunReplOrigNe : __run_evaluate repl ≠ Term.Stuck := by
      intro hStuck
      have hRunReplStuck : runRepl = Term.Stuck := by
        simpa [runRepl] using hStuck
      rw [hRunRepl] at hRunReplStuck
      cases hRunReplStuck
    have hReplProgTy :
        __eo_typeof (__eo_prog_evaluate repl) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq repl SmtType.Char
        hReplTrans (by simpa using hReplTySeq) hRunReplOrigNe
    rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3 M
        (Term.UOp UserOp.str_replace) s pat repl rec) hReplTrans
        hReplProgTy with
      ⟨hReplSameTy, hReplRel⟩
    have hRunReplTyChar :
        __smtx_typeof (__eo_to_smt runRepl) =
          SmtType.Seq SmtType.Char := by
      simpa [runRepl] using hReplSameTy.symm.trans
        (by simpa using hReplTySeq)
    have hReplRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt repl))
          (__smtx_model_eval M (__eo_to_smt runRepl)) := by
      simpa [runRepl] using hReplRel
    have hRunReplaceEq :
        runReplace =
          Term.String
            (EvaluateProofInternal.native_str_replace_eval_result str patStr replStr) := by
      dsimp [runReplace, runBody, runIdx]
      rw [hRunS, hRunPat, hRunRepl]
      exact EvaluateProofInternal.str_replace_result_strings str patStr replStr
    rw [hRunReplaceEq]
    constructor
    · change
        __smtx_typeof
            (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
              (__eo_to_smt repl)) =
          __smtx_typeof
            (SmtTerm.String
              (EvaluateProofInternal.native_str_replace_eval_result str patStr replStr))
      rw [typeof_str_replace_eq]
      have hResultValid :
          native_string_valid
              (EvaluateProofInternal.native_str_replace_eval_result str patStr replStr) = true := by
        unfold EvaluateProofInternal.native_str_replace_eval_result
        by_cases hNeg : native_str_indexof str patStr 0 < 0
        · simp [hNeg, hStrValid]
        · simp [hNeg]
          exact native_string_valid_append
            (native_string_valid_take
              (Int.toNat (native_str_indexof str patStr 0)) hStrValid)
            (native_string_valid_append
              hReplValid
            (native_string_valid_drop
              (Int.toNat (native_str_indexof str patStr 0) +
                patStr.length) hStrValid))
      simp [__smtx_typeof, __smtx_typeof_seq_op_3, hSTySeq, hPatTySeq,
        hReplTySeq, native_Teq, native_ite, hResultValid]
    · have hRelReplace :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_replace_of_rel
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt pat))
          (__smtx_model_eval M (__eo_to_smt repl))
          (__smtx_model_eval M (__eo_to_smt runS))
          (__smtx_model_eval M (__eo_to_smt runPat))
          (__smtx_model_eval M (__eo_to_smt runRepl))
          hSRelRun hPatRelRun hReplRelRun
      have hRunSEval :
          __smtx_model_eval M (__eo_to_smt runS) =
            SmtValue.Seq (native_pack_string str) := by
        rw [hRunS]
        change __smtx_model_eval M (SmtTerm.String str) =
          SmtValue.Seq (native_pack_string str)
        rw [__smtx_model_eval.eq_4]
      have hRunPatEval :
          __smtx_model_eval M (__eo_to_smt runPat) =
            SmtValue.Seq (native_pack_string patStr) := by
        rw [hRunPat]
        change __smtx_model_eval M (SmtTerm.String patStr) =
          SmtValue.Seq (native_pack_string patStr)
        rw [__smtx_model_eval.eq_4]
      have hRunReplEval :
          __smtx_model_eval M (__eo_to_smt runRepl) =
            SmtValue.Seq (native_pack_string replStr) := by
        rw [hRunRepl]
        change __smtx_model_eval M (SmtTerm.String replStr) =
          SmtValue.Seq (native_pack_string replStr)
        rw [__smtx_model_eval.eq_4]
      have hEvalRunReplace :
          __smtx_model_eval_str_replace
              (__smtx_model_eval M (__eo_to_smt runS))
              (__smtx_model_eval M (__eo_to_smt runPat))
              (__smtx_model_eval M (__eo_to_smt runRepl)) =
            __smtx_model_eval M
              (__eo_to_smt
                (Term.String
                  (EvaluateProofInternal.native_str_replace_eval_result str patStr replStr))) := by
        rw [hRunSEval, hRunPatEval, hRunReplEval]
        change
          __smtx_model_eval_str_replace
              (SmtValue.Seq (native_pack_string str))
              (SmtValue.Seq (native_pack_string patStr))
              (SmtValue.Seq (native_pack_string replStr)) =
            __smtx_model_eval M
              (SmtTerm.String
                (EvaluateProofInternal.native_str_replace_eval_result str patStr replStr))
        rw [__smtx_model_eval.eq_4]
        simp only [__smtx_model_eval_str_replace]
        rw [show
            __smtx_elem_typeof_seq_value (native_pack_string str) =
              SmtType.Char by
          simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
        rw [EvaluateProofInternal.native_seq_replace_pack_string str patStr replStr]
      have hEvalReplace :
          __smtx_model_eval M
              (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
                (__eo_to_smt repl)) =
            __smtx_model_eval_str_replace
              (__smtx_model_eval M (__eo_to_smt s))
              (__smtx_model_eval M (__eo_to_smt pat))
              (__smtx_model_eval M (__eo_to_smt repl)) := by
        simp [__smtx_model_eval]
      rw [hEvalReplace]
      rw [hEvalRunReplace] at hRelReplace
      exact hRelReplace

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_replace_all_core
    (M : SmtModel) (_hM : model_wf M)
    (s pat repl : Term)
    (_rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_replace_all) s) pat)
                repl) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  __run_evaluate
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) pat)
        repl) ≠
    Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) pat)
      repl ->
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) pat)
      repl) := by
  intro hActive hATrans _hEvalTy
  let whole :=
    Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) pat)
      repl
  change __run_evaluate whole ≠ whole at hActive
  change
    __smtx_typeof (__eo_to_smt whole) =
        __smtx_typeof (__eo_to_smt (__run_evaluate whole)) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt whole))
        (__smtx_model_eval M (__eo_to_smt (__run_evaluate whole)))
  cases s <;>
    simp [__run_evaluate, whole, __eo_is_str, __eo_is_str_internal,
      __eo_and, __eo_ite, native_and, native_ite, native_teq, native_not]
        at hActive
  rename_i str
  cases pat <;>
    simp [__run_evaluate, whole, __eo_is_str, __eo_is_str_internal,
      __eo_and, __eo_ite, native_and, native_ite, native_teq, native_not]
        at hActive
  rename_i patStr
  cases repl <;>
    simp [__run_evaluate, whole, __eo_is_str, __eo_is_str_internal,
      __eo_and, __eo_ite, native_and, native_ite, native_teq, native_not]
        at hActive
  rename_i replStr
  have hReplaceNN :
      term_has_non_none_type
        (SmtTerm.str_replace_all (SmtTerm.String str)
          (SmtTerm.String patStr) (SmtTerm.String replStr)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation, whole] at hsimpa ⊢
    exact hsimpa
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
      (typeof_str_replace_all_eq (SmtTerm.String str)
        (SmtTerm.String patStr) (SmtTerm.String replStr)) hReplaceNN with
    ⟨T, hSTySeq, hPatTySeq, hReplTySeq⟩
  rcases EvaluateProofInternal.smtx_typeof_eo_string_seq_char_valid str T hSTySeq with
    ⟨hT, hStrValid⟩
  subst T
  have hPatValid : native_string_valid patStr = true :=
    (EvaluateProofInternal.smtx_typeof_eo_string_seq_char_valid patStr SmtType.Char
      (by have hsimpa := hPatTySeq; (try simp at hsimpa ⊢); exact hsimpa)).2
  have hReplValid : native_string_valid replStr = true :=
    (EvaluateProofInternal.smtx_typeof_eo_string_seq_char_valid replStr SmtType.Char
      (by have hsimpa := hReplTySeq; (try simp at hsimpa ⊢); exact hsimpa)).2
  cases patStr with
  | nil =>
      have hRun : __run_evaluate whole = Term.String str := by
        have hsimpa :=
          EvaluateProofInternal.str_replace_all_result_strings_empty str replStr
        try simp [whole] at hsimpa ⊢
        exact hsimpa
      rw [hRun]
      constructor
      · change
          __smtx_typeof
              (SmtTerm.str_replace_all (SmtTerm.String str)
                (SmtTerm.String []) (SmtTerm.String replStr)) =
            __smtx_typeof (SmtTerm.String str)
        rw [typeof_str_replace_all_eq]
        simp [__smtx_typeof, __smtx_typeof_seq_op_3, hStrValid,
          hPatValid, hReplValid, native_Teq, native_ite]
      · rw [show
            __smtx_model_eval M (__eo_to_smt whole) =
              __smtx_model_eval_str_replace_all
                (SmtValue.Seq (native_pack_string str))
                (SmtValue.Seq (native_pack_string []))
                (SmtValue.Seq (native_pack_string replStr)) by
          change
            __smtx_model_eval M
                (SmtTerm.str_replace_all (SmtTerm.String str)
                  (SmtTerm.String []) (SmtTerm.String replStr)) =
              __smtx_model_eval_str_replace_all
                (SmtValue.Seq (native_pack_string str))
                (SmtValue.Seq (native_pack_string []))
                (SmtValue.Seq (native_pack_string replStr))
          simp [__smtx_model_eval]]
        rw [show
            __smtx_model_eval M (__eo_to_smt (Term.String str)) =
              SmtValue.Seq (native_pack_string str) by
          change __smtx_model_eval M (SmtTerm.String str) =
            SmtValue.Seq (native_pack_string str)
          rw [__smtx_model_eval.eq_4]]
        rw [EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string_nil]
        exact RuleProofs.smt_value_rel_refl _
  | cons p ps =>
      have hRun :
          __run_evaluate whole =
            Term.String
              (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str) := by
        have hsimpa :=
          EvaluateProofInternal.str_replace_all_result_strings_cons str replStr p ps
        try simp [whole] at hsimpa ⊢
        exact hsimpa
      rw [hRun]
      have hResultValid :
          native_string_valid
              (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str) =
            true :=
        EvaluateProofInternal.native_string_valid_replace_all_chain (p :: ps) replStr str 0
          hStrValid hReplValid
      constructor
      · change
          __smtx_typeof
              (SmtTerm.str_replace_all (SmtTerm.String str)
                (SmtTerm.String (p :: ps)) (SmtTerm.String replStr)) =
            __smtx_typeof
              (SmtTerm.String
                (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str))
        rw [typeof_str_replace_all_eq]
        simp [__smtx_typeof, __smtx_typeof_seq_op_3, hStrValid,
          hPatValid, hReplValid, hResultValid, native_Teq, native_ite]
      · rw [show
            __smtx_model_eval M (__eo_to_smt whole) =
              __smtx_model_eval_str_replace_all
                (SmtValue.Seq (native_pack_string str))
                (SmtValue.Seq (native_pack_string (p :: ps)))
                (SmtValue.Seq (native_pack_string replStr)) by
          change
            __smtx_model_eval M
                (SmtTerm.str_replace_all (SmtTerm.String str)
                  (SmtTerm.String (p :: ps)) (SmtTerm.String replStr)) =
              __smtx_model_eval_str_replace_all
                (SmtValue.Seq (native_pack_string str))
                (SmtValue.Seq (native_pack_string (p :: ps)))
                (SmtValue.Seq (native_pack_string replStr))
          simp [__smtx_model_eval]]
        rw [show
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.String
                    (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str))) =
              SmtValue.Seq
                (native_pack_string
                  (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str)) by
          change
            __smtx_model_eval M
                (SmtTerm.String
                  (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str)) =
              SmtValue.Seq
                (native_pack_string
                  (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) replStr 0 str))
          rw [__smtx_model_eval.eq_4]]
        rw [EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string]
        rw [EvaluateProofInternal.native_str_replace_all_eval_result_cons_eq_chain]
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_substr_core
    (M : SmtModel) (hM : model_wf M)
    (s n m : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n)
                m) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n) m) := by
  intro hATrans hEvalTy
  let whole :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n) m
  have hSubNN :
      term_has_non_none_type
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases str_substr_args_of_non_none hSubNN with
    ⟨T, hSTySeq, hNTy, hMTy⟩
  have hSTrans : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSTySeq]
    simp
  have hNTrans : RuleProofs.eo_has_smt_translation n := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hNTy]
    simp
  have hMTrans : RuleProofs.eo_has_smt_translation m := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hMTy]
    simp
  let runS := __run_evaluate s
  let runStart := __run_evaluate n
  let runLenTerm := __run_evaluate m
  let runEnd :=
    __eo_add (__eo_add runStart runLenTerm)
      (Term.Numeral (-1 : native_Int))
  let runSub := __eo_extract runS runStart runEnd
  have hRunSubNe : runSub ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole)
            runSub) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunSNe : runS ≠ Term.Stuck :=
    EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [runSub] using hRunSubNe)
  have hRunStartNe : runStart ≠ Term.Stuck :=
    EvaluateProofInternal.eo_extract_start_ne_stuck (by simpa [runSub] using hRunSubNe)
  have hRunEndNe : runEnd ≠ Term.Stuck :=
    EvaluateProofInternal.eo_extract_end_ne_stuck (by simpa [runSub] using hRunSubNe)
  have hRunInnerAddNe : __eo_add runStart runLenTerm ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_left_ne_stuck (by simpa [runEnd] using hRunEndNe)
  have hRunLenTermNe : runLenTerm ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_right_ne_stuck hRunInnerAddNe
  have hRunSOrigNe : __run_evaluate s ≠ Term.Stuck := by
    simpa [runS] using hRunSNe
  have hRunStartOrigNe : __run_evaluate n ≠ Term.Stuck := by
    simpa [runStart] using hRunStartNe
  have hRunLenTermOrigNe : __run_evaluate m ≠ Term.Stuck := by
    simpa [runLenTerm] using hRunLenTermNe
  have hSProgTy : __eo_typeof (__eo_prog_evaluate s) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq s T hSTrans hSTySeq
      hRunSOrigNe
  have hNProgTy : __eo_typeof (__eo_prog_evaluate n) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int n hNTrans hNTy
      hRunStartOrigNe
  have hMProgTy : __eo_typeof (__eo_prog_evaluate m) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int m hMTrans hMTy
      hRunLenTermOrigNe
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg1 M
      (Term.UOp UserOp.str_substr) s n m rec) hSTrans hSProgTy with
    ⟨hSSameTy, hSRel⟩
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg2 M
      (Term.UOp UserOp.str_substr) s n m rec) hNTrans hNProgTy with
    ⟨hNSameTy, hNRel⟩
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3 M
      (Term.UOp UserOp.str_substr) s n m rec) hMTrans hMProgTy with
    ⟨hMSameTy, hMRel⟩
  have hRunSTy :
      __smtx_typeof (__eo_to_smt runS) = SmtType.Seq T := by
    simpa [runS] using hSSameTy.symm.trans hSTySeq
  have hRunNTy :
      __smtx_typeof (__eo_to_smt runStart) = SmtType.Int := by
    simpa [runStart] using hNSameTy.symm.trans hNTy
  have hRunMTy :
      __smtx_typeof (__eo_to_smt runLenTerm) = SmtType.Int := by
    simpa [runLenTerm] using hMSameTy.symm.trans hMTy
  rcases EvaluateProofInternal.eo_extract_seq_args_of_nonstuck runS runStart runEnd hRunSTy
      (by simpa [runSub] using hRunSubNe) with
    ⟨str, start, stop, hRunS, hRunStart, hRunEnd, hStrValid, hTChar⟩
  subst T
  have hEndExpr :
      __eo_add (__eo_add (Term.Numeral start) runLenTerm)
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral stop := by
    dsimp [runEnd] at hRunEnd
    rw [hRunStart] at hRunEnd
    exact hRunEnd
  rcases EvaluateProofInternal.eo_substr_len_arg_of_end_numeral start stop runLenTerm hEndExpr with
    ⟨len, hRunLen, _hStopEq⟩
  have hRunSubEq :
      runSub = Term.String (native_str_substr str start len) := by
    dsimp [runSub, runEnd]
    rw [hRunS, hRunStart, hRunLen]
    exact EvaluateProofInternal.eo_extract_string_substr_window str start len
  have hSubValid :
      native_string_valid (native_str_substr str start len) = true :=
    EvaluateProofInternal.native_string_valid_substr_local start len hStrValid
  change
    __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)) =
        __smtx_typeof (__eo_to_smt runSub) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)))
        (__smtx_model_eval M (__eo_to_smt runSub))
  rw [hRunSubEq]
  constructor
  · change
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)) =
        __smtx_typeof (SmtTerm.String (native_str_substr str start len))
    rw [typeof_str_substr_eq]
    simp [__smtx_typeof_str_substr, __smtx_typeof, hSTySeq, hNTy,
      hMTy, hSubValid, native_ite]
  · have hStrEvalTerm :
        __smtx_model_eval M (__eo_to_smt (Term.String str)) =
          SmtValue.Seq (native_pack_string str) := by
      rw [show __eo_to_smt (Term.String str) = SmtTerm.String str by rfl]
      rw [__smtx_model_eval.eq_4]
    have hStartEvalTerm :
        __smtx_model_eval M (__eo_to_smt (Term.Numeral start)) =
          SmtValue.Numeral start := by
      rw [show __eo_to_smt (Term.Numeral start) =
          SmtTerm.Numeral start by rfl]
      rw [__smtx_model_eval.eq_2]
    have hLenEvalTerm :
        __smtx_model_eval M (__eo_to_smt (Term.Numeral len)) =
          SmtValue.Numeral len := by
      rw [show __eo_to_smt (Term.Numeral len) =
          SmtTerm.Numeral len by rfl]
      rw [__smtx_model_eval.eq_2]
    have hSRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt runS)) := by
      simpa [runS] using hSRel
    have hNRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt n))
          (__smtx_model_eval M (__eo_to_smt runStart)) := by
      simpa [runStart] using hNRel
    have hMRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt m))
          (__smtx_model_eval M (__eo_to_smt runLenTerm)) := by
      simpa [runLenTerm] using hMRel
    have hSRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt (Term.String str))) := by
      simpa [hRunS] using hSRelRun
    have hNRelNumeralTerm :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt n))
          (__smtx_model_eval M (__eo_to_smt (Term.Numeral start))) := by
      simpa [hRunStart] using hNRelRun
    have hMRelNumeralTerm :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt m))
          (__smtx_model_eval M (__eo_to_smt (Term.Numeral len))) := by
      simpa [hRunLen] using hMRelRun
    have hSRelSeq :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt s))
          (SmtValue.Seq (native_pack_string str)) := by
      simpa [hStrEvalTerm] using hSRelString
    have hNRelNumeral :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt n))
          (SmtValue.Numeral start) := by
      simpa [hStartEvalTerm] using hNRelNumeralTerm
    have hMRelNumeral :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt m))
          (SmtValue.Numeral len) := by
      simpa [hLenEvalTerm] using hMRelNumeralTerm
    rcases EvaluateProofInternal.smt_value_rel_seq_right_local hSRelSeq with
      ⟨strEval, hSEval, hSSeqRel⟩
    have hSSeqEq :
        strEval = native_pack_string str :=
      (RuleProofs.smt_seq_rel_iff_eq _ _).1 hSSeqRel
    have hNEval :
        __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral start :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt n)) start hNRelNumeral
    have hMEval :
        __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral len :=
      EvaluateProofInternal.smt_value_rel_numeral_eq
        (__smtx_model_eval M (__eo_to_smt m)) len hMRelNumeral
    have hSubEval :
        __smtx_model_eval M
            (__eo_to_smt (Term.String (native_str_substr str start len))) =
          SmtValue.Seq (native_pack_string (native_str_substr str start len)) := by
      rw [show
          __eo_to_smt (Term.String (native_str_substr str start len)) =
            SmtTerm.String (native_str_substr str start len) by
        rfl]
      rw [__smtx_model_eval.eq_4]
    unfold RuleProofs.smt_value_rel
    rw [show
        __smtx_model_eval M
            (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)) =
          __smtx_model_eval_str_substr
            (__smtx_model_eval M (__eo_to_smt s))
            (__smtx_model_eval M (__eo_to_smt n))
            (__smtx_model_eval M (__eo_to_smt m)) by
      simp [__smtx_model_eval]]
    rw [hSEval, hSSeqEq, hNEval, hMEval, hSubEval]
    simp only [__smtx_model_eval_str_substr]
    rw [show
        __smtx_elem_typeof_seq_value (native_pack_string str) =
          SmtType.Char by
      simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
    rw [EvaluateProofInternal.native_seq_extract_pack_string]
    exact RuleProofs.smtx_model_eval_eq_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_len_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_len) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_len) b) := by
  intro hATrans hEvalTy
  have hLenNN :
      term_has_non_none_type (SmtTerm.str_len (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt b)) hLenNN with
    ⟨T, hBTySeq⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTySeq]
    simp
  let runArg := __run_evaluate b
  let runLen := __eo_len runArg
  have hRunLenNe : runLen ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_len) b))
            runLen) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunArgNe : runArg ≠ Term.Stuck :=
      EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLen] using hRunLenNe)
    simpa [runArg] using hRunArgNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b T hBTrans hBTySeq hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_len) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRunTySeq :
      __smtx_typeof (__eo_to_smt runArg) = SmtType.Seq T :=
    hSameTyRun.symm.trans hBTySeq
  rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runArg hRunTySeq
      (by simpa [runLen] using hRunLenNe) with
    ⟨str, hRunArg, hValid, hTChar⟩
  have hRunLen :
      runLen = Term.Numeral (native_str_len str) := by
    change __eo_len runArg = Term.Numeral (native_str_len str)
    rw [hRunArg]
    rfl
  change
    __smtx_typeof (SmtTerm.str_len (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runLen) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runLen))
  rw [hRunLen]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Numeral (native_str_len str))
    rw [typeof_str_len_eq]
    rw [__smtx_typeof.eq_2]
    simp [__smtx_typeof_seq_op_1_ret, hBTySeq]
  · have hRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg)) := by
      simpa [runArg] using hRel
    have hRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String str))) := by
      rw [← hRunArg]
      exact hRelRun
    have hRelLen :=
      EvaluateProofInternal.smt_value_rel_model_eval_str_len_of_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt (Term.String str)))
        hRelString
    have hEvalLenB :
        __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt b)) =
          __smtx_model_eval_str_len
            (__smtx_model_eval M (__eo_to_smt b)) := by
      rw [smtx_eval_str_len_term_eq]
    have hEvalString :
        __smtx_model_eval M (__eo_to_smt (Term.String str)) =
          SmtValue.Seq (native_pack_string str) := by
      rw [show __eo_to_smt (Term.String str) = SmtTerm.String str by rfl]
      rw [__smtx_model_eval.eq_4]
    have hEvalLenString :
        __smtx_model_eval M
            (__eo_to_smt (Term.Numeral (native_str_len str))) =
          __smtx_model_eval_str_len
            (__smtx_model_eval M (__eo_to_smt (Term.String str))) := by
      rw [hEvalString]
      change
        __smtx_model_eval M (SmtTerm.Numeral (native_str_len str)) =
          __smtx_model_eval_str_len (SmtValue.Seq (native_pack_string str))
      rw [__smtx_model_eval.eq_2]
      simp [__smtx_model_eval_str_len, native_pack_string,
        EvaluateProofInternal.native_unpack_pack_seq_local, native_seq_len, native_str_len]
    rw [hEvalLenB, hEvalLenString]
    exact hRelLen

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_to_code_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_to_code) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_to_code) b) := by
  intro hATrans hEvalTy
  have hCodeNN :
      term_has_non_none_type (SmtTerm.str_to_code (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
      (typeof_str_to_code_eq (__eo_to_smt b)) hCodeNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  let runArg := __run_evaluate b
  let runLen := __eo_len runArg
  let runCode :=
    __eo_ite (__eo_eq runLen (Term.Numeral 1)) (__eo_to_z runArg)
      (__eo_ite (__eo_is_z runLen) (Term.Numeral (-1 : native_Int))
        (__eo_mk_apply (Term.UOp UserOp.str_to_code) runArg))
  have hRunCodeNe : runCode ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_code) b))
            runCode) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunLenNe : runLen ≠ Term.Stuck := by
    intro hStuck
    apply hRunCodeNe
    dsimp [runCode]
    rw [hStuck]
    simp [__eo_eq, __eo_ite, native_ite, native_teq]
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hRunArgNe : runArg ≠ Term.Stuck :=
      EvaluateProofInternal.eo_len_arg_ne_stuck (by simpa [runLen] using hRunLenNe)
    simpa [runArg] using hRunArgNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b SmtType.Char
      hBTrans hBTyChar hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_to_code) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRunTyChar :
      __smtx_typeof (__eo_to_smt runArg) =
        SmtType.Seq SmtType.Char :=
    hSameTyRun.symm.trans hBTyChar
  rcases EvaluateProofInternal.eo_len_seq_arg_of_nonstuck runArg hRunTyChar
      (by simpa [runLen] using hRunLenNe) with
    ⟨str, hRunArg, hValid, _hTChar⟩
  have hRunCode :
      runCode = Term.Numeral (native_str_to_code str) := by
    change
      __eo_ite (__eo_eq (__eo_len runArg) (Term.Numeral 1))
          (__eo_to_z runArg)
          (__eo_ite (__eo_is_z (__eo_len runArg))
            (Term.Numeral (-1 : native_Int))
            (__eo_mk_apply (Term.UOp UserOp.str_to_code) runArg)) =
        Term.Numeral (native_str_to_code str)
    rw [hRunArg]
    exact EvaluateProofInternal.str_to_code_result_string hValid
  change
    __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCode) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_to_code (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCode))
  rw [hRunCode]
  constructor
  · change
      __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Numeral (native_str_to_code str))
    rw [typeof_str_to_code_eq]
    rw [__smtx_typeof.eq_2]
    simp [hBTyChar, native_Teq, native_ite]
  · have hRelRun :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg)) := by
      simpa [runArg] using hRel
    have hRelString :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String str))) := by
      rw [← hRunArg]
      exact hRelRun
    have hRelCode :=
      EvaluateProofInternal.smt_value_rel_model_eval_str_to_code_of_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt (Term.String str)))
        hRelString
    have hEvalCodeB :
        __smtx_model_eval M (SmtTerm.str_to_code (__eo_to_smt b)) =
          __smtx_model_eval_str_to_code
            (__smtx_model_eval M (__eo_to_smt b)) := by
      rw [smtx_eval_str_to_code_term_eq]
    have hEvalString :
        __smtx_model_eval M (__eo_to_smt (Term.String str)) =
          SmtValue.Seq (native_pack_string str) := by
      rw [show __eo_to_smt (Term.String str) = SmtTerm.String str by rfl]
      rw [__smtx_model_eval.eq_4]
    have hEvalCodeString :
        __smtx_model_eval M
            (__eo_to_smt (Term.Numeral (native_str_to_code str))) =
          __smtx_model_eval_str_to_code
            (__smtx_model_eval M (__eo_to_smt (Term.String str))) := by
      rw [hEvalString]
      change
        __smtx_model_eval M (SmtTerm.Numeral (native_str_to_code str)) =
          __smtx_model_eval_str_to_code (SmtValue.Seq (native_pack_string str))
      rw [__smtx_model_eval.eq_2]
      simp [__smtx_model_eval_str_to_code,
        RuleProofs.native_unpack_string_pack_string]
    rw [hEvalCodeB, hEvalCodeString]
    exact hRelCode

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_to_int_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_to_int) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_to_int) b) := by
  intro hATrans hEvalTy
  have hIntNN :
      term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq (__eo_to_smt b)) hIntNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  let runArg := __run_evaluate b
  let runInt :=
    __eo_ite (__eo_is_str runArg)
      (__eo_ite (__eo_eq runArg (Term.String []))
        (Term.Numeral (-1 : native_Int))
        (__str_to_int_eval_rec
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro runArg)))
          (Term.Numeral 1) (Term.Numeral 0)))
      (__eo_mk_apply (Term.UOp UserOp.str_to_int) runArg)
  have hRunIntNe : runInt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_int) b))
            runInt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    intro hRunStuck
    apply hRunIntNe
    dsimp [runInt, runArg]
    rw [hRunStuck]
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply,
      native_and, native_not, native_ite, native_teq]
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq b SmtType.Char
      hBTrans hBTyChar hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_to_int) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRunTyChar :
      __smtx_typeof (__eo_to_smt runArg) =
        SmtType.Seq SmtType.Char :=
    hSameTyRun.symm.trans hBTyChar
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  have hRunTrans : RuleProofs.eo_has_smt_translation runArg := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hRunTyChar]
    simp
  have hRunArgNe : runArg ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation runArg hRunTrans
  change
    __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runInt) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_to_int (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runInt))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq SmtType.Char := by
      rw [← hs]
      exact hRunTyChar
    have hValid : native_string_valid s = true :=
      EvaluateProofInternal.native_string_valid_of_string_type hRunStringTy
    have hRunIntString :
        runInt = Term.Numeral (native_str_to_int s) := by
      dsimp [runInt]
      rw [hs]
      exact EvaluateProofInternal.str_to_int_result_string hValid
    rw [hRunIntString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_str_to_int s))
      rw [typeof_str_to_int_eq]
      rw [__smtx_typeof.eq_2]
      simp [hBTyChar, native_Teq, native_ite]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelInt :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_to_int_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalIntB :
          __smtx_model_eval M (SmtTerm.str_to_int (__eo_to_smt b)) =
            __smtx_model_eval_str_to_int
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_96]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalIntString :
          __smtx_model_eval M
              (__eo_to_smt (Term.Numeral (native_str_to_int s))) =
            __smtx_model_eval_str_to_int
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        change
          __smtx_model_eval M (SmtTerm.Numeral (native_str_to_int s)) =
            __smtx_model_eval_str_to_int
              (SmtValue.Seq (native_pack_string s))
        rw [__smtx_model_eval.eq_2]
        simp [__smtx_model_eval_str_to_int,
          RuleProofs.native_unpack_string_pack_string]
      rw [hEvalIntB, hEvalIntString]
      exact hRelInt
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunIntApply :
        runInt = Term.Apply (Term.UOp UserOp.str_to_int) runArg := by
      dsimp [runInt]
      exact EvaluateProofInternal.str_to_int_result_non_string hNotString hRunArgNe
    rw [hRunIntApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt runArg))
      rw [typeof_str_to_int_eq, typeof_str_to_int_eq]
      simp [hBTyChar, hRunTyChar, native_ite, native_Teq]
    · have hRelInt :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_to_int_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalIntB :
          __smtx_model_eval M (SmtTerm.str_to_int (__eo_to_smt b)) =
            __smtx_model_eval_str_to_int
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_96]
      have hEvalIntRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_int) runArg)) =
            __smtx_model_eval_str_to_int
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_to_int (__eo_to_smt runArg)) =
            __smtx_model_eval_str_to_int
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_96]
      rw [hEvalIntB, hEvalIntRun]
      exact hRelInt

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_to_lower_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_to_lower) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_to_lower) b) := by
  intro hATrans hEvalTy
  have hLowerNN :
      term_has_non_none_type (SmtTerm.str_to_lower (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
      (typeof_str_to_lower_eq (__eo_to_smt b)) hLowerNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  have hBEoSeqChar :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char b hBTrans hBTyChar
  have hLowerEoSeqChar :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    change __eo_typeof_str_to_lower (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rw [hBEoSeqChar]
    rfl
  let runArg := __run_evaluate b
  let runLower :=
    __eo_ite (__eo_is_str runArg)
      (__str_case_conv_rec (__str_flatten (__str_nary_intro runArg))
        (Term.Boolean true))
      (__eo_mk_apply (Term.UOp UserOp.str_to_lower) runArg)
  have hRunLowerNe : runLower ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_lower) b))
            runLower) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.str_to_lower) b))
          runLower ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runLower <;>
      simp [__eo_mk_apply, hRun] at hMk hRunLowerNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_lower) b))
            runLower) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_lower) b))
            runLower) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunLowerEoSeqChar :
      __eo_typeof runLower =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.str_to_lower) b) runLower hEvalEqTy
    exact hEq.symm.trans hLowerEoSeqChar
  have hRunBEoSeqChar :
      __eo_typeof runArg =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    EvaluateProofInternal.eo_str_to_lower_result_arg_typeof_seq_char runArg hRunLowerEoSeqChar
  have hSeqCharNe :
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqCharNe hBEoSeqChar hRunBEoSeqChar
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_to_lower) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  change
    __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runLower) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runLower))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq SmtType.Char := by
      rw [← hs]
      exact hSameTyRun.symm.trans hBTyChar
    have hValid : native_string_valid s = true :=
      EvaluateProofInternal.native_string_valid_of_string_type hRunStringTy
    have hRunLowerString :
        runLower = Term.String (native_str_to_lower s) := by
      dsimp [runLower]
      rw [hs]
      exact EvaluateProofInternal.str_to_lower_result_string hValid
    rw [hRunLowerString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.String (native_str_to_lower s))
      rw [typeof_str_to_lower_eq]
      simp [__smtx_typeof, hBTyChar, native_ite, native_Teq,
        native_str_to_lower_valid hValid]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelLower :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_to_lower_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalLowerB :
          __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt b)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_91]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalLowerString :
          __smtx_model_eval M
              (__eo_to_smt (Term.String (native_str_to_lower s))) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        rw [show __eo_to_smt (Term.String (native_str_to_lower s)) =
          SmtTerm.String (native_str_to_lower s) by rfl]
        rw [__smtx_model_eval.eq_4]
        simp [__smtx_model_eval_str_to_lower,
          RuleProofs.native_unpack_string_pack_string]
      rw [hEvalLowerB, hEvalLowerString]
      exact hRelLower
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunArgNe : runArg ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunBEoSeqChar
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at hRunBEoSeqChar
      cases hRunBEoSeqChar
    have hRunLowerApply :
        runLower = Term.Apply (Term.UOp UserOp.str_to_lower) runArg := by
      dsimp [runLower]
      exact EvaluateProofInternal.str_to_lower_result_non_string hNotString hRunArgNe
    rw [hRunLowerApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt runArg))
      have hRunTyChar :
          __smtx_typeof (__eo_to_smt runArg) =
            SmtType.Seq SmtType.Char :=
        hSameTyRun.symm.trans hBTyChar
      rw [typeof_str_to_lower_eq, typeof_str_to_lower_eq]
      simp [hBTyChar, hRunTyChar, native_ite, native_Teq]
    · have hRelLower :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_to_lower_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalLowerB :
          __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt b)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_91]
      have hEvalLowerRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_lower) runArg)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt runArg)) =
            __smtx_model_eval_str_to_lower
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_91]
      rw [hEvalLowerB, hEvalLowerRun]
      exact hRelLower

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_to_upper_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_to_upper) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_to_upper) b) := by
  intro hATrans hEvalTy
  have hUpperNN :
      term_has_non_none_type (SmtTerm.str_to_upper (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hBTyChar :
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
      (typeof_str_to_upper_eq (__eo_to_smt b)) hUpperNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyChar]
    simp
  have hBEoSeqChar :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char b hBTrans hBTyChar
  have hUpperEoSeqChar :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) b) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    change __eo_typeof_str_to_lower (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rw [hBEoSeqChar]
    rfl
  let runArg := __run_evaluate b
  let runUpper :=
    __eo_ite (__eo_is_str runArg)
      (__str_case_conv_rec (__str_flatten (__str_nary_intro runArg))
        (Term.Boolean false))
      (__eo_mk_apply (Term.UOp UserOp.str_to_upper) runArg)
  have hRunUpperNe : runUpper ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_upper) b))
            runUpper) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.str_to_upper) b))
          runUpper ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runUpper <;>
      simp [__eo_mk_apply, hRun] at hMk hRunUpperNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_upper) b))
            runUpper) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_to_upper) b))
            runUpper) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunUpperEoSeqChar :
      __eo_typeof runUpper =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.str_to_upper) b) runUpper hEvalEqTy
    exact hEq.symm.trans hUpperEoSeqChar
  have hRunBEoSeqChar :
      __eo_typeof runArg =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    EvaluateProofInternal.eo_str_to_upper_result_arg_typeof_seq_char runArg hRunUpperEoSeqChar
  have hSeqCharNe :
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqCharNe hBEoSeqChar hRunBEoSeqChar
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_to_upper) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  change
    __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runUpper) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runUpper))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq SmtType.Char := by
      rw [← hs]
      exact hSameTyRun.symm.trans hBTyChar
    have hValid : native_string_valid s = true :=
      EvaluateProofInternal.native_string_valid_of_string_type hRunStringTy
    have hRunUpperString :
        runUpper = Term.String (native_str_to_upper s) := by
      dsimp [runUpper]
      rw [hs]
      exact EvaluateProofInternal.str_to_upper_result_string hValid
    rw [hRunUpperString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.String (native_str_to_upper s))
      rw [typeof_str_to_upper_eq]
      simp [__smtx_typeof, hBTyChar, native_ite, native_Teq,
        native_str_to_upper_valid hValid]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelUpper :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_to_upper_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalUpperB :
          __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt b)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_92]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalUpperString :
          __smtx_model_eval M
              (__eo_to_smt (Term.String (native_str_to_upper s))) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        rw [show __eo_to_smt (Term.String (native_str_to_upper s)) =
          SmtTerm.String (native_str_to_upper s) by rfl]
        rw [__smtx_model_eval.eq_4]
        simp [__smtx_model_eval_str_to_upper,
          RuleProofs.native_unpack_string_pack_string]
      rw [hEvalUpperB, hEvalUpperString]
      exact hRelUpper
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunArgNe : runArg ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunBEoSeqChar
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at hRunBEoSeqChar
      cases hRunBEoSeqChar
    have hRunUpperApply :
        runUpper = Term.Apply (Term.UOp UserOp.str_to_upper) runArg := by
      dsimp [runUpper]
      exact EvaluateProofInternal.str_to_upper_result_non_string hNotString hRunArgNe
    rw [hRunUpperApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt runArg))
      have hRunTyChar :
          __smtx_typeof (__eo_to_smt runArg) =
            SmtType.Seq SmtType.Char :=
        hSameTyRun.symm.trans hBTyChar
      rw [typeof_str_to_upper_eq, typeof_str_to_upper_eq]
      simp [hBTyChar, hRunTyChar, native_ite, native_Teq]
    · have hRelUpper :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_to_upper_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalUpperB :
          __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt b)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_92]
      have hEvalUpperRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_upper) runArg)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt runArg)) =
            __smtx_model_eval_str_to_upper
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_92]
      rw [hEvalUpperB, hEvalUpperRun]
      exact hRelUpper

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_rev_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_rev) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_rev) b) := by
  intro hATrans hEvalTy
  have hRevNN :
      term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
      (typeof_str_rev_eq (__eo_to_smt b)) hRevNN with
    ⟨T, hBTySeq⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTySeq]
    simp
  rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq b hBTrans hBTySeq with
    ⟨U, hBEoSeq, hUSmt⟩
  have hRevEoSeq :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) b) =
        Term.Apply (Term.UOp UserOp.Seq) U := by
    change __eo_typeof_str_rev (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.Seq) U
    rw [hBEoSeq]
    rfl
  let runArg := __run_evaluate b
  let runRev :=
    __eo_ite (__eo_is_str runArg)
      (__str_nary_elim
        (__str_collect
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro runArg)))))
      (__eo_mk_apply (Term.UOp UserOp.str_rev) runArg)
  have hRunRevNe : runRev ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_rev) b))
            runRev) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.str_rev) b))
          runRev ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runRev <;>
      simp [__eo_mk_apply, hRun] at hMk hRunRevNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_rev) b))
            runRev) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_rev) b))
            runRev) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunRevEoSeq :
      __eo_typeof runRev =
        Term.Apply (Term.UOp UserOp.Seq) U := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.str_rev) b) runRev hEvalEqTy
    exact hEq.symm.trans hRevEoSeq
  have hRunBEoSeq :
      __eo_typeof runArg = Term.Apply (Term.UOp UserOp.Seq) U :=
    EvaluateProofInternal.eo_str_rev_result_arg_typeof_seq runArg U hRunRevEoSeq
  have hSeqNe :
      Term.Apply (Term.UOp UserOp.Seq) U ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.Seq) U)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hSeqNe hBEoSeq hRunBEoSeq
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.str_rev) b rec
      hBTrans hBProgTy with
    ⟨hSameTy, hRel⟩
  have hSameTyRun :
      __smtx_typeof (__eo_to_smt b) =
        __smtx_typeof (__eo_to_smt runArg) := by
    simpa [runArg] using hSameTy
  have hRelRun :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (__eo_to_smt runArg)) := by
    simpa [runArg] using hRel
  change
    __smtx_typeof (SmtTerm.str_rev (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runRev) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runRev))
  by_cases hString : ∃ s : native_String, runArg = Term.String s
  · rcases hString with ⟨s, hs⟩
    have hRunStringTy :
        __smtx_typeof (__eo_to_smt (Term.String s)) =
          SmtType.Seq T := by
      rw [← hs]
      exact hSameTyRun.symm.trans hBTySeq
    rcases EvaluateProofInternal.smt_string_seq_type_inv hRunStringTy with ⟨hValid, hTChar⟩
    subst T
    have hRunRevString :
        runRev = Term.String s.reverse := by
      dsimp [runRev]
      rw [hs]
      exact EvaluateProofInternal.str_rev_result_string
    rw [hRunRevString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_rev (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.String s.reverse)
      rw [typeof_str_rev_eq]
      simp [__smtx_typeof_seq_op_1, hBTySeq, hTChar, __smtx_typeof,
        native_ite, EvaluateProofInternal.native_string_valid_reverse_local hValid]
    · have hRelString :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [← hs]
        exact hRelRun
      have hRelRev :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_rev_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (Term.String s)))
          hRelString
      have hEvalRevB :
          __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_89]
      have hEvalString :
          __smtx_model_eval M (__eo_to_smt (Term.String s)) =
            SmtValue.Seq (native_pack_string s) := by
        rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl]
        rw [__smtx_model_eval.eq_4]
      have hEvalRevString :
          __smtx_model_eval M (__eo_to_smt (Term.String s.reverse)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt (Term.String s))) := by
        rw [hEvalString]
        rw [show __eo_to_smt (Term.String s.reverse) =
          SmtTerm.String s.reverse by rfl]
        rw [__smtx_model_eval.eq_4]
        simp [__smtx_model_eval_str_rev, native_pack_string,
          EvaluateProofInternal.native_unpack_pack_seq_local, EvaluateProofInternal.elem_typeof_pack_seq_local,
          native_seq_rev]
      rw [hEvalRevB, hEvalRevString]
      exact hRelRev
  · have hNotString : ∀ s : native_String, runArg ≠ Term.String s := by
      intro s hs
      exact hString ⟨s, hs⟩
    have hRunArgNe : runArg ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunBEoSeq
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) U at hRunBEoSeq
      cases hRunBEoSeq
    have hRunRevApply :
        runRev = Term.Apply (Term.UOp UserOp.str_rev) runArg := by
      dsimp [runRev]
      exact EvaluateProofInternal.str_rev_result_non_string hNotString hRunArgNe
    rw [hRunRevApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_rev (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.str_rev (__eo_to_smt runArg))
      have hRunTySeq :
          __smtx_typeof (__eo_to_smt runArg) = SmtType.Seq T :=
        hSameTyRun.symm.trans hBTySeq
      rw [typeof_str_rev_eq, typeof_str_rev_eq]
      simp [__smtx_typeof_seq_op_1, hBTySeq, hRunTySeq]
    · have hRelRev :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_rev_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt runArg))
          hRelRun
      have hEvalRevB :
          __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt b)) := by
        rw [__smtx_model_eval.eq_89]
      have hEvalRevRun :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_rev) runArg)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt runArg)) := by
        change
          __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt runArg)) =
            __smtx_model_eval_str_rev
              (__smtx_model_eval M (__eo_to_smt runArg))
        rw [__smtx_model_eval.eq_89]
      rw [hEvalRevB, hEvalRevRun]
      exact hRelRev

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_from_code_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_from_code) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  __run_evaluate (Term.Apply (Term.UOp UserOp.str_from_code) x) ≠
      Term.Apply (Term.UOp UserOp.str_from_code) x ->
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_from_code) x) := by
  intro hActive hATrans hEvalTy
  have hFromNN :
      term_has_non_none_type (SmtTerm.str_from_code (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hxSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
      (typeof_str_from_code_eq (__eo_to_smt x)) hFromNN
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int
      (hXMatch.symm.trans hxSmtTy)
  let runFrom := EvaluateProofInternal.eo_eval_str_from_code_rhs x
  have hRunFromActive :
      runFrom ≠ Term.Apply (Term.UOp UserOp.str_from_code) x := by
    intro hSelf
    apply hActive
    change runFrom = Term.Apply (Term.UOp UserOp.str_from_code) x
    exact hSelf
  have hRunFromNe : runFrom ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_from_code) x))
            runFrom) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
    intro hRunStuck
    apply hRunFromActive
    dsimp [runFrom, EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRunStuck]
    simp [__eo_is_z, __eo_is_z_internal, __eo_ite, native_and,
      native_not, native_ite, native_teq]
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int x hXTrans hxSmtTy hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.str_from_code) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Int := by
    rw [← hXSameTy]
    exact hxSmtTy
  change
    __smtx_typeof (SmtTerm.str_from_code (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runFrom) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_from_code (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runFrom))
  cases hRunX : __run_evaluate x
  case Numeral runN =>
    have hRunFromString :
        runFrom = Term.String (native_str_from_code runN) :=
      EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_of_active
        (x := x) (n := runN) hRunX hXEoInt
        (by simpa [runFrom] using hRunFromNe)
        (by simpa [runFrom] using hRunFromActive)
    rw [hRunFromString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_from_code (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.String (native_str_from_code runN))
      rw [typeof_str_from_code_eq, hxSmtTy]
      simp [__smtx_typeof, native_ite, native_Teq,
        native_str_from_code_valid]
    · have hXRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt x))
            (SmtValue.Numeral runN) := by
        rw [hRunX] at hXRel
        rw [show __eo_to_smt (Term.Numeral runN) =
            SmtTerm.Numeral runN by
          rfl] at hXRel
        rw [__smtx_model_eval.eq_2] at hXRel
        exact hXRel
      have hXEval :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Numeral runN :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt x)) runN hXRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.str_from_code (__eo_to_smt x)) =
            __smtx_model_eval_str_from_code
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_94]]
      rw [show
          __eo_to_smt (Term.String (native_str_from_code runN)) =
            SmtTerm.String (native_str_from_code runN) by
        rfl]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Seq (native_pack_string (native_str_from_code runN)))
          (__smtx_model_eval M
            (SmtTerm.String (native_str_from_code runN)))
      rw [__smtx_model_eval.eq_4]
      exact RuleProofs.smt_value_rel_refl _
  all_goals
    exfalso
    apply hRunFromActive
    dsimp [runFrom, EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRunX]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z,
      __eo_is_z_internal, native_and, native_not]

theorem EvaluateProofInternal.run_evaluate_sound_apply_str_from_int_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.str_from_int) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.str_from_int) x) := by
  intro hATrans hEvalTy
  have hFromNN :
      term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hxSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (typeof_str_from_int_eq (__eo_to_smt x)) hFromNN
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  let runFrom := EvaluateProofInternal.eo_eval_str_from_int_rhs x
  have hRunFromNe : runFrom ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.str_from_int) x))
            runFrom) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
    intro hRunStuck
    apply hRunFromNe
    dsimp [runFrom, EvaluateProofInternal.eo_eval_str_from_int_rhs]
    rw [hRunStuck]
    simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
      native_and, native_not, native_ite, native_teq]
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int x hXTrans hxSmtTy hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.str_from_int) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Int := by
    rw [← hXSameTy]
    exact hxSmtTy
  change
    __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runFrom) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_from_int (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runFrom))
  cases hRunX : __run_evaluate x
  case Numeral runN =>
    have hRunFromString :
        runFrom = Term.String (native_str_from_int runN) := by
      simpa [runFrom] using
        EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral (x := x) (n := runN) hRunX
    rw [hRunFromString]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.String (native_str_from_int runN))
      rw [typeof_str_from_int_eq, hxSmtTy]
      simp [__smtx_typeof, native_ite, native_Teq,
        native_str_from_int_valid]
    · have hXRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt x))
            (SmtValue.Numeral runN) := by
        rw [hRunX] at hXRel
        rw [show __eo_to_smt (Term.Numeral runN) =
            SmtTerm.Numeral runN by
          rfl] at hXRel
        rw [__smtx_model_eval.eq_2] at hXRel
        exact hXRel
      have hXEval :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Numeral runN :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt x)) runN hXRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.str_from_int (__eo_to_smt x)) =
            __smtx_model_eval_str_from_int
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_97]]
      rw [show
          __eo_to_smt (Term.String (native_str_from_int runN)) =
            SmtTerm.String (native_str_from_int runN) by
        rfl]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Seq (native_pack_string (native_str_from_int runN)))
          (__smtx_model_eval M
            (SmtTerm.String (native_str_from_int runN)))
      rw [__smtx_model_eval.eq_4]
      exact RuleProofs.smt_value_rel_refl _
  all_goals
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunXSmtTy
      change __smtx_typeof SmtTerm.None = SmtType.Int at hRunXSmtTy
      simp at hRunXSmtTy
    have hNotNumeral :
        ∀ n : native_Int, __run_evaluate x ≠ Term.Numeral n := by
      intro n hNum
      rw [hRunX] at hNum
      cases hNum
    have hRunFromApply :
        runFrom =
          Term.Apply (Term.UOp UserOp.str_from_int) (__run_evaluate x) := by
      simpa [runFrom] using
        EvaluateProofInternal.eo_eval_str_from_int_rhs_run_non_numeral
          (x := x) (t := __run_evaluate x) rfl hNotNumeral hRunXNe
    rw [hRunFromApply]
    constructor
    · change
        __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt x)) =
          __smtx_typeof
            (SmtTerm.str_from_int (__eo_to_smt (__run_evaluate x)))
      rw [typeof_str_from_int_eq, typeof_str_from_int_eq]
      simp [hxSmtTy, hRunXSmtTy, native_ite, native_Teq]
    · have hRelFrom :=
        EvaluateProofInternal.smt_value_rel_model_eval_str_from_int_of_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt (__run_evaluate x)))
          hXRel
      rw [show
          __smtx_model_eval M
              (SmtTerm.str_from_int (__eo_to_smt x)) =
            __smtx_model_eval_str_from_int
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_97]]
      rw [show
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_from_int)
                  (__run_evaluate x))) =
            __smtx_model_eval_str_from_int
              (__smtx_model_eval M (__eo_to_smt (__run_evaluate x))) by
        change
          __smtx_model_eval M
              (SmtTerm.str_from_int (__eo_to_smt (__run_evaluate x))) =
            __smtx_model_eval_str_from_int
              (__smtx_model_eval M (__eo_to_smt (__run_evaluate x)))
        rw [__smtx_model_eval.eq_97]]
      exact hRelFrom

theorem EvaluateProofInternal.run_evaluate_sound_apply_ubv_to_int_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.ubv_to_int) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.ubv_to_int) x) := by
  intro hATrans hEvalTy
  have hUbvToIntNN :
      term_has_non_none_type
        (SmtTerm.ubv_to_int (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_unop_ret_arg_of_non_none
      (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
      (by rw [smtx_typeof_ubv_to_int_term_eq]) hUbvToIntNN with
    ⟨w, hxSmtTy⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hUbvToIntEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.ubv_to_int) x) =
        Term.UOp UserOp.Int := by
    change __eo_typeof__at_bvsize (__eo_typeof x) = Term.UOp UserOp.Int
    rw [hXEoBv]
    rfl
  let runToInt := __eo_to_z (__run_evaluate x)
  have hRunToIntNe : runToInt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
            runToInt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_z_arg_ne_stuck (by simpa [runToInt] using hRunToIntNe)
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
          runToInt ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runToInt <;>
      simp [__eo_mk_apply, hRun] at hMk hRunToIntNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
            runToInt) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
            runToInt) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunToIntEoInt :
      __eo_typeof runToInt = Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.ubv_to_int) x)
        runToInt hEvalEqTy
    exact hEq.symm.trans hUbvToIntEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec x w hXTrans hxSmtTy hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.ubv_to_int) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.BitVec w := by
    rw [← hXSameTy]
    exact hxSmtTy
  cases hRunX : __run_evaluate x
  case Binary runW runN =>
    change
      __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
          __smtx_typeof (__eo_to_smt runToInt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ubv_to_int (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt runToInt))
    rw [show runToInt = Term.Numeral runN by
      simp [runToInt, hRunX, __eo_to_z]]
    change
      __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.Numeral runN) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ubv_to_int (__eo_to_smt x)))
          (__smtx_model_eval M (SmtTerm.Numeral runN))
    constructor
    · rw [show
          __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret
              (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
        rw [smtx_typeof_ubv_to_int_term_eq]]
      rw [hxSmtTy]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_bv_op_1_ret]
    · have hXRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt x))
            (SmtValue.Binary runW runN) := by
        rw [hRunX] at hXRel
        rw [show __eo_to_smt (Term.Binary runW runN) =
            SmtTerm.Binary runW runN by
          rfl] at hXRel
        rw [__smtx_model_eval.eq_5] at hXRel
        exact hXRel
      have hXEval :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Binary runW runN :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt x)) runW runN hXRelValue
      rw [show
          __smtx_model_eval M
              (SmtTerm.ubv_to_int (__eo_to_smt x)) =
            __smtx_model_eval_ubv_to_int
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [smtx_eval_ubv_to_int_term_eq]]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral runN)
          (__smtx_model_eval M (SmtTerm.Numeral runN))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  case Numeral runN =>
    rw [hRunX] at hRunXSmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) =
      SmtType.BitVec w at hRunXSmtTy
    rw [__smtx_typeof.eq_2] at hRunXSmtTy
    cases hRunXSmtTy
  case Rational runQ =>
    rw [hRunX] at hRunXSmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) =
      SmtType.BitVec w at hRunXSmtTy
    rw [__smtx_typeof.eq_3] at hRunXSmtTy
    cases hRunXSmtTy
  case String runS =>
    rw [hRunX] at hRunXSmtTy
    change __smtx_typeof (SmtTerm.String runS) =
      SmtType.BitVec w at hRunXSmtTy
    rw [__smtx_typeof.eq_4] at hRunXSmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunXSmtTy
  all_goals
    have hRunToIntStuck : runToInt = Term.Stuck := by
      dsimp [runToInt]
      rw [hRunX]
      rfl
    exact False.elim (hRunToIntNe hRunToIntStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_sbv_to_int_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.sbv_to_int) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.sbv_to_int) x) := by
  intro hATrans hEvalTy
  have hSbvToIntNN :
      term_has_non_none_type
        (SmtTerm.sbv_to_int (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_unop_ret_arg_of_non_none
      (op := SmtTerm.sbv_to_int) (ret := SmtType.Int)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hSbvToIntNN with
    ⟨w, hxSmtTy⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxSmtTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hxSmtTy)
  have hSbvToIntEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.sbv_to_int) x) =
        Term.UOp UserOp.Int := by
    change __eo_typeof__at_bvsize (__eo_typeof x) = Term.UOp UserOp.Int
    rw [hXEoBv]
    rfl
  let runToInt := EvaluateProofInternal.eo_eval_sbv_to_int_rhs x
  have hRunToIntNe : runToInt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.sbv_to_int) x))
            runToInt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
    intro hRunStuck
    apply hRunToIntNe
    dsimp [runToInt, EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    rw [hRunStuck]
    rw [show
        __eo_eq (__bv_bitwidth (__eo_typeof Term.Stuck))
            (Term.Numeral 0) =
          Term.Stuck by
      rfl]
    rfl
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.sbv_to_int) x))
          runToInt ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runToInt <;>
      simp [__eo_mk_apply, hRun] at hMk hRunToIntNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.sbv_to_int) x))
            runToInt) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.sbv_to_int) x))
            runToInt) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunToIntEoInt :
      __eo_typeof runToInt = Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.sbv_to_int) x)
        runToInt hEvalEqTy
    exact hEq.symm.trans hSbvToIntEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec x w hXTrans hxSmtTy hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.sbv_to_int) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) =
        SmtType.BitVec w := by
    rw [← hXSameTy]
    exact hxSmtTy
  have hRunTrans : RuleProofs.eo_has_smt_translation (__run_evaluate x) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hRunXSmtTy]
    simp
  have hRunMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation
      (__run_evaluate x) hRunTrans
  have hRunEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hRunMatch.symm.trans hRunXSmtTy)
  by_cases hwZero : w = 0
  · subst w
    have hRunToIntEq : runToInt = Term.Numeral 0 := by
      dsimp [runToInt]
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using
        EvaluateProofInternal.eo_eval_sbv_to_int_rhs_eq_zero_of_run_typeof_zero x hRunEoBv
    rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM (__run_evaluate x) 0
        hRunXSmtTy with
      ⟨runN, hRunEval, hRunNNonneg, hRunNLt⟩
    have hRunNEq : runN = 0 := by
      have hlt : runN < 1 := by
        simpa [native_nat_to_int, Smtm.native_nat_to_int,
          native_int_pow2, native_zexp_total] using hRunNLt
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRunNNonneg
    subst runN
    have hRunEval0 :
        __smtx_model_eval M (__eo_to_smt (__run_evaluate x)) =
          SmtValue.Binary 0 0 := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hRunEval
    have hXRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Binary 0 0) := by
      rw [hRunEval0] at hXRel
      exact hXRel
    have hXEval :
        __smtx_model_eval M (__eo_to_smt x) =
          SmtValue.Binary 0 0 :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt x)) 0 0 hXRelValue
    change
      __smtx_typeof (SmtTerm.sbv_to_int (__eo_to_smt x)) =
          __smtx_typeof (__eo_to_smt runToInt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.sbv_to_int (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt runToInt))
    rw [hRunToIntEq]
    change
      __smtx_typeof (SmtTerm.sbv_to_int (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.Numeral 0) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.sbv_to_int (__eo_to_smt x)))
          (__smtx_model_eval M (SmtTerm.Numeral 0))
    constructor
    · rw [show
          __smtx_typeof (SmtTerm.sbv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret
              (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
        rw [__smtx_typeof.eq_def] <;> simp only]
      rw [hxSmtTy]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_bv_op_1_ret]
    · rw [show
          __smtx_model_eval M
              (SmtTerm.sbv_to_int (__eo_to_smt x)) =
            __smtx_model_eval_sbv_to_int
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel (SmtValue.Numeral 0)
          (__smtx_model_eval M (SmtTerm.Numeral 0))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · have hwNatPos : 0 < w := Nat.pos_of_ne_zero hwZero
    have hwIntPos : 0 < native_nat_to_int w := by
      have hCast : (Int.ofNat 0) < (Int.ofNat w) :=
        Int.ofNat_lt.mpr hwNatPos
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hCast
    rcases EvaluateProofInternal.eo_eval_sbv_to_int_rhs_arg_binary_of_pos_run_typeof_int
        x hRunEoBv hwIntPos hRunToIntEoInt with
      ⟨runW, runN, rfl⟩
    change
      __smtx_typeof (SmtTerm.Binary runW runN) =
        SmtType.BitVec w at hxSmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hxSmtTy with
      ⟨hRunWNonneg, hRunCanon, _hRunNatEq⟩
    have hRunToIntEq :
        runToInt = Term.Numeral (native_binary_uts runW runN) := by
      dsimp [runToInt]
      exact
        EvaluateProofInternal.eo_eval_sbv_to_int_rhs_binary_eq_uts
          (w := runW) (n := runN) hRunWNonneg hRunCanon
    change
      __smtx_typeof
          (SmtTerm.sbv_to_int (SmtTerm.Binary runW runN)) =
          __smtx_typeof (__eo_to_smt runToInt) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.sbv_to_int (SmtTerm.Binary runW runN)))
          (__smtx_model_eval M (__eo_to_smt runToInt))
    rw [hRunToIntEq]
    change
      __smtx_typeof
          (SmtTerm.sbv_to_int (SmtTerm.Binary runW runN)) =
          __smtx_typeof
            (SmtTerm.Numeral (native_binary_uts runW runN)) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.sbv_to_int (SmtTerm.Binary runW runN)))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_binary_uts runW runN)))
    constructor
    · rw [show
          __smtx_typeof
              (SmtTerm.sbv_to_int (SmtTerm.Binary runW runN)) =
            __smtx_typeof_bv_op_1_ret
              (__smtx_typeof (SmtTerm.Binary runW runN)) SmtType.Int by
        rw [__smtx_typeof.eq_def] <;> simp only]
      rw [hxSmtTy]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_bv_op_1_ret]
    · rw [show
          __smtx_model_eval M
              (SmtTerm.sbv_to_int (SmtTerm.Binary runW runN)) =
            __smtx_model_eval_sbv_to_int
              (__smtx_model_eval M (SmtTerm.Binary runW runN)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [__smtx_model_eval.eq_5]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_binary_uts runW runN))
          (__smtx_model_eval M
            (SmtTerm.Numeral (native_binary_uts runW runN)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
