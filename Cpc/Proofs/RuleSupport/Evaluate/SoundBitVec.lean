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

theorem EvaluateProofInternal.run_evaluate_sound_apply_not_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.not) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hATrans hEvalTy
  have hNotBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) :=
    EvaluateProofInternal.has_bool_type_not_of_has_translation b hATrans
  have hBBool : RuleProofs.eo_has_bool_type b :=
    RuleProofs.eo_has_bool_type_not_arg b hNotBool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hNotEoBool :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not) b) = Term.Bool := by
    change __eo_typeof_not (__eo_typeof b) = Term.Bool
    rw [hBEoBool]
    rfl
  have hRunNotNe : __eo_not (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.not) b))
          (__eo_not (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_not (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNotNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNotEoBool : __eo_typeof (__eo_not (__run_evaluate b)) = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.not) b)
        (__eo_not (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hNotEoBool
  rcases EvaluateProofInternal.eo_not_arg_boolean_of_typeof_bool
      (__run_evaluate b) hRunNotEoBool with
    ⟨runBool, hRunBool⟩
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunBool]
    rfl
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool := by
    have hBNe : b ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hRunBEoBool
    have hProgEq :=
      EvaluateProofInternal.eo_prog_evaluate_eq_of_term_and_run_ne_stuck b hBNe hRunBNe
    rw [hProgEq]
    change __eo_typeof_eq (__eo_typeof b) (__eo_typeof (__run_evaluate b)) =
      Term.Bool
    rw [hBEoBool, hRunBEoBool]
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not]
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.not) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.not (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_not (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.not (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_not (__run_evaluate b))))
  rw [hRunBool]
  constructor
  · change
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_not runBool))
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_not_eq]
    rw [hBTy]
    rw [__smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runBool)) := by
      simpa [hRunBool] using hRel
    have hRelNot :=
      EvaluateProofInternal.smt_value_rel_model_eval_not_of_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runBool)) hRelBool
    simpa [__eo_not, __smtx_model_eval, __smtx_model_eval_not] using hRelNot

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvnot_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.bvnot) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.bvnot) b) := by
  intro hATrans hEvalTy
  have hBvNotNN :
      term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvnot) (t := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_39])
      hBvNotNN with
    ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvNotEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvnot (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hBEoBv]
    rfl
  have hRunNotNe : __eo_not (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvnot) b))
          (__eo_not (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_not (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNotNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNotEoBv :
      __eo_typeof (__eo_not (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.bvnot) b)
        (__eo_not (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvNotEoType
  rcases EvaluateProofInternal.eo_not_arg_binary_of_typeof_bitvec
      (__run_evaluate b) (native_nat_to_int w) hRunNotEoBv with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.bvnot) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_not (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_not (__run_evaluate b))))
  rw [hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w))))
    rw [show
        __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
          __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_39]]
    rw [hBTy]
    change SmtType.BitVec w =
      __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_not (native_nat_to_int w) runN)
            (native_int_pow2 (native_nat_to_int w))))
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunB] at hRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_5] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt b)) =
          __smtx_model_eval_bvnot
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hEvalB]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_not (native_nat_to_int w) runN)
            (native_int_pow2 (native_nat_to_int w))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_not (native_nat_to_int w) runN)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w))) by
    rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvneg_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.bvneg) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.bvneg) b) := by
  intro hATrans hEvalTy
  have hBvNegNN :
      term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvneg) (t := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_47])
      hBvNegNN with
    ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvNegEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvnot (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hBEoBv]
    rfl
  have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvneg) b))
          (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_neg (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNegNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNegEoBv :
      __eo_typeof (__eo_neg (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.bvneg) b)
        (__eo_neg (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvNegEoType
  rcases EvaluateProofInternal.eo_neg_arg_binary_of_typeof_bitvec
      (__run_evaluate b) (native_nat_to_int w) hRunNegEoBv with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M (Term.UOp UserOp.bvneg) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_neg (__run_evaluate b))))
  rw [hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w))))
    rw [show
        __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
          __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_47]]
    rw [hBTy]
    change SmtType.BitVec w =
      __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total (native_zneg runN)
            (native_int_pow2 (native_nat_to_int w))))
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunB] at hRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_5] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt b)) =
          __smtx_model_eval_bvneg
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_47]]
    rw [hEvalB]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zneg runN)
            (native_int_pow2 (native_nat_to_int w))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total (native_zneg runN)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_to_real_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.to_real) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.to_real) x) := by
  intro hATrans hEvalTy
  have hToRealNN :
      term_has_non_none_type (SmtTerm.to_real (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hRunToQNe : __eo_to_q (__run_evaluate x) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.to_real) x))
            (__eo_to_q (__run_evaluate x))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunToQNe
  have hXInt := to_real_arg_of_non_none (t := __eo_to_smt x) hToRealNN
  · have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXInt]
      simp
    have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int x hXTrans hXInt hRunXNe
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.UOp UserOp.to_real) x rec hXTrans hXProgTy with
      ⟨hXSameTy, hXRel⟩
    have hRunXSmtTy :
        __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Int := by
      rw [← hXSameTy]
      exact hXInt
    rcases EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
        (__run_evaluate x) hRunXSmtTy hRunToQNe with
      ⟨runN, hRunX⟩
    change
      __smtx_typeof (SmtTerm.to_real (__eo_to_smt x)) =
          __smtx_typeof (__eo_to_smt (__eo_to_q (__run_evaluate x))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.to_real (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt (__eo_to_q (__run_evaluate x))))
    rw [hRunX]
    constructor
    · change
        __smtx_typeof (SmtTerm.to_real (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.Rational (native_to_real runN))
      rw [typeof_to_real_eq, hXInt]
      simp [native_ite, native_Teq, __smtx_typeof]
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
          __smtx_model_eval M (SmtTerm.to_real (__eo_to_smt x)) =
            __smtx_model_eval_to_real
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_to_real runN))
          (__smtx_model_eval M
            (SmtTerm.Rational (native_to_real runN)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_to_int_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.to_int) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.to_int) x) := by
  intro hATrans hEvalTy
  have hToIntNN :
      term_has_non_none_type (SmtTerm.to_int (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hRunToZNe : __eo_to_z (__run_evaluate x) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.to_int) x))
            (__eo_to_z (__run_evaluate x))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_z_arg_ne_stuck hRunToZNe
  have hXReal : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int)
      (typeof_to_int_eq (__eo_to_smt x)) hToIntNN
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXReal]
    simp
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real x hXTrans hXReal hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.to_int) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Real := by
    rw [← hXSameTy]
    exact hXReal
  rcases EvaluateProofInternal.eo_to_z_real_arg_of_nonstuck
      (__run_evaluate x) hRunXSmtTy hRunToZNe with
    ⟨runQ, hRunX⟩
  change
    __smtx_typeof (SmtTerm.to_int (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt (__eo_to_z (__run_evaluate x))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.to_int (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt (__eo_to_z (__run_evaluate x))))
  rw [hRunX]
  constructor
  · change
      __smtx_typeof (SmtTerm.to_int (__eo_to_smt x)) =
        __smtx_typeof (SmtTerm.Numeral (native_to_int runQ))
    rw [typeof_to_int_eq, hXReal]
    simp [native_ite, native_Teq, __smtx_typeof]
  · have hXRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Rational runQ) := by
      rw [hRunX] at hXRel
      rw [show __eo_to_smt (Term.Rational runQ) =
          SmtTerm.Rational runQ by
        rfl] at hXRel
      rw [__smtx_model_eval.eq_3] at hXRel
      exact hXRel
    have hXEval :
        __smtx_model_eval M (__eo_to_smt x) =
          SmtValue.Rational runQ :=
      EvaluateProofInternal.smt_value_rel_rational_eq
        (__smtx_model_eval M (__eo_to_smt x)) runQ hXRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.to_int (__eo_to_smt x)) =
          __smtx_model_eval_to_int
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_def] <;> simp only]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Numeral (native_to_int runQ))
        (__smtx_model_eval M
          (SmtTerm.Numeral (native_to_int runQ)))
    rw [__smtx_model_eval.eq_2]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_is_int_core
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.is_int) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.is_int) x) := by
  intro hATrans hEvalTy
  have hIsIntNN :
      term_has_non_none_type (SmtTerm.is_int (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hRunToQNe : __eo_to_q (__run_evaluate x) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.is_int) x))
            (__eo_eq (__eo_to_q (__eo_to_z (__run_evaluate x)))
              (__eo_to_q (__run_evaluate x)))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    cases hFirst : __eo_to_q (__eo_to_z (__run_evaluate x)) <;>
      rw [hFirst] at hEvalTy <;>
      simp [__eo_eq, __eo_mk_apply] at hEvalTy <;>
      exact False.elim
        ((by native_decide : __eo_typeof Term.Stuck ≠ Term.Bool) hEvalTy)
  have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunToQNe
  have hXReal : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int)
      (typeof_is_int_eq (__eo_to_smt x)) hIsIntNN
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXReal]
    simp
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real x hXTrans hXReal hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.is_int) x rec hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Real := by
    rw [← hXSameTy]
    exact hXReal
  rcases EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
      (__run_evaluate x) hRunXSmtTy hRunToQNe with
    ⟨runQ, hRunX⟩
  change
    __smtx_typeof (SmtTerm.is_int (__eo_to_smt x)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_eq (__eo_to_q (__eo_to_z (__run_evaluate x)))
              (__eo_to_q (__run_evaluate x)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.is_int (__eo_to_smt x)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_eq (__eo_to_q (__eo_to_z (__run_evaluate x)))
              (__eo_to_q (__run_evaluate x)))))
  rw [hRunX]
  constructor
  · change
      __smtx_typeof (SmtTerm.is_int (__eo_to_smt x)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_eq (__eo_to_q (__eo_to_z (Term.Rational runQ)))
              (__eo_to_q (Term.Rational runQ))))
    rw [typeof_is_int_eq, hXReal]
    simp [native_ite, native_Teq, __eo_to_z, __eo_to_q, __eo_eq,
      __smtx_typeof]
  · have hXRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Rational runQ) := by
      rw [hRunX] at hXRel
      rw [show __eo_to_smt (Term.Rational runQ) =
          SmtTerm.Rational runQ by
        rfl] at hXRel
      rw [__smtx_model_eval.eq_3] at hXRel
      exact hXRel
    have hXEval :
        __smtx_model_eval M (__eo_to_smt x) =
          SmtValue.Rational runQ :=
      EvaluateProofInternal.smt_value_rel_rational_eq
        (__smtx_model_eval M (__eo_to_smt x)) runQ hXRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.is_int (__eo_to_smt x)) =
          __smtx_model_eval_is_int
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_def] <;> simp only]
    rw [hXEval]
    exact EvaluateProofInternal.eo_is_int_result_rel M runQ

theorem EvaluateProofInternal.run_evaluate_sound_apply_uneg_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) := by
  intro hATrans hEvalTy
  have hUnegNN :
      term_has_non_none_type (SmtTerm.uneg (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases arith_unop_arg_of_non_none
      (op := SmtTerm.uneg) (t := __eo_to_smt b)
      (typeof_uneg_eq (__eo_to_smt b)) hUnegNN with hBTyInt | hBTyReal
  · have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hUnegEoType :
        __eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Int
      rw [hBEoInt]
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not]
    have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
            (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_neg (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunNegNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunNegEoInt :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b)
          (__eo_neg (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hUnegEoType
    rcases EvaluateProofInternal.eo_neg_arg_numeral_of_typeof_int
        (__run_evaluate b) hRunNegEoInt with
      ⟨runN, hRunB⟩
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
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
        (Term.UOp UserOp.__eoo_neg_2) b rec hBTrans hBProgTy with
      ⟨_hSameTy, hRel⟩
    change
      __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_neg (__run_evaluate b))))
    rw [hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Numeral (native_zneg runN))
      rw [typeof_uneg_eq, hBTyInt]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_arith_overload_op_1]
    · have hRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runN) := by
        rw [hRunB] at hRel
        rw [show __eo_to_smt (Term.Numeral runN) =
            SmtTerm.Numeral runN by
          rfl] at hRel
        rw [__smtx_model_eval.eq_2] at hRel
        exact hRel
      have hEvalB :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runN :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
      rw [show
          __smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)) =
            __smtx_model_eval_uneg
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_25]]
      rw [hEvalB]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Numeral (native_zneg runN))
          (__smtx_model_eval M (SmtTerm.Numeral (native_zneg runN)))
      rw [__smtx_model_eval.eq_2]
      exact RuleProofs.smt_value_rel_refl _
  · have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hUnegEoType :
        __eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Real
      rw [hBEoReal]
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not]
    have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
            (__eo_neg (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun : __eo_neg (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunNegNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b))
              (__eo_neg (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunNegEoReal :
        __eo_typeof (__eo_neg (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.UOp UserOp.__eoo_neg_2) b)
          (__eo_neg (__run_evaluate b)) hEvalEqTy
      exact hEq.symm.trans hUnegEoType
    rcases EvaluateProofInternal.eo_neg_arg_rational_of_typeof_real
        (__run_evaluate b) hRunNegEoReal with
      ⟨runQ, hRunB⟩
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.UOp UserOp.__eoo_neg_2) b rec hBTrans hBProgTy with
      ⟨_hSameTy, hRel⟩
    change
      __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt (__eo_neg (__run_evaluate b))))
    rw [hRunB]
    constructor
    · change
        __smtx_typeof (SmtTerm.uneg (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.Rational (native_qneg runQ))
      rw [typeof_uneg_eq, hBTyReal]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_arith_overload_op_1]
    · have hRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runQ) := by
        rw [hRunB] at hRel
        rw [show __eo_to_smt (Term.Rational runQ) =
            SmtTerm.Rational runQ by
          rfl] at hRel
        rw [__smtx_model_eval.eq_3] at hRel
        exact hRel
      have hEvalB :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runQ :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runQ hRelValue
      rw [show
          __smtx_model_eval M (SmtTerm.uneg (__eo_to_smt b)) =
            __smtx_model_eval_uneg
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_25]]
      rw [hEvalB]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Rational (native_qneg runQ))
          (__smtx_model_eval M (SmtTerm.Rational (native_qneg runQ)))
      rw [__smtx_model_eval.eq_3]
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_abs_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.abs) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.abs) b) := by
  intro hATrans hEvalTy
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases abs_arg_of_non_none hAbsNN with hBTyInt | hBTyReal
  · have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyInt]
      simp
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
    have hAbsEoType :
        __eo_typeof (Term.Apply (Term.UOp UserOp.abs) b) =
          Term.UOp UserOp.Int := by
      change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Int
      rw [hBEoInt]
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not]
    have hRunAbsNe :
        __eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b) ≠
          Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) b))
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.abs) b))
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun :
          __eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunAbsNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) b))
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) b))
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunAbsEoInt :
        __eo_typeof
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b)) =
          Term.UOp UserOp.Int := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.UOp UserOp.abs) b)
          (__eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b))
          hEvalEqTy
      exact hEq.symm.trans hAbsEoType
    rcases EvaluateProofInternal.eo_abs_arg_numeral_of_typeof_int
        (__run_evaluate b) hRunAbsEoInt with
      ⟨runN, hRunB⟩
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int := by
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
        (Term.UOp UserOp.abs) b rec hBTrans hBProgTy with
      ⟨_hSameTy, hRel⟩
    change
      __smtx_typeof (SmtTerm.abs (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.abs (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))))
    rw [hRunB]
    constructor
    · rw [typeof_abs_eq, hBTyInt]
      simp [__smtx_typeof_arith_overload_op_1]
      cases hNeg : native_zlt runN 0
      · simp [__eo_is_neg, hNeg, native_teq]
        change SmtType.Int = __smtx_typeof (SmtTerm.Numeral runN)
        rw [__smtx_typeof.eq_2]
      · simp [__eo_is_neg, __eo_neg, hNeg, native_teq]
        change
          SmtType.Int =
            __smtx_typeof (SmtTerm.Numeral (native_zneg runN))
        rw [__smtx_typeof.eq_2]
    · have hRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Numeral runN) := by
        rw [hRunB] at hRel
        rw [show __eo_to_smt (Term.Numeral runN) =
            SmtTerm.Numeral runN by
          rfl] at hRel
        rw [__smtx_model_eval.eq_2] at hRel
        exact hRel
      have hEvalB :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Numeral runN :=
        EvaluateProofInternal.smt_value_rel_numeral_eq
          (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
      rw [show
          __smtx_model_eval M (SmtTerm.abs (__eo_to_smt b)) =
            __smtx_model_eval_abs
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_24]]
      rw [hEvalB]
      by_cases hLt : runN < 0
      · have hNeg : native_zlt runN 0 = true := by
          unfold native_zlt
          rw [decide_eq_true_eq]
          exact hLt
        simp [__smtx_model_eval_abs, __smtx_model_eval_lt,
          __smtx_model_eval_ite, __eo_is_neg, __eo_neg, __eo_ite, hNeg,
          native_ite, native_teq, RuleProofs.smt_value_rel,
          __smtx_model_eval_eq, native_veq, native_zabs, native_zlt,
          native_zneg, hLt]
        change
          SmtValue.Numeral (native_zneg runN) =
            __smtx_model_eval M (SmtTerm.Numeral (native_zneg runN))
        rw [__smtx_model_eval.eq_2]
      · have hNeg : native_zlt runN 0 = false := by
          unfold native_zlt
          rw [decide_eq_false_iff_not]
          exact hLt
        simp [__smtx_model_eval_abs, __smtx_model_eval_lt,
          __smtx_model_eval_ite, __eo_is_neg, __eo_ite, hNeg,
          native_ite, native_teq, RuleProofs.smt_value_rel,
          __smtx_model_eval_eq, native_veq, native_zabs, native_zlt,
          native_zneg, hLt]
        change
          SmtValue.Numeral runN =
            __smtx_model_eval M (SmtTerm.Numeral runN)
        rw [__smtx_model_eval.eq_2]
  · have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyReal]
      simp
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
    have hBEoReal : __eo_typeof b = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real (hBMatch.symm.trans hBTyReal)
    have hAbsEoType :
        __eo_typeof (Term.Apply (Term.UOp UserOp.abs) b) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_abs (__eo_typeof b) = Term.UOp UserOp.Real
      rw [hBEoReal]
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not]
    have hRunAbsNe :
        __eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b) ≠
          Term.Stuck := by
      intro hStuck
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) b))
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [hStuck] at hEvalTy
      change Term.Stuck = Term.Bool at hEvalTy
      cases hEvalTy
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.abs) b))
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b)) ≠
          Term.Stuck := by
      intro hMk
      cases hRun :
          __eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b) <;>
        simp [__eo_mk_apply, hRun] at hMk hRunAbsNe
    have hEvalEqTy :
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) b))
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
          Term.Bool := by
      change
        __eo_typeof
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) b))
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) =
          Term.Bool at hEvalTy
      rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
      exact hEvalTy
    have hRunAbsEoReal :
        __eo_typeof
            (__eo_ite (__eo_is_neg (__run_evaluate b))
              (__eo_neg (__run_evaluate b)) (__run_evaluate b)) =
          Term.UOp UserOp.Real := by
      have hEq :=
        EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
          (Term.Apply (Term.UOp UserOp.abs) b)
          (__eo_ite (__eo_is_neg (__run_evaluate b))
            (__eo_neg (__run_evaluate b)) (__run_evaluate b))
          hEvalEqTy
      exact hEq.symm.trans hAbsEoType
    rcases EvaluateProofInternal.eo_abs_arg_rational_of_typeof_real
        (__run_evaluate b) hRunAbsEoReal with
      ⟨runQ, hRunB⟩
    have hRunBEoType :
        __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Real := by
      rw [hRunB]
      rfl
    have hRealTypeNe : Term.UOp UserOp.Real ≠ Term.Stuck := by
      intro h
      cases h
    have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
        (Term.UOp UserOp.Real)
        (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
        hRealTypeNe hBEoReal hRunBEoType
    rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
        (Term.UOp UserOp.abs) b rec hBTrans hBProgTy with
      ⟨_hSameTy, hRel⟩
    change
      __smtx_typeof (SmtTerm.abs (__eo_to_smt b)) =
          __smtx_typeof
            (__eo_to_smt
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.abs (__eo_to_smt b)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite (__eo_is_neg (__run_evaluate b))
                (__eo_neg (__run_evaluate b)) (__run_evaluate b))))
    rw [hRunB]
    constructor
    · rw [typeof_abs_eq, hBTyReal]
      simp [__smtx_typeof_arith_overload_op_1]
      cases hNeg : native_qlt runQ (native_mk_rational 0 1)
      · simp [__eo_is_neg, hNeg, native_teq]
        change SmtType.Real = __smtx_typeof (SmtTerm.Rational runQ)
        rw [__smtx_typeof.eq_3]
      · simp [__eo_is_neg, __eo_neg, hNeg, native_teq]
        change
          SmtType.Real =
            __smtx_typeof (SmtTerm.Rational (native_qneg runQ))
        rw [__smtx_typeof.eq_3]
    · have hRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Rational runQ) := by
        rw [hRunB] at hRel
        rw [show __eo_to_smt (Term.Rational runQ) =
            SmtTerm.Rational runQ by
          rfl] at hRel
        rw [__smtx_model_eval.eq_3] at hRel
        exact hRel
      have hEvalB :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Rational runQ :=
        EvaluateProofInternal.smt_value_rel_rational_eq
          (__smtx_model_eval M (__eo_to_smt b)) runQ hRelValue
      rw [show
          __smtx_model_eval M (SmtTerm.abs (__eo_to_smt b)) =
            __smtx_model_eval_abs
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_24]]
      rw [hEvalB]
      by_cases hLt : runQ < 0
      · have hNeg : native_qlt runQ (native_mk_rational 0 1) = true := by
          unfold native_qlt native_mk_rational
          rw [decide_eq_true_eq]
          simpa [rat_zero_div_one] using hLt
        simp [__smtx_model_eval_abs, __smtx_model_eval_lt,
          __smtx_model_eval_ite, __eo_is_neg, __eo_neg, __eo_ite, hNeg,
          native_ite, native_teq, RuleProofs.smt_value_rel,
          __smtx_model_eval_eq, native_veq, native_qabs, native_qneg,
          native_qlt, native_mk_rational, rat_zero_div_one, hLt]
        change
          SmtValue.Rational (native_qneg runQ) =
            __smtx_model_eval M (SmtTerm.Rational (native_qneg runQ))
        rw [__smtx_model_eval.eq_3]
      · have hNeg : native_qlt runQ (native_mk_rational 0 1) = false := by
          unfold native_qlt native_mk_rational
          rw [decide_eq_false_iff_not]
          simpa [rat_zero_div_one] using hLt
        simp [__smtx_model_eval_abs, __smtx_model_eval_lt,
          __smtx_model_eval_ite, __eo_is_neg, __eo_ite, hNeg,
          native_ite, native_teq, RuleProofs.smt_value_rel,
          __smtx_model_eval_eq, native_veq, native_qabs, native_qneg,
          native_qlt, native_mk_rational, rat_zero_div_one, hLt]
        change
          SmtValue.Rational runQ =
            __smtx_model_eval M (SmtTerm.Rational runQ)
        rw [__smtx_model_eval.eq_3]

theorem EvaluateProofInternal.run_evaluate_sound_apply_int_pow2_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.int_pow2) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.int_pow2) b) := by
  intro hATrans hEvalTy
  have hPowNN :
      term_has_non_none_type (SmtTerm.int_pow2 (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hBTyInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
      (typeof_int_pow2_eq (__eo_to_smt b)) hPowNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hPowEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.int_pow2) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_int_pow2 (__eo_typeof b) = Term.UOp UserOp.Int
    rw [hBEoInt]
    rfl
  let runPow :=
    __eo_ite (__eo_is_z (__run_evaluate b))
      (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) (__run_evaluate b))
  have hRunPowNe : runPow ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_pow2) b))
            runPow) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.int_pow2) b))
          runPow ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runPow <;>
      simp [__eo_mk_apply, hRun] at hMk hRunPowNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_pow2) b))
            runPow) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_pow2) b))
            runPow) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunPowEoInt :
      __eo_typeof runPow = Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.int_pow2) b)
        runPow hEvalEqTy
    exact hEq.symm.trans hPowEoType
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int :=
    EvaluateProofInternal.eo_int_pow2_result_arg_typeof_int (__run_evaluate b) hRunPowEoInt
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.int_pow2) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.int_pow2 (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_is_z (__run_evaluate b))
              (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_is_z (__run_evaluate b))
              (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (__run_evaluate b)))))
  cases hRun : __run_evaluate b with
  | Numeral runN =>
      constructor
      · rw [EvaluateProofInternal.eo_int_pow2_eval_numeral_to_smt]
        rw [typeof_int_pow2_eq, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hRelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral runN) := by
          rw [hRun] at hBRel
          rw [show __eo_to_smt (Term.Numeral runN) =
              SmtTerm.Numeral runN by
            rfl] at hBRel
          rw [__smtx_model_eval.eq_2] at hBRel
          exact hBRel
        have hEvalB :
            __smtx_model_eval M (__eo_to_smt b) =
              SmtValue.Numeral runN :=
          EvaluateProofInternal.smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
        rw [show
            __smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt b)) =
              __smtx_model_eval_int_pow2
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_29]]
        rw [hEvalB]
        rw [EvaluateProofInternal.eo_int_pow2_eval_numeral_to_smt]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_int_pow2 runN))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_int_pow2 runN)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _
  | Stuck =>
      rw [hRun] at hRunBEoType
      change Term.Stuck = Term.UOp UserOp.Int at hRunBEoType
      cases hRunBEoType
  | _ =>
      have hRunPowToSmt :
          __eo_to_smt
              (__eo_ite (__eo_is_z (__run_evaluate b))
                (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2) (__run_evaluate b)))
                (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                  (__run_evaluate b))) =
            SmtTerm.int_pow2 (__eo_to_smt (__run_evaluate b)) := by
        rw [hRun]
        simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
          native_ite, native_teq, native_and, native_not] <;> rfl
      rw [← hRun]
      constructor
      · rw [hRunPowToSmt]
        rw [typeof_int_pow2_eq, typeof_int_pow2_eq, ← hBSameTy, hBTyInt]
      · rw [hRunPowToSmt]
        rw [__smtx_model_eval.eq_29, __smtx_model_eval.eq_29]
        exact EvaluateProofInternal.smt_value_rel_model_eval_int_pow2_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (__run_evaluate b))) hBRel

theorem EvaluateProofInternal.run_evaluate_sound_apply_int_log2_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.int_log2) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.int_log2) b) := by
  intro hATrans hEvalTy
  have hLogNN :
      term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  have hBTyInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2)
      (typeof_int_log2_eq (__eo_to_smt b)) hLogNN
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hLogEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.int_log2) b) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_int_pow2 (__eo_typeof b) = Term.UOp UserOp.Int
    rw [hBEoInt]
    rfl
  let runLog :=
    __eo_ite (__eo_is_z (__run_evaluate b))
      (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
        (__eo_log (Term.Numeral 2) (__run_evaluate b)))
      (__eo_mk_apply (Term.UOp UserOp.int_log2) (__run_evaluate b))
  have hRunLogNe : runLog ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_log2) b))
            runLog) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.int_log2) b))
          runLog ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runLog <;>
      simp [__eo_mk_apply, hRun] at hMk hRunLogNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_log2) b))
            runLog) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_log2) b))
            runLog) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunLogEoInt :
      __eo_typeof runLog = Term.UOp UserOp.Int := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.int_log2) b)
        runLog hEvalEqTy
    exact hEq.symm.trans hLogEoType
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int :=
    EvaluateProofInternal.eo_int_log2_result_arg_typeof_int (__run_evaluate b) hRunLogEoInt
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.int_log2) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.int_log2 (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_is_z (__run_evaluate b))
              (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                (__eo_log (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_log2)
                (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.int_log2 (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_ite (__eo_is_z (__run_evaluate b))
              (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                (__eo_log (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_log2)
                (__run_evaluate b)))))
  cases hRun : __run_evaluate b with
  | Numeral runN =>
      constructor
      · rw [EvaluateProofInternal.eo_int_log2_eval_numeral_to_smt]
        rw [typeof_int_log2_eq, hBTyInt]
        rw [__smtx_typeof.eq_2]
        simp [native_ite, native_Teq]
      · have hRelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral runN) := by
          rw [hRun] at hBRel
          rw [show __eo_to_smt (Term.Numeral runN) =
              SmtTerm.Numeral runN by
            rfl] at hBRel
          rw [__smtx_model_eval.eq_2] at hBRel
          exact hBRel
        have hEvalB :
            __smtx_model_eval M (__eo_to_smt b) =
              SmtValue.Numeral runN :=
          EvaluateProofInternal.smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
        rw [show
            __smtx_model_eval M (SmtTerm.int_log2 (__eo_to_smt b)) =
              __smtx_model_eval_int_log2
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_30]]
        rw [hEvalB]
        rw [EvaluateProofInternal.eo_int_log2_eval_numeral_to_smt]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Numeral (native_int_log2 runN))
            (__smtx_model_eval M
              (SmtTerm.Numeral (native_int_log2 runN)))
        rw [__smtx_model_eval.eq_2]
        exact RuleProofs.smt_value_rel_refl _
  | Stuck =>
      rw [hRun] at hRunBEoType
      change Term.Stuck = Term.UOp UserOp.Int at hRunBEoType
      cases hRunBEoType
  | _ =>
      have hRunLogToSmt :
          __eo_to_smt
              (__eo_ite (__eo_is_z (__run_evaluate b))
                (__eo_ite (__eo_is_neg (__run_evaluate b)) (Term.Numeral 0)
                  (__eo_log (Term.Numeral 2) (__run_evaluate b)))
                (__eo_mk_apply (Term.UOp UserOp.int_log2)
                  (__run_evaluate b))) =
            SmtTerm.int_log2 (__eo_to_smt (__run_evaluate b)) := by
        rw [hRun]
        simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
          native_ite, native_teq, native_and, native_not] <;> rfl
      rw [← hRun]
      constructor
      · rw [hRunLogToSmt]
        rw [typeof_int_log2_eq, typeof_int_log2_eq, ← hBSameTy, hBTyInt]
      · rw [hRunLogToSmt]
        rw [__smtx_model_eval.eq_30, __smtx_model_eval.eq_30]
        exact EvaluateProofInternal.smt_value_rel_model_eval_int_log2_of_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (__eo_to_smt (__run_evaluate b))) hBRel

theorem EvaluateProofInternal.run_evaluate_sound_apply_int_ispow2_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.int_ispow2) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.int_ispow2) b) := by
  intro hATrans hEvalTy
  let geqTerm :=
    SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0)
  let eqTerm :=
    SmtTerm.eq (__eo_to_smt b)
      (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b)))
  have hIspowNN :
      term_has_non_none_type (SmtTerm.and geqTerm eqTerm) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation, geqTerm, eqTerm] at hsimpa ⊢
    exact hsimpa
  have hArgs :
      __smtx_typeof geqTerm = SmtType.Bool ∧
        __smtx_typeof eqTerm = SmtType.Bool :=
    bool_binop_args_bool_of_non_none (op := SmtTerm.and)
      (typeof_and_eq geqTerm eqTerm) hIspowNN
  have hGeqNN : term_has_non_none_type geqTerm := by
    unfold term_has_non_none_type
    rw [hArgs.1]
    simp
  have hGeqArgs :
      (__smtx_typeof (__eo_to_smt b) = SmtType.Int ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int) ∨
        (__smtx_typeof (__eo_to_smt b) = SmtType.Real ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Real) :=
    arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt b) (SmtTerm.Numeral 0)) hGeqNN
  have hBTyInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int := by
    rcases hGeqArgs with hInt | hReal
    · exact hInt.1
    · have hZeroReal := hReal.2
      rw [__smtx_typeof.eq_2] at hZeroReal
      simp at hZeroReal
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTyInt]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoInt : __eo_typeof b = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hBMatch.symm.trans hBTyInt)
  have hIspowEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.int_ispow2) b) =
        Term.Bool := by
    change __eo_typeof_int_ispow2 (__eo_typeof b) = Term.Bool
    rw [hBEoInt]
    rfl
  let runIspow :=
    let isNeg := __eo_is_neg (__run_evaluate b)
    let isZ := __eo_is_z (__run_evaluate b)
    __eo_ite isZ
      (__eo_ite isNeg (Term.Boolean false)
        (__eo_eq (__run_evaluate b)
          (__eo_pow (Term.Numeral 2)
            (__eo_ite isZ
              (__eo_ite isNeg (Term.Numeral 0)
                (__eo_log (Term.Numeral 2) (__run_evaluate b)))
              (__eo_mk_apply (Term.UOp UserOp.int_log2)
                (__run_evaluate b))))))
      (__eo_mk_apply (Term.UOp UserOp.int_ispow2) (__run_evaluate b))
  have hRunIspowNe : runIspow ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_ispow2) b))
            runIspow) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.int_ispow2) b))
          runIspow ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runIspow <;>
      simp [__eo_mk_apply, hRun] at hMk hRunIspowNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_ispow2) b))
            runIspow) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.int_ispow2) b))
            runIspow) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunIspowEoBool :
      __eo_typeof runIspow = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.int_ispow2) b)
        runIspow hEvalEqTy
    exact hEq.symm.trans hIspowEoType
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) = Term.UOp UserOp.Int :=
    EvaluateProofInternal.eo_int_ispow2_result_arg_typeof_int
      (__run_evaluate b) hRunIspowEoBool
  have hIntTypeNe : Term.UOp UserOp.Int ≠ Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.UOp UserOp.Int)
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hIntTypeNe hBEoInt hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp UserOp.int_ispow2) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  change
    __smtx_typeof
        (SmtTerm.and
          (SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0))
          (SmtTerm.eq (__eo_to_smt b)
            (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b))))) =
        __smtx_typeof (__eo_to_smt runIspow) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0))
            (SmtTerm.eq (__eo_to_smt b)
              (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b))))))
        (__smtx_model_eval M (__eo_to_smt runIspow))
  cases hRun : __run_evaluate b with
  | Numeral runN =>
      constructor
      · calc
          __smtx_typeof
              (SmtTerm.and
                (SmtTerm.geq (__eo_to_smt b) (SmtTerm.Numeral 0))
                (SmtTerm.eq (__eo_to_smt b)
                  (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt b))))) =
              SmtType.Bool :=
            EvaluateProofInternal.smt_typeof_int_ispow2_formula_eq_bool (__eo_to_smt b) hBTyInt
          _ = __smtx_typeof (__eo_to_smt runIspow) := by
            dsimp [runIspow]
            rw [hRun]
            exact (EvaluateProofInternal.int_ispow2_numeral_to_smt_type_bool runN).symm
      · have hRelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Numeral runN) := by
          rw [hRun] at hBRel
          rw [show __eo_to_smt (Term.Numeral runN) =
              SmtTerm.Numeral runN by
            rfl] at hBRel
          rw [__smtx_model_eval.eq_2] at hBRel
          exact hBRel
        have hEvalB :
            __smtx_model_eval M (__eo_to_smt b) =
              SmtValue.Numeral runN :=
          EvaluateProofInternal.smt_value_rel_numeral_eq
            (__smtx_model_eval M (__eo_to_smt b)) runN hRelValue
        dsimp [runIspow]
        rw [hRun]
        simpa [__smtx_model_eval, hEvalB] using
          EvaluateProofInternal.int_ispow2_numeral_eval_rel M runN
  | Stuck =>
      rw [hRun] at hRunBEoType
      change Term.Stuck = Term.UOp UserOp.Int at hRunBEoType
      cases hRunBEoType
  | _ =>
      have hRunIspowToSmt :
          __eo_to_smt runIspow =
            SmtTerm.and
              (SmtTerm.geq (__eo_to_smt (__run_evaluate b))
                (SmtTerm.Numeral 0))
              (SmtTerm.eq (__eo_to_smt (__run_evaluate b))
                (SmtTerm.int_pow2
                  (SmtTerm.int_log2
                    (__eo_to_smt (__run_evaluate b))))) := by
        dsimp [runIspow]
        rw [hRun]
        simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
          native_ite, native_teq, native_and, native_not] <;> rfl
      have hRunBTyInt :
          __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.Int :=
        hBSameTy.symm.trans hBTyInt
      have hBEvalValueTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt b)) =
            SmtType.Int := by
        simpa [hBTyInt] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt b) (by
              unfold term_has_non_none_type
              rw [hBTyInt]
              simp)
      rcases int_value_canonical hBEvalValueTy with
        ⟨evalB, hEvalB⟩
      have hRunEval :
          __smtx_model_eval M (__eo_to_smt (__run_evaluate b)) =
            SmtValue.Numeral evalB := by
        have hRelSym :=
          RuleProofs.smt_value_rel_symm _ _ hBRel
        rw [hEvalB] at hRelSym
        exact EvaluateProofInternal.smt_value_rel_numeral_eq _ evalB hRelSym
      rw [hRunIspowToSmt]
      constructor
      · exact
          (EvaluateProofInternal.smt_typeof_int_ispow2_formula_eq_bool (__eo_to_smt b) hBTyInt).trans
            (EvaluateProofInternal.smt_typeof_int_ispow2_formula_eq_bool
              (__eo_to_smt (__run_evaluate b)) hRunBTyInt).symm
      · simp [__smtx_model_eval, hEvalB, hRunEval]
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_at_bvsize_core
    (M : SmtModel) (hM : model_wf M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp._at_bvsize) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp._at_bvsize) b) := by
  intro hATrans _hEvalTy
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) b) =
        let _v0 := __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt b))
        native_ite (native_zleq 0 _v0)
          (SmtTerm._at_purify (SmtTerm.Numeral _v0))
          SmtTerm.None := by
    rfl
  have hApplyNN :
      __smtx_typeof
          (let _v0 := __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt b))
           native_ite (native_zleq 0 _v0)
             (SmtTerm._at_purify (SmtTerm.Numeral _v0))
             SmtTerm.None) ≠
        SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hATrans
    rw [← hTranslate]
    exact hATrans
  have hArgExists :
      ∃ w : native_Nat, __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w := by
    cases hTy : __smtx_typeof (__eo_to_smt b) with
    | BitVec w =>
        exact ⟨w, rfl⟩
    | _ =>
        exfalso
        have hNeg : native_zleq 0 (native_zneg 1) = false := by
          native_decide
        apply hApplyNN
        rw [hTy]
        simp [__eo_to_smt_bv_size, hNeg, native_ite]
  rcases hArgExists with ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hRun :
      __run_evaluate (Term.Apply (Term.UOp UserOp._at_bvsize) b) =
        Term.Numeral (native_nat_to_int w) := by
    change __bv_bitwidth (__eo_typeof b) =
      Term.Numeral (native_nat_to_int w)
    rw [hBEoBv]
    rfl
  rw [hRun]
  rw [show
      __eo_to_smt (Term.Numeral (native_nat_to_int w)) =
        SmtTerm.Numeral (native_nat_to_int w) by
    rfl]
  have hWNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  constructor
  · rw [hTranslate, hBTy]
    simp [__eo_to_smt_bv_size, __smtx_typeof, native_ite, hWNonneg]
  · rw [hTranslate, hBTy]
    simp [__eo_to_smt_bv_size, __smtx_model_eval,
      __smtx_model_eval__at_purify, native_ite, hWNonneg]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_zero_extend_core
    (M : SmtModel) (hM : model_wf M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x) := by
  intro hATrans hEvalTy
  have hZeroNN :
      term_has_non_none_type
        (SmtTerm.zero_extend (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases zero_extend_args_of_non_none hZeroNN with
    ⟨i, w, hnSmt, hxSmtTy, hi0⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hIGtNegOne : native_zlt (-1 : native_Int) i = true := by
    have hi : (0 : Int) <= i := by
      simpa [native_zleq, SmtEval.native_zleq] using hi0
    have hlt : (-1 : Int) < i := by omega
    simpa [native_zlt, SmtEval.native_zlt] using hlt
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
  have hZeroEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    change
      __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i))
    rw [hXEoBv]
    simp [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
      __eo_mk_apply, native_ite, native_teq, native_not, hIGtNegOne]
  let runZero :=
    __eo_to_bin
      (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
        (Term.Numeral i))
      (__eo_to_z (__run_evaluate x))
  have hRunZeroNe : runZero ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
            runZero) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
          runZero ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runZero <;>
      simp [__eo_mk_apply, hRun] at hMk hRunZeroNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
            runZero) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x))
            runZero) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunZeroEoBv :
      __eo_typeof runZero =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x)
        runZero hEvalEqTy
    exact hEq.symm.trans hZeroEoType
  rcases EvaluateProofInternal.eo_zero_extend_literal_arg_binary_of_typeof_bitvec
      (__run_evaluate x) i (native_zplus (native_nat_to_int w) i)
      hRunZeroEoBv with
    ⟨runW, runN, hRunX, hWidthEq, hRunZeroEq⟩
  have hRunW : runW = native_nat_to_int w := by
    have hAdd :
        native_nat_to_int w + i = runW + i := by
      simpa [native_zplus, SmtEval.native_zplus] using hWidthEq
    have hAddLeft : i + native_nat_to_int w = i + runW := by
      simpa [Int.add_comm] using hAdd
    exact (Int.add_left_cancel hAddLeft).symm
  subst runW
  have hRunXEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunX]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof x
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
      hBvTypeNe hXEoBv hRunXEoBv
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  have hRunZeroEq' :
      runZero =
        Term.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
            (native_int_pow2 (native_zplus (native_nat_to_int w) i))) := by
    simpa [runZero, hRunX] using hRunZeroEq
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hwNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hwNonneg
  have hWidthNonneg :
      native_zleq 0 (native_zplus (native_nat_to_int w) i) = true := by
    have hAdd : 0 <= native_nat_to_int w + i := Int.add_nonneg hw hi
    have hsimpa := hAdd
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hWidthComm :
      native_zplus i (native_nat_to_int w) =
        native_zplus (native_nat_to_int w) i := by
    simp [SmtEval.native_zplus, Int.add_comm]
  change
    __smtx_typeof
        (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runZero) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runZero))
  rw [hRunZeroEq']
  constructor
  · rw [typeof_zero_extend_eq, hxSmtTy]
    simp [__smtx_typeof_zero_extend, native_ite, hi0]
    change
      SmtType.BitVec
          (native_int_to_nat (native_zplus i (native_nat_to_int w))) =
        __smtx_typeof
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
              (native_int_pow2 (native_zplus (native_nat_to_int w) i))))
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg _ _ hWidthNonneg]
    rw [hWidthComm]
  · have hXRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunX] at hXRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hXRel
      rw [__smtx_model_eval.eq_5] at hXRel
      exact hXRel
    have hXEval :
        __smtx_model_eval M (__eo_to_smt x) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt x))
        (native_nat_to_int w) runN hXRelValue
    have hXEvalValueTy :
        __smtx_typeof_value
            (__smtx_model_eval M (__eo_to_smt x)) =
          SmtType.BitVec w := by
      simpa [hxSmtTy] using
        smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt x) (by
            unfold term_has_non_none_type
            rw [hxSmtTy]
            simp)
    have hCanonOrig :
        native_zeq runN
            (native_mod_total runN
              (native_int_pow2 (native_nat_to_int w))) =
          true :=
      bitvec_payload_canonical (by simpa [hXEval] using hXEvalValueTy)
    have hCanonNew :
        native_zeq runN
            (native_mod_total runN
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i))) =
          true := by
      have hCanon :=
        bitvec_payload_canonical_zero_extend
          (i := i) (w := native_nat_to_int w) (n := runN)
          hi0 hwNonneg hCanonOrig
      simpa [hWidthComm] using hCanon
    have hPayloadEq :
        runN =
          native_mod_total runN
            (native_int_pow2 (native_zplus (native_nat_to_int w) i)) := by
      simpa [SmtEval.native_zeq] using hCanonNew
    rw [show
        __smtx_model_eval M
            (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_model_eval_zero_extend
            (SmtValue.Numeral i)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_67, __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_zplus i (native_nat_to_int w)) runN)
        (__smtx_model_eval M
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
              (native_int_pow2 (native_zplus (native_nat_to_int w) i)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
              (native_mod_total runN
                (native_int_pow2 (native_zplus (native_nat_to_int w) i)))) =
          SmtValue.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total runN
              (native_int_pow2 (native_zplus (native_nat_to_int w) i))) by
      rw [__smtx_model_eval.eq_5]]
    rw [hWidthComm]
    rw [← hPayloadEq]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_sign_extend_core
    (M : SmtModel) (hM : model_wf M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.sign_extend n) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.sign_extend n) x) := by
  intro hATrans hEvalTy
  have hSignNN :
      term_has_non_none_type
        (SmtTerm.sign_extend (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases sign_extend_args_of_non_none hSignNN with
    ⟨i, w, hnSmt, hxSmtTy, hi0⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hIGtNegOne : native_zlt (-1 : native_Int) i = true := by
    have hi : (0 : Int) <= i := by
      simpa [native_zleq, SmtEval.native_zleq] using hi0
    have hlt : (-1 : Int) < i := by omega
    simpa [native_zlt, SmtEval.native_zlt] using hlt
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
  have hSignEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    change
      __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i))
    rw [hXEoBv]
    simp [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
      __eo_mk_apply, native_ite, native_teq, native_not, hIGtNegOne]
  let runSign :=
    EvaluateProofInternal.eo_eval_sign_extend_rhs (__run_evaluate x) (Term.Numeral i)
  have hRunSignNe : runSign ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
            runSign) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
          runSign ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runSign <;>
      simp [__eo_mk_apply, hRun] at hMk hRunSignNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
            runSign) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x))
            runSign) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunSignEoBv :
      __eo_typeof runSign =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x)
        runSign hEvalEqTy
    exact hEq.symm.trans hSignEoType
  rcases EvaluateProofInternal.eo_eval_sign_extend_rhs_binary_of_typeof_bitvec
      (__run_evaluate x) i (native_zplus (native_nat_to_int w) i)
      hRunSignEoBv with
    ⟨runW, runN, hRunX, hWidthEq⟩
  have hRunW : runW = native_nat_to_int w := by
    have hAdd :
        native_nat_to_int w + i = runW + i := by
      simpa [native_zplus, SmtEval.native_zplus] using hWidthEq
    have hAddLeft : i + native_nat_to_int w = i + runW := by
      simpa [Int.add_comm] using hAdd
    exact (Int.add_left_cancel hAddLeft).symm
  subst runW
  have hRunXEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunX]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof x
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
      hBvTypeNe hXEoBv hRunXEoBv
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.sign_extend (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hwNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hwNonneg
  have hWidthNonneg :
      native_zleq 0 (native_zplus (native_nat_to_int w) i) = true := by
    have hAdd : 0 <= native_nat_to_int w + i := Int.add_nonneg hw hi
    have hsimpa := hAdd
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hWidthComm :
      native_zplus i (native_nat_to_int w) =
        native_zplus (native_nat_to_int w) i := by
    simp [SmtEval.native_zplus, Int.add_comm]
  have hXRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (SmtValue.Binary (native_nat_to_int w) runN) := by
    rw [hRunX] at hXRel
    rw [show
        __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
          SmtTerm.Binary (native_nat_to_int w) runN by
      rfl] at hXRel
    rw [__smtx_model_eval.eq_5] at hXRel
    exact hXRel
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) runN :=
    EvaluateProofInternal.smt_value_rel_binary_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (native_nat_to_int w) runN hXRelValue
  have hXEvalValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [hxSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt x) (by
          unfold term_has_non_none_type
          rw [hxSmtTy]
          simp)
  have hCanonOrig :
      native_zeq runN
          (native_mod_total runN
            (native_int_pow2 (native_nat_to_int w))) =
        true :=
    bitvec_payload_canonical (by simpa [hXEval] using hXEvalValueTy)
  have hPayloadEq :
      EvaluateProofInternal.eo_sign_extend_payload (native_nat_to_int w) runN =
        native_binary_uts (native_nat_to_int w) runN :=
    EvaluateProofInternal.eo_sign_extend_payload_eq_uts hwNonneg hCanonOrig
  have hRunSignToBin :
      runSign =
        __eo_to_bin
          (Term.Numeral (native_zplus (native_nat_to_int w) i))
          (Term.Numeral
            (EvaluateProofInternal.eo_sign_extend_payload (native_nat_to_int w) runN)) := by
    simpa [runSign, hRunX] using
      EvaluateProofInternal.eo_eval_sign_extend_rhs_binary_to_bin
        (native_nat_to_int w) runN i
  have hRunSignToBinTy :
      __eo_typeof
          (__eo_to_bin
            (Term.Numeral (native_zplus (native_nat_to_int w) i))
            (Term.Numeral
              (EvaluateProofInternal.eo_sign_extend_payload (native_nat_to_int w) runN))) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus (native_nat_to_int w) i)) := by
    rw [← hRunSignToBin]
    exact hRunSignEoBv
  have hRunSignEq' :
      runSign =
        Term.Binary (native_zplus (native_nat_to_int w) i)
          (native_mod_total
            (native_binary_uts (native_nat_to_int w) runN)
            (native_int_pow2
              (native_zplus (native_nat_to_int w) i))) := by
    have hToBin :=
      EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
        (EvaluateProofInternal.eo_sign_extend_payload (native_nat_to_int w) runN)
        (native_zplus (native_nat_to_int w) i)
        (native_zplus (native_nat_to_int w) i)
        hRunSignToBinTy
    rw [hRunSignToBin]
    rw [hToBin]
    rw [hPayloadEq]
  change
    __smtx_typeof
        (SmtTerm.sign_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runSign) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.sign_extend (SmtTerm.Numeral i) (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runSign))
  rw [hRunSignEq']
  constructor
  · rw [typeof_sign_extend_eq, hxSmtTy]
    simp [__smtx_typeof_sign_extend, native_ite, hi0]
    change
      SmtType.BitVec
          (native_int_to_nat (native_zplus i (native_nat_to_int w))) =
        __smtx_typeof
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total
              (native_binary_uts (native_nat_to_int w) runN)
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i))))
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg _ _ hWidthNonneg]
    rw [hWidthComm]
  · rw [show
        __smtx_model_eval M
            (SmtTerm.sign_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_model_eval_sign_extend
            (SmtValue.Numeral i)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_68, __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_zplus i (native_nat_to_int w))
          (native_mod_total
            (native_binary_uts (native_nat_to_int w) runN)
            (native_int_pow2
              (native_zplus i (native_nat_to_int w)))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total
              (native_binary_uts (native_nat_to_int w) runN)
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zplus (native_nat_to_int w) i)
              (native_mod_total
                (native_binary_uts (native_nat_to_int w) runN)
                (native_int_pow2
                  (native_zplus (native_nat_to_int w) i)))) =
          SmtValue.Binary (native_zplus (native_nat_to_int w) i)
            (native_mod_total
              (native_binary_uts (native_nat_to_int w) runN)
              (native_int_pow2
                (native_zplus (native_nat_to_int w) i))) by
      rw [__smtx_model_eval.eq_5]]
    rw [hWidthComm]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_repeat_core
    (M : SmtModel) (hM : model_wf M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.repeat n) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.repeat n) x) := by
  intro hATrans hEvalTy
  have hRepeatNN :
      term_has_non_none_type
        (SmtTerm.repeat (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases repeat_args_of_non_none hRepeatNN with
    ⟨i, w, hnSmt, hxSmtTy, hi1⟩
  have hnTerm : n = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
  subst n
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
    omega
  have hIGtZero : native_zlt 0 i = true := by
    have hlt : (0 : Int) < i := by omega
    simpa [native_zlt, SmtEval.native_zlt] using hlt
  have hi0 : native_zleq 0 i = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hi0Int
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt, SmtEval.native_zlt]
    omega
  have hIntNat :
      native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi0Int]
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
  have hRepeatEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zmult i (native_nat_to_int w))) := by
    change
      __eo_typeof_repeat (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zmult i (native_nat_to_int w)))
    rw [hXEoBv]
    simp [__eo_typeof_repeat, __eo_requires, __eo_gt, __eo_mul,
      __eo_mk_apply, native_ite, native_teq, native_not, hIGtZero]
  let runRepeat :=
    __bv_eval_concat
      (__eo_list_repeat (Term.UOp UserOp.concat)
        (__run_evaluate x) (Term.Numeral i))
  have hRunRepeatEq :
      __run_evaluate
          (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x) =
        runRepeat := by
    dsimp [runRepeat]
    simp [__run_evaluate, __eo_is_z, __eo_is_z_internal,
      __eo_is_neg, __eo_not, __eo_and, __eo_ite, native_ite,
      native_teq, native_and, native_not, SmtEval.native_not, hiNotNeg]
  have hRunRepeatNe : runRepeat ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
            (__run_evaluate
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))) =
        Term.Bool at hEvalTy
    rw [hRunRepeatEq, hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
          runRepeat ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runRepeat <;>
      simp [__eo_mk_apply, hRun] at hMk hRunRepeatNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
            runRepeat) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))
            (__run_evaluate
              (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x))) =
        Term.Bool at hEvalTy
    rw [hRunRepeatEq] at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunRepeatEoBv :
      __eo_typeof runRepeat =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zmult i (native_nat_to_int w))) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x)
        runRepeat hEvalEqTy
    exact hEq.symm.trans hRepeatEoType
  dsimp [runRepeat] at hRunRepeatEoBv
  rcases EvaluateProofInternal.eo_repeat_literal_arg_binary_of_typeof_bitvec
      (__run_evaluate x) i (native_zmult i (native_nat_to_int w))
      hi1 hRunRepeatEoBv with
    ⟨runW, runN, repM, hRunX, hRunWNonneg, hWidthEq,
      hRunRepeatTerm, hRepCanon⟩
  have hRunW : runW = native_nat_to_int w := by
    have hMul :
        i * native_nat_to_int w = i * runW := by
      simpa [native_zmult, SmtEval.native_zmult] using hWidthEq
    have hiNe : i ≠ 0 := by
      intro hiZero
      have hBad : (1 : Int) <= 0 := by
        simpa [hiZero] using hi
      exact (by decide : ¬ (1 : Int) <= 0) hBad
    have hEq : native_nat_to_int w = runW :=
      (Int.mul_eq_mul_left_iff hiNe).mp hMul
    exact hEq.symm
  subst runW
  have hRunXEoBv :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunX]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof x
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
      hBvTypeNe hXEoBv hRunXEoBv
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  have hXRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (SmtValue.Binary (native_nat_to_int w) runN) := by
    rw [hRunX] at hXRel
    rw [show
        __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
          SmtTerm.Binary (native_nat_to_int w) runN by
      rfl] at hXRel
    rw [__smtx_model_eval.eq_5] at hXRel
    exact hXRel
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) runN :=
    EvaluateProofInternal.smt_value_rel_binary_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (native_nat_to_int w) runN hXRelValue
  have hWidthNonneg :
      native_zleq 0 (native_zmult i (native_nat_to_int w)) = true := by
    have hw : 0 <= native_nat_to_int w := by
      simp [Smtm.native_nat_to_int]
    have hMul : 0 <= i * native_nat_to_int w :=
      Int.mul_nonneg hi0Int hw
    have hsimpa := hMul
    try simp [native_zleq, SmtEval.native_zleq, native_zmult, SmtEval.native_zmult] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hListRun :
      __eo_list_repeat (Term.UOp UserOp.concat)
          (Term.Binary (native_nat_to_int w) runN) (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat)
          (Term.Binary (native_nat_to_int w) runN)
          (native_int_to_nat i) := by
    simp [__eo_list_repeat, native_ite, hiNotNeg]
  rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary
      (native_nat_to_int w) runN hRunWNonneg (native_int_to_nat i) with
    ⟨repM', hRepeatTerm', hRepeatEvalRec, _hRepCanon'⟩
  have hRunRepeatTerm' :
      __bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat)
            (__run_evaluate x) (Term.Numeral i)) =
        Term.Binary (native_zmult i (native_nat_to_int w)) repM' := by
    rw [hRunX, hListRun]
    simpa [hIntNat] using hRepeatTerm'
  have hRepMEq : repM' = repM := by
    rw [hRunRepeatTerm'] at hRunRepeatTerm
    cases hRunRepeatTerm
    rfl
  have hRepeatEvalRec' :
      __smtx_repeat_rec (native_int_to_nat i)
          (SmtValue.Binary (native_nat_to_int w) runN) =
        SmtValue.Binary (native_zmult i (native_nat_to_int w)) repM := by
    rw [hRepeatEvalRec, hRepMEq]
    simp [hIntNat]
  rw [hRunRepeatEq]
  change
    __smtx_typeof
        (SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runRepeat) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runRepeat))
  rw [show
      runRepeat =
        Term.Binary (native_zmult i (native_nat_to_int w)) repM by
    dsimp [runRepeat]
    exact hRunRepeatTerm]
  constructor
  · rw [typeof_repeat_eq, hxSmtTy]
    simp [__smtx_typeof_repeat, native_ite, hi1]
    change
      SmtType.BitVec
          (native_int_to_nat (native_zmult i (native_nat_to_int w))) =
        __smtx_typeof
          (SmtTerm.Binary (native_zmult i (native_nat_to_int w)) repM)
    rw [EvaluateProofInternal.smtx_typeof_binary_of_nonneg_and_canonical
      (native_zmult i (native_nat_to_int w)) repM
      hWidthNonneg hRepCanon]
  · rw [show
        __smtx_model_eval M
            (SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_model_eval_repeat
            (SmtValue.Numeral i)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_38, __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (__smtx_repeat_rec (native_int_to_nat i)
          (SmtValue.Binary (native_nat_to_int w) runN))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_zmult i (native_nat_to_int w)) repM))
    rw [hRepeatEvalRec']
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zmult i (native_nat_to_int w)) repM) =
          SmtValue.Binary (native_zmult i (native_nat_to_int w)) repM by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvand_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) := by
  intro hATrans hEvalTy
  have hBvAndNN :
      term_has_non_none_type
        (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_40]) hBvAndNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAndEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunAndNe :
      __eo_and (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
          (__eo_and (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_and (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAndNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAndEoBv :
      __eo_typeof (__eo_and (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b)
        (__eo_and (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvAndEoType
  rcases EvaluateProofInternal.eo_and_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunAndEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvand) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvand) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_and, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_40]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvand
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvand
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_and, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_and (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvor_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) := by
  intro hATrans hEvalTy
  have hBvOrNN :
      term_has_non_none_type
        (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvor) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_41]) hBvOrNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvOrEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunOrNe :
      __eo_or (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
          (__eo_or (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_or (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunOrNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunOrEoBv :
      __eo_typeof (__eo_or (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b)
        (__eo_or (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvOrEoType
  rcases EvaluateProofInternal.eo_or_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunOrEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_or, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_41]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvor
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_or, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_or (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvxor_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) := by
  intro hATrans hEvalTy
  have hBvXorNN :
      term_has_non_none_type
        (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxor) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_44]) hBvXorNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvXorEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunXorNe :
      __eo_xor (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
          (__eo_xor (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_xor (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunXorNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunXorEoBv :
      __eo_typeof (__eo_xor (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b)
        (__eo_xor (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvXorEoType
  rcases EvaluateProofInternal.eo_xor_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunXorEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvxor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvxor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_xor, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_44]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_xor, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_xor (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_concat_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b) := by
  intro hATrans hEvalTy
  have hConcatNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_concat_args_of_non_none hConcatNN with
    ⟨wa, wb, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int wa)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int wb)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hConcatEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_nat_to_int wa)
              (native_nat_to_int wb))) := by
    change __eo_typeof_concat (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral
          (native_zplus (native_nat_to_int wa)
            (native_nat_to_int wb)))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply]
  have hRunConcatNe :
      __eo_concat (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b))
          (__eo_concat (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_concat (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunConcatNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b))
            (__eo_concat (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunConcatEoBv :
      __eo_typeof (__eo_concat (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_nat_to_int wa)
              (native_nat_to_int wb))) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b)
        (__eo_concat (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hConcatEoType
  rcases EvaluateProofInternal.eo_concat_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b)
      (native_zplus (native_nat_to_int wa) (native_nat_to_int wb))
      hRunConcatEoBv with
    ⟨runWA, runA, runWB, runB, hRunA, hRunB, hRunWidth, hRunWidthNonneg⟩
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    rw [hRunA]
    intro h
    cases h
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    rw [hRunB]
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a wa hATransA hATy hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b wb hBTrans hBTy hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.concat) a b rec hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.concat) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_concat (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_concat (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  have hConcatTerm :
      __eo_to_smt
          (__eo_concat (Term.Binary runWA runA)
            (Term.Binary runWB runB)) =
        SmtTerm.Binary (native_zplus runWA runWB)
          (native_mod_total
            (native_binary_concat runWA runA runWB runB)
            (native_int_pow2 (native_zplus runWA runWB))) := by
    simp [__eo_concat, __eo_mk_binary, hRunWidthNonneg, native_ite]
    rfl
  constructor
  · rw [hConcatTerm]
    rw [typeof_concat_eq]
    rw [hATy, hBTy]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg _ _ hRunWidthNonneg]
    simp [__smtx_typeof_concat]
    rw [hRunWidth]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary runWA runA) := by
      rw [hRunA] at hARel
      rw [show __eo_to_smt (Term.Binary runWA runA) =
          SmtTerm.Binary runWA runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary runWB runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Binary runWB runB) =
          SmtTerm.Binary runWB runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary runWA runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        runWA runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary runWB runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        runWB runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_concat
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_def] <;> simp only]
    rw [hAEval, hBEval, hConcatTerm]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_zplus runWA runWB)
              (native_mod_total
                (native_binary_concat runWA runA runWB runB)
                (native_int_pow2 (native_zplus runWA runWB)))) =
          SmtValue.Binary (native_zplus runWA runWB)
            (native_mod_total
              (native_binary_concat runWA runA runWB runB)
              (native_int_pow2 (native_zplus runWA runWB))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvadd_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) := by
  intro hATrans hEvalTy
  have hBvAddNN :
      term_has_non_none_type
        (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvadd) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_48]) hBvAddNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAddEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunAddNe :
      __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
          (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAddNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAddEoBv :
      __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b)
        (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvAddEoType
  rcases EvaluateProofInternal.eo_add_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunAddEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvadd) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvadd) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_48]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_48]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvadd
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zplus runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvmul_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) := by
  intro hATrans hEvalTy
  have hBvMulNN :
      term_has_non_none_type
        (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvmul) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_49]) hBvMulNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvMulEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunMulNe :
      __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunMulNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunMulEoBv :
      __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b)
        (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvMulEoType
  rcases EvaluateProofInternal.eo_mul_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunMulEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvmul) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvmul) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_mul, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_49]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_49]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvmul
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_mul, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zmult runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvudiv_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b) := by
  intro hATrans hEvalTy
  have hBvUdivNN :
      term_has_non_none_type
        (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvudiv) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_50]) hBvUdivNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvUdivEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runBTerm := __run_evaluate b
  let widthTerm := __bv_bitwidth (__eo_typeof a)
  let maxTerm :=
    __eo_to_bin widthTerm
      (__eo_add
        (__eo_ite (__eo_is_z widthTerm)
          (__eo_ite (__eo_is_neg widthTerm) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) widthTerm))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) widthTerm))
        (Term.Numeral (-1 : native_Int)))
  let runDiv :=
    __eo_ite (__eo_eq (__eo_to_z runBTerm) (Term.Numeral 0))
      maxTerm (__eo_zdiv (__run_evaluate a) runBTerm)
  have hRunDivNe : runDiv ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b))
            runDiv) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b))
          runDiv ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runDiv <;>
      simp [__eo_mk_apply, hRun] at hMk hRunDivNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b))
            runDiv) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b))
            runDiv) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunDivEoBv :
      __eo_typeof runDiv =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) a) b)
        runDiv hEvalEqTy
    exact hEq.symm.trans hBvUdivEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hCondNe :
        __eo_eq (__eo_to_z runBTerm) (Term.Numeral 0) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_ite_cond_ne_stuck (by simpa [runDiv] using hRunDivNe)
    have hToZNe : __eo_to_z runBTerm ≠ Term.Stuck :=
      EvaluateProofInternal.eo_eq_left_ne_stuck hCondNe
    simpa [runBTerm] using EvaluateProofInternal.eo_to_z_arg_ne_stuck hToZNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvudiv) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runDiv) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runDiv))
  cases hRunB : __run_evaluate b
  case Binary runWB runB =>
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary runWB runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Binary runWB runB) =
          SmtTerm.Binary runWB runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hBEvalRel :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary runWB runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b)) runWB runB hBRelValue
    by_cases hRunBZero : runB = 0
    · subst runB
      have hMaxType :
          __eo_typeof
              (__eo_to_bin (Term.Numeral (native_nat_to_int w))
                (Term.Numeral (native_binary_max (native_nat_to_int w)))) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runDiv, runBTerm, maxTerm, widthTerm] at hRunDivEoBv
        rw [hRunB] at hRunDivEoBv
        have hsimpa := hRunDivEoBv
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_eq, __eo_ite, __eo_add, __eo_pow, __eo_is_z, __eo_is_z_internal, __eo_is_neg, native_binary_max, native_teq, native_ite, SmtEval.native_zlt, Smtm.native_nat_to_int] at hsimpa ⊢
        exact hsimpa
      have hRunDivEq :
          runDiv =
            Term.Binary (native_nat_to_int w)
              (native_mod_total (native_binary_max (native_nat_to_int w))
                (native_int_pow2 (native_nat_to_int w))) := by
        have hToBin :=
          EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
            (native_binary_max (native_nat_to_int w))
            (native_nat_to_int w) (native_nat_to_int w) hMaxType
        dsimp [runDiv, runBTerm, maxTerm, widthTerm]
        rw [hRunB]
        have hsimpa := hToBin
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_eq, __eo_ite, __eo_add, __eo_pow, __eo_is_z, __eo_is_z_internal, __eo_is_neg, native_binary_max, native_teq, native_ite, SmtEval.native_zlt, Smtm.native_nat_to_int] at hsimpa ⊢
        exact hsimpa
      rw [hRunDivEq]
      constructor
      · rw [show
            __smtx_typeof
                (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_50]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        change SmtType.BitVec w =
          __smtx_typeof
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total (native_binary_max (native_nat_to_int w))
                (native_int_pow2 (native_nat_to_int w))))
        rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
      · rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM a w hATy with
          ⟨evalA, hAEval, _hARange⟩
        rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM b w hBTy with
          ⟨evalB, hBEvalTyped, _hBRange⟩
        rw [hBEvalRel] at hBEvalTyped
        cases hBEvalTyped
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvudiv
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_50]]
        rw [hAEval, hBEvalRel]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_ite (native_zeq 0 0)
                  (native_binary_max (native_nat_to_int w))
                  (native_div_total evalA 0))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_binary_max (native_nat_to_int w))
                  (native_int_pow2 (native_nat_to_int w)))))
        simp [SmtEval.native_zeq, native_ite]
        rw [__smtx_model_eval.eq_5]
        exact RuleProofs.smt_value_rel_refl _
    · have hZeroFalse : native_zeq 0 runB = false := by
        simp [native_zeq, SmtEval.native_zeq]
        exact fun h => hRunBZero h.symm
      have hRunBZeroSym : ¬ 0 = runB := by
        intro h
        exact hRunBZero h.symm
      have hZDivTy :
          __eo_typeof
              (__eo_zdiv (__run_evaluate a) (Term.Binary runWB runB)) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runDiv, runBTerm] at hRunDivEoBv
        rw [hRunB] at hRunDivEoBv
        simpa [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite,
          hRunBZero, hRunBZeroSym, hZeroFalse] using hRunDivEoBv
      rcases EvaluateProofInternal.eo_zdiv_args_binary_of_typeof_bitvec
          (__run_evaluate a) (Term.Binary runWB runB)
          (native_nat_to_int w) hZDivTy with
        ⟨runA, runB', hRunA, hRunB'⟩
      cases hRunB'
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        rw [hRunA]
        rfl
      have hBvTypeNe :
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) ≠
            Term.Stuck := by
        intro h
        cases h
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)))
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hBvTypeNe hAEoBv hRunAEoType
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.bvudiv) a b rec hATransA hAProgTy with
        ⟨_hASameTy, hARel⟩
      constructor
      · rw [show
            __eo_to_smt runDiv =
              SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total (native_div_total runA runB)
                  (native_int_pow2 (native_nat_to_int w))) by
          dsimp [runDiv, runBTerm, maxTerm, widthTerm]
          rw [hRunA, hRunB]
          simp [__eo_to_z, __eo_eq, __eo_ite, __eo_zdiv, __eo_requires,
            hRunBZeroSym, hZeroFalse, native_ite, native_teq, native_not]
          rfl]
        rw [show
            __smtx_typeof
                (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_50]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Binary (native_nat_to_int w) runA) := by
          rw [hRunA] at hARel
          rw [show
              __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
                SmtTerm.Binary (native_nat_to_int w) runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_5] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Binary (native_nat_to_int w) runA :=
          EvaluateProofInternal.smt_value_rel_binary_eq
            (__smtx_model_eval M (__eo_to_smt a))
            (native_nat_to_int w) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvudiv (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvudiv
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_50]]
        rw [hAEval, hBEvalRel]
        rw [show
            __eo_to_smt runDiv =
              SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total (native_div_total runA runB)
                  (native_int_pow2 (native_nat_to_int w))) by
          dsimp [runDiv, runBTerm, maxTerm, widthTerm]
          rw [hRunA, hRunB]
          simp [__eo_to_z, __eo_eq, __eo_ite, __eo_zdiv, __eo_requires,
            hRunBZeroSym, hZeroFalse, native_ite, native_teq, native_not]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_ite (native_zeq runB 0)
                  (native_binary_max (native_nat_to_int w))
                  (native_div_total runA runB))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total (native_div_total runA runB)
                  (native_int_pow2 (native_nat_to_int w)))))
        have hZeroFalse' : native_zeq runB 0 = false := by
          simp [native_zeq, SmtEval.native_zeq, hRunBZero]
        simp [hZeroFalse', native_ite]
        rw [__smtx_model_eval.eq_5]
        exact RuleProofs.smt_value_rel_refl _
  case Numeral runN =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_2] at hRunBSmtTy
    cases hRunBSmtTy
  case Rational runQ =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_3] at hRunBSmtTy
    cases hRunBSmtTy
  case String runS =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_4] at hRunBSmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunBSmtTy
  all_goals
    have hRunDivStuck : runDiv = Term.Stuck := by
      dsimp [runDiv, runBTerm]
      rw [hRunB]
      simp [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite]
    exact False.elim (hRunDivNe hRunDivStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvurem_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b) := by
  intro hATrans hEvalTy
  have hBvUremNN :
      term_has_non_none_type
        (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvurem) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_51]) hBvUremNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvUremEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runBTerm := __run_evaluate b
  let runATerm := __run_evaluate a
  let runRem :=
    __eo_ite (__eo_eq (__eo_to_z runBTerm) (Term.Numeral 0))
      runATerm (__eo_zmod runATerm runBTerm)
  have hRunRemNe : runRem ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b))
            runRem) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b))
          runRem ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runRem <;>
      simp [__eo_mk_apply, hRun] at hMk hRunRemNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b))
            runRem) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b))
            runRem) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunRemEoBv :
      __eo_typeof runRem =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b)
        runRem hEvalEqTy
    exact hEq.symm.trans hBvUremEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hCondNe :
        __eo_eq (__eo_to_z runBTerm) (Term.Numeral 0) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_ite_cond_ne_stuck (by simpa [runRem] using hRunRemNe)
    have hToZNe : __eo_to_z runBTerm ≠ Term.Stuck :=
      EvaluateProofInternal.eo_eq_left_ne_stuck hCondNe
    simpa [runBTerm] using EvaluateProofInternal.eo_to_z_arg_ne_stuck hToZNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvurem) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runRem) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runRem))
  cases hRunB : __run_evaluate b
  case Binary runWB runB =>
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary runWB runB) := by
      rw [hRunB] at hBRel
      rw [show __eo_to_smt (Term.Binary runWB runB) =
          SmtTerm.Binary runWB runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hBEvalRel :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary runWB runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b)) runWB runB hBRelValue
    by_cases hRunBZero : runB = 0
    · subst runB
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runRem, runBTerm, runATerm] at hRunRemEoBv
        rw [hRunB] at hRunRemEoBv
        simpa [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite]
          using hRunRemEoBv
      have hBvTypeNe :
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) ≠
            Term.Stuck := by
        intro h
        cases h
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)))
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hBvTypeNe hAEoBv hRunAEoType
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.bvurem) a b rec hATransA hAProgTy with
        ⟨hASameTy, hARel⟩
      constructor
      · rw [show __eo_to_smt runRem =
              __eo_to_smt (__run_evaluate a) by
          dsimp [runRem, runBTerm, runATerm]
          rw [hRunB]
          simp [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite]]
        rw [show
            __smtx_typeof
                (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_51]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        exact hATy.symm.trans hASameTy
      · rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM a w hATy with
          ⟨evalA, hAEval, hARange⟩
        rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM b w hBTy with
          ⟨evalB, hBEvalTyped, _hBRange⟩
        rw [hBEvalRel] at hBEvalTyped
        cases hBEvalTyped
        have hEvalAMod :
            native_mod_total evalA (native_int_pow2 (native_nat_to_int w)) =
              evalA := by
          simpa [SmtEval.native_mod_total] using
            (Int.emod_eq_of_lt hARange.1 hARange.2)
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvurem
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_51]]
        rw [hAEval, hBEvalRel]
        rw [show __eo_to_smt runRem =
              __eo_to_smt (__run_evaluate a) by
          dsimp [runRem, runBTerm, runATerm]
          rw [hRunB]
          simp [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite]]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_ite (native_zeq 0 0) evalA
                  (native_mod_total evalA 0))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (__eo_to_smt (__run_evaluate a)))
        simp [SmtEval.native_zeq, native_ite]
        rw [hEvalAMod]
        rw [← hAEval]
        exact hARel
    · have hZeroFalse : native_zeq 0 runB = false := by
        simp [native_zeq, SmtEval.native_zeq]
        exact fun h => hRunBZero h.symm
      have hRunBZeroSym : ¬ 0 = runB := by
        intro h
        exact hRunBZero h.symm
      have hZModTy :
          __eo_typeof
              (__eo_zmod (__run_evaluate a) (Term.Binary runWB runB)) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runRem, runBTerm, runATerm] at hRunRemEoBv
        rw [hRunB] at hRunRemEoBv
        simpa [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite,
          hRunBZero, hRunBZeroSym, hZeroFalse] using hRunRemEoBv
      rcases EvaluateProofInternal.eo_zmod_args_binary_of_typeof_bitvec
          (__run_evaluate a) (Term.Binary runWB runB)
          (native_nat_to_int w) hZModTy with
        ⟨runA, runB', hRunA, hRunB'⟩
      cases hRunB'
      have hRunAEoType :
          __eo_typeof (__run_evaluate a) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        rw [hRunA]
        rfl
      have hBvTypeNe :
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) ≠
            Term.Stuck := by
        intro h
        cases h
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)))
          (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
          hBvTypeNe hAEoBv hRunAEoType
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.bvurem) a b rec hATransA hAProgTy with
        ⟨_hASameTy, hARel⟩
      constructor
      · rw [show
            __eo_to_smt runRem =
              SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total (native_mod_total runA runB)
                  (native_int_pow2 (native_nat_to_int w))) by
          dsimp [runRem, runBTerm, runATerm]
          rw [hRunA, hRunB]
          simp [__eo_to_z, __eo_eq, __eo_ite, __eo_zmod, __eo_requires,
            hRunBZeroSym, hZeroFalse, native_ite, native_teq, native_not]
          rfl]
        rw [show
            __smtx_typeof
                (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_51]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Binary (native_nat_to_int w) runA) := by
          rw [hRunA] at hARel
          rw [show
              __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
                SmtTerm.Binary (native_nat_to_int w) runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_5] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Binary (native_nat_to_int w) runA :=
          EvaluateProofInternal.smt_value_rel_binary_eq
            (__smtx_model_eval M (__eo_to_smt a))
            (native_nat_to_int w) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvurem
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_51]]
        rw [hAEval, hBEvalRel]
        rw [show
            __eo_to_smt runRem =
              SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total (native_mod_total runA runB)
                  (native_int_pow2 (native_nat_to_int w))) by
          dsimp [runRem, runBTerm, runATerm]
          rw [hRunA, hRunB]
          simp [__eo_to_z, __eo_eq, __eo_ite, __eo_zmod, __eo_requires,
            hRunBZeroSym, hZeroFalse, native_ite, native_teq, native_not]
          rfl]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_ite (native_zeq runB 0) runA
                  (native_mod_total runA runB))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total (native_mod_total runA runB)
                  (native_int_pow2 (native_nat_to_int w)))))
        have hZeroFalse' : native_zeq runB 0 = false := by
          simp [native_zeq, SmtEval.native_zeq, hRunBZero]
        simp [hZeroFalse', native_ite]
        rw [__smtx_model_eval.eq_5]
        exact RuleProofs.smt_value_rel_refl _
  case Numeral runN =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_2] at hRunBSmtTy
    cases hRunBSmtTy
  case Rational runQ =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_3] at hRunBSmtTy
    cases hRunBSmtTy
  case String runS =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_4] at hRunBSmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunBSmtTy
  all_goals
    have hRunRemStuck : runRem = Term.Stuck := by
      dsimp [runRem, runBTerm, runATerm]
      rw [hRunB]
      simp [__eo_to_z, __eo_eq, __eo_ite, native_teq, native_ite]
    exact False.elim (hRunRemNe hRunRemStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvult_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b) := by
  intro hATrans hEvalTy
  have hBvUltNN :
      term_has_non_none_type
        (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvult) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_56]) hBvUltNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvUltEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_gt (__eo_to_z (__run_evaluate b)) (__eo_to_z (__run_evaluate a))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvUltEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hToZNe : __eo_to_z (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_to_z_arg_ne_stuck hToZNe
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hToZNe : __eo_to_z (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_right_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_to_z_arg_ne_stuck hToZNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvult) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvult) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  cases hRunA : __run_evaluate a
  case Binary runWA runA =>
    cases hRunB : __run_evaluate b
    case Binary runWB runB =>
      have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Binary runWA runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Binary runWA runA) =
            SmtTerm.Binary runWA runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_5] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Binary runWB runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Binary runWB runB) =
            SmtTerm.Binary runWB runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_5] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Binary runWA runA :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt a)) runWA runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Binary runWB runB :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt b)) runWB runB hBRelValue
      constructor
      · rw [show __eo_to_smt runCmp =
            SmtTerm.Boolean (native_zlt runA runB) by
          dsimp [runCmp]
          rw [hRunA, hRunB]
          simp [__eo_to_z, __eo_gt]]
        rw [show
            __smtx_typeof
                (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2_ret
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
          rw [__smtx_typeof.eq_56]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
        rw [__smtx_typeof.eq_1]
      · rw [show
            __smtx_model_eval M
                (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvult
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_56]]
        rw [hAEval, hBEval]
        rw [show __eo_to_smt runCmp =
            SmtTerm.Boolean (native_zlt runA runB) by
          dsimp [runCmp]
          rw [hRunA, hRunB]
          simp [__eo_to_z, __eo_gt]]
        change
          RuleProofs.smt_value_rel
            (__smtx_model_eval_bvugt
              (SmtValue.Binary runWB runB) (SmtValue.Binary runWA runA))
            (__smtx_model_eval M
              (SmtTerm.Boolean (native_zlt runA runB)))
        simp [__smtx_model_eval_bvugt]
        rw [__smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_2] at hRunBSmtTy
      cases hRunBSmtTy
    case Rational runQ =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_3] at hRunBSmtTy
      cases hRunBSmtTy
    case String runS =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_4] at hRunBSmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunBSmtTy
    all_goals
      have hRunCmpStuck : runCmp = Term.Stuck := by
        dsimp [runCmp]
        rw [hRunA, hRunB]
        simp [__eo_to_z, __eo_gt]
      exact False.elim (hRunCmpNe hRunCmpStuck)
  case Numeral runN =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_2] at hRunASmtTy
    cases hRunASmtTy
  case Rational runQ =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_3] at hRunASmtTy
    cases hRunASmtTy
  case String runS =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_4] at hRunASmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunASmtTy
  all_goals
    have hRunCmpStuck : runCmp = Term.Stuck := by
      dsimp [runCmp]
      rw [hRunA]
      simp [__eo_to_z, __eo_gt]
    exact False.elim (hRunCmpNe hRunCmpStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvugt_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b) := by
  intro hATrans hEvalTy
  have hBvUgtNN :
      term_has_non_none_type
        (SmtTerm.bvugt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvugt) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_58]) hBvUgtNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvUgtEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_gt (__eo_to_z (__run_evaluate a)) (__eo_to_z (__run_evaluate b))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvUgtEoType
  have hBvUltSwapNN :
      term_has_non_none_type
        (SmtTerm.bvult (__eo_to_smt b) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [__smtx_typeof.eq_56, hBTy, hATy]
    simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
  have hBvUltSwapTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) b) a) := by
    unfold RuleProofs.eo_has_smt_translation
    exact hBvUltSwapNN
  have hBvUltSwapEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) b) a) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof b) (__eo_typeof a) = Term.Bool
    rw [hBEoBv, hAEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hBvUltSwapEvalTy :
      __eo_typeof
        (__eo_prog_evaluate
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) b) a)) =
        Term.Bool := by
    apply EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool
    · intro h
      cases h
    · exact hBvUltSwapEoType
    · change __eo_typeof runCmp = Term.Bool
      exact hRunCmpEoBool
  have recSwap :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) b) a) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A := by
    intro A hLt
    apply rec A
    have hSizeEq :
        sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) b) a) =
          sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b) := by
      have hOpSize :
          sizeOf (Term.UOp UserOp.bvult) =
            sizeOf (Term.UOp UserOp.bvugt) := by
        rfl
      change
        1 + (1 + sizeOf (Term.UOp UserOp.bvult) + sizeOf b) + sizeOf a =
          1 + (1 + sizeOf (Term.UOp UserOp.bvugt) + sizeOf a) + sizeOf b
      rw [hOpSize]
      omega
    rw [← hSizeEq]
    exact hLt
  have hSwap :=
    EvaluateProofInternal.run_evaluate_sound_apply_bvult_core M hM b a recSwap
      hBvUltSwapTrans hBvUltSwapEvalTy
  rw [show
      __run_evaluate
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) b) a) =
        runCmp by
    rfl] at hSwap
  change
    __smtx_typeof (SmtTerm.bvugt (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvugt (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  constructor
  · have hTypeEq :
        __smtx_typeof (SmtTerm.bvugt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.bvult (__eo_to_smt b) (__eo_to_smt a)) := by
      rw [__smtx_typeof.eq_58, __smtx_typeof.eq_56, hATy, hBTy]
    rw [hTypeEq]
    exact hSwap.1
  · have hEvalEq :
        __smtx_model_eval M
            (SmtTerm.bvugt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval M
            (SmtTerm.bvult (__eo_to_smt b) (__eo_to_smt a)) := by
      rw [__smtx_model_eval.eq_58, __smtx_model_eval.eq_56]
      rfl
    rw [hEvalEq]
    exact hSwap.2

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvuge_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b) := by
  intro hATrans hEvalTy
  have hBvUgeNN :
      term_has_non_none_type
        (SmtTerm.bvuge (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvuge) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_59]) hBvUgeNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvUgeEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_or
      (__eo_gt (__run_evaluate a) (__run_evaluate b))
      (__eo_eq (__run_evaluate a) (__run_evaluate b))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvUgeEoType
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_gt_left_ne_stuck hGtNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_gt_right_ne_stuck hGtNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvuge) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvuge) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvuge (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvuge (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  cases hRunA : __run_evaluate a
  case Binary runWA runA =>
    cases hRunB : __run_evaluate b
    case Binary runWB runB =>
      have hWidthEq : runWA = runWB := by
        by_cases hWidth : runWA = runWB
        · exact hWidth
        · have hRunCmpStuck : runCmp = Term.Stuck := by
            dsimp [runCmp]
            rw [hRunA, hRunB]
            simp [__eo_or, __eo_gt, __eo_eq, __eo_requires, native_ite,
              native_teq, hWidth]
          exact False.elim (hRunCmpNe hRunCmpStuck)
      subst runWB
      let cmpBool :=
        native_or (native_zlt runB runA)
          (native_veq (SmtValue.Binary runWA runA)
            (SmtValue.Binary runWA runB))
      have hRunCmpSmt :
          __eo_to_smt runCmp = SmtTerm.Boolean cmpBool := by
        dsimp [runCmp, cmpBool]
        rw [hRunA, hRunB]
        by_cases hEq : runA = runB
        · subst runB
          simp [__eo_or, __eo_gt, __eo_eq, __eo_requires, native_ite,
            native_teq, native_not, native_veq]
        · have hEq' : runB ≠ runA := by
            intro hBA
            exact hEq hBA.symm
          simp [__eo_or, __eo_gt, __eo_eq, __eo_requires, native_ite,
            native_teq, native_not, native_veq, hEq, hEq']
      have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Binary runWA runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Binary runWA runA) =
            SmtTerm.Binary runWA runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_5] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Binary runWA runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Binary runWA runB) =
            SmtTerm.Binary runWA runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_5] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Binary runWA runA :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt a)) runWA runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Binary runWA runB :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt b)) runWA runB hBRelValue
      constructor
      · rw [hRunCmpSmt]
        rw [show
            __smtx_typeof
                (SmtTerm.bvuge (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2_ret
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
          rw [__smtx_typeof.eq_59]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
        rw [__smtx_typeof.eq_1]
      · rw [show
            __smtx_model_eval M
                (SmtTerm.bvuge (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvuge
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_59]]
        rw [hAEval, hBEval]
        rw [hRunCmpSmt]
        change
          RuleProofs.smt_value_rel
            (__smtx_model_eval_bvuge
              (SmtValue.Binary runWA runA) (SmtValue.Binary runWA runB))
            (__smtx_model_eval M (SmtTerm.Boolean cmpBool))
        simp [__smtx_model_eval_bvuge, __smtx_model_eval_bvugt, cmpBool]
        rw [__smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_2] at hRunBSmtTy
      cases hRunBSmtTy
    case Rational runQ =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_3] at hRunBSmtTy
      cases hRunBSmtTy
    case String runS =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_4] at hRunBSmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunBSmtTy
    all_goals
      have hRunCmpStuck : runCmp = Term.Stuck := by
        dsimp [runCmp]
        rw [hRunA, hRunB]
        simp [__eo_or, __eo_gt, __eo_eq]
      exact False.elim (hRunCmpNe hRunCmpStuck)
  case Numeral runN =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_2] at hRunASmtTy
    cases hRunASmtTy
  case Rational runQ =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_3] at hRunASmtTy
    cases hRunASmtTy
  case String runS =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_4] at hRunASmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunASmtTy
  all_goals
    have hRunCmpStuck : runCmp = Term.Stuck := by
      dsimp [runCmp]
      rw [hRunA]
      simp [__eo_or, __eo_gt, __eo_eq]
    exact False.elim (hRunCmpNe hRunCmpStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvule_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b) := by
  intro hATrans hEvalTy
  have hBvUleNN :
      term_has_non_none_type
        (SmtTerm.bvule (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvule) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_57]) hBvUleNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvUleEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_or
      (__eo_gt (__run_evaluate b) (__run_evaluate a))
      (__eo_eq (__run_evaluate a) (__run_evaluate b))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvUleEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (__run_evaluate b) (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_gt_left_ne_stuck hGtNe
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (__run_evaluate b) (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_gt_right_ne_stuck hGtNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvule) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvule) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvule (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvule (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  cases hRunA : __run_evaluate a
  case Binary runWA runA =>
    cases hRunB : __run_evaluate b
    case Binary runWB runB =>
      have hWidthEq : runWB = runWA := by
        by_cases hWidth : runWB = runWA
        · exact hWidth
        · have hRunCmpStuck : runCmp = Term.Stuck := by
            dsimp [runCmp]
            rw [hRunA, hRunB]
            simp [__eo_or, __eo_gt, __eo_eq, __eo_requires, native_ite,
              native_teq, hWidth]
          exact False.elim (hRunCmpNe hRunCmpStuck)
      subst runWB
      let cmpBool :=
        native_or (native_zlt runA runB)
          (native_veq (SmtValue.Binary runWA runB)
            (SmtValue.Binary runWA runA))
      have hRunCmpSmt :
          __eo_to_smt runCmp = SmtTerm.Boolean cmpBool := by
        dsimp [runCmp, cmpBool]
        rw [hRunA, hRunB]
        simp [__eo_or, __eo_gt, __eo_eq, __eo_requires, native_ite,
          native_teq, native_not, native_veq]
      have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Binary runWA runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt (Term.Binary runWA runA) =
            SmtTerm.Binary runWA runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_5] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Binary runWA runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt (Term.Binary runWA runB) =
            SmtTerm.Binary runWA runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_5] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Binary runWA runA :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt a)) runWA runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Binary runWA runB :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt b)) runWA runB hBRelValue
      constructor
      · rw [hRunCmpSmt]
        rw [show
            __smtx_typeof
                (SmtTerm.bvule (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2_ret
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
          rw [__smtx_typeof.eq_57]]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
        rw [__smtx_typeof.eq_1]
      · rw [show
            __smtx_model_eval M
                (SmtTerm.bvule (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvule
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_57]]
        rw [hAEval, hBEval]
        rw [hRunCmpSmt]
        change
          RuleProofs.smt_value_rel
            (__smtx_model_eval_bvule
              (SmtValue.Binary runWA runA) (SmtValue.Binary runWA runB))
            (__smtx_model_eval M (SmtTerm.Boolean cmpBool))
        simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
          __smtx_model_eval_bvugt, cmpBool]
        rw [__smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_2] at hRunBSmtTy
      cases hRunBSmtTy
    case Rational runQ =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_3] at hRunBSmtTy
      cases hRunBSmtTy
    case String runS =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_4] at hRunBSmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunBSmtTy
    all_goals
      have hRunCmpStuck : runCmp = Term.Stuck := by
        dsimp [runCmp]
        rw [hRunA, hRunB]
        simp [__eo_or, __eo_gt, __eo_eq]
      exact False.elim (hRunCmpNe hRunCmpStuck)
  case Numeral runN =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_2] at hRunASmtTy
    cases hRunASmtTy
  case Rational runQ =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_3] at hRunASmtTy
    cases hRunASmtTy
  case String runS =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_4] at hRunASmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunASmtTy
  all_goals
    have hRunCmpStuck : runCmp = Term.Stuck := by
      dsimp [runCmp]
      rw [hRunA]
      simp [__eo_or, __eo_gt, __eo_eq]
    exact False.elim (hRunCmpNe hRunCmpStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvsgt_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b) := by
  intro hATrans hEvalTy
  have hBvSgtNN :
      term_has_non_none_type
        (SmtTerm.bvsgt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvsgt) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvSgtNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSgtEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
      (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvSgtEoType
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hSignedNe :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck hSignedNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hSignedNe :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_right_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    exact EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck hSignedNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvsgt) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvsgt) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvsgt (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvsgt (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  cases hRunA : __run_evaluate a
  case Binary runWA runA =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Binary runWA runA) =
      SmtType.BitVec w at hRunASmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunASmtTy with
      ⟨hRunWANonneg, hRunACanon, hRunWANat⟩
    have hRunWAEq : runWA = native_nat_to_int w :=
      EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWANonneg hRunWANat
    subst runWA
    cases hRunB : __run_evaluate b
    case Binary runWB runB =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Binary runWB runB) =
        SmtType.BitVec w at hRunBSmtTy
      rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunBSmtTy with
        ⟨hRunWBNonneg, hRunBCanon, hRunWBNat⟩
      have hRunWBEq : runWB = native_nat_to_int w :=
        EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWBNonneg hRunWBNat
      subst runWB
      have hRunCmpSmt :
          __eo_to_smt runCmp =
            SmtTerm.Boolean
              (native_zlt
                (native_binary_uts (native_nat_to_int w) runB)
                (native_binary_uts (native_nat_to_int w) runA)) := by
        dsimp [runCmp]
        rw [hRunA, hRunB]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runA)
          hRunWANonneg hRunACanon]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runB)
          hRunWBNonneg hRunBCanon]
        simp [__eo_gt]
      have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Binary (native_nat_to_int w) runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt
              (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_5] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Binary (native_nat_to_int w) runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt
              (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_5] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Binary (native_nat_to_int w) runA :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt a))
          (native_nat_to_int w) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Binary (native_nat_to_int w) runB :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt b))
          (native_nat_to_int w) runB hBRelValue
      constructor
      · rw [hRunCmpSmt]
        rw [show
            __smtx_typeof
                (SmtTerm.bvsgt (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2_ret
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
        rw [__smtx_typeof.eq_1]
      · rw [show
            __smtx_model_eval M
                (SmtTerm.bvsgt (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvsgt
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
        rw [hAEval, hBEval]
        rw [hRunCmpSmt]
        rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts
          hRunWANonneg hRunACanon hRunBCanon]
        rw [__smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_2] at hRunBSmtTy
      cases hRunBSmtTy
    case Rational runQ =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_3] at hRunBSmtTy
      cases hRunBSmtTy
    case String runS =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_4] at hRunBSmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunBSmtTy
    all_goals
      have hRunBNotBinary :
          ¬ ∃ wb nb : native_Int,
            __run_evaluate b = Term.Binary wb nb := by
        intro h
        rcases h with ⟨wb, nb, hEq⟩
        rw [hRunB] at hEq
        cases hEq
      have hRunBNotString :
          ¬ ∃ s : native_String,
            __run_evaluate b = Term.String s := by
        intro h
        rcases h with ⟨s, hEq⟩
        rw [hRunB] at hEq
        cases hEq
      have hSignedB :
          EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) = Term.Stuck :=
        EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
          (__run_evaluate b) hRunBNotBinary hRunBNotString
      have hRunCmpStuck : runCmp = Term.Stuck := by
        dsimp [runCmp]
        rw [hSignedB]
        cases EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) <;>
          simp [__eo_gt]
      exact False.elim (hRunCmpNe hRunCmpStuck)
  case Numeral runN =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_2] at hRunASmtTy
    cases hRunASmtTy
  case Rational runQ =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_3] at hRunASmtTy
    cases hRunASmtTy
  case String runS =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_4] at hRunASmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunASmtTy
  all_goals
    have hRunANotBinary :
        ¬ ∃ wa na : native_Int,
          __run_evaluate a = Term.Binary wa na := by
      intro h
      rcases h with ⟨wa, na, hEq⟩
      rw [hRunA] at hEq
      cases hEq
    have hRunANotString :
        ¬ ∃ s : native_String,
          __run_evaluate a = Term.String s := by
      intro h
      rcases h with ⟨s, hEq⟩
      rw [hRunA] at hEq
      cases hEq
    have hSignedA :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) = Term.Stuck :=
      EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
        (__run_evaluate a) hRunANotBinary hRunANotString
    have hRunCmpStuck : runCmp = Term.Stuck := by
      dsimp [runCmp]
      rw [hSignedA]
      simp [__eo_gt]
    exact False.elim (hRunCmpNe hRunCmpStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvslt_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b) := by
  intro hATrans hEvalTy
  have hBvSltNN :
      term_has_non_none_type
        (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvslt) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvSltNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSltEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b))
      (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvSltEoType
  have hBvSgtSwapNN :
      term_has_non_none_type
        (SmtTerm.bvsgt (__eo_to_smt b) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [hBTy, hATy]
    simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
  have hBvSgtSwapTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) b) a) := by
    unfold RuleProofs.eo_has_smt_translation
    exact hBvSgtSwapNN
  have hBvSgtSwapEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) b) a) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof b) (__eo_typeof a) = Term.Bool
    rw [hBEoBv, hAEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hBvSgtSwapEvalTy :
      __eo_typeof
        (__eo_prog_evaluate
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) b) a)) =
        Term.Bool := by
    apply EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool
    · intro h
      cases h
    · exact hBvSgtSwapEoType
    · change __eo_typeof runCmp = Term.Bool
      exact hRunCmpEoBool
  have recSwap :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) b) a) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A := by
    intro A hLt
    apply rec A
    have hSizeEq :
        sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) b) a) =
          sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b) := by
      have hOpSize :
          sizeOf (Term.UOp UserOp.bvsgt) =
            sizeOf (Term.UOp UserOp.bvslt) := by
        rfl
      change
        1 + (1 + sizeOf (Term.UOp UserOp.bvsgt) + sizeOf b) + sizeOf a =
          1 + (1 + sizeOf (Term.UOp UserOp.bvslt) + sizeOf a) + sizeOf b
      rw [hOpSize]
      omega
    rw [← hSizeEq]
    exact hLt
  have hSwap :=
    EvaluateProofInternal.run_evaluate_sound_apply_bvsgt_core M hM b a recSwap
      hBvSgtSwapTrans hBvSgtSwapEvalTy
  rw [show
      __run_evaluate
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) b) a) =
        runCmp by
    rfl] at hSwap
  change
    __smtx_typeof (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  constructor
  · have hTypeEq :
        __smtx_typeof (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof (SmtTerm.bvsgt (__eo_to_smt b) (__eo_to_smt a)) := by
      rw [show
          __smtx_typeof (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (__eo_to_smt a))
              (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
        rw [__smtx_typeof.eq_def] <;> simp only]
      rw [show
          __smtx_typeof (SmtTerm.bvsgt (__eo_to_smt b) (__eo_to_smt a)) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (__eo_to_smt b))
              (__smtx_typeof (__eo_to_smt a)) SmtType.Bool by
        rw [__smtx_typeof.eq_def] <;> simp only]
      rw [hATy, hBTy]
    rw [hTypeEq]
    exact hSwap.1
  · have hEvalEq :
        __smtx_model_eval M
            (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval M
            (SmtTerm.bvsgt (__eo_to_smt b) (__eo_to_smt a)) := by
      rw [show
          __smtx_model_eval M
              (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) =
            __smtx_model_eval_bvslt
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [show
          __smtx_model_eval M
              (SmtTerm.bvsgt (__eo_to_smt b) (__eo_to_smt a)) =
            __smtx_model_eval_bvsgt
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt a)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
      rw [__smtx_model_eval_bvslt]
    rw [hEvalEq]
    exact hSwap.2

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvsge_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b) := by
  intro hATrans hEvalTy
  have hBvSgeNN :
      term_has_non_none_type
        (SmtTerm.bvsge (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvsge) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvSgeNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSgeEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_or
      (__eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
        (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b)))
      (__eo_eq (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
        (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b)))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvSgeEoType
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
          (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b)) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    have hSignedNe :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_left_ne_stuck hGtNe
    exact EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck hSignedNe
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
          (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b)) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    have hSignedNe :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_right_ne_stuck hGtNe
    exact EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck hSignedNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvsge) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvsge) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvsge (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvsge (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  cases hRunA : __run_evaluate a
  case Binary runWA runA =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Binary runWA runA) =
      SmtType.BitVec w at hRunASmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunASmtTy with
      ⟨hRunWANonneg, hRunACanon, hRunWANat⟩
    have hRunWAEq : runWA = native_nat_to_int w :=
      EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWANonneg hRunWANat
    subst runWA
    cases hRunB : __run_evaluate b
    case Binary runWB runB =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Binary runWB runB) =
        SmtType.BitVec w at hRunBSmtTy
      rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunBSmtTy with
        ⟨hRunWBNonneg, hRunBCanon, hRunWBNat⟩
      have hRunWBEq : runWB = native_nat_to_int w :=
        EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWBNonneg hRunWBNat
      subst runWB
      let cmpBool :=
        native_or
          (native_zlt
            (native_binary_uts (native_nat_to_int w) runB)
            (native_binary_uts (native_nat_to_int w) runA))
          (native_teq
            (Term.Numeral
              (native_binary_uts (native_nat_to_int w) runB))
            (Term.Numeral
              (native_binary_uts (native_nat_to_int w) runA)))
      have hRunCmpSmt :
          __eo_to_smt runCmp =
            SmtTerm.Boolean cmpBool := by
        dsimp [runCmp, cmpBool]
        rw [hRunA, hRunB]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runA)
          hRunWANonneg hRunACanon]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runB)
          hRunWBNonneg hRunBCanon]
        simp [__eo_or, __eo_gt, __eo_eq]
      have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Binary (native_nat_to_int w) runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt
              (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_5] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Binary (native_nat_to_int w) runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt
              (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_5] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Binary (native_nat_to_int w) runA :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt a))
          (native_nat_to_int w) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Binary (native_nat_to_int w) runB :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt b))
          (native_nat_to_int w) runB hBRelValue
      constructor
      · rw [hRunCmpSmt]
        rw [show
            __smtx_typeof
                (SmtTerm.bvsge (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2_ret
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
        rw [__smtx_typeof.eq_1]
      · rw [show
            __smtx_model_eval M
                (SmtTerm.bvsge (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvsge
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
        rw [hAEval, hBEval]
        rw [hRunCmpSmt]
        rw [EvaluateProofInternal.smtx_model_eval_bvsge_binary_eq_uts
          hRunWANonneg hRunACanon hRunBCanon]
        rw [__smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_2] at hRunBSmtTy
      cases hRunBSmtTy
    case Rational runQ =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_3] at hRunBSmtTy
      cases hRunBSmtTy
    case String runS =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_4] at hRunBSmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunBSmtTy
    all_goals
      have hRunBNotBinary :
          ¬ ∃ wb nb : native_Int,
            __run_evaluate b = Term.Binary wb nb := by
        intro h
        rcases h with ⟨wb, nb, hEq⟩
        rw [hRunB] at hEq
        cases hEq
      have hRunBNotString :
          ¬ ∃ s : native_String,
            __run_evaluate b = Term.String s := by
        intro h
        rcases h with ⟨s, hEq⟩
        rw [hRunB] at hEq
        cases hEq
      have hSignedB :
          EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) = Term.Stuck :=
        EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
          (__run_evaluate b) hRunBNotBinary hRunBNotString
      have hRunCmpStuck : runCmp = Term.Stuck := by
        dsimp [runCmp]
        rw [hSignedB]
        cases EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) <;>
          simp [__eo_or, __eo_gt, __eo_eq]
      exact False.elim (hRunCmpNe hRunCmpStuck)
  case Numeral runN =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_2] at hRunASmtTy
    cases hRunASmtTy
  case Rational runQ =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_3] at hRunASmtTy
    cases hRunASmtTy
  case String runS =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_4] at hRunASmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunASmtTy
  all_goals
    have hRunANotBinary :
        ¬ ∃ wa na : native_Int,
          __run_evaluate a = Term.Binary wa na := by
      intro h
      rcases h with ⟨wa, na, hEq⟩
      rw [hRunA] at hEq
      cases hEq
    have hRunANotString :
        ¬ ∃ s : native_String,
          __run_evaluate a = Term.String s := by
      intro h
      rcases h with ⟨s, hEq⟩
      rw [hRunA] at hEq
      cases hEq
    have hSignedA :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) = Term.Stuck :=
      EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
        (__run_evaluate a) hRunANotBinary hRunANotString
    have hRunCmpStuck : runCmp = Term.Stuck := by
      dsimp [runCmp]
      rw [hSignedA]
      simp [__eo_or, __eo_gt, __eo_eq]
    exact False.elim (hRunCmpNe hRunCmpStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvsle_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b) := by
  intro hATrans hEvalTy
  have hBvSleNN :
      term_has_non_none_type
        (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvsle) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvSleNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSleEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runCmp :=
    __eo_or
      (__eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b))
        (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a)))
      (__eo_eq (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a))
        (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b)))
  have hRunCmpNe : runCmp ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b))
          runCmp ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runCmp <;>
      simp [__eo_mk_apply, hRun] at hMk hRunCmpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b))
            runCmp) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b))
            runCmp) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunCmpEoBool :
      __eo_typeof runCmp = Term.Bool := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b)
        runCmp hEvalEqTy
    exact hEq.symm.trans hBvSleEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b))
          (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a)) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    have hSignedNe :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_left_ne_stuck hGtNe
    exact EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck hSignedNe
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    have hGtNe :
        __eo_gt (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b))
          (EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a)) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck (by simpa [runCmp] using hRunCmpNe)
    have hSignedNe :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_right_ne_stuck hGtNe
    exact EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck hSignedNe
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvsle) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvsle) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runCmp) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runCmp))
  cases hRunA : __run_evaluate a
  case Binary runWA runA =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Binary runWA runA) =
      SmtType.BitVec w at hRunASmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunASmtTy with
      ⟨hRunWANonneg, hRunACanon, hRunWANat⟩
    have hRunWAEq : runWA = native_nat_to_int w :=
      EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWANonneg hRunWANat
    subst runWA
    cases hRunB : __run_evaluate b
    case Binary runWB runB =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Binary runWB runB) =
        SmtType.BitVec w at hRunBSmtTy
      rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunBSmtTy with
        ⟨hRunWBNonneg, hRunBCanon, hRunWBNat⟩
      have hRunWBEq : runWB = native_nat_to_int w :=
        EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWBNonneg hRunWBNat
      subst runWB
      let cmpBool :=
        native_or
          (native_zlt
            (native_binary_uts (native_nat_to_int w) runA)
            (native_binary_uts (native_nat_to_int w) runB))
          (native_teq
            (Term.Numeral
              (native_binary_uts (native_nat_to_int w) runB))
            (Term.Numeral
              (native_binary_uts (native_nat_to_int w) runA)))
      have hRunCmpSmt :
          __eo_to_smt runCmp =
            SmtTerm.Boolean cmpBool := by
        dsimp [runCmp, cmpBool]
        rw [hRunA, hRunB]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runA)
          hRunWANonneg hRunACanon]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runB)
          hRunWBNonneg hRunBCanon]
        simp [__eo_or, __eo_gt, __eo_eq]
      have hARelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (SmtValue.Binary (native_nat_to_int w) runA) := by
        rw [hRunA] at hARel
        rw [show __eo_to_smt
              (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
          rfl] at hARel
        rw [__smtx_model_eval.eq_5] at hARel
        exact hARel
      have hBRelValue :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (SmtValue.Binary (native_nat_to_int w) runB) := by
        rw [hRunB] at hBRel
        rw [show __eo_to_smt
              (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
          rfl] at hBRel
        rw [__smtx_model_eval.eq_5] at hBRel
        exact hBRel
      have hAEval :
          __smtx_model_eval M (__eo_to_smt a) =
            SmtValue.Binary (native_nat_to_int w) runA :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt a))
          (native_nat_to_int w) runA hARelValue
      have hBEval :
          __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Binary (native_nat_to_int w) runB :=
        EvaluateProofInternal.smt_value_rel_binary_eq
          (__smtx_model_eval M (__eo_to_smt b))
          (native_nat_to_int w) runB hBRelValue
      constructor
      · rw [hRunCmpSmt]
        rw [show
            __smtx_typeof
                (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2_ret
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq]
        rw [__smtx_typeof.eq_1]
      · rw [show
            __smtx_model_eval M
                (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvsle
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
        rw [hAEval, hBEval]
        rw [hRunCmpSmt]
        rw [EvaluateProofInternal.smtx_model_eval_bvsle_binary_eq_uts
          hRunWANonneg hRunACanon hRunBCanon]
        rw [__smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_2] at hRunBSmtTy
      cases hRunBSmtTy
    case Rational runQ =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_3] at hRunBSmtTy
      cases hRunBSmtTy
    case String runS =>
      rw [hRunB] at hRunBSmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunBSmtTy
      rw [__smtx_typeof.eq_4] at hRunBSmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunBSmtTy
    all_goals
      have hRunBNotBinary :
          ¬ ∃ wb nb : native_Int,
            __run_evaluate b = Term.Binary wb nb := by
        intro h
        rcases h with ⟨wb, nb, hEq⟩
        rw [hRunB] at hEq
        cases hEq
      have hRunBNotString :
          ¬ ∃ s : native_String,
            __run_evaluate b = Term.String s := by
        intro h
        rcases h with ⟨s, hEq⟩
        rw [hRunB] at hEq
        cases hEq
      have hSignedB :
          EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) = Term.Stuck :=
        EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
          (__run_evaluate b) hRunBNotBinary hRunBNotString
      have hRunCmpStuck : runCmp = Term.Stuck := by
        dsimp [runCmp]
        rw [hSignedB]
        cases EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) <;>
          simp [__eo_or, __eo_gt, __eo_eq]
      exact False.elim (hRunCmpNe hRunCmpStuck)
  case Numeral runN =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_2] at hRunASmtTy
    cases hRunASmtTy
  case Rational runQ =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_3] at hRunASmtTy
    cases hRunASmtTy
  case String runS =>
    rw [hRunA] at hRunASmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunASmtTy
    rw [__smtx_typeof.eq_4] at hRunASmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunASmtTy
  all_goals
    have hRunANotBinary :
        ¬ ∃ wa na : native_Int,
          __run_evaluate a = Term.Binary wa na := by
      intro h
      rcases h with ⟨wa, na, hEq⟩
      rw [hRunA] at hEq
      cases hEq
    have hRunANotString :
        ¬ ∃ s : native_String,
          __run_evaluate a = Term.String s := by
      intro h
      rcases h with ⟨s, hEq⟩
      rw [hRunA] at hEq
      cases hEq
    have hSignedA :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) = Term.Stuck :=
      EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
        (__run_evaluate a) hRunANotBinary hRunANotString
    have hRunCmpStuck : runCmp = Term.Stuck := by
      dsimp [runCmp]
      rw [hSignedA]
      cases EvaluateProofInternal.eo_signed_bv_value (__run_evaluate b) <;>
        simp [__eo_or, __eo_gt, __eo_eq]
    exact False.elim (hRunCmpNe hRunCmpStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvshl_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b) := by
  intro hATrans hEvalTy
  have hBvShlNN :
      term_has_non_none_type
        (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvshl) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvShlNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvShlEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runAmt := __eo_to_z (__run_evaluate b)
  let widthTerm := __bv_bitwidth (__eo_typeof a)
  let powAmt :=
    __eo_ite (__eo_is_z runAmt)
      (__eo_ite (__eo_is_neg runAmt) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) runAmt))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) runAmt)
  let runShift :=
    __eo_ite (__eo_gt runAmt widthTerm)
      (__eo_to_bin widthTerm (Term.Numeral 0))
      (__eo_to_bin widthTerm
        (__eo_mul (__eo_to_z (__run_evaluate a)) powAmt))
  have hRunShiftNe : runShift ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b))
            runShift) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b))
          runShift ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runShift <;>
      simp [__eo_mk_apply, hRun] at hMk hRunShiftNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b))
            runShift) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b))
            runShift) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunShiftEoBv :
      __eo_typeof runShift =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) a) b)
        runShift hEvalEqTy
    exact hEq.symm.trans hBvShlEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hCondNe : __eo_gt runAmt widthTerm ≠ Term.Stuck :=
      EvaluateProofInternal.eo_ite_cond_ne_stuck hRunShiftNe
    have hRunAmtNe : runAmt ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_left_ne_stuck hCondNe
    simpa [runAmt] using EvaluateProofInternal.eo_to_z_arg_ne_stuck hRunAmtNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvshl) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  have hWNonneg : 0 <= native_nat_to_int w := by
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  change
    __smtx_typeof (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runShift) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runShift))
  cases hRunB : __run_evaluate b
  case Binary runWB runB =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Binary runWB runB) =
      SmtType.BitVec w at hRunBSmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunBSmtTy with
      ⟨hRunWBNonneg, hRunBCanon, hRunWBNat⟩
    have hRunWBEq : runWB = native_nat_to_int w :=
      EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWBNonneg hRunWBNat
    subst runWB
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    by_cases hGt : native_zlt (native_nat_to_int w) runB = true
    · have hGtInt : native_nat_to_int w < runB := by
        simpa [native_zlt, SmtEval.native_zlt] using hGt
      have hZeroTy :
          __eo_typeof
              (__eo_to_bin (Term.Numeral (native_nat_to_int w))
                (Term.Numeral 0)) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runShift, runAmt, widthTerm, powAmt] at hRunShiftEoBv
        rw [hRunB] at hRunShiftEoBv
        have hsimpa := hRunShiftEoBv
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite, native_ite, hGt] at hsimpa ⊢
        exact hsimpa
      have hRunShiftEq :
          runShift =
            Term.Binary (native_nat_to_int w)
              (native_mod_total 0
                (native_int_pow2 (native_nat_to_int w))) := by
        have hToBin :=
          EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec 0
            (native_nat_to_int w) (native_nat_to_int w) hZeroTy
        dsimp [runShift, runAmt, widthTerm, powAmt]
        rw [hRunB]
        have hsimpa := hToBin
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite, native_ite, hGt] at hsimpa ⊢
        exact hsimpa
      rw [hRunShiftEq]
      constructor
      · rw [show
            __smtx_typeof
                (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_def] <;> simp only]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        change SmtType.BitVec w =
          __smtx_typeof
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total 0
                (native_int_pow2 (native_nat_to_int w))))
        rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
      · rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM a w hATy with
          ⟨evalA, hAEval, _hARange⟩
        have hZeroMod :
            native_mod_total
                (native_zmult evalA (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w)) =
              0 :=
          EvaluateProofInternal.native_mod_zmult_pow2_eq_zero_of_lt hWNonneg hGtInt
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvshl
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
        rw [hAEval, hBEval]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zmult evalA (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total 0
                  (native_int_pow2 (native_nat_to_int w)))))
        rw [hZeroMod]
        rw [__smtx_model_eval.eq_5]
        exact RuleProofs.smt_value_rel_refl _
    · have hGtFalse :
          native_zlt (native_nat_to_int w) runB = false := by
        cases h : native_zlt (native_nat_to_int w) runB <;> simp [h] at hGt ⊢
      have hRunANe : __run_evaluate a ≠ Term.Stuck := by
        intro hRunAStuck
        have hRunShiftStuck : runShift = Term.Stuck := by
          dsimp [runShift, runAmt, widthTerm, powAmt]
          rw [hRunAStuck, hRunB]
          simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
            __eo_mul, __eo_to_bin, native_ite, native_teq, hGtFalse]
        exact hRunShiftNe hRunShiftStuck
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
          hRunANe
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.bvshl) a b rec hATransA hAProgTy with
        ⟨hASameTy, hARel⟩
      have hRunASmtTy :
          __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
        rw [← hASameTy]
        exact hATy
      cases hRunA : __run_evaluate a
      case neg.Binary runWA runA =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.Binary runWA runA) =
          SmtType.BitVec w at hRunASmtTy
        rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunASmtTy with
          ⟨hRunWANonneg, _hRunACanon, hRunWANat⟩
        have hRunWAEq : runWA = native_nat_to_int w :=
          EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWANonneg hRunWANat
        subst runWA
        have hPowAmt : powAmt = Term.Numeral (native_int_pow2 runB) := by
          dsimp [powAmt, runAmt]
          rw [hRunB]
          exact EvaluateProofInternal.eo_int_pow2_literal_eq runB
        have hProdTy :
            __eo_typeof
                (__eo_to_bin (Term.Numeral (native_nat_to_int w))
                  (Term.Numeral
                    (native_zmult runA (native_int_pow2 runB)))) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) := by
          dsimp [runShift, runAmt, widthTerm] at hRunShiftEoBv
          rw [hRunA, hRunB, hPowAmt] at hRunShiftEoBv
          simpa [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
            __eo_mul, native_ite, native_teq, hGtFalse]
            using hRunShiftEoBv
        have hRunShiftEq :
            runShift =
              Term.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_zmult runA (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w))) := by
          have hToBin :=
            EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
              (native_zmult runA (native_int_pow2 runB))
              (native_nat_to_int w) (native_nat_to_int w) hProdTy
          dsimp [runShift, runAmt, widthTerm]
          rw [hRunA, hRunB, hPowAmt]
          simpa [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
            __eo_mul, native_ite, native_teq, hGtFalse]
            using hToBin
        rw [hRunShiftEq]
        constructor
        · rw [show
              __smtx_typeof
                  (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_typeof_bv_op_2
                  (__smtx_typeof (__eo_to_smt a))
                  (__smtx_typeof (__eo_to_smt b)) by
            rw [__smtx_typeof.eq_def] <;> simp only]
          rw [hATy, hBTy]
          simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
          change SmtType.BitVec w =
            __smtx_typeof
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_zmult runA (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w))))
          rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
        · have hARelValue :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (SmtValue.Binary (native_nat_to_int w) runA) := by
            rw [hRunA] at hARel
            rw [show
                __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
                  SmtTerm.Binary (native_nat_to_int w) runA by
              rfl] at hARel
            rw [__smtx_model_eval.eq_5] at hARel
            exact hARel
          have hAEval :
              __smtx_model_eval M (__eo_to_smt a) =
                SmtValue.Binary (native_nat_to_int w) runA :=
            EvaluateProofInternal.smt_value_rel_binary_eq
              (__smtx_model_eval M (__eo_to_smt a))
              (native_nat_to_int w) runA hARelValue
          rw [show
              __smtx_model_eval M
                  (SmtTerm.bvshl (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_model_eval_bvshl
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) by
            rw [__smtx_model_eval.eq_def] <;> simp only]
          rw [hAEval, hBEval]
          change
            RuleProofs.smt_value_rel
              (SmtValue.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_zmult runA (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w))))
              (__smtx_model_eval M
                (SmtTerm.Binary (native_nat_to_int w)
                  (native_mod_total
                    (native_zmult runA (native_int_pow2 runB))
                    (native_int_pow2 (native_nat_to_int w)))))
          rw [__smtx_model_eval.eq_5]
          exact RuleProofs.smt_value_rel_refl _
      case neg.Numeral runN =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
          at hRunASmtTy
        rw [__smtx_typeof.eq_2] at hRunASmtTy
        cases hRunASmtTy
      case neg.Rational runQ =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
          at hRunASmtTy
        rw [__smtx_typeof.eq_3] at hRunASmtTy
        cases hRunASmtTy
      case neg.String runS =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
          at hRunASmtTy
        rw [__smtx_typeof.eq_4] at hRunASmtTy
        cases hValid : native_string_valid runS <;>
          simp [native_ite, hValid] at hRunASmtTy
      all_goals
        have hRunShiftStuck : runShift = Term.Stuck := by
            dsimp [runShift, runAmt, widthTerm, powAmt]
            rw [hRunA, hRunB]
            simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
              __eo_mul, __eo_to_bin, __eo_is_z, __eo_is_z_internal,
              __eo_is_neg, native_ite, native_teq, hGtFalse]
        exact False.elim (hRunShiftNe hRunShiftStuck)
  case Numeral runN =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_2] at hRunBSmtTy
    cases hRunBSmtTy
  case Rational runQ =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_3] at hRunBSmtTy
    cases hRunBSmtTy
  case String runS =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_4] at hRunBSmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunBSmtTy
  all_goals
    have hRunShiftStuck : runShift = Term.Stuck := by
        dsimp [runShift, runAmt, widthTerm, powAmt]
        rw [hRunB]
        simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
          native_ite, native_teq]
    exact False.elim (hRunShiftNe hRunShiftStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvlshr_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b) := by
  intro hATrans hEvalTy
  have hBvLshrNN :
      term_has_non_none_type
        (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvlshr) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvLshrNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvLshrEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runAmt := __eo_to_z (__run_evaluate b)
  let widthTerm := __bv_bitwidth (__eo_typeof a)
  let powAmt :=
    __eo_ite (__eo_is_z runAmt)
      (__eo_ite (__eo_is_neg runAmt) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) runAmt))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) runAmt)
  let runShift :=
    __eo_ite (__eo_gt runAmt widthTerm)
      (__eo_to_bin widthTerm (Term.Numeral 0))
      (__eo_to_bin widthTerm
        (__eo_zdiv (__eo_to_z (__run_evaluate a)) powAmt))
  have hRunShiftNe : runShift ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b))
            runShift) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b))
          runShift ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runShift <;>
      simp [__eo_mk_apply, hRun] at hMk hRunShiftNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b))
            runShift) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b))
            runShift) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunShiftEoBv :
      __eo_typeof runShift =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) a) b)
        runShift hEvalEqTy
    exact hEq.symm.trans hBvLshrEoType
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    have hCondNe : __eo_gt runAmt widthTerm ≠ Term.Stuck :=
      EvaluateProofInternal.eo_ite_cond_ne_stuck hRunShiftNe
    have hRunAmtNe : runAmt ≠ Term.Stuck :=
      EvaluateProofInternal.eo_gt_left_ne_stuck hCondNe
    simpa [runAmt] using EvaluateProofInternal.eo_to_z_arg_ne_stuck hRunAmtNe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvlshr) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  have hWNonneg : 0 <= native_nat_to_int w := by
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  change
    __smtx_typeof (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runShift) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runShift))
  cases hRunB : __run_evaluate b
  case Binary runWB runB =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Binary runWB runB) =
      SmtType.BitVec w at hRunBSmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunBSmtTy with
      ⟨hRunWBNonneg, hRunBCanon, hRunWBNat⟩
    have hRunWBEq : runWB = native_nat_to_int w :=
      EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWBNonneg hRunWBNat
    subst runWB
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    by_cases hGt : native_zlt (native_nat_to_int w) runB = true
    · have hGtInt : native_nat_to_int w < runB := by
        simpa [native_zlt, SmtEval.native_zlt] using hGt
      have hZeroTy :
          __eo_typeof
              (__eo_to_bin (Term.Numeral (native_nat_to_int w))
                (Term.Numeral 0)) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runShift, runAmt, widthTerm, powAmt] at hRunShiftEoBv
        rw [hRunB] at hRunShiftEoBv
        have hsimpa := hRunShiftEoBv
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite, native_ite, hGt] at hsimpa ⊢
        exact hsimpa
      have hRunShiftEq :
          runShift =
            Term.Binary (native_nat_to_int w)
              (native_mod_total 0
                (native_int_pow2 (native_nat_to_int w))) := by
        have hToBin :=
          EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec 0
            (native_nat_to_int w) (native_nat_to_int w) hZeroTy
        dsimp [runShift, runAmt, widthTerm, powAmt]
        rw [hRunB]
        have hsimpa := hToBin
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite, native_ite, hGt] at hsimpa ⊢
        exact hsimpa
      rw [hRunShiftEq]
      constructor
      · rw [show
            __smtx_typeof
                (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_def] <;> simp only]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        change SmtType.BitVec w =
          __smtx_typeof
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total 0
                (native_int_pow2 (native_nat_to_int w))))
        rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
      · rcases EvaluateProofInternal.model_eval_bitvec_term_binary M hM a w hATy with
          ⟨evalA, hAEval, hARange⟩
        have hZeroMod :
            native_mod_total
                (native_div_total evalA (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w)) =
              0 :=
          EvaluateProofInternal.native_mod_div_pow2_eq_zero_of_lt hWNonneg hGtInt
            hARange.1 hARange.2
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvlshr
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
        rw [hAEval, hBEval]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_div_total evalA (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total 0
                  (native_int_pow2 (native_nat_to_int w)))))
        rw [hZeroMod]
        rw [__smtx_model_eval.eq_5]
        exact RuleProofs.smt_value_rel_refl _
    · have hGtFalse :
          native_zlt (native_nat_to_int w) runB = false := by
        cases h : native_zlt (native_nat_to_int w) runB <;> simp [h] at hGt ⊢
      have hRunANe : __run_evaluate a ≠ Term.Stuck := by
        intro hRunAStuck
        have hRunShiftStuck : runShift = Term.Stuck := by
          dsimp [runShift, runAmt, widthTerm, powAmt]
          rw [hRunAStuck, hRunB]
          simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
            __eo_zdiv, __eo_to_bin, native_ite, native_teq, hGtFalse]
        exact hRunShiftNe hRunShiftStuck
      have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
        EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
          hRunANe
      rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
          (Term.UOp UserOp.bvlshr) a b rec hATransA hAProgTy with
        ⟨hASameTy, hARel⟩
      have hRunASmtTy :
          __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
        rw [← hASameTy]
        exact hATy
      have hRunBRange :=
        Smtm.bitvec_payload_range_of_canonical hRunWBNonneg hRunBCanon
      have hPowZeroFalse :
          native_zeq 0 (native_int_pow2 runB) = false := by
        have hPowPos : 0 < native_int_pow2 runB :=
          EvaluateProofInternal.native_int_pow2_pos_of_nonneg hRunBRange.1
        simp [native_zeq, SmtEval.native_zeq]
        exact Int.ne_of_lt hPowPos
      cases hRunA : __run_evaluate a
      case neg.Binary runWA runA =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.Binary runWA runA) =
          SmtType.BitVec w at hRunASmtTy
        rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunASmtTy with
          ⟨hRunWANonneg, _hRunACanon, hRunWANat⟩
        have hRunWAEq : runWA = native_nat_to_int w :=
          EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWANonneg hRunWANat
        subst runWA
        have hPowAmt : powAmt = Term.Numeral (native_int_pow2 runB) := by
          dsimp [powAmt, runAmt]
          rw [hRunB]
          exact EvaluateProofInternal.eo_int_pow2_literal_eq runB
        have hDivTy :
            __eo_typeof
                (__eo_to_bin (Term.Numeral (native_nat_to_int w))
                  (Term.Numeral
                    (native_div_total runA (native_int_pow2 runB)))) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) := by
          dsimp [runShift, runAmt, widthTerm] at hRunShiftEoBv
          rw [hRunA, hRunB, hPowAmt] at hRunShiftEoBv
          simpa [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
            __eo_zdiv, native_ite, native_teq, hGtFalse, hPowZeroFalse]
            using hRunShiftEoBv
        have hRunShiftEq :
            runShift =
              Term.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_div_total runA (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w))) := by
          have hToBin :=
            EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
              (native_div_total runA (native_int_pow2 runB))
              (native_nat_to_int w) (native_nat_to_int w) hDivTy
          dsimp [runShift, runAmt, widthTerm]
          rw [hRunA, hRunB, hPowAmt]
          simpa [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
            __eo_zdiv, native_ite, native_teq, hGtFalse, hPowZeroFalse]
            using hToBin
        rw [hRunShiftEq]
        constructor
        · rw [show
              __smtx_typeof
                  (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_typeof_bv_op_2
                  (__smtx_typeof (__eo_to_smt a))
                  (__smtx_typeof (__eo_to_smt b)) by
            rw [__smtx_typeof.eq_def] <;> simp only]
          rw [hATy, hBTy]
          simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
          change SmtType.BitVec w =
            __smtx_typeof
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_div_total runA (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w))))
          rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
        · have hARelValue :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (SmtValue.Binary (native_nat_to_int w) runA) := by
            rw [hRunA] at hARel
            rw [show
                __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
                  SmtTerm.Binary (native_nat_to_int w) runA by
              rfl] at hARel
            rw [__smtx_model_eval.eq_5] at hARel
            exact hARel
          have hAEval :
              __smtx_model_eval M (__eo_to_smt a) =
                SmtValue.Binary (native_nat_to_int w) runA :=
            EvaluateProofInternal.smt_value_rel_binary_eq
              (__smtx_model_eval M (__eo_to_smt a))
              (native_nat_to_int w) runA hARelValue
          rw [show
              __smtx_model_eval M
                  (SmtTerm.bvlshr (__eo_to_smt a) (__eo_to_smt b)) =
                __smtx_model_eval_bvlshr
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) by
            rw [__smtx_model_eval.eq_def] <;> simp only]
          rw [hAEval, hBEval]
          change
            RuleProofs.smt_value_rel
              (SmtValue.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_div_total runA (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w))))
              (__smtx_model_eval M
                (SmtTerm.Binary (native_nat_to_int w)
                  (native_mod_total
                    (native_div_total runA (native_int_pow2 runB))
                    (native_int_pow2 (native_nat_to_int w)))))
          rw [__smtx_model_eval.eq_5]
          exact RuleProofs.smt_value_rel_refl _
      case neg.Numeral runN =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
          at hRunASmtTy
        rw [__smtx_typeof.eq_2] at hRunASmtTy
        cases hRunASmtTy
      case neg.Rational runQ =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
          at hRunASmtTy
        rw [__smtx_typeof.eq_3] at hRunASmtTy
        cases hRunASmtTy
      case neg.String runS =>
        rw [hRunA] at hRunASmtTy
        change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
          at hRunASmtTy
        rw [__smtx_typeof.eq_4] at hRunASmtTy
        cases hValid : native_string_valid runS <;>
          simp [native_ite, hValid] at hRunASmtTy
      all_goals
        have hRunShiftStuck : runShift = Term.Stuck := by
            dsimp [runShift, runAmt, widthTerm, powAmt]
            rw [hRunA, hRunB]
            simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
              __eo_zdiv, __eo_to_bin, __eo_is_z, __eo_is_z_internal,
              __eo_is_neg, native_ite, native_teq, hGtFalse]
        exact False.elim (hRunShiftNe hRunShiftStuck)
  case Numeral runN =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_2] at hRunBSmtTy
    cases hRunBSmtTy
  case Rational runQ =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_3] at hRunBSmtTy
    cases hRunBSmtTy
  case String runS =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_4] at hRunBSmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunBSmtTy
  all_goals
    have hRunShiftStuck : runShift = Term.Stuck := by
        dsimp [runShift, runAmt, widthTerm, powAmt]
        rw [hRunB]
        simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_gt, __eo_ite,
          native_ite, native_teq]
    exact False.elim (hRunShiftNe hRunShiftStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvashr_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b) := by
  intro hATrans hEvalTy
  have hBvAshrNN :
      term_has_non_none_type
        (SmtTerm.bvashr (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvashr) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hBvAshrNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAshrEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  let runShift := EvaluateProofInternal.eo_eval_bvashr_rhs a b
  have hRunShiftNe : runShift ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b))
            runShift) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b))
          runShift ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runShift <;>
      simp [__eo_mk_apply, hRun] at hMk hRunShiftNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b))
            runShift) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b))
            runShift) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunShiftEoBv :
      __eo_typeof runShift =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) a) b)
        runShift hEvalEqTy
    exact hEq.symm.trans hBvAshrEoType
  have hRunANe : __run_evaluate a ≠ Term.Stuck := by
    intro hRunAStuck
    have hSignedStuck :
        EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) = Term.Stuck := by
      rw [hRunAStuck]
      simp [EvaluateProofInternal.eo_signed_bv_value, __eo_extract, __eo_eq, __eo_ite,
        native_ite, native_teq]
    have hRunShiftStuck : runShift = Term.Stuck := by
      dsimp [runShift, EvaluateProofInternal.eo_eval_bvashr_rhs]
      rw [hSignedStuck]
      simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_zdiv,
        __eo_to_bin, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
        __eo_mk_apply, native_ite, native_teq]
    exact hRunShiftNe hRunShiftStuck
  have hRunBNe : __run_evaluate b ≠ Term.Stuck := by
    intro hRunBStuck
    have hRunShiftStuck : runShift = Term.Stuck := by
      dsimp [runShift, EvaluateProofInternal.eo_eval_bvashr_rhs]
      rw [hRunBStuck]
      simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_zdiv,
        __eo_to_bin, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
        __eo_mk_apply, native_ite, native_teq]
    exact hRunShiftNe hRunShiftStuck
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec a w hATransA hATy
      hRunANe
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec b w hBTrans hBTy
      hRunBNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
      (Term.UOp UserOp.bvashr) a b rec hATransA hAProgTy with
    ⟨hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvashr) a) b rec hBTrans hBProgTy with
    ⟨hBSameTy, hBRel⟩
  have hRunASmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate a)) = SmtType.BitVec w := by
    rw [← hASameTy]
    exact hATy
  have hRunBSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate b)) = SmtType.BitVec w := by
    rw [← hBSameTy]
    exact hBTy
  change
    __smtx_typeof (SmtTerm.bvashr (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt runShift) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvashr (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt runShift))
  cases hRunB : __run_evaluate b
  case Binary runWB runB =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Binary runWB runB) =
      SmtType.BitVec w at hRunBSmtTy
    rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunBSmtTy with
      ⟨hRunWBNonneg, hRunBCanon, hRunWBNat⟩
    have hRunWBEq : runWB = native_nat_to_int w :=
      EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWBNonneg hRunWBNat
    subst runWB
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    have hRunBRange :=
      Smtm.bitvec_payload_range_of_canonical hRunWBNonneg hRunBCanon
    have hPowZeroFalse :
        native_zeq 0 (native_int_pow2 runB) = false := by
      have hPowPos : 0 < native_int_pow2 runB :=
        EvaluateProofInternal.native_int_pow2_pos_of_nonneg hRunBRange.1
      simp [native_zeq, SmtEval.native_zeq]
      exact Int.ne_of_lt hPowPos
    cases hRunA : __run_evaluate a
    case Binary runWA runA =>
      rw [hRunA] at hRunASmtTy
      change __smtx_typeof (SmtTerm.Binary runWA runA) =
        SmtType.BitVec w at hRunASmtTy
      rcases EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts hRunASmtTy with
        ⟨hRunWANonneg, hRunACanon, hRunWANat⟩
      have hRunWAEq : runWA = native_nat_to_int w :=
        EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq hRunWANonneg hRunWANat
      subst runWA
      have hPowAmt :
          __eo_ite (__eo_is_z (Term.Numeral runB))
              (__eo_ite (__eo_is_neg (Term.Numeral runB)) (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2) (Term.Numeral runB)))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (Term.Numeral runB)) =
            Term.Numeral (native_int_pow2 runB) :=
        EvaluateProofInternal.eo_int_pow2_literal_eq runB
      have hDivTy :
          __eo_typeof
              (__eo_to_bin (Term.Numeral (native_nat_to_int w))
                (Term.Numeral
                  (native_div_total
                    (native_binary_uts (native_nat_to_int w) runA)
                    (native_int_pow2 runB)))) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) := by
        dsimp [runShift, EvaluateProofInternal.eo_eval_bvashr_rhs] at hRunShiftEoBv
        rw [hRunA, hRunB] at hRunShiftEoBv
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runA)
          hRunWANonneg hRunACanon] at hRunShiftEoBv
        simp [__eo_to_z] at hRunShiftEoBv
        rw [hPowAmt] at hRunShiftEoBv
        have hsimpa := hRunShiftEoBv
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_zdiv, hPowZeroFalse] at hsimpa ⊢
        exact hsimpa
      have hRunShiftEq :
          runShift =
            Term.Binary (native_nat_to_int w)
              (native_mod_total
                (native_div_total
                  (native_binary_uts (native_nat_to_int w) runA)
                  (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w))) := by
        have hToBin :=
          EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
            (native_div_total
              (native_binary_uts (native_nat_to_int w) runA)
              (native_int_pow2 runB))
            (native_nat_to_int w) (native_nat_to_int w) hDivTy
        dsimp [runShift, EvaluateProofInternal.eo_eval_bvashr_rhs]
        rw [hRunA, hRunB]
        rw [EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
          (w := native_nat_to_int w) (n := runA)
          hRunWANonneg hRunACanon]
        simp [__eo_to_z]
        rw [hPowAmt]
        have hsimpa := hToBin
        try simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_zdiv, hPowZeroFalse] at hsimpa ⊢
        exact hsimpa
      rw [hRunShiftEq]
      constructor
      · rw [show
            __smtx_typeof
                (SmtTerm.bvashr (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (__eo_to_smt a))
                (__smtx_typeof (__eo_to_smt b)) by
          rw [__smtx_typeof.eq_def] <;> simp only]
        rw [hATy, hBTy]
        simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
        change SmtType.BitVec w =
          __smtx_typeof
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_div_total
                  (native_binary_uts (native_nat_to_int w) runA)
                  (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w))))
        rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
      · have hARelValue :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (SmtValue.Binary (native_nat_to_int w) runA) := by
          rw [hRunA] at hARel
          rw [show
              __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
                SmtTerm.Binary (native_nat_to_int w) runA by
            rfl] at hARel
          rw [__smtx_model_eval.eq_5] at hARel
          exact hARel
        have hAEval :
            __smtx_model_eval M (__eo_to_smt a) =
              SmtValue.Binary (native_nat_to_int w) runA :=
          EvaluateProofInternal.smt_value_rel_binary_eq
            (__smtx_model_eval M (__eo_to_smt a))
            (native_nat_to_int w) runA hARelValue
        rw [show
            __smtx_model_eval M
                (SmtTerm.bvashr (__eo_to_smt a) (__eo_to_smt b)) =
              __smtx_model_eval_bvashr
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
        rw [hAEval, hBEval]
        rw [EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div
          hRunWANonneg hRunACanon hRunBCanon]
        change
          RuleProofs.smt_value_rel
            (SmtValue.Binary (native_nat_to_int w)
              (native_mod_total
                (native_div_total
                  (native_binary_uts (native_nat_to_int w) runA)
                  (native_int_pow2 runB))
                (native_int_pow2 (native_nat_to_int w))))
            (__smtx_model_eval M
              (SmtTerm.Binary (native_nat_to_int w)
                (native_mod_total
                  (native_div_total
                    (native_binary_uts (native_nat_to_int w) runA)
                    (native_int_pow2 runB))
                  (native_int_pow2 (native_nat_to_int w)))))
        rw [__smtx_model_eval.eq_5]
        exact RuleProofs.smt_value_rel_refl _
    case Numeral runN =>
      rw [hRunA] at hRunASmtTy
      change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
        at hRunASmtTy
      rw [__smtx_typeof.eq_2] at hRunASmtTy
      cases hRunASmtTy
    case Rational runQ =>
      rw [hRunA] at hRunASmtTy
      change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
        at hRunASmtTy
      rw [__smtx_typeof.eq_3] at hRunASmtTy
      cases hRunASmtTy
    case String runS =>
      rw [hRunA] at hRunASmtTy
      change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
        at hRunASmtTy
      rw [__smtx_typeof.eq_4] at hRunASmtTy
      cases hValid : native_string_valid runS <;>
        simp [native_ite, hValid] at hRunASmtTy
    all_goals
      have hSignedStuck :
          EvaluateProofInternal.eo_signed_bv_value (__run_evaluate a) = Term.Stuck := by
        rw [hRunA]
        apply EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
        · rintro ⟨w, n, hEq⟩
          cases hEq
        · rintro ⟨s, hEq⟩
          cases hEq
      have hRunShiftStuck : runShift = Term.Stuck := by
        dsimp [runShift, EvaluateProofInternal.eo_eval_bvashr_rhs]
        rw [hRunB, hSignedStuck]
        simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_zdiv,
          __eo_to_bin, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
          native_ite, native_teq]
      exact False.elim (hRunShiftNe hRunShiftStuck)
  case Numeral runN =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Numeral runN) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_2] at hRunBSmtTy
    cases hRunBSmtTy
  case Rational runQ =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.Rational runQ) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_3] at hRunBSmtTy
    cases hRunBSmtTy
  case String runS =>
    rw [hRunB] at hRunBSmtTy
    change __smtx_typeof (SmtTerm.String runS) = SmtType.BitVec w
      at hRunBSmtTy
    rw [__smtx_typeof.eq_4] at hRunBSmtTy
    cases hValid : native_string_valid runS <;>
      simp [native_ite, hValid] at hRunBSmtTy
  all_goals
    have hRunShiftStuck : runShift = Term.Stuck := by
      dsimp [runShift, EvaluateProofInternal.eo_eval_bvashr_rhs]
      rw [hRunB]
      simp [hAEoBv, __bv_bitwidth, __eo_to_z, __eo_zdiv,
        __eo_to_bin, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
        __eo_mk_apply, native_ite, native_teq]
    exact False.elim (hRunShiftNe hRunShiftStuck)

theorem EvaluateProofInternal.run_evaluate_sound_apply_bvsub_core
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) := by
  intro hATrans hEvalTy
  have hBvSubNN :
      term_has_non_none_type
        (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvsub) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_52]) hBvSubNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSubEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunSubNe :
      __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
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
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunSubEoBv :
      __eo_typeof
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b)
        (__eo_add (__run_evaluate a)
          (__eo_neg (__run_evaluate b))) hEvalEqTy
    exact hEq.symm.trans hBvSubEoType
  rcases EvaluateProofInternal.eo_add_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__eo_neg (__run_evaluate b))
      (native_nat_to_int w) hRunSubEoBv with
    ⟨runA, runNegB, hRunA, hRunNegB⟩
  rcases EvaluateProofInternal.eo_neg_arg_binary_of_eq_binary
      (__run_evaluate b) (native_nat_to_int w) runNegB hRunNegB with
    ⟨runB, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvsub) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvsub) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))))
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_neg, __eo_requires, native_ite, native_teq,
        native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_52]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      EvaluateProofInternal.smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvsub
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_52]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvsub
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_neg, __eo_requires, native_ite, native_teq,
        native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zplus runA
                  (native_mod_total (native_zneg runB)
                    (native_int_pow2 (native_nat_to_int w))))
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _
