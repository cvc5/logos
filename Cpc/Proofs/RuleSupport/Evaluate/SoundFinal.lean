module

public import Cpc.Proofs.RuleSupport.Evaluate.SoundBitVec
import all Cpc.Proofs.RuleSupport.Evaluate.SoundBitVec
public import Cpc.Proofs.RuleSupport.Evaluate.SoundArith
import all Cpc.Proofs.RuleSupport.Evaluate.SoundArith
public import Cpc.Proofs.RuleSupport.Evaluate.SoundBoolString
import all Cpc.Proofs.RuleSupport.Evaluate.SoundBoolString

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.run_evaluate_sound_apply_ite_core
    (M : SmtModel) (hM : model_wf M)
    (c t e : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) := by
  intro hATrans hEvalTy
  let whole :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e
  let runIte := __eo_ite (__run_evaluate c) (__run_evaluate t) (__run_evaluate e)
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation, whole] using hATrans
  rcases ite_args_of_non_none hIteNN with
    ⟨T, hCSmtBool, hTSmtTy, hESmtTy, hTNN⟩
  have hCTrans : RuleProofs.eo_has_smt_translation c := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hCSmtBool]
    simp
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTSmtTy]
    exact hTNN
  have hETrans : RuleProofs.eo_has_smt_translation e := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hESmtTy]
    exact hTNN
  have hCMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation c hCTrans
  have hCEoBool : __eo_typeof c = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hCMatch.symm.trans hCSmtBool)
  have hWholeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation whole hATrans
  have hWholeTypeSmtNN :
      __eo_to_smt_type (__eo_typeof whole) ≠ SmtType.None := by
    rw [← hWholeMatch]
    exact hATrans
  have hWholeTypeNe : __eo_typeof whole ≠ Term.Stuck :=
    TranslationProofs.eo_term_ne_stuck_of_smt_type_non_none
      (__eo_typeof whole) hWholeTypeSmtNN
  have hOrigIteNe :
      __eo_typeof_ite (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) ≠
        Term.Stuck := by
    have hsimpa := hWholeTypeNe
    try simp [whole] at hsimpa ⊢
    exact hsimpa
  rcases EvaluateProofInternal.eo_typeof_ite_args_of_ne_stuck
      (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) hOrigIteNe with
    ⟨_hCType, hThenElseEoEq, hThenTypeNe⟩
  have hWholeTypeEqThen :
      __eo_typeof whole = __eo_typeof t := by
    change
      __eo_typeof_ite (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) =
        __eo_typeof t
    rw [hCEoBool, ← hThenElseEoEq]
    exact EvaluateProofInternal.eo_typeof_ite_bool_same_of_ne_stuck (__eo_typeof t) hThenTypeNe
  have hElseTypeNe : __eo_typeof e ≠ Term.Stuck := by
    rw [← hThenElseEoEq]
    exact hThenTypeNe
  have hRunIteNe : runIte ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runIte) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq) whole) runIte ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runIte <;>
      simp [__eo_mk_apply, hRun] at hMk hRunIteNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runIte) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq) whole) runIte) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunIteEoType :
      __eo_typeof runIte = __eo_typeof whole := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq whole runIte hEvalEqTy
    exact hEq.symm
  rcases EvaluateProofInternal.eo_ite_selected_type_of_typeof
      (__run_evaluate c) (__run_evaluate t) (__run_evaluate e)
      (__eo_typeof whole) hRunIteEoType hWholeTypeNe with
    ⟨runCond, hRunCond, hSelectedTy⟩
  have hRunCEoBool :
      __eo_typeof (__run_evaluate c) = Term.Bool := by
    rw [hRunCond]
    rfl
  have hCProgTy : __eo_typeof (__eo_prog_evaluate c) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool c
      (RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans)
      hCEoBool hRunCEoBool
  rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg1 M
      (Term.UOp UserOp.ite) c t e rec) hCTrans hCProgTy with
    ⟨_hCSameTy, hCRel⟩
  have hCRelValue :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt c))
        (SmtValue.Boolean runCond) := by
    rw [hRunCond] at hCRel
    simpa [__smtx_model_eval] using hCRel
  have hCEval :
      __smtx_model_eval M (__eo_to_smt c) =
        SmtValue.Boolean runCond :=
    EvaluateProofInternal.smt_value_rel_boolean_eq
      (__smtx_model_eval M (__eo_to_smt c)) runCond hCRelValue
  cases runCond
  · have hRunEType :
        __eo_typeof (__run_evaluate e) = __eo_typeof e := by
      rw [hWholeTypeEqThen, hThenElseEoEq] at hSelectedTy
      exact hSelectedTy
    have hEProgTy : __eo_typeof (__eo_prog_evaluate e) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof e
        (__eo_typeof e)
        (RuleProofs.term_ne_stuck_of_has_smt_translation e hETrans)
        hElseTypeNe rfl hRunEType
    rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3 M
        (Term.UOp UserOp.ite) c t e rec) hETrans hEProgTy with
      ⟨hESameTy, hERel⟩
    change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt runIte) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M (__eo_to_smt runIte))
    dsimp [runIte]
    rw [hRunCond]
    constructor
    · change
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt (__run_evaluate e))
      calc
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) = T := by
          rw [typeof_ite_eq, hCSmtBool, hTSmtTy, hESmtTy]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        _ = __smtx_typeof (__eo_to_smt e) := hESmtTy.symm
        _ = __smtx_typeof (__eo_to_smt (__run_evaluate e)) := hESameTy
    · change
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite (Term.Boolean false) (__run_evaluate t)
                (__run_evaluate e))))
      simpa [__smtx_model_eval, __smtx_model_eval_ite, __eo_ite,
        native_ite, native_teq, hCEval] using hERel
  · have hRunTType :
        __eo_typeof (__run_evaluate t) = __eo_typeof t := by
      rw [hWholeTypeEqThen] at hSelectedTy
      exact hSelectedTy
    have hTProgTy : __eo_typeof (__eo_prog_evaluate t) = Term.Bool :=
      EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof t
        (__eo_typeof t)
        (RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans)
        hThenTypeNe rfl hRunTType
    rcases (EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg2 M
        (Term.UOp UserOp.ite) c t e rec) hTTrans hTProgTy with
      ⟨hTSameTy, hTRel⟩
    change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt runIte) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M (__eo_to_smt runIte))
    dsimp [runIte]
    rw [hRunCond]
    constructor
    · change
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) =
          __smtx_typeof (__eo_to_smt (__run_evaluate t))
      calc
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) = T := by
          rw [typeof_ite_eq, hCSmtBool, hTSmtTy, hESmtTy]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        _ = __smtx_typeof (__eo_to_smt t) := hTSmtTy.symm
        _ = __smtx_typeof (__eo_to_smt (__run_evaluate t)) := hTSameTy
    · change
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_ite (Term.Boolean true) (__run_evaluate t)
                (__run_evaluate e))))
      simpa [__smtx_model_eval, __smtx_model_eval_ite, __eo_ite,
        native_ite, native_teq, hCEval] using hTRel

theorem EvaluateProofInternal.run_evaluate_sound_apply_int_to_bv_core
    (M : SmtModel) (hM : model_wf M)
    (n x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) x) := by
  intro hATrans hEvalTy
  have hIntToBvNN :
      term_has_non_none_type
        (SmtTerm.int_to_bv (__eo_to_smt n) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases int_to_bv_args_of_non_none hIntToBvNN with
    ⟨i, hnSmt, hxSmtTy, hi0⟩
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
  have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int (hXMatch.symm.trans hxSmtTy)
  have hIntToBvEoType :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral i) := by
    change
      __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral i)
          (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral i)
    rw [hXEoInt]
    simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
      native_teq, native_not, hIGtNegOne]
  let runToBv := __eo_to_bin (Term.Numeral i) (__run_evaluate x)
  have hRunToBvNe : runToBv ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
            runToBv) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
    EvaluateProofInternal.eo_to_bin_value_ne_stuck (by simpa [runToBv] using hRunToBvNe)
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
          runToBv ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runToBv <;>
      simp [__eo_mk_apply, hRun] at hMk hRunToBvNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
            runToBv) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x))
            runToBv) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunToBvEoBv :
      __eo_typeof runToBv =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral i) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x)
        runToBv hEvalEqTy
    exact hEq.symm.trans hIntToBvEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int x hXTrans hxSmtTy hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) x rec
      hXTrans hXProgTy with
    ⟨hXSameTy, hXRel⟩
  have hRunXSmtTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate x)) = SmtType.Int := by
    rw [← hXSameTy]
    exact hxSmtTy
  cases hRunX : __run_evaluate x
  case Numeral runN =>
    have hRunToBvEq :
        runToBv =
          Term.Binary i (native_mod_total runN (native_int_pow2 i)) := by
      have hToBin :=
        EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec runN i i
          (by simpa [runToBv, hRunX] using hRunToBvEoBv)
      simpa [runToBv, hRunX] using hToBin
    change
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_typeof (__eo_to_smt runToBv) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt runToBv))
    rw [hRunToBvEq]
    change
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)) =
          __smtx_typeof
            (SmtTerm.Binary i
              (native_mod_total runN (native_int_pow2 i))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)))
          (__smtx_model_eval M
            (SmtTerm.Binary i
              (native_mod_total runN (native_int_pow2 i))))
    constructor
    · rw [typeof_int_to_bv_eq, hxSmtTy]
      simp [__smtx_typeof_int_to_bv, native_ite, hi0]
      rw [EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg _ _ hi0]
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
              (SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt x)) =
            __smtx_model_eval_int_to_bv
              (SmtValue.Numeral i)
              (__smtx_model_eval M (__eo_to_smt x)) by
        rw [smtx_eval_int_to_bv_term_eq, __smtx_model_eval.eq_2]]
      rw [hXEval]
      change
        RuleProofs.smt_value_rel
          (SmtValue.Binary i
            (native_mod_total runN (native_int_pow2 i)))
          (__smtx_model_eval M
            (SmtTerm.Binary i
              (native_mod_total runN (native_int_pow2 i))))
      rw [__smtx_model_eval.eq_5]
      exact RuleProofs.smt_value_rel_refl _
  case Binary runW runN =>
    rw [hRunX] at hRunXSmtTy
    change __smtx_typeof (SmtTerm.Binary runW runN) = SmtType.Int at hRunXSmtTy
    unfold __smtx_typeof at hRunXSmtTy
    cases hOk :
        native_and (native_zleq 0 runW)
          (native_zeq runN (native_mod_total runN (native_int_pow2 runW))) <;>
      simp [hOk, native_ite] at hRunXSmtTy
  all_goals
    exfalso
    apply hRunToBvNe
    simp [runToBv, hRunX, __eo_to_bin]

theorem EvaluateProofInternal.run_evaluate_sound_apply_extract_core
    (M : SmtModel) (hM : model_wf M)
    (hi lo x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M
    (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) := by
  intro hATrans hEvalTy
  have hExtNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    have hsimpa := hATrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases extract_args_of_non_none hExtNN with
    ⟨i, j, w, hHiSmt, hLoSmt, hxSmtTy, hj0, hji, hiw⟩
  have hHiTerm : hi = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral hi i hHiSmt
  have hLoTerm : lo = Term.Numeral j :=
    TranslationProofs.eo_to_smt_eq_numeral lo j hLoSmt
  subst hi
  subst lo
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
  have hjNonneg : 0 <= j := by
    simpa [native_zleq, SmtEval.native_zleq] using hj0
  have hLowSuccPos : native_zlt 0 (j + 1) = true := by
    have h : 0 < j + 1 := Int.lt_add_one_of_le hjNonneg
    simpa [native_zlt, SmtEval.native_zlt] using h
  have hJGtNegOne : native_zlt (-1 : native_Int) j = true := by
    have hlt : (-1 : native_Int) < j :=
      Int.lt_of_lt_of_le (by decide) hjNonneg
    simpa [native_zlt, SmtEval.native_zlt] using hlt
  have hWidthAssoc :
      native_zplus (native_zplus i 1) (native_zneg j) =
        native_zplus (native_zplus i (native_zneg j)) 1 := by
    simp [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have hWidthPos :
      native_zlt 0 (native_zplus (native_zplus i (native_zneg j)) 1) =
        true := by
    simpa [hWidthAssoc] using hji
  have hWidthPosRaw : native_zlt 0 (i + -j + 1) = true := by
    simpa [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.add_assoc] using hWidthPos
  have hWidthNonneg :
      native_zleq 0 (native_zplus (native_zplus i (native_zneg j)) 1) =
        true := by
    have hPos :
        (0 : native_Int) <
          native_zplus (native_zplus i (native_zneg j)) 1 := by
      simpa [native_zlt, SmtEval.native_zlt] using hWidthPos
    simpa [native_zleq, SmtEval.native_zleq] using Int.le_of_lt hPos
  have hExtractEoType :
      __eo_typeof
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_zplus i (native_zneg j)) 1)) := by
      change
        __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral i)
          (Term.UOp UserOp.Int) (Term.Numeral j) (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral
              (native_zplus (native_zplus i (native_zneg j)) 1))
      rw [hXEoBv]
      simp [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt, __eo_requires,
        __eo_mk_apply, hLowSuccPos, hJGtNegOne, hWidthNonneg, hWidthPos,
        hWidthPosRaw, hiw, native_ite, native_teq, native_not, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
  let runExt :=
    __eo_extract (__run_evaluate x) (Term.Numeral j) (Term.Numeral i)
  have hRunExtNe : runExt ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
                x))
            runExt) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
    EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [runExt] using hRunExtNe)
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
              x))
          runExt ≠
        Term.Stuck := by
    intro hMk
    cases hRun : runExt <;>
      simp [__eo_mk_apply, hRun] at hMk hRunExtNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
                x))
            runExt) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j))
                x))
            runExt) =
        Term.Bool at hEvalTy
    rw [EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunExtEoBv :
      __eo_typeof runExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    have hEq :=
      EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) x)
        runExt hEvalEqTy
    exact hEq.symm.trans hExtractEoType
  have hXProgTy : __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
    EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec x w hXTrans hxSmtTy hRunXNe
  rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
      (Term.UOp2 UserOp2.extract (Term.Numeral i) (Term.Numeral j)) x rec
      hXTrans hXProgTy with
    ⟨_hXSameTy, hXRel⟩
  rcases EvaluateProofInternal.eo_extract_literal_arg_binary_of_typeof_bitvec
      (__run_evaluate x) i j
      (native_zplus (native_zplus i (native_zneg j)) 1)
      hj0 hji hRunExtEoBv with
    ⟨runW, runN, hRunX, _hWidthEq, hRunExtEq⟩
  have hRunExtEq' :
      runExt =
        Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
          (native_mod_total (native_binary_extract runW runN i j)
            (native_int_pow2
              (native_zplus (native_zplus i (native_zneg j)) 1))) := by
    simpa [runExt] using hRunExtEq
  have hXRelValue :
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
  change
    __smtx_typeof
        (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
          (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt runExt) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
            (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt runExt))
  rw [hRunExtEq']
  change
    __smtx_typeof
        (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
          (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Binary
            (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract runW runN i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
            (__eo_to_smt x)))
        (__smtx_model_eval M
          (SmtTerm.Binary
            (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract runW runN i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))))
  constructor
  · rw [typeof_extract_eq, hxSmtTy]
    simp [__smtx_typeof_extract, native_ite, hj0, hji, hiw]
    rw [hWidthAssoc]
    rw [EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg _ _ hWidthNonneg]
  · rw [show
        __smtx_model_eval M
            (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral j)
              (__eo_to_smt x)) =
          __smtx_model_eval_extract
            (SmtValue.Numeral i) (SmtValue.Numeral j)
            (__smtx_model_eval M (__eo_to_smt x)) by
      rw [__smtx_model_eval.eq_37, __smtx_model_eval.eq_2,
        __smtx_model_eval.eq_2]]
    rw [hXEval]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary
          (native_zplus (native_zplus i 1) (native_zneg j))
          (native_mod_total (native_binary_extract runW runN i j)
            (native_int_pow2
              (native_zplus (native_zplus i 1) (native_zneg j)))))
        (__smtx_model_eval M
          (SmtTerm.Binary
            (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract runW runN i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))))
    rw [__smtx_model_eval.eq_5]
    rw [hWidthAssoc]
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_sound_active_apply_core
    (M : SmtModel) (hM : model_wf M)
    (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  __run_evaluate (Term.Apply f x) ≠ Term.Apply f x ->
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply f x) := by
  intro hActive hATrans hEvalTy
  cases f with
  | UOp op =>
      cases op <;> try exact False.elim (hActive rfl)
      case not =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_not_core M hM x rec hATrans hEvalTy
      case bvnot =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_bvnot_core M hM x rec hATrans hEvalTy
      case bvneg =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_bvneg_core M hM x rec hATrans hEvalTy
      case to_real =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_to_real_core M hM x rec hATrans hEvalTy
      case to_int =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_to_int_core M hM x rec hATrans hEvalTy
      case is_int =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_is_int_core M hM x rec hATrans hEvalTy
      case __eoo_neg_2 =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_uneg_core M hM x rec hATrans hEvalTy
      case abs =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_abs_core M hM x rec hATrans hEvalTy
      case int_log2 =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_int_log2_core M hM x rec hATrans hEvalTy
      case int_pow2 =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_int_pow2_core M hM x rec hATrans hEvalTy
      case int_ispow2 =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_int_ispow2_core M hM x rec hATrans hEvalTy
      case _at_bvsize =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_at_bvsize_core M hM x rec hATrans hEvalTy
      case str_len =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_len_core M hM x rec hATrans hEvalTy
      case str_to_lower =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_to_lower_core M hM x rec hATrans hEvalTy
      case str_to_upper =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_to_upper_core M hM x rec hATrans hEvalTy
      case str_rev =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_rev_core M hM x rec hATrans hEvalTy
      case str_to_code =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_to_code_core M hM x rec hATrans hEvalTy
      case str_to_int =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_to_int_core M hM x rec hATrans hEvalTy
      case str_from_code =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_from_code_core M hM x rec hActive
            hATrans hEvalTy
      case ubv_to_int =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_ubv_to_int_core M hM x rec hATrans hEvalTy
      case sbv_to_int =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_sbv_to_int_core M hM x rec hATrans hEvalTy
      case str_from_int =>
          exact EvaluateProofInternal.run_evaluate_sound_apply_str_from_int_core M hM x rec
            hATrans hEvalTy
  | UOp1 op a =>
      cases op
      case «repeat» =>
        exact EvaluateProofInternal.run_evaluate_sound_apply_repeat_core M hM a x rec
          hATrans hEvalTy
      case zero_extend =>
        exact EvaluateProofInternal.run_evaluate_sound_apply_zero_extend_core M hM a x rec
          hATrans hEvalTy
      case sign_extend =>
        exact EvaluateProofInternal.run_evaluate_sound_apply_sign_extend_core M hM a x rec
          hATrans hEvalTy
      case int_to_bv =>
        exact EvaluateProofInternal.run_evaluate_sound_apply_int_to_bv_core M hM a x rec
          hATrans hEvalTy
      all_goals
        exact False.elim (hActive rfl)
  | UOp2 op a b =>
      cases op
      case extract =>
        exact EvaluateProofInternal.run_evaluate_sound_apply_extract_core M hM a b x rec
          hATrans hEvalTy
      all_goals
        exact False.elim (hActive rfl)
  | Apply g y =>
      cases g with
      | UOp op =>
          cases op <;> try exact False.elim (hActive rfl)
          case eq =>
              rcases eq_operands_same_smt_type_of_eq_has_smt_translation y x
                hATrans with ⟨hYXTy, hYNonNone⟩
              have hYTrans : RuleProofs.eo_has_smt_translation y := by
                simpa [RuleProofs.eo_has_smt_translation] using hYNonNone
              have hXTrans : RuleProofs.eo_has_smt_translation x := by
                intro hXNone
                exact hYNonNone (hYXTy.trans hXNone)
              have hRunEqNe :
                  __run_evaluate
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) ≠
                    Term.Stuck := by
                intro hStuck
                change
                  __eo_typeof
                      (__eo_mk_apply
                        (Term.Apply (Term.UOp UserOp.eq)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.eq) y) x))
                        (__run_evaluate
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.eq) y) x))) =
                    Term.Bool at hEvalTy
                rw [hStuck] at hEvalTy
                change Term.Stuck = Term.Bool at hEvalTy
                cases hEvalTy
              have hRunYNe : __run_evaluate y ≠ Term.Stuck := by
                intro hStuck
                apply hRunEqNe
                cases hx : __run_evaluate x <;>
                  simp [__run_evaluate, hStuck, hx, __eo_ite,
                    __eo_and, __eo_is_q, __eo_is_q_internal, __eo_is_z,
                    __eo_is_z_internal, __eo_is_bin, __eo_is_bin_internal,
                    __eo_is_str, __eo_is_str_internal, __eo_is_bool,
                    __eo_is_bool_internal, __eo_mk_apply, native_ite,
                    native_and, native_not, native_teq]
              have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
                intro hStuck
                apply hRunEqNe
                cases hy : __run_evaluate y <;>
                  simp [__run_evaluate, hStuck, hy, __eo_ite,
                    __eo_and, __eo_is_q, __eo_is_q_internal, __eo_is_z,
                    __eo_is_z_internal, __eo_is_bin, __eo_is_bin_internal,
                    __eo_is_str, __eo_is_str_internal, __eo_is_bool,
                    __eo_is_bool_internal, __eo_mk_apply, native_ite,
                    native_and, native_not, native_teq]
              have hYProgTy :
                  __eo_typeof (__eo_prog_evaluate y) = Term.Bool :=
                EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation y hYTrans
                  hRunYNe
              have hXProgTy :
                  __eo_typeof (__eo_prog_evaluate x) = Term.Bool :=
                EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation x hXTrans
                  hRunXNe
              rcases EvaluateProofInternal.run_evaluate_rec_apply_apply_arg M
                  (Term.UOp UserOp.eq) y x rec hYTrans hYProgTy with
                ⟨hYSameTy, hYRel⟩
              rcases EvaluateProofInternal.run_evaluate_rec_apply_arg M
                  (Term.Apply (Term.UOp UserOp.eq) y) x rec hXTrans
                  hXProgTy with
                ⟨hXSameTy, hXRel⟩
              have hRunEqTy :
                  __smtx_typeof (__eo_to_smt (__run_evaluate y)) =
                    __smtx_typeof (__eo_to_smt (__run_evaluate x)) := by
                rw [← hYSameTy, ← hXSameTy]
                exact hYXTy
              have hRunNonNone :
                  __smtx_typeof (__eo_to_smt (__run_evaluate y)) ≠
                    SmtType.None := by
                intro hNone
                exact hYNonNone (hYSameTy.trans hNone)
              constructor
              · have hOrigTy :
                    __smtx_typeof
                        (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x)) =
                      SmtType.Bool := by
                  rw [Smtm.typeof_eq_eq]
                  exact (RuleProofs.smtx_typeof_eq_bool_iff
                    (__smtx_typeof (__eo_to_smt y))
                    (__smtx_typeof (__eo_to_smt x))).mpr
                      ⟨hYXTy, hYNonNone⟩
                have hEvalTy :
                    __smtx_typeof
                        (__eo_to_smt
                          (__run_evaluate
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.eq) y) x))) =
                      SmtType.Bool :=
                  EvaluateProofInternal.run_evaluate_apply_eq_smt_type_bool y x hRunEqTy
                    hRunNonNone
                simpa [eo_to_smt_eq_eq] using hOrigTy.trans hEvalTy.symm
              · rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
                have hEqRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval_eq
                        (__smtx_model_eval M (__eo_to_smt y))
                        (__smtx_model_eval M (__eo_to_smt x)))
                      (__smtx_model_eval_eq
                        (__smtx_model_eval M
                          (__eo_to_smt (__run_evaluate y)))
                        (__smtx_model_eval M
                          (__eo_to_smt (__run_evaluate x)))) :=
                  EvaluateProofInternal.smt_value_rel_model_eval_eq_congr
                    (__smtx_model_eval M (__eo_to_smt y))
                    (__smtx_model_eval M (__eo_to_smt x))
                    (__smtx_model_eval M
                      (__eo_to_smt (__run_evaluate y)))
                    (__smtx_model_eval M
                      (__eo_to_smt (__run_evaluate x)))
                    hYRel hXRel
                have hEvalRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval_eq
                        (__smtx_model_eval M
                          (__eo_to_smt (__run_evaluate y)))
                        (__smtx_model_eval M
                          (__eo_to_smt (__run_evaluate x))))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (__run_evaluate
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.eq) y) x)))) :=
                  EvaluateProofInternal.run_evaluate_apply_eq_value_rel M y x hRunEqTy
                    hRunNonNone
                exact RuleProofs.smt_value_rel_trans _ _ _ hEqRel
                  hEvalRel
          case and =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_and_core M hM y x rec hATrans hEvalTy
          case or =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_or_core M hM y x rec hATrans hEvalTy
          case imp =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_imp_core M hM y x rec hATrans hEvalTy
          case xor =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_xor_core M hM y x rec hATrans hEvalTy
          case str_concat =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_str_concat_core M hM y x rec hATrans hEvalTy
          case str_at =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_str_at_core M hM y x rec hATrans hEvalTy
          case str_prefixof =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_str_prefixof_core M hM y x rec
                hATrans hEvalTy
          case str_suffixof =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_str_suffixof_core M hM y x rec
                hATrans hEvalTy
          case str_contains =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_str_contains_core M hM y x rec
                hATrans hEvalTy
          case str_leq =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_str_leq_core M hM y x rec
                hATrans hEvalTy
          case plus =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_plus_core M hM y x rec hATrans hEvalTy
          case neg =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_neg_core M hM y x rec hATrans hEvalTy
          case mult =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_mult_core M hM y x rec hATrans hEvalTy
          case lt =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_lt_core M hM y x rec hATrans hEvalTy
          case leq =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_leq_core M hM y x rec hATrans hEvalTy
          case gt =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_gt_core M hM y x rec hATrans hEvalTy
          case geq =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_geq_core M hM y x rec hATrans hEvalTy
          case div =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_div_core M hM y x rec hATrans hEvalTy
          case mod =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_mod_core M hM y x rec hATrans hEvalTy
          case qdiv =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_qdiv_core M hM y x rec hATrans hEvalTy
          case qdiv_total =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_qdiv_total_core M hM y x rec hATrans hEvalTy
          case div_total =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_div_total_core M hM y x rec hATrans hEvalTy
          case mod_total =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_mod_total_core M hM y x rec hATrans hEvalTy
          case bvand =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvand_core M hM y x rec hATrans hEvalTy
          case bvor =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvor_core M hM y x rec hATrans hEvalTy
          case bvxor =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvxor_core M hM y x rec hATrans hEvalTy
          case concat =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_concat_core M hM y x rec hATrans hEvalTy
          case bvadd =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvadd_core M hM y x rec hATrans hEvalTy
          case bvmul =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvmul_core M hM y x rec hATrans hEvalTy
          case bvsub =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvsub_core M hM y x rec hATrans hEvalTy
          case bvudiv =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvudiv_core M hM y x rec hATrans hEvalTy
          case bvurem =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvurem_core M hM y x rec hATrans hEvalTy
          case bvult =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvult_core M hM y x rec hATrans hEvalTy
          case bvule =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvule_core M hM y x rec hATrans hEvalTy
          case bvsle =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvsle_core M hM y x rec hATrans hEvalTy
          case bvugt =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvugt_core M hM y x rec hATrans hEvalTy
          case bvuge =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvuge_core M hM y x rec hATrans hEvalTy
          case bvshl =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvshl_core M hM y x rec hATrans hEvalTy
          case bvlshr =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvlshr_core M hM y x rec hATrans hEvalTy
          case bvashr =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvashr_core M hM y x rec hATrans hEvalTy
          case bvsgt =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvsgt_core M hM y x rec hATrans hEvalTy
          case bvslt =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvslt_core M hM y x rec hATrans hEvalTy
          case bvsge =>
              exact EvaluateProofInternal.run_evaluate_sound_apply_bvsge_core M hM y x rec hATrans hEvalTy
      | Apply h z =>
          cases h with
          | UOp op =>
              cases op <;> try exact False.elim (hActive rfl)
              case ite =>
                  exact EvaluateProofInternal.run_evaluate_sound_apply_ite_core M hM z y x rec
                    hATrans hEvalTy
              case str_substr =>
                  exact EvaluateProofInternal.run_evaluate_sound_apply_str_substr_core M hM z y x rec
                    hATrans hEvalTy
              case str_replace =>
                  exact EvaluateProofInternal.run_evaluate_sound_apply_str_replace_core M hM z y x rec
                    hATrans hEvalTy
              case str_replace_all =>
                  exact EvaluateProofInternal.run_evaluate_sound_apply_str_replace_all_core M hM z y x rec
                    hActive hATrans hEvalTy
              case str_indexof =>
                  exact EvaluateProofInternal.run_evaluate_sound_apply_str_indexof_core M hM z y x rec
                    hATrans hEvalTy
              case str_update =>
                  exact EvaluateProofInternal.run_evaluate_sound_apply_str_update_core M hM z y x rec
                    hATrans hEvalTy
          | _ =>
              exact False.elim (hActive rfl)
      | _ =>
          exact False.elim (hActive rfl)
  | _ =>
      exact False.elim (hActive rfl)

theorem EvaluateProofInternal.run_evaluate_sound_apply
    (M : SmtModel) (hM : model_wf M)
    (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M (Term.Apply f x) := by
  intro hATrans hEvalTy
  by_cases hRun : __run_evaluate (Term.Apply f x) = Term.Apply f x
  · exact EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ hRun hATrans hEvalTy
  · exact EvaluateProofInternal.run_evaluate_sound_active_apply_core M hM f x rec hRun hATrans hEvalTy

theorem EvaluateProofInternal.run_evaluate_sound_core
    (M : SmtModel) (hM : model_wf M) :
    ∀ A : Term, EvaluateProofInternal.RunEvaluateSoundGoal M A
  | Term.Apply f x =>
      EvaluateProofInternal.run_evaluate_sound_apply M hM
        f x (fun A _hA => EvaluateProofInternal.run_evaluate_sound_core M hM A)
  | Term.Stuck => by
      intro hATrans _hEvalTy
      exact False.elim
        (RuleProofs.term_ne_stuck_of_has_smt_translation _ hATrans rfl)
  | Term.UOp _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp1 _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2.extract _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2.re_loop _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_quantifiers_skolemize _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_const _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp3 _ _ _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List_nil =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List_cons =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Bool =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Boolean _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Numeral _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Rational _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.String _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Binary _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Type =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.FunType =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.Var _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.DatatypeType _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.DatatypeTypeRef _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtcAppType _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtCons _ _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtSel _ _ _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.USort _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl
  | Term.UConst _ _ =>
      EvaluateProofInternal.run_evaluate_sound_of_eq_self M _ rfl

/--
Semantic soundness target for the generated evaluator.

The command-level `evaluate` rule is premise-free and emits
`A = __run_evaluate A`.  The large theorem to prove is that, whenever the
checker accepts that emitted equality as Boolean and the input term has an SMT
translation, `__run_evaluate A` has the same SMT type as `A` and evaluates to
the same SMT value.
-/
theorem run_evaluate_sound
    (M : SmtModel) (hM : model_wf M) (A : Term) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  __smtx_typeof (__eo_to_smt A) =
      __smtx_typeof (__eo_to_smt (__run_evaluate A)) ∧
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt (__run_evaluate A))) :=
by
  exact EvaluateProofInternal.run_evaluate_sound_core M hM A

theorem run_evaluate_properties
    (M : SmtModel) (hM : model_wf M) (A : Term) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  StepRuleProperties M [] (__eo_prog_evaluate A) :=
by
  intro hATrans hEvalTy
  have hProg : __eo_prog_evaluate A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hEvalTy
  have hProgEq := EvaluateProofInternal.eo_prog_evaluate_eq_of_ne_stuck A hProg
  rcases run_evaluate_sound M hM A hATrans hEvalTy with
    ⟨hSameTy, hEvalRel⟩
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A)
          (__run_evaluate A)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type A (__run_evaluate A)
      hSameTy hATrans
  refine ⟨?_, ?_⟩
  · intro _hTrue
    rw [hProgEq]
    exact RuleProofs.eo_interprets_eq_of_rel M A (__run_evaluate A)
      hEqBool hEvalRel
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
