module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm
open SetsBasicRewritesSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem smtx_eval_map_diff_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.map_diff x y) =
      __smtx_model_eval_map_diff (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_set_singleton_term_eq'
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_singleton x) =
      __smtx_model_eval_set_singleton (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_set_empty_term_eq'
    (M : SmtModel) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.set_empty T) =
      SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem a1_trans_of_wfElem
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    RuleProofs.eo_has_smt_translation a1 := by
  unfold RuleProofs.eo_has_smt_translation
  intro hNone
  rw [hNone] at hWf
  simp [__smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

/-- smt typeof of `set_singleton (to_smt a1)` is `Set A` where `A` is the smt
    typeof of `a1`. -/
private theorem singleton_smt_type
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt a1)) =
      SmtType.Set (__smtx_typeof (__eo_to_smt a1)) := by
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof (__eo_to_smt a1))) = true :=
    type_wf_set_of_component (__smtx_typeof (__eo_to_smt a1)) hWf
  rw [smtx_typeof_set_singleton_term_eq]
  simp [__smtx_typeof_guard_wf, hSetWf, native_ite]

/-- The full SMT translation of `set.choose (set.singleton a1)`. -/
private def chooseSmt (a1 : Term) : SmtTerm :=
  SmtTerm.map_diff (SmtTerm.set_singleton (__eo_to_smt a1))
    (SmtTerm.set_empty
      (__eo_to_smt_set_elem_type
        (__smtx_typeof (SmtTerm.set_singleton (__eo_to_smt a1)))))

private theorem to_smt_choose_singleton (a1 : Term) :
    __eo_to_smt
        (Term.Apply (Term.UOp UserOp.set_choose)
          (Term.Apply (Term.UOp UserOp.set_singleton) a1)) =
      chooseSmt a1 := by
  rfl

private theorem choose_smt_type
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    __smtx_typeof (chooseSmt a1) = __smtx_typeof (__eo_to_smt a1) := by
  have hSing := singleton_smt_type a1 hWf
  have hA1NN : __smtx_typeof (__eo_to_smt a1) ≠ SmtType.None :=
    a1_trans_of_wfElem a1 hWf
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof (__eo_to_smt a1))) = true :=
    type_wf_set_of_component (__smtx_typeof (__eo_to_smt a1)) hWf
  unfold chooseSmt
  rw [hSing]
  rw [typeof_map_diff_eq, hSing]
  -- set_empty (elem_type (Set A)) typeof = Set A
  have hEmptyTy :
      __smtx_typeof
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type
              (SmtType.Set (__smtx_typeof (__eo_to_smt a1))))) =
        SmtType.Set (__smtx_typeof (__eo_to_smt a1)) := by
    rw [smtx_typeof_set_empty_term_eq]
    simp [__eo_to_smt_set_elem_type, __smtx_typeof_guard_wf, hSetWf, native_ite]
  rw [hEmptyTy]
  simp [__smtx_typeof_map_diff, native_ite, native_Teq, hA1NN]

private theorem typed___eo_prog_sets_choose_singleton_impl
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    RuleProofs.eo_has_bool_type (__eo_prog_sets_choose_singleton a1) := by
  have ha1Trans : RuleProofs.eo_has_smt_translation a1 := a1_trans_of_wfElem a1 hWf
  have ha1NS : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 ha1Trans
  let lhs := Term.Apply (Term.UOp UserOp.set_choose)
    (Term.Apply (Term.UOp UserOp.set_singleton) a1)
  let rhs := a1
  have hChooseTy := choose_smt_type a1 hWf
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = __smtx_typeof (__eo_to_smt a1) := by
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.set_choose)
            (Term.Apply (Term.UOp UserOp.set_singleton) a1))) =
      __smtx_typeof (__eo_to_smt a1)
    rw [to_smt_choose_singleton]; exact hChooseTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy]) (by rw [hLhsTy]; exact ha1Trans)
  have hProg :
      __eo_prog_sets_choose_singleton a1 =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_sets_choose_singleton a1 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.UOp UserOp.set_choose)
                (Term.Apply (Term.UOp UserOp.set_singleton) a1)))
            a1 := by
      cases a1 <;> simp [__eo_prog_sets_choose_singleton] at ha1NS ⊢
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]; exact hBoolEq

private theorem facts___eo_prog_sets_choose_singleton_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    eo_interprets M (__eo_prog_sets_choose_singleton a1) true := by
  have ha1Trans : RuleProofs.eo_has_smt_translation a1 := a1_trans_of_wfElem a1 hWf
  have ha1NS : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 ha1Trans
  let lhs := Term.Apply (Term.UOp UserOp.set_choose)
    (Term.Apply (Term.UOp UserOp.set_singleton) a1)
  let rhs := a1
  have hProg :
      __eo_prog_sets_choose_singleton a1 =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_sets_choose_singleton a1 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.UOp UserOp.set_choose)
                (Term.Apply (Term.UOp UserOp.set_singleton) a1)))
            a1 := by
      cases a1 <;> simp [__eo_prog_sets_choose_singleton] at ha1NS ⊢
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using typed___eo_prog_sets_choose_singleton_impl a1 hWf
  -- the evaluated element value v := eval a1 ; typed A and canonical
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) =
        __smtx_typeof (__eo_to_smt a1) :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1)
      (by unfold term_has_non_none_type; exact ha1Trans)
  have hA1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt a1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM a1 ha1Trans
  have hA1CanBool :
      __smtx_value_canonical (__smtx_model_eval M (__eo_to_smt a1)) = true := by
    simpa [Smtm.value_canonical_bool_eq_true] using hA1Can
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof (__eo_to_smt a1))) = true :=
    type_wf_set_of_component (__smtx_typeof (__eo_to_smt a1)) hWf
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M (chooseSmt a1) = __smtx_model_eval M (__eo_to_smt a1)
    unfold chooseSmt
    -- the set_empty type argument: elem_type (typeof (singleton a1)) = A
    rw [singleton_smt_type a1 hWf]
    have hElemTy :
        __eo_to_smt_set_elem_type
            (SmtType.Set (__smtx_typeof (__eo_to_smt a1))) =
          __smtx_typeof (__eo_to_smt a1) := rfl
    rw [hElemTy]
    rw [smtx_eval_map_diff_term_eq, smtx_eval_set_singleton_term_eq',
      smtx_eval_set_empty_term_eq']
    rw [__smtx_model_eval_set_singleton, __smtx_model_eval_map_diff]
    rw [hA1EvalTy]
    exact map_diff_singleton_empty_eq
      (__smtx_model_eval M (__eo_to_smt a1)) (__smtx_typeof (__eo_to_smt a1))
      hA1EvalTy hA1CanBool
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_sets_choose_singleton_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_choose_singleton args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_choose_singleton args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_choose_singleton args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_choose_singleton args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hWf :
                  __smtx_type_wf_component
                      (__smtx_typeof (__eo_to_smt a1)) = true := by
                have hMask :
                    argTranslationOkMasked ArgTranslationKind.wfElem a1 ∧ True := by
                  simpa [cmdTranslationOk, cArgListTranslationOkMask] using hCmdTrans
                simpa [argTranslationOkMasked] using hMask.1
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_sets_choose_singleton a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_sets_choose_singleton_impl a1 hWf)⟩
                intro _hTrue
                exact facts___eo_prog_sets_choose_singleton_impl M hM a1 hWf
              change StepRuleProperties M []
                (__eo_prog_sets_choose_singleton a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
