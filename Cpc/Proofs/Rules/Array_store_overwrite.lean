module

public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_array_store_overwrite_eq
    (t1 i1 e1 f1 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck)
    (hI1NotStuck : i1 ≠ Term.Stuck)
    (hE1NotStuck : e1 ≠ Term.Stuck)
    (hF1NotStuck : f1 ≠ Term.Stuck) :
    __eo_prog_array_store_overwrite t1 i1 e1 f1 =
      (Term.Apply
        (Term.Apply Term.eq
          (Term.Apply
            (Term.Apply
              (Term.Apply Term.store
                (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1))
        (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)) := by
  by_cases hT : t1 = Term.Stuck
  · contradiction
  · by_cases hI : i1 = Term.Stuck
    · contradiction
    · by_cases hE : e1 = Term.Stuck
      · contradiction
      · by_cases hF : f1 = Term.Stuck
        · contradiction
        · simp [__eo_prog_array_store_overwrite]

private theorem typeof_args_of_prog_array_store_overwrite_bool
    (t1 i1 e1 f1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hI1Trans : RuleProofs.eo_has_smt_translation i1)
    (hE1Trans : RuleProofs.eo_has_smt_translation e1)
    (hF1Trans : RuleProofs.eo_has_smt_translation f1)
    (h : __eo_typeof (__eo_prog_array_store_overwrite t1 i1 e1 f1) = Term.Bool) :
    __eo_typeof t1 = Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1) ∧
      __eo_typeof e1 = __eo_typeof f1 := by
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hF1NotStuck : f1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f1 hF1Trans
  rw [prog_array_store_overwrite_eq t1 i1 e1 f1 hT1NotStuck hI1NotStuck hE1NotStuck hF1NotStuck] at h
  change __eo_typeof_eq
      (__eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply Term.store
              (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1))
      (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)) =
    Term.Bool at h
  have hTypesNotStuck :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply Term.store
              (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1))
      (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)) h
  have hRhsNotStuck :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1) ≠ Term.Stuck :=
    hTypesNotStuck.2
  have hLhsNotStuck :
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply Term.store
              (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1) ≠
        Term.Stuck :=
    hTypesNotStuck.1
  have hInnerTyF :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1) =
        Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1) := by
    change __eo_typeof_store
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
        (__eo_typeof i1) (__eo_typeof f1) ≠ Term.Stuck at hLhsNotStuck
    exact RuleProofs.eo_typeof_store_not_stuck_implies_array
      (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
      (__eo_typeof i1) (__eo_typeof f1) hLhsNotStuck
  have hInnerNotStuck :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1) ≠ Term.Stuck := by
    rw [hInnerTyF]
    simp
  have hT1TyF :
      __eo_typeof t1 =
        Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1) := by
    change __eo_typeof_store (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof f1) ≠ Term.Stuck
      at hRhsNotStuck
    exact RuleProofs.eo_typeof_store_not_stuck_implies_array
      (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof f1) hRhsNotStuck
  have hT1TyE :
      __eo_typeof t1 =
        Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1) := by
    change __eo_typeof_store (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof e1) ≠ Term.Stuck
      at hInnerNotStuck
    exact RuleProofs.eo_typeof_store_not_stuck_implies_array
      (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof e1) hInnerNotStuck
  have hArrayEq :
      Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1) =
        Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1) :=
    hT1TyE.symm.trans hT1TyF
  have hEF : __eo_typeof e1 = __eo_typeof f1 := by
    injection hArrayEq with _ hEF
  exact ⟨hT1TyF, hEF⟩

private theorem typed___eo_prog_array_store_overwrite_impl
    (t1 i1 e1 f1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  RuleProofs.eo_has_smt_translation f1 ->
  __eo_typeof (__eo_prog_array_store_overwrite t1 i1 e1 f1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_array_store_overwrite t1 i1 e1 f1) := by
  intro hT1Trans hI1Trans hE1Trans hF1Trans hResultTy
  rcases typeof_args_of_prog_array_store_overwrite_bool
      t1 i1 e1 f1 hT1Trans hI1Trans hE1Trans hF1Trans hResultTy with
    ⟨hT1Ty, hEF⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hF1NotStuck : f1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f1 hF1Trans
  have hSmtT1Raw :
      __smtx_typeof (__eo_to_smt t1) =
        __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1)) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hT1TyNonNone :
      __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof f1)) ≠
        SmtType.None := by
    rw [← hSmtT1Raw]
    exact hT1Trans
  have hSmtT1 :
      __smtx_typeof (__eo_to_smt t1) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    exact hSmtT1Raw.trans
      (RuleProofs.eo_to_smt_type_array_of_non_none
        (__eo_typeof i1) (__eo_typeof f1) hT1TyNonNone)
  have hSmtI1 :
      __smtx_typeof (__eo_to_smt i1) = __eo_to_smt_type (__eo_typeof i1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation i1 hI1Trans
  have hSmtE1 :
      __smtx_typeof (__eo_to_smt e1) = __eo_to_smt_type (__eo_typeof f1) := by
    exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      e1 (__eo_typeof f1) (__eo_to_smt e1) rfl hE1Trans hEF
  have hSmtF1 :
      __smtx_typeof (__eo_to_smt f1) = __eo_to_smt_type (__eo_typeof f1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation f1 hF1Trans
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hSmtT1, hSmtI1, hSmtE1]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.store
                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hInnerTy, hSmtI1, hSmtF1]
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof f1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store,
      native_ite, native_Teq, hSmtT1, hSmtI1, hSmtF1]
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply
            (Term.Apply Term.store
              (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1) := by
    simp [RuleProofs.eo_has_smt_translation, hLhsTy]
  rw [prog_array_store_overwrite_eq t1 i1 e1 f1 hT1NotStuck hI1NotStuck hE1NotStuck hF1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply Term.store
          (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1)
    (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)
    (by rw [hLhsTy, hRhsTy]) hLhsTrans

private theorem facts___eo_prog_array_store_overwrite_impl
    (M : SmtModel) (hM : model_wf M) (t1 i1 e1 f1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  RuleProofs.eo_has_smt_translation f1 ->
  __eo_typeof (__eo_prog_array_store_overwrite t1 i1 e1 f1) = Term.Bool ->
  eo_interprets M (__eo_prog_array_store_overwrite t1 i1 e1 f1) true := by
  intro hT1Trans hI1Trans hE1Trans hF1Trans hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_array_store_overwrite t1 i1 e1 f1) :=
    typed___eo_prog_array_store_overwrite_impl
      t1 i1 e1 f1 hT1Trans hI1Trans hE1Trans hF1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hF1NotStuck : f1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f1 hF1Trans
  have hT1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt t1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM t1 hT1Trans
  have hI1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt i1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM i1 hI1Trans
  have hE1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt e1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM e1 hE1Trans
  have hF1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt f1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM f1 hF1Trans
  have hProgEq :=
    prog_array_store_overwrite_eq t1 i1 e1 f1
      hT1NotStuck hI1NotStuck hE1NotStuck hF1NotStuck
  have hProgBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.store
                  (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1))
          (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)) := by
    simpa [hProgEq] using hProgBool
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply
      (Term.Apply
        (Term.Apply Term.store
          (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1)
    (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1)
    hProgBool' <| by
      simpa [RuleProofs.eo_to_smt_store_eq, __smtx_model_eval] using
        (RuleProofs.smt_value_rel_store_overwrite
          (__smtx_model_eval M (__eo_to_smt t1))
          (__smtx_model_eval M (__eo_to_smt i1))
          (__smtx_model_eval M (__eo_to_smt e1))
          (__smtx_model_eval M (__eo_to_smt f1))
          hT1Can hI1Can hE1Can hF1Can)

public theorem cmd_step_array_store_overwrite_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_store_overwrite args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.array_store_overwrite args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_store_overwrite args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.array_store_overwrite args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          let T1 := a1
                          let I1 := a2
                          let E1 := a3
                          let F1 := a4
                          have hTranses :
                              RuleProofs.eo_has_smt_translation T1 ∧
                                RuleProofs.eo_has_smt_translation I1 ∧
                                RuleProofs.eo_has_smt_translation E1 ∧
                                RuleProofs.eo_has_smt_translation F1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                          change __eo_typeof (__eo_prog_array_store_overwrite T1 I1 E1 F1) = Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M (__eo_prog_array_store_overwrite T1 I1 E1 F1) true
                            exact facts___eo_prog_array_store_overwrite_impl M hM
                              T1 I1 E1 F1
                              hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2 hResultTy
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_array_store_overwrite T1 I1 E1 F1)
                            exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                              (__eo_prog_array_store_overwrite T1 I1 E1 F1)
                              (typed___eo_prog_array_store_overwrite_impl
                                T1 I1 E1 F1
                                hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2 hResultTy)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
