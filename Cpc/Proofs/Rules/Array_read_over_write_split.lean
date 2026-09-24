module

public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_array_read_over_write_split_eq
    (t1 i1 e1 j1 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck)
    (hI1NotStuck : i1 ≠ Term.Stuck)
    (hE1NotStuck : e1 ≠ Term.Stuck)
    (hJ1NotStuck : j1 ≠ Term.Stuck) :
    __eo_prog_array_read_over_write_split t1 i1 e1 j1 =
      (Term.Apply
        (Term.Apply Term.eq
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1)) i1))
        (Term.Apply
          (Term.Apply
            (Term.Apply Term.ite
              (Term.Apply (Term.Apply Term.eq i1) j1)) e1)
          (Term.Apply (Term.Apply Term.select t1) i1))) := by
  by_cases hT : t1 = Term.Stuck
  · contradiction
  · by_cases hI : i1 = Term.Stuck
    · contradiction
    · by_cases hE : e1 = Term.Stuck
      · contradiction
      · by_cases hJ : j1 = Term.Stuck
        · contradiction
        · simp [__eo_prog_array_read_over_write_split]

private theorem eo_typeof_ite_args_of_ne_stuck
    (C X Y : Term) :
    __eo_typeof_ite C X Y ≠ Term.Stuck ->
      C = Term.Bool ∧ X = Y ∧ X ≠ Term.Stuck := by
  intro h
  exact RuleProofs.eo_typeof_ite_args_of_ne_stuck C X Y h

private theorem typeof_args_of_prog_array_read_over_write_split_bool
    (t1 i1 e1 j1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hI1Trans : RuleProofs.eo_has_smt_translation i1)
    (hE1Trans : RuleProofs.eo_has_smt_translation e1)
    (hJ1Trans : RuleProofs.eo_has_smt_translation j1)
    (h :
      __eo_typeof (__eo_prog_array_read_over_write_split t1 i1 e1 j1) =
        Term.Bool) :
    __eo_typeof t1 = Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof e1) ∧
      __eo_typeof i1 = __eo_typeof j1 := by
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  rw [prog_array_read_over_write_split_eq t1 i1 e1 j1 hT1NotStuck hI1NotStuck
    hE1NotStuck hJ1NotStuck] at h
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1)) i1
  let rhs :=
    Term.Apply
      (Term.Apply
        (Term.Apply Term.ite
          (Term.Apply (Term.Apply Term.eq i1) j1)) e1)
      (Term.Apply (Term.Apply Term.select t1) i1)
  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) = Term.Bool at h
  have hTypesNotStuck :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof lhs) (__eo_typeof rhs) h
  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
    hTypesNotStuck.1
  have hRhsNotStuck : __eo_typeof rhs ≠ Term.Stuck :=
    hTypesNotStuck.2
  have hStoreNotStuck :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1) ≠
        Term.Stuck := by
    intro hStoreStuck
    change __eo_typeof_select
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1))
        (__eo_typeof i1) ≠ Term.Stuck at hLhsNotStuck
    rw [hStoreStuck] at hLhsNotStuck
    have hSelectStuck : __eo_typeof_select Term.Stuck (__eo_typeof i1) = Term.Stuck := by
      cases __eo_typeof i1 <;> simp [__eo_typeof_select]
    exact hLhsNotStuck hSelectStuck
  change __eo_typeof_store (__eo_typeof t1) (__eo_typeof j1) (__eo_typeof e1) ≠
    Term.Stuck at hStoreNotStuck
  have hT1Ty :
      __eo_typeof t1 = Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof e1) :=
    RuleProofs.eo_typeof_store_not_stuck_implies_array
      (__eo_typeof t1) (__eo_typeof j1) (__eo_typeof e1) hStoreNotStuck
  change __eo_typeof_ite
      (__eo_typeof (Term.Apply (Term.Apply Term.eq i1) j1))
      (__eo_typeof e1)
      (__eo_typeof (Term.Apply (Term.Apply Term.select t1) i1)) ≠
        Term.Stuck at hRhsNotStuck
  rcases eo_typeof_ite_args_of_ne_stuck
      (__eo_typeof (Term.Apply (Term.Apply Term.eq i1) j1))
      (__eo_typeof e1)
      (__eo_typeof (Term.Apply (Term.Apply Term.select t1) i1))
      hRhsNotStuck with
    ⟨hCondTy, _hBranches, _hETypeNotStuck⟩
  change __eo_typeof_eq (__eo_typeof i1) (__eo_typeof j1) = Term.Bool at hCondTy
  exact ⟨hT1Ty, RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof i1) (__eo_typeof j1) hCondTy⟩

private theorem typed___eo_prog_array_read_over_write_split_impl
    (t1 i1 e1 j1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  __eo_typeof (__eo_prog_array_read_over_write_split t1 i1 e1 j1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_array_read_over_write_split t1 i1 e1 j1) := by
  intro hT1Trans hI1Trans hE1Trans hJ1Trans hResultTy
  rcases typeof_args_of_prog_array_read_over_write_split_bool
      t1 i1 e1 j1 hT1Trans hI1Trans hE1Trans hJ1Trans hResultTy with
    ⟨hT1Ty, hI1J1Ty⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  let A := __eo_to_smt_type (__eo_typeof j1)
  let B := __eo_to_smt_type (__eo_typeof e1)
  have hSmtT1Raw :
      __smtx_typeof (__eo_to_smt t1) =
        __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof e1)) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hT1TyNonNone :
      __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof e1)) ≠
        SmtType.None := by
    rw [← hSmtT1Raw]
    exact hT1Trans
  have hSmtT1 :
      __smtx_typeof (__eo_to_smt t1) = SmtType.Map A B := by
    exact hSmtT1Raw.trans
      (RuleProofs.eo_to_smt_type_array_of_non_none
        (__eo_typeof j1) (__eo_typeof e1) hT1TyNonNone)
  have hSmtI1 :
      __smtx_typeof (__eo_to_smt i1) = A := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation i1 hI1Trans,
      hI1J1Ty]
  have hSmtJ1 :
      __smtx_typeof (__eo_to_smt j1) = A :=
    TranslationProofs.eo_to_smt_typeof_matches_translation j1 hJ1Trans
  have hSmtE1 :
      __smtx_typeof (__eo_to_smt e1) = B :=
    TranslationProofs.eo_to_smt_typeof_matches_translation e1 hE1Trans
  have hANonNone : A ≠ SmtType.None := by
    rw [← hSmtJ1]
    exact hJ1Trans
  have hBNonNone : B ≠ SmtType.None := by
    rw [← hSmtE1]
    exact hE1Trans
  let cond := Term.Apply (Term.Apply Term.eq i1) j1
  let rhsSelect := Term.Apply (Term.Apply Term.select t1) i1
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1)) i1
  let rhs := Term.Apply (Term.Apply (Term.Apply Term.ite cond) e1) rhsSelect
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rw [show __eo_to_smt cond = SmtTerm.eq (__eo_to_smt i1) (__eo_to_smt j1) by rfl]
    rw [typeof_eq_eq]
    exact (RuleProofs.smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt i1))
      (__smtx_typeof (__eo_to_smt j1))).mpr
        ⟨by rw [hSmtI1, hSmtJ1], by rw [hSmtI1]; exact hANonNone⟩
  have hRhsSelectTy :
      __smtx_typeof (__eo_to_smt rhsSelect) = B := by
    rw [RuleProofs.eo_to_smt_select_eq]
    simp [__smtx_typeof, __smtx_typeof_select, native_ite, native_Teq,
      hSmtT1, hSmtI1]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = B := by
    rw [RuleProofs.eo_to_smt_select_eq, RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_select, __smtx_typeof_store,
      native_ite, native_Teq, hSmtT1, hSmtI1, hSmtJ1, hSmtE1]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = B := by
    rw [show __eo_to_smt rhs =
        SmtTerm.ite (__eo_to_smt cond) (__eo_to_smt e1) (__eo_to_smt rhsSelect) by rfl]
    rw [typeof_ite_eq]
    simp [__smtx_typeof_ite, hCondTy, hSmtE1, hRhsSelectTy, native_ite, native_Teq]
  rw [prog_array_read_over_write_split_eq t1 i1 e1 j1
    hT1NotStuck hI1NotStuck hE1NotStuck hJ1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; exact hBNonNone)

private theorem smt_type_ne_reglan_of_wf_rec
    {T : SmtType}
    (h : __smtx_type_wf_rec T = true) :
    T ≠ SmtType.RegLan := by
  intro hReg
  subst T
  simp [__smtx_type_wf_rec] at h

private theorem smtx_model_eval_eq_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

private theorem smtx_model_eval_eq_false_of_ne_true
    (v1 v2 : SmtValue)
    (h : __smtx_model_eval_eq v1 v2 ≠ SmtValue.Boolean true) :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false := by
  rcases smtx_model_eval_eq_boolean v1 v2 with ⟨b, hb⟩
  cases b
  · exact hb
  · exact False.elim (h hb)

private theorem facts___eo_prog_array_read_over_write_split_impl
    (M : SmtModel) (hM : model_wf M) (t1 i1 e1 j1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  __eo_typeof (__eo_prog_array_read_over_write_split t1 i1 e1 j1) = Term.Bool ->
  eo_interprets M (__eo_prog_array_read_over_write_split t1 i1 e1 j1) true := by
  intro hT1Trans hI1Trans hE1Trans hJ1Trans hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_array_read_over_write_split t1 i1 e1 j1) :=
    typed___eo_prog_array_read_over_write_split_impl
      t1 i1 e1 j1 hT1Trans hI1Trans hE1Trans hJ1Trans hResultTy
  rcases typeof_args_of_prog_array_read_over_write_split_bool
      t1 i1 e1 j1 hT1Trans hI1Trans hE1Trans hJ1Trans hResultTy with
    ⟨hT1Ty, hI1J1Ty⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  let A := __eo_to_smt_type (__eo_typeof j1)
  let B := __eo_to_smt_type (__eo_typeof e1)
  have hSmtT1Raw :
      __smtx_typeof (__eo_to_smt t1) =
        __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof e1)) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hT1TyNonNone :
      __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) (__eo_typeof e1)) ≠
        SmtType.None := by
    rw [← hSmtT1Raw]
    exact hT1Trans
  have hSmtT1 :
      __smtx_typeof (__eo_to_smt t1) = SmtType.Map A B := by
    exact hSmtT1Raw.trans
      (RuleProofs.eo_to_smt_type_array_of_non_none
        (__eo_typeof j1) (__eo_typeof e1) hT1TyNonNone)
  have hSmtI1 :
      __smtx_typeof (__eo_to_smt i1) = A := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation i1 hI1Trans,
      hI1J1Ty]
  have hSmtJ1 :
      __smtx_typeof (__eo_to_smt j1) = A :=
    TranslationProofs.eo_to_smt_typeof_matches_translation j1 hJ1Trans
  have hT1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt t1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM t1 hT1Trans
  have hI1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt i1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM i1 hI1Trans
  have hE1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt e1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM e1 hE1Trans
  have hJ1Can :
      value_canonical (__smtx_model_eval M (__eo_to_smt j1)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM j1 hJ1Trans
  have hEvalT1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        SmtType.Map A B := by
    rw [Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
      (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hT1Trans)]
    exact hSmtT1
  rcases Smtm.map_value_canonical hEvalT1Ty with ⟨m, hT1EvalMap⟩
  have hMapCan : __smtx_map_canonical m = true := by
    rw [hT1EvalMap] at hT1Can
    simpa [value_canonical, __smtx_value_canonical] using hT1Can
  have hARec : __smtx_type_wf_rec A = true :=
    (Smtm.smt_map_components_wf_rec_of_non_none_type
      (__eo_to_smt t1) A B hSmtT1).1
  have hANeRegLan : A ≠ SmtType.RegLan :=
    smt_type_ne_reglan_of_wf_rec hARec
  have hEvalI1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt i1)) = A := by
    rw [Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt i1)
      (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hI1Trans)]
    exact hSmtI1
  have hEvalJ1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt j1)) = A := by
    rw [Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt j1)
      (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hJ1Trans)]
    exact hSmtJ1
  let cond := Term.Apply (Term.Apply Term.eq i1) j1
  let rhsSelect := Term.Apply (Term.Apply Term.select t1) i1
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1)) i1
  let rhs := Term.Apply (Term.Apply (Term.Apply Term.ite cond) e1) rhsSelect
  have hProgEq :=
    prog_array_read_over_write_split_eq t1 i1 e1 j1
      hT1NotStuck hI1NotStuck hE1NotStuck hJ1NotStuck
  have hProgBool' : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, lhs, rhs, cond, rhsSelect] using hProgBool
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hProgBool' <| by
    have hLhsSmt :
        __eo_to_smt lhs =
          SmtTerm.select
            (SmtTerm.store (__eo_to_smt t1) (__eo_to_smt j1) (__eo_to_smt e1))
            (__eo_to_smt i1) := by
      rfl
    have hRhsSmt :
        __eo_to_smt rhs =
          SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt i1) (__eo_to_smt j1))
            (__eo_to_smt e1)
            (SmtTerm.select (__eo_to_smt t1) (__eo_to_smt i1)) := by
      rfl
    rw [hLhsSmt, hRhsSmt]
    by_cases hEqEval :
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt i1))
          (__smtx_model_eval M (__eo_to_smt j1)) =
            SmtValue.Boolean true
    · have hEqValues :
          __smtx_model_eval M (__eo_to_smt i1) =
            __smtx_model_eval M (__eo_to_smt j1) :=
        RuleProofs.smt_value_rel_eq_of_type_ne_reglan
          (v1 := __smtx_model_eval M (__eo_to_smt i1))
          (v2 := __smtx_model_eval M (__eo_to_smt j1))
          (T := A)
          hEvalI1Ty hEvalJ1Ty
          hANeRegLan hEqEval
      simpa [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq, __smtx_model_eval,
        __smtx_model_eval_ite, hT1EvalMap, hEqEval, hEqValues,
        RuleProofs.smtx_model_eval_eq_refl] using
        (RuleProofs.smt_value_rel_select_store_same_of_map
          m
          (__smtx_model_eval M (__eo_to_smt j1))
          (__smtx_model_eval M (__eo_to_smt e1))
          hMapCan hJ1Can hE1Can)
    · have hEqFalse :
          __smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt i1))
            (__smtx_model_eval M (__eo_to_smt j1)) =
              SmtValue.Boolean false :=
        smtx_model_eval_eq_false_of_ne_true
          (__smtx_model_eval M (__eo_to_smt i1))
          (__smtx_model_eval M (__eo_to_smt j1)) hEqEval
      have hij :
          native_veq
            (__smtx_model_eval M (__eo_to_smt j1))
            (__smtx_model_eval M (__eo_to_smt i1)) = false := by
        have hNative :
            native_veq
              (__smtx_model_eval M (__eo_to_smt i1))
              (__smtx_model_eval M (__eo_to_smt j1)) = false :=
          RuleProofs.native_veq_false_of_model_eval_eq_false hEqFalse
        exact Smtm.native_veq_false_symm hNative
      simpa [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq, __smtx_model_eval,
        __smtx_model_eval_ite, hT1EvalMap, hEqFalse] using
        (RuleProofs.smt_value_rel_select_store_other_of_native_veq_false
          (__smtx_model_eval M (__eo_to_smt t1))
          (__smtx_model_eval M (__eo_to_smt j1))
          (__smtx_model_eval M (__eo_to_smt i1))
          (__smtx_model_eval M (__eo_to_smt e1))
          hT1Can hJ1Can hI1Can hE1Can hij)

public theorem cmd_step_array_read_over_write_split_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_read_over_write_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.array_read_over_write_split args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_read_over_write_split args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.array_read_over_write_split args premises ≠ Term.Stuck :=
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
                          let J1 := a4
                          have hTranses :
                              RuleProofs.eo_has_smt_translation T1 ∧
                                RuleProofs.eo_has_smt_translation I1 ∧
                                RuleProofs.eo_has_smt_translation E1 ∧
                                RuleProofs.eo_has_smt_translation J1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                          change __eo_typeof
                              (__eo_prog_array_read_over_write_split T1 I1 E1 J1) =
                            Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_array_read_over_write_split T1 I1 E1 J1) true
                            exact facts___eo_prog_array_read_over_write_split_impl M hM
                              T1 I1 E1 J1 hTranses.1 hTranses.2.1 hTranses.2.2.1
                              hTranses.2.2.2 hResultTy
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_array_read_over_write_split T1 I1 E1 J1)
                            exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                              (__eo_prog_array_read_over_write_split T1 I1 E1 J1)
                              (typed___eo_prog_array_read_over_write_split_impl
                                T1 I1 E1 J1 hTranses.1 hTranses.2.1
                                hTranses.2.2.1 hTranses.2.2.2 hResultTy)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
