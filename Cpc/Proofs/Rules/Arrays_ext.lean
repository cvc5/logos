module

public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_not_bool_arg
    (T : Term)
    (h : __eo_typeof_not T = Term.Bool) :
    T = Term.Bool := by
  cases T <;> simp [__eo_typeof_not] at h ⊢

private theorem eo_typeof_select_array_self_eq
    (I E : Term)
    (hI : I ≠ Term.Stuck) :
    __eo_typeof_select (Term.Apply (Term.Apply Term.Array I) E) I = E := by
  cases I <;> simp [__eo_typeof_select, __eo_requires, __eo_eq, native_ite,
    native_teq, SmtEval.native_not] at hI ⊢

private theorem eo_to_smt_type_array_components_non_none
    (I E : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.Apply Term.Array I) E) ≠ SmtType.None) :
    __eo_to_smt_type I ≠ SmtType.None ∧ __eo_to_smt_type E ≠ SmtType.None := by
  cases hI : __eo_to_smt_type I <;> cases hE : __eo_to_smt_type E <;>
    simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_guard,
      native_ite, native_Teq, hI, hE] at h ⊢

private theorem cmd_step_arrays_ext_one_eq
    (s : CState) (n : CIndex) :
    __eo_cmd_step_proven s CRule.arrays_ext CArgList.nil (CIndexList.cons n CIndexList.nil) =
      __eo_prog_arrays_ext (Proof.pf (__eo_state_proven_nth s n)) := by
  rfl

private theorem arrays_ext_array_types_of_result_bool
    (a b : Term)
    (h :
      __eo_typeof
          (__eo_prog_arrays_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ I E : Term,
      __eo_typeof a = Term.Apply (Term.Apply Term.Array I) E ∧
        __eo_typeof b = Term.Apply (Term.Apply Term.Array I) E ∧
        __eo_typeof (Term._at_array_deq_diff a b) = I := by
  let idx := Term._at_array_deq_diff a b
  let lhs := Term.Apply (Term.Apply Term.select a) idx
  let rhs := Term.Apply (Term.Apply Term.select b) idx
  have hNot :
      __eo_typeof_not (__eo_typeof (Term.Apply (Term.Apply Term.eq lhs) rhs)) =
        Term.Bool := by
    have hsimpa := h
    try simp [__eo_prog_arrays_ext, idx, lhs, rhs] at hsimpa ⊢
    exact hsimpa
  have hEqTy :
      __eo_typeof (Term.Apply (Term.Apply Term.eq lhs) rhs) = Term.Bool :=
    eo_typeof_not_bool_arg _ hNot
  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) = Term.Bool at hEqTy
  have hTypesNotStuck :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof lhs) (__eo_typeof rhs) hEqTy
  have hTypesEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq
      (__eo_typeof lhs) (__eo_typeof rhs) hEqTy
  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck := hTypesNotStuck.1
  have hRhsNotStuck : __eo_typeof rhs ≠ Term.Stuck := hTypesNotStuck.2
  change __eo_typeof_select (__eo_typeof a) (__eo_typeof idx) ≠ Term.Stuck
    at hLhsNotStuck
  change __eo_typeof_select (__eo_typeof b) (__eo_typeof idx) ≠ Term.Stuck
    at hRhsNotStuck
  rcases RuleProofs.eo_typeof_select_not_stuck_implies_array
      (__eo_typeof a) (__eo_typeof idx) hLhsNotStuck with
    ⟨Ea, hA⟩
  rcases RuleProofs.eo_typeof_select_not_stuck_implies_array
      (__eo_typeof b) (__eo_typeof idx) hRhsNotStuck with
    ⟨Eb, hB⟩
  have hIdxNotStuck : __eo_typeof idx ≠ Term.Stuck := by
    intro hIdx
    apply hLhsNotStuck
    rw [hIdx]
    cases __eo_typeof a <;> simp [__eo_typeof_select]
  have hLhsTy : __eo_typeof lhs = Ea := by
    change __eo_typeof_select (__eo_typeof a) (__eo_typeof idx) = Ea
    rw [hA]
    exact eo_typeof_select_array_self_eq (__eo_typeof idx) Ea hIdxNotStuck
  have hRhsTy : __eo_typeof rhs = Eb := by
    change __eo_typeof_select (__eo_typeof b) (__eo_typeof idx) = Eb
    rw [hB]
    exact eo_typeof_select_array_self_eq (__eo_typeof idx) Eb hIdxNotStuck
  have hEaEb : Ea = Eb := by
    rw [hLhsTy, hRhsTy] at hTypesEq
    exact hTypesEq
  exact ⟨__eo_typeof idx, Ea, hA, by simpa [← hEaEb] using hB, rfl⟩

private theorem arrays_ext_operand_translations_of_premise_bool
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b))) :
    RuleProofs.eo_has_smt_translation a ∧
      RuleProofs.eo_has_smt_translation b ∧
      __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) := by
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) :=
    RuleProofs.eo_has_bool_type_not_arg _ hPremBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
    ⟨hEq, hNonNone⟩
  exact ⟨hNonNone, by have hsimpa := hNonNone; (try simp [hEq] at hsimpa ⊢); exact hsimpa, hEq⟩

private theorem arrays_ext_smt_array_types
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_arrays_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ I E : Term,
      let A := __eo_to_smt_type I
      let B := __eo_to_smt_type E
      __eo_typeof a = Term.Apply (Term.Apply Term.Array I) E ∧
        __eo_typeof b = Term.Apply (Term.Apply Term.Array I) E ∧
        __eo_typeof (Term._at_array_deq_diff a b) = I ∧
        __smtx_typeof (__eo_to_smt a) = SmtType.Map A B ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Map A B ∧
        __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff a b)) = A ∧
        __eo_to_smt (Term._at_array_deq_diff a b) =
          SmtTerm.map_diff (__eo_to_smt a) (__eo_to_smt b) ∧
        A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
        RuleProofs.eo_has_smt_translation a ∧ RuleProofs.eo_has_smt_translation b := by
  rcases arrays_ext_array_types_of_result_bool a b hResultTy with
    ⟨I, E, hATy, hBTy, hIdxTy⟩
  rcases arrays_ext_operand_translations_of_premise_bool a b hPremBool with
    ⟨hATrans, hBTrans, _hABSame⟩
  have hSmtARaw :
      __smtx_typeof (__eo_to_smt a) =
        __eo_to_smt_type (Term.Apply (Term.Apply Term.Array I) E) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      a _ (__eo_to_smt a) rfl hATrans hATy
  have hArrayNonNone :
      __eo_to_smt_type (Term.Apply (Term.Apply Term.Array I) E) ≠ SmtType.None := by
    rw [← hSmtARaw]
    exact hATrans
  have hArrayTy :
      __eo_to_smt_type (Term.Apply (Term.Apply Term.Array I) E) =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) :=
    RuleProofs.eo_to_smt_type_array_of_non_none I E hArrayNonNone
  have hComps := eo_to_smt_type_array_components_non_none I E hArrayNonNone
  have hSmtA :
      __smtx_typeof (__eo_to_smt a) =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) :=
    hSmtARaw.trans hArrayTy
  have hSmtBRaw :
      __smtx_typeof (__eo_to_smt b) =
        __eo_to_smt_type (Term.Apply (Term.Apply Term.Array I) E) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      b _ (__eo_to_smt b) rfl hBTrans hBTy
  have hSmtB :
      __smtx_typeof (__eo_to_smt b) =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) :=
    hSmtBRaw.trans hArrayTy
  have hIdxSmtTerm :
      __eo_to_smt (Term._at_array_deq_diff a b) =
        SmtTerm.map_diff (__eo_to_smt a) (__eo_to_smt b) := by
    change
      __eo_to_smt_array_deq_diff (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) =
        SmtTerm.map_diff (__eo_to_smt a) (__eo_to_smt b)
    simp [__eo_to_smt_array_deq_diff, hSmtA, hSmtB]
  have hIdxSmtTy :
      __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff a b)) =
        __eo_to_smt_type I := by
    rw [hIdxSmtTerm, Smtm.typeof_map_diff_eq]
    simp [__smtx_typeof_map_diff, hSmtA, hSmtB, native_ite, native_Teq,
      SmtEval.native_and]
  exact ⟨I, E, hATy, hBTy, hIdxTy, hSmtA, hSmtB, hIdxSmtTy, hIdxSmtTerm,
    hComps.1, hComps.2, hATrans, hBTrans⟩

private theorem smt_map_elem_type_ne_reglan_of_typeof
    (t : SmtTerm) (A B : SmtType)
    (hTy : __smtx_typeof t = SmtType.Map A B) :
    B ≠ SmtType.RegLan := by
  exact Smtm.type_wf_rec_ne_reglan
    (Smtm.smt_map_components_wf_rec_of_non_none_type t A B hTy).2

private theorem smt_map_domain_inhabited_wf_rec_of_typeof
    (t : SmtTerm) (A B : SmtType)
    (hTy : __smtx_typeof t = SmtType.Map A B) :
    native_inhabited_type A = true ∧
      __smtx_type_wf_rec A = true := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hWF : __smtx_type_wf (SmtType.Map A B) = true := by
    have hGood := smt_term_result_seq_components_wf_of_non_none t hNN
    simpa [hTy, type_result_seq_components_wf] using hGood
  have hComponent :
      __smtx_type_wf_component (SmtType.Map A B) = true := by
    simpa [__smtx_type_wf] using hWF
  have hParts :
        native_inhabited_type A = true ∧
        __smtx_type_wf_rec A = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B = true := by
    have hRec := (smtx_type_wf_component_parts hComponent).2
    have hRecParts :
        (native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true) ∧
          native_inhabited_type B = true ∧ __smtx_type_wf_rec B = true := by
      simpa [__smtx_type_wf_rec, SmtEval.native_and] using hRec
    exact ⟨hRecParts.1.1, hRecParts.1.2, hRecParts.2.1, hRecParts.2.2⟩
  exact ⟨hParts.1, hParts.2.1⟩

private theorem typed___eo_prog_arrays_ext_impl
    (a b : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) ->
  __eo_typeof
      (__eo_prog_arrays_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
    Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_arrays_ext
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) := by
  intro hPremBool hResultTy
  rcases arrays_ext_smt_array_types a b hPremBool hResultTy with
    ⟨I, E, hATy, hBTy, hIdxTy, hSmtA, hSmtB, hIdxSmtTy, hIdxSmtTerm,
      hINonNone, hENonNone, _hATrans, _hBTrans⟩
  let idx := Term._at_array_deq_diff a b
  let lhs := Term.Apply (Term.Apply Term.select a) idx
  let rhs := Term.Apply (Term.Apply Term.select b) idx
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = __eo_to_smt_type E := by
    rw [RuleProofs.eo_to_smt_select_eq]
    simp [idx,Smtm.typeof_select_eq, __smtx_typeof_select,hSmtA, hIdxSmtTy, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = __eo_to_smt_type E := by
    rw [RuleProofs.eo_to_smt_select_eq]
    simp [idx,Smtm.typeof_select_eq, __smtx_typeof_select,hSmtB, hIdxSmtTy, native_ite, native_Teq]
  have hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by simpa [hLhsTy] using hENonNone)
  have hNotBool : RuleProofs.eo_has_bool_type (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq lhs) rhs)) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqBool
  simpa [__eo_prog_arrays_ext, idx, lhs, rhs] using hNotBool

private theorem facts___eo_prog_arrays_ext_impl
    (M : SmtModel) (hM : model_wf M) (a b : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) ->
  __eo_typeof
      (__eo_prog_arrays_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
    Term.Bool ->
  eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) true ->
  eo_interprets M
    (__eo_prog_arrays_ext
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) true := by
  intro hPremBool hResultTy hPremTrue
  rcases arrays_ext_smt_array_types a b hPremBool hResultTy with
    ⟨I, E, hATy, hBTy, hIdxTy, hSmtA, hSmtB, hIdxSmtTy, hIdxSmtTerm,
      hINonNone, hENonNone, hATrans, hBTrans⟩
  let idx := Term._at_array_deq_diff a b
  let lhs := Term.Apply (Term.Apply Term.select a) idx
  let rhs := Term.Apply (Term.Apply Term.select b) idx
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arrays_ext
          (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) :=
    typed___eo_prog_arrays_ext_impl a b hPremBool hResultTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    have hNot :
        RuleProofs.eo_has_bool_type (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq lhs) rhs)) := by
      simpa [__eo_prog_arrays_ext, idx, lhs, rhs] using hProgBool
    exact RuleProofs.eo_has_bool_type_not_arg _ hNot
  have hPremEqFalse :
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false :=
    RuleProofs.model_eval_eq_false_of_not_eq_true M a b hPremTrue
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) := by
    simpa [hSmtA] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a) hATrans
  have hEvalBTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) := by
    simpa [hSmtB] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt b) hBTrans
  rcases Smtm.map_value_canonical hEvalATy with ⟨m1, hEvalA⟩
  rcases Smtm.map_value_canonical hEvalBTy with ⟨m2, hEvalB⟩
  have hm1Ty :
      __smtx_typeof_map_value m1 =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) := by
    have hsimpa := hEvalATy
    try simp [hEvalA] at hsimpa ⊢
    exact hsimpa
  have hm2Ty :
      __smtx_typeof_map_value m2 =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) := by
    have hsimpa := hEvalBTy
    try simp [hEvalB] at hsimpa ⊢
    exact hsimpa
  have hACan : value_canonical (__smtx_model_eval M (__eo_to_smt a)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM a hATrans
  have hBCan : value_canonical (__smtx_model_eval M (__eo_to_smt b)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM b hBTrans
  have hm1Can : __smtx_map_canonical m1 = true := by
    simpa [hEvalA, value_canonical, __smtx_value_canonical] using hACan
  have hm2Can : __smtx_map_canonical m2 = true := by
    simpa [hEvalB, value_canonical, __smtx_value_canonical] using hBCan
  have hMapsEqFalse :
      __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
        SmtValue.Boolean false := by
    simpa [hEvalA, hEvalB] using hPremEqFalse
  have hENeRegLan : __eo_to_smt_type E ≠ SmtType.RegLan :=
    smt_map_elem_type_ne_reglan_of_typeof
      (__eo_to_smt a) (__eo_to_smt_type I) (__eo_to_smt_type E) hSmtA
  have hADomain :
      native_inhabited_type (__eo_to_smt_type I) = true ∧
        __smtx_type_wf_rec (__eo_to_smt_type I) = true :=
    smt_map_domain_inhabited_wf_rec_of_typeof
      (__eo_to_smt a) (__eo_to_smt_type I) (__eo_to_smt_type E) hSmtA
  have hSelectEqFalse :
      __smtx_model_eval_eq
          (__smtx_map_lookup m1 (native_eval_map_diff m1 m2))
          (__smtx_map_lookup m2 (native_eval_map_diff m1 m2)) =
        SmtValue.Boolean false :=
    RuleProofs.map_diff_selects_model_eval_eq_false
      m1 m2 (__eo_to_smt_type I) (__eo_to_smt_type E)
      hm1Ty hm2Ty hm1Can hm2Can hADomain.1 hADomain.2 hENeRegLan hMapsEqFalse
  have hEqEvalFalse :
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Term.eq lhs) rhs)) =
        SmtValue.Boolean false := by
    rw [RuleProofs.eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
    have hsimpa := hSelectEqFalse
    try simp [lhs, rhs, idx, RuleProofs.eo_to_smt_select_eq, hIdxSmtTerm, __smtx_model_eval, __smtx_model_eval_select, __smtx_model_eval_map_diff, hEvalA, hEvalB] at hsimpa ⊢
    exact hsimpa
  have hEqFalse : eo_interprets M (Term.Apply (Term.Apply Term.eq lhs) rhs) false :=
    RuleProofs.eo_interprets_of_bool_eval M
      (Term.Apply (Term.Apply Term.eq lhs) rhs) false hEqBool hEqEvalFalse
  have hNotTrue : eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq lhs) rhs)) true :=
    RuleProofs.eo_interprets_not_of_false M _ hEqFalse
  simpa [__eo_prog_arrays_ext, idx, lhs, rhs] using hNotTrue

public theorem cmd_step_arrays_ext_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arrays_ext args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_ext args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arrays_ext args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n premises =>
          cases premises with
          | nil =>
              have hPremBoolState :
                  RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n) :=
                hPremisesBool (__eo_state_proven_nth s n) (by simp [premiseTermList])
              cases hp : __eo_state_proven_nth s n with
              | Apply f pArg =>
                  cases f with
                  | UOp op =>
                      cases op with
                      | not =>
                          cases pArg with
                          | Apply fEq b =>
                              cases fEq with
                              | Apply gEq a =>
                                  cases gEq with
                                  | UOp opEq =>
                                      by_cases hOpEq : opEq = UserOp.eq
                                      · subst opEq
                                        have hPremBool :
                                            RuleProofs.eo_has_bool_type
                                              (Term.Apply Term.not
                                                (Term.Apply (Term.Apply Term.eq a) b)) := by
                                          simpa [hp] using hPremBoolState
                                        have hResultTyAB :
                                            __eo_typeof
                                                (__eo_prog_arrays_ext
                                                  (Proof.pf
                                                    (Term.Apply Term.not
                                                      (Term.Apply (Term.Apply Term.eq a) b)))) =
                                              Term.Bool := by
                                          simpa [cmd_step_arrays_ext_one_eq, hp] using hResultTy
                                        refine ⟨?_, ?_⟩
                                        · intro hPremTrue
                                          have hStatePremTrue :
                                              eo_interprets M (__eo_state_proven_nth s n) true :=
                                            hPremTrue (__eo_state_proven_nth s n)
                                              (by simp [premiseTermList])
                                          have hThisPremTrue :
                                              eo_interprets M
                                                (Term.Apply Term.not
                                                  (Term.Apply (Term.Apply Term.eq a) b)) true :=
                                            by simpa [hp] using hStatePremTrue
                                          simpa [cmd_step_arrays_ext_one_eq, hp] using
                                            facts___eo_prog_arrays_ext_impl M hM a b
                                              hPremBool hResultTyAB hThisPremTrue
                                        · simpa [cmd_step_arrays_ext_one_eq, hp] using
                                            RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                              (typed___eo_prog_arrays_ext_impl a b
                                                hPremBool hResultTyAB)
                                      · have hBad :
                                            __eo_cmd_step_proven s CRule.arrays_ext
                                                CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                              Term.Stuck := by
                                          rw [cmd_step_arrays_ext_one_eq, hp]
                                          simp [__eo_prog_arrays_ext, hOpEq]
                                        exact False.elim (hProg hBad)
                                  | _ =>
                                      have hBad :
                                          __eo_cmd_step_proven s CRule.arrays_ext
                                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                            Term.Stuck := by
                                        rw [cmd_step_arrays_ext_one_eq, hp]
                                        simp [__eo_prog_arrays_ext]
                                      exact False.elim (hProg hBad)
                              | _ =>
                                  have hBad :
                                      __eo_cmd_step_proven s CRule.arrays_ext
                                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                        Term.Stuck := by
                                    rw [cmd_step_arrays_ext_one_eq, hp]
                                    simp [__eo_prog_arrays_ext]
                                  exact False.elim (hProg hBad)
                          | _ =>
                              have hBad :
                                  __eo_cmd_step_proven s CRule.arrays_ext
                                      CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                    Term.Stuck := by
                                rw [cmd_step_arrays_ext_one_eq, hp]
                                simp [__eo_prog_arrays_ext]
                              exact False.elim (hProg hBad)
                      | _ =>
                          have hBad :
                              __eo_cmd_step_proven s CRule.arrays_ext
                                  CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                Term.Stuck := by
                            rw [cmd_step_arrays_ext_one_eq, hp]
                            simp [__eo_prog_arrays_ext]
                          exact False.elim (hProg hBad)
                  | _ =>
                      have hBad :
                          __eo_cmd_step_proven s CRule.arrays_ext
                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                            Term.Stuck := by
                        rw [cmd_step_arrays_ext_one_eq, hp]
                        simp [__eo_prog_arrays_ext]
                      exact False.elim (hProg hBad)
              | _ =>
                  have hBad :
                      __eo_cmd_step_proven s CRule.arrays_ext
                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                        Term.Stuck := by
                    rw [cmd_step_arrays_ext_one_eq, hp]
                    simp [__eo_prog_arrays_ext]
                  exact False.elim (hProg hBad)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
