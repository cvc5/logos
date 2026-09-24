module

public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport

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

private theorem cmd_step_sets_ext_one_eq
    (s : CState) (n : CIndex) :
    __eo_cmd_step_proven s CRule.sets_ext CArgList.nil (CIndexList.cons n CIndexList.nil) =
      __eo_prog_sets_ext (Proof.pf (__eo_state_proven_nth s n)) := by
  rfl

private theorem eo_to_smt_set_member_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.set_member x) y) =
      SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_typeof_set_member_not_stuck_implies_set
    (T S : Term)
    (h : __eo_typeof_set_member T S ≠ Term.Stuck) :
    S = Term.Apply Term.Set T := by
  by_cases hT : T = Term.Stuck
  · subst T
    simp [__eo_typeof_set_member] at h
  · cases S with
    | Apply f U =>
        cases f with
        | UOp op =>
            cases op with
            | Set =>
                have hReq :
                    __eo_requires (__eo_eq T U) (Term.Boolean true) Term.Bool ≠
                      Term.Stuck := by
                  simpa [__eo_typeof_set_member, hT] using h
                have hEq : U = T :=
                  RuleProofs.eq_of_requires_eq_true_not_stuck T U Term.Bool hReq
                simp [hEq]
            | _ =>
                simp [__eo_typeof_set_member] at h
        | _ =>
            simp [__eo_typeof_set_member] at h
    | _ =>
        simp [__eo_typeof_set_member] at h

private theorem sets_ext_set_types_of_result_bool
    (a b : Term)
    (h :
      __eo_typeof
          (__eo_prog_sets_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ T : Term,
      __eo_typeof a = Term.Apply Term.Set T ∧
        __eo_typeof b = Term.Apply Term.Set T ∧
        __eo_typeof (Term._at_sets_deq_diff a b) = T := by
  let idx := Term._at_sets_deq_diff a b
  let lhs := Term.Apply (Term.Apply Term.set_member idx) a
  let rhs := Term.Apply (Term.Apply Term.set_member idx) b
  have hNot :
      __eo_typeof_not (__eo_typeof (Term.Apply (Term.Apply Term.eq lhs) rhs)) =
        Term.Bool := by
    exact h
  have hEqTy :
      __eo_typeof (Term.Apply (Term.Apply Term.eq lhs) rhs) = Term.Bool :=
    eo_typeof_not_bool_arg _ hNot
  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) = Term.Bool at hEqTy
  have hTypesNotStuck :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof lhs) (__eo_typeof rhs) hEqTy
  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck := hTypesNotStuck.1
  have hRhsNotStuck : __eo_typeof rhs ≠ Term.Stuck := hTypesNotStuck.2
  change __eo_typeof_set_member (__eo_typeof idx) (__eo_typeof a) ≠ Term.Stuck
    at hLhsNotStuck
  change __eo_typeof_set_member (__eo_typeof idx) (__eo_typeof b) ≠ Term.Stuck
    at hRhsNotStuck
  have hA :
      __eo_typeof a = Term.Apply Term.Set (__eo_typeof idx) :=
    eo_typeof_set_member_not_stuck_implies_set
      (__eo_typeof idx) (__eo_typeof a) hLhsNotStuck
  have hB :
      __eo_typeof b = Term.Apply Term.Set (__eo_typeof idx) :=
    eo_typeof_set_member_not_stuck_implies_set
      (__eo_typeof idx) (__eo_typeof b) hRhsNotStuck
  exact ⟨__eo_typeof idx, hA, hB, rfl⟩

private theorem sets_ext_operand_translations_of_premise_bool
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

private theorem eo_to_smt_type_set_of_non_none
    (T : Term)
    (h : __eo_to_smt_type (Term.Apply Term.Set T) ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply Term.Set T) =
      SmtType.Set (__eo_to_smt_type T) := by
  cases hT : __eo_to_smt_type T <;>
    simp [TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
      native_ite, native_Teq, hT] at h ⊢

private theorem eo_to_smt_type_set_component_non_none
    (T : Term)
    (h : __eo_to_smt_type (Term.Apply Term.Set T) ≠ SmtType.None) :
    __eo_to_smt_type T ≠ SmtType.None := by
  cases hT : __eo_to_smt_type T <;>
    simp [TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
      native_ite, native_Teq, hT] at h ⊢

private theorem sets_ext_smt_set_types
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_sets_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ T : Term,
      let A := __eo_to_smt_type T
      __eo_typeof a = Term.Apply Term.Set T ∧
        __eo_typeof b = Term.Apply Term.Set T ∧
        __eo_typeof (Term._at_sets_deq_diff a b) = T ∧
        __smtx_typeof (__eo_to_smt a) = SmtType.Set A ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Set A ∧
        __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff a b)) = A ∧
        __eo_to_smt (Term._at_sets_deq_diff a b) =
          SmtTerm.map_diff (__eo_to_smt a) (__eo_to_smt b) ∧
        A ≠ SmtType.None ∧
        RuleProofs.eo_has_smt_translation a ∧ RuleProofs.eo_has_smt_translation b := by
  rcases sets_ext_set_types_of_result_bool a b hResultTy with
    ⟨T, hATy, hBTy, hIdxTy⟩
  rcases sets_ext_operand_translations_of_premise_bool a b hPremBool with
    ⟨hATrans, hBTrans, _hABSame⟩
  have hSmtARaw :
      __smtx_typeof (__eo_to_smt a) =
        __eo_to_smt_type (Term.Apply Term.Set T) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      a _ (__eo_to_smt a) rfl hATrans hATy
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply Term.Set T) ≠ SmtType.None := by
    rw [← hSmtARaw]
    exact hATrans
  have hSetTy :
      __eo_to_smt_type (Term.Apply Term.Set T) =
        SmtType.Set (__eo_to_smt_type T) :=
    eo_to_smt_type_set_of_non_none T hSetNonNone
  have hTNonNone : __eo_to_smt_type T ≠ SmtType.None :=
    eo_to_smt_type_set_component_non_none T hSetNonNone
  have hSmtA :
      __smtx_typeof (__eo_to_smt a) =
        SmtType.Set (__eo_to_smt_type T) :=
    hSmtARaw.trans hSetTy
  have hSmtBRaw :
      __smtx_typeof (__eo_to_smt b) =
        __eo_to_smt_type (Term.Apply Term.Set T) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      b _ (__eo_to_smt b) rfl hBTrans hBTy
  have hSmtB :
      __smtx_typeof (__eo_to_smt b) =
        SmtType.Set (__eo_to_smt_type T) :=
    hSmtBRaw.trans hSetTy
  have hIdxSmtTerm :
      __eo_to_smt (Term._at_sets_deq_diff a b) =
        SmtTerm.map_diff (__eo_to_smt a) (__eo_to_smt b) := by
    change
      __eo_to_smt_sets_deq_diff (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) =
        SmtTerm.map_diff (__eo_to_smt a) (__eo_to_smt b)
    simp [__eo_to_smt_sets_deq_diff, hSmtA, hSmtB]
  have hIdxSmtTy :
      __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff a b)) =
        __eo_to_smt_type T := by
    rw [hIdxSmtTerm, Smtm.typeof_map_diff_eq]
    simp [__smtx_typeof_map_diff, hSmtA, hSmtB, native_ite, native_Teq]
  exact ⟨T, hATy, hBTy, hIdxTy, hSmtA, hSmtB, hIdxSmtTy, hIdxSmtTerm,
    hTNonNone, hATrans, hBTrans⟩

private theorem set_model_eval_eq_false_to_map_eq_false
    (m1 m2 : SmtMap)
    (h :
      __smtx_model_eval_eq (SmtValue.Set m1) (SmtValue.Set m2) =
        SmtValue.Boolean false) :
    __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false := by
  simpa [__smtx_model_eval_eq, native_veq] using h

private theorem typed___eo_prog_sets_ext_impl
    (a b : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) ->
  __eo_typeof
      (__eo_prog_sets_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
    Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_sets_ext
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) := by
  intro hPremBool hResultTy
  rcases sets_ext_smt_set_types a b hPremBool hResultTy with
    ⟨T, hATy, hBTy, hIdxTy, hSmtA, hSmtB, hIdxSmtTy, hIdxSmtTerm,
      hTNonNone, _hATrans, _hBTrans⟩
  let idx := Term._at_sets_deq_diff a b
  let lhs := Term.Apply (Term.Apply Term.set_member idx) a
  let rhs := Term.Apply (Term.Apply Term.set_member idx) b
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.set_member (__eo_to_smt idx) (__eo_to_smt a)) =
      SmtType.Bool
    rw [Smtm.typeof_set_member_eq]
    simp [idx, __smtx_typeof_set_member, hSmtA, hIdxSmtTy,
      native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.set_member (__eo_to_smt idx) (__eo_to_smt b)) =
      SmtType.Bool
    rw [Smtm.typeof_set_member_eq]
    simp [idx, __smtx_typeof_set_member, hSmtB, hIdxSmtTy,
      native_ite, native_Teq]
  have hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by simp [hLhsTy])
  have hNotBool :
      RuleProofs.eo_has_bool_type (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq lhs) rhs)) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqBool
  simpa [__eo_prog_sets_ext, idx, lhs, rhs] using hNotBool

private theorem facts___eo_prog_sets_ext_impl
    (M : SmtModel) (hM : model_wf M) (a b : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) ->
  __eo_typeof
      (__eo_prog_sets_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
    Term.Bool ->
  eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) true ->
  eo_interprets M
    (__eo_prog_sets_ext
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) true := by
  intro hPremBool hResultTy hPremTrue
  rcases sets_ext_smt_set_types a b hPremBool hResultTy with
    ⟨T, hATy, hBTy, hIdxTy, hSmtA, hSmtB, hIdxSmtTy, hIdxSmtTerm,
      hTNonNone, hATrans, hBTrans⟩
  let idx := Term._at_sets_deq_diff a b
  let lhs := Term.Apply (Term.Apply Term.set_member idx) a
  let rhs := Term.Apply (Term.Apply Term.set_member idx) b
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_sets_ext
          (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) :=
    typed___eo_prog_sets_ext_impl a b hPremBool hResultTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    have hNot :
        RuleProofs.eo_has_bool_type (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq lhs) rhs)) := by
      simpa [__eo_prog_sets_ext, idx, lhs, rhs] using hProgBool
    exact RuleProofs.eo_has_bool_type_not_arg _ hNot
  have hPremEqFalse :
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false :=
    RuleProofs.model_eval_eq_false_of_not_eq_true M a b hPremTrue
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hSmtA] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a) hATrans
  have hEvalBTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hSmtB] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt b) hBTrans
  rcases Smtm.set_value_canonical hEvalATy with ⟨m1, hEvalA⟩
  rcases Smtm.set_value_canonical hEvalBTy with ⟨m2, hEvalB⟩
  have hm1Ty :
      __smtx_typeof_map_value m1 =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool :=
    Smtm.set_map_value_typed (by simpa [hEvalA] using hEvalATy)
  have hm2Ty :
      __smtx_typeof_map_value m2 =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool :=
    Smtm.set_map_value_typed (by simpa [hEvalB] using hEvalBTy)
  have hACan : value_canonical (__smtx_model_eval M (__eo_to_smt a)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM a hATrans
  have hBCan : value_canonical (__smtx_model_eval M (__eo_to_smt b)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM b hBTrans
  have hm1Can : __smtx_map_canonical m1 = true := by
    have hParts := hACan
    simp [hEvalA, value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact hParts.1
  have hm2Can : __smtx_map_canonical m2 = true := by
    have hParts := hBCan
    simp [hEvalB, value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact hParts.1
  have hm1DefaultFalse :
      __smtx_map_get_default m1 = SmtValue.Boolean false := by
    have hParts := hACan
    simp [hEvalA, value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact Smtm.eq_of_native_veq_true hParts.2
  have hm2DefaultFalse :
      __smtx_map_get_default m2 = SmtValue.Boolean false := by
    have hParts := hBCan
    simp [hEvalB, value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact Smtm.eq_of_native_veq_true hParts.2
  have hDefaultsEq : __smtx_map_get_default m1 = __smtx_map_get_default m2 :=
    hm1DefaultFalse.trans hm2DefaultFalse.symm
  have hSetsEqFalse :
      __smtx_model_eval_eq (SmtValue.Set m1) (SmtValue.Set m2) =
        SmtValue.Boolean false := by
    simpa [hEvalA, hEvalB] using hPremEqFalse
  have hMapsEqFalse :
      __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
        SmtValue.Boolean false :=
    set_model_eval_eq_false_to_map_eq_false m1 m2 hSetsEqFalse
  have hSelectEqFalse :
      __smtx_model_eval_eq
          (__smtx_map_lookup m1 (native_eval_map_diff m1 m2))
          (__smtx_map_lookup m2 (native_eval_map_diff m1 m2)) =
        SmtValue.Boolean false :=
    RuleProofs.map_diff_selects_model_eval_eq_false_of_default_eq
      m1 m2 (__eo_to_smt_type T) SmtType.Bool
      hm1Ty hm2Ty hm1Can hm2Can hDefaultsEq (by decide) hMapsEqFalse
  have hEqEvalFalse :
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Term.eq lhs) rhs)) =
        SmtValue.Boolean false := by
    rw [RuleProofs.eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
    change
      __smtx_model_eval_eq
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.Apply Term.set_member idx) a)))
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.Apply Term.set_member idx) b))) =
        SmtValue.Boolean false
    rw [eo_to_smt_set_member_eq idx a, eo_to_smt_set_member_eq idx b]
    have hsimpa :=
      hSelectEqFalse
    try simp [idx, hIdxSmtTerm, __smtx_model_eval, __smtx_model_eval_set_member, __smtx_model_eval_map_diff, __smtx_map_select, hEvalA, hEvalB] at hsimpa ⊢
    exact hsimpa
  have hEqFalse : eo_interprets M (Term.Apply (Term.Apply Term.eq lhs) rhs) false :=
    RuleProofs.eo_interprets_of_bool_eval M
      (Term.Apply (Term.Apply Term.eq lhs) rhs) false hEqBool hEqEvalFalse
  have hNotTrue :
      eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq lhs) rhs)) true :=
    RuleProofs.eo_interprets_not_of_false M _ hEqFalse
  simpa [__eo_prog_sets_ext, idx, lhs, rhs] using hNotTrue

public theorem cmd_step_sets_ext_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_ext args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_ext args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_ext args premises ≠ Term.Stuck :=
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
                                                (__eo_prog_sets_ext
                                                  (Proof.pf
                                                    (Term.Apply Term.not
                                                      (Term.Apply (Term.Apply Term.eq a) b)))) =
                                              Term.Bool := by
                                          simpa [cmd_step_sets_ext_one_eq, hp] using hResultTy
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
                                          simpa [cmd_step_sets_ext_one_eq, hp] using
                                            facts___eo_prog_sets_ext_impl M hM a b
                                              hPremBool hResultTyAB hThisPremTrue
                                        · simpa [cmd_step_sets_ext_one_eq, hp] using
                                            RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                              (typed___eo_prog_sets_ext_impl a b
                                                hPremBool hResultTyAB)
                                      · have hBad :
                                            __eo_cmd_step_proven s CRule.sets_ext
                                                CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                              Term.Stuck := by
                                          rw [cmd_step_sets_ext_one_eq, hp]
                                          simp [__eo_prog_sets_ext, hOpEq]
                                        exact False.elim (hProg hBad)
                                  | _ =>
                                      have hBad :
                                          __eo_cmd_step_proven s CRule.sets_ext
                                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                            Term.Stuck := by
                                        rw [cmd_step_sets_ext_one_eq, hp]
                                        simp [__eo_prog_sets_ext]
                                      exact False.elim (hProg hBad)
                              | _ =>
                                  have hBad :
                                      __eo_cmd_step_proven s CRule.sets_ext
                                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                        Term.Stuck := by
                                    rw [cmd_step_sets_ext_one_eq, hp]
                                    simp [__eo_prog_sets_ext]
                                  exact False.elim (hProg hBad)
                          | _ =>
                              have hBad :
                                  __eo_cmd_step_proven s CRule.sets_ext
                                      CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                    Term.Stuck := by
                                rw [cmd_step_sets_ext_one_eq, hp]
                                simp [__eo_prog_sets_ext]
                              exact False.elim (hProg hBad)
                      | _ =>
                          have hBad :
                              __eo_cmd_step_proven s CRule.sets_ext
                                  CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                Term.Stuck := by
                            rw [cmd_step_sets_ext_one_eq, hp]
                            simp [__eo_prog_sets_ext]
                          exact False.elim (hProg hBad)
                  | _ =>
                      have hBad :
                          __eo_cmd_step_proven s CRule.sets_ext
                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                            Term.Stuck := by
                        rw [cmd_step_sets_ext_one_eq, hp]
                        simp [__eo_prog_sets_ext]
                      exact False.elim (hProg hBad)
              | _ =>
                  have hBad :
                      __eo_cmd_step_proven s CRule.sets_ext
                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                        Term.Stuck := by
                    rw [cmd_step_sets_ext_one_eq, hp]
                    simp [__eo_prog_sets_ext]
                  exact False.elim (hProg hBad)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
