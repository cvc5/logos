module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm
open SetsMemberSupport
open SetsBasicRewritesSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem smtx_eval_set_member_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_member x y) =
      __smtx_model_eval_set_member (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_set_singleton_term_eq'
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_singleton x) =
      __smtx_model_eval_set_singleton (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private def memberSingletonFormula (a1 a2 : Term) : Term :=
  SetsBasicRewritesSupport.mkEq (SetsBasicRewritesSupport.mkSetMember a1 (SetsBasicRewritesSupport.mkSetSingleton a2)) (SetsBasicRewritesSupport.mkEq a1 a2)

private theorem prog_eq_of_ne_stuck
    {a1 a2 : Term}
    (h1 : a1 ≠ Term.Stuck)
    (h2 : a2 ≠ Term.Stuck) :
    __eo_prog_sets_member_singleton a1 a2 = memberSingletonFormula a1 a2 := by
  cases a1 <;> cases a2 <;>
    simp [__eo_prog_sets_member_singleton, memberSingletonFormula, SetsBasicRewritesSupport.mkEq,
      SetsBasicRewritesSupport.mkSetMember, SetsBasicRewritesSupport.mkSetSingleton] at h1 h2 ⊢

private theorem a2_trans_of_wfElem
    (a2 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a2)) = true) :
    RuleProofs.eo_has_smt_translation a2 := by
  unfold RuleProofs.eo_has_smt_translation
  intro hNone
  rw [hNone] at hWf
  simp [__smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

/-- The element type of a wfElem argument is not RegLan. -/
private theorem a2_smt_ty_ne_reglan
    (a2 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a2)) = true) :
    __smtx_typeof (__eo_to_smt a2) ≠ SmtType.RegLan := by
  intro hReg
  rw [hReg] at hWf
  simp [__smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

private theorem eo_typeof_eq_bool_of_ne_stuck
    {A B : Term} (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  by_cases hA : A = Term.Stuck
  · subst A; simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B; cases A <;> simp [__eo_typeof_eq] at h
  have hReqNS :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
    simpa [__eo_typeof_eq, hA, hB] using h
  simpa [__eo_typeof_eq, hA, hB] using
    SetsEvalOpSupport.req_result hReqNS

/-- Extracts the operand element type from a member-singleton formula whose
    `__eo_typeof` is `Bool`. -/
private theorem memberSingleton_eo_arg_types
    {a1 a2 : Term}
    (hTy : __eo_typeof (memberSingletonFormula a1 a2) = Term.Bool) :
    ∃ T : Term, __eo_typeof a1 = T ∧ __eo_typeof a2 = T := by
  have hEqTy :
      __eo_typeof_eq
        (__eo_typeof_set_member (__eo_typeof a1)
          (__eo_typeof_set_singleton (__eo_typeof a2)))
        (__eo_typeof_eq (__eo_typeof a1) (__eo_typeof a2)) = Term.Bool := by
    have hsimpa := hTy
    try simp [memberSingletonFormula, SetsBasicRewritesSupport.mkEq, SetsBasicRewritesSupport.mkSetMember, SetsBasicRewritesSupport.mkSetSingleton] at hsimpa ⊢
    exact hsimpa
  obtain ⟨hSame, hMemberNS⟩ := SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy
  -- hSame : member = inner   ;   hMemberNS : member ≠ Stuck
  have hInnerNS :
      __eo_typeof_eq (__eo_typeof a1) (__eo_typeof a2) ≠ Term.Stuck := by
    rw [← hSame]; exact hMemberNS
  have hInnerBool :
      __eo_typeof_eq (__eo_typeof a1) (__eo_typeof a2) = Term.Bool :=
    eo_typeof_eq_bool_of_ne_stuck hInnerNS
  have hMemberBool :
      __eo_typeof_set_member (__eo_typeof a1)
          (__eo_typeof_set_singleton (__eo_typeof a2)) = Term.Bool := by
    rw [hSame]; exact hInnerBool
  rcases SetsMemberSupport.eo_typeof_set_member_eq_bool_info hMemberBool with
    ⟨T, ha1Ty, hSingTy, hTNS⟩
  -- typeof (singleton a2) = Set (typeof a2) = Set T  ⟹  typeof a2 = T
  have ha2NS : __eo_typeof a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hSingTy
    simp [__eo_typeof_set_singleton] at hSingTy
  have hSingEq :
      Term.Apply (Term.UOp UserOp.Set) (__eo_typeof a2) =
        Term.Apply (Term.UOp UserOp.Set) T := by
    have hh : __eo_typeof_set_singleton (__eo_typeof a2) =
        Term.Apply (Term.UOp UserOp.Set) T := hSingTy
    cases hCase : __eo_typeof a2 with
    | Stuck => exact absurd hCase ha2NS
    | _ => rw [hCase] at hh; simpa [__eo_typeof_set_singleton] using hh
  have ha2Ty : __eo_typeof a2 = T := by
    injection hSingEq
  exact ⟨T, ha1Ty, ha2Ty⟩

private theorem smt_arg_types
    {a1 a2 T : Term}
    (ha1Trans : RuleProofs.eo_has_smt_translation a1)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a2)) = true)
    (ha1Ty : __eo_typeof a1 = T)
    (ha2Ty : __eo_typeof a2 = T) :
    __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type T ∧
      __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type T := by
  have ha1Match :
      __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a1 ha1Trans
  have ha2Trans : RuleProofs.eo_has_smt_translation a2 :=
    a2_trans_of_wfElem a2 hWf
  have ha2Match :
      __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a2 ha2Trans
  exact ⟨by rw [ha1Match, ha1Ty], by rw [ha2Match, ha2Ty]⟩

private theorem typed___eo_prog_sets_member_singleton_impl
    (a1 a2 : Term)
    (ha1Trans : RuleProofs.eo_has_smt_translation a1)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a2)) = true)
    (hTy : __eo_typeof (__eo_prog_sets_member_singleton a1 a2) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sets_member_singleton a1 a2) := by
  have ha1NS : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 ha1Trans
  have ha2Trans : RuleProofs.eo_has_smt_translation a2 := a2_trans_of_wfElem a2 hWf
  have ha2NS : a2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a2 ha2Trans
  have hProgEq :
      __eo_prog_sets_member_singleton a1 a2 = memberSingletonFormula a1 a2 :=
    prog_eq_of_ne_stuck ha1NS ha2NS
  have hFormulaTy : __eo_typeof (memberSingletonFormula a1 a2) = Term.Bool := by
    rw [hProgEq] at hTy; exact hTy
  rcases memberSingleton_eo_arg_types (a1 := a1) (a2 := a2) hFormulaTy with
    ⟨T, ha1Ty, ha2Ty⟩
  rcases smt_arg_types ha1Trans hWf ha1Ty ha2Ty with ⟨ha1SmtTy, ha2SmtTy⟩
  have hB : __eo_to_smt_type T = __smtx_typeof (__eo_to_smt a2) := ha2SmtTy.symm
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof (__eo_to_smt a2))) = true :=
    type_wf_set_of_component (__smtx_typeof (__eo_to_smt a2)) hWf
  have hSingTy :
      __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt a2)) =
        SmtType.Set (__smtx_typeof (__eo_to_smt a2)) := by
    rw [smtx_typeof_set_singleton_term_eq]
    simp [__smtx_typeof_guard_wf, hSetWf, native_ite]
  have hMemberTy :
      __smtx_typeof
          (SmtTerm.set_member (__eo_to_smt a1)
            (SmtTerm.set_singleton (__eo_to_smt a2))) = SmtType.Bool := by
    rw [typeof_set_member_eq, hSingTy]
    rw [ha1SmtTy, hB]
    simp [__smtx_typeof_set_member, native_ite, native_Teq]
  rw [hProgEq]
  unfold memberSingletonFormula SetsBasicRewritesSupport.mkEq SetsBasicRewritesSupport.mkSetMember SetsBasicRewritesSupport.mkSetSingleton
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) a1)
      (Term.Apply (Term.UOp UserOp.set_singleton) a2))
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a1) a2)
    (by
      change
        __smtx_typeof
            (SmtTerm.set_member (__eo_to_smt a1)
              (SmtTerm.set_singleton (__eo_to_smt a2))) =
          __smtx_typeof (SmtTerm.eq (__eo_to_smt a1) (__eo_to_smt a2))
      rw [hMemberTy, typeof_eq_eq, ha1SmtTy, ha2SmtTy]
      have hBNN : __eo_to_smt_type T ≠ SmtType.None := by
        rw [hB]; exact ha2Trans
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
        hBNN])
    (by
      change
        __smtx_typeof
            (SmtTerm.set_member (__eo_to_smt a1)
              (SmtTerm.set_singleton (__eo_to_smt a2))) ≠ SmtType.None
      rw [hMemberTy]; simp)

private theorem facts___eo_prog_sets_member_singleton_impl
    (M : SmtModel) (hM : model_wf M) (a1 a2 : Term)
    (ha1Trans : RuleProofs.eo_has_smt_translation a1)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a2)) = true)
    (hTy : __eo_typeof (__eo_prog_sets_member_singleton a1 a2) = Term.Bool) :
    eo_interprets M (__eo_prog_sets_member_singleton a1 a2) true := by
  have ha1NS : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 ha1Trans
  have ha2Trans : RuleProofs.eo_has_smt_translation a2 := a2_trans_of_wfElem a2 hWf
  have ha2NS : a2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a2 ha2Trans
  have hProgEq :
      __eo_prog_sets_member_singleton a1 a2 = memberSingletonFormula a1 a2 :=
    prog_eq_of_ne_stuck ha1NS ha2NS
  have hBoolEq :
      RuleProofs.eo_has_bool_type (memberSingletonFormula a1 a2) := by
    have := typed___eo_prog_sets_member_singleton_impl a1 a2 ha1Trans hWf hTy
    rwa [hProgEq] at this
  -- eval the member-of-singleton side vs the equality side
  have hv2NeReg :
      ∀ r, __smtx_model_eval M (__eo_to_smt a2) ≠ SmtValue.RegLan r := by
    intro r hEq
    have ha2NeReg : __smtx_typeof (__eo_to_smt a2) ≠ SmtType.RegLan :=
      a2_smt_ty_ne_reglan a2 hWf
    have hEvalTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a2)) =
          __smtx_typeof (__eo_to_smt a2) :=
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a2)
        (by unfold term_has_non_none_type; exact ha2Trans)
    rw [hEq] at hEvalTy
    apply ha2NeReg
    rw [← hEvalTy]
    simp [__smtx_typeof_value]
  have hMemberEqGen :
      ∀ v1 v2 : SmtValue, (∀ r, v2 ≠ SmtValue.RegLan r) ->
        __smtx_model_eval_set_member v1
            (__smtx_model_eval_set_singleton v2) =
          __smtx_model_eval_eq v1 v2 := by
    intro v1 v2 hv2NR
    rw [__smtx_model_eval_set_member, __smtx_model_eval_set_singleton,
      __smtx_map_select, __smtx_map_lookup, __smtx_map_lookup]
    have hEqSide :
        __smtx_model_eval_eq v1 v2 = SmtValue.Boolean (native_veq v1 v2) := by
      cases v2 with
      | RegLan r => exact absurd rfl (hv2NR r)
      | _ => cases v1 <;> simp [__smtx_model_eval_eq]
    rw [hEqSide]
    by_cases hveq : v1 = v2
    · subst hveq
      simp [native_ite, native_veq]
    · have h2 : native_veq v1 v2 = false := by
        simp only [native_veq, decide_eq_false_iff_not]; exact hveq
      have h1 : native_veq v2 v1 = false := Smtm.native_veq_false_symm h2
      rw [h1, h2]
      simp [native_ite]
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (SetsBasicRewritesSupport.mkSetMember a1 (SetsBasicRewritesSupport.mkSetSingleton a2))) =
        __smtx_model_eval M (__eo_to_smt (SetsBasicRewritesSupport.mkEq a1 a2)) := by
    change
      __smtx_model_eval M
          (SmtTerm.set_member (__eo_to_smt a1)
            (SmtTerm.set_singleton (__eo_to_smt a2))) =
        __smtx_model_eval M (SmtTerm.eq (__eo_to_smt a1) (__eo_to_smt a2))
    rw [smtx_eval_eq_term_eq, smtx_eval_set_member_term_eq,
      smtx_eval_set_singleton_term_eq']
    exact hMemberEqGen (__smtx_model_eval M (__eo_to_smt a1))
      (__smtx_model_eval M (__eo_to_smt a2)) hv2NeReg
  rw [hProgEq]
  unfold memberSingletonFormula
  exact RuleProofs.eo_interprets_eq_of_rel M
    (SetsBasicRewritesSupport.mkSetMember a1 (SetsBasicRewritesSupport.mkSetSingleton a2)) (SetsBasicRewritesSupport.mkEq a1 a2) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (SetsBasicRewritesSupport.mkEq a1 a2)))

public theorem cmd_step_sets_member_singleton_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_member_singleton args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_member_singleton args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_member_singleton args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_member_singleton args premises ≠
        Term.Stuck :=
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
              cases premises with
              | nil =>
                  have hMask :
                      argTranslationOkMasked ArgTranslationKind.term a1 ∧
                        argTranslationOkMasked ArgTranslationKind.wfElem a2 ∧
                          True := by
                    simpa [cmdTranslationOk, cArgListTranslationOkMask]
                      using hCmdTrans
                  have ha1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [argTranslationOkMasked] using hMask.1
                  have hWf :
                      __smtx_type_wf_component
                          (__smtx_typeof (__eo_to_smt a2)) = true := by
                    simpa [argTranslationOkMasked] using hMask.2.1
                  change __eo_typeof
                      (__eo_prog_sets_member_singleton a1 a2) = Term.Bool
                    at hResultTy
                  change StepRuleProperties M []
                    (__eo_prog_sets_member_singleton a1 a2)
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    exact facts___eo_prog_sets_member_singleton_impl M hM a1 a2
                      ha1Trans hWf hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_sets_member_singleton_impl a1 a2 ha1Trans
                        hWf hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
