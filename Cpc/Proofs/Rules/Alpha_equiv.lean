module

public import Cpc.Proofs.RuleSupport.AlphaEquivSupport
import all Cpc.Proofs.RuleSupport.AlphaEquivSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

public theorem cmd_step_alpha_equiv_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.alpha_equiv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.alpha_equiv args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.alpha_equiv args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.alpha_equiv args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons t args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons vs args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons ts args =>
              cases args with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      change __eo_prog_alpha_equiv t vs ts ≠ Term.Stuck at hProg
                      change
                        eoHasSmtTranslation t ∧
                          EoListAllHaveSmtTranslation vs ∧
                          EoListAllHaveSmtTranslation ts ∧ True
                        at hCmdTrans
                      rcases hCmdTrans with
                        ⟨hTTransEo, hVsTrans, hTsTrans, _⟩
                      have hTTrans : RuleProofs.eo_has_smt_translation t := by
                        simpa [RuleProofs.eo_has_smt_translation,
                          eoHasSmtTranslation] using hTTransEo
                      rcases AlphaEquivRule.prog_alpha_equiv_shape
                          t vs ts hProg with
                        ⟨hVsSet, hTsSet, hRenameGuard, hNoSource,
                          hNoTarget, hResultEq⟩
                      rcases AlphaEquivRule.renamingLists_of_is_renaming_rec
                          vs ts hVsTrans hTsTrans hRenameGuard with
                        ⟨pairs, hLists⟩
                      have hDistinct := hLists.distinct hVsSet hTsSet
                      have hActuals :
                          SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes
                            vs ts :=
                        hLists.actuals hTsTrans
                      let tSub :=
                        __substitute_simul_rec (Term.Boolean true) t vs ts
                          Term.__eo_List_nil
                      have hEqMkTy :
                          __eo_typeof
                              (__eo_mk_apply
                                (Term.Apply (Term.UOp UserOp.eq) t) tSub) =
                            Term.Bool := by
                        change __eo_typeof (__eo_prog_alpha_equiv t vs ts) =
                          Term.Bool at hResultTy
                        rw [hResultEq] at hResultTy
                        simpa [tSub] using hResultTy
                      have hEqMkTyNe :
                          __eo_typeof
                              (__eo_mk_apply
                                (Term.Apply (Term.UOp UserOp.eq) t) tSub) ≠
                            Term.Stuck := by
                        rw [hEqMkTy]
                        intro h
                        cases h
                      have hEqMk :
                          __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) tSub =
                            Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) tSub :=
                        SubstituteTranslatabilitySupport.eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
                          (Term.UOp UserOp.eq) t tSub hEqMkTyNe
                      have hEqApplyTy :
                          __eo_typeof
                              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t)
                                tSub) = Term.Bool := by
                        rw [← hEqMk]
                        exact hEqMkTy
                      have hTypesEq : __eo_typeof t = __eo_typeof tSub := by
                        apply support_eo_typeof_eq_bool_operands_eq
                        change __eo_typeof_eq (__eo_typeof t)
                          (__eo_typeof tSub) = Term.Bool at hEqApplyTy
                        exact hEqApplyTy
                      have hTTypeNe : __eo_typeof t ≠ Term.Stuck :=
                        SubstituteSupport.eo_typeof_ne_stuck_of_has_smt_translation
                          t hTTrans
                      have hSubTyNe : __eo_typeof tSub ≠ Term.Stuck := by
                        rw [← hTypesEq]
                        exact hTTypeNe
                      have hPreserves :=
                        AlphaEquivRule.alpha_preserves_type_and_translation
                          t vs ts Term.__eo_List_nil hLists hDistinct.1
                          (EoVarEnvPerm.of_exact hLists.envs.1)
                          (EoVarEnvPerm.of_exact EoVarEnv.nil)
                          hTTrans hTsTrans hActuals
                          (by
                            simpa [tSub,
                              SubstitutePreservationSupport.substResult] using
                              hSubTyNe)
                      have hSubType : __eo_typeof tSub = __eo_typeof t := by
                        simpa [tSub,
                          SubstitutePreservationSupport.substResult] using
                          hPreserves.1
                      have hSubTrans :
                          RuleProofs.eo_has_smt_translation tSub := by
                        simpa [tSub,
                          SubstitutePreservationSupport.substResult] using
                          hPreserves.2
                      have hSameSmtType :
                          __smtx_typeof (__eo_to_smt t) =
                            __smtx_typeof (__eo_to_smt tSub) := by
                        rw [TranslationProofs.eo_to_smt_typeof_matches_translation
                            t hTTrans,
                          TranslationProofs.eo_to_smt_typeof_matches_translation
                            tSub hSubTrans,
                          hSubType]
                      have hTNonNone :
                          __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
                        exact hTTrans
                      have hEqBool :
                          RuleProofs.eo_has_bool_type
                            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t)
                              tSub) :=
                        RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                          t tSub hSameSmtType hTNonNone
                      have hEqTrans :
                          RuleProofs.eo_has_smt_translation
                            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t)
                              tSub) :=
                        RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          hEqBool
                      have hEval :
                          __smtx_model_eval M (__eo_to_smt tSub) =
                            __smtx_model_eval M (__eo_to_smt t) := by
                        simpa [tSub] using
                          AlphaEquivRule.alpha_renaming_eval_eq M hM t vs ts
                            hLists hDistinct.1 hDistinct.2 hTTrans hTsTrans
                            hActuals hSubTrans hNoSource hNoTarget
                      refine ⟨?_, ?_⟩
                      · intro _hEvid
                        change eo_interprets M
                          (__eo_prog_alpha_equiv t vs ts) true
                        rw [hResultEq, hEqMk]
                        apply RuleProofs.eo_interprets_eq_of_rel M
                        · exact hEqBool
                        · rw [hEval]
                          exact RuleProofs.smt_value_rel_refl _
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_alpha_equiv t vs ts)
                        rw [hResultEq, hEqMk]
                        exact hEqTrans
