module

public import Cpc.Proofs.RuleSupport.BvNegoEliminateSupport
import all Cpc.Proofs.RuleSupport.BvNegoEliminateSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_nego_eliminate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_nego_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_nego_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_nego_eliminate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_nego_eliminate args premises ≠
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n1 premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let P1 := __eo_state_proven_nth s n1
                      change
                        StepRuleProperties M [P1]
                          (__eo_prog_bv_nego_eliminate a1 a2 (Proof.pf P1))
                      have hProgLocal :
                          __eo_prog_bv_nego_eliminate a1 a2 (Proof.pf P1) ≠
                            Term.Stuck := by
                        exact hProg
                      rcases bv_nego_shape_of_ne_stuck a1 a2 P1 hProgLocal with
                        ⟨hA1Ne, hA2Ne, px, pn, hP1⟩
                      have hReqNe :
                          __eo_requires (__eo_and (__eo_eq a2 pn) (__eo_eq a1 px))
                              (Term.Boolean true)
                              (bvNegoTerm a1 a2) ≠ Term.Stuck := by
                        have h := hProgLocal
                        rw [hP1] at h
                        unfold bvNegoPrem at h
                        rw [__eo_prog_bv_nego_eliminate.eq_3 a1 a2 pn px hA1Ne hA2Ne]
                          at h
                        simpa [bvNegoPrem, bvNegoTerm, bvNegoMin] using h
                      rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                          a2 a1 pn px (bvNegoTerm a1 a2) hReqNe with
                        ⟨hPn, hPx⟩
                      subst pn
                      subst px
                      have hATransPair :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                      have hResultTyCanonical :
                          __eo_typeof (bvNegoTerm a1 a2) = Term.Bool := by
                        have hResultTyLocal := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_nego_eliminate a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))) =
                          Term.Bool at hResultTyLocal
                        simpa [P1, hP1, prog_bv_nego_eliminate_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne] using hResultTyLocal
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M
                          (__eo_prog_bv_nego_eliminate a1 a2 (Proof.pf P1)) true
                        rw [hP1, prog_bv_nego_eliminate_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne]
                        exact facts_bv_nego_term M hM a1 a2 hA1Trans
                          hResultTyCanonical
                      · rw [hP1, prog_bv_nego_eliminate_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne]
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_bv_nego_term a1 a2 hA1Trans
                            hResultTyCanonical)
