module

public import Cpc.Proofs.RuleSupport.BvSaddoElimSupport
import all Cpc.Proofs.RuleSupport.BvSaddoElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_saddo_eliminate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_saddo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_saddo_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_saddo_eliminate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_saddo_eliminate args premises ≠
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
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
                          change StepRuleProperties M [P1]
                            (__eo_prog_bv_saddo_eliminate a1 a2 a3
                              (Proof.pf P1))
                          have hProgLocal :
                              __eo_prog_bv_saddo_eliminate a1 a2 a3
                                  (Proof.pf P1) ≠ Term.Stuck := by
                            have hsimpa := hProg
                            try simp [P1] at hsimpa ⊢
                            exact hsimpa
                          rcases bv_saddo_eliminate_shape_of_ne_stuck
                              a1 a2 a3 P1 hProgLocal with
                            ⟨hA1Ne, hA2Ne, hA3Ne, pnm, px, hP1⟩
                          have hReqNe := hProgLocal
                          rw [hP1] at hReqNe
                          unfold bvSdivPrem at hReqNe
                          rw [__eo_prog_bv_saddo_eliminate.eq_4
                            a1 a2 a3 pnm px hA1Ne hA2Ne hA3Ne] at hReqNe
                          rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                              a3 a1 pnm px _ hReqNe with
                            ⟨hPnm, hPx⟩
                          subst pnm
                          subst px
                          have hArgsTrans :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                RuleProofs.eo_has_smt_translation a3 ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans
                          have hA1Trans := hArgsTrans.1
                          have hA2Trans := hArgsTrans.2.1
                          have hA3Trans := hArgsTrans.2.2.1
                          have hResultTyCanonical :
                              __eo_typeof (bvSaddoProgram a1 a2 a3) =
                                Term.Bool := by
                            have h := hResultTy
                            change __eo_typeof
                                (__eo_prog_bv_saddo_eliminate a1 a2 a3
                                  (Proof.pf (__eo_state_proven_nth s n1))) =
                              Term.Bool at h
                            simpa [P1, hP1, bvSaddoProgram] using h
                          simpa [hP1, bvSaddoProgram] using
                            (show StepRuleProperties M
                                [bvSdivPrem a1 a3]
                                (bvSaddoProgram a1 a2 a3) from
                              ⟨(by
                                  intro hPremisesTrue
                                  have hPrem :
                                      eo_interprets M
                                        (bvSdivPrem a1 a3) true :=
                                    hPremisesTrue.true_here _ (by simp)
                                  exact facts_bv_saddo_program M hM a1 a2 a3
                                    hA1Trans hA2Trans hA3Trans hPrem
                                    hResultTyCanonical),
                                RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed_bv_saddo_program a1 a2 a3
                                    hA1Trans hA2Trans hA3Trans
                                    hResultTyCanonical)⟩)
