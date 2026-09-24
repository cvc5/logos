module

public import Cpc.Proofs.RuleSupport.BvUltAddOneSupport
import all Cpc.Proofs.RuleSupport.BvUltAddOneSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_ult_add_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_add_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ult_add_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_add_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_ult_add_one args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons ys args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons zs args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons c args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons w args =>
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
                              | nil =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | cons n2 premises =>
                                  cases premises with
                                  | cons _ _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                                  | nil =>
                                      let P1 := __eo_state_proven_nth s n1
                                      let P2 := __eo_state_proven_nth s n2
                                      change StepRuleProperties M [P1, P2]
                                        (BvUltAddOneSupport.program
                                          x ys zs c w P1 P2)
                                      have hArgsTrans :
                                          RuleProofs.eo_has_smt_translation x ∧
                                          RuleProofs.eo_has_smt_translation ys ∧
                                          RuleProofs.eo_has_smt_translation zs ∧
                                          RuleProofs.eo_has_smt_translation c ∧
                                          RuleProofs.eo_has_smt_translation w ∧
                                          True := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using hCmdTrans
                                      have hXTrans := hArgsTrans.1
                                      have hYsTrans := hArgsTrans.2.1
                                      have hZsTrans := hArgsTrans.2.2.1
                                      have hCTrans := hArgsTrans.2.2.2.1
                                      have hWTrans := hArgsTrans.2.2.2.2.1
                                      have hProgramTy :
                                          __eo_typeof
                                            (BvUltAddOneSupport.program
                                              x ys zs c w P1 P2) =
                                            Term.Bool := by
                                        have hsimpa := hResultTy
                                        try simp [P1, P2] at hsimpa ⊢
                                        exact hsimpa
                                      refine ⟨?_, ?_⟩
                                      · intro hPremisesTrue
                                        have hP1True : eo_interprets M P1 true :=
                                          hPremisesTrue P1 (by simp)
                                        have hP2True : eo_interprets M P2 true :=
                                          hPremisesTrue P2 (by simp)
                                        exact BvUltAddOneSupport.factsProgram
                                          M hM x ys zs c w P1 P2 hXTrans
                                          hYsTrans hZsTrans hCTrans hWTrans
                                          hProgramTy hP1True hP2True
                                      · exact
                                          RuleProofs.eo_has_smt_translation_of_has_bool_type
                                            _
                                            (BvUltAddOneSupport.typedProgram
                                              x ys zs c w P1 P2 hXTrans
                                              hYsTrans hZsTrans hCTrans hWTrans
                                              hProgramTy)
