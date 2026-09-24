module

public import Cpc.Proofs.RuleSupport.BvMultPow2Support
import all Cpc.Proofs.RuleSupport.BvMultPow2Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_mult_pow2_2b_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_pow2_2b args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_mult_pow2_2b args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_pow2_2b args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_mult_pow2_2b args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons z args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons size args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons exponent args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons u args =>
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
                                  | nil =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                                  | cons n3 premises =>
                                      cases premises with
                                      | cons _ _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                      | nil =>
                                          let P1 := __eo_state_proven_nth s n1
                                          let P2 := __eo_state_proven_nth s n2
                                          let P3 := __eo_state_proven_nth s n3
                                          change StepRuleProperties M
                                            [P1, P2, P3]
                                            (bvMultPow2Program z size n
                                              exponent u P1 P2 P3)
                                          have hArgsTrans :
                                              RuleProofs.eo_has_smt_translation z ∧
                                              RuleProofs.eo_has_smt_translation size ∧
                                              RuleProofs.eo_has_smt_translation n ∧
                                              RuleProofs.eo_has_smt_translation exponent ∧
                                              RuleProofs.eo_has_smt_translation u ∧
                                              True := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using
                                              hCmdTrans
                                          have hZTrans := hArgsTrans.1
                                          have hSizeTrans := hArgsTrans.2.1
                                          have hNTrans := hArgsTrans.2.2.1
                                          have hExponentTrans :=
                                            hArgsTrans.2.2.2.1
                                          have hUTrans :=
                                            hArgsTrans.2.2.2.2.1
                                          have hProgramTy :
                                              __eo_typeof
                                                (bvMultPow2Program z size n
                                                  exponent u P1 P2 P3) =
                                                Term.Bool := by
                                            have hsimpa := hResultTy
                                            try simp [P1, P2, P3] at hsimpa ⊢
                                            exact hsimpa
                                          refine ⟨?_, ?_⟩
                                          · intro hPremisesTrue
                                            have hP1True :
                                                eo_interprets M P1 true :=
                                              hPremisesTrue P1 (by simp)
                                            have hP2True :
                                                eo_interprets M P2 true :=
                                              hPremisesTrue P2 (by simp)
                                            have hP3True :
                                                eo_interprets M P3 true :=
                                              hPremisesTrue P3 (by simp)
                                            exact facts_bv_mult_pow2_program
                                              M hM z size n exponent u P1 P2 P3
                                              hZTrans hSizeTrans hNTrans
                                              hExponentTrans hUTrans hProgramTy
                                              hP1True hP2True hP3True
                                          · exact
                                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                _
                                                (typed_bv_mult_pow2_program
                                                  z size n exponent u P1 P2 P3
                                                  hZTrans hSizeTrans hNTrans
                                                  hExponentTrans hUTrans
                                                  hProgramTy)
