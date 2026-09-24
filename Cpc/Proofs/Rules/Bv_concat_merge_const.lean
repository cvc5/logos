module

public import Cpc.Proofs.RuleSupport.BvConcatMergeConstSupport
import all Cpc.Proofs.RuleSupport.BvConcatMergeConstSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_concat_merge_const_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_concat_merge_const args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_concat_merge_const args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_concat_merge_const args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_concat_merge_const args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons xs args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons w1 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n2 args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons w2 args =>
                      cases args with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons ww args =>
                          cases args with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons zs args =>
                              cases args with
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  cases premises with
                                  | nil =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                                  | cons index premises =>
                                      cases premises with
                                      | cons _ _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                      | nil =>
                                          let P := __eo_state_proven_nth s index
                                          change StepRuleProperties M [P]
                                            (bvConcatMergeConstProgram xs n1 w1
                                              n2 w2 ww zs P)
                                          have hArgsTrans :
                                              RuleProofs.eo_has_smt_translation xs ∧
                                              RuleProofs.eo_has_smt_translation n1 ∧
                                              RuleProofs.eo_has_smt_translation w1 ∧
                                              RuleProofs.eo_has_smt_translation n2 ∧
                                              RuleProofs.eo_has_smt_translation w2 ∧
                                              RuleProofs.eo_has_smt_translation ww ∧
                                              RuleProofs.eo_has_smt_translation zs ∧
                                              True := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using hCmdTrans
                                          have hXsTrans := hArgsTrans.1
                                          have hN1Trans := hArgsTrans.2.1
                                          have hW1Trans := hArgsTrans.2.2.1
                                          have hN2Trans := hArgsTrans.2.2.2.1
                                          have hW2Trans := hArgsTrans.2.2.2.2.1
                                          have hWwTrans := hArgsTrans.2.2.2.2.2.1
                                          have hZsTrans :=
                                            hArgsTrans.2.2.2.2.2.2.1
                                          have hProgramTy :
                                              __eo_typeof
                                                  (bvConcatMergeConstProgram xs n1
                                                    w1 n2 w2 ww zs P) =
                                                Term.Bool := by
                                            have hsimpa := hResultTy
                                            try simp [P] at hsimpa ⊢
                                            exact hsimpa
                                          have hProgramNe :
                                              bvConcatMergeConstProgram xs n1 w1
                                                  n2 w2 ww zs P ≠ Term.Stuck :=
                                            term_ne_stuck_of_typeof_bool hProgramTy
                                          refine ⟨?_, ?_⟩
                                          · intro hPremisesTrue
                                            have hPremTrue : eo_interprets M P true :=
                                              hPremisesTrue P (by simp)
                                            exact facts_bv_concat_merge_const_program
                                              M hM xs n1 w1 n2 w2 ww zs P
                                              hXsTrans hN1Trans hW1Trans hN2Trans
                                              hW2Trans hWwTrans hZsTrans hProgramNe
                                              hProgramTy hPremTrue
                                          · exact
                                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                _
                                                (typed_bv_concat_merge_const_program
                                                  xs n1 w1 n2 w2 ww zs P
                                                  hXsTrans hN1Trans hW1Trans hN2Trans
                                                  hW2Trans hWwTrans hZsTrans hProgramNe
                                                  hProgramTy)
