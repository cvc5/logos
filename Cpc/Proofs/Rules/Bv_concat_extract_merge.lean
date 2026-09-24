module

public import Cpc.Proofs.RuleSupport.BvConcatExtractMergeSupport
import all Cpc.Proofs.RuleSupport.BvConcatExtractMergeSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_concat_extract_merge_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_concat_extract_merge args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_concat_extract_merge args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_concat_extract_merge args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_concat_extract_merge args premises ≠
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
              | cons i args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons j1 args =>
                      cases args with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons j2 args =>
                          cases args with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons k args =>
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
                                            (bvConcatExtractMergeProgram xs x ys
                                              i j1 j2 k P)
                                          have hArgsTrans :
                                              RuleProofs.eo_has_smt_translation xs ∧
                                              RuleProofs.eo_has_smt_translation x ∧
                                              RuleProofs.eo_has_smt_translation ys ∧
                                              RuleProofs.eo_has_smt_translation i ∧
                                              RuleProofs.eo_has_smt_translation j1 ∧
                                              RuleProofs.eo_has_smt_translation j2 ∧
                                              RuleProofs.eo_has_smt_translation k ∧
                                              True := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using hCmdTrans
                                          have hXsTrans := hArgsTrans.1
                                          have hXTrans := hArgsTrans.2.1
                                          have hYsTrans := hArgsTrans.2.2.1
                                          have hITrans := hArgsTrans.2.2.2.1
                                          have hJ1Trans := hArgsTrans.2.2.2.2.1
                                          have hJ2Trans := hArgsTrans.2.2.2.2.2.1
                                          have hKTrans :=
                                            hArgsTrans.2.2.2.2.2.2.1
                                          have hProgramTy :
                                              __eo_typeof
                                                  (bvConcatExtractMergeProgram xs x
                                                    ys i j1 j2 k P) =
                                                Term.Bool := by
                                            have hsimpa := hResultTy
                                            try simp [P] at hsimpa ⊢
                                            exact hsimpa
                                          have hProgramNe :
                                              bvConcatExtractMergeProgram xs x ys i
                                                  j1 j2 k P ≠ Term.Stuck :=
                                            term_ne_stuck_of_typeof_bool hProgramTy
                                          refine ⟨?_, ?_⟩
                                          · intro hPremisesTrue
                                            have hPremTrue : eo_interprets M P true :=
                                              hPremisesTrue P (by simp)
                                            exact facts_bv_concat_extract_merge_program
                                              M hM xs x ys i j1 j2 k P
                                              hXsTrans hXTrans hYsTrans hITrans
                                              hJ1Trans hJ2Trans hKTrans hProgramNe
                                              hProgramTy hPremTrue
                                          · exact
                                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                _
                                                (typed_bv_concat_extract_merge_program
                                                  xs x ys i j1 j2 k P
                                                  hXsTrans hXTrans hYsTrans hITrans
                                                  hJ1Trans hJ2Trans hKTrans hProgramNe
                                                  hProgramTy)
