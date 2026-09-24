module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_extract_sign_extend_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_sign_extend_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_sign_extend_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_sign_extend_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_sign_extend_1 args premises ≠
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
      | cons low args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons high args =>
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
                      | cons n premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let P := __eo_state_proven_nth s n
                              change StepRuleProperties M [P]
                                (bvExtractSignExtend1Program x low high k P)
                              have hArgsTrans :
                                  RuleProofs.eo_has_smt_translation x ∧
                                    RuleProofs.eo_has_smt_translation low ∧
                                    RuleProofs.eo_has_smt_translation high ∧
                                    RuleProofs.eo_has_smt_translation k ∧
                                    True := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans
                              have hXTrans := hArgsTrans.1
                              have hLowTrans := hArgsTrans.2.1
                              have hHighTrans := hArgsTrans.2.2.1
                              have hKTrans := hArgsTrans.2.2.2.1
                              have hProgramTy :
                                  __eo_typeof
                                      (bvExtractSignExtend1Program
                                        x low high k P) = Term.Bool := by
                                exact hResultTy
                              refine ⟨?_, ?_⟩
                              · intro hPremisesTrue
                                have hPTrue : eo_interprets M P true :=
                                  hPremisesTrue P (by simp)
                                exact facts_bv_extract_sign_extend_1_program
                                  M hM x low high k P hXTrans hLowTrans
                                  hHighTrans hKTrans hProgramTy hPTrue
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed_bv_extract_sign_extend_1_program
                                      x low high k P hXTrans hLowTrans
                                      hHighTrans hKTrans hProgramTy)
