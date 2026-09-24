module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_extract_not_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_not args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_not args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_not args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_not args premises ≠ Term.Stuck :=
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
      | cons i args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons j args =>
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
                      have hArgsTrans :
                          RuleProofs.eo_has_smt_translation x ∧
                            RuleProofs.eo_has_smt_translation i ∧
                            RuleProofs.eo_has_smt_translation j ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans
                      have hXTrans := hArgsTrans.1
                      have hITrans := hArgsTrans.2.1
                      have hJTrans := hArgsTrans.2.2.1
                      change __eo_typeof (bvExtractNotProgram x i j) = Term.Bool
                        at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hPremisesTrue
                        change eo_interprets M (bvExtractNotProgram x i j) true
                        exact facts_bv_extract_not_program M hM x i j
                          hXTrans hITrans hJTrans hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_bv_extract_not_program x i j
                            hXTrans hITrans hJTrans hResultTy)
