module

public import Cpc.Proofs.RuleSupport.BvAbstractionRuleSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionRuleSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_abstraction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_abstraction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_abstraction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_abstraction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_abstraction args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons F args =>
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
              have hFTrans : RuleProofs.eo_has_smt_translation F := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              change __eo_typeof (__eo_prog_bv_abstraction F) =
                Term.Bool at hResultTy
              change __eo_prog_bv_abstraction F ≠ Term.Stuck at hProg
              have hMatch :=
                BvAbstraction.Rule.match_eq_true_of_program_ne_stuck F hProg
              have hProgEq :=
                BvAbstraction.Rule.program_eq_input_of_match F hMatch
              have hFType : __eo_typeof F = Term.Bool := by
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFBool : RuleProofs.eo_has_bool_type F :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type F hFTrans hFType
              change StepRuleProperties M [] (__eo_prog_bv_abstraction F)
              rw [hProgEq]
              refine ⟨?_, hFTrans⟩
              intro _hPremises
              exact BvAbstraction.Rule.bv_abstraction_match_sound
                M hM F hFBool hMatch
