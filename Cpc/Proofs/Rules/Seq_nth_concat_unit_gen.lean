module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


public theorem cmd_step_seq_nth_concat_unit_gen_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_nth_concat_unit_gen args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen args premises) :=
by
  sorry
