module

public import Cpc.Proofs.RuleSupport.BvConcatPullupSupport
import all Cpc.Proofs.RuleSupport.BvConcatPullupSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_or_concat_pullup2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_or_concat_pullup2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_or_concat_pullup2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_or_concat_pullup2 args premises) :=
by
  simpa [BvConcatPullupOp.pullup2Rule] using
    (cmd_step_bvConcatPullup2_properties M hM .bor s args premises)
