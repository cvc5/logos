module

public import Cpc.Proofs.RuleSupport.BooleanElimSupport
import all Cpc.Proofs.RuleSupport.BooleanElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_not_ite_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_ite_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_ite_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_ite_elim1 args premises) :=
by
  exact BooleanElimSupport.cmd_step_not_ite_elim1_properties M hM s args premises
