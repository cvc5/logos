module

public import Cpc.Proofs.RuleSupport.ArithSimpleSupport
import all Cpc.Proofs.RuleSupport.ArithSimpleSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_arith_div_total_zero_real_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_div_total_zero_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_div_total_zero_real args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_div_total_zero_real args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_div_total_zero_real args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
              let T1 := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons T1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hT1Trans : RuleProofs.eo_has_smt_translation T1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_arith_div_total_zero_real T1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_div_total_zero_real T1) true
                exact ArithSimpleSupport.facts_arith_div_total_zero_real
                  M hM T1 hT1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_arith_div_total_zero_real T1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_arith_div_total_zero_real T1)
                  (ArithSimpleSupport.typed_arith_div_total_zero_real
                    T1 hT1Trans hResultTy)
