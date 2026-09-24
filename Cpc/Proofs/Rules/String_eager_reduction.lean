module

public import Cpc.Proofs.RuleSupport.StringEagerReductionSupport
import all Cpc.Proofs.RuleSupport.StringEagerReductionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_string_eager_reduction_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_eager_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_eager_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_eager_reduction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.string_eager_reduction args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | cons b args =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons n premises =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              have hPBool :
                  RuleProofs.eo_has_bool_type (__eo_prog_string_eager_reduction a) := by
                exact string_eager_reduction_has_bool_type a hATrans hResultTy
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hPBool⟩
              intro _hPremisesTrue
              exact string_eager_reduction_true M hM a hPBool
