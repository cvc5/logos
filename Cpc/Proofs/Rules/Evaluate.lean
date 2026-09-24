module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Evaluate.SoundFinal

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/-- Bit-vector signed comparison on canonical binary payloads. -/
public theorem smtx_model_eval_bvsgt_binary_eq_uts_public
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) = true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) = true) :
    __smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_zlt (native_binary_uts w n2)
          (native_binary_uts w n1)) :=
  EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts
    hw0 hCanon1 hCanon2

public theorem cmd_step_evaluate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.evaluate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.evaluate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.evaluate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.evaluate args premises ≠
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
              have hATransPair : eoHasSmtTranslation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hATransPair.1
              have hEvalTy :
                  __eo_typeof (__eo_prog_evaluate a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_evaluate a1) = Term.Bool
                  at hResultTy
                exact hResultTy
              -- `__eo_cmd_step_proven ..` delta-reduces to `__eo_prog_evaluate ..`
              exact run_evaluate_properties M hM a1 hATrans hEvalTy
