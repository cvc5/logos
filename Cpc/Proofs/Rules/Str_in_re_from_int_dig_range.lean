
module

public import Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport

open Eo
open SmtEval
open Smtm
open RuleProofs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_in_re_from_int_dig_range_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_from_int_dig_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_from_int_dig_range args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_from_int_dig_range args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_from_int_dig_range args
      premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change __eo_typeof
                  (__eo_prog_str_in_re_from_int_dig_range a1) = Term.Bool
                at hResultTy
              have hA1Ty : __eo_typeof a1 = Term.UOp UserOp.Int :=
                StrInReFromIntDigRangeProof.typeof_arg_of_prog_bool a1
                  hResultTy
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_str_in_re_from_int_dig_range a1) := by
                have hA1NotStuck : a1 ≠ Term.Stuck :=
                  RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                have hProgEq :
                    __eo_prog_str_in_re_from_int_dig_range a1 =
                      StrInReFromIntDigRangeProof.concl a1 :=
                  StrInReFromIntDigRangeProof.prog_eq_of_ne_stuck a1 hA1NotStuck
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    rw [hProgEq]
                    exact StrInReFromIntDigRangeProof.typed_concl a1
                      hA1Trans hA1Ty)⟩
                intro _hTrue
                rw [hProgEq]
                exact StrInReFromIntDigRangeProof.facts M hM a1
                  hA1Trans hA1Ty
              change StepRuleProperties M []
                (__eo_prog_str_in_re_from_int_dig_range a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
