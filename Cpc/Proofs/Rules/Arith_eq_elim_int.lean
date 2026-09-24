module

public import Cpc.Proofs.RuleSupport.ArithSimpleSupport
import all Cpc.Proofs.RuleSupport.ArithSimpleSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_arith_eq_elim_int_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_eq_elim_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_eq_elim_int args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_eq_elim_int args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_eq_elim_int args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
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
                  let S1 := a2
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons T1 (CArgList.cons S1 CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hT1Trans : RuleProofs.eo_has_smt_translation T1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.1
                  have hS1Trans : RuleProofs.eo_has_smt_translation S1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.2
                  change __eo_typeof (__eo_prog_arith_eq_elim_int T1 S1) = Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_arith_eq_elim_int T1 S1) true
                    exact ArithSimpleSupport.facts_arith_eq_elim_int
                      M hM T1 S1 hT1Trans hS1Trans hResultTy
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_eq_elim_int T1 S1)
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_arith_eq_elim_int T1 S1)
                      (ArithSimpleSupport.typed_arith_eq_elim_int
                        T1 S1 hT1Trans hS1Trans hResultTy)
