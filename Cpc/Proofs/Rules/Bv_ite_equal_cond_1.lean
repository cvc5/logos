module

public import Cpc.Proofs.RuleSupport.BvIteEqualCond1Support
import all Cpc.Proofs.RuleSupport.BvIteEqualCond1Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_ite_equal_cond_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_cond_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ite_equal_cond_1 args premises ≠
      Term.Stuck :=
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
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
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
                          have hATransPair :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                RuleProofs.eo_has_smt_translation a3 ∧
                                RuleProofs.eo_has_smt_translation a4 ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk,
                              eoHasSmtTranslation,
                              RuleProofs.eo_has_smt_translation] using hCmdTrans
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                            hATransPair.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                            hATransPair.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                            hATransPair.2.2.1
                          have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                            hATransPair.2.2.2.1
                          change __eo_typeof
                              (__eo_prog_bv_ite_equal_cond_1 a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_bv_ite_equal_cond_1 a1 a2 a3 a4) true
                            exact facts___eo_prog_bv_ite_equal_cond_1_impl M hM
                              a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans
                              hA4Trans hResultTy
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_bv_ite_equal_cond_1_impl a1 a2 a3 a4
                                hA1Trans hA2Trans hA3Trans hA4Trans hResultTy)
