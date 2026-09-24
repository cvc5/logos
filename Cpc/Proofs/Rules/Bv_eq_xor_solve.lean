module

public import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import all Cpc.Proofs.RuleSupport.BvCommutativeXorSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_eq_xor_solve_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_xor_solve args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_eq_xor_solve args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_xor_solve args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_eq_xor_solve args premises ≠ Term.Stuck :=
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
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  cases premises with
                  | nil =>
                      have hATrans :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧
                            RuleProofs.eo_has_smt_translation a3 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATrans.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 := hATrans.2.2.1
                      change __eo_typeof (bvEqXorSolveProgram a1 a2 a3) =
                        Term.Bool at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (bvEqXorSolveProgram a1 a2 a3) true
                        exact facts_bv_eq_xor_solve_program M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_bv_eq_xor_solve_program a1 a2 a3 hA1Trans
                            hA2Trans hA3Trans hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
