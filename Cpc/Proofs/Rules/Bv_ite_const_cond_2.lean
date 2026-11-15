module

public import Cpc.Proofs.RuleSupport.BvIteConstCondSupport
import all Cpc.Proofs.RuleSupport.BvIteConstCondSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem typed___eo_prog_bv_ite_const_cond_2_impl (t1 e1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    __eo_typeof (__eo_prog_bv_ite_const_cond_2 t1 e1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_const_cond_2 t1 e1) := by
  intro hT1Trans hE1Trans hResultTy
  rw [prog_bv_ite_const_cond_2_eq_of_ne_stuck t1 e1
    (RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans)] at hResultTy ⊢
  exact has_bool_type_bvite_const_eq 0 (by decide) t1 e1 e1 hT1Trans hE1Trans
    (Or.inr rfl) hResultTy

private theorem facts___eo_prog_bv_ite_const_cond_2_impl
    (M : SmtModel) (t1 e1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    __eo_typeof (__eo_prog_bv_ite_const_cond_2 t1 e1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ite_const_cond_2 t1 e1) true := by
  intro hT1Trans hE1Trans hResultTy
  have hProgBool :=
    typed___eo_prog_bv_ite_const_cond_2_impl t1 e1 hT1Trans hE1Trans hResultTy
  rw [prog_bv_ite_const_cond_2_eq_of_ne_stuck t1 e1
    (RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans)] at hProgBool ⊢
  apply RuleProofs.eo_interprets_eq_of_rel M _ _ hProgBool
  rw [eval_bvite_const1_zero M t1 e1]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_ite_const_cond_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_const_cond_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ite_const_cond_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_const_cond_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ite_const_cond_2 args premises ≠ Term.Stuck :=
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
              cases premises with
              | nil =>
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_bv_ite_const_cond_2 a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_ite_const_cond_2 a1 a2) true
                    exact facts___eo_prog_bv_ite_const_cond_2_impl M a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_ite_const_cond_2_impl a1 a2 hA1Trans
                        hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
