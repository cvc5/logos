module

public import Cpc.Proofs.RuleSupport.ArithMultSupport
import all Cpc.Proofs.RuleSupport.ArithMultSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_arith_mult_abs_comparison_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_abs_comparison args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mult_abs_comparison args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_abs_comparison args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_mult_abs_comparison args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      let ps := premiseTermList s premises
      have hMk :
          __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
            premiseAndFormulaList ps := by
        simpa [ps] using mk_premise_list_and_eq_premiseAndFormulaList s premises
      have hResultTyPs :
          __eo_typeof
            (__eo_prog_arith_mult_abs_comparison (Proof.pf (premiseAndFormulaList ps))) =
            Term.Bool := by
        change __eo_typeof
          (__eo_prog_arith_mult_abs_comparison
            (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
          Term.Bool at hResultTy
        simpa [hMk] using hResultTy
      have hPremisesBoolPs : AllHaveBoolType ps := by
        simpa [ps] using hPremisesBool
      refine ⟨?_, ?_⟩
      · intro hPremisesTrue
        change eo_interprets M
          (__eo_prog_arith_mult_abs_comparison
            (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
        rw [hMk]
        exact ArithMultSupport.facts_arith_mult_abs_comparison M hM ps
          hPremisesTrue.true_here hResultTyPs
      · change RuleProofs.eo_has_smt_translation
          (__eo_prog_arith_mult_abs_comparison
            (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
        rw [hMk]
        exact ArithMultSupport.arith_mult_abs_comparison_has_smt_translation
          M hM ps hPremisesBoolPs hResultTyPs
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
