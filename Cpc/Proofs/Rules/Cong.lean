module

public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cong_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cong args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cong args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cong args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          have hCmdTransArgs :
              cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
            simpa [cmdTranslationOk] using hCmdTrans
          have hATrans : RuleProofs.eo_has_smt_translation a1 := by
            simpa [cArgListTranslationOk, eoHasSmtTranslation,
              RuleProofs.eo_has_smt_translation] using hCmdTransArgs.1
          have hProgCong :
              __eo_prog_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
                Term.Stuck := by
            change
              __eo_prog_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
                Term.Stuck at hProg
            exact hProg
          have hProgCongType :
              __eo_typeof
                (__eo_prog_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
                Term.Bool := by
            change
              __eo_typeof
                (__eo_prog_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
                Term.Bool at hResultTy
            exact hResultTy
          have hProgCongListNN :
              __eo_prog_cong a1
                  (Proof.pf (premiseAndFormulaList (premiseTermList s premises))) ≠
                Term.Stuck := by
            rw [← mk_premise_list_and_eq_premiseAndFormulaList]
            exact hProgCong
          have hProgCongListType :
              __eo_typeof
                (__eo_prog_cong a1
                  (Proof.pf (premiseAndFormulaList (premiseTermList s premises)))) =
                Term.Bool := by
            rw [← mk_premise_list_and_eq_premiseAndFormulaList]
            exact hProgCongType
          have hProgCongListBool :
              RuleProofs.eo_has_bool_type
                (__eo_prog_cong a1
                  (Proof.pf (premiseAndFormulaList (premiseTermList s premises)))) :=
            CongSupport.typed___eo_prog_cong_impl a1
              (premiseTermList s premises)
              hATrans
              hPremisesBool
              hProgCongListNN
              hProgCongListType
          refine ⟨?_, ?_⟩
          · intro hEvidence
            change eo_interprets M
              (__eo_prog_cong a1
                (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
            rw [mk_premise_list_and_eq_premiseAndFormulaList]
            exact CongSupport.facts___eo_prog_cong_impl M hM a1
              (premiseTermList s premises)
              hATrans
              hEvidence
              hProgCongListBool
              hProgCongListNN
          · change RuleProofs.eo_has_smt_translation
              (__eo_prog_cong a1
                (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
            apply RuleProofs.eo_has_smt_translation_of_has_bool_type
            rw [mk_premise_list_and_eq_premiseAndFormulaList]
            exact hProgCongListBool
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
