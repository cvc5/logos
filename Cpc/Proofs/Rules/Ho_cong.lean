module

public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_ho_cong_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ho_cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ho_cong args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ho_cong args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ho_cong args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      have hProgHo :
          __eo_prog_ho_cong
              (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
            Term.Stuck := by
        change __eo_prog_ho_cong
          (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
            Term.Stuck at hProg
        exact hProg
      have hProgHoType :
          __eo_typeof (__eo_prog_ho_cong
              (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
            Term.Bool := by
        change __eo_typeof (__eo_prog_ho_cong
          (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
          Term.Bool at hResultTy
        exact hResultTy
      have hProgHoListNN :
          __eo_prog_ho_cong
              (Proof.pf (premiseAndFormulaList (premiseTermList s premises))) ≠
            Term.Stuck := by
        rw [← mk_premise_list_and_eq_premiseAndFormulaList]
        exact hProgHo
      have hProgHoListType :
          __eo_typeof (__eo_prog_ho_cong
              (Proof.pf (premiseAndFormulaList (premiseTermList s premises)))) =
            Term.Bool := by
        rw [← mk_premise_list_and_eq_premiseAndFormulaList]
        exact hProgHoType
      have hProgHoListBool :
          RuleProofs.eo_has_bool_type
            (__eo_prog_ho_cong
              (Proof.pf (premiseAndFormulaList (premiseTermList s premises)))) :=
        CongSupport.typed___eo_prog_ho_cong_impl
          (premiseTermList s premises)
          hPremisesBool hProgHoListNN hProgHoListType
      refine ⟨?_, ?_⟩
      · intro hEvidence
        change eo_interprets M
          (__eo_prog_ho_cong
            (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
        rw [mk_premise_list_and_eq_premiseAndFormulaList]
        exact CongSupport.facts___eo_prog_ho_cong_impl M hM
          (premiseTermList s premises)
          hEvidence hProgHoListBool hProgHoListNN hProgHoListType
      · change RuleProofs.eo_has_smt_translation
          (__eo_prog_ho_cong
            (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
        apply RuleProofs.eo_has_smt_translation_of_has_bool_type
        rw [mk_premise_list_and_eq_premiseAndFormulaList]
        exact hProgHoListBool
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
