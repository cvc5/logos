module

public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_pairwise_cong_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.pairwise_cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.pairwise_cong args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.pairwise_cong args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.pairwise_cong args premises ≠ Term.Stuck :=
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
          have hProgPairwiseCong :
              __eo_prog_pairwise_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
                Term.Stuck := by
            change
              __eo_prog_pairwise_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
                Term.Stuck at hProg
            exact hProg
          have hProgPairwiseCongType :
              __eo_typeof
                (__eo_prog_pairwise_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
                Term.Bool := by
            change
              __eo_typeof
                (__eo_prog_pairwise_cong a1
                  (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
                Term.Bool at hResultTy
            exact hResultTy
          cases a1 with
          | Apply f xs =>
              have hProgPairwiseCongListNN :
                  __eo_prog_pairwise_cong (Term.Apply f xs)
                      (Proof.pf (premiseAndFormulaList (premiseTermList s premises))) ≠
                    Term.Stuck := by
                rw [← mk_premise_list_and_eq_premiseAndFormulaList]
                exact hProgPairwiseCong
              have hProgPairwiseCongListType :
                  __eo_typeof
                    (__eo_prog_pairwise_cong (Term.Apply f xs)
                      (Proof.pf (premiseAndFormulaList (premiseTermList s premises)))) =
                    Term.Bool := by
                rw [← mk_premise_list_and_eq_premiseAndFormulaList]
                exact hProgPairwiseCongType
              cases
                  CongSupport.eo_apply_arg_has_translation_of_has_translation_or_distinct
                    f xs hATrans with
              | inl hDistinct =>
                  subst f
                  have hProgPairwiseCongListBool :
                      RuleProofs.eo_has_bool_type
                        (__eo_prog_pairwise_cong
                          (Term.Apply (Term.UOp UserOp.distinct) xs)
                          (Proof.pf
                            (premiseAndFormulaList (premiseTermList s premises)))) :=
                    CongSupport.typed___eo_prog_pairwise_cong_distinct_impl xs
                      (premiseTermList s premises)
                      hATrans
                      hPremisesBool
                      hProgPairwiseCongListNN
                      hProgPairwiseCongListType
                  refine ⟨?_, ?_⟩
                  · intro hEvidence
                    change eo_interprets M
                      (__eo_prog_pairwise_cong
                        (Term.Apply (Term.UOp UserOp.distinct) xs)
                        (Proof.pf
                          (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
                    rw [mk_premise_list_and_eq_premiseAndFormulaList]
                    exact
                      CongSupport.facts___eo_prog_pairwise_cong_distinct_impl
                        M hM xs (premiseTermList s premises)
                        hATrans hEvidence.true_here hProgPairwiseCongListBool
                        hProgPairwiseCongListNN
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_pairwise_cong
                        (Term.Apply (Term.UOp UserOp.distinct) xs)
                        (Proof.pf
                          (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
                    apply RuleProofs.eo_has_smt_translation_of_has_bool_type
                    rw [mk_premise_list_and_eq_premiseAndFormulaList]
                    exact hProgPairwiseCongListBool
              | inr hXsTrans =>
                  have hProgPairwiseCongListBool :
                      RuleProofs.eo_has_bool_type
                        (__eo_prog_pairwise_cong (Term.Apply f xs)
                          (Proof.pf
                            (premiseAndFormulaList (premiseTermList s premises)))) :=
                    CongSupport.typed___eo_prog_pairwise_cong_apply_impl f xs
                      (premiseTermList s premises)
                      hATrans
                      hXsTrans
                      hPremisesBool
                      hProgPairwiseCongListNN
                      hProgPairwiseCongListType
                  refine ⟨?_, ?_⟩
                  · intro hEvidence
                    change eo_interprets M
                      (__eo_prog_pairwise_cong (Term.Apply f xs)
                        (Proof.pf
                          (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
                    rw [mk_premise_list_and_eq_premiseAndFormulaList]
                    exact CongSupport.facts___eo_prog_pairwise_cong_apply_impl
                      M hM f xs (premiseTermList s premises)
                      hATrans
                      hXsTrans
                      hEvidence
                      hProgPairwiseCongListBool
                      hProgPairwiseCongListNN
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_pairwise_cong (Term.Apply f xs)
                        (Proof.pf
                          (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
                    apply RuleProofs.eo_has_smt_translation_of_has_bool_type
                    rw [mk_premise_list_and_eq_premiseAndFormulaList]
                    exact hProgPairwiseCongListBool
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProgPairwiseCong
              exact False.elim (hProgPairwiseCong rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
