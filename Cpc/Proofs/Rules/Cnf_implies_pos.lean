module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cnf_implies_pos_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_implies_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cnf_implies_pos args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_implies_pos args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cnf_implies_pos args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons F args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change __eo_prog_cnf_implies_pos F ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_cnf_implies_pos F) = Term.Bool at hResultTy
              cases F with
              | Apply f F2 =>
                  cases f with
                  | Apply op F1 =>
                      cases op with
                      | UOp op =>
                          cases op with
                          | imp =>
                              have hArgTrans :
                                  RuleProofs.eo_has_smt_translation
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2) := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              rcases CnfSupport.imp_args_have_bool_type_of_translation F1 F2 hArgTrans with
                                ⟨hF1Bool, hF2Bool⟩
                              have hImpBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2) :=
                                CnfSupport.eo_has_bool_type_imp_of_bool_args F1 F2 hF1Bool hF2Bool
                              have hNotImpBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.UOp UserOp.not)
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2)) :=
                                RuleProofs.eo_has_bool_type_not_of_bool_arg
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2) hImpBool
                              have hNotF1Bool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.UOp UserOp.not) F1) :=
                                RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool
                              have hResultTrue :
                                  eo_interprets M
                                    (__eo_prog_cnf_implies_pos
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2)) true := by
                                rcases CnfSupport.eo_interprets_bool_cases M hM F1 hF1Bool with
                                  hF1True | hF1False
                                · rcases CnfSupport.eo_interprets_bool_cases M hM F2 hF2Bool with
                                    hF2True | hF2False
                                  · simpa [__eo_prog_cnf_implies_pos] using
                                      CnfSupport.clause3_right_true M hM
                                        (Term.Apply (Term.UOp UserOp.not)
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2))
                                        (Term.Apply (Term.UOp UserOp.not) F1) F2
                                        hNotImpBool hNotF1Bool hF2True
                                  · have hImpFalse :
                                        eo_interprets M
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2)
                                          false :=
                                      RuleProofs.eo_interprets_imp_false_intro M F1 F2
                                        hF1True hF2False
                                    simpa [__eo_prog_cnf_implies_pos] using
                                      CnfSupport.clause3_left_true M hM
                                        (Term.Apply (Term.UOp UserOp.not)
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2))
                                        (Term.Apply (Term.UOp UserOp.not) F1) F2
                                        (RuleProofs.eo_interprets_not_of_false M
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2)
                                          hImpFalse)
                                        hNotF1Bool hF2Bool
                                · simpa [__eo_prog_cnf_implies_pos] using
                                    CnfSupport.clause3_middle_true M hM
                                      (Term.Apply (Term.UOp UserOp.not)
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F1) F2))
                                      (Term.Apply (Term.UOp UserOp.not) F1) F2
                                      hNotImpBool
                                      (RuleProofs.eo_interprets_not_of_false M F1 hF1False)
                                      hF2Bool
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                exact hResultTrue
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hResultTrue)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
