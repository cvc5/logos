module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cnf_xor_pos2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_xor_pos2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cnf_xor_pos2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_xor_pos2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cnf_xor_pos2 args premises ≠ Term.Stuck :=
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
              change __eo_prog_cnf_xor_pos2 F ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_cnf_xor_pos2 F) = Term.Bool at hResultTy
              cases F with
              | Apply f F2 =>
                  cases f with
                  | Apply op F1 =>
                      cases op with
                      | UOp op =>
                          cases op with
                          | xor =>
                              have hArgTrans :
                                  RuleProofs.eo_has_smt_translation
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              rcases CnfSupport.xor_args_have_bool_type_of_translation F1 F2 hArgTrans with
                                ⟨hF1Bool, hF2Bool⟩
                              have hXorBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) :=
                                CnfSupport.eo_has_bool_type_xor_of_bool_args F1 F2 hF1Bool hF2Bool
                              have hNotXorBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.UOp UserOp.not)
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2)) :=
                                RuleProofs.eo_has_bool_type_not_of_bool_arg
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) hXorBool
                              have hNotF1Bool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.UOp UserOp.not) F1) :=
                                RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool
                              have hNotF2Bool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.UOp UserOp.not) F2) :=
                                RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool
                              have hResultTrue :
                                  eo_interprets M
                                    (__eo_prog_cnf_xor_pos2
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2)) true := by
                                rcases CnfSupport.eo_interprets_bool_cases M hM F1 hF1Bool with
                                  hF1True | hF1False
                                · rcases CnfSupport.eo_interprets_bool_cases M hM F2 hF2Bool with
                                    hF2True | hF2False
                                  · have hXorFalse :
                                        eo_interprets M
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2)
                                          false :=
                                      CnfSupport.eo_interprets_xor_false_of_true_true M F1 F2
                                        hF1True hF2True
                                    simpa [__eo_prog_cnf_xor_pos2] using
                                      CnfSupport.clause3_left_true M hM
                                        (Term.Apply (Term.UOp UserOp.not)
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2))
                                        (Term.Apply (Term.UOp UserOp.not) F1)
                                        (Term.Apply (Term.UOp UserOp.not) F2)
                                        (RuleProofs.eo_interprets_not_of_false M
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2)
                                          hXorFalse)
                                        hNotF1Bool hNotF2Bool
                                  · simpa [__eo_prog_cnf_xor_pos2] using
                                      CnfSupport.clause3_right_true M hM
                                        (Term.Apply (Term.UOp UserOp.not)
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2))
                                        (Term.Apply (Term.UOp UserOp.not) F1)
                                        (Term.Apply (Term.UOp UserOp.not) F2)
                                        hNotXorBool hNotF1Bool
                                        (RuleProofs.eo_interprets_not_of_false M F2 hF2False)
                                · simpa [__eo_prog_cnf_xor_pos2] using
                                    CnfSupport.clause3_middle_true M hM
                                      (Term.Apply (Term.UOp UserOp.not)
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2))
                                      (Term.Apply (Term.UOp UserOp.not) F1)
                                      (Term.Apply (Term.UOp UserOp.not) F2)
                                      hNotXorBool
                                      (RuleProofs.eo_interprets_not_of_false M F1 hF1False)
                                      hNotF2Bool
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
