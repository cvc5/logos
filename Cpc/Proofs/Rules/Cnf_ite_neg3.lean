module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cnf_ite_neg3_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_neg3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cnf_ite_neg3 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_neg3 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cnf_ite_neg3 args premises ≠ Term.Stuck :=
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
              change __eo_prog_cnf_ite_neg3 F ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_cnf_ite_neg3 F) = Term.Bool at hResultTy
              cases F with
              | Apply f F2 =>
                  cases f with
                  | Apply g F1 =>
                      cases g with
                      | Apply op C =>
                          cases op with
                          | UOp op =>
                              cases op with
                              | ite =>
                                  have hArgTrans :
                                      RuleProofs.eo_has_smt_translation
                                        (Term.Apply
                                          (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                          F2) := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                                  rcases CnfSupport.ite_args_have_translation_of_translation C F1 F2
                                      hArgTrans with
                                    ⟨_hCTrans, hF1Trans, hF2Trans⟩
                                  have hTyData := hResultTy
                                  simp [__eo_prog_cnf_ite_neg3] at hTyData
                                  change __eo_typeof_or
                                      (__eo_typeof_ite (__eo_typeof C) (__eo_typeof F1)
                                        (__eo_typeof F2))
                                      (__eo_typeof_or (__eo_typeof_not (__eo_typeof F1))
                                        (__eo_typeof_or (__eo_typeof_not (__eo_typeof F2))
                                          Term.Bool)) = Term.Bool
                                    at hTyData
                                  have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                                    CnfSupport.typeof_not_eq_bool
                                      (CnfSupport.typeof_clause3_middle_eq_bool hTyData)
                                  have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                                    CnfSupport.typeof_not_eq_bool
                                      (CnfSupport.typeof_clause3_right_eq_bool hTyData)
                                  have hCBool : RuleProofs.eo_has_bool_type C :=
                                    CnfSupport.ite_cond_has_bool_type_of_translation C F1 F2 hArgTrans
                                  have hF1Bool : RuleProofs.eo_has_bool_type F1 :=
                                    RuleProofs.eo_typeof_bool_implies_has_bool_type F1
                                      hF1Trans hF1Typeof
                                  have hF2Bool : RuleProofs.eo_has_bool_type F2 :=
                                    RuleProofs.eo_typeof_bool_implies_has_bool_type F2
                                      hF2Trans hF2Typeof
                                  have hIteBool : RuleProofs.eo_has_bool_type
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2) :=
                                    CnfSupport.eo_has_bool_type_ite_of_bool_args C F1 F2
                                      hCBool hF1Bool hF2Bool
                                  have hNotF1Bool : RuleProofs.eo_has_bool_type
                                      (Term.Apply (Term.UOp UserOp.not) F1) :=
                                    RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool
                                  have hNotF2Bool : RuleProofs.eo_has_bool_type
                                      (Term.Apply (Term.UOp UserOp.not) F2) :=
                                    RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool
                                  have hResultTrue :
                                      eo_interprets M
                                        (__eo_prog_cnf_ite_neg3
                                          (Term.Apply
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                            F2)) true := by
                                    rcases CnfSupport.eo_interprets_bool_cases M hM F1 hF1Bool with
                                      hF1True | hF1False
                                    · rcases CnfSupport.eo_interprets_bool_cases M hM F2 hF2Bool with
                                        hF2True | hF2False
                                      · rcases CnfSupport.eo_interprets_bool_cases M hM C hCBool with
                                          hCTrue | hCFalse
                                        · have hIteTrue :
                                              eo_interprets M
                                                (Term.Apply
                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                                  F2)
                                                true :=
                                            CnfSupport.eo_interprets_ite_true_of_cond_true M C F1 F2
                                              hCTrue hF1True hF2Bool
                                          simpa [__eo_prog_cnf_ite_neg3] using
                                            CnfSupport.clause3_left_true M hM
                                              (Term.Apply
                                                (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                                F2)
                                              (Term.Apply (Term.UOp UserOp.not) F1)
                                              (Term.Apply (Term.UOp UserOp.not) F2)
                                              hIteTrue hNotF1Bool hNotF2Bool
                                        · have hIteTrue :
                                              eo_interprets M
                                                (Term.Apply
                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                                  F2)
                                                true :=
                                            CnfSupport.eo_interprets_ite_true_of_cond_false M C F1 F2
                                              hCFalse hF1Bool hF2True
                                          simpa [__eo_prog_cnf_ite_neg3] using
                                            CnfSupport.clause3_left_true M hM
                                              (Term.Apply
                                                (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                                F2)
                                              (Term.Apply (Term.UOp UserOp.not) F1)
                                              (Term.Apply (Term.UOp UserOp.not) F2)
                                              hIteTrue hNotF1Bool hNotF2Bool
                                      · simpa [__eo_prog_cnf_ite_neg3] using
                                          CnfSupport.clause3_right_true M hM
                                            (Term.Apply
                                              (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                              F2)
                                            (Term.Apply (Term.UOp UserOp.not) F1)
                                            (Term.Apply (Term.UOp UserOp.not) F2)
                                            hIteBool hNotF1Bool
                                            (RuleProofs.eo_interprets_not_of_false M F2 hF2False)
                                    · simpa [__eo_prog_cnf_ite_neg3] using
                                        CnfSupport.clause3_middle_true M hM
                                          (Term.Apply
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1)
                                            F2)
                                          (Term.Apply (Term.UOp UserOp.not) F1)
                                          (Term.Apply (Term.UOp UserOp.not) F2)
                                          hIteBool
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
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
