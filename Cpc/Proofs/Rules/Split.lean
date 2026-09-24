module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_split_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.split args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.split args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.split args premises ≠ Term.Stuck :=
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
              change __eo_prog_split F ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_split F) = Term.Bool at hResultTy
              have hFNe : F ≠ Term.Stuck := by
                intro hF
                subst hF
                simp [__eo_prog_split] at hProg
              have hFTrans : RuleProofs.eo_has_smt_translation F := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hFTypeof : __eo_typeof F = Term.Bool := by
                have hTyData := hResultTy
                simp [__eo_prog_split] at hTyData
                change __eo_typeof_or (__eo_typeof F)
                    (__eo_typeof_or (__eo_typeof_not (__eo_typeof F)) Term.Bool) =
                  Term.Bool at hTyData
                exact CnfSupport.typeof_or_eq_bool_left hTyData
              have hFBool : RuleProofs.eo_has_bool_type F :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type F hFTrans hFTypeof
              have hNotFBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) F) :=
                RuleProofs.eo_has_bool_type_not_of_bool_arg F hFBool
              have hInnerBool : RuleProofs.eo_has_bool_type
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                    (Term.Apply (Term.UOp UserOp.not) F)) (Term.Boolean false)) :=
                RuleProofs.eo_has_bool_type_or_of_bool_args
                  (Term.Apply (Term.UOp UserOp.not) F) (Term.Boolean false)
                  hNotFBool RuleProofs.eo_has_bool_type_false
              have hResultTrue : eo_interprets M (__eo_prog_split F) true := by
                rcases CnfSupport.eo_interprets_bool_cases M hM F hFBool with hFTrue | hFFalse
                · simpa [__eo_prog_split, hFNe] using
                    RuleProofs.eo_interprets_or_left_intro M hM F
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                        (Term.Apply (Term.UOp UserOp.not) F)) (Term.Boolean false))
                      hFTrue hInnerBool
                · have hNotFTrue : eo_interprets M (Term.Apply (Term.UOp UserOp.not) F) true :=
                    RuleProofs.eo_interprets_not_of_false M F hFFalse
                  have hInnerTrue : eo_interprets M
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                        (Term.Apply (Term.UOp UserOp.not) F)) (Term.Boolean false)) true :=
                    RuleProofs.eo_interprets_or_left_intro M hM
                      (Term.Apply (Term.UOp UserOp.not) F) (Term.Boolean false)
                      hNotFTrue RuleProofs.eo_has_bool_type_false
                  simpa [__eo_prog_split, hFNe] using
                    RuleProofs.eo_interprets_or_right_intro M hM F
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                        (Term.Apply (Term.UOp UserOp.not) F)) (Term.Boolean false))
                      hFBool hInnerTrue
              refine ⟨?_, ?_⟩
              · intro _hPremisesTrue
                exact hResultTrue
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hResultTrue)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
