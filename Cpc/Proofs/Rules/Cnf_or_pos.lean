module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cnf_or_pos_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_or_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cnf_or_pos args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_or_pos args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cnf_or_pos args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons Fs args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change __eo_prog_cnf_or_pos Fs ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_cnf_or_pos Fs) = Term.Bool at hResultTy
              have hFsNe : Fs ≠ Term.Stuck := by
                intro hFs
                subst hFs
                simp [__eo_prog_cnf_or_pos] at hProg
              have hFsTrans : RuleProofs.eo_has_smt_translation Fs := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hFsTypeof : __eo_typeof Fs = Term.Bool := by
                have hTyData := hResultTy
                simp [__eo_prog_cnf_or_pos] at hTyData
                change __eo_typeof_or (__eo_typeof_not (__eo_typeof Fs)) (__eo_typeof Fs) =
                    Term.Bool at hTyData
                exact CnfSupport.typeof_not_eq_bool
                  (CnfSupport.typeof_or_eq_bool_left hTyData)
              have hFsBool : RuleProofs.eo_has_bool_type Fs :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type Fs hFsTrans hFsTypeof
              have hResultTrue : eo_interprets M (__eo_prog_cnf_or_pos Fs) true := by
                rcases CnfSupport.eo_interprets_bool_cases M hM Fs hFsBool with hFsTrue | hFsFalse
                · simpa [__eo_prog_cnf_or_pos, hFsNe] using
                    RuleProofs.eo_interprets_or_right_intro M hM
                      (Term.Apply (Term.UOp UserOp.not) Fs) Fs
                      (RuleProofs.eo_has_bool_type_not_of_bool_arg Fs hFsBool) hFsTrue
                · simpa [__eo_prog_cnf_or_pos, hFsNe] using
                    RuleProofs.eo_interprets_or_left_intro M hM
                      (Term.Apply (Term.UOp UserOp.not) Fs) Fs
                      (RuleProofs.eo_interprets_not_of_false M Fs hFsFalse) hFsBool
              refine ⟨?_, ?_⟩
              · intro _hTrue
                exact hResultTrue
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hResultTrue)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
