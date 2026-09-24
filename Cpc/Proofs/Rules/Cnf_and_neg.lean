module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cnf_and_neg_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_and_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cnf_and_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_and_neg args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cnf_and_neg args premises ≠ Term.Stuck :=
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
              change __eo_prog_cnf_and_neg Fs ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_cnf_and_neg Fs) = Term.Bool at hResultTy
              have hFsNe : Fs ≠ Term.Stuck := by
                intro hFs
                subst hFs
                simp [__eo_prog_cnf_and_neg] at hProg
              have hLowerNe : __lower_not_and Fs ≠ Term.Stuck := by
                intro hLower
                apply hProg
                simp [__eo_prog_cnf_and_neg, hLower, __eo_mk_apply]
              have hFsList : CnfSupport.AndList Fs :=
                CnfSupport.andList_of_lower_not_and_ne_stuck hLowerNe
              have hFsTrans : RuleProofs.eo_has_smt_translation Fs := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hTyData := hResultTy
              simp [__eo_prog_cnf_and_neg, __eo_mk_apply] at hTyData
              change __eo_typeof_or (__eo_typeof Fs) (__eo_typeof (__lower_not_and Fs)) =
                  Term.Bool at hTyData
              have hFsTypeof : __eo_typeof Fs = Term.Bool :=
                CnfSupport.typeof_or_eq_bool_left hTyData
              have hFsBool : RuleProofs.eo_has_bool_type Fs :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type Fs hFsTrans hFsTypeof
              have hLowerBool : RuleProofs.eo_has_bool_type (__lower_not_and Fs) :=
                CnfSupport.lower_not_and_has_bool_type hFsList hFsBool
              have hResultTrue : eo_interprets M (__eo_prog_cnf_and_neg Fs) true := by
                rcases CnfSupport.eo_interprets_bool_cases M hM Fs hFsBool with
                  hFsTrue | hFsFalse
                · simpa [__eo_prog_cnf_and_neg, hFsNe, hLowerNe, __eo_mk_apply] using
                    RuleProofs.eo_interprets_or_left_intro M hM Fs (__lower_not_and Fs)
                      hFsTrue hLowerBool
                · have hLowerTrue : eo_interprets M (__lower_not_and Fs) true :=
                    CnfSupport.lower_not_and_true_of_false M hM hFsList hFsBool hFsFalse
                  simpa [__eo_prog_cnf_and_neg, hFsNe, hLowerNe, __eo_mk_apply] using
                    RuleProofs.eo_interprets_or_right_intro M hM Fs (__lower_not_and Fs)
                      hFsBool hLowerTrue
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
