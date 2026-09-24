module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_cnf_and_pos_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_and_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cnf_and_pos args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_and_pos args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cnf_and_pos args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons Fs args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons i args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  change __eo_prog_cnf_and_pos Fs i ≠ Term.Stuck at hProg
                  change __eo_typeof (__eo_prog_cnf_and_pos Fs i) = Term.Bool at hResultTy
                  have hFsNe : Fs ≠ Term.Stuck := by
                    intro hFs
                    subst hFs
                    simp [__eo_prog_cnf_and_pos] at hProg
                  have hINe : i ≠ Term.Stuck := by
                    intro hI
                    subst hI
                    simp [__eo_prog_cnf_and_pos] at hProg
                  have hNthNe : __eo_list_nth (Term.UOp UserOp.and) Fs i ≠ Term.Stuck := by
                    intro hNth
                    apply hProg
                    simp [__eo_prog_cnf_and_pos, hNth, __eo_mk_apply]
                  have hFsList : CnfSupport.AndList Fs :=
                    CnfSupport.andList_of_list_nth_ne_stuck hNthNe
                  have hArgsTrans := hCmdTrans
                  simp [cmdTranslationOk, cArgListTranslationOk] at hArgsTrans
                  rcases hArgsTrans with ⟨hFsTrans, hITrans⟩
                  have hTyData := hResultTy
                  simp [__eo_prog_cnf_and_pos, __eo_mk_apply] at hTyData
                  change __eo_typeof_or (__eo_typeof_not (__eo_typeof Fs))
                      (__eo_typeof_or
                        (__eo_typeof (__eo_list_nth (Term.UOp UserOp.and) Fs i))
                        (__eo_typeof (Term.Boolean false))) = Term.Bool at hTyData
                  have hFsTypeof : __eo_typeof Fs = Term.Bool :=
                    CnfSupport.typeof_not_eq_bool
                      (CnfSupport.typeof_or_eq_bool_left hTyData)
                  have hFsBool : RuleProofs.eo_has_bool_type Fs :=
                    RuleProofs.eo_typeof_bool_implies_has_bool_type Fs hFsTrans hFsTypeof
                  have hNthBool : RuleProofs.eo_has_bool_type
                      (__eo_list_nth (Term.UOp UserOp.and) Fs i) :=
                    CnfSupport.andList_nth_has_bool_type hFsList hFsBool hNthNe
                  have hInnerBool : RuleProofs.eo_has_bool_type
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                        (__eo_list_nth (Term.UOp UserOp.and) Fs i)) (Term.Boolean false)) :=
                    RuleProofs.eo_has_bool_type_or_of_bool_args
                      (__eo_list_nth (Term.UOp UserOp.and) Fs i) (Term.Boolean false)
                      hNthBool RuleProofs.eo_has_bool_type_false
                  have hNotFsBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) Fs) :=
                    RuleProofs.eo_has_bool_type_not_of_bool_arg Fs hFsBool
                  have hResultTrue : eo_interprets M (__eo_prog_cnf_and_pos Fs i) true := by
                    rcases CnfSupport.eo_interprets_bool_cases M hM Fs hFsBool with hFsTrue | hFsFalse
                    · have hNthTrue : eo_interprets M (__eo_list_nth (Term.UOp UserOp.and) Fs i) true :=
                        CnfSupport.andList_nth_true_of_true M hFsList hFsBool hFsTrue hNthNe
                      have hInnerTrue :
                          eo_interprets M
                            (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                              (__eo_list_nth (Term.UOp UserOp.and) Fs i)) (Term.Boolean false))
                            true :=
                        RuleProofs.eo_interprets_or_left_intro M hM
                          (__eo_list_nth (Term.UOp UserOp.and) Fs i) (Term.Boolean false)
                          hNthTrue RuleProofs.eo_has_bool_type_false
                      simpa [__eo_prog_cnf_and_pos, hFsNe, hINe, hNthNe, __eo_mk_apply] using
                        RuleProofs.eo_interprets_or_right_intro M hM
                          (Term.Apply (Term.UOp UserOp.not) Fs)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                            (__eo_list_nth (Term.UOp UserOp.and) Fs i)) (Term.Boolean false))
                          hNotFsBool hInnerTrue
                    · simpa [__eo_prog_cnf_and_pos, hFsNe, hINe, hNthNe, __eo_mk_apply] using
                        RuleProofs.eo_interprets_or_left_intro M hM
                          (Term.Apply (Term.UOp UserOp.not) Fs)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                            (__eo_list_nth (Term.UOp UserOp.and) Fs i)) (Term.Boolean false))
                          (RuleProofs.eo_interprets_not_of_false M Fs hFsFalse) hInnerBool
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
