module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- The purify marker preserves translated SMT type. -/
private theorem eo_to_smt_purify_wrap_eq (x : Term) :
    __eo_to_smt (Term._at_purify x) = SmtTerm._at_purify (__eo_to_smt x) := by
  rfl

/-- The purify marker preserves translated SMT type. -/
private theorem smtx_typeof_eo_to_smt_purify_eq (x : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) =
      __smtx_typeof (__eo_to_smt x) := by
  rw [eo_to_smt_purify_wrap_eq]
  simp [__smtx_typeof]

/-- The purify marker preserves translated SMT evaluation. -/
private theorem smtx_model_eval_eo_to_smt_purify_rel (M : SmtModel) (x : Term) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term._at_purify x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rw [eo_to_smt_purify_wrap_eq]
  simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using
    RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))

/-- Expands `__eo_prog_skolem_intro` on purify inputs. -/
private theorem eo_prog_skolem_intro_purify_eq (x : Term) :
    __eo_prog_skolem_intro (Term._at_purify x) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term._at_purify x)) x := by
  simp [__eo_prog_skolem_intro]

/-- Shows that the EO program for `skolem_intro` is well typed. -/
theorem typed___eo_prog_skolem_intro_impl (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_skolem_intro (Term._at_purify x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_skolem_intro (Term._at_purify x1)) := by
  intro hTrans _hProg
  rw [eo_prog_skolem_intro_purify_eq x1]
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · exact smtx_typeof_eo_to_smt_purify_eq x1
  · simpa [RuleProofs.eo_has_smt_translation,
      smtx_typeof_eo_to_smt_purify_eq] using hTrans

/-- Derives the checker facts exposed by the EO program for `skolem_intro`. -/
theorem facts___eo_prog_skolem_intro_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_skolem_intro (Term._at_purify x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_skolem_intro (Term._at_purify x1)) true := by
  intro hTrans hProg
  have hBool : RuleProofs.eo_has_bool_type (__eo_prog_skolem_intro (Term._at_purify x1)) :=
    typed___eo_prog_skolem_intro_impl x1 hTrans hProg
  rw [eo_prog_skolem_intro_purify_eq x1]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [eo_prog_skolem_intro_purify_eq] using hBool
  · exact smtx_model_eval_eo_to_smt_purify_rel M x1

public theorem cmd_step_skolem_intro_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolem_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.skolem_intro args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolem_intro args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.skolem_intro args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
          cases a1 with
              | Apply f x1 =>
                  cases f with
                  | UOp op =>
                      cases op with
                      | _at_purify =>
                          have hATransPair : RuleProofs.eo_has_smt_translation (Term._at_purify x1) ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                          have hXTrans : RuleProofs.eo_has_smt_translation x1 := by
                            simpa [RuleProofs.eo_has_smt_translation,
                              smtx_typeof_eo_to_smt_purify_eq] using
                              hATransPair.1
                          have hProgIntro : __eo_prog_skolem_intro (Term._at_purify x1) ≠ Term.Stuck := by
                            change __eo_prog_skolem_intro (Term._at_purify x1) ≠ Term.Stuck at hProg
                            exact hProg
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            exact facts___eo_prog_skolem_intro_impl M hM x1 hXTrans hProgIntro
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_skolem_intro_impl x1 hXTrans hProgIntro)
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
