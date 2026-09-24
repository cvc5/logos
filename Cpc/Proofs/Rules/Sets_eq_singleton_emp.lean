module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_sets_eq_singleton_emp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_eq_singleton_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_eq_singleton_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_eq_singleton_emp args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_eq_singleton_emp args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons y args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons ty args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n premises =>
                      cases premises with
                      | nil =>
                          let P := __eo_state_proven_nth s n
                          change
                            __eo_typeof
                                (__eo_prog_sets_eq_singleton_emp x y ty
                                  (Proof.pf P)) = Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_sets_eq_singleton_emp x y ty
                                  (Proof.pf P) ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases
                              SetsBasicRewritesSupport.prog_sets_eq_singleton_emp_info
                                x y ty P hProgRule with
                            ⟨T, x0, T0, hTyArg, hPremShape, hx0, hT0,
                              hProgEq⟩
                          subst ty
                          subst x0
                          subst T0
                          have hMask :
                              RuleProofs.eo_has_smt_translation x ∧
                                RuleProofs.eo_has_smt_translation y ∧
                                  __smtx_type_wf
                                    (__eo_to_smt_type
                                      (Term.Apply (Term.UOp UserOp.Set) T)) =
                                    true ∧
                                    True := by
                            simpa [cmdTranslationOk, cArgListTranslationOkMask,
                              argTranslationOkMasked] using hCmdTrans
                          have hxTrans : RuleProofs.eo_has_smt_translation x :=
                            hMask.1
                          have hyTrans : RuleProofs.eo_has_smt_translation y :=
                            hMask.2.1
                          have hTypeWf :
                              __smtx_type_wf
                                  (__eo_to_smt_type
                                    (Term.Apply (Term.UOp UserOp.Set) T)) =
                                true :=
                            hMask.2.2.1
                          have hFormulaTy :
                              __eo_typeof
                                  (SetsBasicRewritesSupport.mkEq
                                    (SetsBasicRewritesSupport.mkEq x
                                      (SetsBasicRewritesSupport.mkSetSingleton y))
                                    (Term.Boolean false)) = Term.Bool := by
                            simpa [hProgEq] using hResultTy
                          have hFormulaBool :
                              RuleProofs.eo_has_bool_type
                                (SetsBasicRewritesSupport.mkEq
                                  (SetsBasicRewritesSupport.mkEq x
                                    (SetsBasicRewritesSupport.mkSetSingleton y))
                                  (Term.Boolean false)) :=
                            SetsBasicRewritesSupport.typed_set_eq_singleton_emp
                              x y hxTrans hyTrans hFormulaTy
                          have hPremBoolRaw : RuleProofs.eo_has_bool_type P :=
                            hPremisesBool P (by simp [P, premiseTermList])
                          have hPremBool :
                              RuleProofs.eo_has_bool_type
                                (SetsBasicRewritesSupport.mkEq x
                                  (SetsBasicRewritesSupport.mkSetEmpty T)) := by
                            simpa [hPremShape] using hPremBoolRaw
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (SetsBasicRewritesSupport.mkEq x
                                    (SetsBasicRewritesSupport.mkSetEmpty T))
                                  true := by
                              simpa [hPremShape] using hPremRaw
                            change
                              eo_interprets M
                                (__eo_prog_sets_eq_singleton_emp x y
                                  (Term.Apply (Term.UOp UserOp.Set) T)
                                  (Proof.pf P)) true
                            rw [hProgEq]
                            exact
                              SetsBasicRewritesSupport.facts_set_eq_singleton_emp_false
                                M hM x y T hxTrans hyTrans hTypeWf hPremBool
                                hFormulaTy hPrem
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_sets_eq_singleton_emp x y
                                (Term.Apply (Term.UOp UserOp.Set) T)
                                (Proof.pf P))
                            rw [hProgEq]
                            exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                hFormulaBool
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
