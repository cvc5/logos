module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_sets_minus_self_eq_of_ne_stuck (x T : Term) :
    x ≠ Term.Stuck ->
    __eo_prog_sets_minus_self x (Term.Apply (Term.UOp UserOp.Set) T) =
      SetsBasicRewritesSupport.mkEq
        (SetsBasicRewritesSupport.mkSetMinus x x)
        (SetsBasicRewritesSupport.mkSetEmpty T) := by
  intro hx
  cases x <;>
    simp [__eo_prog_sets_minus_self,
      SetsBasicRewritesSupport.mkEq,
      SetsBasicRewritesSupport.mkSetMinus,
      SetsBasicRewritesSupport.mkSetEmpty] at hx ⊢

public theorem cmd_step_sets_minus_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_minus_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_minus_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_minus_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_minus_self args premises ≠ Term.Stuck :=
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
      | cons ty args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  change __eo_typeof (__eo_prog_sets_minus_self x ty) = Term.Bool at hResultTy
                  have hProgProg :
                      __eo_prog_sets_minus_self x ty ≠ Term.Stuck :=
                    term_ne_stuck_of_typeof_bool hResultTy
                  cases ty with
                  | Apply f T =>
                      cases f with
                      | UOp op =>
                          by_cases hSet : op = UserOp.Set
                          · subst op
                            have hMask :
                                RuleProofs.eo_has_smt_translation x ∧
                                  __smtx_type_wf
                                    (__eo_to_smt_type
                                      (Term.Apply (Term.UOp UserOp.Set) T)) = true ∧
                                    True := by
                              simpa [cmdTranslationOk, cArgListTranslationOkMask,
                                argTranslationOkMasked] using hCmdTrans
                            have hxTrans : RuleProofs.eo_has_smt_translation x :=
                              hMask.1
                            have hTypeWf :
                                __smtx_type_wf
                                    (__eo_to_smt_type
                                      (Term.Apply (Term.UOp UserOp.Set) T)) = true :=
                              hMask.2.1
                            have hxNe : x ≠ Term.Stuck :=
                              RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
                            have hProgEq :
                                __eo_prog_sets_minus_self x
                                    (Term.Apply (Term.UOp UserOp.Set) T) =
                                  SetsBasicRewritesSupport.mkEq
                                    (SetsBasicRewritesSupport.mkSetMinus x x)
                                    (SetsBasicRewritesSupport.mkSetEmpty T) := by
                              exact prog_sets_minus_self_eq_of_ne_stuck x T hxNe
                            have hFormulaTy :
                                __eo_typeof
                                    (SetsBasicRewritesSupport.mkEq
                                      (SetsBasicRewritesSupport.mkSetMinus x x)
                                      (SetsBasicRewritesSupport.mkSetEmpty T)) =
                                  Term.Bool := by
                              simpa [hProgEq] using hResultTy
                            refine ⟨?_, ?_⟩
                            · intro _hPremisesTrue
                              change
                                eo_interprets M
                                  (__eo_prog_sets_minus_self x
                                    (Term.Apply (Term.UOp UserOp.Set) T)) true
                              rw [hProgEq]
                              exact SetsBasicRewritesSupport.facts_set_minus_self_eq_empty M hM x T
                                hxTrans hTypeWf hFormulaTy
                            · change RuleProofs.eo_has_smt_translation
                                (__eo_prog_sets_minus_self x
                                  (Term.Apply (Term.UOp UserOp.Set) T))
                              rw [hProgEq]
                              exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (SetsBasicRewritesSupport.typed_set_minus_self_eq_empty
                                  x T hxTrans hTypeWf hFormulaTy)
                          · exact False.elim (hProgProg (by
                              by_cases hx : x = Term.Stuck
                              · subst x
                                simp [__eo_prog_sets_minus_self]
                              · simp [__eo_prog_sets_minus_self, hx, hSet]))
                      | _ =>
                          exact False.elim (hProgProg (by
                            by_cases hx : x = Term.Stuck
                            · subst x
                              simp [__eo_prog_sets_minus_self]
                            · simp [__eo_prog_sets_minus_self, hx]))
                  | _ =>
                      exact False.elim (hProgProg (by
                        by_cases hx : x = Term.Stuck
                        · subst x
                          simp [__eo_prog_sets_minus_self]
                        · simp [__eo_prog_sets_minus_self, hx]))
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
