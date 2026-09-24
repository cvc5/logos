module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

public theorem cmd_step_sets_union_emp2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_union_emp2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_union_emp2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_union_emp2 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_union_emp2 args premises ≠ Term.Stuck :=
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
                                (__eo_prog_sets_union_emp2 x y ty
                                  (Proof.pf P)) = Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_sets_union_emp2 x y ty
                                  (Proof.pf P) ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases SetsBasicRewritesSupport.prog_sets_union_emp2_info
                              x y ty P hProgRule with
                            ⟨T, y0, T0, hTyArg, hPremShape, hy0, hT0,
                              hProgEq⟩
                          subst ty
                          subst y0
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
                                    (SetsBasicRewritesSupport.mkSetUnion x y)
                                    x) = Term.Bool := by
                            simpa [hProgEq] using hResultTy
                          have hFormulaBool :
                              RuleProofs.eo_has_bool_type
                                (SetsBasicRewritesSupport.mkEq
                                  (SetsBasicRewritesSupport.mkSetUnion x y)
                                  x) :=
                            SetsBasicRewritesSupport.typed_set_union_eq_right
                              x y x hxTrans hyTrans hxTrans hFormulaTy
                          have hPremBoolRaw : RuleProofs.eo_has_bool_type P :=
                            hPremisesBool P (by simp [P, premiseTermList])
                          have hPremBool :
                              RuleProofs.eo_has_bool_type
                                (SetsBasicRewritesSupport.mkEq y
                                  (SetsBasicRewritesSupport.mkSetEmpty T)) := by
                            simpa [hPremShape] using hPremBoolRaw
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (SetsBasicRewritesSupport.mkEq y
                                    (SetsBasicRewritesSupport.mkSetEmpty T))
                                  true := by
                              simpa [hPremShape] using hPremRaw
                            change
                              eo_interprets M
                                (__eo_prog_sets_union_emp2 x y
                                  (Term.Apply (Term.UOp UserOp.Set) T)
                                  (Proof.pf P)) true
                            rw [hProgEq]
                            exact RuleProofs.eo_interprets_eq_of_rel M
                              (SetsBasicRewritesSupport.mkSetUnion x y) x
                              hFormulaBool
                              (SetsBasicRewritesSupport.set_union_empty_right_rel_of_premise_bool
                                M hM x y T hxTrans hyTrans hTypeWf
                                hPremBool hFormulaTy hPrem)
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_sets_union_emp2 x y
                                (Term.Apply (Term.UOp UserOp.Set) T)
                                (Proof.pf P))
                            rw [hProgEq]
                            exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              hFormulaBool
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
