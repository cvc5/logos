module

public import Cpc.Proofs.RuleSupport.BvAndSimplifySupport
import all Cpc.Proofs.RuleSupport.BvAndSimplifySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_and_simplify_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_and_simplify_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_and_simplify_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_and_simplify_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_and_simplify_1 args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons a5 args =>
                      cases args with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons i1 premises =>
                              cases premises with
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  let P1 := __eo_state_proven_nth s i1
                                  change StepRuleProperties M [P1]
                                    (__eo_prog_bv_and_simplify_1
                                      a1 a2 a3 a4 a5 (Proof.pf P1))
                                  have hProgLocal :
                                      __eo_prog_bv_and_simplify_1
                                          a1 a2 a3 a4 a5 (Proof.pf P1) ≠
                                        Term.Stuck := by
                                    have hsimpa := hProg
                                    try simp [P1] at hsimpa ⊢
                                    exact hsimpa
                                  rcases
                                      BvAndSimplifySupport.program1_shape_of_ne_stuck
                                        a1 a2 a3 a4 a5 P1 hProgLocal with
                                    ⟨hA1Ne, hA2Ne, hA3Ne, hA4Ne, hA5Ne,
                                      pw, px, hP1⟩
                                  have hReqNe := hProgLocal
                                  rw [hP1] at hReqNe
                                  unfold bvAllOnesWidthPrem at hReqNe
                                  rw [__eo_prog_bv_and_simplify_1.eq_6
                                    a1 a2 a3 a4 a5 pw px
                                    hA1Ne hA2Ne hA3Ne hA4Ne hA5Ne] at hReqNe
                                  rcases
                                      RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                        a5 a4 pw px _ hReqNe with
                                    ⟨hPw, hPx⟩
                                  subst pw
                                  subst px
                                  have hResultTyCanonical :
                                      __eo_typeof
                                          (__eo_prog_bv_and_simplify_1
                                            a1 a2 a3 a4 a5
                                            (Proof.pf
                                              (bvAllOnesWidthPrem a4 a5))) =
                                        Term.Bool := by
                                    have h := hResultTy
                                    change __eo_typeof
                                        (__eo_prog_bv_and_simplify_1
                                          a1 a2 a3 a4 a5
                                          (Proof.pf
                                            (__eo_state_proven_nth s i1))) =
                                      Term.Bool at h
                                    simpa [P1, hP1] using h
                                  rcases BvAndSimplifySupport.program1_context
                                      a1 a2 a3 a4 a5 hA1Ne hA2Ne hA3Ne
                                      hA4Ne hA5Ne hResultTyCanonical with
                                    ⟨hProgEq, hA1List, hA2List, hA3List⟩
                                  have hTermTy :
                                      __eo_typeof
                                          (BvAndSimplifySupport.andTerm1
                                            a1 a2 a3 a4 a5) = Term.Bool := by
                                    rw [hProgEq] at hResultTyCanonical
                                    exact hResultTyCanonical
                                  have hArgTranslations :
                                      RuleProofs.eo_has_smt_translation a1 ∧
                                      RuleProofs.eo_has_smt_translation a2 ∧
                                      RuleProofs.eo_has_smt_translation a3 ∧
                                      RuleProofs.eo_has_smt_translation a4 ∧
                                      RuleProofs.eo_has_smt_translation a5 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk,
                                      eoHasSmtTranslation,
                                      RuleProofs.eo_has_smt_translation] using
                                      hCmdTrans
                                  rcases
                                      BvAndSimplifySupport.inferred_argument_types1
                                        a1 a2 a3 a4 a5
                                        hArgTranslations.1
                                        hArgTranslations.2.1
                                        hArgTranslations.2.2.1
                                        hArgTranslations.2.2.2.1
                                        hArgTranslations.2.2.2.2
                                        hA1List hA2List hTermTy with
                                    ⟨W, hA5, hW0, hA1Ty, hA2Ty,
                                      hA3Ty, hA4Ty⟩
                                  simpa [P1, hP1, hProgEq] using
                                    (show StepRuleProperties M
                                        [bvAllOnesWidthPrem a4 a5]
                                        (BvAndSimplifySupport.andTerm1
                                          a1 a2 a3 a4 a5) from
                                      ⟨(by
                                          intro _hPremisesTrue
                                          exact
                                            BvAndSimplifySupport.facts_term1_of_type_or_nil
                                              M hM a1 a2 a3 a4 a5 W
                                              hA1Ty hA2Ty hA3Ty hA4Ty
                                              hA5 hW0 hA1List hA2List hA3List),
                                        RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                          (BvAndSimplifySupport.typed_term1_of_type_or_nil
                                            a1 a2 a3 a4 a5 W
                                            hA1Ty hA2Ty hA3Ty hA4Ty
                                            hA5 hW0 hA1List hA2List hA3List)⟩)
