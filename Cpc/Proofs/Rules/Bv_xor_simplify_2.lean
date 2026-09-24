module

public import Cpc.Proofs.RuleSupport.BvXorSimplifySupport
import all Cpc.Proofs.RuleSupport.BvXorSimplifySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_xor_simplify_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_simplify_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises ≠
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
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hArgTranslations :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                RuleProofs.eo_has_smt_translation a3 ∧
                                RuleProofs.eo_has_smt_translation a4 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk,
                              eoHasSmtTranslation,
                              RuleProofs.eo_has_smt_translation] using hCmdTrans
                          have hA1Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a1
                              hArgTranslations.1
                          have hA2Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a2
                              hArgTranslations.2.1
                          have hA3Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a3
                              hArgTranslations.2.2.1
                          have hA4Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a4
                              hArgTranslations.2.2.2
                          change __eo_typeof
                              (__eo_prog_bv_xor_simplify_2 a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          have hLists :=
                            BvXorSimplifySupport.program2_lists_of_ne_stuck
                              a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne
                              hResultTy
                          have hProgEq :=
                            BvXorSimplifySupport.program2_eq_term_of_ne_stuck
                              a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne
                              hResultTy
                          have hTermTy :
                              __eo_typeof
                                  (BvXorSimplifySupport.term2 a1 a2 a3 a4) =
                                Term.Bool := by
                            rw [hProgEq] at hResultTy
                            exact hResultTy
                          rcases BvXorSimplifySupport.inferred_argument_types2
                              a1 a2 a3 a4 hArgTranslations.1
                              hArgTranslations.2.1 hArgTranslations.2.2.1
                              hArgTranslations.2.2.2 hLists.1 hLists.2.1
                              hTermTy with
                            ⟨width, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                          change StepRuleProperties M []
                            (__eo_prog_bv_xor_simplify_2 a1 a2 a3 a4)
                          rw [hProgEq]
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            exact
                              BvXorSimplifySupport.facts_term2_of_type_or_nil M hM
                              a1 a2 a3 a4 width
                              hA1Ty hA2Ty hA3Ty hA4Ty
                              hLists.1 hLists.2.1 hLists.2.2
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (BvXorSimplifySupport.typed_term2_of_type_or_nil
                                  a1 a2 a3 a4 width
                                  hA1Ty hA2Ty hA3Ty hA4Ty
                                  hLists.1 hLists.2.1 hLists.2.2)
