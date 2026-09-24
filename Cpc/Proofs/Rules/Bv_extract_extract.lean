module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_extract_extract_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_extract args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_extract args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_extract args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_extract args premises ≠
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
      | cons i args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons j args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons k args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons l args =>
                      cases args with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons ll args =>
                          cases args with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons kk args =>
                              cases args with
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  cases premises with
                                  | nil =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                                  | cons n1 premises =>
                                      cases premises with
                                      | nil =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                      | cons n2 premises =>
                                          cases premises with
                                          | cons _ _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                          | nil =>
                                              let P1 := __eo_state_proven_nth s n1
                                              let P2 := __eo_state_proven_nth s n2
                                              change StepRuleProperties M [P1, P2]
                                                (bvExtractExtractProgram x i j k l ll kk
                                                  (Proof.pf P1) (Proof.pf P2))
                                              have hArgsTrans :
                                                  RuleProofs.eo_has_smt_translation x ∧
                                                    RuleProofs.eo_has_smt_translation i ∧
                                                    RuleProofs.eo_has_smt_translation j ∧
                                                    RuleProofs.eo_has_smt_translation k ∧
                                                    RuleProofs.eo_has_smt_translation l ∧
                                                    RuleProofs.eo_has_smt_translation ll ∧
                                                    RuleProofs.eo_has_smt_translation kk ∧
                                                    True := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using hCmdTrans
                                              have hXTrans := hArgsTrans.1
                                              have hITrans := hArgsTrans.2.1
                                              have hJTrans := hArgsTrans.2.2.1
                                              have hKTrans := hArgsTrans.2.2.2.1
                                              have hLTrans := hArgsTrans.2.2.2.2.1
                                              have hLlTrans :=
                                                hArgsTrans.2.2.2.2.2.1
                                              have hKkTrans :=
                                                hArgsTrans.2.2.2.2.2.2.1
                                              have hProgramTy :
                                                  __eo_typeof
                                                      (bvExtractExtractProgram
                                                        x i j k l ll kk
                                                        (Proof.pf P1) (Proof.pf P2)) =
                                                    Term.Bool := by
                                                exact hResultTy
                                              refine ⟨?_, ?_⟩
                                              · intro hPremisesTrue
                                                have hP1True : eo_interprets M P1 true :=
                                                  hPremisesTrue P1 (by simp)
                                                have hP2True : eo_interprets M P2 true :=
                                                  hPremisesTrue P2 (by simp)
                                                exact facts_bv_extract_extract_program
                                                  M hM x i j k l ll kk P1 P2
                                                  hXTrans hITrans hJTrans hKTrans
                                                  hLTrans hLlTrans hKkTrans hProgramTy
                                                  hP1True hP2True
                                              · exact
                                                  RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                                    (typed_bv_extract_extract_program
                                                      x i j k l ll kk P1 P2
                                                      hXTrans hITrans hJTrans hKTrans
                                                      hLTrans hLlTrans hKkTrans hProgramTy)
