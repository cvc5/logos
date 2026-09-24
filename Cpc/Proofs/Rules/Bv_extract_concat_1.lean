module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_extract_concat_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_concat_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_1 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_concat_1 args premises ≠
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
      | cons xs args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons y args =>
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
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  change StepRuleProperties M [P1]
                                    (__eo_prog_bv_extract_concat_1 x xs y i j
                                      (Proof.pf P1))
                                  have hArgsTrans :
                                      RuleProofs.eo_has_smt_translation x ∧
                                        RuleProofs.eo_has_smt_translation xs ∧
                                        RuleProofs.eo_has_smt_translation y ∧
                                        RuleProofs.eo_has_smt_translation i ∧
                                        RuleProofs.eo_has_smt_translation j ∧
                                        True := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans
                                  have hXTrans := hArgsTrans.1
                                  have hXsTrans := hArgsTrans.2.1
                                  have hYTrans := hArgsTrans.2.2.1
                                  have hITrans := hArgsTrans.2.2.2.1
                                  have hJTrans := hArgsTrans.2.2.2.2.1
                                  have hProgLocal :
                                      bvExtractConcat1Program x xs y i j
                                          (Proof.pf P1) ≠ Term.Stuck := by
                                    have hsimpa := hProg
                                    try simp [bvExtractConcat1Program, P1] at hsimpa ⊢
                                    exact hsimpa
                                  rcases bvExtractConcat1Program_normalize
                                      x xs y i j P1 hXTrans hXsTrans
                                      hYTrans hITrans hJTrans hProgLocal with
                                    ⟨hP1, hProgEq⟩
                                  have hBodyTy :
                                      __eo_typeof
                                          (bvExtractConcat1ProgramBody x xs y i j) =
                                        Term.Bool := by
                                    have hTy := hResultTy
                                    change __eo_typeof
                                        (bvExtractConcat1Program x xs y i j
                                          (Proof.pf P1)) = Term.Bool at hTy
                                    rw [hProgEq] at hTy
                                    exact hTy
                                  have hPremBool :
                                      RuleProofs.eo_has_bool_type
                                        (bvExtractConcat1Prem x j) := by
                                    have h := hPremisesBool P1
                                      (by simp [premiseTermList, P1])
                                    rw [hP1] at h
                                    exact h
                                  refine ⟨?_, ?_⟩
                                  · intro hPremEvidence
                                    change eo_interprets M
                                      (__eo_prog_bv_extract_concat_1 x xs y i j
                                        (Proof.pf P1)) true
                                    have hPremTrue :
                                        eo_interprets M
                                          (bvExtractConcat1Prem x j)
                                          true := by
                                      have h := hPremEvidence P1
                                        (by simp [P1])
                                      rw [hP1] at h
                                      exact h
                                    rw [show
                                      __eo_prog_bv_extract_concat_1 x xs y i j
                                          (Proof.pf P1) =
                                        bvExtractConcat1ProgramBody x xs y i j by
                                      simpa [bvExtractConcat1Program] using
                                        hProgEq]
                                    exact facts_bv_extract_concat1_program_body
                                      M hM x xs y i j hXsTrans hYTrans
                                      hPremBool hBodyTy hPremTrue
                                  · rw [show
                                      __eo_prog_bv_extract_concat_1 x xs y i j
                                          (Proof.pf P1) =
                                        bvExtractConcat1ProgramBody x xs y i j by
                                      simpa [bvExtractConcat1Program] using
                                        hProgEq]
                                    exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (typed_bv_extract_concat1_program_body
                                          x xs y i j hXsTrans hYTrans
                                          hPremBool hBodyTy)
