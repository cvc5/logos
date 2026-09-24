module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_extract_concat_3_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_concat_3 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_3 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_concat_3 args premises ≠
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
          | cons xs args =>
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
                      | cons u args =>
                          cases args with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons l args =>
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
                                          | nil =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                          | cons n3 premises =>
                                              cases premises with
                                              | cons _ _ =>
                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                  exact False.elim (hProg rfl)
                                              | nil =>
                                                  let P1 :=
                                                    __eo_state_proven_nth s n1
                                                  let P2 :=
                                                    __eo_state_proven_nth s n2
                                                  let P3 :=
                                                    __eo_state_proven_nth s n3
                                                  change StepRuleProperties M
                                                    [P1, P2, P3]
                                                    (__eo_prog_bv_extract_concat_3
                                                      x y xs i j u l
                                                      (Proof.pf P1)
                                                      (Proof.pf P2)
                                                      (Proof.pf P3))
                                                  have hArgsTrans :
                                                      RuleProofs.eo_has_smt_translation x ∧
                                                        RuleProofs.eo_has_smt_translation y ∧
                                                        RuleProofs.eo_has_smt_translation xs ∧
                                                        RuleProofs.eo_has_smt_translation i ∧
                                                        RuleProofs.eo_has_smt_translation j ∧
                                                        RuleProofs.eo_has_smt_translation u ∧
                                                        RuleProofs.eo_has_smt_translation l ∧
                                                        True := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                      hCmdTrans
                                                  have hXTrans := hArgsTrans.1
                                                  have hYTrans := hArgsTrans.2.1
                                                  have hXsTrans := hArgsTrans.2.2.1
                                                  have hITrans := hArgsTrans.2.2.2.1
                                                  have hJTrans := hArgsTrans.2.2.2.2.1
                                                  have hUTrans := hArgsTrans.2.2.2.2.2.1
                                                  have hLTrans :=
                                                    hArgsTrans.2.2.2.2.2.2.1
                                                  have hProgLocal :
                                                      bvExtractConcat3Program
                                                          x y xs i j u l P1 P2 P3 ≠
                                                        Term.Stuck := by
                                                    have hsimpa := hProg
                                                    try simp [bvExtractConcat3Program, P1, P2, P3] at hsimpa ⊢
                                                    exact hsimpa
                                                  rcases
                                                      bvExtractConcat3Program_normalize
                                                        x y xs i j u l P1 P2 P3
                                                        hXTrans hYTrans hXsTrans
                                                        hITrans hJTrans hUTrans
                                                        hLTrans hProgLocal with
                                                    ⟨hP1, hP2, hP3, hProgEq⟩
                                                  have hBodyTy :
                                                      __eo_typeof
                                                          (bvExtractConcat3ProgramBody
                                                            x y xs i j u l) =
                                                        Term.Bool := by
                                                    have hTy := hResultTy
                                                    change __eo_typeof
                                                        (bvExtractConcat3Program
                                                          x y xs i j u l P1 P2 P3) =
                                                      Term.Bool at hTy
                                                    rw [hProgEq] at hTy
                                                    exact hTy
                                                  have hPremBool :
                                                      RuleProofs.eo_has_bool_type
                                                        (bvExtractConcat3PremI x i) := by
                                                    have h := hPremisesBool P1
                                                      (by
                                                        simp [premiseTermList, P1])
                                                    rw [hP1] at h
                                                    exact h
                                                  refine ⟨?_, ?_⟩
                                                  · intro hPremEvidence
                                                    change eo_interprets M
                                                      (__eo_prog_bv_extract_concat_3
                                                        x y xs i j u l
                                                        (Proof.pf P1)
                                                        (Proof.pf P2)
                                                        (Proof.pf P3)) true
                                                    have hP1True :
                                                        eo_interprets M
                                                          (bvExtractConcat3PremI x i)
                                                          true := by
                                                      have h := hPremEvidence P1
                                                        (by simp [P1, P2, P3])
                                                      rw [hP1] at h
                                                      exact h
                                                    have hP2True :
                                                        eo_interprets M
                                                          (bvExtractConcat3PremU x j u)
                                                          true := by
                                                      have h := hPremEvidence P2
                                                        (by simp [P1, P2, P3])
                                                      rw [hP2] at h
                                                      exact h
                                                    have hP3True :
                                                        eo_interprets M
                                                          (bvExtractConcat3PremL x i l)
                                                          true := by
                                                      have h := hPremEvidence P3
                                                        (by simp [P1, P2, P3])
                                                      rw [hP3] at h
                                                      exact h
                                                    rw [show
                                                      __eo_prog_bv_extract_concat_3
                                                          x y xs i j u l
                                                          (Proof.pf P1)
                                                          (Proof.pf P2)
                                                          (Proof.pf P3) =
                                                        bvExtractConcat3ProgramBody
                                                          x y xs i j u l by
                                                      simpa [bvExtractConcat3Program]
                                                        using hProgEq]
                                                    exact
                                                      facts_bv_extract_concat3_program_body
                                                        M hM x y xs i j u l
                                                        hYTrans hXsTrans hPremBool
                                                        hBodyTy hP1True hP2True hP3True
                                                  · rw [show
                                                      __eo_prog_bv_extract_concat_3
                                                          x y xs i j u l
                                                          (Proof.pf P1)
                                                          (Proof.pf P2)
                                                          (Proof.pf P3) =
                                                        bvExtractConcat3ProgramBody
                                                          x y xs i j u l by
                                                      simpa [bvExtractConcat3Program]
                                                        using hProgEq]
                                                    exact
                                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                        _
                                                        (typed_bv_extract_concat3_program_body
                                                          x y xs i j u l hYTrans
                                                          hXsTrans hPremBool hBodyTy)
