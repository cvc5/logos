module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_extract_concat_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_concat_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_2 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_concat_2 args premises ≠
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
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons u1 args =>
                          cases args with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons u2 args =>
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
                                              | nil =>
                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                  exact False.elim (hProg rfl)
                                              | cons n4 premises =>
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
                                                      let P4 :=
                                                        __eo_state_proven_nth s n4
                                                      change StepRuleProperties M
                                                        [P1, P2, P3, P4]
                                                        (__eo_prog_bv_extract_concat_2
                                                          x xs y i j u1 u2
                                                          (Proof.pf P1)
                                                          (Proof.pf P2)
                                                          (Proof.pf P3)
                                                          (Proof.pf P4))
                                                      have hArgsTrans :
                                                          RuleProofs.eo_has_smt_translation x ∧
                                                            RuleProofs.eo_has_smt_translation xs ∧
                                                            RuleProofs.eo_has_smt_translation y ∧
                                                            RuleProofs.eo_has_smt_translation i ∧
                                                            RuleProofs.eo_has_smt_translation j ∧
                                                            RuleProofs.eo_has_smt_translation u1 ∧
                                                            RuleProofs.eo_has_smt_translation u2 ∧
                                                            True := by
                                                        simpa [cmdTranslationOk,
                                                          cArgListTranslationOk] using
                                                          hCmdTrans
                                                      have hXTrans := hArgsTrans.1
                                                      have hXsTrans := hArgsTrans.2.1
                                                      have hYTrans := hArgsTrans.2.2.1
                                                      have hITrans := hArgsTrans.2.2.2.1
                                                      have hJTrans := hArgsTrans.2.2.2.2.1
                                                      have hU1Trans :=
                                                        hArgsTrans.2.2.2.2.2.1
                                                      have hU2Trans :=
                                                        hArgsTrans.2.2.2.2.2.2.1
                                                      have hProgLocal :
                                                          bvExtractConcat2Program
                                                              x xs y i j u1 u2
                                                              P1 P2 P3 P4 ≠
                                                            Term.Stuck := by
                                                        have hsimpa := hProg
                                                        try simp [bvExtractConcat2Program, P1, P2, P3, P4] at hsimpa ⊢
                                                        exact hsimpa
                                                      rcases
                                                          bvExtractConcat2Program_normalize
                                                            x xs y i j u1 u2
                                                            P1 P2 P3 P4
                                                            hXTrans hXsTrans hYTrans
                                                            hITrans hJTrans hU1Trans
                                                            hU2Trans hProgLocal with
                                                        ⟨hP1, hP2, hP3, hP4, hProgEq⟩
                                                      have hBodyTy :
                                                          __eo_typeof
                                                              (bvExtractConcat2ProgramBody
                                                                x xs y i j u1 u2) =
                                                            Term.Bool := by
                                                        have hTy := hResultTy
                                                        change __eo_typeof
                                                            (bvExtractConcat2Program
                                                              x xs y i j u1 u2
                                                              P1 P2 P3 P4) =
                                                          Term.Bool at hTy
                                                        rw [hProgEq] at hTy
                                                        exact hTy
                                                      have hPremBool :
                                                          RuleProofs.eo_has_bool_type
                                                            (bvExtractConcat2PremI x i) := by
                                                        have h := hPremisesBool P1
                                                          (by
                                                            simp [premiseTermList, P1])
                                                        rw [hP1] at h
                                                        exact h
                                                      refine ⟨?_, ?_⟩
                                                      · intro hPremEvidence
                                                        change eo_interprets M
                                                          (__eo_prog_bv_extract_concat_2
                                                            x xs y i j u1 u2
                                                            (Proof.pf P1)
                                                            (Proof.pf P2)
                                                            (Proof.pf P3)
                                                            (Proof.pf P4)) true
                                                        have hP1True :
                                                            eo_interprets M
                                                              (bvExtractConcat2PremI x i)
                                                              true := by
                                                          have h := hPremEvidence P1
                                                            (by simp [P1, P2, P3, P4])
                                                          rw [hP1] at h
                                                          exact h
                                                        have hP2True :
                                                            eo_interprets M
                                                              (bvExtractConcat2PremJ x j)
                                                              true := by
                                                          have h := hPremEvidence P2
                                                            (by simp [P1, P2, P3, P4])
                                                          rw [hP2] at h
                                                          exact h
                                                        have hP3True :
                                                            eo_interprets M
                                                              (bvExtractConcat2PremU1 x j u1)
                                                              true := by
                                                          have h := hPremEvidence P3
                                                            (by simp [P1, P2, P3, P4])
                                                          rw [hP3] at h
                                                          exact h
                                                        have hP4True :
                                                            eo_interprets M
                                                              (bvExtractConcat2PremU2 x u2)
                                                              true := by
                                                          have h := hPremEvidence P4
                                                            (by simp [P1, P2, P3, P4])
                                                          rw [hP4] at h
                                                          exact h
                                                        rw [show
                                                          __eo_prog_bv_extract_concat_2
                                                              x xs y i j u1 u2
                                                              (Proof.pf P1)
                                                              (Proof.pf P2)
                                                              (Proof.pf P3)
                                                              (Proof.pf P4) =
                                                            bvExtractConcat2ProgramBody
                                                              x xs y i j u1 u2 by
                                                          simpa [bvExtractConcat2Program]
                                                            using hProgEq]
                                                        exact
                                                          facts_bv_extract_concat2_program_body
                                                            M hM x xs y i j u1 u2
                                                            hYTrans hXsTrans hPremBool
                                                            hBodyTy hP1True hP2True
                                                            hP3True hP4True
                                                      · rw [show
                                                          __eo_prog_bv_extract_concat_2
                                                              x xs y i j u1 u2
                                                              (Proof.pf P1)
                                                              (Proof.pf P2)
                                                              (Proof.pf P3)
                                                              (Proof.pf P4) =
                                                            bvExtractConcat2ProgramBody
                                                              x xs y i j u1 u2 by
                                                          simpa [bvExtractConcat2Program]
                                                            using hProgEq]
                                                        exact
                                                          RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                            _
                                                            (typed_bv_extract_concat2_program_body
                                                              x xs y i j u1 u2
                                                              hYTrans hXsTrans
                                                              hPremBool hBodyTy)
