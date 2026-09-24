module

public import Cpc.Proofs.RuleSupport.BvMergeExtendSupport
import all Cpc.Proofs.RuleSupport.BvMergeExtendSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_merge_sign_extend_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_merge_sign_extend_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_merge_sign_extend_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_merge_sign_extend_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_merge_sign_extend_2 args premises ≠
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
                                    (__eo_prog_bv_merge_sign_extend_2
                                      a1 a2 a3 a4
                                      (Proof.pf P1) (Proof.pf P2))
                                  have hProgLocal :
                                      __eo_prog_bv_merge_sign_extend_2
                                          a1 a2 a3 a4
                                          (Proof.pf P1) (Proof.pf P2) ≠
                                        Term.Stuck := by
                                    have hsimpa := hProg
                                    try simp [P1, P2] at hsimpa ⊢
                                    exact hsimpa
                                  rcases
                                      bv_merge_sign_extend_2_shape_of_ne_stuck
                                        a1 a2 a3 a4 P1 P2 hProgLocal with
                                    ⟨hA1Ne, hA2Ne, hA3Ne, hA4Ne,
                                      pjPos, pk, pi, pjSum, hP1, hP2⟩
                                  have hReqNe := hProgLocal
                                  rw [hP1, hP2] at hReqNe
                                  unfold bvMergeSignExtend2PremPos
                                    bvMergeSignExtend2PremSum
                                    bvMergeSignExtend1Prem at hReqNe
                                  rw [__eo_prog_bv_merge_sign_extend_2.eq_5
                                    a1 a2 a3 a4 pjPos pk pi pjSum
                                    hA1Ne hA2Ne hA3Ne hA4Ne] at hReqNe
                                  rcases bv_merge_sign_extend_2_guard_eqs
                                      a1 a2 a3 a4 pjPos pk pi pjSum _
                                      hReqNe with
                                    ⟨hPjPos, hPk, hPi, hPjSum⟩
                                  subst pjPos
                                  subst pk
                                  subst pi
                                  subst pjSum
                                  have hArgsTrans :
                                      RuleProofs.eo_has_smt_translation a1 ∧
                                        RuleProofs.eo_has_smt_translation a2 ∧
                                        RuleProofs.eo_has_smt_translation a3 ∧
                                        RuleProofs.eo_has_smt_translation a4 ∧
                                        True := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans
                                  have hA1Trans := hArgsTrans.1
                                  have hA2Trans := hArgsTrans.2.1
                                  have hA3Trans := hArgsTrans.2.2.1
                                  have hA4Trans := hArgsTrans.2.2.2.1
                                  have hResultTyCanonical :
                                      __eo_typeof
                                          (bvMergeSignExtend2Program
                                            a1 a2 a3 a4) = Term.Bool := by
                                    have h := hResultTy
                                    change __eo_typeof
                                        (__eo_prog_bv_merge_sign_extend_2
                                          a1 a2 a3 a4
                                          (Proof.pf
                                            (__eo_state_proven_nth s n1))
                                          (Proof.pf
                                            (__eo_state_proven_nth s n2))) =
                                      Term.Bool at h
                                    simpa [P1, P2, hP1, hP2,
                                      bvMergeSignExtend2Program] using h
                                  simpa [hP1, hP2,
                                    bvMergeSignExtend2Program] using
                                    (show StepRuleProperties M
                                        [bvMergeSignExtend2PremPos a3,
                                          bvMergeSignExtend2PremSum
                                            a2 a3 a4]
                                        (bvMergeSignExtend2Program
                                          a1 a2 a3 a4) from
                                      ⟨(by
                                          intro hPremisesTrue
                                          have hPremPos :
                                              eo_interprets M
                                                (bvMergeSignExtend2PremPos a3)
                                                true :=
                                            hPremisesTrue.true_here _ (by simp)
                                          have hPremSum :
                                              eo_interprets M
                                                (bvMergeSignExtend2PremSum
                                                  a2 a3 a4) true :=
                                            hPremisesTrue.true_here _ (by simp)
                                          exact
                                            facts_bv_merge_sign_extend_2_program
                                              M hM a1 a2 a3 a4 hA1Trans
                                              hA2Trans hA3Trans hA4Trans
                                              hPremPos hPremSum
                                              hResultTyCanonical),
                                        RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                          (typed_bv_merge_sign_extend_2_program
                                            a1 a2 a3 a4 hA1Trans hA2Trans
                                            hA3Trans hA4Trans
                                            hResultTyCanonical)⟩)
