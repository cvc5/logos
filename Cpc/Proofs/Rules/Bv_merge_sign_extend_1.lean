module

public import Cpc.Proofs.RuleSupport.BvMergeExtendSupport
import all Cpc.Proofs.RuleSupport.BvMergeExtendSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_merge_sign_extend_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_merge_sign_extend_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_merge_sign_extend_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_merge_sign_extend_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_merge_sign_extend_1 args premises ≠
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
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let P1 := __eo_state_proven_nth s n1
                              change StepRuleProperties M [P1]
                                (__eo_prog_bv_merge_sign_extend_1
                                  a1 a2 a3 a4 (Proof.pf P1))
                              have hProgLocal :
                                  __eo_prog_bv_merge_sign_extend_1
                                      a1 a2 a3 a4 (Proof.pf P1) ≠
                                    Term.Stuck := by
                                have hsimpa := hProg
                                try simp [P1] at hsimpa ⊢
                                exact hsimpa
                              rcases bv_merge_sign_extend_1_shape_of_ne_stuck
                                  a1 a2 a3 a4 P1 hProgLocal with
                                ⟨hA1Ne, hA2Ne, hA3Ne, hA4Ne,
                                  pk, pi, pj, hP1⟩
                              have hReqNe := hProgLocal
                              rw [hP1] at hReqNe
                              unfold bvMergeSignExtend1Prem at hReqNe
                              rw [__eo_prog_bv_merge_sign_extend_1.eq_5
                                a1 a2 a3 a4 pk pi pj
                                hA1Ne hA2Ne hA3Ne hA4Ne] at hReqNe
                              rcases bv_merge_sign_extend_1_guard_eqs
                                  a1 a2 a3 a4 pk pi pj _ hReqNe with
                                ⟨hPk, hPi, hPj⟩
                              subst pk
                              subst pi
                              subst pj
                              have hArgsTrans :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                    RuleProofs.eo_has_smt_translation a3 ∧
                                    RuleProofs.eo_has_smt_translation a4 ∧
                                    True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk]
                                  using hCmdTrans
                              have hA1Trans := hArgsTrans.1
                              have hA2Trans := hArgsTrans.2.1
                              have hA3Trans := hArgsTrans.2.2.1
                              have hA4Trans := hArgsTrans.2.2.2.1
                              have hResultTyCanonical :
                                  __eo_typeof
                                      (bvMergeSignExtend1Program
                                        a1 a2 a3 a4) = Term.Bool := by
                                have h := hResultTy
                                change __eo_typeof
                                    (__eo_prog_bv_merge_sign_extend_1
                                      a1 a2 a3 a4
                                      (Proof.pf
                                        (__eo_state_proven_nth s n1))) =
                                  Term.Bool at h
                                simpa [P1, hP1, bvMergeSignExtend1Program]
                                  using h
                              simpa [hP1, bvMergeSignExtend1Program] using
                                (show StepRuleProperties M
                                    [bvMergeSignExtend1Prem a2 a3 a4]
                                    (bvMergeSignExtend1Program
                                      a1 a2 a3 a4) from
                                  ⟨(by
                                      intro hPremisesTrue
                                      have hPrem :
                                          eo_interprets M
                                            (bvMergeSignExtend1Prem
                                              a2 a3 a4) true :=
                                        hPremisesTrue.true_here _ (by simp)
                                      exact
                                        facts_bv_merge_sign_extend_1_program
                                          M hM a1 a2 a3 a4 hA1Trans
                                          hA2Trans hA3Trans hA4Trans hPrem
                                          hResultTyCanonical),
                                    RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (typed_bv_merge_sign_extend_1_program
                                        a1 a2 a3 a4 hA1Trans hA2Trans
                                        hA3Trans hA4Trans
                                        hResultTyCanonical)⟩)
