module

public import Cpc.Proofs.RuleSupport.BvRotateDecompSupport
import all Cpc.Proofs.RuleSupport.BvRotateDecompSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_rotate_left_eliminate_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_rotate_left_eliminate_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_1 args premises ≠
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
      | cons amount args =>
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
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons l1 args =>
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
                                              let P1 := __eo_state_proven_nth s n1
                                              let P2 := __eo_state_proven_nth s n2
                                              let P3 := __eo_state_proven_nth s n3
                                              let P4 := __eo_state_proven_nth s n4
                                              change StepRuleProperties M
                                                [P1, P2, P3, P4]
                                                (__eo_prog_bv_rotate_left_eliminate_1
                                                  x amount u1 u2 l1
                                                  (Proof.pf P1) (Proof.pf P2)
                                                  (Proof.pf P3) (Proof.pf P4))
                                              have hProgLocal :
                                                  __eo_prog_bv_rotate_left_eliminate_1
                                                      x amount u1 u2 l1
                                                      (Proof.pf P1) (Proof.pf P2)
                                                      (Proof.pf P3) (Proof.pf P4) ≠
                                                    Term.Stuck := by
                                                exact hProg
                                              rcases
                                                  bv_rotate_left_decomp_shape_of_ne_stuck
                                                    x amount u1 u2 l1 P1 P2 P3 P4
                                                    hProgLocal with
                                                ⟨hXNe, hAmountNe, hU1Ne, hU2Ne,
                                                  hL1Ne, pa1, px1, pu1, px2, pa2,
                                                  px3, pu2, px4, pl1, px5, pa3, px6,
                                                  hP1, hP2, hP3, hP4⟩
                                              have hReqNe := hProgLocal
                                              rw [hP1, hP2, hP3, hP4] at hReqNe
                                              unfold bvRotateNonzeroPrem
                                                bvRotateLeftUpper1PremRaw
                                                bvRotateUpper2Prem
                                                bvRotateLeftLowerPremRaw
                                                bvRotateWidthMinusOneTerm
                                                bvRotateModTerm at hReqNe
                                              rw [__eo_prog_bv_rotate_left_eliminate_1.eq_6
                                                x amount u1 u2 l1 pa1 px1 pu1 px2
                                                pa2 px3 pu2 px4 pl1 px5 pa3 px6
                                                hXNe hAmountNe hU1Ne hU2Ne hL1Ne]
                                                at hReqNe
                                              rcases bv_rotate_left_decomp_guard_eqs
                                                  x amount u1 u2 l1 pa1 px1 pu1 px2
                                                  pa2 px3 pu2 px4 pl1 px5 pa3 px6 _
                                                  hReqNe with
                                                ⟨hPa1, hPx1, hPu1, hPx2, hPa2,
                                                  hPx3, hPu2, hPx4, hPl1, hPx5,
                                                  hPa3, hPx6⟩
                                              subst pa1
                                              subst px1
                                              subst pu1
                                              subst px2
                                              subst pa2
                                              subst px3
                                              subst pu2
                                              subst px4
                                              subst pl1
                                              subst px5
                                              subst pa3
                                              subst px6
                                              have hP1Canonical :
                                                  P1 = bvRotateNonzeroPrem x amount := hP1
                                              have hP2Canonical :
                                                  P2 = bvRotateLeftUpper1Prem x amount u1 := by
                                                simpa [bvRotateLeftUpper1Prem] using hP2
                                              have hP3Canonical :
                                                  P3 = bvRotateUpper2Prem x u2 := hP3
                                              have hP4Canonical :
                                                  P4 = bvRotateLeftLowerPrem x amount l1 := by
                                                simpa [bvRotateLeftLowerPrem] using hP4
                                              have hArgsTrans :
                                                  RuleProofs.eo_has_smt_translation x ∧
                                                    RuleProofs.eo_has_smt_translation amount ∧
                                                    RuleProofs.eo_has_smt_translation u1 ∧
                                                    RuleProofs.eo_has_smt_translation u2 ∧
                                                    RuleProofs.eo_has_smt_translation l1 ∧
                                                    True := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using hCmdTrans
                                              have hXTrans := hArgsTrans.1
                                              have hProgramEq :=
                                                bv_rotate_left_decomp_program_eq_term_of_ne_stuck
                                                  x amount u1 u2 l1 hXNe hAmountNe
                                                  hU1Ne hU2Ne hL1Ne
                                              have hProgramTy :
                                                  __eo_typeof
                                                      (bvRotateLeftDecompProgram
                                                        x amount u1 u2 l1) = Term.Bool := by
                                                have h := hResultTy
                                                change __eo_typeof
                                                    (__eo_prog_bv_rotate_left_eliminate_1
                                                      x amount u1 u2 l1
                                                      (Proof.pf P1) (Proof.pf P2)
                                                      (Proof.pf P3) (Proof.pf P4)) =
                                                  Term.Bool at h
                                                simpa [hP1Canonical, hP2Canonical,
                                                  hP3Canonical, hP4Canonical,
                                                  bvRotateLeftDecompProgram] using h
                                              have hTermTy :
                                                  __eo_typeof
                                                      (bvRotateDecompTerm .left
                                                        x amount u1 u2 l1) = Term.Bool := by
                                                rw [← hProgramEq]
                                                exact hProgramTy
                                              simpa [hP1Canonical, hP2Canonical,
                                                hP3Canonical, hP4Canonical,
                                                bvRotateLeftDecompProgram] using
                                                (show StepRuleProperties M
                                                    [bvRotateNonzeroPrem x amount,
                                                      bvRotateLeftUpper1Prem x amount u1,
                                                      bvRotateUpper2Prem x u2,
                                                      bvRotateLeftLowerPrem x amount l1]
                                                    (bvRotateLeftDecompProgram
                                                      x amount u1 u2 l1) from
                                                  ⟨(by
                                                      intro hPremisesTrue
                                                      have hPrem1 :=
                                                        hPremisesTrue.true_here
                                                          (bvRotateNonzeroPrem x amount)
                                                          (by simp)
                                                      have hPrem2 :=
                                                        hPremisesTrue.true_here
                                                          (bvRotateLeftUpper1Prem
                                                            x amount u1) (by simp)
                                                      have hPrem3 :=
                                                        hPremisesTrue.true_here
                                                          (bvRotateUpper2Prem x u2)
                                                          (by simp)
                                                      have hPrem4 :=
                                                        hPremisesTrue.true_here
                                                          (bvRotateLeftLowerPrem
                                                            x amount l1) (by simp)
                                                      rw [hProgramEq]
                                                      exact facts_bv_rotate_decomp_term
                                                        M hM .left x amount u1 u2 l1
                                                        hXTrans hTermTy hPrem1 hPrem2
                                                        hPrem3 hPrem4),
                                                    RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                                      (by
                                                        rw [hProgramEq]
                                                        exact typed_bv_rotate_decomp_term
                                                          .left x amount u1 u2 l1
                                                          hXTrans hTermTy)⟩)
