module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_bv_ult_ones_eq_of_ne_stuck
    (x n w : Term) :
    x ≠ Term.Stuck -> n ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_typeof x ≠ Term.Stuck ->
    __eo_prog_bv_ult_ones x n w
        (Proof.pf (bvAllOnesValuePrem n w)) =
      bvUltOnesTerm x n w := by
  intro hX hN hW hXTy
  unfold bvAllOnesValuePrem
  rw [__eo_prog_bv_ult_ones.eq_4 x n w n w hX hN hW]
  simp [bvUltOnesTerm, bvUltOnesDistinct, bvUltOnesList,
    bvAllOnesConst, __eo_requires, __eo_and, __eo_eq,
    __eo_mk_apply, __eo_nil, __eo_nil__at__at_TypedList_cons,
    native_ite, native_teq, native_not, SmtEval.native_not,
    SmtEval.native_and, hX, hN, hW, hXTy]

private theorem bv_ult_ones_shape_of_ne_stuck
    (x n w P : Term) :
    __eo_prog_bv_ult_ones x n w (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      ∃ pn pw, P = bvAllOnesValuePrem pn pw := by
  intro hProg
  have hX : x ≠ Term.Stuck := by
    intro h
    subst x
    exact hProg (__eo_prog_bv_ult_ones.eq_1 n w (Proof.pf P))
  have hN : n ≠ Term.Stuck := by
    intro h
    subst n
    exact hProg (__eo_prog_bv_ult_ones.eq_2 x w (Proof.pf P) hX)
  have hW : w ≠ Term.Stuck := by
    intro h
    subst w
    exact hProg (__eo_prog_bv_ult_ones.eq_3 x n (Proof.pf P) hX hN)
  by_cases hShape : ∃ pn pw, P = bvAllOnesValuePrem pn pw
  · rcases hShape with ⟨pn, pw, hP⟩
    exact ⟨hX, hN, hW, pn, pw, hP⟩
  · have hStuck :
        __eo_prog_bv_ult_ones x n w (Proof.pf P) = Term.Stuck := by
      exact __eo_prog_bv_ult_ones.eq_5 x n w (Proof.pf P)
        hX hN hW (by
          intro pn pw hp
          cases hp
          exact hShape ⟨pn, pw, rfl⟩)
    exact False.elim (hProg hStuck)

private theorem eo_typeof_ne_stuck_of_translation
    (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x ≠ Term.Stuck := by
  intro hTrans hType
  have hTypeMatch :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (__eo_typeof x) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hTrans rfl
  have hNone : __eo_to_smt_type (__eo_typeof x) = SmtType.None := by
    rw [hType]
    rfl
  rw [hNone] at hTypeMatch
  exact hTrans hTypeMatch

public theorem cmd_step_bv_ult_ones_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_ones args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ult_ones args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_ones args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_ult_ones args premises ≠
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
                            (__eo_prog_bv_ult_ones a1 a2 a3 (Proof.pf P1))
                          have hProgLocal :
                              __eo_prog_bv_ult_ones a1 a2 a3
                                  (Proof.pf P1) ≠ Term.Stuck := by
                            have hsimpa := hProg
                            try simp [P1] at hsimpa ⊢
                            exact hsimpa
                          rcases bv_ult_ones_shape_of_ne_stuck
                              a1 a2 a3 P1 hProgLocal with
                            ⟨hA1Ne, hA2Ne, hA3Ne, pn, pw, hP1⟩
                          have hReqNe := hProgLocal
                          rw [hP1] at hReqNe
                          unfold bvAllOnesValuePrem at hReqNe
                          rw [__eo_prog_bv_ult_ones.eq_4
                            a1 a2 a3 pn pw hA1Ne hA2Ne hA3Ne] at hReqNe
                          rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                              a2 a3 pn pw _ hReqNe with
                            ⟨hPn, hPw⟩
                          subst pn
                          subst pw
                          have hArgs :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                RuleProofs.eo_has_smt_translation a3 ∧
                                True := by
                            simpa [cmdTranslationOk,
                              cArgListTranslationOk,
                              RuleProofs.eo_has_smt_translation,
                              eoHasSmtTranslation] using hCmdTrans
                          have hA1Trans := hArgs.1
                          have hA2Trans := hArgs.2.1
                          have hA3Trans := hArgs.2.2.1
                          have hA1TypeNe : __eo_typeof a1 ≠ Term.Stuck :=
                            eo_typeof_ne_stuck_of_translation a1 hA1Trans
                          have hResultTyCanonical :
                              __eo_typeof (bvUltOnesTerm a1 a2 a3) =
                                Term.Bool := by
                            have h := hResultTy
                            change __eo_typeof
                                (__eo_prog_bv_ult_ones a1 a2 a3
                                  (Proof.pf (__eo_state_proven_nth s i1))) =
                              Term.Bool at h
                            simpa [P1, hP1,
                              prog_bv_ult_ones_eq_of_ne_stuck
                                a1 a2 a3 hA1Ne hA2Ne hA3Ne hA1TypeNe] using h
                          simpa [hP1,
                              prog_bv_ult_ones_eq_of_ne_stuck
                                a1 a2 a3 hA1Ne hA2Ne hA3Ne hA1TypeNe] using
                            (show StepRuleProperties M
                                [bvAllOnesValuePrem a2 a3]
                                (bvUltOnesTerm a1 a2 a3) from
                              ⟨(by
                                  intro hPremisesTrue
                                  have hPrem :
                                      eo_interprets M
                                        (bvAllOnesValuePrem a2 a3) true :=
                                    hPremisesTrue.true_here _ (by simp)
                                  exact facts_bv_ult_ones_term M hM
                                    a1 a2 a3 hA1Trans
                                    hA2Trans hA3Trans hPrem
                                    hResultTyCanonical),
                                RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed_bv_ult_ones_term a1 a2 a3
                                    hA1Trans hA2Trans hA3Trans
                                    hResultTyCanonical)⟩)
