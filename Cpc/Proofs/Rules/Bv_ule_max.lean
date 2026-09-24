module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem eo_and_eq_true_left_local {x y : Term} :
    __eo_and x y = Term.Boolean true -> x = Term.Boolean true := by
  intro h
  exact (RuleProofs.eo_and_eq_true_args x y h).1

private theorem eo_and_eq_true_right_local {x y : Term} :
    __eo_and x y = Term.Boolean true -> y = Term.Boolean true := by
  intro h
  exact (RuleProofs.eo_and_eq_true_args x y h).2

private theorem prog_bv_ule_max_eq_of_ne_stuck
    (x n w : Term) :
    x ≠ Term.Stuck -> n ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_prog_bv_ule_max x n w
        (Proof.pf (bvAllOnesWidthPrem x w))
        (Proof.pf (bvUleMaxValuePrem x n)) =
      bvUleMaxTerm x n w := by
  intro hX hN hW
  unfold bvAllOnesWidthPrem bvUleMaxValuePrem
  rw [__eo_prog_bv_ule_max.eq_4 x n w w x n x hX hN hW]
  simp [bvUleMaxTerm, bvAllOnesConst, __eo_requires, __eo_and,
    __eo_eq, native_ite, native_teq, native_not, SmtEval.native_not,
    SmtEval.native_and, hX, hN, hW]

private theorem bv_ule_max_shape_of_ne_stuck
    (x n w P1 P2 : Term) :
    __eo_prog_bv_ule_max x n w (Proof.pf P1) (Proof.pf P2) ≠
      Term.Stuck ->
    x ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      ∃ px pw px' pn,
        P1 = bvAllOnesWidthPrem px pw ∧
        P2 = bvUleMaxValuePrem px' pn := by
  intro hProg
  have hX : x ≠ Term.Stuck := by
    intro h
    subst x
    exact hProg (__eo_prog_bv_ule_max.eq_1 n w (Proof.pf P1) (Proof.pf P2))
  have hN : n ≠ Term.Stuck := by
    intro h
    subst n
    exact hProg
      (__eo_prog_bv_ule_max.eq_2 x w (Proof.pf P1) (Proof.pf P2) hX)
  have hW : w ≠ Term.Stuck := by
    intro h
    subst w
    exact hProg
      (__eo_prog_bv_ule_max.eq_3 x n (Proof.pf P1) (Proof.pf P2) hX hN)
  by_cases hShape :
      ∃ pw px pn px',
        P1 = bvAllOnesWidthPrem px pw ∧
        P2 = bvUleMaxValuePrem px' pn
  · rcases hShape with ⟨pw, px, pn, px', hP1, hP2⟩
    exact ⟨hX, hN, hW, px, pw, px', pn, hP1, hP2⟩
  · have hStuck :
        __eo_prog_bv_ule_max x n w (Proof.pf P1) (Proof.pf P2) =
          Term.Stuck := by
      exact __eo_prog_bv_ule_max.eq_5 x n w (Proof.pf P1) (Proof.pf P2)
        hX hN hW (by
          intro pw px pn px' hp1 hp2
          cases hp1
          cases hp2
          exact hShape ⟨pw, px, pn, px', rfl, rfl⟩)
    exact False.elim (hProg hStuck)

private theorem bv_ule_max_bound_vars
    (x n w px pw px' pn : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq w pw) (__eo_eq x px))
            (__eo_eq n pn))
          (__eo_eq x px'))
        (Term.Boolean true) (bvUleMaxTerm x n w) ≠ Term.Stuck ->
    pw = w ∧ px = x ∧ pn = n ∧ px' = x := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  have h123 := eo_and_eq_true_left_local hGuard
  have h4 := eo_and_eq_true_right_local hGuard
  have h12 := eo_and_eq_true_left_local h123
  have h3 := eo_and_eq_true_right_local h123
  have h1 := eo_and_eq_true_left_local h12
  have h2 := eo_and_eq_true_right_local h12
  exact ⟨RuleProofs.eq_of_eo_eq_true w pw h1,
    RuleProofs.eq_of_eo_eq_true x px h2,
    RuleProofs.eq_of_eo_eq_true n pn h3,
    RuleProofs.eq_of_eo_eq_true x px' h4⟩

public theorem cmd_step_bv_ule_max_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ule_max args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ule_max args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ule_max args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_ule_max args premises ≠ Term.Stuck :=
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
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons i2 premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let P1 := __eo_state_proven_nth s i1
                              let P2 := __eo_state_proven_nth s i2
                              change StepRuleProperties M [P1, P2]
                                (__eo_prog_bv_ule_max a1 a2 a3
                                  (Proof.pf P1) (Proof.pf P2))
                              have hProgLocal :
                                  __eo_prog_bv_ule_max a1 a2 a3
                                      (Proof.pf P1) (Proof.pf P2) ≠
                                    Term.Stuck := by
                                have hsimpa := hProg
                                try simp [P1, P2] at hsimpa ⊢
                                exact hsimpa
                              rcases bv_ule_max_shape_of_ne_stuck
                                  a1 a2 a3 P1 P2 hProgLocal with
                                ⟨hA1Ne, hA2Ne, hA3Ne,
                                  px, pw, px', pn, hP1, hP2⟩
                              have hReqNe :
                                  __eo_requires
                                      (__eo_and
                                        (__eo_and
                                          (__eo_and (__eo_eq a3 pw)
                                            (__eo_eq a1 px))
                                          (__eo_eq a2 pn))
                                        (__eo_eq a1 px'))
                                      (Term.Boolean true)
                                      (bvUleMaxTerm a1 a2 a3) ≠
                                    Term.Stuck := by
                                have h := hProgLocal
                                rw [hP1, hP2] at h
                                unfold bvAllOnesWidthPrem bvUleMaxValuePrem at h
                                rw [__eo_prog_bv_ule_max.eq_4
                                  a1 a2 a3 pw px pn px'
                                  hA1Ne hA2Ne hA3Ne] at h
                                simpa [bvUleMaxTerm, bvAllOnesConst] using h
                              rcases bv_ule_max_bound_vars
                                  a1 a2 a3 px pw px' pn hReqNe with
                                ⟨hPw, hPx, hPn, hPx'⟩
                              subst pw
                              subst px
                              subst pn
                              subst px'
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
                              have hResultTyCanonical :
                                  __eo_typeof (bvUleMaxTerm a1 a2 a3) =
                                    Term.Bool := by
                                have h := hResultTy
                                change __eo_typeof
                                    (__eo_prog_bv_ule_max a1 a2 a3
                                      (Proof.pf (__eo_state_proven_nth s i1))
                                      (Proof.pf (__eo_state_proven_nth s i2))) =
                                    Term.Bool at h
                                simpa [P1, P2, hP1, hP2,
                                  prog_bv_ule_max_eq_of_ne_stuck
                                    a1 a2 a3 hA1Ne hA2Ne hA3Ne] using h
                              simpa [hP1, hP2,
                                  prog_bv_ule_max_eq_of_ne_stuck
                                    a1 a2 a3 hA1Ne hA2Ne hA3Ne] using
                                (show StepRuleProperties M
                                    [bvAllOnesWidthPrem a1 a3,
                                      bvUleMaxValuePrem a1 a2]
                                    (bvUleMaxTerm a1 a2 a3) from
                                  ⟨(by
                                      intro hPremisesTrue
                                      have hValuePrem :
                                          eo_interprets M
                                            (bvUleMaxValuePrem a1 a2) true :=
                                        hPremisesTrue.true_here _ (by simp)
                                      exact facts_bv_ule_max_term M hM
                                        a1 a2 a3 hA1Trans hA2Trans
                                        hA3Trans hValuePrem
                                        hResultTyCanonical),
                                    RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (typed_bv_ule_max_term a1 a2 a3
                                        hA1Trans hA2Trans hA3Trans
                                        hResultTyCanonical)⟩)
