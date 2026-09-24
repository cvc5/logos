module

public import Cpc.Proofs.RuleSupport.BvRotateElimSupport
import all Cpc.Proofs.RuleSupport.BvRotateElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_rotate_right_eliminate_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_rotate_right_eliminate_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_2 args premises ≠
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let P := __eo_state_proven_nth s n
                      change StepRuleProperties M [P]
                        (__eo_prog_bv_rotate_right_eliminate_2 x amount
                          (Proof.pf P))
                      have hProgLocal :
                          __eo_prog_bv_rotate_right_eliminate_2 x amount
                              (Proof.pf P) ≠
                            Term.Stuck := by
                        exact hProg
                      rcases bv_rotate_right_elim_shape_of_ne_stuck
                          x amount P hProgLocal with
                        ⟨hXNe, hAmountNe, pa, px, hPShape⟩
                      have hReqNe := hProgLocal
                      rw [hPShape] at hReqNe
                      unfold bvRotateElimPrem at hReqNe
                      rw [__eo_prog_bv_rotate_right_eliminate_2.eq_3
                        x amount pa px hXNe hAmountNe] at hReqNe
                      rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                          amount x pa px _ hReqNe with
                        ⟨hPa, hPx⟩
                      subst pa
                      subst px
                      have hArgsTrans :
                          RuleProofs.eo_has_smt_translation x ∧
                            RuleProofs.eo_has_smt_translation amount ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans
                      have hXTrans : RuleProofs.eo_has_smt_translation x :=
                        hArgsTrans.1
                      have hProgramEq :=
                        bv_rotate_right_elim_program_eq_term_of_ne_stuck
                          x amount hXNe hAmountNe
                      have hTermTy :
                          __eo_typeof
                              (bvRotateElimTerm .right x amount) =
                            Term.Bool := by
                        have h := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_rotate_right_eliminate_2 x amount
                              (Proof.pf P)) = Term.Bool at h
                        rw [hPShape, hProgramEq] at h
                        exact h
                      rw [hPShape, hProgramEq]
                      refine ⟨?_, ?_⟩
                      · intro hPremTrue
                        have hPrem :
                            eo_interprets M (bvRotateElimPrem x amount) true :=
                          hPremTrue _ (by simp)
                        exact facts_bv_rotate_elim_term M hM .right x amount
                          hXTrans hTermTy hPrem
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_bv_rotate_elim_term .right x amount
                            hXTrans hTermTy)
