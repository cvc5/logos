module

public import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import all Cpc.Proofs.RuleSupport.BvCommutativeXorSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_xor_duplicate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_duplicate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_xor_duplicate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_duplicate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_xor_duplicate args premises ≠ Term.Stuck :=
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
                        (__eo_prog_bv_xor_duplicate a1 a2 (Proof.pf P1))
                      have hProgLocal :
                          __eo_prog_bv_xor_duplicate a1 a2 (Proof.pf P1) ≠
                            Term.Stuck := by
                        exact hProg
                      rcases bv_xor_duplicate_shape_of_ne_stuck a1 a2 P1 hProgLocal with
                        ⟨ha1, ha2, pw, px, hP1⟩
                      subst P1
                      have hReqNe := by
                        have h := hProgLocal
                        rw [hP1] at h
                        rw [__eo_prog_bv_xor_duplicate.eq_3 a1 a2 pw px ha1 ha2] at h
                        exact h
                      rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck a2 a1 pw px
                          _ hReqNe with
                        ⟨hpw, hpx⟩
                      subst pw
                      subst px
                      have hATransPair :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                      have hResultTyCanonical :
                          __eo_typeof (bvXorDuplicateProgram a1 a2) = Term.Bool := by
                        have h := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_xor_duplicate a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))) =
                          Term.Bool at h
                        simpa [hP1, bvXorDuplicateProgram] using h
                      simpa [hP1, bvXorDuplicateProgram] using
                        (show StepRuleProperties M
                            [Term.Apply (Term.Apply (Term.UOp UserOp.eq) a2)
                              (Term.Apply (Term.UOp UserOp._at_bvsize) a1)]
                            (bvXorDuplicateProgram a1 a2) from
                          ⟨(by
                              intro _hPrem
                              exact facts_bv_xor_duplicate_program M hM a1 a2
                                hA1Trans hA2Trans hResultTyCanonical),
                            RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed_bv_xor_duplicate_program a1 a2
                                hA1Trans hA2Trans hResultTyCanonical)⟩)
