module

public import Cpc.Proofs.RuleSupport.BvZeroExtendUltConstSupport
import all Cpc.Proofs.RuleSupport.BvZeroExtendUltConstSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_sign_extend_eq_const_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_eq_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_1 args premises ≠
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
      | cons m args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons c args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons nm args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons mp args =>
                      cases args with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons nm2 args =>
                          cases args with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons nmm1 args =>
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
                                                  let P1 := __eo_state_proven_nth s n1
                                                  let P2 := __eo_state_proven_nth s n2
                                                  let P3 := __eo_state_proven_nth s n3
                                                  change StepRuleProperties M [P1, P2, P3]
                                                    (bvSignExtendEqConst1Program
                                                      x m c nm mp nm2 nmm1 P1 P2 P3)
                                                  have hArgsTrans :
                                                      RuleProofs.eo_has_smt_translation x ∧
                                                        RuleProofs.eo_has_smt_translation m ∧
                                                        RuleProofs.eo_has_smt_translation c ∧
                                                        RuleProofs.eo_has_smt_translation nm ∧
                                                        RuleProofs.eo_has_smt_translation mp ∧
                                                        RuleProofs.eo_has_smt_translation nm2 ∧
                                                        RuleProofs.eo_has_smt_translation nmm1 ∧
                                                        True := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using hCmdTrans
                                                  have hXTrans := hArgsTrans.1
                                                  have hMTrans := hArgsTrans.2.1
                                                  have hCTrans := hArgsTrans.2.2.1
                                                  have hNmTrans := hArgsTrans.2.2.2.1
                                                  have hMpTrans := hArgsTrans.2.2.2.2.1
                                                  have hNm2Trans := hArgsTrans.2.2.2.2.2.1
                                                  have hNmm1Trans :=
                                                    hArgsTrans.2.2.2.2.2.2.1
                                                  have hProgramTy :
                                                      __eo_typeof
                                                          (bvSignExtendEqConst1Program
                                                            x m c nm mp nm2 nmm1
                                                            P1 P2 P3) =
                                                        Term.Bool := by
                                                    have hsimpa := hResultTy
                                                    try simp [P1, P2, P3] at hsimpa ⊢
                                                    exact hsimpa
                                                  refine ⟨?_, ?_⟩
                                                  · intro hPremisesTrue
                                                    have hP1True :
                                                        eo_interprets M P1 true :=
                                                      hPremisesTrue P1 (by simp)
                                                    have hP2True :
                                                        eo_interprets M P2 true :=
                                                      hPremisesTrue P2 (by simp)
                                                    have hP3True :
                                                        eo_interprets M P3 true :=
                                                      hPremisesTrue P3 (by simp)
                                                    exact
                                                      facts_bv_sign_extend_eq_const_1_program
                                                        M hM x m c nm mp nm2 nmm1
                                                        P1 P2 P3 hXTrans hMTrans
                                                        hCTrans hNmTrans hMpTrans
                                                        hNm2Trans hNmm1Trans
                                                        hProgramTy hP1True hP2True
                                                        hP3True
                                                  · exact
                                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                        _
                                                        (typed_bv_sign_extend_eq_const_1_program
                                                          x m c nm mp nm2 nmm1
                                                          P1 P2 P3 hXTrans hMTrans
                                                          hCTrans hNmTrans hMpTrans
                                                          hNm2Trans hNmm1Trans
                                                          hProgramTy)
