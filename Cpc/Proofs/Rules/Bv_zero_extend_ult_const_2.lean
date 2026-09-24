module

public import Cpc.Proofs.RuleSupport.BvZeroExtendUltConstSupport
import all Cpc.Proofs.RuleSupport.BvZeroExtendUltConstSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_zero_extend_ult_const_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_ult_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_2 args premises ≠
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
                  | cons nm2 args =>
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
                                        (bvZeroExtendUltConst2Program
                                          x m c nm nm2 P1 P2)
                                      have hArgsTrans :
                                          RuleProofs.eo_has_smt_translation x ∧
                                            RuleProofs.eo_has_smt_translation m ∧
                                            RuleProofs.eo_has_smt_translation c ∧
                                            RuleProofs.eo_has_smt_translation nm ∧
                                            RuleProofs.eo_has_smt_translation nm2 ∧
                                            True := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using hCmdTrans
                                      have hXTrans := hArgsTrans.1
                                      have hMTrans := hArgsTrans.2.1
                                      have hCTrans := hArgsTrans.2.2.1
                                      have hNmTrans := hArgsTrans.2.2.2.1
                                      have hNm2Trans := hArgsTrans.2.2.2.2.1
                                      have hProgramTy :
                                          __eo_typeof
                                              (bvZeroExtendUltConst2Program
                                                x m c nm nm2 P1 P2) =
                                            Term.Bool := by
                                        have hsimpa := hResultTy
                                        try simp [P1, P2] at hsimpa ⊢
                                        exact hsimpa
                                      refine ⟨?_, ?_⟩
                                      · intro hPremisesTrue
                                        have hP1True : eo_interprets M P1 true :=
                                          hPremisesTrue P1 (by simp)
                                        have hP2True : eo_interprets M P2 true :=
                                          hPremisesTrue P2 (by simp)
                                        exact facts_bv_zero_extend_ult_const_2_program
                                          M hM x m c nm nm2 P1 P2
                                          hXTrans hMTrans hCTrans hNmTrans
                                          hNm2Trans hProgramTy hP1True hP2True
                                      · exact
                                          RuleProofs.eo_has_smt_translation_of_has_bool_type
                                            _
                                            (typed_bv_zero_extend_ult_const_2_program
                                              x m c nm nm2 P1 P2 hXTrans
                                              hMTrans hCTrans hNmTrans
                                              hNm2Trans hProgramTy)
