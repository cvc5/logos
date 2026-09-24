module

public import Cpc.Proofs.RuleSupport.BvEqExtractElimSupport
import all Cpc.Proofs.RuleSupport.BvEqExtractElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_eq_extract_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_extract_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_eq_extract_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_extract_elim1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_eq_extract_elim1 args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons y args =>
          cases args with
          | nil => exact False.elim (hProg rfl)
          | cons i args =>
              cases args with
              | nil => exact False.elim (hProg rfl)
              | cons j args =>
                  cases args with
                  | nil => exact False.elim (hProg rfl)
                  | cons wm args =>
                      cases args with
                      | nil => exact False.elim (hProg rfl)
                      | cons jp args =>
                          cases args with
                          | nil => exact False.elim (hProg rfl)
                          | cons im args =>
                              cases args with
                              | cons _ _ => exact False.elim (hProg rfl)
                              | nil =>
                                  cases premises with
                                  | nil => exact False.elim (hProg rfl)
                                  | cons n1 premises =>
                                      cases premises with
                                      | nil => exact False.elim (hProg rfl)
                                      | cons n2 premises =>
                                          cases premises with
                                          | nil =>
                                              exact False.elim (hProg rfl)
                                          | cons n3 premises =>
                                              cases premises with
                                              | nil =>
                                                  exact False.elim (hProg rfl)
                                              | cons n4 premises =>
                                                  cases premises with
                                                  | nil =>
                                                      exact False.elim
                                                        (hProg rfl)
                                                  | cons n5 premises =>
                                                      cases premises with
                                                      | cons _ _ =>
                                                          exact False.elim
                                                            (hProg rfl)
                                                      | nil =>
                                                          let P1 :=
                                                            __eo_state_proven_nth
                                                              s n1
                                                          let P2 :=
                                                            __eo_state_proven_nth
                                                              s n2
                                                          let P3 :=
                                                            __eo_state_proven_nth
                                                              s n3
                                                          let P4 :=
                                                            __eo_state_proven_nth
                                                              s n4
                                                          let P5 :=
                                                            __eo_state_proven_nth
                                                              s n5
                                                          change
                                                            StepRuleProperties M
                                                              [P1, P2, P3,
                                                                P4, P5]
                                                              (bvEqExtractElim1Program
                                                                x y i j wm jp im
                                                                P1 P2 P3 P4 P5)
                                                          have hArgsTrans :
                                                              RuleProofs.eo_has_smt_translation x ∧
                                                                RuleProofs.eo_has_smt_translation y ∧
                                                                RuleProofs.eo_has_smt_translation i ∧
                                                                RuleProofs.eo_has_smt_translation j ∧
                                                                RuleProofs.eo_has_smt_translation wm ∧
                                                                RuleProofs.eo_has_smt_translation jp ∧
                                                                RuleProofs.eo_has_smt_translation im ∧
                                                                True := by
                                                            simpa [cmdTranslationOk,
                                                              cArgListTranslationOk]
                                                              using hCmdTrans
                                                          have hProgramTy :
                                                              __eo_typeof
                                                                  (bvEqExtractElim1Program
                                                                    x y i j wm jp im
                                                                    P1 P2 P3 P4 P5) =
                                                                Term.Bool := by
                                                            have hsimpa :=
                                                              hResultTy
                                                            try simp [P1, P2, P3, P4, P5] at hsimpa ⊢
                                                            exact hsimpa
                                                          refine ⟨?_, ?_⟩
                                                          · intro hPremisesTrue
                                                            exact
                                                              facts_bv_eq_extract_elim1_program
                                                                M hM x y i j wm jp im
                                                                P1 P2 P3 P4 P5
                                                                hArgsTrans.1
                                                                hArgsTrans.2.1
                                                                hArgsTrans.2.2.1
                                                                hArgsTrans.2.2.2.1
                                                                hArgsTrans.2.2.2.2.1
                                                                hArgsTrans.2.2.2.2.2.1
                                                                hArgsTrans.2.2.2.2.2.2.1
                                                                hProgramTy
                                                                (hPremisesTrue P1
                                                                  (by simp))
                                                                (hPremisesTrue P2
                                                                  (by simp))
                                                                (hPremisesTrue P3
                                                                  (by simp))
                                                                (hPremisesTrue P4
                                                                  (by simp))
                                                                (hPremisesTrue P5
                                                                  (by simp))
                                                          · exact
                                                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                                                (typed_bv_eq_extract_elim1_program
                                                                  x y i j wm jp im
                                                                  P1 P2 P3 P4 P5
                                                                  hArgsTrans.1
                                                                  hArgsTrans.2.1
                                                                  hArgsTrans.2.2.1
                                                                  hArgsTrans.2.2.2.1
                                                                  hArgsTrans.2.2.2.2.1
                                                                  hArgsTrans.2.2.2.2.2.1
                                                                  hArgsTrans.2.2.2.2.2.2.1
                                                                  hProgramTy)
