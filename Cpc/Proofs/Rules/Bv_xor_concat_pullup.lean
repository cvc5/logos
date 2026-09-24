module

public import Cpc.Proofs.RuleSupport.BvConcatPullupSupport
import all Cpc.Proofs.RuleSupport.BvConcatPullupSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_bv_xor_concat_pullup_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_concat_pullup args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_xor_concat_pullup args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_concat_pullup args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_xor_concat_pullup args premises ≠
        Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons xs args =>
    cases args with
    | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
    | cons ws args =>
      cases args with
      | nil =>
        change Term.Stuck ≠ Term.Stuck at hProg
        exact False.elim (hProg rfl)
      | cons y args =>
        cases args with
        | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
        | cons z args =>
          cases args with
          | nil =>
            change Term.Stuck ≠ Term.Stuck at hProg
            exact False.elim (hProg rfl)
          | cons ys args =>
            cases args with
            | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
            | cons nxm args =>
              cases args with
              | nil =>
                change Term.Stuck ≠ Term.Stuck at hProg
                exact False.elim (hProg rfl)
              | cons ny args =>
                cases args with
                | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
                | cons nym args =>
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
                              (__eo_prog_bv_xor_concat_pullup xs ws y z ys
                                nxm ny nym (Proof.pf P1) (Proof.pf P2)
                                (Proof.pf P3))
                            have hArgsTrans :
                                RuleProofs.eo_has_smt_translation xs ∧
                                RuleProofs.eo_has_smt_translation ws ∧
                                RuleProofs.eo_has_smt_translation y ∧
                                RuleProofs.eo_has_smt_translation z ∧
                                RuleProofs.eo_has_smt_translation ys ∧
                                RuleProofs.eo_has_smt_translation nxm ∧
                                RuleProofs.eo_has_smt_translation ny ∧
                                RuleProofs.eo_has_smt_translation nym ∧
                                True := by
                              simpa [cmdTranslationOk,
                                cArgListTranslationOk] using hCmdTrans
                            have hP1Bool := hPremisesBool P1 (by
                              simp [premiseTermList, P1])
                            have hP2Bool := hPremisesBool P2 (by
                              simp [premiseTermList, P2])
                            have hP3Bool := hPremisesBool P3 (by
                              simp [premiseTermList, P3])
                            have hResultTyLocal : __eo_typeof
                                (bvConcatPullup1Program .bxor xs ws y z ys
                                  nxm ny nym P1 P2 P3) = Term.Bool := by
                              have hsimpa := hResultTy
                              try simp [bvConcatPullup1Program, P1, P2, P3] at hsimpa ⊢
                              exact hsimpa
                            simpa [bvConcatPullup1Program, P1, P2, P3] using
                              (bvConcatPullup1ProgramProperties M hM .bxor
                                xs ws y z ys nxm ny nym P1 P2 P3
                                hArgsTrans.1 hArgsTrans.2.1
                                hArgsTrans.2.2.1 hArgsTrans.2.2.2.1
                                hArgsTrans.2.2.2.2.1
                                hArgsTrans.2.2.2.2.2.1
                                hArgsTrans.2.2.2.2.2.2.1
                                hArgsTrans.2.2.2.2.2.2.2.1
                                hP1Bool hP2Bool hP3Bool hResultTyLocal)
