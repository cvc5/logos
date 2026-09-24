module

public import Cpc.Proofs.RuleSupport.StrReplaceFindSupport
import all Cpc.Proofs.RuleSupport.StrReplaceFindSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_replace_find_first_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_find_first_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_find_first_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_find_first_concat args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_replace_find_first_concat args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons a3 args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons a4 args =>
                  cases args with
                  | nil => exact absurd rfl hProg
                  | cons a5 args =>
                      cases args with
                      | nil => exact absurd rfl hProg
                      | cons a6 args =>
                          cases args with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
                              cases premises with
                              | nil => exact absurd rfl hProg
                              | cons p1 premises =>
                                  cases premises with
                                  | nil => exact absurd rfl hProg
                                  | cons p2 premises =>
                                      cases premises with
                                      | nil => exact absurd rfl hProg
                                      | cons p3 premises =>
                                          cases premises with
                                          | cons _ _ => exact absurd rfl hProg
                                          | nil =>
                                              let P1 := __eo_state_proven_nth s p1
                                              let P2 := __eo_state_proven_nth s p2
                                              let P3 := __eo_state_proven_nth s p3
                                              have hA1Trans :
                                                  RuleProofs.eo_has_smt_translation a1 := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using
                                                    hCmdTrans.1
                                              have hA2Trans :
                                                  RuleProofs.eo_has_smt_translation a2 := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using
                                                    hCmdTrans.2.1
                                              have hA3Trans :
                                                  RuleProofs.eo_has_smt_translation a3 := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using
                                                    hCmdTrans.2.2.1
                                              have hA4Trans :
                                                  RuleProofs.eo_has_smt_translation a4 := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using
                                                    hCmdTrans.2.2.2.1
                                              have hA5Trans :
                                                  RuleProofs.eo_has_smt_translation a5 := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using
                                                    hCmdTrans.2.2.2.2.1
                                              have hA6Trans :
                                                  RuleProofs.eo_has_smt_translation a6 := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk] using
                                                    hCmdTrans.2.2.2.2.2.1
                                              change __eo_typeof
                                                  (__eo_prog_str_replace_find_first_concat
                                                    a1 a2 a3 a4 a5 a6
                                                    (Proof.pf P1) (Proof.pf P2)
                                                    (Proof.pf P3)) =
                                                Term.Bool at hResultTy
                                              have hRuleProg :
                                                  __eo_prog_str_replace_find_first_concat
                                                      a1 a2 a3 a4 a5 a6
                                                      (Proof.pf P1) (Proof.pf P2)
                                                      (Proof.pf P3) ≠ Term.Stuck :=
                                                term_ne_stuck_of_typeof_bool
                                                  hResultTy
                                              rcases
                                                  StrReplaceFindSupport.prog_first_concat_info
                                                    a1 a2 a3 a4 a5 a6 P1 P2 P3
                                                    hRuleProg with
                                                ⟨hP1, hP2, hP3, hProgEq⟩
                                              rw [hProgEq] at hResultTy
                                              have hOps :=
                                                RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                                  (__eo_typeof
                                                    (StrReplaceFindSupport.firstConcatLeft
                                                      a1 a2 a3 a4))
                                                  (__eo_typeof
                                                    (StrReplaceFindSupport.firstConcatRight
                                                      a5 a4 a6 a2))
                                                  hResultTy
                                              have hLeftNN := hOps.1
                                              have hRightNN := hOps.2
                                              change __eo_typeof_str_replace
                                                  (__eo_typeof
                                                    (StrReplaceFindSupport.firstConcatSource
                                                      a1 a2))
                                                  (__eo_typeof a3)
                                                  (__eo_typeof a4) ≠
                                                Term.Stuck at hLeftNN
                                              rcases
                                                  StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                                                    (__eo_typeof
                                                      (StrReplaceFindSupport.firstConcatSource
                                                        a1 a2))
                                                    (__eo_typeof a3)
                                                    (__eo_typeof a4) hLeftNN with
                                                ⟨T, hSourceTy, hA3Ty, hA4Ty⟩
                                              have hSourceArgs :=
                                                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                                  a1 a2 T hSourceTy
                                              have hA1Ty := hSourceArgs.1
                                              have hA2Ty := hSourceArgs.2
                                              change __eo_typeof_str_concat
                                                  (__eo_typeof a5)
                                                  (__eo_typeof
                                                    (Term.Apply
                                                      (Term.Apply Term.str_concat a4)
                                                      (Term.Apply
                                                        (Term.Apply Term.str_concat a6)
                                                        a2))) ≠
                                                Term.Stuck at hRightNN
                                              rcases
                                                  StrSubstrContainsSupport.eo_typeof_str_concat_args_of_ne_stuck
                                                    (__eo_typeof a5)
                                                    (__eo_typeof
                                                      (Term.Apply
                                                        (Term.Apply Term.str_concat a4)
                                                        (Term.Apply
                                                          (Term.Apply Term.str_concat a6)
                                                          a2))) hRightNN with
                                                ⟨U, hA5TyU, hInnerTyU⟩
                                              have hInnerArgs :=
                                                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                                  a4
                                                  (Term.Apply
                                                    (Term.Apply Term.str_concat a6) a2)
                                                  U hInnerTyU
                                              have hPostTailArgs :=
                                                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                                  a6 a2 U hInnerArgs.2
                                              have hUT : U = T := by
                                                have hSeq :
                                                    Term.Apply Term.Seq U =
                                                      Term.Apply Term.Seq T := by
                                                  rw [← hInnerArgs.1, hA4Ty]
                                                injection hSeq
                                              subst U
                                              have hA5Ty := hA5TyU
                                              have hA6Ty := hPostTailArgs.1
                                              refine ⟨?_, ?_⟩
                                              · intro hTrue
                                                have hPrem1Raw :
                                                    eo_interprets M P1 true :=
                                                  hTrue P1 (by
                                                    simp [P1, premiseTermList])
                                                have hPrem2Raw :
                                                    eo_interprets M P2 true :=
                                                  hTrue P2 (by
                                                    simp [P2, premiseTermList])
                                                have hPrem3Raw :
                                                    eo_interprets M P3 true :=
                                                  hTrue P3 (by
                                                    simp [P3, premiseTermList])
                                                have hPrem1 : eo_interprets M
                                                    (StrReplaceFindSupport.foundPremise
                                                      a1 a3) true := by
                                                  simpa [hP1] using hPrem1Raw
                                                have hPrem2 : eo_interprets M
                                                    (StrReplaceFindSupport.prePremise
                                                      a1 a3 a5) true := by
                                                  simpa [hP2] using hPrem2Raw
                                                have hPrem3 : eo_interprets M
                                                    (StrReplaceFindSupport.postPremise
                                                      a1 a3 a6) true := by
                                                  simpa [hP3] using hPrem3Raw
                                                exact
                                                  StrReplaceFindSupport.facts_first_concat
                                                    M hM a1 a2 a3 a4 a5 a6
                                                    P1 P2 P3 T hA1Trans hA2Trans
                                                    hA3Trans hA4Trans hA5Trans
                                                    hA6Trans hA1Ty hA2Ty hA3Ty
                                                    hA4Ty hA5Ty hA6Ty hPrem1
                                                    hPrem2 hPrem3 hProgEq
                                              · exact
                                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                    _
                                                    (StrReplaceFindSupport.typed_first_concat
                                                      a1 a2 a3 a4 a5 a6
                                                      P1 P2 P3 T hA1Trans hA2Trans
                                                      hA3Trans hA4Trans hA5Trans
                                                      hA6Trans hA1Ty hA2Ty hA3Ty
                                                      hA4Ty hA5Ty hA6Ty hProgEq)
