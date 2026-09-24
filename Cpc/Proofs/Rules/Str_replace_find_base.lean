module

public import Cpc.Proofs.RuleSupport.StrReplaceFindSupport
import all Cpc.Proofs.RuleSupport.StrReplaceFindSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_replace_find_base_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_find_base args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_find_base args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_find_base args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_replace_find_base args premises ≠
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
                                          change __eo_typeof
                                              (__eo_prog_str_replace_find_base
                                                a1 a2 a3 a4 a5
                                                (Proof.pf P1) (Proof.pf P2)
                                                (Proof.pf P3)) =
                                            Term.Bool at hResultTy
                                          have hRuleProg :
                                              __eo_prog_str_replace_find_base
                                                  a1 a2 a3 a4 a5
                                                  (Proof.pf P1) (Proof.pf P2)
                                                  (Proof.pf P3) ≠ Term.Stuck :=
                                            term_ne_stuck_of_typeof_bool
                                              hResultTy
                                          rcases
                                              StrReplaceFindSupport.prog_base_info
                                                a1 a2 a3 a4 a5 P1 P2 P3
                                                hRuleProg with
                                            ⟨hP1, hP2, hP3, hProgGen⟩
                                          have hGeneratedTy :
                                              __eo_typeof
                                                  (StrReplaceFindSupport.baseGeneratedConclusion
                                                    a1 a2 a3 a4 a5) =
                                                Term.Bool := by
                                            simpa [hProgGen] using hResultTy
                                          have hLeftNN :=
                                            StrReplaceFindSupport.base_lhs_type_ne_stuck_of_generated_type_bool
                                              a1 a2 a3 a4 a5 hGeneratedTy
                                          change __eo_typeof_str_replace
                                              (__eo_typeof a1) (__eo_typeof a2)
                                              (__eo_typeof a3) ≠
                                            Term.Stuck at hLeftNN
                                          rcases
                                              StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                                                (__eo_typeof a1) (__eo_typeof a2)
                                                (__eo_typeof a3) hLeftNN with
                                            ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                                          have hP2BoolRaw :
                                              RuleProofs.eo_has_bool_type P2 :=
                                            hPremisesBool P2 (by
                                              simp [P2, premiseTermList])
                                          have hP2Bool : RuleProofs.eo_has_bool_type
                                              (StrReplaceFindSupport.prePremise
                                                a1 a2 a4) := by
                                            simpa [hP2] using hP2BoolRaw
                                          have hP2EoBool :=
                                            StrReplaceFindSupport.eo_typeof_eq_bool_of_has_bool_type
                                              a4
                                              (Term.Apply
                                                (Term.Apply
                                                  (Term.Apply Term.str_substr a1)
                                                  (Term.Numeral 0))
                                                (StrReplaceFindSupport.indexTerm
                                                  a1 a2)) hP2Bool
                                          have hP2Ops :=
                                            RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                              (__eo_typeof a4)
                                              (__eo_typeof
                                                (Term.Apply
                                                  (Term.Apply
                                                    (Term.Apply Term.str_substr a1)
                                                    (Term.Numeral 0))
                                                  (StrReplaceFindSupport.indexTerm
                                                    a1 a2))) hP2EoBool
                                          have hPreTypeEq :=
                                            StrReplaceFindSupport.eo_typeof_eq_operands_of_has_bool_type
                                              a4
                                              (Term.Apply
                                                (Term.Apply
                                                  (Term.Apply Term.str_substr a1)
                                                  (Term.Numeral 0))
                                                (StrReplaceFindSupport.indexTerm
                                                  a1 a2)) hP2Bool
                                          have hSubPreNN := hP2Ops.2
                                          change __eo_typeof_str_substr
                                              (__eo_typeof a1)
                                              (__eo_typeof (Term.Numeral 0))
                                              (__eo_typeof
                                                (StrReplaceFindSupport.indexTerm
                                                  a1 a2)) ≠
                                            Term.Stuck at hSubPreNN
                                          rcases
                                              StrSubstrContainsSupport.eo_typeof_str_substr_args_of_ne_stuck
                                                (__eo_typeof a1)
                                                (__eo_typeof (Term.Numeral 0))
                                                (__eo_typeof
                                                  (StrReplaceFindSupport.indexTerm
                                                    a1 a2)) hSubPreNN with
                                            ⟨U, hA1TyU, hZeroTy, hIndexTy⟩
                                          have hUT : U = T := by
                                            have hSeq :
                                                Term.Apply Term.Seq U =
                                                  Term.Apply Term.Seq T := by
                                              rw [← hA1TyU, hA1Ty]
                                            injection hSeq
                                          subst U
                                          have hSubPreRaw :=
                                            StrSubstrContainsSupport.eo_typeof_str_substr_result_of_seq_args
                                              T (by
                                                simpa [hA1Ty, hZeroTy, hIndexTy]
                                                  using hSubPreNN)
                                          have hSubPreTy :
                                              __eo_typeof
                                                  (Term.Apply
                                                    (Term.Apply
                                                      (Term.Apply Term.str_substr a1)
                                                      (Term.Numeral 0))
                                                    (StrReplaceFindSupport.indexTerm
                                                      a1 a2)) =
                                                Term.Apply Term.Seq T := by
                                            change __eo_typeof_str_substr
                                                (__eo_typeof a1)
                                                (__eo_typeof (Term.Numeral 0))
                                                (__eo_typeof
                                                  (StrReplaceFindSupport.indexTerm
                                                    a1 a2)) = _
                                            rw [hA1Ty, hZeroTy, hIndexTy]
                                            exact hSubPreRaw
                                          have hA4Ty :
                                              __eo_typeof a4 =
                                                Term.Apply Term.Seq T := by
                                            rw [hPreTypeEq, hSubPreTy]
                                          have hP3BoolRaw :
                                              RuleProofs.eo_has_bool_type P3 :=
                                            hPremisesBool P3 (by
                                              simp [P3, premiseTermList])
                                          have hP3Bool : RuleProofs.eo_has_bool_type
                                              (StrReplaceFindSupport.postPremise
                                                a1 a2 a5) := by
                                            simpa [hP3] using hP3BoolRaw
                                          let postSub := Term.Apply
                                            (Term.Apply
                                              (Term.Apply Term.str_substr a1)
                                              (StrReplaceFindSupport.afterStart
                                                a1 a2))
                                            (Term.Apply Term.str_len a1)
                                          have hP3EoBool :=
                                            StrReplaceFindSupport.eo_typeof_eq_bool_of_has_bool_type
                                              a5 postSub hP3Bool
                                          have hP3Ops :=
                                            RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                              (__eo_typeof a5)
                                              (__eo_typeof postSub) hP3EoBool
                                          have hPostTypeEq :=
                                            StrReplaceFindSupport.eo_typeof_eq_operands_of_has_bool_type
                                              a5 postSub hP3Bool
                                          have hSubPostNN := hP3Ops.2
                                          change __eo_typeof_str_substr
                                              (__eo_typeof a1)
                                              (__eo_typeof
                                                (StrReplaceFindSupport.afterStart
                                                  a1 a2))
                                              (__eo_typeof
                                                (Term.Apply Term.str_len a1)) ≠
                                            Term.Stuck at hSubPostNN
                                          rcases
                                              StrSubstrContainsSupport.eo_typeof_str_substr_args_of_ne_stuck
                                                (__eo_typeof a1)
                                                (__eo_typeof
                                                  (StrReplaceFindSupport.afterStart
                                                    a1 a2))
                                                (__eo_typeof
                                                  (Term.Apply Term.str_len a1))
                                                hSubPostNN with
                                            ⟨V, hA1TyV, hStartTy, hLenTy⟩
                                          have hVT : V = T := by
                                            have hSeq :
                                                Term.Apply Term.Seq V =
                                                  Term.Apply Term.Seq T := by
                                              rw [← hA1TyV, hA1Ty]
                                            injection hSeq
                                          subst V
                                          have hSubPostRaw :=
                                            StrSubstrContainsSupport.eo_typeof_str_substr_result_of_seq_args
                                              T (by
                                                simpa [hA1Ty, hStartTy, hLenTy]
                                                  using hSubPostNN)
                                          have hSubPostTy :
                                              __eo_typeof postSub =
                                                Term.Apply Term.Seq T := by
                                            change __eo_typeof_str_substr
                                                (__eo_typeof a1)
                                                (__eo_typeof
                                                  (StrReplaceFindSupport.afterStart
                                                    a1 a2))
                                                (__eo_typeof
                                                  (Term.Apply Term.str_len a1)) = _
                                            rw [hA1Ty, hStartTy, hLenTy]
                                            exact hSubPostRaw
                                          have hA5Ty :
                                              __eo_typeof a5 =
                                                Term.Apply Term.Seq T := by
                                            rw [hPostTypeEq, hSubPostTy]
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
                                                  a1 a2) true := by
                                              simpa [hP1] using hPrem1Raw
                                            have hPrem2 : eo_interprets M
                                                (StrReplaceFindSupport.prePremise
                                                  a1 a2 a4) true := by
                                              simpa [hP2] using hPrem2Raw
                                            have hPrem3 : eo_interprets M
                                                (StrReplaceFindSupport.postPremise
                                                  a1 a2 a5) true := by
                                              simpa [hP3] using hPrem3Raw
                                            exact
                                              StrReplaceFindSupport.facts_base
                                                M hM a1 a2 a3 a4 a5 P1 P2 P3 T
                                                hA1Trans hA2Trans hA3Trans
                                                hA4Trans hA5Trans hA1Ty hA2Ty
                                                hA3Ty hA4Ty hA5Ty hPrem1 hPrem2
                                                hPrem3 hProgGen
                                          · exact
                                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                _
                                                (StrReplaceFindSupport.typed_base
                                                  a1 a2 a3 a4 a5 P1 P2 P3 T
                                                  hA1Trans hA2Trans hA3Trans
                                                  hA4Trans hA5Trans hA1Ty hA2Ty
                                                  hA3Ty hA4Ty hA5Ty hProgGen)
