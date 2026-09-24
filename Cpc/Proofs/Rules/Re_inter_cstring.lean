
module

public import Cpc.Proofs.RuleSupport.ReInterCstringSupport
import all Cpc.Proofs.RuleSupport.ReInterCstringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

public theorem cmd_step_re_inter_cstring_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_cstring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_inter_cstring args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_cstring args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_inter_cstring args premises ≠
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
                  | cons n premises =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.2.1
                          show StepRuleProperties M [__eo_state_proven_nth s n]
                            (__eo_prog_re_inter_cstring a1 a2 a3
                              (Proof.pf (__eo_state_proven_nth s n)))
                          generalize hP : __eo_state_proven_nth s n = P
                          have hProgNe :
                              __eo_prog_re_inter_cstring a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck := by
                            rw [← hP]
                            change __eo_cmd_step_proven s CRule.re_inter_cstring
                                (CArgList.cons a1
                                  (CArgList.cons a2
                                    (CArgList.cons a3 CArgList.nil)))
                                (CIndexList.cons n CIndexList.nil) ≠ Term.Stuck
                            exact hProg
                          obtain ⟨hPShape, hProgEq⟩ :=
                            ReInterCstringProof.prog_form a1 a2 a3 P hProgNe
                          have hResultTyProg :
                              __eo_typeof
                                  (__eo_prog_re_inter_cstring a1 a2 a3
                                    (Proof.pf P)) = Term.Bool := by
                            rw [← hP]
                            change __eo_typeof
                                (__eo_cmd_step_proven s CRule.re_inter_cstring
                                  (CArgList.cons a1
                                    (CArgList.cons a2
                                      (CArgList.cons a3 CArgList.nil)))
                                  (CIndexList.cons n CIndexList.nil)) =
                              Term.Bool
                            exact hResultTy
                          have hConclTy :
                              __eo_typeof (ReInterCstringProof.concl a1 a2 a3) =
                                Term.Bool := by
                            rw [hProgEq] at hResultTyProg
                            exact hResultTyProg
                          change __eo_typeof_eq
                              (__eo_typeof (ReInterCstringProof.lhs a1 a2 a3))
                              (__eo_typeof (ReInterCstringProof.rhs a3)) =
                            Term.Bool at hConclTy
                          have hLhsNotStuck :
                              __eo_typeof (ReInterCstringProof.lhs a1 a2 a3) ≠
                                Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof (ReInterCstringProof.lhs a1 a2 a3))
                              (__eo_typeof (ReInterCstringProof.rhs a3))
                              hConclTy).1
                          have hOuterArgs :
                              __eo_typeof
                                  (Term.Apply (Term.UOp UserOp.str_to_re) a3) =
                                  Term.UOp UserOp.RegLan ∧
                                __eo_typeof (ReInterCstringProof.reInter a1 a2) =
                                  Term.UOp UserOp.RegLan := by
                            change __eo_typeof_re_concat
                                (__eo_typeof
                                  (Term.Apply (Term.UOp UserOp.str_to_re) a3))
                                (__eo_typeof (ReInterCstringProof.reInter a1 a2)) ≠
                              Term.Stuck at hLhsNotStuck
                            exact
                              ReInterCstringProof.eo_typeof_re_concat_ne_stuck_args_reglan
                                _ _ hLhsNotStuck
                          have hInnerArgs :
                              __eo_typeof a1 = Term.UOp UserOp.RegLan ∧
                                __eo_typeof a2 = Term.UOp UserOp.RegLan := by
                            have hInnerTy := hOuterArgs.2
                            change __eo_typeof_re_concat (__eo_typeof a1)
                                (__eo_typeof a2) =
                              Term.UOp UserOp.RegLan at hInnerTy
                            exact
                              ReInterCstringProof.eo_typeof_re_concat_eq_reglan_args_reglan
                                _ _ hInnerTy
                          have hA1Ty : __eo_typeof a1 = Term.UOp UserOp.RegLan :=
                            hInnerArgs.1
                          have hA2Ty : __eo_typeof a2 = Term.UOp UserOp.RegLan :=
                            hInnerArgs.2
                          have hA3Ty :
                              __eo_typeof a3 = Term.Apply Term.Seq Term.Char := by
                            have hStrToReTy := hOuterArgs.1
                            change __eo_typeof_str_to_re (__eo_typeof a3) =
                              Term.UOp UserOp.RegLan at hStrToReTy
                            exact
                              ReInterCstringProof.eo_typeof_str_to_re_eq_seq_char_of_reglan
                                (__eo_typeof a3) hStrToReTy
                          have hA1SmtTy :
                              __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a1) =
                                  __eo_to_smt_type (__eo_typeof a1) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a1 hA1Trans
                            rw [hA1Ty] at hTyRaw
                            simpa [TranslationProofs.eo_to_smt_type_reglan] using
                              hTyRaw
                          have hA2SmtTy :
                              __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a2) =
                                  __eo_to_smt_type (__eo_typeof a2) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a2 hA2Trans
                            rw [hA2Ty] at hTyRaw
                            simpa [TranslationProofs.eo_to_smt_type_reglan] using
                              hTyRaw
                          have hA3SmtTy :
                              __smtx_typeof (__eo_to_smt a3) =
                                SmtType.Seq SmtType.Char := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a3) =
                                  __eo_to_smt_type (__eo_typeof a3) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a3 hA3Trans
                            rw [hA3Ty] at hTyRaw
                            have hsimpa := hTyRaw
                            try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
                            exact hsimpa
                          have hProgBool :
                              RuleProofs.eo_has_bool_type
                                (__eo_prog_re_inter_cstring a1 a2 a3
                                  (Proof.pf P)) := by
                            rw [hProgEq]
                            exact ReInterCstringProof.typed_concl a1 a2 a3
                              hA1SmtTy hA2SmtTy hA3SmtTy
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            hProgBool⟩
                          intro hEv
                          have hPrem :
                              eo_interprets M
                                (ReInterCstringProof.prem a3 a1 a2) true := by
                            have hHere := hEv.true_here P (by simp)
                            simpa [hPShape] using hHere
                          rw [hProgEq]
                          exact ReInterCstringProof.facts M hM a1 a2 a3
                            hA1SmtTy hA2SmtTy hA3SmtTy hPrem
