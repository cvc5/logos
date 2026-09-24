module

public import Cpc.Proofs.RuleSupport.StrConcatClashSupport
import all Cpc.Proofs.RuleSupport.StrConcatClashSupport

open Eo
open SmtEval
open Smtm
open StrConcatClashSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_str_concat_clash_info
    (x xs y ys P1 P2 : Term)
    (hProg : __eo_prog_str_concat_clash x xs y ys (Proof.pf P1)
      (Proof.pf P2) ≠ Term.Stuck) :
    P1 = concatClashNePremise x y ∧
      P2 = concatClashLenPremise x y ∧
      __eo_prog_str_concat_clash x xs y ys (Proof.pf P1) (Proof.pf P2) =
        concatClashConclusion x xs y ys := by
  unfold __eo_prog_str_concat_clash at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    have hCond := concat_clash_requires_guard_eq _ _ _ hProg
    rcases concat_clash_eo_and_true_split _ _ hCond with ⟨h123, h4⟩
    rcases concat_clash_eo_and_true_split _ _ h123 with ⟨h12, h3⟩
    rcases concat_clash_eo_and_true_split _ _ h12 with ⟨h1, h2⟩
    have e1 := RuleProofs.eq_of_eo_eq_true _ _ h1
    have e2 := RuleProofs.eq_of_eo_eq_true _ _ h2
    have e3 := RuleProofs.eq_of_eo_eq_true _ _ h3
    have e4 := RuleProofs.eq_of_eo_eq_true _ _ h4
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp [__eo_prog_str_concat_clash, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not,
      concatClashConclusion, mkEq, mkConcat]

public theorem cmd_step_str_concat_clash_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_clash args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_clash args premises ≠
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
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | nil => exact absurd rfl hProg
                      | cons n1 premises =>
                          cases premises with
                          | nil => exact absurd rfl hProg
                          | cons n2 premises =>
                              cases premises with
                              | cons _ _ => exact absurd rfl hProg
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  let P2 := __eo_state_proven_nth s n2
                                  have hA1Trans :
                                      RuleProofs.eo_has_smt_translation a1 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.1
                                  have hA2Trans :
                                      RuleProofs.eo_has_smt_translation a2 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.2.1
                                  have hA3Trans :
                                      RuleProofs.eo_has_smt_translation a3 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.2.2.1
                                  have hA4Trans :
                                      RuleProofs.eo_has_smt_translation a4 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.2.2.2.1
                                  change __eo_typeof
                                      (__eo_prog_str_concat_clash a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2)) =
                                    Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_concat_clash a1 a2 a3 a4
                                          (Proof.pf P1) (Proof.pf P2) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_concat_clash_info
                                      a1 a2 a3 a4 P1 P2 hRuleProg with
                                    ⟨hP1, hP2, hProgEq⟩
                                  have hConclusionTy :
                                      __eo_typeof
                                          (concatClashConclusion a1 a2 a3 a4) =
                                        Term.Bool := by
                                    simpa [hProgEq] using hResultTy
                                  rcases concat_clash_smt_seq_types_of_eo_type
                                      a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans
                                      hA4Trans hConclusionTy with
                                    ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                                  have hBool := eo_has_bool_type_concat_clash
                                    a1 a2 a3 a4 T hA1Ty hA2Ty hA3Ty hA4Ty
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem1Raw : eo_interprets M P1 true :=
                                      hTrue P1 (by
                                        simp [P1, premiseTermList])
                                    have hPrem2Raw : eo_interprets M P2 true :=
                                      hTrue P2 (by
                                        simp [P2, premiseTermList])
                                    have hPrem1 : eo_interprets M
                                        (concatClashNePremise a1 a3) true := by
                                      simpa [hP1] using hPrem1Raw
                                    have hPrem2 : eo_interprets M
                                        (concatClashLenPremise a1 a3) true := by
                                      simpa [hP2] using hPrem2Raw
                                    change eo_interprets M
                                      (__eo_prog_str_concat_clash a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2)) true
                                    rw [hProgEq]
                                    exact eo_interprets_concat_clash M hM
                                      a1 a2 a3 a4 T hA1Ty hA2Ty hA3Ty hA4Ty
                                      hPrem1 hPrem2
                                  · change RuleProofs.eo_has_smt_translation
                                      (__eo_prog_str_concat_clash a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2))
                                    rw [hProgEq]
                                    exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _ hBool
