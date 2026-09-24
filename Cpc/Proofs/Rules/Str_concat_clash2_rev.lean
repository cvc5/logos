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

private abbrev rawRev2EqConclusion (left right : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) left) right))
    (Term.Boolean false)

private theorem raw_rev2_eq_conclusion_eq (left right : Term)
    (h : rawRev2EqConclusion left right ≠ Term.Stuck) :
    rawRev2EqConclusion left right =
      mkEq (mkEq left right) (Term.Boolean false) := by
  let inner := __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) left) right
  let f := __eo_mk_apply (Term.UOp UserOp.eq) inner
  have hf : f ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f (Term.Boolean false)
      (by simpa [rawRev2EqConclusion, inner, f] using h)
  have hInner : inner ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) inner hf
  have e1 : inner = Term.Apply (Term.Apply (Term.UOp UserOp.eq) left) right :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) left) right hInner
  have e2 : f = Term.Apply (Term.UOp UserOp.eq) inner :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) inner hf
  have e3 : __eo_mk_apply f (Term.Boolean false) =
      Term.Apply f (Term.Boolean false) :=
    eo_mk_apply_eq_apply_of_ne_stuck f (Term.Boolean false)
      (by simpa [rawRev2EqConclusion, inner, f] using h)
  change __eo_mk_apply f (Term.Boolean false) =
    mkEq (mkEq left right) (Term.Boolean false)
  rw [e3, e2, e1]

private theorem prog_str_concat_clash2_rev_info
    (x y ys P1 P2 : Term)
    (hProg : __eo_prog_str_concat_clash2_rev x y ys (Proof.pf P1)
      (Proof.pf P2) ≠ Term.Stuck) :
    P1 = concatClashNePremise x y ∧
      P2 = concatClashLenPremise x y ∧
      __eo_prog_str_concat_clash2_rev x y ys (Proof.pf P1) (Proof.pf P2) =
        concatClash2RevConclusion x y ys := by
  let X := x
  let Y := y
  let YS := ys
  unfold __eo_prog_str_concat_clash2_rev at hProg
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
    let right := concatClashRevTail Y YS
    have hBody :
        __eo_prog_str_concat_clash2_rev X Y YS
            (Proof.pf (concatClashNePremise X Y))
            (Proof.pf (concatClashLenPremise X Y)) =
          rawRev2EqConclusion X right := by
      simp_all [__eo_prog_str_concat_clash2_rev, __eo_requires, __eo_eq,
        __eo_and, native_ite, native_teq, native_and, SmtEval.native_not,
        rawRev2EqConclusion, X, Y, YS, right, concatClashRevTail,
        concatClashNePremise, concatClashLenPremise, mkEq, mkStrLen]
    have hRawNe : rawRev2EqConclusion X right ≠ Term.Stuck := by
      have hResultNe := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
      simpa [rawRev2EqConclusion, X, Y, YS, right,
        concatClashRevTail] using hResultNe
    refine ⟨rfl, rfl, ?_⟩
    rw [hBody]
    simpa [X, Y, YS, right, concatClash2RevConclusion] using
      raw_rev2_eq_conclusion_eq X right hRawNe

public theorem cmd_step_str_concat_clash2_rev_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash2_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_clash2_rev args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash2_rev args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_clash2_rev args premises ≠
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
                              change __eo_typeof
                                  (__eo_prog_str_concat_clash2_rev a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_concat_clash2_rev a1 a2 a3
                                      (Proof.pf P1) (Proof.pf P2) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_concat_clash2_rev_info
                                  a1 a2 a3 P1 P2 hRuleProg with
                                ⟨hP1, hP2, hProgEq⟩
                              have hConclusionTy :
                                  __eo_typeof
                                      (concatClash2RevConclusion a1 a2 a3) =
                                    Term.Bool := by
                                simpa [hProgEq] using hResultTy
                              have hRightEoTy :=
                                concat_clash2_rev_tail_eo_type_not_stuck
                                  a1 a2 a3 hConclusionTy
                              rcases concat_clash_rev_tail_smt_types
                                  a2 a3 hA2Trans hA3Trans hRightEoTy with
                                ⟨T, hA2Ty, hA3Ty, hRightTy⟩
                              have hP1BoolRaw :
                                  RuleProofs.eo_has_bool_type P1 :=
                                hPremisesBool P1 (by
                                  simp [P1, premiseTermList])
                              have hP1Bool : RuleProofs.eo_has_bool_type
                                  (concatClashNePremise a1 a2) := by
                                simpa [hP1] using hP1BoolRaw
                              have hSame :=
                                concat_clash_ne_operands_same_smt_type
                                  a1 a2 hP1Bool
                              have hA1Ty :
                                  __smtx_typeof (__eo_to_smt a1) =
                                    SmtType.Seq T :=
                                hSame.1.trans hA2Ty
                              have hBool := eo_has_bool_type_concat_clash2_rev
                                a1 a2 a3 T hA1Ty hA2Ty hA3Ty hRightTy
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPrem1Raw : eo_interprets M P1 true :=
                                  hTrue P1 (by simp [P1, premiseTermList])
                                have hPrem2Raw : eo_interprets M P2 true :=
                                  hTrue P2 (by simp [P2, premiseTermList])
                                have hPrem1 : eo_interprets M
                                    (concatClashNePremise a1 a2) true := by
                                  simpa [hP1] using hPrem1Raw
                                have hPrem2 : eo_interprets M
                                    (concatClashLenPremise a1 a2) true := by
                                  simpa [hP2] using hPrem2Raw
                                change eo_interprets M
                                  (__eo_prog_str_concat_clash2_rev a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2)) true
                                rw [hProgEq]
                                exact eo_interprets_concat_clash2_rev M hM
                                  a1 a2 a3 T hA1Ty hA2Ty hA3Ty hRightTy
                                  hRightEoTy hPrem1 hPrem2
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_concat_clash2_rev a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2))
                                rw [hProgEq]
                                exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _ hBool
