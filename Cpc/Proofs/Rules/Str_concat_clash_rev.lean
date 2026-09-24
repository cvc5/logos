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

private abbrev rawRevEqConclusion (left right : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq) left) right))
    (Term.Boolean false)

private theorem raw_rev_eq_conclusion_eq (left right : Term)
    (h : rawRevEqConclusion left right ≠ Term.Stuck) :
    rawRevEqConclusion left right =
      mkEq (mkEq left right) (Term.Boolean false) := by
  let f1 := __eo_mk_apply (Term.UOp UserOp.eq) left
  let inner := __eo_mk_apply f1 right
  let f2 := __eo_mk_apply (Term.UOp UserOp.eq) inner
  have hf2 : f2 ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f2 (Term.Boolean false)
      (by simpa [rawRevEqConclusion, f1, inner, f2] using h)
  have hInner : inner ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) inner hf2
  have hf1 : f1 ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f1 right hInner
  have e1 : f1 = Term.Apply (Term.UOp UserOp.eq) left :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) left hf1
  have e2 : inner = Term.Apply f1 right :=
    eo_mk_apply_eq_apply_of_ne_stuck f1 right hInner
  have e3 : f2 = Term.Apply (Term.UOp UserOp.eq) inner :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) inner hf2
  have e4 : __eo_mk_apply f2 (Term.Boolean false) =
      Term.Apply f2 (Term.Boolean false) :=
    eo_mk_apply_eq_apply_of_ne_stuck f2 (Term.Boolean false)
      (by simpa [rawRevEqConclusion, f1, inner, f2] using h)
  change __eo_mk_apply f2 (Term.Boolean false) =
    mkEq (mkEq left right) (Term.Boolean false)
  rw [e4, e3, e2, e1]

private theorem prog_str_concat_clash_rev_info
    (x xs y ys P1 P2 : Term)
    (hProg : __eo_prog_str_concat_clash_rev x xs y ys (Proof.pf P1)
      (Proof.pf P2) ≠ Term.Stuck) :
    P1 = concatClashNePremise x y ∧
      P2 = concatClashLenPremise x y ∧
      __eo_prog_str_concat_clash_rev x xs y ys (Proof.pf P1) (Proof.pf P2) =
        concatClashRevConclusion x xs y ys := by
  let X := x
  let XS := xs
  let Y := y
  let YS := ys
  unfold __eo_prog_str_concat_clash_rev at hProg
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
    let left := concatClashRevTail X XS
    let right := concatClashRevTail Y YS
    have hBody :
        __eo_prog_str_concat_clash_rev X XS Y YS
            (Proof.pf (concatClashNePremise X Y))
            (Proof.pf (concatClashLenPremise X Y)) =
          rawRevEqConclusion left right := by
      simp_all [__eo_prog_str_concat_clash_rev, __eo_requires, __eo_eq, __eo_and,
        native_ite, native_teq, native_and, SmtEval.native_not,
        rawRevEqConclusion, X, XS, Y, YS, left, right, concatClashRevTail,
        concatClashNePremise, concatClashLenPremise, mkEq, mkStrLen]
    have hRawNe : rawRevEqConclusion left right ≠ Term.Stuck := by
      have hResultNe := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
      simpa [rawRevEqConclusion, left, right, X, XS, Y, YS,
        concatClashRevTail] using hResultNe
    refine ⟨rfl, rfl, ?_⟩
    rw [hBody]
    simpa [X, XS, Y, YS, left, right, concatClashRevConclusion] using
      raw_rev_eq_conclusion_eq left right hRawNe

public theorem cmd_step_str_concat_clash_rev_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_clash_rev args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash_rev args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_clash_rev args premises ≠
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
                                      (__eo_prog_str_concat_clash_rev a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2)) =
                                    Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_concat_clash_rev a1 a2 a3 a4
                                          (Proof.pf P1) (Proof.pf P2) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_concat_clash_rev_info
                                      a1 a2 a3 a4 P1 P2 hRuleProg with
                                    ⟨hP1, hP2, hProgEq⟩
                                  have hConclusionTy :
                                      __eo_typeof
                                          (concatClashRevConclusion a1 a2 a3 a4) =
                                        Term.Bool := by
                                    simpa [hProgEq] using hResultTy
                                  rcases concat_clash_rev_tail_eo_types_not_stuck
                                      a1 a2 a3 a4 hConclusionTy with
                                    ⟨hLeftEoTy, hRightEoTy⟩
                                  rcases concat_clash_rev_tail_smt_types
                                      a1 a2 hA1Trans hA2Trans hLeftEoTy with
                                    ⟨T, hA1Ty, hA2Ty, hLeftTy⟩
                                  rcases concat_clash_rev_tail_smt_types
                                      a3 a4 hA3Trans hA4Trans hRightEoTy with
                                    ⟨U, hA3TyU, hA4TyU, hRightTyU⟩
                                  have hP1BoolRaw :
                                      RuleProofs.eo_has_bool_type P1 :=
                                    hPremisesBool P1 (by
                                      simp [P1, premiseTermList])
                                  have hP1Bool : RuleProofs.eo_has_bool_type
                                      (concatClashNePremise a1 a3) := by
                                    simpa [hP1] using hP1BoolRaw
                                  have hSame :=
                                    concat_clash_ne_operands_same_smt_type
                                      a1 a3 hP1Bool
                                  have hTU : T = U := by
                                    have hSeq : SmtType.Seq T = SmtType.Seq U := by
                                      rw [← hA1Ty, ← hA3TyU]
                                      exact hSame.1
                                    injection hSeq
                                  subst U
                                  have hBool := eo_has_bool_type_concat_clash_rev
                                    a1 a2 a3 a4 T hA1Ty hA2Ty hA3TyU hA4TyU
                                      hLeftTy hRightTyU
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem1Raw : eo_interprets M P1 true :=
                                      hTrue P1 (by simp [P1, premiseTermList])
                                    have hPrem2Raw : eo_interprets M P2 true :=
                                      hTrue P2 (by simp [P2, premiseTermList])
                                    have hPrem1 : eo_interprets M
                                        (concatClashNePremise a1 a3) true := by
                                      simpa [hP1] using hPrem1Raw
                                    have hPrem2 : eo_interprets M
                                        (concatClashLenPremise a1 a3) true := by
                                      simpa [hP2] using hPrem2Raw
                                    change eo_interprets M
                                      (__eo_prog_str_concat_clash_rev a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2)) true
                                    rw [hProgEq]
                                    exact eo_interprets_concat_clash_rev M hM
                                      a1 a2 a3 a4 T hA1Ty hA2Ty hA3TyU hA4TyU
                                      hLeftTy hRightTyU hLeftEoTy hRightEoTy
                                      hPrem1 hPrem2
                                  · change RuleProofs.eo_has_smt_translation
                                      (__eo_prog_str_concat_clash_rev a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2))
                                    rw [hProgEq]
                                    exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _ hBool
