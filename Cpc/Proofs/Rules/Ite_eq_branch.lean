module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_ite_eq_branch_eq_of_ne_stuck (c1 x1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    __eo_prog_ite_eq_branch c1 x1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) x1)) x1 := by
  intro hC1 hX1
  cases c1 <;> cases x1 <;> simp [__eo_prog_ite_eq_branch] at hC1 hX1 ⊢

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem eo_typeof_ite_args_of_ne_stuck
    (C X Y : Term) :
    __eo_typeof_ite C X Y ≠ Term.Stuck ->
      C = Term.Bool ∧ X = Y ∧ X ≠ Term.Stuck := by
  intro h
  exact RuleProofs.eo_typeof_ite_args_of_ne_stuck C X Y h

private theorem args_of_prog_ite_eq_branch_bool (c1 x1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_ite_eq_branch c1 x1) = Term.Bool ->
    __eo_typeof c1 = Term.Bool ∧ __eo_typeof x1 ≠ Term.Stuck := by
  intro hC1 hX1 hTy
  rw [prog_ite_eq_branch_eq_of_ne_stuck c1 x1 hC1 hX1] at hTy
  change __eo_typeof_eq
    (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof x1))
    (__eo_typeof x1) = Term.Bool at hTy
  rcases eo_typeof_eq_bool_same
      (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof x1))
      (__eo_typeof x1) hTy with
    ⟨_hIteEq, hIteNonStuck⟩
  rcases eo_typeof_ite_args_of_ne_stuck (__eo_typeof c1) (__eo_typeof x1)
      (__eo_typeof x1) hIteNonStuck with
    ⟨hC1Type, _hBranchTypes, hXTypeNonStuck⟩
  exact ⟨hC1Type, hXTypeNonStuck⟩

private theorem smt_type_ite_same_as_then
    (c x y : Term) :
  RuleProofs.eo_has_bool_type c ->
  RuleProofs.eo_has_smt_translation x ->
  RuleProofs.eo_has_smt_translation y ->
  __eo_typeof x = __eo_typeof y ->
  __smtx_typeof
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c) x) y)) =
    __smtx_typeof (__eo_to_smt x) := by
  intro hCBool hXTrans hYTrans hTypes
  rw [RuleProofs.eo_has_bool_type] at hCBool
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y (__eo_typeof y) (__eo_to_smt y) rfl hYTrans rfl
  rw [show __eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply Term.ite c) x) y) =
      SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y) by
      rfl]
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hCBool, hXSmtTy, hYSmtTy, ← hTypes, native_Teq,
    native_ite]

private theorem typed___eo_prog_ite_eq_branch_impl (c1 x1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof (__eo_prog_ite_eq_branch c1 x1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_ite_eq_branch c1 x1) := by
  intro hC1Trans hX1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases args_of_prog_ite_eq_branch_bool c1 x1 hC1NotStuck hX1NotStuck
      hResultTy with
    ⟨hC1Type, _hXTypeNonStuck⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  let iteTerm :=
    Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) x1
  have hIteSame : __smtx_typeof (__eo_to_smt iteTerm) =
      __smtx_typeof (__eo_to_smt x1) := by
    simpa [iteTerm] using smt_type_ite_same_as_then c1 x1 x1 hC1Bool
      hX1Trans hX1Trans rfl
  have hIteNonNone : __smtx_typeof (__eo_to_smt iteTerm) ≠ SmtType.None := by
    rw [hIteSame]
    exact hX1Trans
  rw [prog_ite_eq_branch_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type iteTerm x1 hIteSame
    hIteNonNone

private theorem facts___eo_prog_ite_eq_branch_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof (__eo_prog_ite_eq_branch c1 x1) = Term.Bool ->
  eo_interprets M (__eo_prog_ite_eq_branch c1 x1) true := by
  intro hC1Trans hX1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_ite_eq_branch c1 x1) :=
    typed___eo_prog_ite_eq_branch_impl c1 x1 hC1Trans hX1Trans hResultTy
  rcases args_of_prog_ite_eq_branch_bool c1 x1 hC1NotStuck hX1NotStuck
      hResultTy with
    ⟨hC1Type, _hXTypeNonStuck⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  rw [prog_ite_eq_branch_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_ite_eq_branch_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
      using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM c1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) x1) =
        SmtTerm.ite (__eo_to_smt c1) (__eo_to_smt x1) (__eo_to_smt x1) by
        rfl]
    simp only [smtx_eval_ite_term_eq, hEvalC1]
    cases bc <;>
      simpa [__smtx_model_eval_ite] using
        RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x1))

public theorem cmd_step_ite_eq_branch_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_eq_branch args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_eq_branch args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_eq_branch args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_eq_branch args premises ≠ Term.Stuck :=
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
              cases premises with
              | nil =>
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_ite_eq_branch a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_ite_eq_branch a1 a2) true
                    exact facts___eo_prog_ite_eq_branch_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_ite_eq_branch_impl a1 a2 hA1Trans hA2Trans
                        hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
