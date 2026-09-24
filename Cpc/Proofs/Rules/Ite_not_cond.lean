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

private theorem prog_ite_not_cond_eq_of_ne_stuck (c1 x1 y1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_ite_not_cond c1 x1 y1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not c1)) x1) y1))
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) y1) x1) := by
  intro hC1 hX1 hY1
  cases c1 <;> cases x1 <;> cases y1 <;>
    simp [__eo_prog_ite_not_cond] at hC1 hX1 hY1 ⊢

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem eo_typeof_not_arg_of_bool (A : Term) :
    __eo_typeof_not A = Term.Bool ->
    A = Term.Bool := by
  intro hTy
  cases A <;> simp [__eo_typeof_not] at hTy ⊢

private theorem eo_typeof_ite_args_of_ne_stuck
    (C X Y : Term) :
    __eo_typeof_ite C X Y ≠ Term.Stuck ->
      C = Term.Bool ∧ X = Y ∧ X ≠ Term.Stuck := by
  intro h
  exact RuleProofs.eo_typeof_ite_args_of_ne_stuck C X Y h

private theorem args_of_prog_ite_not_cond_bool (c1 x1 y1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_ite_not_cond c1 x1 y1) = Term.Bool ->
    __eo_typeof c1 = Term.Bool ∧ __eo_typeof x1 = __eo_typeof y1 ∧
      __eo_typeof x1 ≠ Term.Stuck := by
  intro hC1 hX1 hY1 hTy
  rw [prog_ite_not_cond_eq_of_ne_stuck c1 x1 y1 hC1 hX1 hY1] at hTy
  change __eo_typeof_eq
    (__eo_typeof_ite (__eo_typeof_not (__eo_typeof c1)) (__eo_typeof x1)
      (__eo_typeof y1))
    (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof y1) (__eo_typeof x1)) =
    Term.Bool at hTy
  rcases eo_typeof_eq_bool_same
      (__eo_typeof_ite (__eo_typeof_not (__eo_typeof c1)) (__eo_typeof x1)
        (__eo_typeof y1))
      (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof y1) (__eo_typeof x1))
      hTy with
    ⟨_hSides, hLeftNonStuck⟩
  rcases eo_typeof_ite_args_of_ne_stuck
      (__eo_typeof_not (__eo_typeof c1)) (__eo_typeof x1) (__eo_typeof y1)
      hLeftNonStuck with
    ⟨hNotCType, hBranchTypes, hXTypeNonStuck⟩
  exact ⟨eo_typeof_not_arg_of_bool (__eo_typeof c1) hNotCType, hBranchTypes,
    hXTypeNonStuck⟩

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

private theorem typed___eo_prog_ite_not_cond_impl (c1 x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_not_cond c1 x1 y1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_ite_not_cond c1 x1 y1) := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  rcases args_of_prog_ite_not_cond_bool c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck hResultTy with
    ⟨hC1Type, hBranchTypes, _hXTypeNonStuck⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hNotC1Bool : RuleProofs.eo_has_bool_type (Term.Apply Term.not c1) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg c1 hC1Bool
  let left :=
    Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not c1)) x1) y1
  let right :=
    Term.Apply (Term.Apply (Term.Apply Term.ite c1) y1) x1
  have hLeftSame : __smtx_typeof (__eo_to_smt left) =
      __smtx_typeof (__eo_to_smt x1) := by
    simpa [left] using smt_type_ite_same_as_then (Term.Apply Term.not c1) x1 y1
      hNotC1Bool hX1Trans hY1Trans hBranchTypes
  have hRightSame : __smtx_typeof (__eo_to_smt right) =
      __smtx_typeof (__eo_to_smt y1) := by
    simpa [right] using smt_type_ite_same_as_then c1 y1 x1 hC1Bool hY1Trans
      hX1Trans hBranchTypes.symm
  have hBranchSmtTypes :
      __smtx_typeof (__eo_to_smt x1) = __smtx_typeof (__eo_to_smt y1) := by
    have hXSmtTy :
        __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1) :=
      TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x1 (__eo_typeof x1) (__eo_to_smt x1) rfl hX1Trans rfl
    have hYSmtTy :
        __smtx_typeof (__eo_to_smt y1) = __eo_to_smt_type (__eo_typeof y1) :=
      TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        y1 (__eo_typeof y1) (__eo_to_smt y1) rfl hY1Trans rfl
    rw [hXSmtTy, hYSmtTy, hBranchTypes]
  have hSame : __smtx_typeof (__eo_to_smt left) =
      __smtx_typeof (__eo_to_smt right) :=
    hLeftSame.trans (hBranchSmtTypes.trans hRightSame.symm)
  have hLeftNonNone : __smtx_typeof (__eo_to_smt left) ≠ SmtType.None := by
    rw [hLeftSame]
    exact hX1Trans
  rw [prog_ite_not_cond_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
    hY1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type left right hSame
    hLeftNonNone

private theorem facts___eo_prog_ite_not_cond_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_not_cond c1 x1 y1) = Term.Bool ->
  eo_interprets M (__eo_prog_ite_not_cond c1 x1 y1) true := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_ite_not_cond c1 x1 y1) :=
    typed___eo_prog_ite_not_cond_impl c1 x1 y1 hC1Trans hX1Trans hY1Trans
      hResultTy
  rcases args_of_prog_ite_not_cond_bool c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck hResultTy with
    ⟨hC1Type, _hBranchTypes, _hXTypeNonStuck⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  rw [prog_ite_not_cond_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
    hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_ite_not_cond_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM c1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not c1)) x1)
          y1) =
        SmtTerm.ite (SmtTerm.not (__eo_to_smt c1)) (__eo_to_smt x1)
          (__eo_to_smt y1) by
        rfl]
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) y1) x1) =
        SmtTerm.ite (__eo_to_smt c1) (__eo_to_smt y1) (__eo_to_smt x1) by
        rfl]
    simp only [__smtx_model_eval.eq_7, smtx_eval_ite_term_eq, hEvalC1]
    cases bc
    · simpa [__smtx_model_eval_ite, __smtx_model_eval_not, SmtEval.native_not]
        using RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x1))
    · simpa [__smtx_model_eval_ite, __smtx_model_eval_not, SmtEval.native_not]
        using RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt y1))

public theorem cmd_step_ite_not_cond_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_not_cond args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_not_cond args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_not_cond args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_not_cond args premises ≠ Term.Stuck :=
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
              | nil =>
                  cases premises with
                  | nil =>
                      have hATransPair :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧
                              RuleProofs.eo_has_smt_translation a3 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                        hATransPair.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                        hATransPair.2.2.1
                      change __eo_typeof (__eo_prog_ite_not_cond a1 a2 a3) =
                        Term.Bool at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (__eo_prog_ite_not_cond a1 a2 a3) true
                        exact facts___eo_prog_ite_not_cond_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_ite_not_cond_impl a1 a2 a3
                            hA1Trans hA2Trans hA3Trans hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
