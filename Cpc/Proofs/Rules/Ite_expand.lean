module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_ite_expand_eq_of_ne_stuck (c1 x1 y1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_ite_expand c1 x1 y1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
            (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))
          (Term.Apply (Term.Apply Term.and
            (Term.Apply (Term.Apply Term.or c1)
              (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
            (Term.Boolean true))) := by
  intro hC1 hX1 hY1
  unfold __eo_prog_ite_expand
  split <;> simp_all

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

private theorem eo_typeof_ite_bool_self (X : Term) (hX : X ≠ Term.Stuck) :
    __eo_typeof_ite Term.Bool X X = X := by
  exact RuleProofs.eo_typeof_ite_bool_self X hX

private theorem eo_typeof_or_bool_or_stuck (A B : Term) :
    __eo_typeof_or A B = Term.Bool ∨ __eo_typeof_or A B = Term.Stuck := by
  cases A <;> cases B <;> simp [__eo_typeof_or]

private theorem typeof_args_of_prog_ite_expand_bool (c1 x1 y1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_ite_expand c1 x1 y1) = Term.Bool ->
    __eo_typeof c1 = Term.Bool ∧ __eo_typeof x1 = Term.Bool ∧
      __eo_typeof y1 = Term.Bool := by
  intro hC1 hX1 hY1 hTy
  rw [prog_ite_expand_eq_of_ne_stuck c1 x1 y1 hC1 hX1 hY1] at hTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))
      (__eo_typeof (Term.Apply (Term.Apply Term.and
        (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or c1)
            (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
          (Term.Boolean true)))) = Term.Bool at hTy
  rcases eo_typeof_eq_bool_same _ _ hTy with ⟨hSides, hLNonStuck⟩
  rcases eo_typeof_ite_args_of_ne_stuck (__eo_typeof c1) (__eo_typeof x1)
      (__eo_typeof y1) hLNonStuck with ⟨hC1Type, hXY, hXNonStuck⟩
  have hLeftRed :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1) =
        __eo_typeof x1 := by
    change __eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1) =
      __eo_typeof x1
    rw [hC1Type, ← hXY]
    exact eo_typeof_ite_bool_self (__eo_typeof x1) hXNonStuck
  have hAndCases :
      __eo_typeof (Term.Apply (Term.Apply Term.and
        (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or c1)
            (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
          (Term.Boolean true))) = Term.Bool ∨
      __eo_typeof (Term.Apply (Term.Apply Term.and
        (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or c1)
            (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
          (Term.Boolean true))) = Term.Stuck :=
    eo_typeof_or_bool_or_stuck _ _
  rw [hLeftRed] at hSides
  have hX1Type : __eo_typeof x1 = Term.Bool := by
    rcases hAndCases with h | h
    · exact hSides.trans h
    · exact absurd (hSides.trans h) hXNonStuck
  have hY1Type : __eo_typeof y1 = Term.Bool := hXY ▸ hX1Type
  exact ⟨hC1Type, hX1Type, hY1Type⟩

private theorem typed___eo_prog_ite_expand_impl (c1 x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_expand c1 x1 y1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_ite_expand c1 x1 y1) := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  rcases typeof_args_of_prog_ite_expand_bool c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck hResultTy with ⟨hC1Type, hX1Type, hY1Type⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  have hY1Bool : RuleProofs.eo_has_bool_type y1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 Term.Bool (__eo_to_smt y1) rfl hY1Trans hY1Type
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1) :=
    CnfSupport.eo_has_bool_type_ite_of_bool_args c1 x1 y1 hC1Bool hX1Bool hY1Bool
  have hNotC1Bool : RuleProofs.eo_has_bool_type (Term.Apply Term.not c1) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg c1 hC1Bool
  have hOrX1Bool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args x1 (Term.Boolean false) hX1Bool
      RuleProofs.eo_has_bool_type_false
  have hInnerLeftBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args _ _ hNotC1Bool hOrX1Bool
  have hOrY1Bool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args y1 (Term.Boolean false) hY1Bool
      RuleProofs.eo_has_bool_type_false
  have hInnerRightInnerBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or c1)
          (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args c1 _ hC1Bool hOrY1Bool
  have hInnerRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or c1)
            (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
          (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ (Term.Boolean true)
      hInnerRightInnerBool RuleProofs.eo_has_bool_type_true
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
            (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))
          (Term.Apply (Term.Apply Term.and
            (Term.Apply (Term.Apply Term.or c1)
              (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
            (Term.Boolean true))) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hInnerLeftBool hInnerRightBool
  rw [prog_ite_expand_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck hY1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by
      rw [hLeftBool]
      decide)

private theorem facts___eo_prog_ite_expand_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_expand c1 x1 y1) = Term.Bool ->
  eo_interprets M (__eo_prog_ite_expand c1 x1 y1) true := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_ite_expand c1 x1 y1) :=
    typed___eo_prog_ite_expand_impl c1 x1 y1 hC1Trans hX1Trans hY1Trans hResultTy
  rcases typeof_args_of_prog_ite_expand_bool c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck hResultTy with ⟨hC1Type, hX1Type, hY1Type⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  have hY1Bool : RuleProofs.eo_has_bool_type y1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 Term.Bool (__eo_to_smt y1) rfl hY1Trans hY1Type
  rw [prog_ite_expand_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_ite_expand_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM c1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x1 hX1Bool with
      ⟨bx, hEvalX1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM y1 hY1Bool with
      ⟨bY, hEvalY1⟩
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1) =
        SmtTerm.ite (__eo_to_smt c1) (__eo_to_smt x1) (__eo_to_smt y1) by rfl]
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply Term.and
          (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1))
            (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))
          (Term.Apply (Term.Apply Term.and
            (Term.Apply (Term.Apply Term.or c1)
              (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false))))
            (Term.Boolean true))) =
        SmtTerm.and
          (SmtTerm.or (SmtTerm.not (__eo_to_smt c1))
            (SmtTerm.or (__eo_to_smt x1) (SmtTerm.Boolean false)))
          (SmtTerm.and
            (SmtTerm.or (__eo_to_smt c1)
              (SmtTerm.or (__eo_to_smt y1) (SmtTerm.Boolean false)))
            (SmtTerm.Boolean true)) by rfl]
    simp only [smtx_eval_ite_term_eq, smtx_eval_and_term_eq, smtx_eval_or_term_eq,
      smtx_eval_not_term_eq, hEvalC1, hEvalX1, hEvalY1]
    cases bc <;> cases bx <;> cases bY <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_ite,
        __smtx_model_eval_and, __smtx_model_eval_or, __smtx_model_eval_not,
        __smtx_model_eval.eq_1, native_veq, SmtEval.native_and, SmtEval.native_or,
        SmtEval.native_not]

public theorem cmd_step_ite_expand_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_expand args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_expand args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_expand args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.ite_expand args premises ≠ Term.Stuck :=
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
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                        hATransPair.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                        hATransPair.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                        hATransPair.2.2.1
                      change __eo_typeof (__eo_prog_ite_expand a1 a2 a3) = Term.Bool
                        at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (__eo_prog_ite_expand a1 a2 a3) true
                        exact facts___eo_prog_ite_expand_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_ite_expand_impl a1 a2 a3 hA1Trans hA2Trans
                            hA3Trans hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
