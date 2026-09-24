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

private theorem prog_bool_not_ite_elim_eq_of_ne_stuck (c1 x1 y1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_bool_not_ite_elim c1 x1 y1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply Term.not
          (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)))
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1)
          (Term.Apply Term.not x1)) (Term.Apply Term.not y1)) := by
  intro hC1 hX1 hY1
  cases c1 <;> cases x1 <;> cases y1 <;>
    simp [__eo_prog_bool_not_ite_elim] at hC1 hX1 hY1 ⊢

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem eo_typeof_not_nonstuck_bool_arg (A : Term) :
    __eo_typeof_not A ≠ Term.Stuck ->
    A = Term.Bool := by
  intro hNotStuck
  cases A <;> simp [__eo_typeof_not] at hNotStuck ⊢

private theorem eo_typeof_ite_args_of_ne_stuck
    (C X Y : Term) :
    __eo_typeof_ite C X Y ≠ Term.Stuck ->
      C = Term.Bool ∧ X = Y ∧ X ≠ Term.Stuck := by
  intro h
  exact RuleProofs.eo_typeof_ite_args_of_ne_stuck C X Y h

private theorem eo_typeof_ite_bool_same_of_ne_stuck
    (T : Term) :
    T ≠ Term.Stuck ->
      __eo_typeof_ite Term.Bool T T = T := by
  intro hT
  exact RuleProofs.eo_typeof_ite_bool_self T hT

private theorem eo_typeof_ite_bool_args (C X Y : Term) :
    __eo_typeof_ite C X Y = Term.Bool ->
    C = Term.Bool ∧ X = Term.Bool ∧ Y = Term.Bool := by
  intro hTy
  have hNonStuck : __eo_typeof_ite C X Y ≠ Term.Stuck := by
    intro hStuck
    rw [hTy] at hStuck
    cases hStuck
  rcases eo_typeof_ite_args_of_ne_stuck C X Y hNonStuck with
    ⟨hC, hXY, hXNonStuck⟩
  have hSame : __eo_typeof_ite Term.Bool X X = X :=
    eo_typeof_ite_bool_same_of_ne_stuck X hXNonStuck
  have hX : X = Term.Bool := by
    rw [hC, ← hXY] at hTy
    rw [hSame] at hTy
    exact hTy
  exact ⟨hC, hX, by rw [← hXY]; exact hX⟩

private theorem typeof_args_of_prog_bool_not_ite_elim_bool (c1 x1 y1 : Term) :
    __eo_typeof (__eo_prog_bool_not_ite_elim c1 x1 y1) = Term.Bool ->
    __eo_typeof c1 = Term.Bool ∧ __eo_typeof x1 = Term.Bool ∧
      __eo_typeof y1 = Term.Bool := by
  intro hTy
  by_cases hC1 : c1 = Term.Stuck
  · subst c1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hX1 : x1 = Term.Stuck
    · subst x1
      cases c1 <;> simp [__eo_prog_bool_not_ite_elim] at hC1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · by_cases hY1 : y1 = Term.Stuck
      · subst y1
        cases c1 <;> cases x1 <;> simp [__eo_prog_bool_not_ite_elim] at hC1 hX1 hTy
        all_goals
          have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
            native_decide
          exact False.elim (hStuckTy hTy)
      · rw [prog_bool_not_ite_elim_eq_of_ne_stuck c1 x1 y1 hC1 hX1 hY1] at hTy
        change __eo_typeof_eq
          (__eo_typeof_not
            (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1)))
          (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof_not (__eo_typeof x1))
            (__eo_typeof_not (__eo_typeof y1))) =
          Term.Bool at hTy
        rcases eo_typeof_eq_bool_same
            (__eo_typeof_not
              (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1)))
            (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof_not (__eo_typeof x1))
              (__eo_typeof_not (__eo_typeof y1))) hTy with
          ⟨_hSides, hLeftNotStuck⟩
        have hIteBool :
            __eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1) =
              Term.Bool :=
          eo_typeof_not_nonstuck_bool_arg
            (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1))
            hLeftNotStuck
        exact eo_typeof_ite_bool_args (__eo_typeof c1) (__eo_typeof x1)
          (__eo_typeof y1) hIteBool

private theorem typed___eo_prog_bool_not_ite_elim_impl (c1 x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_bool_not_ite_elim c1 x1 y1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_bool_not_ite_elim c1 x1 y1) := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  rcases typeof_args_of_prog_bool_not_ite_elim_bool c1 x1 y1 hResultTy with
    ⟨hC1Type, hX1Type, hY1Type⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  have hY1Bool : RuleProofs.eo_has_bool_type y1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 Term.Bool (__eo_to_smt y1) rfl hY1Trans hY1Type
  have hIteBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1) :=
    CnfSupport.eo_has_bool_type_ite_of_bool_args c1 x1 y1 hC1Bool hX1Bool hY1Bool
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not
          (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg _ hIteBool
  have hNotXBool : RuleProofs.eo_has_bool_type (Term.Apply Term.not x1) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg x1 hX1Bool
  have hNotYBool : RuleProofs.eo_has_bool_type (Term.Apply Term.not y1) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg y1 hY1Bool
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Apply Term.not x1))
          (Term.Apply Term.not y1)) :=
    CnfSupport.eo_has_bool_type_ite_of_bool_args c1 (Term.Apply Term.not x1)
      (Term.Apply Term.not y1) hC1Bool hNotXBool hNotYBool
  rw [prog_bool_not_ite_elim_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
    hY1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by
      rw [hLeftBool]
      decide)

private theorem facts___eo_prog_bool_not_ite_elim_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_bool_not_ite_elim c1 x1 y1) = Term.Bool ->
  eo_interprets M (__eo_prog_bool_not_ite_elim c1 x1 y1) true := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bool_not_ite_elim c1 x1 y1) :=
    typed___eo_prog_bool_not_ite_elim_impl c1 x1 y1 hC1Trans hX1Trans hY1Trans
      hResultTy
  rcases typeof_args_of_prog_bool_not_ite_elim_bool c1 x1 y1 hResultTy with
    ⟨hC1Type, hX1Type, hY1Type⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  have hY1Bool : RuleProofs.eo_has_bool_type y1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 Term.Bool (__eo_to_smt y1) rfl hY1Trans hY1Type
  rw [prog_bool_not_ite_elim_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
    hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bool_not_ite_elim_eq_of_ne_stuck c1 x1 y1 hC1NotStuck hX1NotStuck
      hY1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM c1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x1 hX1Bool with
      ⟨bx, hEvalX1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM y1 hY1Bool with
      ⟨bY, hEvalY1⟩
    rw [show __eo_to_smt
        (Term.Apply Term.not
          (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)) =
        SmtTerm.not (SmtTerm.ite (__eo_to_smt c1) (__eo_to_smt x1)
          (__eo_to_smt y1)) by
        rfl]
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Apply Term.not x1))
          (Term.Apply Term.not y1)) =
        SmtTerm.ite (__eo_to_smt c1) (SmtTerm.not (__eo_to_smt x1))
          (SmtTerm.not (__eo_to_smt y1)) by
        rfl]
    simp only [__smtx_model_eval.eq_7, smtx_eval_ite_term_eq, hEvalC1, hEvalX1,
      hEvalY1]
    cases bc <;> cases bx <;> cases bY <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_ite,
        __smtx_model_eval_not, native_veq, SmtEval.native_not]

public theorem cmd_step_bool_not_ite_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_ite_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_not_ite_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_ite_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_not_ite_elim args premises ≠ Term.Stuck :=
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
                      change __eo_typeof (__eo_prog_bool_not_ite_elim a1 a2 a3) =
                        Term.Bool at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (__eo_prog_bool_not_ite_elim a1 a2 a3) true
                        exact facts___eo_prog_bool_not_ite_elim_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_bool_not_ite_elim_impl a1 a2 a3
                            hA1Trans hA2Trans hA3Trans hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
