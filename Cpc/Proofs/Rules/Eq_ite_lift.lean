module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_eq_ite_lift_eq_of_ne_stuck (C1 t1 s1 r1 : Term) :
    C1 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    s1 ≠ Term.Stuck ->
    r1 ≠ Term.Stuck ->
    __eo_prog_eq_ite_lift C1 t1 s1 r1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1))
        (Term.Apply (Term.Apply (Term.Apply Term.ite C1)
          (Term.Apply (Term.Apply Term.eq t1) r1))
          (Term.Apply (Term.Apply Term.eq s1) r1)) := by
  intro hC1 ht1 hs1 hr1
  unfold __eo_prog_eq_ite_lift
  split <;> simp_all

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem eo_typeof_eq_args_of_ne_stuck (A B : Term) :
    __eo_typeof_eq A B ≠ Term.Stuck ->
    A = B ∧ A ≠ Term.Stuck := by
  intro h
  exact RuleProofs.eo_typeof_eq_args_of_ne_stuck A B h

private theorem eo_typeof_ite_args_of_ne_stuck
    (C X Y : Term) :
    __eo_typeof_ite C X Y ≠ Term.Stuck ->
      C = Term.Bool ∧ X = Y ∧ X ≠ Term.Stuck := by
  intro h
  exact RuleProofs.eo_typeof_ite_args_of_ne_stuck C X Y h

private theorem eo_typeof_ite_bool_self (X : Term) (hX : X ≠ Term.Stuck) :
    __eo_typeof_ite Term.Bool X X = X := by
  exact RuleProofs.eo_typeof_ite_bool_self X hX

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

private theorem smt_branches_eq_of_typeof_eq
    (x y : Term) :
  RuleProofs.eo_has_smt_translation x ->
  RuleProofs.eo_has_smt_translation y ->
  __eo_typeof x = __eo_typeof y ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) := by
  intro hXTrans hYTrans hTypes
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y (__eo_typeof y) (__eo_to_smt y) rfl hYTrans rfl
  rw [hXSmtTy, hYSmtTy, hTypes]

private theorem args_of_prog_eq_ite_lift (C1 t1 s1 r1 : Term) :
    C1 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    s1 ≠ Term.Stuck ->
    r1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_eq_ite_lift C1 t1 s1 r1) = Term.Bool ->
    __eo_typeof C1 = Term.Bool ∧ __eo_typeof t1 = __eo_typeof s1 ∧
      __eo_typeof t1 = __eo_typeof r1 ∧ __eo_typeof t1 ≠ Term.Stuck := by
  intro hC1 ht1 hs1 hr1 hTy
  rw [prog_eq_ite_lift_eq_of_ne_stuck C1 t1 s1 r1 hC1 ht1 hs1 hr1] at hTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1))
      (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.ite C1)
        (Term.Apply (Term.Apply Term.eq t1) r1))
        (Term.Apply (Term.Apply Term.eq s1) r1))) = Term.Bool at hTy
  rcases eo_typeof_eq_bool_same _ _ hTy with ⟨_hSides, hLNonStuck⟩
  rcases eo_typeof_eq_args_of_ne_stuck
      (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1))
      (__eo_typeof r1) hLNonStuck with ⟨hIteEqR, hIteNonStuck⟩
  rcases eo_typeof_ite_args_of_ne_stuck (__eo_typeof C1) (__eo_typeof t1)
      (__eo_typeof s1) hIteNonStuck with ⟨hCType, hTS, hTNonStuck⟩
  have hIteRed :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1) =
        __eo_typeof t1 := by
    change __eo_typeof_ite (__eo_typeof C1) (__eo_typeof t1) (__eo_typeof s1) =
      __eo_typeof t1
    rw [hCType, ← hTS]
    exact eo_typeof_ite_bool_self (__eo_typeof t1) hTNonStuck
  have hTR : __eo_typeof t1 = __eo_typeof r1 := by
    rw [← hIteRed]; exact hIteEqR
  exact ⟨hCType, hTS, hTR, hTNonStuck⟩

private theorem typed___eo_prog_eq_ite_lift_impl (C1 t1 s1 r1 : Term) :
  RuleProofs.eo_has_smt_translation C1 ->
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  RuleProofs.eo_has_smt_translation r1 ->
  __eo_typeof (__eo_prog_eq_ite_lift C1 t1 s1 r1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_eq_ite_lift C1 t1 s1 r1) := by
  intro hC1Trans hT1Trans hS1Trans hR1Trans hResultTy
  have hC1NotStuck : C1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation C1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hR1NotStuck : r1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r1 hR1Trans
  rcases args_of_prog_eq_ite_lift C1 t1 s1 r1 hC1NotStuck hT1NotStuck hS1NotStuck
      hR1NotStuck hResultTy with ⟨hCType, hTS, hTR, _hTNonStuck⟩
  have hC1Bool : RuleProofs.eo_has_bool_type C1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      C1 Term.Bool (__eo_to_smt C1) rfl hC1Trans hCType
  have hIteSmt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_type_ite_same_as_then C1 t1 s1 hC1Bool hT1Trans hS1Trans hTS
  have hTRSmt :
      __smtx_typeof (__eo_to_smt t1) = __smtx_typeof (__eo_to_smt r1) :=
    smt_branches_eq_of_typeof_eq t1 r1 hT1Trans hR1Trans hTR
  have hTSSmt :
      __smtx_typeof (__eo_to_smt t1) = __smtx_typeof (__eo_to_smt s1) :=
    smt_branches_eq_of_typeof_eq t1 s1 hT1Trans hS1Trans hTS
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hIteSmt.trans hTRSmt)
      (by rw [hIteSmt]; exact hT1Trans)
  have hEqTrBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t1) r1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ hTRSmt hT1Trans
  have hEqSrBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s1) r1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hTSSmt.symm.trans hTRSmt) hS1Trans
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply Term.ite C1)
          (Term.Apply (Term.Apply Term.eq t1) r1))
          (Term.Apply (Term.Apply Term.eq s1) r1)) :=
    CnfSupport.eo_has_bool_type_ite_of_bool_args C1
      (Term.Apply (Term.Apply Term.eq t1) r1)
      (Term.Apply (Term.Apply Term.eq s1) r1) hC1Bool hEqTrBool hEqSrBool
  rw [prog_eq_ite_lift_eq_of_ne_stuck C1 t1 s1 r1 hC1NotStuck hT1NotStuck
    hS1NotStuck hR1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by rw [hLeftBool]; decide)

private theorem facts___eo_prog_eq_ite_lift_impl
    (M : SmtModel) (hM : model_wf M) (C1 t1 s1 r1 : Term) :
  RuleProofs.eo_has_smt_translation C1 ->
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  RuleProofs.eo_has_smt_translation r1 ->
  __eo_typeof (__eo_prog_eq_ite_lift C1 t1 s1 r1) = Term.Bool ->
  eo_interprets M (__eo_prog_eq_ite_lift C1 t1 s1 r1) true := by
  intro hC1Trans hT1Trans hS1Trans hR1Trans hResultTy
  have hC1NotStuck : C1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation C1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hR1NotStuck : r1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r1 hR1Trans
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_eq_ite_lift C1 t1 s1 r1) :=
    typed___eo_prog_eq_ite_lift_impl C1 t1 s1 r1 hC1Trans hT1Trans hS1Trans
      hR1Trans hResultTy
  rcases args_of_prog_eq_ite_lift C1 t1 s1 r1 hC1NotStuck hT1NotStuck hS1NotStuck
      hR1NotStuck hResultTy with ⟨hCType, _hTS, _hTR, _hTNonStuck⟩
  have hC1Bool : RuleProofs.eo_has_bool_type C1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      C1 Term.Bool (__eo_to_smt C1) rfl hC1Trans hCType
  rw [prog_eq_ite_lift_eq_of_ne_stuck C1 t1 s1 r1 hC1NotStuck hT1NotStuck
    hS1NotStuck hR1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_eq_ite_lift_eq_of_ne_stuck C1 t1 s1 r1 hC1NotStuck hT1NotStuck
      hS1NotStuck hR1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM C1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1) =
        SmtTerm.eq
          (SmtTerm.ite (__eo_to_smt C1) (__eo_to_smt t1) (__eo_to_smt s1))
          (__eo_to_smt r1) by rfl]
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite C1)
          (Term.Apply (Term.Apply Term.eq t1) r1))
          (Term.Apply (Term.Apply Term.eq s1) r1)) =
        SmtTerm.ite (__eo_to_smt C1)
          (SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt r1))
          (SmtTerm.eq (__eo_to_smt s1) (__eo_to_smt r1)) by rfl]
    simp only [smtx_eval_eq_term_eq, smtx_eval_ite_term_eq, hEvalC1]
    cases bc
    · simpa [__smtx_model_eval_ite] using
        RuleProofs.smt_value_rel_refl
          (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt s1))
            (__smtx_model_eval M (__eo_to_smt r1)))
    · simpa [__smtx_model_eval_ite] using
        RuleProofs.smt_value_rel_refl
          (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t1))
            (__smtx_model_eval M (__eo_to_smt r1)))

public theorem cmd_step_eq_ite_lift_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_ite_lift args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.eq_ite_lift args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_ite_lift args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.eq_ite_lift args premises ≠ Term.Stuck :=
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          have hATransPair :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                  RuleProofs.eo_has_smt_translation a3 ∧
                                    RuleProofs.eo_has_smt_translation a4 ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                            hATransPair.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                            hATransPair.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                            hATransPair.2.2.1
                          have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                            hATransPair.2.2.2.1
                          change __eo_typeof (__eo_prog_eq_ite_lift a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_eq_ite_lift a1 a2 a3 a4) true
                            exact facts___eo_prog_eq_ite_lift_impl M hM a1 a2 a3 a4
                              hA1Trans hA2Trans hA3Trans hA4Trans hResultTy
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_eq_ite_lift_impl a1 a2 a3 a4
                                hA1Trans hA2Trans hA3Trans hA4Trans hResultTy)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
