module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_ite_neg_branch_self_eq_of_ne_stuck
    (c1 x1 y1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_ite_neg_branch c1 x1 y1
      (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not y1)) x1)) =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))
        (Term.Apply (Term.Apply Term.eq c1) x1) := by
  intro hC1 hX1 hY1
  simp [__eo_prog_ite_neg_branch, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, native_and, SmtEval.native_not,
    SmtEval.native_and]

private theorem shape_of_prog_ite_neg_branch_not_stuck
    (c1 x1 y1 p : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p) ≠ Term.Stuck ->
    p = Term.Apply (Term.Apply Term.eq (Term.Apply Term.not y1)) x1 := by
  intro hC1 hX1 hY1 hProg
  cases p with
  | Apply f pX =>
      cases f with
      | Apply g pNot =>
          cases g with
          | UOp op =>
              cases op <;> try (simp [__eo_prog_ite_neg_branch] at hProg)
              case eq =>
                cases pNot with
                | Apply nOp pY =>
                    cases nOp with
                    | UOp opN =>
                        cases opN <;> try (simp at hProg)
                        case not =>
                          rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                              y1 x1 pY pX
                              (Term.Apply (Term.Apply Term.eq
                                (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))
                                (Term.Apply (Term.Apply Term.eq c1) x1)) hProg with
                            ⟨hPY, hPX⟩
                          subst pY
                          subst pX
                          rfl
                    | _ =>
                        simp at hProg
                | _ =>
                    simp at hProg
          | _ =>
              simp [__eo_prog_ite_neg_branch] at hProg
      | _ =>
          simp [__eo_prog_ite_neg_branch] at hProg
  | _ =>
      simp [__eo_prog_ite_neg_branch] at hProg

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem eo_typeof_eq_bool_of_ne_stuck (A B : Term) :
    __eo_typeof_eq A B ≠ Term.Stuck ->
    __eo_typeof_eq A B = Term.Bool := by
  intro hNe
  exact RuleProofs.eo_typeof_eq_eq_bool_of_ne_stuck A B hNe

private theorem eo_typeof_ite_bool_args_of_bool (C X Y : Term) :
    __eo_typeof_ite C X Y = Term.Bool ->
      C = Term.Bool ∧ X = Term.Bool ∧ Y = Term.Bool := by
  intro hTy
  exact RuleProofs.eo_typeof_ite_eq_nonstuck_args C X Y Term.Bool hTy
    (by decide)

private theorem bool_arg_types_of_ite_neg_branch_body_bool
    (c1 x1 y1 : Term) :
    __eo_typeof
        (Term.Apply (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))
          (Term.Apply (Term.Apply Term.eq c1) x1)) = Term.Bool ->
      __eo_typeof c1 = Term.Bool ∧ __eo_typeof x1 = Term.Bool ∧
        __eo_typeof y1 = Term.Bool := by
  intro hTy
  change __eo_typeof_eq
    (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1))
    (__eo_typeof_eq (__eo_typeof c1) (__eo_typeof x1)) = Term.Bool at hTy
  rcases eo_typeof_eq_bool_same
      (__eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1))
      (__eo_typeof_eq (__eo_typeof c1) (__eo_typeof x1)) hTy with
    ⟨hSides, hLeftNe⟩
  have hRightNe :
      __eo_typeof_eq (__eo_typeof c1) (__eo_typeof x1) ≠ Term.Stuck := by
    rw [← hSides]
    exact hLeftNe
  have hRightBool :
      __eo_typeof_eq (__eo_typeof c1) (__eo_typeof x1) = Term.Bool :=
    eo_typeof_eq_bool_of_ne_stuck (__eo_typeof c1) (__eo_typeof x1) hRightNe
  have hLeftBool :
      __eo_typeof_ite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1) =
        Term.Bool := by
    rw [hSides, hRightBool]
  exact eo_typeof_ite_bool_args_of_bool
    (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof y1) hLeftBool

private theorem typed___eo_prog_ite_neg_branch_impl
    (c1 x1 y1 p1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p1)) = Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p1)) := by
  intro hC1Trans hX1Trans hY1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProg :
      __eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  have hShape :
      p1 = Term.Apply (Term.Apply Term.eq (Term.Apply Term.not y1)) x1 :=
    shape_of_prog_ite_neg_branch_not_stuck c1 x1 y1 p1
      hC1NotStuck hX1NotStuck hY1NotStuck hProg
  subst p1
  rw [prog_ite_neg_branch_self_eq_of_ne_stuck c1 x1 y1 hC1NotStuck
    hX1NotStuck hY1NotStuck] at hResultTy ⊢
  rcases bool_arg_types_of_ite_neg_branch_body_bool c1 x1 y1 hResultTy with
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
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)
    (Term.Apply (Term.Apply Term.eq c1) x1)
    (CnfSupport.eo_has_bool_type_ite_of_bool_args c1 x1 y1
      hC1Bool hX1Bool hY1Bool)
    (CnfSupport.eo_has_bool_type_eq_of_bool_args c1 x1 hC1Bool hX1Bool)

private theorem facts___eo_prog_ite_neg_branch_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 y1 p1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  eo_interprets M p1 true ->
  __eo_typeof (__eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p1)) = Term.Bool ->
  eo_interprets M (__eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p1)) true := by
  intro hC1Trans hX1Trans hY1Trans hP1True hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProg :
      __eo_prog_ite_neg_branch c1 x1 y1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  have hShape :
      p1 = Term.Apply (Term.Apply Term.eq (Term.Apply Term.not y1)) x1 :=
    shape_of_prog_ite_neg_branch_not_stuck c1 x1 y1 p1
      hC1NotStuck hX1NotStuck hY1NotStuck hProg
  subst p1
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_ite_neg_branch c1 x1 y1
          (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not y1)) x1))) :=
    typed___eo_prog_ite_neg_branch_impl c1 x1 y1
      (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not y1)) x1)
      hC1Trans hX1Trans hY1Trans hResultTy
  have hResultTyBody :
      __eo_typeof
        (Term.Apply (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))
          (Term.Apply (Term.Apply Term.eq c1) x1)) = Term.Bool := by
    simpa [prog_ite_neg_branch_self_eq_of_ne_stuck c1 x1 y1 hC1NotStuck
      hX1NotStuck hY1NotStuck] using hResultTy
  rcases bool_arg_types_of_ite_neg_branch_body_bool c1 x1 y1 hResultTyBody with
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
  rw [prog_ite_neg_branch_self_eq_of_ne_stuck c1 x1 y1 hC1NotStuck
    hX1NotStuck hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_ite_neg_branch_self_eq_of_ne_stuck c1 x1 y1 hC1NotStuck
      hX1NotStuck hY1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM c1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x1 hX1Bool with
      ⟨bx, hEvalX1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM y1 hY1Bool with
      ⟨bY, hEvalY1⟩
    have hPremRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.not y1)))
          (__smtx_model_eval M (__eo_to_smt x1)) :=
      RuleProofs.eo_interprets_eq_rel M (Term.Apply Term.not y1) x1 hP1True
    rw [show __eo_to_smt (Term.Apply Term.not y1) =
        SmtTerm.not (__eo_to_smt y1) by rfl,
      smtx_eval_not_term_eq, hEvalY1, hEvalX1] at hPremRel
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1) =
        SmtTerm.ite (__eo_to_smt c1) (__eo_to_smt x1) (__eo_to_smt y1) by
        rfl]
    rw [show __eo_to_smt (Term.Apply (Term.Apply Term.eq c1) x1) =
        SmtTerm.eq (__eo_to_smt c1) (__eo_to_smt x1) by rfl]
    simp only [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq, hEvalC1, hEvalX1,
      hEvalY1]
    cases bc <;> cases bx <;> cases bY <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
        __smtx_model_eval_ite, __smtx_model_eval_not, native_veq,
        SmtEval.native_not] at hPremRel ⊢

public theorem cmd_step_ite_neg_branch_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_neg_branch args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_neg_branch args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_neg_branch args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_neg_branch args premises ≠ Term.Stuck :=
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
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n1 premises =>
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
                          let P := __eo_state_proven_nth s n1
                          change __eo_typeof (__eo_prog_ite_neg_branch a1 a2 a3
                            (Proof.pf P)) = Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            change eo_interprets M
                              (__eo_prog_ite_neg_branch a1 a2 a3 (Proof.pf P)) true
                            exact facts___eo_prog_ite_neg_branch_impl M hM a1 a2 a3 P
                              hA1Trans hA2Trans hA3Trans
                              (hTrue P (by simp [P, premiseTermList]))
                              hResultTy
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_ite_neg_branch_impl a1 a2 a3 P
                                hA1Trans hA2Trans hA3Trans hResultTy)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
