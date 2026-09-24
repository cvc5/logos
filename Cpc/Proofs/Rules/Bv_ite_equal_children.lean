module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_bv_ite_equal_children_eq_of_ne_stuck (c1 x1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    __eo_prog_bv_ite_equal_children c1 x1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1) x1) x1)) x1 := by
  intro hC1 hX1
  cases c1 <;> cases x1 <;> simp [__eo_prog_bv_ite_equal_children] at hC1 hX1 ⊢

private theorem typeof_bvite_same_not_stuck_implies_args (cTy xTy : Term) :
    __eo_typeof_bvite cTy xTy xTy ≠ Term.Stuck ->
    cTy = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      xTy ≠ Term.Stuck := by
  intro hNotStuck
  have hXTyNN : xTy ≠ Term.Stuck := by
    intro hXTy
    subst xTy
    exact hNotStuck rfl
  have hCTy :
      cTy = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    by_cases hCTy : cTy = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
    · exact hCTy
    · exfalso
      apply hNotStuck
      cases xTy <;> try rfl
      all_goals
        cases cTy <;> try rfl
        rename_i f w
        cases f <;> try rfl
        rename_i op
        cases op <;> try rfl
        cases w <;> try rfl
        rename_i n
        by_cases hn : n = 1
        · subst n
          exact False.elim (hCTy rfl)
        · simp [__eo_typeof_bvite, __eo_requires, __eo_eq, native_ite,
            native_teq, native_not, hn]
  exact ⟨hCTy, hXTyNN⟩

private theorem typeof_args_of_prog_bv_ite_equal_children_bool (c1 x1 : Term) :
    __eo_typeof (__eo_prog_bv_ite_equal_children c1 x1) = Term.Bool ->
    __eo_typeof c1 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      __eo_typeof x1 ≠ Term.Stuck := by
  intro hTy
  by_cases hC1 : c1 = Term.Stuck
  · subst c1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hX1 : x1 = Term.Stuck
    · subst x1
      cases c1 <;> simp [__eo_prog_bv_ite_equal_children] at hC1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_ite_equal_children_eq_of_ne_stuck c1 x1 hC1 hX1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof x1))
          (__eo_typeof x1) =
        Term.Bool at hTy
      have hLeftNN :
          __eo_typeof_bvite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof x1) ≠
            Term.Stuck :=
        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
          (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof x1) (__eo_typeof x1))
          (__eo_typeof x1) hTy).1
      exact typeof_bvite_same_not_stuck_implies_args
        (__eo_typeof c1) (__eo_typeof x1) hLeftNN

private theorem smt_typeof_binary_one_one :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    native_decide
  exact TranslationProofs.smtx_typeof_binary_of_non_none 1 1 hNN

private theorem smt_typeof_c1_bitvec_one
    (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof c1 = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ->
    __smtx_typeof (__eo_to_smt c1) = SmtType.BitVec 1 := by
  intro hC1Trans hC1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt c1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) (__eo_to_smt c1) rfl
      hC1Trans hC1Type
  simpa [__eo_to_smt_type, SmtEval.native_zleq, native_int_to_nat, native_ite] using hSmtType

private theorem smt_typeof_bvite_same
    (c1 x1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_ite_equal_children c1 x1) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1) x1) x1)) =
      __smtx_typeof (__eo_to_smt x1) := by
  intro hC1Trans hX1Trans hResultTy
  rcases typeof_args_of_prog_bv_ite_equal_children_bool c1 x1 hResultTy with
    ⟨hC1Type, _hX1TyNN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hCondTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hC1SmtTy,
      smt_typeof_binary_one_one, native_Teq, native_ite]
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt x1) (__eo_to_smt x1)) =
    __smtx_typeof (__eo_to_smt x1)
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hCondTy, native_Teq, native_ite]

private theorem typed___eo_prog_bv_ite_equal_children_impl (c1 x1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_ite_equal_children c1 x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_equal_children c1 x1) := by
  intro hC1Trans hX1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rw [prog_bv_ite_equal_children_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1) x1) x1) x1
    (smt_typeof_bvite_same c1 x1 hC1Trans hX1Trans hResultTy)
    (by
      rw [smt_typeof_bvite_same c1 x1 hC1Trans hX1Trans hResultTy]
      exact hX1Trans)

private theorem smtx_model_eval_eq_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

private theorem smtx_model_eval_ite_same_of_eq_cond
    (v1 v2 x : SmtValue) :
    __smtx_model_eval_ite (__smtx_model_eval_eq v1 v2) x x = x := by
  rcases smtx_model_eval_eq_boolean v1 v2 with ⟨b, hb⟩
  cases b <;> simp [hb, __smtx_model_eval_ite]

private theorem eval_bvite_same
    (M : SmtModel) (c1 x1 : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1) x1) x1)) =
      __smtx_model_eval M (__eo_to_smt x1) := by
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt x1) (__eo_to_smt x1)) =
    __smtx_model_eval M (__eo_to_smt x1)
  rw [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq]
  exact smtx_model_eval_ite_same_of_eq_cond
    (__smtx_model_eval M (__eo_to_smt c1))
    (__smtx_model_eval M (SmtTerm.Binary 1 1))
    (__smtx_model_eval M (__eo_to_smt x1))

private theorem facts___eo_prog_bv_ite_equal_children_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_ite_equal_children c1 x1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ite_equal_children c1 x1) true := by
  intro hC1Trans hX1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_equal_children c1 x1) :=
    typed___eo_prog_bv_ite_equal_children_impl c1 x1 hC1Trans hX1Trans hResultTy
  rw [prog_bv_ite_equal_children_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_ite_equal_children_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
      using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1) x1) x1)))
      (__smtx_model_eval M (__eo_to_smt x1))
    rw [eval_bvite_same M c1 x1]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_ite_equal_children_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_children args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ite_equal_children args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_children args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ite_equal_children args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_bv_ite_equal_children a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_ite_equal_children a1 a2) true
                    exact facts___eo_prog_bv_ite_equal_children_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_ite_equal_children_impl a1 a2 hA1Trans
                        hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
