module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_bv_sle_self_eq_of_ne_stuck (x1 : Term) :
    x1 ≠ Term.Stuck ->
    __eo_prog_bv_sle_self x1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1))
        (Term.Boolean true) := by
  intro hX1
  cases x1 <;> simp [__eo_prog_bv_sle_self] at hX1 ⊢

private theorem typeof_arg_of_prog_bv_sle_self_bool (x1 : Term) :
    __eo_typeof (__eo_prog_bv_sle_self x1) = Term.Bool ->
    ∃ w, __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧ w ≠ Term.Stuck := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bv_sle_self_eq_of_ne_stuck x1 hX1] at hTy
    change __eo_typeof_eq (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1))
      Term.Bool = Term.Bool at hTy
    change __eo_typeof_eq (__eo_typeof_bvult (__eo_typeof x1) (__eo_typeof x1))
      Term.Bool = Term.Bool at hTy
    cases hT : __eo_typeof x1 with
    | Apply f w =>
        cases f with
        | UOp op =>
            cases op <;>
              simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_requires, __eo_eq,
                native_ite, native_teq, native_not, hT] at hTy ⊢
            · intro hW
              subst w
              simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_requires, __eo_eq,
                native_ite, native_teq, native_not, hT] at hTy
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_requires, __eo_eq,
              native_ite, native_teq, native_not, hT] at hTy
    | _ =>
        simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_requires, __eo_eq,
          native_ite, native_teq, native_not, hT] at hTy

private theorem smt_bitvec_type_of_eo_bitvec_type
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec n := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hX1Trans hSmtType)
    · exact ⟨native_int_to_nat n, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

private theorem eo_has_bool_type_bvsle_self
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sle_self x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_sle_self_bool x1 hResultTy with ⟨w, hX1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type x1 w hX1Trans hX1Type with ⟨n, hSmtTy⟩
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.bvsle (__eo_to_smt x1) (__eo_to_smt x1)) = SmtType.Bool
  rw [__smtx_typeof.eq_61]
  simp [__smtx_typeof_bv_op_2_ret, hSmtTy, native_nateq, native_ite]

private theorem typed___eo_prog_bv_sle_self_impl (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sle_self x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_sle_self x1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hInnerBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1) :=
    eo_has_bool_type_bvsle_self x1 hX1Trans hResultTy
  rw [prog_bv_sle_self_eq_of_ne_stuck x1 hX1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1) (Term.Boolean true)
    (hInnerBool.trans RuleProofs.eo_has_bool_type_true.symm)
    (by
      rw [hInnerBool]
      decide)

private theorem eval_bvsle_self_true
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sle_self x1) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1)) =
      SmtValue.Boolean true := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_sle_self_bool x1 hResultTy with ⟨w, hX1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type x1 w hX1Trans hX1Type with ⟨n, hSmtTy⟩
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec n := by
    simpa [hSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨k, hEvalX1⟩
  change __smtx_model_eval M (SmtTerm.bvsle (__eo_to_smt x1) (__eo_to_smt x1)) =
    SmtValue.Boolean true
  rw [__smtx_model_eval.eq_61, hEvalX1]
  simp [__smtx_model_eval_bvsle, __smtx_model_eval_bvsge,
    __smtx_model_eval_bvsgt, __smtx_model_eval_bvugt,
    __smtx_model_eval_eq, __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_extract, __smtx_model_eval__,
    native_zlt, native_veq, native_not, native_and, native_or]

private theorem facts___eo_prog_bv_sle_self_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_sle_self x1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_sle_self x1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_sle_self x1) :=
    typed___eo_prog_bv_sle_self_impl x1 hX1Trans hResultTy
  rw [prog_bv_sle_self_eq_of_ne_stuck x1 hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_sle_self_eq_of_ne_stuck x1 hX1NotStuck] using hProgBool
  · have hTrueEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
          SmtValue.Boolean true := by
      change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
      rw [__smtx_model_eval.eq_1]
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x1) x1)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true)))
    rw [eval_bvsle_self_true M hM x1 hX1Trans hResultTy, hTrueEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

public theorem cmd_step_bv_sle_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sle_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_sle_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sle_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_sle_self args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              change __eo_typeof (__eo_prog_bv_sle_self a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bv_sle_self a1) true
                exact facts___eo_prog_bv_sle_self_impl M hM a1 hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bv_sle_self_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
