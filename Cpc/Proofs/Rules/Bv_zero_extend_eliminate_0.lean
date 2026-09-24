module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_bv_zero_extend_eliminate_0_eq_of_ne_stuck (x1 : Term) :
    x1 ≠ Term.Stuck ->
    __eo_prog_bv_zero_extend_eliminate_0 x1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)) x1)) x1 := by
  intro hX1
  cases x1 <;> simp [__eo_prog_bv_zero_extend_eliminate_0] at hX1 ⊢

private theorem typeof_arg_of_prog_bv_zero_extend_eliminate_0_bool (x1 : Term) :
    __eo_typeof (__eo_prog_bv_zero_extend_eliminate_0 x1) = Term.Bool ->
    ∃ w, __eo_typeof x1 =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bv_zero_extend_eliminate_0_eq_of_ne_stuck x1 hX1] at hTy
    change __eo_typeof_eq
        (__eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral 0)
          (__eo_typeof x1))
        (__eo_typeof x1) = Term.Bool at hTy
    cases hT : __eo_typeof x1 with
    | Apply f w =>
        cases f with
        | UOp op =>
            cases op <;>
              simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
                __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
                native_teq, native_not, hT] at hTy ⊢
            · cases w <;>
                simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
                  __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
                  native_teq, native_not, hT] at hTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
              __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
              native_teq, native_not, hT] at hTy
    | _ =>
        simp [__eo_typeof_eq, __eo_typeof_zero_extend, __eo_requires,
          __eo_gt, __eo_eq, __eo_add, __eo_mk_apply, native_ite,
          native_teq, native_not, hT] at hTy

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 : Term) (w : native_Int) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    native_zleq 0 w = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat w) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
      (__eo_to_smt x1) rfl hX1Trans hX1Type
  cases hNonneg : native_zleq 0 w <;>
    simp [__eo_to_smt_type, hNonneg] at hSmtType
  · exact False.elim (hX1Trans hSmtType)
  · exact ⟨rfl, hSmtType⟩

private theorem smt_type_zero_extend_zero_eq
    (x1 : Term) (w : native_Int) :
    __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat w) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)) x1)) =
      __smtx_typeof (__eo_to_smt x1) := by
  intro hX1SmtTy
  have hWidthRound :
      native_int_to_nat
          (native_zplus 0 (native_nat_to_int (native_int_to_nat w))) =
        native_int_to_nat w := by
    by_cases hw : 0 ≤ w
    · have hCast : native_nat_to_int (native_int_to_nat w) = w := by
        simpa [native_int_to_nat, native_nat_to_int] using
          Int.toNat_of_nonneg hw
      simp [SmtEval.native_zplus, hCast]
    · have hwlt : w < 0 := Int.lt_of_not_ge hw
      have hWZero : native_int_to_nat w = 0 := by
        simpa [native_int_to_nat] using
          Int.toNat_eq_zero.mpr (Int.le_of_lt hwlt)
      rw [hWZero]
      simp [SmtEval.native_zplus, native_int_to_nat, native_nat_to_int]
  change __smtx_typeof (SmtTerm.zero_extend (SmtTerm.Numeral 0) (__eo_to_smt x1)) =
    __smtx_typeof (__eo_to_smt x1)
  rw [typeof_zero_extend_eq, hX1SmtTy]
  simp [__smtx_typeof_zero_extend, native_ite, SmtEval.native_zleq,
    hWidthRound]

private theorem eo_has_bool_type_zero_extend_zero_eq_self
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_extend_eliminate_0 x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)) x1)) x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_zero_extend_eliminate_0_bool x1 hResultTy with
    ⟨w, hX1Type⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨_hWNonneg, hX1SmtTy⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)) x1) x1
    (smt_type_zero_extend_zero_eq x1 w hX1SmtTy)
    (by
      rw [smt_type_zero_extend_zero_eq x1 w hX1SmtTy, hX1SmtTy]
      simp)

private theorem typed___eo_prog_bv_zero_extend_eliminate_0_impl (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_extend_eliminate_0 x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_zero_extend_eliminate_0 x1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rw [prog_bv_zero_extend_eliminate_0_eq_of_ne_stuck x1 hX1NotStuck]
  exact eo_has_bool_type_zero_extend_zero_eq_self x1 hX1Trans hResultTy

private theorem eval_zero_extend_zero_self
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_extend_eliminate_0 x1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)) x1)) =
      __smtx_model_eval M (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_zero_extend_eliminate_0_bool x1 hResultTy with
    ⟨w, hX1Type⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x1 w hX1Trans hX1Type with
    ⟨_hWNonneg, hX1SmtTy⟩
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hX1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX1⟩
  change __smtx_model_eval M
      (SmtTerm.zero_extend (SmtTerm.Numeral 0) (__eo_to_smt x1)) =
    __smtx_model_eval M (__eo_to_smt x1)
  rw [show __smtx_model_eval M
        (SmtTerm.zero_extend (SmtTerm.Numeral 0) (__eo_to_smt x1)) =
      __smtx_model_eval_zero_extend
        (__smtx_model_eval M (SmtTerm.Numeral 0))
        (__smtx_model_eval M (__eo_to_smt x1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hEvalX1]
  simp [__smtx_model_eval_zero_extend, SmtEval.native_zplus]

private theorem facts___eo_prog_bv_zero_extend_eliminate_0_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_zero_extend_eliminate_0 x1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_zero_extend_eliminate_0 x1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_zero_extend_eliminate_0 x1) :=
    typed___eo_prog_bv_zero_extend_eliminate_0_impl x1 hX1Trans hResultTy
  rw [prog_bv_zero_extend_eliminate_0_eq_of_ne_stuck x1 hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_zero_extend_eliminate_0_eq_of_ne_stuck x1 hX1NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)) x1)))
      (__smtx_model_eval M (__eo_to_smt x1))
    rw [eval_zero_extend_zero_self M hM x1 hX1Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x1))

public theorem cmd_step_bv_zero_extend_eliminate_0_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_eliminate_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_zero_extend_eliminate_0 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_eliminate_0 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_zero_extend_eliminate_0 args premises ≠ Term.Stuck :=
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
              change __eo_typeof (__eo_prog_bv_zero_extend_eliminate_0 a1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bv_zero_extend_eliminate_0 a1) true
                exact facts___eo_prog_bv_zero_extend_eliminate_0_impl M hM a1
                  hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bv_zero_extend_eliminate_0_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
