module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_not_arg_bool_of_ne_stuck (A : Term) :
    __eo_typeof_not A ≠ Term.Stuck -> A = Term.Bool := by
  intro h
  cases A <;> simp [__eo_typeof_not] at h ⊢

private theorem prog_distinct_binary_elim_type_not_stuck
    (t1 s1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hResultTy : __eo_typeof (__eo_prog_distinct_binary_elim t1 s1) = Term.Bool) :
    __eo_typeof t1 ≠ Term.Stuck := by
  have hProg : __eo_prog_distinct_binary_elim t1 s1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  intro hTType
  have hStuck : __eo_prog_distinct_binary_elim t1 s1 = Term.Stuck := by
    by_cases hT : t1 = Term.Stuck
    · contradiction
    · by_cases hS : s1 = Term.Stuck
      · contradiction
      · simp [__eo_prog_distinct_binary_elim, __eo_mk_apply, __eo_nil, hTType]
  exact hProg hStuck

private theorem prog_distinct_binary_elim_eq
    (t1 s1 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck)
    (hS1NotStuck : s1 ≠ Term.Stuck)
    (hT1TypeNotStuck : __eo_typeof t1 ≠ Term.Stuck) :
    __eo_prog_distinct_binary_elim t1 s1 =
      Term.Apply
        (Term.Apply Term.eq
          (Term.Apply Term.distinct
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) t1)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s1)
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof t1))))))
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) s1)) := by
  by_cases hT : t1 = Term.Stuck
  · contradiction
  · by_cases hS : s1 = Term.Stuck
    · contradiction
    · simp [__eo_prog_distinct_binary_elim, __eo_mk_apply, __eo_nil,
        __eo_nil__at__at_TypedList_cons]

private theorem operand_types_of_prog_distinct_binary_elim_bool
    (t1 s1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hResultTy : __eo_typeof (__eo_prog_distinct_binary_elim t1 s1) = Term.Bool) :
    __eo_typeof t1 = __eo_typeof s1 ∧ __eo_typeof t1 ≠ Term.Stuck := by
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hT1TypeNotStuck :
      __eo_typeof t1 ≠ Term.Stuck :=
    prog_distinct_binary_elim_type_not_stuck t1 s1 hT1Trans hS1Trans hResultTy
  rw [prog_distinct_binary_elim_eq t1 s1 hT1NotStuck hS1NotStuck hT1TypeNotStuck]
    at hResultTy
  let nil := Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof t1)
  let tail :=
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s1) nil
  let xs :=
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) t1) tail
  let distinctTerm := Term.Apply Term.distinct xs
  let eqTerm := Term.Apply (Term.Apply Term.eq t1) s1
  let notEq := Term.Apply Term.not eqTerm
  change __eo_typeof_eq (__eo_typeof distinctTerm) (__eo_typeof notEq) =
    Term.Bool at hResultTy
  have hRightNotStuck :
      __eo_typeof notEq ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof distinctTerm) (__eo_typeof notEq) hResultTy).2
  change __eo_typeof_not (__eo_typeof_eq (__eo_typeof t1) (__eo_typeof s1)) ≠
    Term.Stuck at hRightNotStuck
  have hEqTyBool :
      __eo_typeof_eq (__eo_typeof t1) (__eo_typeof s1) = Term.Bool :=
    eo_typeof_not_arg_bool_of_ne_stuck
      (__eo_typeof_eq (__eo_typeof t1) (__eo_typeof s1)) hRightNotStuck
  exact ⟨RuleProofs.eo_typeof_eq_bool_operands_eq
    (__eo_typeof t1) (__eo_typeof s1) hEqTyBool, hT1TypeNotStuck⟩

private theorem smtx_model_eval_eq_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

private theorem eo_to_smt_distinct_eq_of_elem_type_ne_none (xs : Term) :
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
    __eo_to_smt (Term.Apply Term.distinct xs) = __eo_to_smt_distinct xs := by
  intro hElemNN
  change native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
    __eo_to_smt_distinct xs
  have hGuard :
      native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None = false := by
    cases hElem : __eo_to_smt_typed_list_elem_type xs <;>
      simp [hElem, native_Teq] at hElemNN ⊢
    all_goals rfl
  rw [hGuard]
  simp [native_ite]

private theorem typed___eo_prog_distinct_binary_elim_impl
    (t1 s1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  __smtx_type_wf (__smtx_typeof (__eo_to_smt t1)) = true ->
  __eo_typeof (__eo_prog_distinct_binary_elim t1 s1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_distinct_binary_elim t1 s1) := by
  intro hT1Trans hS1Trans hT1SmtWf hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  rcases operand_types_of_prog_distinct_binary_elim_bool
      t1 s1 hT1Trans hS1Trans hResultTy with
    ⟨hTypes, hT1TypeNotStuck⟩
  let nil := Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof t1)
  let tail :=
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s1) nil
  let xs :=
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) t1) tail
  let distinctTerm := Term.Apply Term.distinct xs
  let eqTerm := Term.Apply (Term.Apply Term.eq t1) s1
  let notEq := Term.Apply Term.not eqTerm
  have hT1SmtTy :
      __smtx_typeof (__eo_to_smt t1) = __eo_to_smt_type (__eo_typeof t1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 (__eo_typeof t1) (__eo_to_smt t1) rfl hT1Trans rfl
  have hS1SmtTy :
      __smtx_typeof (__eo_to_smt s1) = __eo_to_smt_type (__eo_typeof s1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s1 (__eo_typeof s1) (__eo_to_smt s1) rfl hS1Trans rfl
  have hSameSmt :
      __smtx_typeof (__eo_to_smt t1) = __smtx_typeof (__eo_to_smt s1) := by
    rw [hT1SmtTy, hS1SmtTy, hTypes]
  have hEqBool : RuleProofs.eo_has_bool_type eqTerm :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t1 s1 hSameSmt hT1Trans
  have hNotEqBool : RuleProofs.eo_has_bool_type notEq :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg eqTerm hEqBool
  have hNotEqSmtTy :
      __smtx_typeof
          (SmtTerm.not (SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt s1))) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, notEq, eqTerm, __eo_to_smt, __smtx_typeof] using hNotEqBool
  have hEqSmtTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt s1)) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eqTerm, __eo_to_smt, __smtx_typeof] using hEqBool
  have hEqSmtTy' :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt t1))
          (__smtx_typeof (__eo_to_smt s1)) = SmtType.Bool := by
    rw [← typeof_eq_eq]
    exact hEqSmtTy
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    have hTypesSymm := hTypes.symm
    have hTypeWf :
        __smtx_type_wf (__eo_to_smt_type (__eo_typeof t1)) = true := by
      rw [← hT1SmtTy]
      exact hT1SmtWf
    have hTypeNN :
        __eo_to_smt_type (__eo_typeof t1) ≠ SmtType.None := by
      rw [← hT1SmtTy]
      exact hT1Trans
    simp [xs, tail, nil, hTypesSymm, hT1SmtTy, hS1SmtTy,
      __eo_to_smt_typed_list_elem_type, hTypeNN, hTypeWf, native_ite,
      native_Teq]
  have hDistinctBool : RuleProofs.eo_has_bool_type distinctTerm := by
    unfold RuleProofs.eo_has_bool_type
    rw [show __eo_to_smt distinctTerm = __eo_to_smt_distinct xs by
      simp [distinctTerm, eo_to_smt_distinct_eq_of_elem_type_ne_none, hElemNN]]
    change
      __smtx_typeof
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.not (SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt s1)))
            (SmtTerm.Boolean true))
          (SmtTerm.and (SmtTerm.Boolean true) (SmtTerm.Boolean true))) =
        SmtType.Bool
    have hTrueTy :
        __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool := rfl
    simp only [typeof_and_eq, hNotEqSmtTy, hTrueTy, native_Teq, native_ite]
    simp
  rw [prog_distinct_binary_elim_eq t1 s1 hT1NotStuck hS1NotStuck hT1TypeNotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type distinctTerm notEq
    (by rw [hDistinctBool, hNotEqBool])
    (by rw [hDistinctBool]; decide)

private theorem facts___eo_prog_distinct_binary_elim_impl
    (M : SmtModel) (hM : model_wf M) (t1 s1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  __smtx_type_wf (__smtx_typeof (__eo_to_smt t1)) = true ->
  __eo_typeof (__eo_prog_distinct_binary_elim t1 s1) = Term.Bool ->
  eo_interprets M (__eo_prog_distinct_binary_elim t1 s1) true := by
  intro hT1Trans hS1Trans hT1SmtWf hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  rcases operand_types_of_prog_distinct_binary_elim_bool
      t1 s1 hT1Trans hS1Trans hResultTy with
    ⟨_hTypes, hT1TypeNotStuck⟩
  let nil := Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof t1)
  let tail :=
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s1) nil
  let xs :=
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) t1) tail
  let distinctTerm := Term.Apply Term.distinct xs
  let eqTerm := Term.Apply (Term.Apply Term.eq t1) s1
  let notEq := Term.Apply Term.not eqTerm
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_distinct_binary_elim t1 s1) :=
    typed___eo_prog_distinct_binary_elim_impl t1 s1 hT1Trans hS1Trans
      hT1SmtWf hResultTy
  have hT1SmtTy :
      __smtx_typeof (__eo_to_smt t1) = __eo_to_smt_type (__eo_typeof t1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 (__eo_typeof t1) (__eo_to_smt t1) rfl hT1Trans rfl
  have hS1SmtTy :
      __smtx_typeof (__eo_to_smt s1) = __eo_to_smt_type (__eo_typeof s1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s1 (__eo_typeof s1) (__eo_to_smt s1) rfl hS1Trans rfl
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    have hTypesSymm := _hTypes.symm
    have hTypeWf :
        __smtx_type_wf (__eo_to_smt_type (__eo_typeof t1)) = true := by
      rw [← hT1SmtTy]
      exact hT1SmtWf
    have hTypeNN :
        __eo_to_smt_type (__eo_typeof t1) ≠ SmtType.None := by
      rw [← hT1SmtTy]
      exact hT1Trans
    simp [xs, tail, nil, hTypesSymm, hT1SmtTy, hS1SmtTy,
      __eo_to_smt_typed_list_elem_type, hTypeNN, hTypeWf, native_ite,
      native_Teq]
  rw [prog_distinct_binary_elim_eq t1 s1 hT1NotStuck hS1NotStuck hT1TypeNotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_distinct_binary_elim_eq t1 s1 hT1NotStuck hS1NotStuck
      hT1TypeNotStuck] using hProgBool
  · rw [show __eo_to_smt distinctTerm = __eo_to_smt_distinct xs by
      simp [distinctTerm, eo_to_smt_distinct_eq_of_elem_type_ne_none, hElemNN]]
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.not (SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt s1)))
            (SmtTerm.Boolean true))
          (SmtTerm.and (SmtTerm.Boolean true) (SmtTerm.Boolean true))))
      (__smtx_model_eval M (__eo_to_smt notEq))
    rw [show __eo_to_smt notEq =
        SmtTerm.not (SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt s1)) by
      simp [notEq, eqTerm, RuleProofs.eo_to_smt_not_eq, RuleProofs.eo_to_smt_eq_eq]]
    rcases smtx_model_eval_eq_boolean
        (__smtx_model_eval M (__eo_to_smt t1))
        (__smtx_model_eval M (__eo_to_smt s1)) with
      ⟨b, hEqEval⟩
    cases b <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval,
        __smtx_model_eval_and, __smtx_model_eval_not,
        SmtEval.native_and, SmtEval.native_not, hEqEval]
    all_goals simp [__smtx_model_eval_eq]
    all_goals simp [native_veq]

public theorem cmd_step_distinct_binary_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_binary_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_binary_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_binary_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.distinct_binary_elim args premises ≠ Term.Stuck :=
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
                  have hATrans :
                      (RuleProofs.eo_has_smt_translation a1 ∧
                        __smtx_type_wf (__smtx_typeof (__eo_to_smt a1)) = true) ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOkMask,
                      argTranslationOkMasked, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hCmdTrans
                  change __eo_typeof (__eo_prog_distinct_binary_elim a1 a2) =
                    Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_distinct_binary_elim a1 a2) true
                    exact facts___eo_prog_distinct_binary_elim_impl M hM a1 a2
                      hATrans.1.1 hATrans.2.1 hATrans.1.2 hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_distinct_binary_elim_impl a1 a2
                        hATrans.1.1 hATrans.2.1 hATrans.1.2 hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
