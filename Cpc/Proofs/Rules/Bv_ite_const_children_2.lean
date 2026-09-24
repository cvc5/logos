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
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_bv_ite_const_children_2_eq_of_ne_stuck (c1 : Term) :
    c1 ≠ Term.Stuck ->
    __eo_prog_bv_ite_const_children_2 c1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) c1 := by
  intro hC1
  cases c1 <;> simp [__eo_prog_bv_ite_const_children_2] at hC1 ⊢

private theorem typeof_bvite_const_children_not_stuck_implies_cond
    (cTy : Term) :
    __eo_typeof_bvite cTy
        (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) ≠ Term.Stuck ->
    cTy = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  intro hNotStuck
  by_cases hCTy : cTy = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  · exact hCTy
  · exfalso
    apply hNotStuck
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
    · have hOneTy :
          __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)) =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        native_decide
      have hZeroTy :
          __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)) =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        native_decide
      rw [hOneTy, hZeroTy]
      simp [__eo_typeof_bvite, hn]

private theorem typeof_arg_of_prog_bv_ite_const_children_2_bool (c1 : Term) :
    __eo_typeof (__eo_prog_bv_ite_const_children_2 c1) = Term.Bool ->
    __eo_typeof c1 = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  intro hTy
  by_cases hC1 : c1 = Term.Stuck
  · subst c1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bv_ite_const_children_2_eq_of_ne_stuck c1 hC1] at hTy
    change __eo_typeof_eq
        (__eo_typeof_bvite (__eo_typeof c1)
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))))
        (__eo_typeof c1) = Term.Bool at hTy
    have hLeftNN :
        __eo_typeof_bvite (__eo_typeof c1)
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) ≠
          Term.Stuck :=
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof_bvite (__eo_typeof c1)
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))))
        (__eo_typeof c1) hTy).1
    exact typeof_bvite_const_children_not_stuck_implies_cond (__eo_typeof c1) hLeftNN

private theorem smt_typeof_binary_one_one :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    native_decide
  exact TranslationProofs.smtx_typeof_binary_of_non_none 1 1 hNN

private theorem smt_typeof_bv_one_one :
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1))) =
      SmtType.BitVec 1 := by
  native_decide

private theorem smt_typeof_bv_zero_one :
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) =
      SmtType.BitVec 1 := by
  native_decide

private theorem smt_eval_bv_one_one (M : SmtModel) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1))) =
      SmtValue.Binary 1 1 := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 1)) =
    SmtValue.Binary 1 1
  simp [native_ite, SmtEval.native_zleq]
  native_decide

private theorem smt_eval_binary_one_one (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.Binary 1 1) =
      SmtValue.Binary 1 1 := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smt_eval_bv_zero_one (M : SmtModel) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) =
      SmtValue.Binary 1 0 := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)) =
    SmtValue.Binary 1 0
  simp [native_ite, SmtEval.native_zleq]
  native_decide

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

private theorem smt_typeof_bvite_const_children_2
    (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof (__eo_prog_bv_ite_const_children_2 c1) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
      __smtx_typeof (__eo_to_smt c1) := by
  intro hC1Trans hResultTy
  have hC1Type := typeof_arg_of_prog_bv_ite_const_children_2_bool c1 hResultTy
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hCondTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hC1SmtTy,
      smt_typeof_binary_one_one, native_Teq, native_ite]
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
    __smtx_typeof (__eo_to_smt c1)
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hCondTy, hC1SmtTy, smt_typeof_bv_one_one,
    smt_typeof_bv_zero_one, native_Teq, native_ite]

private theorem typed___eo_prog_bv_ite_const_children_2_impl (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof (__eo_prog_bv_ite_const_children_2 c1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_const_children_2 c1) := by
  intro hC1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  rw [prog_bv_ite_const_children_2_eq_of_ne_stuck c1 hC1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0))) c1
    (smt_typeof_bvite_const_children_2 c1 hC1Trans hResultTy)
    (by
      rw [smt_typeof_bvite_const_children_2 c1 hC1Trans hResultTy]
      exact hC1Trans)

private theorem eval_bvite_const_children_2
    (M : SmtModel) (hM : model_wf M) (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof (__eo_prog_bv_ite_const_children_2 c1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
      __smtx_model_eval M (__eo_to_smt c1) := by
  intro hC1Trans hResultTy
  have hC1Type := typeof_arg_of_prog_bv_ite_const_children_2_bool c1 hResultTy
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.BitVec 1 := by
    simpa [hC1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hC1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalC⟩
  have hPayloadCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 1)) = true := by
    exact bitvec_payload_canonical (by simpa [hEvalC, native_nat_to_int] using hEvalTy)
  have hWidth : native_zleq 0 1 = true := by
    native_decide
  have hRange := bitvec_payload_range_of_canonical hWidth hPayloadCanon
  have hPayloadCases : payload = 0 ∨ payload = 1 := by
    have hLtTwo : payload < 2 := by
      simpa [native_int_pow2, native_zexp_total] using hRange.2
    have hLeOne : payload ≤ 1 := Int.le_of_lt_add_one hLtTwo
    rcases Int.lt_or_eq_of_le hRange.1 with hPos | hZero
    · have hGeOne : 1 ≤ payload := (Int.add_one_le_iff).mpr hPos
      exact Or.inr (Int.le_antisymm hLeOne hGeOne)
    · exact Or.inl hZero.symm
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))) =
    __smtx_model_eval M (__eo_to_smt c1)
  rw [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq, hEvalC,
    smt_eval_binary_one_one M, smt_eval_bv_one_one M, smt_eval_bv_zero_one M]
  have hNatOne : native_nat_to_int 1 = 1 := by
    native_decide
  rcases hPayloadCases with hPayload | hPayload <;> subst payload <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_ite, native_veq, hNatOne]

private theorem facts___eo_prog_bv_ite_const_children_2_impl
    (M : SmtModel) (hM : model_wf M) (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof (__eo_prog_bv_ite_const_children_2 c1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ite_const_children_2 c1) true := by
  intro hC1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_const_children_2 c1) :=
    typed___eo_prog_bv_ite_const_children_2_impl c1 hC1Trans hResultTy
  rw [prog_bv_ite_const_children_2_eq_of_ne_stuck c1 hC1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_ite_const_children_2_eq_of_ne_stuck c1 hC1NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c1)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)))))
      (__smtx_model_eval M (__eo_to_smt c1))
    rw [eval_bvite_const_children_2 M hM c1 hC1Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_ite_const_children_2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_const_children_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ite_const_children_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_const_children_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ite_const_children_2 args premises ≠ Term.Stuck :=
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              change __eo_typeof (__eo_prog_bv_ite_const_children_2 a1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bv_ite_const_children_2 a1) true
                exact facts___eo_prog_bv_ite_const_children_2_impl M hM a1
                  hA1Trans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bv_ite_const_children_2_impl a1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
