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

private theorem prog_bv_not_idemp_eq_of_ne_stuck (x1 : Term) :
    x1 ≠ Term.Stuck ->
    __eo_prog_bv_not_idemp x1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.UOp UserOp.bvnot)
          (Term.Apply (Term.UOp UserOp.bvnot) x1))) x1 := by
  intro hX1
  cases x1 <;> simp [__eo_prog_bv_not_idemp] at hX1 ⊢

private theorem typeof_arg_of_prog_bv_not_idemp_bool (x1 : Term) :
    __eo_typeof (__eo_prog_bv_not_idemp x1) = Term.Bool ->
    ∃ w, __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bv_not_idemp_eq_of_ne_stuck x1 hX1] at hTy
    change __eo_typeof_eq
      (__eo_typeof_bvnot (__eo_typeof_bvnot (__eo_typeof x1)))
      (__eo_typeof x1) = Term.Bool at hTy
    cases hT : __eo_typeof x1 with
    | Apply f w =>
        cases f with
        | UOp op =>
            cases op <;>
              simp [__eo_typeof_eq, __eo_typeof_bvnot, __eo_requires, __eo_eq,
                native_ite, native_teq, native_not, hT] at hTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_bvnot, __eo_requires, __eo_eq,
              native_ite, native_teq, native_not, hT] at hTy
    | _ =>
        simp [__eo_typeof_eq, __eo_typeof_bvnot, __eo_requires, __eo_eq,
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

private theorem eo_has_bool_type_bvnot_bvnot_eq_self
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_not_idemp x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.UOp UserOp.bvnot)
          (Term.Apply (Term.UOp UserOp.bvnot) x1))) x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_not_idemp_bool x1 hResultTy with ⟨w, hX1Type⟩
  rcases smt_bitvec_type_of_eo_bitvec_type x1 w hX1Trans hX1Type with ⟨n, hSmtTy⟩
  have hNotTy :
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x1)) = SmtType.BitVec n := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_1, hSmtTy]
  have hDoubleTy :
      __smtx_typeof (SmtTerm.bvnot (SmtTerm.bvnot (__eo_to_smt x1))) =
        SmtType.BitVec n := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_1, hNotTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp.bvnot)
      (Term.Apply (Term.UOp UserOp.bvnot) x1)) x1
    (by
      change __smtx_typeof (SmtTerm.bvnot (SmtTerm.bvnot (__eo_to_smt x1))) =
        __smtx_typeof (__eo_to_smt x1)
      rw [hDoubleTy, hSmtTy])
    (by
      change __smtx_typeof (SmtTerm.bvnot (SmtTerm.bvnot (__eo_to_smt x1))) ≠
        SmtType.None
      rw [hDoubleTy]
      simp)

private theorem typed___eo_prog_bv_not_idemp_impl (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_not_idemp x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_not_idemp x1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rw [prog_bv_not_idemp_eq_of_ne_stuck x1 hX1NotStuck]
  exact eo_has_bool_type_bvnot_bvnot_eq_self x1 hX1Trans hResultTy

private theorem native_binary_not_eq_pow_sub_succ
    (w n : native_Int) :
    native_binary_not w n =
      native_int_pow2 w - (n + 1) := by
  simp [native_binary_not, native_zplus, native_zneg,
    Int.sub_eq_add_neg]

private theorem native_binary_not_involutive
    (w n : native_Int) :
    native_binary_not w (native_binary_not w n) = n := by
  rw [native_binary_not_eq_pow_sub_succ w (native_binary_not w n)]
  rw [native_binary_not_eq_pow_sub_succ w n]
  grind

private theorem native_binary_not_range_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    0 <= native_binary_not w n ∧
      native_binary_not w n < native_int_pow2 w := by
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hRaw := native_binary_not_eq_pow_sub_succ w n
  constructor
  · rw [hRaw]
    exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hRange.2)
  · rw [hRaw]
    exact Int.sub_lt_self _ (Int.lt_add_one_of_le hRange.1)

private theorem native_binary_not_mod_self_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    native_mod_total (native_binary_not w n) (native_int_pow2 w) =
      native_binary_not w n := by
  have hRange := native_binary_not_range_of_canonical
    (w := w) (n := n) hw0 hCanon
  simpa [native_mod_total] using
    Int.emod_eq_of_lt hRange.1 hRange.2

private theorem smtx_model_eval_bvnot_bvnot_binary_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvnot (__smtx_model_eval_bvnot (SmtValue.Binary w n)) =
      SmtValue.Binary w n := by
  have hNotMod :
      native_mod_total (native_binary_not w n) (native_int_pow2 w) =
        native_binary_not w n :=
    native_binary_not_mod_self_of_canonical (w := w) (n := n) hw0 hCanon
  have hPayloadMod :
      native_mod_total n (native_int_pow2 w) = n := by
    have hPayloadEq :
        n = native_mod_total n (native_int_pow2 w) := by
      simpa [SmtEval.native_zeq] using hCanon
    exact hPayloadEq.symm
  have hDouble : native_binary_not w (native_binary_not w n) = n :=
    native_binary_not_involutive w n
  simp [__smtx_model_eval_bvnot, hNotMod, hDouble, hPayloadMod]

private theorem eval_bvnot_bvnot_self
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_not_idemp x1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.UOp UserOp.bvnot) x1))) =
      __smtx_model_eval M (__eo_to_smt x1) := by
  intro hX1Trans hResultTy
  rcases typeof_arg_of_prog_bv_not_idemp_bool x1 hResultTy with ⟨w, hX1Type⟩
  rcases smt_bitvec_type_of_eo_bitvec_type x1 w hX1Trans hX1Type with ⟨n, hSmtTy⟩
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x1)) =
        SmtType.BitVec n := by
    simpa [hSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hX1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX1⟩
  have hWidth : native_zleq 0 (native_nat_to_int n) = true := by
    exact bitvec_width_nonneg (by simpa [hEvalX1] using hEvalTy)
  have hCanon :
      native_zeq payload
          (native_mod_total payload (native_int_pow2 (native_nat_to_int n))) =
        true := by
    exact bitvec_payload_canonical (by simpa [hEvalX1] using hEvalTy)
  change __smtx_model_eval M (SmtTerm.bvnot (SmtTerm.bvnot (__eo_to_smt x1))) =
    __smtx_model_eval M (__eo_to_smt x1)
  rw [show __smtx_model_eval M (SmtTerm.bvnot (SmtTerm.bvnot (__eo_to_smt x1))) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x1))) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [show __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x1)) =
      __smtx_model_eval_bvnot (__smtx_model_eval M (__eo_to_smt x1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hEvalX1]
  exact smtx_model_eval_bvnot_bvnot_binary_of_canonical
    (w := native_nat_to_int n) (n := payload) hWidth hCanon

private theorem facts___eo_prog_bv_not_idemp_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_bv_not_idemp x1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_not_idemp x1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_not_idemp x1) :=
    typed___eo_prog_bv_not_idemp_impl x1 hX1Trans hResultTy
  rw [prog_bv_not_idemp_eq_of_ne_stuck x1 hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_not_idemp_eq_of_ne_stuck x1 hX1NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.UOp UserOp.bvnot) x1))))
      (__smtx_model_eval M (__eo_to_smt x1))
    rw [eval_bvnot_bvnot_self M hM x1 hX1Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x1))

public theorem cmd_step_bv_not_idemp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_not_idemp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_not_idemp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_not_idemp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_not_idemp args premises ≠ Term.Stuck :=
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
              change __eo_typeof (__eo_prog_bv_not_idemp a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bv_not_idemp a1) true
                exact facts___eo_prog_bv_not_idemp_impl M hM a1 hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bv_not_idemp_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
