module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_div_total_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.div_total x) y) =
      SmtTerm.div_total (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem prog_arith_int_div_total_one_eq
    (t1 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck) :
    __eo_prog_arith_int_div_total_one t1 =
      (Term.Apply
        (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1)))
        t1) := by
  cases hTy : t1 <;> simp [__eo_prog_arith_int_div_total_one, hTy] at hT1NotStuck ⊢

private theorem typeof_arg_of_prog_arith_int_div_total_one_bool
    (t1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (h : __eo_typeof (__eo_prog_arith_int_div_total_one t1) = Term.Bool) :
    __eo_typeof t1 = Term.Int := by
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  rw [prog_arith_int_div_total_one_eq t1 hT1NotStuck] at h
  change __eo_typeof_eq (__eo_typeof (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1)))
    (__eo_typeof t1) = Term.Bool at h
  change __eo_typeof_eq (__eo_typeof_div (__eo_typeof t1) (__eo_typeof (Term.Numeral 1)))
    (__eo_typeof t1) = Term.Bool at h
  have hNumTy : __eo_typeof (Term.Numeral 1) = Term.Int := by
    native_decide
  rw [hNumTy] at h
  cases hTy : __eo_typeof t1 with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
          native_ite, native_teq, native_not, hTy] at h ⊢
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_div,
        hTy] at h

private theorem eval_numeral (M : SmtModel) (n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
  change __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
  rw [__smtx_model_eval.eq_2]

private theorem typed___eo_prog_arith_int_div_total_one_impl
    (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  __eo_typeof (__eo_prog_arith_int_div_total_one t1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_int_div_total_one t1) := by
  intro hT1Trans hResultTy
  have hT1Ty : __eo_typeof t1 = Term.Int :=
    typeof_arg_of_prog_arith_int_div_total_one_bool t1 hT1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hSmtT1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Int (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1))) =
        SmtType.Int := by
    have hNumTy : __smtx_typeof (__eo_to_smt (Term.Numeral 1)) = SmtType.Int := by
      change __smtx_typeof (SmtTerm.Numeral 1) = SmtType.Int
      rw [__smtx_typeof.eq_2]
    rw [eo_to_smt_div_total_eq]
    rw [typeof_div_total_eq]
    simp [native_ite, native_Teq, hSmtT1, hNumTy]
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1)) := by
    simp [RuleProofs.eo_has_smt_translation, hLhsTy]
  rw [prog_arith_int_div_total_one_eq t1 hT1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1)) t1
    (by rw [hLhsTy, hSmtT1]) hLhsTrans

private theorem facts___eo_prog_arith_int_div_total_one_impl
    (M : SmtModel) (hM : model_wf M) (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  __eo_typeof (__eo_prog_arith_int_div_total_one t1) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_int_div_total_one t1) true := by
  intro hT1Trans hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_arith_int_div_total_one t1) :=
    typed___eo_prog_arith_int_div_total_one_impl t1 hT1Trans hResultTy
  have hT1Ty : __eo_typeof t1 = Term.Int :=
    typeof_arg_of_prog_arith_int_div_total_one_bool t1 hT1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hProgEq := prog_arith_int_div_total_one_eq t1 hT1NotStuck
  have hProgBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1)))
          t1) := by
    simpa [hProgEq] using hProgBool
  have hSmtT1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Int (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hEvalT1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) = SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t1) SmtType.Int hSmtT1
      (by simp) type_inhabited_int
  rcases int_value_canonical hEvalT1Ty with ⟨n, hEvalT1⟩
  have hEval1 :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 1)) = SmtValue.Numeral 1 :=
    eval_numeral M 1
  have hEvalLhs :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1))) =
        SmtValue.Numeral n := by
    rw [eo_to_smt_div_total_eq]
    rw [__smtx_model_eval.eq_31]
    rw [hEvalT1, hEval1]
    simp [__smtx_model_eval_div_total]
    simp [SmtEval.native_div_total]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1)) t1
    hProgBool' <| by
      rw [hEvalLhs, hEvalT1]
      exact RuleProofs.smt_value_rel_refl (SmtValue.Numeral n)

public theorem cmd_step_arith_int_div_total_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_div_total_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_int_div_total_one args premises ≠ Term.Stuck :=
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
              let T1 := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons T1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hT1Trans : RuleProofs.eo_has_smt_translation T1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_arith_int_div_total_one T1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_int_div_total_one T1) true
                exact facts___eo_prog_arith_int_div_total_one_impl M hM T1 hT1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_arith_int_div_total_one T1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_arith_int_div_total_one T1)
                  (typed___eo_prog_arith_int_div_total_one_impl T1 hT1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
