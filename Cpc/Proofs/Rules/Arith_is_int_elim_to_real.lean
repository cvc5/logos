module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RealBridge
import all Cpc.Proofs.RealBridge

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev isIntToRealTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.is_int) (Term.Apply (Term.UOp UserOp.to_real) t)

private theorem eo_to_smt_is_int_to_real_eq (t : Term) :
    __eo_to_smt (isIntToRealTerm t) =
      SmtTerm.is_int (SmtTerm.to_real (__eo_to_smt t)) := by
  rfl

private theorem prog_arith_is_int_elim_to_real_eq
    (t : Term) (ht : t ≠ Term.Stuck) :
    __eo_prog_arith_is_int_elim_to_real t =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) (isIntToRealTerm t))
        (Term.Boolean true) := by
  cases t <;> simp [__eo_prog_arith_is_int_elim_to_real] at ht ⊢

private theorem typeof_arg_of_prog_arith_is_int_elim_to_real_bool
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (h : __eo_typeof (__eo_prog_arith_is_int_elim_to_real t) = Term.Bool) :
    __eo_typeof t = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  rw [prog_arith_is_int_elim_to_real_eq t ht] at h
  change __eo_typeof_eq (__eo_typeof (isIntToRealTerm t))
    (__eo_typeof (Term.Boolean true)) = Term.Bool at h
  rcases RuleProofs.eo_typeof_eq_bool_same _ _ h with ⟨_hSame, hNonStuck⟩
  change __eo_typeof_is_int (__eo_typeof_to_real (__eo_typeof t)) ≠ Term.Stuck
    at hNonStuck
  cases hTy : __eo_typeof t with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_is_int, __eo_typeof_to_real, hTy] at hNonStuck ⊢
  | _ =>
      simp [__eo_typeof_is_int, __eo_typeof_to_real, hTy] at hNonStuck

private theorem typed___eo_prog_arith_is_int_elim_to_real_impl
    (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  __eo_typeof (__eo_prog_arith_is_int_elim_to_real t) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_is_int_elim_to_real t) := by
  intro hTTrans hResultTy
  have hTTy : __eo_typeof t = Term.Int :=
    typeof_arg_of_prog_arith_is_int_elim_to_real_bool t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTTy
  have hLhsTy : __smtx_typeof (__eo_to_smt (isIntToRealTerm t)) = SmtType.Bool := by
    rw [eo_to_smt_is_int_to_real_eq, typeof_is_int_eq, typeof_to_real_eq]
    simp [native_ite, native_Teq, hSmtT]
  have hRhsTy : __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_1]
  rw [prog_arith_is_int_elim_to_real_eq t ht]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (isIntToRealTerm t) (Term.Boolean true)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_arith_is_int_elim_to_real_impl
    (M : SmtModel) (hM : model_wf M) (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  __eo_typeof (__eo_prog_arith_is_int_elim_to_real t) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_is_int_elim_to_real t) true := by
  intro hTTrans hResultTy
  have hProgBool :=
    typed___eo_prog_arith_is_int_elim_to_real_impl t hTTrans hResultTy
  have hTTy : __eo_typeof t = Term.Int :=
    typeof_arg_of_prog_arith_is_int_elim_to_real_bool t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_is_int_elim_to_real_eq t ht
  rw [hProgEq] at hProgBool ⊢
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTTy
  have hEvalTTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t) SmtType.Int hSmtT
      (by simp) type_inhabited_int
  rcases int_value_canonical hEvalTTy with ⟨n, hEvalT⟩
  have hEvalLhs :
      __smtx_model_eval M (__eo_to_smt (isIntToRealTerm t)) =
        SmtValue.Boolean true := by
    rw [eo_to_smt_is_int_to_real_eq, __smtx_model_eval.eq_23,
      __smtx_model_eval.eq_21, hEvalT]
    change __smtx_model_eval_eq
        (SmtValue.Real (native_int_to_real
          (native_real_to_int (native_int_to_real n))))
        (SmtValue.Real (native_int_to_real n)) = SmtValue.Boolean true
    rw [native_real_to_int_int_to_real]
    exact RuleProofs.smtx_model_eval_eq_refl _
  have hEvalRhs :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    rw [__smtx_model_eval.eq_1]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (isIntToRealTerm t) (Term.Boolean true) hProgBool <| by
      rw [hEvalLhs, hEvalRhs]
      exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_arith_is_int_elim_to_real_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_is_int_elim_to_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_is_int_elim_to_real args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_is_int_elim_to_real args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_is_int_elim_to_real args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hT1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_arith_is_int_elim_to_real a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_is_int_elim_to_real a1) true
                exact facts___eo_prog_arith_is_int_elim_to_real_impl M hM a1
                  hT1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_arith_is_int_elim_to_real a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_arith_is_int_elim_to_real a1)
                  (typed___eo_prog_arith_is_int_elim_to_real_impl a1 hT1Trans hResultTy)
