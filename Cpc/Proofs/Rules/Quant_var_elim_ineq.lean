module

public import Cpc.Proofs.RuleSupport.QuantVarElimIneqSoundness
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqSoundness
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqQuantSupport
import all Cpc.Proofs.RuleSupport.Support

open Eo SmtEval Smtm

set_option maxHeartbeats 1000000

namespace QuantVarElimIneq

private abbrev formula (xs F G : Term) : Term :=
  ((Term.UOp UserOp.eq).Apply (qforall xs F)).Apply G

private theorem program_shape {a : Term}
    (h : __eo_prog_quant_var_elim_ineq a ≠ Term.Stuck) :
    ∃ xs F G, a = formula xs F G ∧
      __is_quant_var_elim_ineq xs F G = Term.Boolean true ∧
      __eo_prog_quant_var_elim_ineq a = a := by
  rw [__eo_prog_quant_var_elim_ineq.eq_def] at h
  split at h
  · have hg := support_eo_requires_cond_eq_of_non_stuck h
    refine ⟨_,_,_,rfl,hg,?_⟩
    simp [__eo_prog_quant_var_elim_ineq, hg, __eo_requires, native_ite, native_teq, native_not]
  · contradiction

private theorem formula_true (M : SmtModel) (hM : model_wf M) (xs F G : Term)
    (hb : RuleProofs.eo_has_bool_type (formula xs F G))
    (hg : __is_quant_var_elim_ineq xs F G = Term.Boolean true) :
    eo_interprets M (formula xs F G) true := by
  have hops := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type (qforall xs F) G hb
  have hLTrans : RuleProofs.eo_has_smt_translation (qforall xs F) := hops.2
  have hLBool := forall_bool hLTrans
  have hGBool : RuleProofs.eo_has_bool_type G := hops.1.symm.trans hLBool
  have hi := guard_truth M hM xs F G hLTrans hGBool hg
  obtain ⟨b,hbval⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt (qforall xs F)) hLBool
  obtain ⟨c,hcval⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt G) hGBool
  apply RuleProofs.eo_interprets_of_bool_eval M _ true hb
  change __smtx_model_eval M (SmtTerm.eq (__eo_to_smt (qforall xs F)) (__eo_to_smt G)) = _
  rw [__smtx_model_eval.eq_def]
  dsimp only
  rw [hbval, hcval]
  rw [hbval,hcval] at hi
  cases b <;> cases c <;> simp_all [__smtx_model_eval_eq, native_veq]

end QuantVarElimIneq

public theorem cmd_step_quant_var_elim_ineq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_var_elim_ineq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_var_elim_ineq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_var_elim_ineq args premises) := by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | cons _ _ => exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ => exact False.elim (hProg rfl)
          | nil =>
              change __eo_prog_quant_var_elim_ineq a ≠ Term.Stuck at hProg
              obtain ⟨xs,F,G,ha,hg,hout⟩ := QuantVarElimIneq.program_shape hProg
              have hTrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              change __eo_typeof (__eo_prog_quant_var_elim_ineq a) = Term.Bool at hResultTy
              rw [hout] at hResultTy
              have hBool := RuleProofs.eo_typeof_bool_implies_has_bool_type a hTrans hResultTy
              have hFact : eo_interprets M a true := by
                rw [ha] at hBool ⊢
                exact QuantVarElimIneq.formula_true M hM xs F G hBool hg
              constructor
              · intro _
                change eo_interprets M (__eo_prog_quant_var_elim_ineq a) true
                rw [hout]
                exact hFact
              · change RuleProofs.eo_has_smt_translation (__eo_prog_quant_var_elim_ineq a)
                rw [hout]
                exact hTrans
