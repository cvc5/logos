module

public import Cpc.Proofs.RuleSupport.QuantVarElimIneqSingleSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqSingleSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqQuantSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqEvalSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqSupport
public import Cpc.Proofs.RuleSupport.QuantVarElimIneqEnvSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqEnvSupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

public section

/-!
Soundness of the complete `quant_var_elim_ineq` guard. The multiple-binder
case moves the selected binder last and applies single-binder elimination in
every assignment to the retained binders.
-/
open Eo SmtEval Smtm
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace QuantVarElimIneq

private theorem erased_forall_iff (M : SmtModel) (hM : model_wf M)
    {xs ys F G : Term} {vs : List EoVarKey}
    (hEnv : EoVarEnv xs vs) (s : native_String) (T : Term)
    (hMem : (s,T) ∈ vs)
    (hErase : __eo_list_erase Term.__eo_List_cons xs (qvar s T) = ys)
    (hXs : xs ≠ Term.__eo_List_nil) (hYs : ys ≠ Term.__eo_List_nil)
    (hw : ∀ s T, (s,T) ∈ vs → __smtx_type_wf (__eo_to_smt_type T) = true)
    (hF : RuleProofs.eo_has_bool_type F) (hG : RuleProofs.eo_has_bool_type G)
    (hg : __is_quant_var_elim_ineq (single (qvar s T)) F G = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (qforall xs F)) = SmtValue.Boolean true ↔
    __smtx_model_eval M (__eo_to_smt (qforall ys G)) = SmtValue.Boolean true := by
  have hy : EoVarEnv ys (vs.erase (s,T)) := by
    rw [← hErase]
    exact hEnv.erase_exact s T
  have hwy : ∀ s' T', (s',T') ∈ vs.erase (s,T) →
      __smtx_type_wf (__eo_to_smt_type T') = true :=
    fun s' T' hm => hw s' T' (List.mem_of_mem_erase hm)
  rw [forall_env_iff hEnv hXs hw hF M hM, forall_env_iff hy hYs hwy hG M hM]
  have hp : vs.Perm (vs.erase (s,T) ++ [(s,T)]) :=
    (List.perm_cons_erase hMem).trans
      (show ([(s,T)] ++ vs.erase (s,T)).Perm (vs.erase (s,T) ++ [(s,T)]) from List.perm_append_comm)
  have hpm := hp.map (fun (s,T) => (s,__eo_to_smt_type T))
  have hap := assignments_perm hpm (smtBinders_wf hw) hF M hM
  change AllAssignments (smtBinders vs) M _ ↔ _ at hap
  rw [hap]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [AllAssignments.append]
  exact AllAssignments.congr (smtBinders_wf hwy)
    (fun N hN => singleton_guard_assignments N hN s T F G hF hG hg) M hM

private theorem guard_cases {xs F G : Term}
    (hg : __is_quant_var_elim_ineq xs F G = Term.Boolean true) :
    (∃ x, xs = single x) ∨
    ∃ ys H, G = qforall ys H ∧
      let x := __eo_list_nth Term.__eo_List_cons
        (__eo_list_diff Term.__eo_List_cons xs ys) (Term.Numeral 0)
      x ≠ Term.Stuck ∧ __eo_list_erase Term.__eo_List_cons xs x = ys ∧
        __is_quant_var_elim_ineq (single x) F H = Term.Boolean true := by
  rw [__is_quant_var_elim_ineq.eq_def] at hg
  split at hg <;> try contradiction
  · left
    exact ⟨_, rfl⟩
  · rename_i u v w ys H hx hsingle hF
    right
    refine ⟨_,_,rfl,?_⟩
    obtain ⟨he,hr⟩ := requires_facts hg (by decide)
    dsimp only at he hr ⊢
    have hn : __eo_list_nth Term.__eo_List_cons
        (__eo_list_diff Term.__eo_List_cons xs ys) (Term.Numeral 0) ≠ Term.Stuck := by
      intro hz
      simp [hz, __eo_mk_apply, __is_quant_var_elim_ineq] at hr
    exact ⟨hn,he, by simpa [single, __eo_mk_apply, hn] using hr⟩

private theorem singleton_env_shape {x : Term} {vs : List EoVarKey}
    (h : EoVarEnv (single x) vs) : ∃ s T, x = qvar s T := by
  cases h with
  | cons htail => exact ⟨_,_,rfl⟩

private theorem forall_bool {xs F : Term}
    (h : RuleProofs.eo_has_smt_translation (qforall xs F)) :
    RuleProofs.eo_has_bool_type (qforall xs F) := by
  have hn := SubstituteTranslatabilitySupport.forall_binders_non_nil_of_has_smt_translation xs F h
  unfold RuleProofs.eo_has_bool_type
  unfold RuleProofs.eo_has_smt_translation at h
  rw [SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil xs F hn] at h ⊢
  exact smtx_typeof_not_eq_bool_of_non_none _ h

theorem guard_truth (M : SmtModel) (hM : model_wf M) (xs F G : Term)
    (hForall : RuleProofs.eo_has_smt_translation (qforall xs F))
    (hG : RuleProofs.eo_has_bool_type G)
    (hg : __is_quant_var_elim_ineq xs F G = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (qforall xs F)) = SmtValue.Boolean true ↔
    __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  obtain ⟨vs,hEnv⟩ := SubstituteTranslatabilitySupport.forall_binders_env_of_has_smt_translation xs F hForall
  have hw := SubstituteTranslatabilitySupport.forall_binder_types_wf_of_has_smt_translation hForall hEnv
  have hF := SubstituteTranslatabilitySupport.forall_body_has_bool_type_of_has_smt_translation xs F hForall
  have hXs := SubstituteTranslatabilitySupport.forall_binders_non_nil_of_has_smt_translation xs F hForall
  rcases guard_cases hg with ⟨x,rfl⟩ | ⟨ys,H,rfl,hn,he,hg'⟩
  · obtain ⟨s,T,rfl⟩ := singleton_env_shape hEnv
    have hSingleEnv : EoVarEnv (single (qvar s T)) [(s,T)] := .cons .nil
    have hvs := EoVarEnv.vars_eq_of_same_env hEnv hSingleEnv
    subst vs
    rw [forall_env_iff hEnv hXs hw hF M hM]
    exact singleton_guard_assignments M hM s T F G hF hG hg
  · have hGTrans := RuleProofs.eo_has_smt_translation_of_has_bool_type _ hG
    obtain ⟨ysv,hYsEnv⟩ := SubstituteTranslatabilitySupport.forall_binders_env_of_has_smt_translation ys H hGTrans
    have hYs := SubstituteTranslatabilitySupport.forall_binders_non_nil_of_has_smt_translation ys H hGTrans
    have hH := SubstituteTranslatabilitySupport.forall_body_has_bool_type_of_has_smt_translation ys H hGTrans
    obtain ⟨s,T,hm,hx⟩ := EoVarEnv.selected_mem hEnv hYsEnv hn
    rw [hx] at he hg'
    exact erased_forall_iff M hM hEnv s T hm he hXs hYs hw hF hH hg'

end QuantVarElimIneq
