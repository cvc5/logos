module

public import Cpc.Proofs.RuleSupport.QuantVarElimIneqEvalSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqEvalSupport
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

public section

/-!
Lift eventual falsity of individual literals to the complete disjunction.
Retained disjuncts are invariant under assignments to the eliminated variable;
a common bound handles all removed disjuncts.
-/

open Eo SmtEval Smtm

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

namespace QuantVarElimIneq

private theorem eval_or (M : SmtModel) (f g : Term) :
    __smtx_model_eval M (__eo_to_smt (qor f g)) =
      __smtx_model_eval_or (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g)) := by
  change __smtx_model_eval M (SmtTerm.or (__eo_to_smt f) (__eo_to_smt g)) = _
  rw [__smtx_model_eval.eq_def]

private theorem bool_args {f g : Term} (h : RuleProofs.eo_has_bool_type (qor f g)) :
    RuleProofs.eo_has_bool_type f ∧ RuleProofs.eo_has_bool_type g :=
  ⟨RuleProofs.eo_has_bool_type_or_left f g h, RuleProofs.eo_has_bool_type_or_right f g h⟩

theorem Eliminates.bool_type {x F G : Term} {d e : Int}
    (h : Eliminates x F G d e) (hF : RuleProofs.eo_has_bool_type F) :
    RuleProofs.eo_has_bool_type G := by
  induction h with
  | nil => exact hF
  | keep f fs gs d e hf h ih =>
      exact RuleProofs.eo_has_bool_type_or_of_bool_args _ _ (bool_args hF).1 (ih (bool_args hF).2)
  | drop _ _ _ _ _ _ _ _ _ _ _ ih => exact ih (bool_args hF).2

theorem Eliminates.orLists {x F G : Term} {d e : Int} (h : Eliminates x F G d e) :
    CnfSupport.OrList F ∧ CnfSupport.OrList G := by
  induction h with
  | nil => exact ⟨.false, .false⟩
  | keep _ _ _ _ _ _ _ ih => exact ⟨.cons _ _ ih.1, .cons _ _ ih.2⟩
  | drop _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨.cons _ _ ih.1, ih.2⟩

private theorem free_term_eval {M N : SmtModel} {s : native_String} {T f : Term}
    (hBool : RuleProofs.eo_has_bool_type f)
    (hf : __contains_atomic_term_list_free_rec f (single (qvar s T)) Term.__eo_List_nil =
      Term.Boolean false) (hAgree : Agree s T N M) :
    __smtx_model_eval N (__eo_to_smt f) = __smtx_model_eval M (__eo_to_smt f) := by
  exact smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (EoVarEnvPerm.of_exact (EoVarEnv.cons EoVarEnv.nil))
    (EoVarEnvPerm.of_exact EoVarEnv.nil)
    (RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool) hf hAgree

theorem Eliminates.output_eval {M N : SmtModel} {s : native_String} {T F G : Term} {d e : Int}
    (h : Eliminates (qvar s T) F G d e) (hF : RuleProofs.eo_has_bool_type F)
    (hAgree : Agree s T N M) :
    __smtx_model_eval N (__eo_to_smt G) = __smtx_model_eval M (__eo_to_smt G) := by
  induction h with
  | nil => rfl
  | keep f fs gs d e hf h ih =>
      rw [eval_or, eval_or, free_term_eval (bool_args hF).1 hf hAgree, ih (bool_args hF).2]
  | drop _ _ _ _ _ _ _ _ _ _ _ ih => exact ih (bool_args hF).2

theorem Eliminates.weaken (M : SmtModel) (hM : model_wf M)
    {x F G : Term} {d e : Int} (h : Eliminates x F G d e)
    (hF : RuleProofs.eo_has_bool_type F)
    (hG : __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt F) = SmtValue.Boolean true := by
  induction h with
  | nil => exact hG
  | keep f fs gs d e hf h ih =>
      obtain ⟨b, hb⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt f) (bool_args hF).1
      rw [eval_or, hb] at hG ⊢
      cases b with
      | false =>
          have htail : __smtx_model_eval M (__eo_to_smt gs) = SmtValue.Boolean true := by
            cases he : __smtx_model_eval M (__eo_to_smt gs) <;>
              simp [he, __smtx_model_eval_or, native_or] at hG ⊢
            assumption
          rw [ih (bool_args hF).2 htail]
          rfl
      | true =>
          obtain ⟨b, hb⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt fs) (bool_args hF).2
          rw [hb]
          cases b <;> rfl
  | drop f fs gs d e k hf hk hkRange hdk h ih =>
      have ht := ih (bool_args hF).2 hG
      obtain ⟨b, hb⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt f) (bool_args hF).1
      rw [eval_or, hb, ht]
      cases b <;> rfl

/-- At a sufficiently distant point in the final direction, every removed
literal is false and the original disjunction equals the retained one. -/
theorem Eliminates.eventual_eval (M : SmtModel) (hM : model_wf M) (s : native_String)
    {T F G : Term} {d e sign : Int} (hT : ArithType T)
    (h : Eliminates (qvar s T) F G d e) (hF : RuleProofs.eo_has_bool_type F)
    (hd : IsDirection d) (hs : sign = -1 ∨ sign = 1) (he : e * sign ≠ -1) :
    Eventually (fun n => __smtx_model_eval (push M s T (sign * n)) (__eo_to_smt F) =
      __smtx_model_eval M (__eo_to_smt G)) := by
  induction h with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | keep f fs gs d e hf h ih =>
      obtain ⟨B, hB⟩ := ih (bool_args hF).2 hd he
      refine ⟨B, ?_⟩
      intro n hn
      rw [eval_or, eval_or, free_term_eval (bool_args hF).1 hf (push_agree M s T _), hB n hn]
  | drop f fs gs d e k hf hk hkRange hdk h ih =>
      have hd' : IsDirection (if k = 0 then d else k) := by split <;> assumption
      have hnext := h.initial_compatible hd' hs he
      have hkSign := (compatible_previous hd hkRange hs hdk hnext).2
      have hfEscape := literal_escapes M hM s hT (bool_args hF).1 hs hkSign hk
      obtain ⟨B, hB⟩ := Eventually.and hfEscape (ih (bool_args hF).2 hd' he)
      obtain ⟨b, hb⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt gs)
        (h.bool_type (bool_args hF).2)
      refine ⟨B, ?_⟩
      intro n hn
      rw [eval_or, (hB n hn).1, (hB n hn).2, hb]
      cases b <;> rfl

end QuantVarElimIneq
