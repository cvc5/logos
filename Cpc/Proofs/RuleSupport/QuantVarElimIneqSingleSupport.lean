module

public import Cpc.Proofs.RuleSupport.QuantVarElimIneqBoolSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqBoolSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqEvalSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.QuantVarElimIneqQuantSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqQuantSupport

public section

/-!
Connect the disjunction semantics to elimination of one arithmetic binder.
The checker's singleton introduction and elimination preserve Boolean values.
-/
open Eo SmtEval Smtm
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace QuantVarElimIneq

theorem Eliminates.all_assignments (M : SmtModel) (hM : model_wf M) (s : native_String)
    {T F G : Term} {e : Int} (hT : ArithType T)
    (h : Eliminates (qvar s T) F G 0 e) (hF : RuleProofs.eo_has_bool_type F) :
    AllAssignments [(s,__eo_to_smt_type T)] M
      (fun N => __smtx_model_eval N (__eo_to_smt F) = SmtValue.Boolean true) ↔
    __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  constructor
  · intro hall
    have hd : IsDirection (0 : Int) := Or.inr (Or.inl rfl)
    have he := h.final_direction hd
    let sign : Int := if e = -1 then -1 else 1
    have hs : sign = -1 ∨ sign = 1 := by simp only [sign]; split <;> simp
    have hsign : e * sign ≠ -1 := by
      rcases he with rfl | rfl | rfl <;> decide
    obtain ⟨B, hB⟩ := h.eventual_eval M hM s hT hF hd hs hsign
    have hv := arithValue_facts hT (sign * B)
    have hf := hall (arithValue T (sign * B)) hv.2.1 hv.2.2
    exact (hB B (Int.le_refl B)).symm.trans hf
  · intro hg v hvT hvC
    have hw := (arithValue_facts hT 0).1
    have hN := model_total_typed_push hM s (__eo_to_smt_type T) v hw hvT hvC
    have ha : Agree s T (native_model_push M s (__eo_to_smt_type T) v) M :=
      model_agrees_except_on_env_push_left_of_mem_except (by simp) (by simp)
    exact h.weaken _ hN hF ((h.output_eval hF ha).trans hg)

theorem intro_shape {F : Term}
    (h : __eo_list_singleton_intro (Term.UOp UserOp.or) F ≠ Term.Stuck) :
    __eo_list_singleton_intro (Term.UOp UserOp.or) F = F ∨
    __eo_list_singleton_intro (Term.UOp UserOp.or) F = qor F (Term.Boolean false) := by
  have h' := h
  unfold __eo_list_singleton_intro at h'
  rcases ite_facts rfl h' with ⟨_, he⟩ | ⟨_, he⟩
  · exact Or.inl he.symm
  · have hbranch := fun hz => h' (he.symm.trans hz)
    right
    change _ = qor F (Term.Boolean false)
    unfold __eo_list_singleton_intro
    dsimp only
    rw [← he]
    cases ht : __eo_typeof F <;>
      simp [ht, __eo_nil, __eo_requires, __eo_is_list, __eo_get_nil_rec,
        __eo_is_ok, __eo_is_list_nil, __eo_mk_apply, native_ite, native_teq,
        native_not] at hbranch ⊢

theorem intro_type {F : Term} (hF : RuleProofs.eo_has_bool_type F)
    (h : __eo_list_singleton_intro (Term.UOp UserOp.or) F ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (__eo_list_singleton_intro (Term.UOp UserOp.or) F) := by
  rcases intro_shape h with he | he <;> rw [he]
  · exact hF
  · exact RuleProofs.eo_has_bool_type_or_of_bool_args _ _ hF RuleProofs.eo_has_bool_type_false

theorem intro_eval (M : SmtModel) (hM : model_wf M) {F : Term}
    (hF : RuleProofs.eo_has_bool_type F)
    (h : __eo_list_singleton_intro (Term.UOp UserOp.or) F ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_intro (Term.UOp UserOp.or) F)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  rcases intro_shape h with he | he
  · rw [he]
  · rw [he]
    obtain ⟨b,hb⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt F) hF
    rw [eval_or, hb]
    cases b <;> rfl

theorem elim_eval (M : SmtModel) (hM : model_wf M) {G : Term}
    (hList : CnfSupport.OrList G) (hG : RuleProofs.eo_has_bool_type G) :
    __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.or) G)) =
      __smtx_model_eval M (__eo_to_smt G) := by
  simp only [__eo_list_singleton_elim]
  rw [CnfSupport.orList_is_list_true hList]
  simp [__eo_requires, native_ite, native_teq, native_not]
  cases hList with
  | false => rfl
  | cons f fs hfs =>
      cases hfs with
      | false =>
          have hf := RuleProofs.eo_has_bool_type_or_left _ _ hG
          obtain ⟨b,hb⟩ := smt_model_eval_bool_is_boolean M hM (__eo_to_smt f) hf
          simp only [__eo_list_singleton_elim_2, __eo_is_list_nil]
          simp [__eo_ite, native_ite, native_teq]
          change __smtx_model_eval M (__eo_to_smt f) = __smtx_model_eval M (__eo_to_smt (qor f (Term.Boolean false)))
          rw [eval_or, hb]
          cases b <;> rfl
      | cons g gs hgs => rfl

theorem singleton_guard_assignments (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T F G : Term)
    (hF : RuleProofs.eo_has_bool_type F) (hG : RuleProofs.eo_has_bool_type G)
    (hg : __is_quant_var_elim_ineq (single (qvar s T)) F G = Term.Boolean true) :
    AllAssignments [(s,__eo_to_smt_type T)] M
      (fun N => __smtx_model_eval N (__eo_to_smt F) = SmtValue.Boolean true) ↔
    __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  have hFn := RuleProofs.term_ne_stuck_of_has_smt_translation F
    (RuleProofs.eo_has_smt_translation_of_has_bool_type F hF)
  have hGn := RuleProofs.term_ne_stuck_of_has_smt_translation G
    (RuleProofs.eo_has_smt_translation_of_has_bool_type G hG)
  rw [__is_quant_var_elim_ineq.eq_def] at hg
  split at hg <;> try contradiction
  all_goals
    try
      exact False.elim
        (‹∀ x : Term, single (qvar s T) = (Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil → False›
          (qvar s T) rfl)
  rename_i F G u v w x hshape hFn' hGn'
  have hx : qvar s T = x := by simpa [single] using hshape
  subst x
  obtain ⟨hT,hEq⟩ := requires_facts hg (by decide)
  change __is_arith_type T = Term.Boolean true at hT
  have hArith : ArithType T := by
    unfold __is_arith_type at hT
    split at hT <;> simp_all [ArithType]
  have he := (RuleProofs.eq_of_eo_eq_true _ _ hEq).symm
  let L := __eo_list_singleton_intro (Term.UOp UserOp.or) F
  let Q := __mk_quant_var_elim_ineq (qvar s T) L (Term.Numeral 0)
  have hQ : Q ≠ Term.Stuck := by
    intro hz
    have he' : __eo_list_singleton_elim (Term.UOp UserOp.or) Q = G := he
    rw [hz] at he'
    simp [__eo_list_singleton_elim, __eo_is_list, __eo_requires] at he'
    exact hGn he'.symm
  obtain ⟨e,helim⟩ := mk_eliminates (qvar s T) L 0 Q (by simp [qvar]) rfl hQ
  have hL : L ≠ Term.Stuck := CnfSupport.orList_ne_stuck helim.orLists.1
  have hLT := intro_type hF hL
  have hw : ∀ b ∈ [(s,__eo_to_smt_type T)], __smtx_type_wf b.2 = true := by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact (arithValue_facts hArith 0).1
  have hconv := AllAssignments.congr hw
    (P := fun N => __smtx_model_eval N (__eo_to_smt F) = SmtValue.Boolean true)
    (Q := fun N => __smtx_model_eval N (__eo_to_smt L) = SmtValue.Boolean true)
    (fun N hN => by rw [intro_eval N hN hF hL]) M hM
  rw [hconv, helim.all_assignments M hM s hArith hLT]
  have hEval := elim_eval M hM helim.orLists.2 (helim.bool_type hLT)
  change __smtx_model_eval M (__eo_to_smt Q) = _ ↔ _
  rw [he] at hEval
  rw [hEval]

end QuantVarElimIneq
