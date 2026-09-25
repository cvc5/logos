module

public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
public import Cpc.Proofs.Rules.Quant_var_reordering
import all Cpc.Proofs.Rules.Quant_var_reordering

public section

/-!
Universal-quantifier semantics as sequences of typed, canonical assignments.
The permutation lemma reuses the existing quantifier-reordering proof, which
also handles repeated binders.
-/

open Eo SmtEval Smtm
set_option maxHeartbeats 300000
namespace QuantVarElimIneq

private theorem eval_not (M : SmtModel) (t : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not t) =
      __smtx_model_eval_not (__smtx_model_eval M t) := by
  rw [__smtx_model_eval.eq_def]

private theorem not_true_iff (v : SmtValue) :
    __smtx_model_eval_not v = SmtValue.Boolean true ↔ v = SmtValue.Boolean false := by
  cases v <;> simp [__smtx_model_eval_not, native_not]

theorem forall_encoding_step_iff
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T : SmtType) (tail : SmtTerm)
    (hWf : __smtx_type_wf T = true)
    (hTailTy : __smtx_typeof tail = SmtType.Bool) :
    __smtx_model_eval M (SmtTerm.not (SmtTerm.exists s T tail)) =
        SmtValue.Boolean true ↔
      ∀ v : SmtValue, __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push M s T v) (SmtTerm.not tail) =
          SmtValue.Boolean true := by
  classical
  constructor
  · intro h v hvT hvC
    rw [eval_not] at h
    have hExFalse : __smtx_model_eval M (SmtTerm.exists s T tail) =
        SmtValue.Boolean false :=
      (not_true_iff _).1 h
    have hNoSat : ¬ (∃ w : SmtValue,
        __smtx_typeof_value w = T ∧
          __smtx_value_canonical w = true ∧
            __smtx_model_eval (native_model_push M s T w) tail =
              SmtValue.Boolean true) := by
      intro hSat
      have : __smtx_model_eval M (SmtTerm.exists s T tail) =
          SmtValue.Boolean true := by
        show (if _ : (∃ w : SmtValue,
            __smtx_typeof_value w = T ∧
              __smtx_value_canonical w = true ∧
                __smtx_model_eval (native_model_push M s T w) tail =
                  SmtValue.Boolean true)
          then SmtValue.Boolean true else SmtValue.Boolean false) =
          SmtValue.Boolean true
        rw [dif_pos hSat]
      rw [hExFalse] at this
      exact absurd this (by decide)
    have hPushTotal : model_wf (native_model_push M s T v) :=
      model_total_typed_push hM s T v hWf hvT
        (by simpa [value_canonical] using hvC)
    obtain ⟨b, hb⟩ :=
      smt_model_eval_bool_is_boolean (native_model_push M s T v) hPushTotal
        tail hTailTy
    cases b
    · rw [eval_not, hb]
      rfl
    · exact absurd ⟨v, hvT, hvC, hb⟩ hNoSat
  · intro h
    have hNoSat : ¬ (∃ w : SmtValue,
        __smtx_typeof_value w = T ∧
          __smtx_value_canonical w = true ∧
            __smtx_model_eval (native_model_push M s T w) tail =
              SmtValue.Boolean true) := by
      rintro ⟨w, hwT, hwC, hwE⟩
      have := h w hwT hwC
      rw [eval_not, hwE] at this
      exact absurd this (by decide)
    have hExFalse : __smtx_model_eval M (SmtTerm.exists s T tail) =
        SmtValue.Boolean false := by
      show (if _ : (∃ w : SmtValue,
          __smtx_typeof_value w = T ∧
            __smtx_value_canonical w = true ∧
              __smtx_model_eval (native_model_push M s T w) tail =
                SmtValue.Boolean true)
        then SmtValue.Boolean true else SmtValue.Boolean false) =
        SmtValue.Boolean false
      rw [dif_neg hNoSat]
    rw [eval_not, hExFalse]
    rfl


/-- Universal evaluation as a sequence of typed assignments. -/
def AllAssignments : List (native_String × SmtType) → SmtModel → (SmtModel → Prop) → Prop
  | [], M, P => P M
  | (s, T) :: bs, M, P => ∀ v, __smtx_typeof_value v = T →
      __smtx_value_canonical v = true → AllAssignments bs (native_model_push M s T v) P

def existsBinders : List (native_String × SmtType) → SmtTerm → SmtTerm
  | [], body => body
  | (s, T) :: bs, body => SmtTerm.exists s T (existsBinders bs body)

private theorem existsBinders_type {bs : List (native_String × SmtType)} {body : SmtTerm}
    (hw : ∀ b ∈ bs, __smtx_type_wf b.2 = true)
    (hb : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (existsBinders bs body) = SmtType.Bool := by
  induction bs with
  | nil => exact hb
  | cons b bs ih =>
      rcases b with ⟨s,T⟩
      have ht := ih (fun b h => hw b (List.Mem.tail _ h))
      change __smtx_typeof (SmtTerm.exists s T (existsBinders bs body)) = _
      rw [__smtx_typeof.eq_def]
      simp [__smtx_typeof_guard_wf, hw (s,T) (by simp), ht, native_ite, native_Teq]

theorem forallBinders_true_iff {bs : List (native_String × SmtType)} {body : SmtTerm}
    (hw : ∀ b ∈ bs, __smtx_type_wf b.2 = true)
    (hb : __smtx_typeof body = SmtType.Bool) (M : SmtModel) (hM : model_wf M) :
    __smtx_model_eval M (SmtTerm.not (existsBinders bs (SmtTerm.not body))) =
      SmtValue.Boolean true ↔
    AllAssignments bs M (fun N => __smtx_model_eval N body = SmtValue.Boolean true) := by
  induction bs generalizing M with
  | nil =>
      obtain ⟨b, he⟩ := smt_model_eval_bool_is_boolean M hM body hb
      simp only [existsBinders, AllAssignments, eval_not, he]
      cases b <;> decide
  | cons b bs ih =>
      rcases b with ⟨s,T⟩
      have hwT := hw (s,T) (by simp)
      have hwbs := fun b h => hw b (List.Mem.tail (s,T) h)
      have hnot : __smtx_typeof (SmtTerm.not body) = SmtType.Bool := by
        rw [typeof_not_eq]; simp [hb, native_ite, native_Teq]
      change __smtx_model_eval M (SmtTerm.not (SmtTerm.exists s T _)) = _ ↔ _
      rw [forall_encoding_step_iff M hM s T _ hwT (existsBinders_type hwbs hnot)]
      simp only [AllAssignments]
      apply forall_congr'; intro v
      apply imp_congr_right; intro hvT
      apply imp_congr_right; intro hvC
      exact ih hwbs (native_model_push M s T v)
        (model_total_typed_push hM s T v hwT hvT hvC)

theorem AllAssignments.append (xs ys : List (native_String × SmtType))
    (M : SmtModel) (P : SmtModel → Prop) :
    AllAssignments (xs ++ ys) M P ↔
      AllAssignments xs M (fun N => AllAssignments ys N P) := by
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨s,T⟩
      simp only [List.cons_append, AllAssignments]
      apply forall_congr'; intro v
      apply imp_congr_right; intro _
      apply imp_congr_right; intro _
      exact ih _

theorem AllAssignments.congr {xs : List (native_String × SmtType)}
    (hw : ∀ b ∈ xs, __smtx_type_wf b.2 = true)
    {P Q : SmtModel → Prop} (h : ∀ M, model_wf M → (P M ↔ Q M))
    (M : SmtModel) (hM : model_wf M) :
    AllAssignments xs M P ↔ AllAssignments xs M Q := by
  induction xs generalizing M with
  | nil => exact h M hM
  | cons x xs ih =>
      rcases x with ⟨s,T⟩
      simp only [AllAssignments]
      apply forall_congr'; intro v
      apply imp_congr_right; intro hvT
      apply imp_congr_right; intro hvC
      exact ih (fun b hb => hw b (List.Mem.tail _ hb)) _
        (model_total_typed_push hM s T v (hw (s,T) (by simp)) hvT hvC)

def smtBinders (vs : List EoVarKey) : List (native_String × SmtType) :=
  vs.map (fun (s,T) => (s,__eo_to_smt_type T))

theorem exists_env {xs : Term} {vs : List EoVarKey}
    (h : EoVarEnv xs vs) (body : SmtTerm) :
    __eo_to_smt_exists xs body = existsBinders (smtBinders vs) body := by
  induction h with
  | nil => rfl
  | cons hh ih => simpa [__eo_to_smt_exists, smtBinders, existsBinders] using ih

theorem smtBinders_wf {vs : List EoVarKey}
    (hw : ∀ s T, (s,T) ∈ vs → __smtx_type_wf (__eo_to_smt_type T) = true) :
    ∀ b ∈ smtBinders vs, __smtx_type_wf b.2 = true := by
  intro b hb
  obtain ⟨⟨s,T⟩,hm,rfl⟩ := List.mem_map.mp hb
  exact hw s T hm

abbrev qforall (xs F : Term) : Term := ((Term.UOp UserOp.forall).Apply xs).Apply F

theorem forall_env_iff {xs : Term} {vs : List EoVarKey} {F : Term}
    (h : EoVarEnv xs vs) (hxs : xs ≠ Term.__eo_List_nil)
    (hw : ∀ s T, (s,T) ∈ vs → __smtx_type_wf (__eo_to_smt_type T) = true)
    (hF : RuleProofs.eo_has_bool_type F) (M : SmtModel) (hM : model_wf M) :
    __smtx_model_eval M (__eo_to_smt (qforall xs F)) = SmtValue.Boolean true ↔
    AllAssignments (smtBinders vs) M
      (fun N => __smtx_model_eval N (__eo_to_smt F) = SmtValue.Boolean true) := by
  rw [SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil xs F hxs,
    exists_env h]
  exact forallBinders_true_iff (smtBinders_wf hw) hF M hM

private theorem existsBinders_eq_fold (bs : List (native_String × SmtType)) (body : SmtTerm) :
    existsBinders bs body = smtExistsOfBinders bs body := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b; simp [existsBinders, smtExistsOfBinders, ih]

theorem assignments_perm {bs cs : List (native_String × SmtType)} {body : SmtTerm}
    (hp : bs.Perm cs) (hw : ∀ b ∈ bs, __smtx_type_wf b.2 = true)
    (hb : __smtx_typeof body = SmtType.Bool) (M : SmtModel) (hM : model_wf M) :
    AllAssignments bs M (fun N => __smtx_model_eval N body = SmtValue.Boolean true) ↔
    AllAssignments cs M (fun N => __smtx_model_eval N body = SmtValue.Boolean true) := by
  rw [← forallBinders_true_iff hw hb M hM,
    ← forallBinders_true_iff (fun b h => hw b (hp.mem_iff.mpr h)) hb M hM,
    existsBinders_eq_fold, existsBinders_eq_fold, eval_not, eval_not,
    smtExistsOfBinders_eval_perm _ hp M]

end QuantVarElimIneq
