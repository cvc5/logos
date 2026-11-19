module

public import Cpc.Proofs.StaticTyping
import all Cpc.Proofs.StaticTyping

public section

open Smtm

namespace RuleProofs

/-- The `Boolean` arm of model evaluation.

Using `unfold` here also generates `__smtx_model_eval.eq_def` in this shared
proof module. The evaluator has an exposed body, so downstream proofs reuse
that unfolding theorem under the same name instead of generating private
copies in each module. Keep this proof before the rest of the proof stack. -/
theorem model_eval_boolean_eq (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  unfold __smtx_model_eval
  rfl

end RuleProofs

section

open SmtEval

namespace Smtm

/-- A binding `(s T v)` occurs in the bindings `bs` of a `let`. -/
inductive SmtBindings.Mem : SmtBindings -> native_String -> SmtType -> SmtTerm -> Prop
  | head (s : native_String) (T : SmtType) (v : SmtTerm) (bs : SmtBindings) :
      SmtBindings.Mem (SmtBindings.cons s T v bs) s T v
  | tail {bs : SmtBindings} {s : native_String} {T : SmtType} {v : SmtTerm}
      (s' : native_String) (T' : SmtType) (v' : SmtTerm) :
      SmtBindings.Mem bs s T v -> SmtBindings.Mem (SmtBindings.cons s' T' v' bs) s T v

theorem SmtBindings.Mem.sizeOf_lt {bs : SmtBindings} {s : native_String} {T : SmtType}
    {v : SmtTerm} (h : SmtBindings.Mem bs s T v) : sizeOf v < sizeOf bs := by
  induction h with
  | head => simp; omega
  | tail _ _ _ _ ih => simp; omega

/-- A bound term is smaller than the `let` it is bound in. -/
theorem SmtBindings.Mem.sizeOf_lt_bind {bs : SmtBindings} {s : native_String} {T : SmtType}
    {v : SmtTerm} (x : SmtTerm) (h : SmtBindings.Mem bs s T v) :
    sizeOf v < sizeOf (SmtTerm.bind bs x) := by
  have := h.sizeOf_lt
  simp; omega

theorem model_push_bindings_nil (M N : SmtModel) :
    __smtx_model_push_bindings M N SmtBindings.nil = N := by
  rw [__smtx_model_push_bindings.eq_def]

theorem model_push_bindings_cons (M N : SmtModel) (s : native_String) (T : SmtType)
    (v : SmtTerm) (bs : SmtBindings) :
    __smtx_model_push_bindings M N (SmtBindings.cons s T v bs) =
      __smtx_model_push_bindings M (native_model_push N s T (__smtx_model_eval M v)) bs := by
  rw [__smtx_model_push_bindings.eq_def]

/-- Pushing bindings leaves the sort domains alone. -/
theorem model_push_bindings_usortDom (M : SmtModel) :
    ∀ (N : SmtModel) (bs : SmtBindings),
      (__smtx_model_push_bindings M N bs).usortDom = N.usortDom
  | N, SmtBindings.nil => by rw [model_push_bindings_nil]
  | N, SmtBindings.cons s T v bs => by
      rw [model_push_bindings_cons, model_push_bindings_usortDom M _ bs]
      rfl

end Smtm

end
