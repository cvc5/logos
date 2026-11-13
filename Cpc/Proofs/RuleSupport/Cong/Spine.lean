module

public import Cpc.Proofs.RuleSupport.Cong.Impl
import all Cpc.Proofs.RuleSupport.Cong.Impl

/-!
# Model-free congruence of application spines

`congEvidenceSpine_eq_true` states congruence for one model and a list of
premises, which is what the `cong` rule needs. This module restates it for a
downstream user that has no premise list: an application spine
`(head x₁ … xₙ)`, written `xs.foldl Term.Apply head`, is equal to
`(head y₁ … yₙ)` in every well-formed model when each `(= xᵢ yᵢ)` is well typed
and true in every well-formed model.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace CongSupport

/-- The equalities `(= x₁ y₁) … (= xₙ yₙ)` that justify a spine congruence. -/
def congSpinePremises : List Term -> List Term -> List Term
  | x :: xs, y :: ys => mkEq x y :: congSpinePremises xs ys
  | _, _ => []

/-- Every premise of `congSpinePremises xs ys` is a pairwise equality `(= x y)`
satisfying the pointwise relation. -/
private theorem congSpinePremises_forall
    {R : Term -> Term -> Prop} {P : Term -> Prop}
    (hP : ∀ x y, R x y -> P (mkEq x y)) :
    ∀ {xs ys : List Term}, List.Forall₂ R xs ys ->
      ∀ p ∈ congSpinePremises xs ys, P p := by
  intro xs ys h
  induction h with
  | nil => simp [congSpinePremises]
  | cons hxy _ ih =>
      intro p hp
      simp only [congSpinePremises, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hP _ _ hxy
      · exact ih p hp

/-- An evidence spine over `xs` and `ys`, extending one between the heads. -/
theorem congEvidenceSpine_foldl
    (M : SmtModel) (P : List Term) {R : Term -> Term -> Prop}
    (hR : ∀ x y, R x y -> eo_interprets M (mkEq x y) true) :
    ∀ {h₁ h₂ : Term} {xs ys : List Term},
      CongEvidenceSpine M P h₁ h₂ ->
      List.Forall₂ R xs ys ->
      (∀ p ∈ congSpinePremises xs ys, p ∈ P) ->
      CongEvidenceSpine M P (xs.foldl Term.Apply h₁) (ys.foldl Term.Apply h₂) := by
  intro h₁ h₂ xs ys hh h hsub
  induction h generalizing h₁ h₂ with
  | nil => exact hh
  | @cons x y xs ys hxy _ ih =>
      refine ih (CongEvidenceSpine.app hh
        (hsub _ (by simp [congSpinePremises])) (hR x y hxy)) ?_
      intro p hp
      exact hsub p (by simp [congSpinePremises, hp])

/-- A type spine over `xs` and `ys`, extending one between the heads. -/
theorem congTypeSpine_foldl {R : Term -> Term -> Prop}
    (hR : ∀ x y, R x y -> RuleProofs.eo_has_bool_type (mkEq x y)) :
    ∀ {h₁ h₂ : Term} {xs ys : List Term},
      CongTypeSpine h₁ h₂ -> List.Forall₂ R xs ys ->
      CongTypeSpine (xs.foldl Term.Apply h₁) (ys.foldl Term.Apply h₂) := by
  intro h₁ h₂ xs ys hh h
  induction h generalizing h₁ h₂ with
  | nil => exact hh
  | cons hxy _ ih => exact ih (CongTypeSpine.app hh (hR _ _ hxy))

/--
Model-free congruence of application spines. If `(head x₁ … xₙ)` is well typed
and each `(= xᵢ yᵢ)` is well typed and true in every well-formed model, then
`(= (head x₁ … xₙ) (head y₁ … yₙ))` is well typed and true in every well-formed
model. Any head is allowed, including a partial application such as
`(forall xs)`.
-/
theorem cong_spine_valid (head : Term) (xs ys : List Term) :
    RuleProofs.eo_has_smt_translation (xs.foldl Term.Apply head) ->
    List.Forall₂ (fun x y =>
      RuleProofs.eo_has_bool_type (mkEq x y) ∧
      ∀ M, model_wf M -> eo_interprets M (mkEq x y) true) xs ys ->
    RuleProofs.eo_has_bool_type
        (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head)) ∧
      ∀ M, model_wf M ->
        eo_interprets M
          (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head)) true := by
  intro hTrans h
  have hBool :
      RuleProofs.eo_has_bool_type
        (mkEq (xs.foldl Term.Apply head) (ys.foldl Term.Apply head)) :=
    congTypeSpine_eq_has_bool_type _ _ hTrans
      (congTypeSpine_foldl (fun _ _ hxy => hxy.1) (CongTypeSpine.refl head) h)
  refine ⟨hBool, fun M hM => ?_⟩
  have hValid :
      ∀ p ∈ congSpinePremises xs ys,
        ∀ N, model_wf N -> eo_interprets N p true :=
    congSpinePremises_forall (fun _ _ hxy => hxy.2) h
  exact congEvidenceSpine_eq_true M hM (congSpinePremises xs ys) _ _
    ⟨fun p hp => hValid p hp M hM, fun N hN _ p hp => hValid p hp N hN⟩ hBool
    (congEvidenceSpine_foldl M _ (fun _ _ hxy => hxy.2 M hM)
      (CongEvidenceSpine.refl head) h (fun _ hp => hp))

end CongSupport
