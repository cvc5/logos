module

public import CpcMini.Proofs.Common
import all CpcMini.Proofs.Common
public import CpcMini.Proofs.Assumptions
import all CpcMini.Proofs.Assumptions

@[expose] public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
# The checker/rule contract

What a rule must prove about its premises and conclusion
(`StepRuleProperties`, `StepPopRuleProperties`, `RulePremiseEvidence`), and the
premise accessors the checker needs in order to state it.

This is the whole of what `CpcMini/Proofs/CheckerState.lean` and its dependants
use from the rule-support layer.  Splitting it out keeps rule-only material --
in particular the `not` and `eq` lemmas of `Proofs/CommonBoolOps.lean` -- out of
the checker's transitive imports.
-/

/-- Collects the proven terms referenced by a premise index list in a checker state. -/
def premiseTermList (s : CState) : CIndexList -> List Term
  | CIndexList.nil => []
  | CIndexList.cons n premises =>
      __eo_state_proven_nth s n :: premiseTermList s premises

/-- Predicate asserting that every term in a list is interpreted as `true` by a model. -/
def AllInterpretedTrue (M : SmtModel) (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_interprets M t true

/--
Two models agree on the global part of the interpretation.

Variables may vary, but user constants and native function interpretations are
kept fixed. This is the model relation used when a binder pushes fresh variable
assignments.
-/
def model_agrees_on_globals (M N : SmtModel) : Prop :=
  (∀ s T, native_model_lookup M s T = native_model_lookup N s T) ∧
  (∀ fid T U, model_fun_lookup M fid T U =
    model_fun_lookup N fid T U)

theorem model_agrees_on_globals_refl (M : SmtModel) :
  model_agrees_on_globals M M :=
by
  exact ⟨by intro s T; rfl, by intro fid T U; rfl⟩

theorem model_agrees_on_globals_trans {M N K : SmtModel} :
  model_agrees_on_globals M N ->
  model_agrees_on_globals N K ->
  model_agrees_on_globals M K :=
by
  intro hMN hNK
  exact
    ⟨by
      intro s T
      exact (hMN.1 s T).trans (hNK.1 s T),
    by
      intro fid T U
      exact (hMN.2 fid T U).trans (hNK.2 fid T U)⟩

/--
Contextual truth for a derived formula.

The first field is the ordinary checker fact in the current model. The second
field is the freshness/parametricity fact needed by binder-sensitive rules:
the derived formula remains true in any model that only changes variables,
provided the same assumptions and local pushes hold there.
-/
structure ContextualTruth
    (M : SmtModel) (assumes pushes P : Term) : Prop where
  true_here :
    eo_interprets M assumes true ->
    eo_interprets M pushes true ->
    eo_interprets M P true
  true_in_var_model :
    ∀ N, model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N assumes true ->
      eo_interprets N pushes true ->
      eo_interprets N P true

/-- The premise evidence supplied to a rule. -/
structure RulePremiseEvidence
    (M : SmtModel) (premises : List Term) : Prop where
  true_here :
    AllInterpretedTrue M premises

instance RulePremiseEvidence.instCoeFun
    {M : SmtModel} {premises : List Term} :
    CoeFun (RulePremiseEvidence M premises)
      (fun _ => ∀ t, t ∈ premises -> eo_interprets M t true) where
  coe h := h.true_here

/-- Predicate asserting that every term in a list has an SMT translation. -/
def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_smt_translation t

/-- Predicate asserting that every term in a list has translated SMT Boolean type. -/
def AllHaveBoolType (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_bool_type t

/-- Predicate asserting that every term in a list has EO type `Bool`. -/
def AllTypeofBool (ts : List Term) : Prop :=
  ∀ t ∈ ts, __eo_typeof t = Term.Bool

/-- A term with EO type `Bool` cannot be `Stuck`. -/
theorem term_ne_stuck_of_typeof_bool
    {t : Term}
    (hTy : __eo_typeof t = Term.Bool) :
    t ≠ Term.Stuck := by
  intro hStuck
  rw [hStuck] at hTy
  have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
    native_decide
  exact hStuckTy hTy

/-- Structure bundling the correctness and translation obligations for rules that only add a proven fact. -/
structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    RulePremiseEvidence M premises ->
    eo_interprets M P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/-- Predicate packaging the correctness and translation obligations for rules that also pop assumptions. -/
def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_wf M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      eo_interprets M P true) ∧
    RuleProofs.eo_has_smt_translation P
