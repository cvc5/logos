module

public import CpcMini.Proofs.CommonBoolOps
import all CpcMini.Proofs.CommonBoolOps
public import CpcMini.Proofs.Assumptions
import all CpcMini.Proofs.Assumptions

/-!
# What the checker needs to know about `argListAssumes`

`argListAssumes` (`Proofs/CalculusAssumptions.lean`) is the calculus's choice of
one formula for an input assumption list.  `correct___eo_is_refutation` is
proved about the list and transferred to that formula by the two lemmas here,
which are the calculus's side of the bargain: the formula is Boolean when every
assumption is, and a model that makes it true makes every assumption true.
-/

public section

open Eo
open SmtEval
open Smtm

/-- The formula of a list of Boolean-typed assumptions is Boolean-typed. -/
theorem argListAssumes_has_bool_type (F : CArgList) :
  (∀ A ∈ argListTerms F, RuleProofs.eo_has_bool_type A) ->
  RuleProofs.eo_has_bool_type (argListAssumes F) := by
  induction F with
  | nil =>
      intro _
      exact RuleProofs.eo_has_bool_type_true
  | cons A rest ih =>
      intro hBool
      exact RuleProofs.eo_has_bool_type_and_of_bool_args A (argListAssumes rest)
        (hBool A List.mem_cons_self)
        (ih (fun B hB => hBool B (List.mem_cons_of_mem A hB)))

/-- A model that interprets the formula of a list as `true` interprets every assumption as `true`. -/
theorem argListTerms_true_of_argListAssumes_true (M : SmtModel) (F : CArgList) :
  eo_interprets M (argListAssumes F) true ->
  ∀ A ∈ argListTerms F, eo_interprets M A true := by
  induction F with
  | nil =>
      intro _ A hA
      cases hA
  | cons A rest ih =>
      intro h B hB
      cases hB with
      | head =>
          exact RuleProofs.eo_interprets_and_left M A (argListAssumes rest) h
      | tail _ hB =>
          exact ih (RuleProofs.eo_interprets_and_right M A (argListAssumes rest) h) B hB
