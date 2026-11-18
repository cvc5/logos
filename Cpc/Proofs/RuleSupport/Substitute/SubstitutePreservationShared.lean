module

public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SubstitutePreservationSupport

theorem eo_and_boolean_true_split
    {a b : Term}
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at h ⊢
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [native_and] at h ⊢
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hW : w₁ = w₂ <;> simp [hW] at h

theorem eo_to_smt_typeof_ne_none_of_has_smt_translation
    (X : Term)
    (hX : RuleProofs.eo_has_smt_translation X) :
    __eo_to_smt_type (__eo_typeof X) ≠ SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hX
  unfold RuleProofs.eo_has_smt_translation at hX
  intro hNone
  rw [hXSmt, hNone] at hX
  exact hX rfl

theorem smt_typeof_binary_one_one :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  decide +kernel

theorem smt_typeof_binary_one_zero :
    __smtx_typeof (SmtTerm.Binary 1 0) = SmtType.BitVec 1 := by
  decide +kernel

end SubstitutePreservationSupport
