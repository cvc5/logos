module

public import CpcMini.SmtModel
import all CpcMini.SmtModel

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
