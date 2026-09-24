module

public import CpcMini.Proofs.TypePreservation.Predicates
import all CpcMini.Proofs.TypePreservation.Predicates
public import CpcMini.Proofs.Canonical.TypeDefaultBasic
import all CpcMini.Proofs.Canonical.TypeDefaultBasic

public section

open SmtEval
open Smtm

namespace Smtm

/--
Datatype-default canonicity for the generated Mini model.

The theorem keeps the historical `_assumption` name used by the downstream
proof skeleton. Typing is extracted from `native_inhabited_type`; canonicity
follows from the recursive datatype well-formedness hypothesis.
-/
theorem cpcmini_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatypeDecl)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  classical
  have hTyped : native_Teq (__smtx_typeof_value
      (__smtx_type_default (SmtType.Datatype s d))) (SmtType.Datatype s d) = true := by
    have h2 := _hInh
    simp only [native_inhabited_type, native_and, Bool.and_eq_true] at h2
    exact h2.2
  refine ⟨of_decide_eq_true (by simpa [native_Teq] using hTyped), ?_⟩
  -- Canonicity follows from recursive well-formedness of the datatype block.
  simpa [value_canonical] using
    type_default_canonical_of_inhabited_wf_rec
      (SmtType.Datatype s d) _hInh _hRec

end Smtm
