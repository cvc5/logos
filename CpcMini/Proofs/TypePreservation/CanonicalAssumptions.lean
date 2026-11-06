module

public import CpcMini.Proofs.TypePreservation.Predicates
import all CpcMini.Proofs.TypePreservation.Predicates
public import CpcMini.Proofs.Canonical.TypeDefaultBasic
import all CpcMini.Proofs.Canonical.TypeDefaultBasic

public section

variable {uc : SmtUSortDom}

open SmtEval
open Smtm

namespace Smtm

/--
Datatype-default canonicity for the generated Mini model.

The theorem keeps the historical `_assumption` name used by the downstream
proof skeleton. Typing and canonicity both follow from inhabitation together with the
recursive datatype well-formedness hypothesis.
-/
theorem cpcmini_datatype_type_default_typed_canonical_assumption (huc : usort_dom_wf uc)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (_hInh : __smtx_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      value_canonical uc (__smtx_type_default (SmtType.Datatype s d)) := by
  refine ⟨type_default_typed _ _hInh _hRec, ?_⟩
  -- Canonicity follows from recursive well-formedness of the datatype block.
  simpa [value_canonical] using
    type_default_canonical_of_inhabited_wf_rec huc
      (SmtType.Datatype s d) _hInh _hRec

end Smtm
