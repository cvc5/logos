module

public import Cpc.Proofs.ModelEval
import all Cpc.Proofs.ModelEval

public section

variable {uc : native_Nat -> native_Nat}

open SmtEval
open Smtm

namespace Smtm

/-- Semantic inhabitation of an SMT type. -/
def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

/-- Proof-facing canonicality predicate for SMT values. -/
def value_canonical (uc : native_Nat -> native_Nat) (v : SmtValue) : Prop :=
  __smtx_value_canonical uc v = true

end Smtm
