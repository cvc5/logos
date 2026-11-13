module

import Lean
public import CpcMini.Proofs.TypePreservation.Model
import all CpcMini.Proofs.TypePreservation.Model

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Shows that evaluating `boolean` terms produces values of the expected type. -/
theorem typeof_value_model_eval_boolean
    (M : SmtModel)
    (b : native_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `numeral` terms produces values of the expected type. -/
theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : native_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `rational` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `binary` terms produces values of the expected type. -/
theorem typeof_value_model_eval_binary
    (M : SmtModel)
    (w n : native_Int)
    (ht : term_has_non_none_type (SmtTerm.Binary w n)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Binary w n)) =
      __smtx_typeof (SmtTerm.Binary w n) := by
  unfold term_has_non_none_type at ht
  let g :=
    native_and (native_zleq 0 w)
      (native_zeq n (native_mod_total n (native_int_pow2 w)))
  have hg : g = true := by
    by_cases h : g = true
    · exact h
    · exfalso
      apply ht
      simp [__smtx_typeof, g, native_ite, h]
  have hWidth : native_zleq 0 w = true := by
    cases h1 : native_zleq 0 w
    · simp [g, SmtEval.native_and, h1] at hg
    · rfl
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases h2 : native_zeq n (native_mod_total n (native_int_pow2 w))
    · simp [g, SmtEval.native_and, hWidth, h2] at hg
    · rfl
  simp [__smtx_model_eval, __smtx_typeof_value, __smtx_typeof, native_ite, SmtEval.native_and, hWidth, hMod]

/-- Shows that evaluating `var` terms produces values of the expected type. -/
theorem typeof_value_model_eval_var
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Var s T)) =
      __smtx_typeof (SmtTerm.Var s T) := by
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  simpa [__smtx_model_eval, __smtx_typeof] using
    (Eq.trans (model_total_typed_var_lookup hM s T hWF) hGuard.symm)

/-- Shows that evaluating `uconst` terms produces values of the expected type. -/
theorem typeof_value_model_eval_uconst
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.UConst s T)) =
      __smtx_typeof (SmtTerm.UConst s T) := by
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  simpa [__smtx_model_eval, __smtx_typeof] using
    (Eq.trans (model_total_typed_lookup hM s T hWF) hGuard.symm)

end Smtm
