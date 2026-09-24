module

public import Cpc.Proofs.Canonical.Maps
import all Cpc.Proofs.Canonical.Maps
public import Cpc.Proofs.Canonical.Seq
import all Cpc.Proofs.Canonical.Seq
import Cpc.Proofs.TypePreservation.Datatypes
import all Cpc.Proofs.TypePreservation.Datatypes

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Value-level SMT equality always returns a canonical Boolean value. -/
theorem model_eval_eq_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_eq v1 v2) :=
  value_canonical_of_bool_type (typeof_value_model_eval_eq_value v1 v2)

/-- Value-level Boolean negation always returns a canonical value. -/
theorem model_eval_not_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_not v) := by
  cases v <;>
    simp [__smtx_model_eval_not, value_canonical,
      __smtx_value_canonical]

/-- Value-level Boolean disjunction always returns a canonical value. -/
theorem model_eval_or_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_or v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_or, value_canonical,
      __smtx_value_canonical]

/-- Value-level Boolean conjunction always returns a canonical value. -/
theorem model_eval_and_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_and v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_and, value_canonical,
      __smtx_value_canonical]

/-- Value-level implication always returns a canonical value. -/
theorem model_eval_imp_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_imp v1 v2) := by
  simpa [__smtx_model_eval_imp] using
    model_eval_or_canonical (__smtx_model_eval_not v1) v2

/-- Value-level xor always returns a canonical value. -/
theorem model_eval_xor_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_xor v1 v2) := by
  simpa [__smtx_model_eval_xor] using
    model_eval_not_canonical (__smtx_model_eval_eq v1 v2)

/-- Value-level arithmetic addition always returns a canonical value. -/
theorem model_eval_plus_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_plus v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_plus, value_canonical,
      __smtx_value_canonical]

/-- Value-level arithmetic subtraction always returns a canonical value. -/
theorem model_eval_sub_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval__ v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval__, value_canonical,
      __smtx_value_canonical]

/-- Value-level arithmetic multiplication always returns a canonical value. -/
theorem model_eval_mult_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_mult v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_mult, value_canonical,
      __smtx_value_canonical]

/-- Value-level less-than always returns a canonical value. -/
theorem model_eval_lt_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_lt v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_lt, value_canonical,
      __smtx_value_canonical]

/-- Value-level less-or-equal always returns a canonical value. -/
theorem model_eval_leq_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_leq v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_leq, value_canonical,
      __smtx_value_canonical]

theorem model_eval_gt_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_gt v1 v2) := by
  simpa [__smtx_model_eval_gt] using model_eval_lt_canonical v2 v1

theorem model_eval_geq_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_geq v1 v2) := by
  simpa [__smtx_model_eval_geq] using model_eval_leq_canonical v2 v1

theorem model_eval_to_real_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_to_real v) := by
  cases v <;>
    simp [__smtx_model_eval_to_real, value_canonical,
      __smtx_value_canonical]

theorem model_eval_to_int_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_to_int, value_canonical,
      __smtx_value_canonical]

theorem model_eval_is_int_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_is_int v) := by
  simpa [__smtx_model_eval_is_int] using
    model_eval_eq_canonical (__smtx_model_eval_to_real (__smtx_model_eval_to_int v)) v

theorem model_eval_abs_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_abs v) := by
  cases v <;>
    simp [__smtx_model_eval_abs, value_canonical, __smtx_value_canonical]

theorem model_eval_uneg_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_uneg v) := by
  cases v <;>
    simp [__smtx_model_eval_uneg, value_canonical,
      __smtx_value_canonical]

theorem model_eval_divisible_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_divisible v1 v2) := by
  simpa [__smtx_model_eval_divisible] using
    model_eval_eq_canonical (__smtx_model_eval_mod_total v2 v1) (SmtValue.Numeral 0)

theorem model_eval_int_pow2_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_int_pow2 v) := by
  cases v <;>
    simp [__smtx_model_eval_int_pow2, value_canonical,
      __smtx_value_canonical]

theorem model_eval_int_log2_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_int_log2 v) := by
  cases v <;>
    simp [__smtx_model_eval_int_log2, value_canonical,
      __smtx_value_canonical]

theorem model_eval_div_total_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_div_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_div_total, value_canonical,
      __smtx_value_canonical]

theorem model_eval_mod_total_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_mod_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_mod_total, value_canonical,
      __smtx_value_canonical]

theorem model_eval_qdiv_total_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_qdiv_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_qdiv_total, value_canonical,
      __smtx_value_canonical]

theorem model_eval_apply_fun_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (fid : native_String)
    (A B : SmtType)
    (x : SmtValue)
    (hxTy : __smtx_typeof_value x = A)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true) :
    value_canonical (__smtx_model_eval_apply M (SmtValue.Fun fid A B) x) := by
  by_cases hxNot : x = SmtValue.NotValue
  · subst x
    have hAWF : __smtx_type_wf A = true := (fun_type_wf_components_of_wf hFunWF).1
    have hANN : A ≠ SmtType.None := type_wf_non_none hAWF
    simp [__smtx_typeof_value] at hxTy
    exact False.elim (hANN hxTy.symm)
  · have hCan :
        value_canonical (native_eval_fun_apply M fid A B x) :=
      (model_total_typed_native_fun_typed hM fid A B x hFunWF hxTy).2
    have hApply :
        __smtx_model_eval_apply M (SmtValue.Fun fid A B) x =
          native_eval_fun_apply M fid A B x := by
      cases x <;> simp [__smtx_model_eval_apply] at hxNot ⊢
    simpa [hApply] using hCan

private theorem model_eval_apply_not_value_canonical
    (M : SmtModel) (x : SmtValue) :
    value_canonical (__smtx_model_eval_apply M SmtValue.NotValue x) := by
  cases x <;>
    simp [__smtx_model_eval_apply, value_canonical,
      __smtx_value_canonical]

theorem model_eval_apply_lookup_fun_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (A B : SmtType)
    (x : SmtValue)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true)
    (hxTy : __smtx_typeof_value x = A) :
    value_canonical
      (__smtx_model_eval_apply M
        (native_model_lookup M s (SmtType.FunType A B)) x) := by
  have hLookupTy :
      __smtx_typeof_value (native_model_lookup M s (SmtType.FunType A B)) =
        SmtType.FunType A B :=
    model_total_typed_lookup hM s (SmtType.FunType A B) hFunWF
  have hLookupCan :
      value_canonical (native_model_lookup M s (SmtType.FunType A B)) :=
    model_total_typed_lookup_canonical hM s (SmtType.FunType A B) hFunWF
  rcases fun_value_canonical hLookupTy with ⟨fid, hLookupEq⟩
  rw [hLookupEq] at hLookupCan ⊢
  exact model_eval_apply_fun_canonical M hM fid A B x hxTy hFunWF

theorem model_eval_apply_canonical
    (M : SmtModel)
    (hM : model_wf M)
    {f x : SmtValue}
    {A B : SmtType}
    (hHead :
      __smtx_typeof_value f = SmtType.FunType A B ∨
        __smtx_typeof_value f = SmtType.DtcAppType A B)
    (hFunWF :
      __smtx_typeof_value f = SmtType.FunType A B ->
        __smtx_type_wf (SmtType.FunType A B) = true)
    (hxTy : __smtx_typeof_value x = A)
    (hf : value_canonical f)
    (hx : value_canonical x) :
    value_canonical (__smtx_model_eval_apply M f x) := by
  cases hHead with
  | inl hFun =>
      rcases fun_value_canonical hFun with ⟨fid, rfl⟩
      exact model_eval_apply_fun_canonical M hM fid A B x hxTy (hFunWF rfl)
  | inr hDtc =>
      cases f <;> cases x <;>
        simp [__smtx_model_eval_apply, __smtx_typeof_value,
          value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hDtc hf hx ⊢
      all_goals
        first
        | assumption
        | constructor <;> assumption

/-- Value-level SMT `ite` preserves canonicality of the selected branch. -/
theorem model_eval_ite_canonical
    {c t e : SmtValue}
    (ht : value_canonical t)
    (he : value_canonical e) :
    value_canonical (__smtx_model_eval_ite c t e) := by
  cases c <;>
    try
      simpa [__smtx_model_eval_ite] using value_canonical_notValue
  · cases ‹native_Bool› <;>
      simp [__smtx_model_eval_ite, ht, he]

theorem value_canonical_binary_mod
    (w n : native_Int) :
    value_canonical
      (SmtValue.Binary w (native_mod_total n (native_int_pow2 w))) := by
  cases hw : native_zleq 0 w <;>
    simp [value_canonical, __smtx_value_canonical, native_ite,
      hw, native_mod_total_canonical]

theorem model_eval_concat_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_concat v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_concat, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_extract_canonical
    (v1 v2 v3 : SmtValue) :
    value_canonical (__smtx_model_eval_extract v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_extract, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_repeat_rec_canonical :
    ∀ n v, value_canonical (__smtx_repeat_rec n v)
  | native_nat_zero, v => by
      simp [__smtx_repeat_rec, value_canonical,
        __smtx_value_canonical, native_ite, native_zleq, native_zeq,
        native_mod_total, native_int_pow2, native_zexp_total]
  | native_nat_succ n, v => by
      simpa [__smtx_repeat_rec] using
        model_eval_concat_canonical v (__smtx_repeat_rec n v)

theorem model_eval_repeat_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_repeat v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_repeat, value_canonical_notValue,
      model_eval_repeat_rec_canonical]

theorem model_eval_bvnot_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_bvnot v) := by
  cases v <;>
    simp [__smtx_model_eval_bvnot, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvand_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvand v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvand, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvor_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvor v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvor, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvxor_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvxor v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvxor, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvnand_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvnand v1 v2) := by
  simpa [__smtx_model_eval_bvnand] using
    model_eval_bvnot_canonical (__smtx_model_eval_bvand v1 v2)

theorem model_eval_bvnor_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvnor v1 v2) := by
  simpa [__smtx_model_eval_bvnor] using
    model_eval_bvnot_canonical (__smtx_model_eval_bvor v1 v2)

theorem model_eval_bvxnor_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvxnor v1 v2) := by
  simpa [__smtx_model_eval_bvxnor] using
    model_eval_bvnot_canonical (__smtx_model_eval_bvxor v1 v2)

theorem model_eval_bvcomp_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvcomp v1 v2) := by
  simpa [__smtx_model_eval_bvcomp] using
    model_eval_ite_canonical
      (t := SmtValue.Binary 1 1)
      (e := SmtValue.Binary 1 0)
      (by simp [value_canonical, __smtx_value_canonical, native_ite,
        native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total])
      (by simp [value_canonical, __smtx_value_canonical, native_ite,
        native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total])

theorem model_eval_bvneg_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_bvneg v) := by
  cases v <;>
    simp [__smtx_model_eval_bvneg, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvadd_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvadd v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvadd, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvmul_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvmul v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvmul, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvudiv_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvudiv v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvudiv, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvurem_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvurem v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvurem, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvsub_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsub v1 v2) := by
  simpa [__smtx_model_eval_bvsub] using
    model_eval_bvadd_canonical v1 (__smtx_model_eval_bvneg v2)

theorem model_eval_bvugt_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvugt v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvugt, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvult_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvult v1 v2) := by
  simpa [__smtx_model_eval_bvult] using model_eval_bvugt_canonical v2 v1

theorem model_eval_bvuge_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvuge v1 v2) := by
  simpa [__smtx_model_eval_bvuge] using
    model_eval_or_canonical (__smtx_model_eval_bvugt v1 v2) (__smtx_model_eval_eq v1 v2)

theorem model_eval_bvule_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvule v1 v2) := by
  simpa [__smtx_model_eval_bvule] using model_eval_bvuge_canonical v2 v1

theorem model_eval_bvshl_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvshl v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvshl, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvlshr_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvlshr v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvlshr, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_sign_extend_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_sign_extend v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_sign_extend, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_int_to_bv_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_int_to_bv v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_int_to_bv, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_ubv_to_int_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_ubv_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_ubv_to_int, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_sbv_to_int_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_sbv_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_sbv_to_int, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_bvuaddo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvuaddo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvuaddo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvnego_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_bvnego v) := by
  cases v <;>
    simp [__smtx_model_eval_bvnego, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvsaddo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsaddo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvsaddo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvumulo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvumulo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvumulo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvsmulo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsmulo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvsmulo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvusubo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvusubo v1 v2) := by
  simpa [__smtx_model_eval_bvusubo] using model_eval_bvult_canonical v1 v2

theorem model_eval_bvsgt_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsgt v1 v2) := by
  simpa [__smtx_model_eval_bvsgt] using
    model_eval_or_canonical
      (__smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              v1)
            (SmtValue.Binary 1 1)))
        (__smtx_model_eval_eq
          (__smtx_model_eval_extract
            (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
              (SmtValue.Numeral 1))
            (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
              (SmtValue.Numeral 1))
            v2)
          (SmtValue.Binary 1 1)))
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              v1)
            (SmtValue.Binary 1 1))
          (__smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
                (SmtValue.Numeral 1))
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
                (SmtValue.Numeral 1))
              v2)
            (SmtValue.Binary 1 1)))
        (__smtx_model_eval_bvugt v1 v2))

theorem model_eval_bvslt_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvslt v1 v2) := by
  simpa [__smtx_model_eval_bvslt] using model_eval_bvsgt_canonical v2 v1

theorem model_eval_bvsge_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsge v1 v2) := by
  simpa [__smtx_model_eval_bvsge] using
    model_eval_or_canonical (__smtx_model_eval_bvsgt v1 v2) (__smtx_model_eval_eq v1 v2)

theorem model_eval_bvsle_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsle v1 v2) := by
  simpa [__smtx_model_eval_bvsle] using model_eval_bvsge_canonical v2 v1

theorem model_eval_bvsdiv_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsdiv v1 v2) := by
  unfold __smtx_model_eval_bvsdiv
  repeat first
    | apply model_eval_ite_canonical
    | exact model_eval_bvudiv_canonical _ _
    | exact model_eval_bvneg_canonical _

theorem model_eval_bvsrem_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsrem v1 v2) := by
  unfold __smtx_model_eval_bvsrem
  repeat first
    | apply model_eval_ite_canonical
    | exact model_eval_bvurem_canonical _ _
    | exact model_eval_bvneg_canonical _

theorem model_eval_bvsmod_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsmod v1 v2) := by
  unfold __smtx_model_eval_bvsmod
  repeat first
    | apply model_eval_ite_canonical
    | exact model_eval_bvurem_canonical _ _
    | exact model_eval_bvneg_canonical _
    | exact model_eval_bvadd_canonical _ _

theorem model_eval_bvashr_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvashr v1 v2) := by
  unfold __smtx_model_eval_bvashr
  exact model_eval_ite_canonical
    (model_eval_bvlshr_canonical v1 v2)
    (model_eval_bvnot_canonical (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot v1) v2))

theorem model_eval_bvssubo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvssubo v1 v2) := by
  unfold __smtx_model_eval_bvssubo
  exact model_eval_ite_canonical
    (model_eval_bvsge_canonical v1 (SmtValue.Binary (__smtx_bv_sizeof_value v1) 0))
    (model_eval_bvsaddo_canonical v1 (__smtx_model_eval_bvneg v2))

theorem model_eval_bvsdivo_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_bvsdivo v1 v2) := by
  simpa [__smtx_model_eval_bvsdivo] using
    model_eval_and_canonical
      (__smtx_model_eval_bvnego v1)
      (__smtx_model_eval_eq v2
        (__smtx_model_eval_bvnot (SmtValue.Binary (__smtx_bv_sizeof_value v1) 0)))

theorem model_eval_rotate_left_rec_canonical :
    ∀ n v,
      value_canonical v ->
        value_canonical (__smtx_rotate_left_rec n v)
  | native_nat_zero, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_rotate_left_rec] using hv
      | _ =>
          simp [__smtx_rotate_left_rec, value_canonical_notValue]
  | native_nat_succ n, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_rotate_left_rec] using
            model_eval_rotate_left_rec_canonical n
              (__smtx_model_eval_concat
                (__smtx_model_eval_extract
                  (SmtValue.Numeral (native_zplus (native_zplus w (native_zneg 1)) (native_zneg 1)))
                  (SmtValue.Numeral 0) (SmtValue.Binary w x))
                (__smtx_model_eval_extract
                  (SmtValue.Numeral (native_zplus w (native_zneg 1)))
                  (SmtValue.Numeral (native_zplus w (native_zneg 1))) (SmtValue.Binary w x)))
              (model_eval_concat_canonical _ _)
      | _ =>
          simp [__smtx_rotate_left_rec, value_canonical_notValue]

theorem model_eval_rotate_right_rec_canonical :
    ∀ n v,
      value_canonical v ->
        value_canonical (__smtx_rotate_right_rec n v)
  | native_nat_zero, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_rotate_right_rec] using hv
      | _ =>
          simp [__smtx_rotate_right_rec, value_canonical_notValue]
  | native_nat_succ n, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_rotate_right_rec] using
            model_eval_rotate_right_rec_canonical n
              (__smtx_model_eval_concat
                (__smtx_model_eval_extract (SmtValue.Numeral 0)
                  (SmtValue.Numeral 0) (SmtValue.Binary w x))
                (__smtx_model_eval_extract
                  (SmtValue.Numeral (native_zplus w (native_zneg 1)))
                  (SmtValue.Numeral 1) (SmtValue.Binary w x)))
              (model_eval_concat_canonical _ _)
      | _ =>
          simp [__smtx_rotate_right_rec, value_canonical_notValue]

theorem model_eval_rotate_left_canonical
    (v1 v2 : SmtValue)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_rotate_left v1 v2) := by
  cases v1 with
  | Numeral n =>
      simpa [__smtx_model_eval_rotate_left] using
        model_eval_rotate_left_rec_canonical (native_int_to_nat n) v2 hv2
  | _ =>
      simp [__smtx_model_eval_rotate_left, value_canonical_notValue]

theorem model_eval_rotate_right_canonical
    (v1 v2 : SmtValue)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_rotate_right v1 v2) := by
  cases v1 with
  | Numeral n =>
      simpa [__smtx_model_eval_rotate_right] using
        model_eval_rotate_right_rec_canonical (native_int_to_nat n) v2 hv2
  | _ =>
      simp [__smtx_model_eval_rotate_right, value_canonical_notValue]

/-- Literal strings evaluate to canonical sequence values. -/
theorem model_eval_string_value_canonical
    (s : native_String)
    (hs : native_string_valid s = true) :
    value_canonical (SmtValue.Seq (native_pack_string s)) :=
  value_canonical_string s hs

theorem model_eval_seq_empty_value_canonical
    (T : SmtType) :
    value_canonical (SmtValue.Seq (SmtSeq.empty T)) :=
  value_canonical_seq_empty T

theorem model_eval_seq_unit_value_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical
      (SmtValue.Seq (SmtSeq.cons v (SmtSeq.empty (__smtx_typeof_value v)))) := by
  exact value_canonical_seq_cons hv (seq_canonical_empty (__smtx_typeof_value v))

theorem model_eval_str_concat_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_str_concat v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_str_concat] using value_canonical_notValue
  case Seq.Seq s1 s2 =>
    have hs1 : __smtx_seq_canonical s1 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv1
    have hs2 : __smtx_seq_canonical s2 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv2
    simpa [__smtx_model_eval_str_concat, value_canonical,
      __smtx_value_canonical, native_seq_concat] using
      seq_canonical_pack_unpack_concat (__smtx_elem_typeof_seq_value s1)
        hs1 hs2

theorem model_eval_str_rev_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_str_rev v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_rev] using value_canonical_notValue
  · have hs : __smtx_seq_canonical ‹SmtSeq› = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    simpa [__smtx_model_eval_str_rev, value_canonical,
      __smtx_value_canonical, native_seq_rev] using
      seq_canonical_pack_unpack_reverse (__smtx_elem_typeof_seq_value ‹SmtSeq›) hs

set_option maxHeartbeats 200000

theorem model_eval_str_substr_canonical
    {v i n : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_str_substr v i n) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_substr] using value_canonical_notValue
  case Seq s =>
    cases i <;>
      try
        simpa [__smtx_model_eval_str_substr] using value_canonical_notValue
    case Numeral start =>
      cases n <;>
        try
          simpa [__smtx_model_eval_str_substr] using value_canonical_notValue
      case Numeral len =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [value_canonical, __smtx_value_canonical] using hv
        simpa [__smtx_model_eval_str_substr, value_canonical,
          __smtx_value_canonical] using
          seq_canonical_pack_unpack_extract (__smtx_elem_typeof_seq_value s)
            hs start len

theorem model_eval_str_replace_canonical
    {v pat repl : SmtValue}
    (hv : value_canonical v)
    (hpat : value_canonical pat)
    (hrepl : value_canonical repl) :
    value_canonical (__smtx_model_eval_str_replace v pat repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace] using value_canonical_notValue
  case Seq s =>
    cases pat <;>
      try
        simpa [__smtx_model_eval_str_replace] using value_canonical_notValue
    case Seq p =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_replace] using value_canonical_notValue
      case Seq r =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [value_canonical, __smtx_value_canonical] using hv
        have hpatSeq : __smtx_seq_canonical p = true := by
          simpa [value_canonical, __smtx_value_canonical] using hpat
        have hreplSeq : __smtx_seq_canonical r = true := by
          simpa [value_canonical, __smtx_value_canonical] using hrepl
        simpa [__smtx_model_eval_str_replace, value_canonical,
          __smtx_value_canonical] using
          seq_canonical_pack_unpack_replace (__smtx_elem_typeof_seq_value s)
            hs hpatSeq hreplSeq

theorem model_eval_str_at_canonical
    {v i : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_str_at v i) := by
  simpa [__smtx_model_eval_str_at] using
    model_eval_str_substr_canonical (v := v) (i := i) (n := SmtValue.Numeral 1) hv

theorem model_eval_str_update_canonical
    {v i repl : SmtValue}
    (hv : value_canonical v)
    (hrepl : value_canonical repl) :
    value_canonical (__smtx_model_eval_str_update v i repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_update] using value_canonical_notValue
  case Seq s =>
    cases i <;>
      try
        simpa [__smtx_model_eval_str_update] using value_canonical_notValue
    case Numeral n =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_update] using value_canonical_notValue
      case Seq r =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [value_canonical, __smtx_value_canonical] using hv
        have hreplSeq : __smtx_seq_canonical r = true := by
          simpa [value_canonical, __smtx_value_canonical] using hrepl
        simpa [__smtx_model_eval_str_update, value_canonical,
          __smtx_value_canonical] using
          seq_canonical_pack_unpack_update (__smtx_elem_typeof_seq_value s)
            hs hreplSeq n

theorem model_eval_str_to_lower_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_str_to_lower v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_to_lower] using value_canonical_notValue
  case Seq s =>
    have hs : __smtx_seq_canonical s = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    have hValid :
        native_string_valid (native_str_to_lower (native_unpack_string s)) = true :=
      native_str_to_lower_valid (native_unpack_string_valid_of_seq_canonical hs)
    simpa [__smtx_model_eval_str_to_lower, value_canonical,
      __smtx_value_canonical] using
      seq_canonical_pack_string (native_str_to_lower (native_unpack_string s)) hValid

theorem model_eval_str_to_upper_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_str_to_upper v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_to_upper] using value_canonical_notValue
  case Seq s =>
    have hs : __smtx_seq_canonical s = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    have hValid :
        native_string_valid (native_str_to_upper (native_unpack_string s)) = true :=
      native_str_to_upper_valid (native_unpack_string_valid_of_seq_canonical hs)
    simpa [__smtx_model_eval_str_to_upper, value_canonical,
      __smtx_value_canonical] using
      seq_canonical_pack_string (native_str_to_upper (native_unpack_string s)) hValid

theorem model_eval_str_from_code_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_str_from_code v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_from_code] using value_canonical_notValue
  case Numeral n =>
    simpa [__smtx_model_eval_str_from_code, value_canonical,
      __smtx_value_canonical] using
      seq_canonical_pack_string (native_str_from_code n)
        (native_str_from_code_valid n)

theorem model_eval_str_from_int_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_str_from_int v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_from_int] using value_canonical_notValue
  case Numeral n =>
    simpa [__smtx_model_eval_str_from_int, value_canonical,
      __smtx_value_canonical] using
      seq_canonical_pack_string (native_str_from_int n)
        (native_str_from_int_valid n)

theorem model_eval_str_replace_all_canonical
    {v pat repl : SmtValue}
    (hv : value_canonical v)
    (hpat : value_canonical pat)
    (hrepl : value_canonical repl) :
    value_canonical (__smtx_model_eval_str_replace_all v pat repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace_all] using value_canonical_notValue
  case Seq s =>
    cases pat <;>
      try
        simpa [__smtx_model_eval_str_replace_all] using value_canonical_notValue
    case Seq p =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_replace_all] using value_canonical_notValue
      case Seq r =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [value_canonical, __smtx_value_canonical] using hv
        have hpatSeq : __smtx_seq_canonical p = true := by
          simpa [value_canonical, __smtx_value_canonical] using hpat
        have hreplSeq : __smtx_seq_canonical r = true := by
          simpa [value_canonical, __smtx_value_canonical] using hrepl
        simpa [__smtx_model_eval_str_replace_all, value_canonical,
          __smtx_value_canonical] using
          seq_canonical_pack_unpack_replace_all (__smtx_elem_typeof_seq_value s)
            hs hpatSeq hreplSeq

theorem model_eval_str_replace_re_canonical
    {v repl : SmtValue}
    (re : SmtValue)
    (hv : value_canonical v)
    (hrepl : value_canonical repl) :
    value_canonical (__smtx_model_eval_str_replace_re v re repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace_re] using value_canonical_notValue
  case Seq s =>
    cases re <;>
      try
        simpa [__smtx_model_eval_str_replace_re] using value_canonical_notValue
    case RegLan r =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_replace_re] using value_canonical_notValue
      case Seq replacement =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [value_canonical, __smtx_value_canonical] using hv
        have hreplacement :
            __smtx_seq_canonical replacement = true := by
          simpa [value_canonical, __smtx_value_canonical] using hrepl
        simpa [__smtx_model_eval_str_replace_re, value_canonical,
          __smtx_value_canonical] using
          seq_canonical_pack_unpack_replace_re
            (__smtx_elem_typeof_seq_value s) r hs hreplacement

theorem model_eval_str_replace_re_all_canonical
    {v repl : SmtValue}
    (re : SmtValue)
    (hv : value_canonical v)
    (hrepl : value_canonical repl) :
    value_canonical (__smtx_model_eval_str_replace_re_all v re repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace_re_all] using value_canonical_notValue
  case Seq s =>
    cases re <;>
      try
        simpa [__smtx_model_eval_str_replace_re_all] using value_canonical_notValue
    case RegLan r =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_replace_re_all] using value_canonical_notValue
      case Seq replacement =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [value_canonical, __smtx_value_canonical] using hv
        have hreplacement :
            __smtx_seq_canonical replacement = true := by
          simpa [value_canonical, __smtx_value_canonical] using hrepl
        simpa [__smtx_model_eval_str_replace_re_all, value_canonical,
          __smtx_value_canonical] using
          seq_canonical_pack_unpack_replace_re_all
            (__smtx_elem_typeof_seq_value s) r hs hreplacement

theorem model_eval_str_len_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_str_len v) := by
  cases v <;>
    simp [__smtx_model_eval_str_len, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_contains_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_str_contains v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_str_contains, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_str_indexof_canonical
    (v1 v2 v3 : SmtValue) :
    value_canonical (__smtx_model_eval_str_indexof v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_str_indexof, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_indexof_re_canonical
    (v1 v2 v3 : SmtValue) :
    value_canonical (__smtx_model_eval_str_indexof_re v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_str_indexof_re, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_at_strings_occur_index_canonical
    (v1 v2 v3 : SmtValue) :
    value_canonical (__smtx_model_eval__at_strings_occur_index v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval__at_strings_occur_index, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_at_strings_occur_index_re_canonical
    (v1 v2 v3 : SmtValue) :
    value_canonical (__smtx_model_eval__at_strings_occur_index_re v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval__at_strings_occur_index_re, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_indexof_re_split_canonical
    (v1 v2 v3 : SmtValue) :
    value_canonical (__smtx_model_eval_str_indexof_re_split v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_str_indexof_re_split, value_canonical_notValue,
      value_canonical_numeral]

theorem model_eval_str_to_code_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_str_to_code v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_code, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_to_int_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_str_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_int, value_canonical_notValue, value_canonical_numeral]

private theorem native_re_mk_star_canonical
    {r : SmtRegLan}
    (hr : __smtx_re_canonical r = true) :
    __smtx_re_canonical (native_re_mk_star r) = true := by
  cases r <;>
    simp_all [native_re_mk_star, native_re_mult, __smtx_re_canonical, native_and]

private theorem native_re_mk_comp_canonical
    {r : SmtRegLan}
    (hr : __smtx_re_canonical r = true) :
    __smtx_re_canonical (native_re_mk_comp r) = true := by
  cases r <;>
    simp_all [native_re_mk_comp, native_re_comp, __smtx_re_canonical, native_and]

private theorem native_re_mk_concat_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_mk_concat r1 r2) = true := by
  cases r1 <;> cases r2 <;>
    simp_all [native_re_mk_concat, native_re_concat, __smtx_re_canonical, native_and]

private theorem native_re_mk_inter_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_mk_inter r1 r2) = true := by
  cases r1 <;> cases r2 <;>
    simp_all [native_re_mk_inter, native_re_inter, __smtx_re_canonical, native_and] <;>
    split <;> simp_all [__smtx_re_canonical, native_and]

private theorem native_re_mk_union_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_mk_union r1 r2) = true := by
  cases r1 <;> cases r2 <;>
    simp_all [native_re_mk_union, native_re_union, __smtx_re_canonical, native_and] <;>
    split <;> simp_all [__smtx_re_canonical, native_and]

private theorem native_re_mult_canonical_of_canonical
    {r : SmtRegLan}
    (hr : __smtx_re_canonical r = true) :
    __smtx_re_canonical (native_re_mult r) = true := by
  exact native_re_mk_star_canonical hr

private theorem native_re_comp_canonical_of_canonical
    {r : SmtRegLan}
    (hr : __smtx_re_canonical r = true) :
    __smtx_re_canonical (native_re_comp r) = true := by
  exact native_re_mk_comp_canonical hr

private theorem native_re_concat_canonical_of_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_concat r1 r2) = true := by
  exact native_re_mk_concat_canonical hr1 hr2

private theorem native_re_inter_canonical_of_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_inter r1 r2) = true := by
  exact native_re_mk_inter_canonical hr1 hr2

private theorem native_re_union_canonical_of_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_union r1 r2) = true := by
  exact native_re_mk_union_canonical hr1 hr2

private theorem native_re_diff_canonical_of_canonical
    {r1 r2 : SmtRegLan}
    (hr1 : __smtx_re_canonical r1 = true)
    (hr2 : __smtx_re_canonical r2 = true) :
    __smtx_re_canonical (native_re_diff r1 r2) = true := by
  simpa [native_re_diff] using
    native_re_mk_inter_canonical hr1 (native_re_mk_comp_canonical hr2)

private theorem native_str_to_re_canonical_of_typed :
    ∀ {s : List SmtValue},
      list_typed SmtType.Char s ->
        __smtx_re_canonical (native_str_to_re s) = true
  | [], _ => by
      simp [native_str_to_re, impl_native_re_of_list, __smtx_re_canonical]
  | v :: vs, hs => by
      rcases hs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, rfl, hc⟩
      simpa [native_str_to_re, impl_native_re_of_list] using
        native_re_mk_concat_canonical
          (r1 := SmtRegLan.char (SmtValue.Char c))
          (r2 := impl_native_re_of_list vs)
          (by simpa [__smtx_re_canonical, native_re_elem_valid] using hc)
          (by simpa [native_str_to_re] using
            native_str_to_re_canonical_of_typed hvs)

private theorem native_re_range_canonical_of_typed
    {s1 s2 : List SmtValue}
    (hs1 : list_typed SmtType.Char s1)
    (hs2 : list_typed SmtType.Char s2) :
    __smtx_re_canonical (native_re_range s1 s2) = true := by
  cases s1 with
  | nil =>
      simp [native_re_range, __smtx_re_canonical]
  | cons c1 s1Tail =>
      cases s1Tail with
      | nil =>
          cases s2 with
          | nil =>
              simp [native_re_range, __smtx_re_canonical]
          | cons c2 s2Tail =>
              cases s2Tail with
              | nil =>
                  rcases hs1 with ⟨hc1, _⟩
                  rcases hs2 with ⟨hc2, _⟩
                  rcases char_value_canonical hc1 with ⟨d1, rfl, hd1⟩
                  rcases char_value_canonical hc2 with ⟨d2, rfl, hd2⟩
                  simp [native_re_range, __smtx_re_canonical, native_and,
                    native_re_elem_valid, hd1, hd2]
              | cons _ _ =>
                  simp [native_re_range, __smtx_re_canonical]
      | cons _ _ =>
          simp [native_re_range, __smtx_re_canonical]

private theorem empty_regex_value_canonical :
    value_canonical
      (SmtValue.RegLan
        (native_str_to_re (native_unpack_seq (SmtSeq.empty SmtType.Char)))) := by
  simp [value_canonical, __smtx_value_canonical,
    native_unpack_seq, native_str_to_re,
    impl_native_re_of_list, __smtx_re_canonical]

theorem model_eval_str_to_re_canonical
    {v : SmtValue}
    (hv : value_canonical v)
    (hTy : __smtx_typeof_value v = SmtType.Seq SmtType.Char) :
    value_canonical (__smtx_model_eval_str_to_re v) := by
  rcases seq_value_canonical hTy with ⟨s, rfl⟩
  have hsTy : __smtx_typeof_seq_value s = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using hTy
  simpa [__smtx_model_eval_str_to_re] using
    value_canonical_reglan
      (native_str_to_re (native_unpack_seq s))
      (native_str_to_re_canonical_of_typed
        (typed_unpack_seq_of_typeof_seq_value hsTy))

theorem model_eval_re_mult_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_re_mult v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_re_mult] using value_canonical_notValue
  case RegLan r =>
    have hr : __smtx_re_canonical r = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    simpa [__smtx_model_eval_re_mult] using
      value_canonical_reglan (native_re_mult r)
        (native_re_mult_canonical_of_canonical hr)

theorem model_eval_re_concat_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_re_concat v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_re_concat] using value_canonical_notValue
  case RegLan.RegLan r1 r2 =>
    have hr1 : __smtx_re_canonical r1 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv1
    have hr2 : __smtx_re_canonical r2 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv2
    simpa [__smtx_model_eval_re_concat] using
      value_canonical_reglan (native_re_concat r1 r2)
        (native_re_concat_canonical_of_canonical hr1 hr2)

theorem model_eval_re_inter_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_re_inter v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_re_inter] using value_canonical_notValue
  case RegLan.RegLan r1 r2 =>
    have hr1 : __smtx_re_canonical r1 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv1
    have hr2 : __smtx_re_canonical r2 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv2
    simpa [__smtx_model_eval_re_inter] using
      value_canonical_reglan (native_re_inter r1 r2)
        (native_re_inter_canonical_of_canonical hr1 hr2)

theorem model_eval_re_union_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_re_union v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_re_union] using value_canonical_notValue
  case RegLan.RegLan r1 r2 =>
    have hr1 : __smtx_re_canonical r1 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv1
    have hr2 : __smtx_re_canonical r2 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv2
    simpa [__smtx_model_eval_re_union] using
      value_canonical_reglan (native_re_union r1 r2)
        (native_re_union_canonical_of_canonical hr1 hr2)

theorem model_eval_re_diff_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_re_diff v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_re_diff] using value_canonical_notValue
  case RegLan.RegLan r1 r2 =>
    have hr1 : __smtx_re_canonical r1 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv1
    have hr2 : __smtx_re_canonical r2 = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv2
    simpa [__smtx_model_eval_re_diff] using
      value_canonical_reglan (native_re_diff r1 r2)
        (native_re_diff_canonical_of_canonical hr1 hr2)

theorem model_eval_re_plus_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_re_plus v) := by
  simpa [__smtx_model_eval_re_plus] using
    model_eval_re_concat_canonical hv (model_eval_re_mult_canonical hv)

theorem model_eval_re_opt_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_re_opt v) := by
  simpa [__smtx_model_eval_re_opt] using
    model_eval_re_union_canonical hv empty_regex_value_canonical

theorem model_eval_re_comp_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_re_comp v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_re_comp] using value_canonical_notValue
  case RegLan r =>
    have hr : __smtx_re_canonical r = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    simpa [__smtx_model_eval_re_comp] using
      value_canonical_reglan (native_re_comp r)
        (native_re_comp_canonical_of_canonical hr)

theorem model_eval_re_range_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2)
    (hTy1 : __smtx_typeof_value v1 = SmtType.Seq SmtType.Char)
    (hTy2 : __smtx_typeof_value v2 = SmtType.Seq SmtType.Char) :
    value_canonical (__smtx_model_eval_re_range v1 v2) := by
  rcases seq_value_canonical hTy1 with ⟨s1, rfl⟩
  rcases seq_value_canonical hTy2 with ⟨s2, rfl⟩
  have hsTy1 : __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using hTy1
  have hsTy2 : __smtx_typeof_seq_value s2 = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using hTy2
  simpa [__smtx_model_eval_re_range] using
    value_canonical_reglan
      (native_re_range (native_unpack_seq s1) (native_unpack_seq s2))
      (native_re_range_canonical_of_typed
        (typed_unpack_seq_of_typeof_seq_value hsTy1)
        (typed_unpack_seq_of_typeof_seq_value hsTy2))

theorem model_eval_re_exp_rec_canonical :
    ∀ n {v}, value_canonical v ->
      value_canonical (__smtx_re_exp_rec n v)
  | native_nat_zero, v, _hv => by
      simpa [__smtx_re_exp_rec] using empty_regex_value_canonical
  | native_nat_succ n, v, hv => by
      simpa [__smtx_re_exp_rec] using
        model_eval_re_concat_canonical
          (model_eval_re_exp_rec_canonical n hv) hv

theorem model_eval_re_exp_canonical
    (v1 : SmtValue)
    {v2 : SmtValue}
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_re_exp v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_re_exp] using value_canonical_notValue
  case Numeral.RegLan n r =>
    simpa [__smtx_model_eval_re_exp] using
      model_eval_re_exp_rec_canonical (native_int_to_nat n) hv2

theorem model_eval_re_loop_rec_canonical :
    ∀ n v1 v2 {v3}, value_canonical v3 ->
      value_canonical (__smtx_re_loop_rec n v1 v2 v3)
  | native_nat_zero, v1, v2, v3, hv3 => by
      cases v2 <;>
        try
          simpa [__smtx_re_loop_rec] using value_canonical_notValue
      case Numeral _ =>
        simpa [__smtx_re_loop_rec] using
          model_eval_re_exp_canonical v1 hv3
  | native_nat_succ n, v1, v2, v3, hv3 => by
      cases v2 with
      | Numeral z =>
          simpa [__smtx_re_loop_rec] using
            model_eval_re_union_canonical
              (model_eval_re_loop_rec_canonical n v1
                (SmtValue.Numeral (native_zplus z (native_zneg 1))) hv3)
              (model_eval_re_exp_canonical (SmtValue.Numeral z) hv3)
      | _ =>
          simp [__smtx_re_loop_rec, value_canonical_notValue]

theorem model_eval_re_loop_canonical
    (v1 v2 : SmtValue)
    {v3 : SmtValue}
    (hv3 : value_canonical v3) :
    value_canonical (__smtx_model_eval_re_loop v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    try
      simpa [__smtx_model_eval_re_loop] using value_canonical_notValue
  case Numeral.Numeral.RegLan n1 n2 r =>
    simpa [__smtx_model_eval_re_loop] using
      model_eval_ite_canonical
        (t := SmtValue.RegLan native_re_none)
        (e := __smtx_re_loop_rec (native_int_to_nat (native_zplus n2 (native_zneg n1)))
          (SmtValue.Numeral n1) (SmtValue.Numeral n2) (SmtValue.RegLan r))
        (value_canonical_reglan native_re_none native_re_canonical_none)
        (model_eval_re_loop_rec_canonical _ _ _ hv3)

theorem model_eval_str_in_re_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_str_in_re v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_str_in_re, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_str_lt_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_str_lt v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_str_lt, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_str_leq_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_str_leq v1 v2) := by
  simpa [__smtx_model_eval_str_leq] using
    model_eval_or_canonical (__smtx_model_eval_eq v1 v2) (__smtx_model_eval_str_lt v1 v2)

theorem model_eval_str_prefixof_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_str_prefixof v1 v2) := by
  simpa [__smtx_model_eval_str_prefixof] using
    model_eval_eq_canonical v1
      (__smtx_model_eval_str_substr v2 (SmtValue.Numeral 0) (__smtx_model_eval_str_len v1))

theorem model_eval_str_suffixof_canonical
    (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_str_suffixof v1 v2) := by
  simpa [__smtx_model_eval_str_suffixof] using
    model_eval_eq_canonical v1
      (__smtx_model_eval_str_substr v2
        (__smtx_model_eval__ (__smtx_model_eval_str_len v2) (__smtx_model_eval_str_len v1))
        (__smtx_model_eval_str_len v1))

theorem model_eval_str_is_digit_canonical
    (v : SmtValue) :
    value_canonical (__smtx_model_eval_str_is_digit v) := by
  simpa [__smtx_model_eval_str_is_digit] using
    model_eval_and_canonical
      (__smtx_model_eval_leq (SmtValue.Numeral 48) (__smtx_model_eval_str_to_code v))
      (__smtx_model_eval_leq (__smtx_model_eval_str_to_code v) (SmtValue.Numeral 57))

theorem model_eval_set_empty_value_canonical
    (T : SmtType) :
    value_canonical (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false))) := by
  simp [value_canonical, __smtx_value_canonical,
    __smtx_map_canonical, __smtx_map_default_canonical, __smtx_typeof_value,
    __smtx_type_default, __smtx_map_get_default, native_ite, native_veq,
    SmtEval.native_and]

theorem set_empty_map_canonical
    (T : SmtType) :
    __smtx_map_canonical (SmtMap.default T (SmtValue.Boolean false)) = true := by
  simp [__smtx_map_canonical, __smtx_map_default_canonical, __smtx_typeof_value,
    __smtx_type_default, __smtx_value_canonical, native_ite, native_veq,
    SmtEval.native_and]

theorem model_eval_set_singleton_value_canonical
    {v : SmtValue}
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_set_singleton v) := by
  have hvBool : __smtx_value_canonical v = true := by
    simpa [value_canonical] using hv
  simp [__smtx_model_eval_set_singleton, value_canonical,
    __smtx_value_canonical, __smtx_map_canonical,
    __smtx_map_entries_ordered_after, __smtx_map_default_canonical,
    __smtx_typeof_value, __smtx_type_default, __smtx_map_get_default,
    native_ite, native_veq, hvBool, SmtEval.native_and, SmtEval.native_not]

theorem mss_op_internal_canonical
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap},
      __smtx_map_canonical m1 = true ->
        __smtx_map_canonical acc = true ->
          __smtx_map_canonical (__smtx_set_op_rec isInter m1 m2 acc) = true
  | SmtMap.default T efalse, m2, acc, _hm1, hacc => by
      simpa [__smtx_set_op_rec] using hacc
  | SmtMap.cons e etrue m1, m2, acc, hm1, hacc => by
      have he : value_canonical e := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.1
      have hmTail : __smtx_map_canonical m1 = true := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      have htrue : value_canonical (SmtValue.Boolean true) :=
        value_canonical_boolean true
      cases hCond :
          native_iff (native_veq (__smtx_map_lookup m2 e) (SmtValue.Boolean true)) isInter
      · simpa [__smtx_set_op_rec, native_ite, hCond] using
          mss_op_internal_canonical isInter hmTail hacc
      · have hacc' :
            __smtx_map_canonical
              (__smtx_map_update_aux (__smtx_map_get_default acc) acc e
                (SmtValue.Boolean true)) = true :=
          map_update_aux_canonical hacc he htrue
        simpa [__smtx_set_op_rec, native_ite, hCond] using
          mss_op_internal_canonical isInter hmTail hacc'

theorem mss_op_internal_get_default
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap},
      __smtx_map_get_default (__smtx_set_op_rec isInter m1 m2 acc) =
        __smtx_map_get_default acc
  | SmtMap.default _ _, _m2, _acc => by
      simp [__smtx_set_op_rec]
  | SmtMap.cons e _ m1, m2, acc => by
      cases hCond :
          native_iff (native_veq (__smtx_map_lookup m2 e) (SmtValue.Boolean true)) isInter
      · simpa [__smtx_set_op_rec, native_ite, hCond] using
          mss_op_internal_get_default isInter (m1 := m1) (m2 := m2) (acc := acc)
      · simpa [__smtx_set_op_rec, native_ite, hCond,
          map_update_aux_get_default (__smtx_map_get_default acc) acc e
            (SmtValue.Boolean true)] using
          mss_op_internal_get_default isInter (m1 := m1) (m2 := m2)
            (acc := __smtx_map_update_aux (__smtx_map_get_default acc) acc e
              (SmtValue.Boolean true))

theorem model_eval_set_inter_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (_hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_set_inter v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_set_inter, __smtx_set_inter] using
        value_canonical_notValue
  case Set.Set m1 m2 =>
    have hm1 : __smtx_map_canonical m1 = true := by
      have hParts := hv1
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact hParts.1
    exact value_canonical_set_of_map_canonical
      (mss_op_internal_canonical true hm1
        (set_empty_map_canonical (__smtx_index_typeof_map (__smtx_typeof_map_value m1))))
      (by
        simpa [__smtx_map_get_default] using
          mss_op_internal_get_default true (m1 := m1) (m2 := m2)
            (acc := SmtMap.default
              (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
              (SmtValue.Boolean false)))

theorem model_eval_set_minus_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (_hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_set_minus v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_set_minus, __smtx_set_minus] using
        value_canonical_notValue
  case Set.Set m1 m2 =>
    have hm1 : __smtx_map_canonical m1 = true := by
      have hParts := hv1
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact hParts.1
    exact value_canonical_set_of_map_canonical
      (mss_op_internal_canonical false hm1
        (set_empty_map_canonical (__smtx_index_typeof_map (__smtx_typeof_map_value m1))))
      (by
        simpa [__smtx_map_get_default] using
          mss_op_internal_get_default false (m1 := m1) (m2 := m2)
            (acc := SmtMap.default
              (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
              (SmtValue.Boolean false)))

theorem model_eval_set_union_canonical
    {v1 v2 : SmtValue}
    (hv1 : value_canonical v1)
    (hv2 : value_canonical v2) :
    value_canonical (__smtx_model_eval_set_union v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_set_union, __smtx_set_union] using
        value_canonical_notValue
  case Set.Set m1 m2 =>
    have hm1 : __smtx_map_canonical m1 = true := by
      have hParts := hv1
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact hParts.1
    have hm2 : __smtx_map_canonical m2 = true := by
      have hParts := hv2
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact hParts.1
    exact value_canonical_set_of_map_canonical
      (mss_op_internal_canonical false hm1 hm2)
      (by
        have hParts := hv2
        simp [value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hParts
        have hDef : __smtx_map_get_default m2 = SmtValue.Boolean false :=
          eq_of_native_veq_true hParts.2
        simpa [hDef] using
          mss_op_internal_get_default false (m1 := m1)
            (m2 := SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1))
              (SmtValue.Boolean false))
            (acc := m2))

theorem model_eval_seq_nth_wrong_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : SmtSeq)
    (n : native_Int)
    (T : SmtType)
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)) = true) :
    value_canonical (__smtx_seq_nth_wrong M s n (SmtType.Seq T)) := by
  let mapTy := SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)
  have hLookup : value_canonical
        (native_model_lookup M native_oob_seq_nth_id mapTy) :=
    model_total_typed_lookup_canonical hM native_oob_seq_nth_id mapTy
      (by simpa [mapTy] using hMapWF)
  have hFirst : value_canonical
      (__smtx_model_eval_select
        (native_model_lookup M native_oob_seq_nth_id mapTy)
        (SmtValue.Seq s)) :=
    model_eval_select_canonical hLookup
  have hSecond : value_canonical
      (__smtx_model_eval_select
        (__smtx_model_eval_select
          (native_model_lookup M native_oob_seq_nth_id mapTy)
          (SmtValue.Seq s))
        (SmtValue.Numeral n)) :=
    model_eval_select_canonical hFirst
  simpa [__smtx_seq_nth_wrong, mapTy, __smtx_model_eval_select] using hSecond

theorem seq_nth_aux_canonical :
    ∀ {s : SmtSeq} {n : native_Int} {d : SmtValue},
      __smtx_seq_canonical s = true ->
        value_canonical d ->
          value_canonical (__smtx_seq_value_nth s n d)
  | SmtSeq.empty T, n, d, _hs, hd => by
      simpa [__smtx_seq_value_nth] using hd
  | SmtSeq.cons v vs, n, d, hs, hd => by
      have hv : value_canonical v := by
        have hParts := hs
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.1
      have hvs : __smtx_seq_canonical vs = true := by
        have hParts := hs
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.2
      by_cases hn : n = 0
      · subst n
        simpa [__smtx_seq_value_nth] using hv
      · have hRec :
            value_canonical
              (__smtx_seq_value_nth vs (native_zplus n (native_zneg 1)) d) :=
          seq_nth_aux_canonical hvs hd
        simpa [__smtx_seq_value_nth, hn] using hRec

theorem model_eval_seq_nth_canonical
    (M : SmtModel)
    (hM : model_wf M)
    {v i : SmtValue}
    (hv : value_canonical v)
    (T : SmtType)
    (hvTy : __smtx_typeof_value v = SmtType.Seq T)
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)) = true) :
    value_canonical (__smtx_seq_nth M v i) := by
  cases v <;> cases i <;>
    try
      simpa [__smtx_seq_nth] using value_canonical_notValue
  case Seq.Numeral s n =>
    have hs : __smtx_seq_canonical s = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    have hsTy : __smtx_typeof_seq_value s = SmtType.Seq T := by
      simpa [__smtx_typeof_value] using hvTy
    simp only [__smtx_seq_nth]
    rw [hsTy]
    exact seq_nth_aux_canonical hs
      (model_eval_seq_nth_wrong_canonical M hM s n T hMapWF)

theorem vsm_apply_arg_nth_canonical :
    ∀ {v : SmtValue} {n npos : native_Nat},
      value_canonical v ->
        value_canonical (__smtx_apply_arg_nth_value v n npos)
  | SmtValue.Apply f a, n, npos, hv => by
      cases npos with
      | zero =>
          simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
      | succ npos =>
          have hf : value_canonical f := by
            have hParts := hv
            simp [value_canonical, __smtx_value_canonical,
              SmtEval.native_and] at hParts
            exact hParts.1
          have ha : value_canonical a := by
            have hParts := hv
            simp [value_canonical, __smtx_value_canonical,
              SmtEval.native_and] at hParts
            exact hParts.2
          cases hEq : native_nateq n npos
          · simpa [__smtx_apply_arg_nth_value, native_ite, hEq] using
              vsm_apply_arg_nth_canonical hf
          · simpa [__smtx_apply_arg_nth_value, native_ite, hEq] using ha
  | SmtValue.NotValue, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Boolean b, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Numeral k, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Rational q, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Binary w k, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Map m, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Fun fid A B, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Set m, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Seq s, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.Char c, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.UValue u k, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.RegLan r, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue
  | SmtValue.DtCons s d i, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using value_canonical_notValue

theorem model_eval_dt_sel_wrong_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (n m : native_Nat)
    (v : SmtValue)
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))) = true)
    (hvTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    value_canonical
      (__smtx_model_eval_apply M
        (native_model_lookup M (native_wrong_apply_sel_id n m)
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))
        v) := by
  exact
    model_eval_apply_lookup_fun_canonical M hM (native_wrong_apply_sel_id n m)
      (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m) v
      (dt_sel_wrong_fun_type_wf_of_map_wf s d n m hMapWF) hvTy

theorem model_eval_dt_sel_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (n m : native_Nat)
    {v : SmtValue}
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))) = true)
    (hvTy : __smtx_typeof_value v = SmtType.Datatype s d)
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_dt_sel M s d n m v) := by
  unfold __smtx_model_eval_dt_sel
  cases hEq : native_veq (__smtx_apply_head_value v) (SmtValue.DtCons s d n)
  · simpa [native_ite, hEq] using
      model_eval_dt_sel_wrong_canonical M hM s d n m v hMapWF hvTy
  · simpa [native_ite, hEq] using
      vsm_apply_arg_nth_canonical (v := v) (n := m)
        (npos := __smtx_dt_num_sels (__smtx_dd_lookup s d) n) hv

/--
Store canonicality reduces to the map-update canonicality theorem. This isolates
the remaining sorted-map preservation obligation from the value-level evaluator.
-/
theorem model_eval_store_canonical_of_map_update
    {m : SmtMap}
    {i e : SmtValue}
    (hUpdate :
      __smtx_map_canonical
        (__smtx_map_update_aux (__smtx_map_get_default m) m i e) = true) :
    value_canonical
      (__smtx_model_eval_store (SmtValue.Map m) i e) := by
  simpa [__smtx_model_eval_store, __smtx_map_store,
    value_canonical, __smtx_value_canonical] using hUpdate

/-- Set-store canonicality has the same map-update obligation as array-store. -/
theorem model_eval_store_canonical_of_set_update
    {m : SmtMap}
    {i e : SmtValue}
    (hUpdate :
      __smtx_map_canonical
        (__smtx_map_update_aux (__smtx_map_get_default m) m i e) = true)
    (hDef : __smtx_map_get_default m = SmtValue.Boolean false) :
    value_canonical
      (__smtx_model_eval_store (SmtValue.Set m) i e) := by
  exact value_canonical_set_of_map_canonical
    (m := __smtx_map_update_aux (__smtx_map_get_default m) m i e)
    hUpdate
    (by
      simpa [map_update_aux_get_default (__smtx_map_get_default m) m i e] using hDef)

/-- Map-store preserves canonicality, assuming the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_canonical_of_map
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : value_canonical i)
    (he : value_canonical e) :
    value_canonical
      (__smtx_model_eval_store (SmtValue.Map m) i e) := by
  exact model_eval_store_canonical_of_map_update
    (map_update_aux_canonical_of_order_laws hFlip hTrans hm hi he)

/-- Set-store preserves canonicality, assuming the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_canonical_of_set
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hDef : __smtx_map_get_default m = SmtValue.Boolean false)
    (hi : value_canonical i)
    (he : value_canonical e) :
    value_canonical
      (__smtx_model_eval_store (SmtValue.Set m) i e) := by
  exact model_eval_store_canonical_of_set_update
    (map_update_aux_canonical_of_order_laws hFlip hTrans hm hi he) hDef

/-- Value-level store preserves canonicality modulo the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_canonical_of_order_laws
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    {v i e : SmtValue}
    (hv : value_canonical v)
    (hi : value_canonical i)
    (he : value_canonical e) :
    value_canonical (__smtx_model_eval_store v i e) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_store, __smtx_map_store] using
        value_canonical_notValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [value_canonical, __smtx_value_canonical] using hv
    exact model_eval_store_canonical_of_map hFlip hTrans hm hi he
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      have hParts := hv
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact hParts.1
    have hDef : __smtx_map_get_default ‹SmtMap› = SmtValue.Boolean false := by
      have hParts := hv
      simp [value_canonical, __smtx_value_canonical,
        SmtEval.native_and] at hParts
      exact eq_of_native_veq_true hParts.2
    exact model_eval_store_canonical_of_set hFlip hTrans hm hDef hi he

/-- Value-level store preserves canonicality under the `native_vcmp` order laws. -/
theorem model_eval_store_canonical
    {v i e : SmtValue}
    (hv : value_canonical v)
    (hi : value_canonical i)
    (he : value_canonical e) :
    value_canonical (__smtx_model_eval_store v i e) :=
  model_eval_store_canonical_of_order_laws
    (fun hNe hCmp => native_vcmp_flip hNe hCmp)
    (fun hAB hBC => native_vcmp_trans hAB hBC)
    hv hi he

end Smtm
