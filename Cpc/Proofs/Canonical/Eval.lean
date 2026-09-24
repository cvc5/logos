module

public import Cpc.Proofs.Canonical.Ops
import all Cpc.Proofs.Canonical.Ops
public import Cpc.Proofs.Canonical.BasicModel
import all Cpc.Proofs.Canonical.BasicModel

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

theorem model_eval_boolean_canonical
    (M : SmtModel)
    (b : native_Bool) :
    value_canonical (__smtx_model_eval M (SmtTerm.Boolean b)) := by
  simpa [__smtx_model_eval] using value_canonical_boolean b

theorem model_eval_numeral_canonical
    (M : SmtModel)
    (n : native_Int) :
    value_canonical (__smtx_model_eval M (SmtTerm.Numeral n)) := by
  simpa [__smtx_model_eval] using value_canonical_numeral n

theorem model_eval_rational_canonical
    (M : SmtModel)
    (q : native_Rat) :
    value_canonical (__smtx_model_eval M (SmtTerm.Rational q)) := by
  simpa [__smtx_model_eval] using value_canonical_rational q

theorem model_eval_string_canonical
    (M : SmtModel)
    (s : native_String)
    (hs : native_string_valid s = true) :
    value_canonical (__smtx_model_eval M (SmtTerm.String s)) := by
  simpa [__smtx_model_eval] using model_eval_string_value_canonical s hs

theorem model_eval_var_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    value_canonical (__smtx_model_eval M (SmtTerm.Var s T)) := by
  simpa [__smtx_model_eval] using
    model_total_typed_var_lookup_canonical hM s T hWF

theorem model_eval_uconst_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    value_canonical (__smtx_model_eval M (SmtTerm.UConst s T)) := by
  simpa [__smtx_model_eval] using
    model_total_typed_lookup_canonical hM s T hWF

theorem model_eval_eq_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.eq t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_eq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_not_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.not t)) := by
  simpa [__smtx_model_eval] using
    model_eval_not_canonical (__smtx_model_eval M t)

theorem model_eval_or_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.or t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_or_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_and_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.and t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_and_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_imp_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.imp t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_imp_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_xor_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.xor t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_xor_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_plus_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.plus t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_plus_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_sub_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.neg t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_sub_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_mult_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.mult t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_mult_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_lt_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.lt t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_lt_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_leq_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.leq t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_leq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_gt_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.gt t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_gt_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_geq_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.geq t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_geq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_to_real_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.to_real t)) := by
  simpa [__smtx_model_eval] using
    model_eval_to_real_canonical (__smtx_model_eval M t)

theorem model_eval_to_int_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.to_int t)) := by
  simpa [__smtx_model_eval] using
    model_eval_to_int_canonical (__smtx_model_eval M t)

theorem model_eval_is_int_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.is_int t)) := by
  simpa [__smtx_model_eval] using
    model_eval_is_int_canonical (__smtx_model_eval M t)

theorem model_eval_abs_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.abs t)) := by
  simpa [__smtx_model_eval] using
    model_eval_abs_canonical (__smtx_model_eval M t)

theorem model_eval_uneg_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    value_canonical (__smtx_model_eval M (SmtTerm.uneg t)) := by
  simpa [__smtx_model_eval] using
    model_eval_uneg_canonical (__smtx_model_eval M t)

theorem model_eval_ite_term_canonical
    (M : SmtModel)
    (c t e : SmtTerm)
    (ht : value_canonical (__smtx_model_eval M t))
    (he : value_canonical (__smtx_model_eval M e)) :
    value_canonical (__smtx_model_eval M (SmtTerm.ite c t e)) := by
  simpa [__smtx_model_eval] using
    model_eval_ite_canonical
      (c := __smtx_model_eval M c)
      (t := __smtx_model_eval M t)
      (e := __smtx_model_eval M e) ht he

theorem model_eval_select_term_canonical
    (M : SmtModel)
    (a i : SmtTerm)
    (ha : value_canonical (__smtx_model_eval M a)) :
    value_canonical (__smtx_model_eval M (SmtTerm.select a i)) := by
  simpa [__smtx_model_eval] using
    model_eval_select_canonical
      (v := __smtx_model_eval M a)
      (i := __smtx_model_eval M i) ha

theorem model_eval_seq_empty_term_canonical
    (M : SmtModel)
    (T : SmtType) :
    value_canonical (__smtx_model_eval M (SmtTerm.seq_empty T)) := by
  simpa [__smtx_model_eval] using model_eval_seq_empty_value_canonical T

theorem model_eval_seq_unit_term_canonical
    (M : SmtModel)
    (t : SmtTerm)
    (ht : value_canonical (__smtx_model_eval M t)) :
    value_canonical (__smtx_model_eval M (SmtTerm.seq_unit t)) := by
  simpa [__smtx_model_eval] using
    model_eval_seq_unit_value_canonical (v := __smtx_model_eval M t) ht

theorem model_eval_str_concat_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h2 : value_canonical (__smtx_model_eval M t2)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_concat t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_concat_canonical
      (v1 := __smtx_model_eval M t1)
      (v2 := __smtx_model_eval M t2) h1 h2

theorem model_eval_str_rev_term_canonical
    (M : SmtModel)
    (t : SmtTerm)
    (ht : value_canonical (__smtx_model_eval M t)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_rev t)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_rev_canonical (v := __smtx_model_eval M t) ht

theorem model_eval_str_substr_term_canonical
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_substr t1 t2 t3)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_substr_canonical
      (v := __smtx_model_eval M t1)
      (i := __smtx_model_eval M t2)
      (n := __smtx_model_eval M t3) h1

theorem model_eval_str_replace_term_canonical
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h2 : value_canonical (__smtx_model_eval M t2))
    (h3 : value_canonical (__smtx_model_eval M t3)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_replace t1 t2 t3)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_replace_canonical
      (v := __smtx_model_eval M t1)
      (pat := __smtx_model_eval M t2)
      (repl := __smtx_model_eval M t3) h1 h2 h3

theorem model_eval_str_at_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_at t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_at_canonical
      (v := __smtx_model_eval M t1)
      (i := __smtx_model_eval M t2) h1

theorem model_eval_str_update_term_canonical
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h3 : value_canonical (__smtx_model_eval M t3)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_update t1 t2 t3)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_update_canonical
      (v := __smtx_model_eval M t1)
      (i := __smtx_model_eval M t2)
      (repl := __smtx_model_eval M t3) h1 h3

theorem model_eval_str_replace_all_term_canonical
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h2 : value_canonical (__smtx_model_eval M t2))
    (h3 : value_canonical (__smtx_model_eval M t3)) :
    value_canonical (__smtx_model_eval M (SmtTerm.str_replace_all t1 t2 t3)) := by
  simpa [__smtx_model_eval] using
    model_eval_str_replace_all_canonical
      (v := __smtx_model_eval M t1)
      (pat := __smtx_model_eval M t2)
      (repl := __smtx_model_eval M t3) h1 h2 h3

theorem model_eval_set_empty_term_canonical
    (M : SmtModel)
    (T : SmtType) :
    value_canonical (__smtx_model_eval M (SmtTerm.set_empty T)) := by
  simpa [__smtx_model_eval] using model_eval_set_empty_value_canonical T

theorem model_eval_set_singleton_term_canonical
    (M : SmtModel)
    (t : SmtTerm)
    (ht : value_canonical (__smtx_model_eval M t)) :
    value_canonical (__smtx_model_eval M (SmtTerm.set_singleton t)) := by
  simpa [__smtx_model_eval] using
    model_eval_set_singleton_value_canonical (v := __smtx_model_eval M t) ht

theorem model_eval_set_union_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h2 : value_canonical (__smtx_model_eval M t2)) :
    value_canonical (__smtx_model_eval M (SmtTerm.set_union t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_set_union_canonical
      (v1 := __smtx_model_eval M t1)
      (v2 := __smtx_model_eval M t2) h1 h2

theorem model_eval_set_inter_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h2 : value_canonical (__smtx_model_eval M t2)) :
    value_canonical (__smtx_model_eval M (SmtTerm.set_inter t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_set_inter_canonical
      (v1 := __smtx_model_eval M t1)
      (v2 := __smtx_model_eval M t2) h1 h2

theorem model_eval_set_minus_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (h1 : value_canonical (__smtx_model_eval M t1))
    (h2 : value_canonical (__smtx_model_eval M t2)) :
    value_canonical (__smtx_model_eval M (SmtTerm.set_minus t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_set_minus_canonical
      (v1 := __smtx_model_eval M t1)
      (v2 := __smtx_model_eval M t2) h1 h2

theorem model_eval_seq_nth_term_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hElemRec :
      ∀ {T : SmtType},
        __smtx_typeof t1 = SmtType.Seq T ->
          __smtx_type_wf_rec T = true)
    (h1 : value_canonical (__smtx_model_eval M t1)) :
    value_canonical (__smtx_model_eval M (SmtTerm.seq_nth t1 t2)) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, ht1Ty, ht2Ty⟩
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_seq_nth_eq t1 t2] at ht
    simpa [__smtx_typeof_seq_nth, ht1Ty, ht2Ty] using ht
  have hTWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hRec : __smtx_type_wf_rec T = true := hElemRec ht1Ty
  have hTInh : native_inhabited_type T = true := by
    cases T <;>
      simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        native_and] at hTWf hRec ⊢
    all_goals first | exact hTWf | exact hTWf.1 | exact hTWf.1.1 | contradiction
  have hMapWF := seq_nth_wrong_map_type_wf hTInh hRec
  have ht1 : term_has_non_none_type t1 := by
    unfold term_has_non_none_type
    rw [ht1Ty]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t1) = SmtType.Seq T :=
    (smt_model_eval_preserves_type_of_non_none M hM t1 ht1).trans ht1Ty
  simpa [__smtx_model_eval] using
    model_eval_seq_nth_canonical
      (M := M) (hM := hM)
      (v := __smtx_model_eval M t1)
      (i := __smtx_model_eval M t2) h1 T hValTy hMapWF

theorem model_eval_dt_sel_term_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i j : native_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hx : value_canonical (__smtx_model_eval M x)) :
    value_canonical
      (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  have htx : term_has_non_none_type x :=
    by
      unfold term_has_non_none_type
      rw [dt_sel_arg_datatype_of_non_none ht]
      simp
  have hxTy :
      __smtx_typeof_value (__smtx_model_eval M x) = SmtType.Datatype s d := by
    simpa [dt_sel_arg_datatype_of_non_none ht] using
      smt_model_eval_preserves_type_of_non_none M hM x htx
  simpa [__smtx_model_eval] using
    model_eval_dt_sel_canonical M hM s d i j
      (v := __smtx_model_eval M x)
      (dt_sel_wrong_map_type_wf_of_non_none ht) hxTy hx

theorem native_eval_tchoice_canonical
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm) :
    value_canonical (native_eval_choice M s T body) := by
  classical
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · have hCan : value_canonical (Classical.choose hSat) := by
      simpa [value_canonical] using (Classical.choose_spec hSat).2.1
    simpa [hSat] using hCan
  · by_cases hTy :
        ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v
    · have hCan : value_canonical (Classical.choose hTy) := by
        simpa [value_canonical] using (Classical.choose_spec hTy).2
      simpa [hSat, hTy] using hCan
    · simpa [hSat, hTy] using value_canonical_notValue

/-- Term-level store preserves canonicality modulo the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_term_canonical_of_order_laws
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
    (M : SmtModel)
    (a i e : SmtTerm)
    (ha : value_canonical (__smtx_model_eval M a))
    (hi : value_canonical (__smtx_model_eval M i))
    (he : value_canonical (__smtx_model_eval M e)) :
    value_canonical (__smtx_model_eval M (SmtTerm.store a i e)) := by
  simpa [__smtx_model_eval] using
    model_eval_store_canonical_of_order_laws
      hFlip hTrans
      (v := __smtx_model_eval M a)
      (i := __smtx_model_eval M i)
      (e := __smtx_model_eval M e) ha hi he

/-- Term-level store preserves canonicality under the `native_vcmp` order laws. -/
theorem model_eval_store_term_canonical
    (M : SmtModel)
    (a i e : SmtTerm)
    (ha : value_canonical (__smtx_model_eval M a))
    (hi : value_canonical (__smtx_model_eval M i))
    (he : value_canonical (__smtx_model_eval M e)) :
    value_canonical (__smtx_model_eval M (SmtTerm.store a i e)) := by
  simpa [__smtx_model_eval] using
    model_eval_store_canonical
      (v := __smtx_model_eval M a)
      (i := __smtx_model_eval M i)
      (e := __smtx_model_eval M e) ha hi he

theorem model_eval_zero_extend_term_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (t1 t2 : SmtTerm)
    (hTy : term_has_non_none_type (SmtTerm.zero_extend t1 t2)) :
    value_canonical (__smtx_model_eval M (SmtTerm.zero_extend t1 t2)) := by
  rcases zero_extend_args_of_non_none hTy with ⟨i, w, h1, h2, hi0⟩
  exact model_eval_canonical_of_bitvec_type M hM _ (native_int_to_nat (native_zplus i (native_nat_to_int w))) (by
    rw [typeof_zero_extend_eq]
    simp [__smtx_typeof_zero_extend, h1, h2, hi0, native_ite])

/--
Canonicity of SMT model evaluation over the supported, non-`None` fragment.
-/
theorem model_eval_canonical_of_supported
    (M : SmtModel)
    (hM : model_wf M)
    (t : SmtTerm)
    (hTy : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    value_canonical (__smtx_model_eval M t) := by
  induction hs generalizing M
  case boolean b =>
      exact model_eval_boolean_canonical M b
  case numeral n =>
      exact model_eval_numeral_canonical M n
  case rational q =>
      exact model_eval_rational_canonical M q
  case string s =>
      have hsValid : native_string_valid s = true := by
        rw [term_has_non_none_type, __smtx_typeof.eq_4] at hTy
        cases hValid : native_string_valid s <;>
          simp [native_ite, hValid] at hTy ⊢
      exact model_eval_string_canonical M s hsValid
  case binary w n =>
      cases hw : native_zleq 0 w <;>
        cases hn : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_model_eval, __smtx_typeof, value_canonical,
            __smtx_value_canonical, term_has_non_none_type,
            native_and, SmtEval.native_and,
            native_ite, hw, hn] at hTy ⊢
  case purify ht hs ih =>
      simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using
        ih M hM ht
  case var s T hT =>
      exact model_eval_var_canonical M hM s T
        (smtx_typeof_guard_wf_wf_of_non_none T T (by
          simpa [term_has_non_none_type, __smtx_typeof] using hTy))
  case uconst s T hT =>
      exact model_eval_uconst_canonical M hM s T
        (smtx_typeof_guard_wf_wf_of_non_none T T (by
          simpa [term_has_non_none_type, __smtx_typeof] using hTy))
  case re_allchar =>
      simpa [__smtx_model_eval] using value_canonical_reglan_allchar
  case re_none =>
      simpa [__smtx_model_eval] using value_canonical_reglan_none
  case re_all =>
      simpa [__smtx_model_eval] using value_canonical_reglan_all
  case seq_empty T hT =>
      exact model_eval_seq_empty_term_canonical M T
  case set_empty T hT =>
      exact model_eval_set_empty_term_canonical M T
  case seq_unit ht hs ih =>
      exact model_eval_seq_unit_term_canonical M _ (ih M hM ht)
  case set_singleton ht hs ih =>
      exact model_eval_set_singleton_term_canonical M _ (ih M hM ht)
  case seq_nth ht1 hs1 ht2 hs2 hT hElemRec ih1 ih2 =>
      exact model_eval_seq_nth_term_canonical M hM _ _ hTy hElemRec
        (ih1 M hM ht1)
  case set_union ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_set_union_term_canonical M _ _ (ih1 M hM ht1) (ih2 M hM ht2)
  case set_inter ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_set_inter_term_canonical M _ _ (ih1 M hM ht1) (ih2 M hM ht2)
  case set_minus ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_set_minus_term_canonical M _ _ (ih1 M hM ht1) (ih2 M hM ht2)
  case set_member ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval, __smtx_model_eval_set_member,
        __smtx_model_eval_select] using
        model_eval_select_canonical
          (v := __smtx_model_eval M _)
          (i := __smtx_model_eval M _) (ih2 M hM ht2)
  case set_subset ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval, __smtx_model_eval_set_subset] using
        model_eval_eq_canonical
          (__smtx_model_eval_set_inter (__smtx_model_eval M _) (__smtx_model_eval M _))
          (__smtx_model_eval M _)
  case select ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_select_term_canonical M _ _ (ih1 M hM ht1)
  case store ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      exact model_eval_store_term_canonical M _ _ _
        (ih1 M hM ht1) (ih2 M hM ht2) (ih3 M hM ht3)
  case map_diff ht1 hs1 ht2 hs2 hDefault ih1 ih2 =>
      exact model_eval_map_diff_canonical M _ _ hTy
        (fun {A} hA => (hDefault (A := A) hA).2)
        (smt_model_eval_preserves_type_of_non_none M hM _ ht1)
        (smt_model_eval_preserves_type_of_non_none M hM _ ht2)
  case seq_diff ht1 hs1 ht2 hs2 ih1 ih2 =>
      refine model_eval_canonical_of_int_type M hM _ ?_
      rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
          (typeof_seq_diff_eq _ _) hTy with ⟨T, h1, h2⟩
      rw [typeof_seq_diff_eq]
      simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2]
  case ite htc hsc ht1 hs1 ht2 hs2 ihc ih1 ih2 =>
      exact model_eval_ite_term_canonical M _ _ _
        (ih1 M hM ht1) (ih2 M hM ht2)
  case «exists» s T body =>
      exact model_eval_canonical_of_bool_type M hM _ (exists_term_typeof_of_non_none hTy)
  case «forall» s T body =>
      exact model_eval_canonical_of_bool_type M hM _ (forall_term_typeof_of_non_none hTy)
  case choice s T body htc =>
      simpa [__smtx_model_eval] using native_eval_tchoice_canonical M s T body
  case bind s T x1 x2 hbt hs1 hs2 ih1 ih2 =>
      have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none hTy
      have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none hTy
      have hTx1 : __smtx_typeof x1 = T := bind_arg1_type_of_non_none hTy
      have hWf : __smtx_type_wf T = true := bind_binder_type_wf_of_non_none hTy
      have hx1ty : __smtx_typeof_value (__smtx_model_eval M x1) = __smtx_typeof x1 :=
        smt_model_eval_preserves_type_of_non_none M hM x1 ht1
      have hx1canon : value_canonical (__smtx_model_eval M x1) :=
        ih1 M hM ht1
      have hM' : model_wf (native_model_push M s T (__smtx_model_eval M x1)) :=
        model_total_typed_push hM s T (__smtx_model_eval M x1) hWf (hx1ty.trans hTx1) hx1canon
      rw [smtx_model_eval_bind_eq]
      exact ih2 _ hM' ht2
  case not ht hs ih =>
      exact model_eval_not_term_canonical M _
  case or ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_or_term_canonical M _ _
  case and ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_and_term_canonical M _ _
  case imp ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_imp_term_canonical M _ _
  case eq t1 t2 =>
      exact model_eval_eq_term_canonical M t1 t2
  case xor t1 t2 =>
      exact model_eval_xor_term_canonical M t1 t2
  case plus ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_plus_term_canonical M _ _
  case arith_neg ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_sub_term_canonical M _ _
  case mult ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_mult_term_canonical M _ _
  case lt ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_lt_term_canonical M _ _
  case leq ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_leq_term_canonical M _ _
  case gt ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_gt_term_canonical M _ _
  case geq ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_geq_term_canonical M _ _
  case to_real ht hs ih =>
      exact model_eval_to_real_term_canonical M _
  case to_int ht hs ih =>
      exact model_eval_to_int_term_canonical M _
  case is_int ht hs ih =>
      exact model_eval_is_int_term_canonical M _
  case abs ht hs ih =>
      exact model_eval_abs_term_canonical M _
  case uneg ht hs ih =>
      exact model_eval_uneg_term_canonical M _
  case div t1 t2 ht1 hs1 ht2 hs2 ih1 ih2 =>
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) (typeof_div_eq t1 t2) hTy
      have hxTy :
          __smtx_typeof_value (__smtx_model_eval M t1) = SmtType.Int := by
        simpa [hArgs.1] using smt_model_eval_preserves_type_of_non_none M hM t1 ht1
      simpa [__smtx_model_eval] using
        model_eval_ite_canonical
          (model_eval_apply_lookup_fun_canonical M hM native_div_by_zero_id
            SmtType.Int SmtType.Int (__smtx_model_eval M t1) fun_type_wf_int_int hxTy)
          (model_eval_div_total_canonical _ _)
  case mod t1 t2 ht1 hs1 ht2 hs2 ih1 ih2 =>
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) (typeof_mod_eq t1 t2) hTy
      have hxTy :
          __smtx_typeof_value (__smtx_model_eval M t1) = SmtType.Int := by
        simpa [hArgs.1] using smt_model_eval_preserves_type_of_non_none M hM t1 ht1
      simpa [__smtx_model_eval] using
        model_eval_ite_canonical
          (model_eval_apply_lookup_fun_canonical M hM native_mod_by_zero_id
            SmtType.Int SmtType.Int (__smtx_model_eval M t1) fun_type_wf_int_int hxTy)
          (model_eval_mod_total_canonical _ _)
  case divisible ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_divisible_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case int_pow2 ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_int_pow2_canonical (__smtx_model_eval M _)
  case int_log2 ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_int_log2_canonical (__smtx_model_eval M _)
  case div_total ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_div_total_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case mod_total ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_mod_total_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case qdiv t1 t2 ht1 hs1 ht2 hs2 ih1 ih2 =>
      rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (typeof_qdiv_eq t1 t2) hTy with hArgs | hArgs
      · have hpres1 :=
          smt_model_eval_preserves_type_of_non_none M hM t1 ht1
        rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
        have hxTy :
            __smtx_typeof_value
              (__smtx_to_real_coerce (__smtx_model_eval M t1)) = SmtType.Real := by
          rw [hn1]
          simp [__smtx_to_real_coerce, __smtx_typeof_value]
        simpa [__smtx_model_eval] using
          model_eval_ite_canonical
            (model_eval_apply_lookup_fun_canonical M hM native_qdiv_by_zero_id
              SmtType.Real SmtType.Real
              (__smtx_to_real_coerce (__smtx_model_eval M t1))
              fun_type_wf_real_real hxTy)
            (model_eval_qdiv_total_canonical _ _)
      · have hxTyRaw :
            __smtx_typeof_value (__smtx_model_eval M t1) = SmtType.Real := by
          simpa [hArgs.1] using smt_model_eval_preserves_type_of_non_none M hM t1 ht1
        rcases real_value_canonical hxTyRaw with ⟨q1, hq1⟩
        have hxTy :
            __smtx_typeof_value
              (__smtx_to_real_coerce (__smtx_model_eval M t1)) = SmtType.Real := by
          rw [hq1]
          simp [__smtx_to_real_coerce, __smtx_typeof_value]
        simpa [__smtx_model_eval] using
          model_eval_ite_canonical
            (model_eval_apply_lookup_fun_canonical M hM native_qdiv_by_zero_id
              SmtType.Real SmtType.Real
              (__smtx_to_real_coerce (__smtx_model_eval M t1))
              fun_type_wf_real_real hxTy)
            (model_eval_qdiv_total_canonical _ _)
  case qdiv_total ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_qdiv_total_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_concat ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_str_concat_term_canonical M _ _ (ih1 M hM ht1) (ih2 M hM ht2)
  case str_substr ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      exact model_eval_str_substr_term_canonical M _ _ _ (ih1 M hM ht1)
  case str_at ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_str_at_term_canonical M _ _ (ih1 M hM ht1)
  case str_replace ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      exact model_eval_str_replace_term_canonical M _ _ _
        (ih1 M hM ht1) (ih2 M hM ht2) (ih3 M hM ht3)
  case str_rev ht hs ih =>
      exact model_eval_str_rev_term_canonical M _ (ih M hM ht)
  case str_update ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      exact model_eval_str_update_term_canonical M _ _ _ (ih1 M hM ht1) (ih3 M hM ht3)
  case str_to_lower ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_lower_canonical (ih M hM ht)
  case str_to_upper ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_upper_canonical (ih M hM ht)
  case str_from_code ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_from_code_canonical (__smtx_model_eval M _)
  case str_from_int ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_from_int_canonical (__smtx_model_eval M _)
  case str_replace_all ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      exact model_eval_str_replace_all_term_canonical M _ _ _
        (ih1 M hM ht1) (ih2 M hM ht2) (ih3 M hM ht3)
  case str_replace_re ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_replace_re_canonical
          (__smtx_model_eval M _) (ih1 M hM ht1) (ih3 M hM ht3)
  case str_replace_re_all ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_replace_re_all_canonical
          (__smtx_model_eval M _) (ih1 M hM ht1) (ih3 M hM ht3)
  case str_len ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_len_canonical (__smtx_model_eval M _)
  case str_contains ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_contains_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_indexof ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_indexof_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_indexof_re ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_indexof_re_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_indexof_re_split ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_indexof_re_split_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case _at_strings_occur_index ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_at_strings_occur_index_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case _at_strings_occur_index_re ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_at_strings_occur_index_re_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_to_code ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_code_canonical (__smtx_model_eval M _)
  case str_to_int ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_int_canonical (__smtx_model_eval M _)
  case str_to_re t ht hs ih =>
      have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
          (typeof_str_to_re_eq t) hTy
      have hEvalTy :
          __smtx_typeof_value (__smtx_model_eval M t) =
            SmtType.Seq SmtType.Char := by
        simpa [hArg] using
          smt_model_eval_preserves_type_of_non_none M hM t ht
      simpa [__smtx_model_eval] using
        model_eval_str_to_re_canonical (ih M hM ht) hEvalTy
  case re_mult ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_re_mult_canonical (ih M hM ht)
  case re_plus ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_re_plus_canonical (ih M hM ht)
  case re_exp n ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_re_exp_canonical (SmtValue.Numeral _) (ih M hM ht)
  case re_opt ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_re_opt_canonical (ih M hM ht)
  case re_comp ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_re_comp_canonical (ih M hM ht)
  case re_range t1 t2 ht1 hs1 ht2 hs2 ih1 ih2 =>
      have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
        (typeof_re_range_eq t1 t2) hTy
      have hEvalTy1 :
          __smtx_typeof_value (__smtx_model_eval M t1) =
            SmtType.Seq SmtType.Char := by
        simpa [hArgs.1] using
          smt_model_eval_preserves_type_of_non_none M hM t1 ht1
      have hEvalTy2 :
          __smtx_typeof_value (__smtx_model_eval M t2) =
            SmtType.Seq SmtType.Char := by
        simpa [hArgs.2] using
          smt_model_eval_preserves_type_of_non_none M hM t2 ht2
      simpa [__smtx_model_eval] using
        model_eval_re_range_canonical (ih1 M hM ht1) (ih2 M hM ht2)
          hEvalTy1 hEvalTy2
  case re_concat ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_concat_canonical (ih1 M hM ht1) (ih2 M hM ht2)
  case re_inter ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_inter_canonical (ih1 M hM ht1) (ih2 M hM ht2)
  case re_union ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_union_canonical (ih1 M hM ht1) (ih2 M hM ht2)
  case re_diff ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_diff_canonical (ih1 M hM ht1) (ih2 M hM ht2)
  case re_loop n1 n2 ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_re_loop_canonical (SmtValue.Numeral _) (SmtValue.Numeral _)
          (ih M hM ht)
  case str_in_re ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_in_re_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_lt ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_lt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_leq ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_leq_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_prefixof ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_prefixof_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_suffixof ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_suffixof_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_is_digit ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_str_is_digit_canonical (__smtx_model_eval M _)
  case bv_concat ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_concat_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case extract ht1 hs1 ht2 hs2 ht3 hs3 ih1 ih2 ih3 =>
      simpa [__smtx_model_eval] using
        model_eval_extract_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «repeat» ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_repeat_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnot ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_bvnot_canonical (__smtx_model_eval M _)
  case bvand ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvand_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvor ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnand ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvnand_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnor ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvnor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvxor ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvxor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvxnor ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvxnor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvcomp ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvcomp_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvneg ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_bvneg_canonical (__smtx_model_eval M _)
  case bvadd ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvadd_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvmul ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvmul_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvudiv ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvudiv_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvurem ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvurem_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsub ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsub_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvult ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvult_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvule ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvule_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvugt ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvugt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvuge ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvuge_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvslt ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvslt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsle ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsle_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsgt ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsgt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsge ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsge_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvshl ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvshl_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvlshr ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvlshr_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsdiv ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsdiv_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsrem ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsrem_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsmod ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsmod_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvashr ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvashr_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case rotate_left ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_rotate_left_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (ih2 M hM ht2)
  case rotate_right ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_rotate_right_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (ih2 M hM ht2)
  case bvuaddo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvuaddo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnego ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_bvnego_canonical (__smtx_model_eval M _)
  case bvsaddo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsaddo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvumulo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvumulo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsmulo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsmulo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvusubo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvusubo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvssubo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvssubo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsdivo ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsdivo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case zero_extend ht1 hs1 ht2 hs2 ih1 ih2 =>
      exact model_eval_zero_extend_term_canonical M hM _ _ hTy
  case sign_extend ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_sign_extend_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case int_to_bv ht1 hs1 ht2 hs2 ih1 ih2 =>
      simpa [__smtx_model_eval] using
        model_eval_int_to_bv_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case ubv_to_int ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_ubv_to_int_canonical (__smtx_model_eval M _)
  case sbv_to_int ht hs ih =>
      simpa [__smtx_model_eval] using
        model_eval_sbv_to_int_canonical (__smtx_model_eval M _)
  case dt_cons s d i =>
      simpa [__smtx_model_eval] using value_canonical_dt_cons s d i
  case dt_sel ht hT htx hsx ihx =>
      exact model_eval_dt_sel_term_canonical M hM _ _ _ _ _ hTy (ihx M hM htx)
  case dt_tester s d i x =>
      simpa [__smtx_model_eval, __smtx_model_eval_dt_tester] using
        value_canonical_boolean (native_veq (__smtx_apply_head_value (__smtx_model_eval M x))
          (SmtValue.DtCons s d i))
  case apply f x hTyApp hEval htf hsf htx hsx ihf ihx =>
      have hf := ihf M hM htf
      have hx := ihx M hM htx
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        unfold term_has_non_none_type at hTy
        rw [hTyApp] at hTy
        exact hTy
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHeadTerm, hX, _hA, _hB⟩
      have hPresF :
          __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
        smt_model_eval_preserves_type_of_non_none M hM f htf
      have hPresX :
          __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
        smt_model_eval_preserves_type_of_non_none M hM x htx
      have hxTy :
          __smtx_typeof_value (__smtx_model_eval M x) = A := by
        simpa [hX] using hPresX
      have hHeadVal :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ∨
            __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
        cases hHeadTerm with
        | inl hFun =>
            exact Or.inl (by simpa [hFun] using hPresF)
        | inr hDtc =>
            exact Or.inr (by simpa [hDtc] using hPresF)
      have hFunWF :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ->
            __smtx_type_wf (SmtType.FunType A B) = true := by
        intro hValFun
        cases hHeadTerm with
        | inl hFun =>
            exact smt_term_fun_type_wf_of_non_none f htf hFun
        | inr hDtc =>
            have hValDtc :
                __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
              simpa [hDtc] using hPresF
            rw [hValFun] at hValDtc
            cases hValDtc
      simpa [hEval M] using
        model_eval_apply_canonical M hM
          (f := __smtx_model_eval M f)
          (x := __smtx_model_eval M x)
          (hHead := hHeadVal)
          (hFunWF := hFunWF)
          (hxTy := hxTy)
          hf hx
  all_goals
    first
    | exact model_eval_canonical_of_bool_type M hM _ (by
        simpa [__smtx_typeof] using hTy)
    | exact model_eval_canonical_of_int_type M hM _ (by
        simpa [__smtx_typeof] using hTy)
    | exact model_eval_canonical_of_real_type M hM _ (by
        simpa [__smtx_typeof] using hTy)

/--
Central canonicity theorem for SMT model evaluation.

This is the public theorem array extensionality should consume.
-/
theorem model_eval_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (t : SmtTerm)
    (hTy : term_has_non_none_type t) :
    value_canonical (__smtx_model_eval M t) := by
  exact model_eval_canonical_of_supported M hM t hTy
    (supported_preservation_term_of_non_none t hTy)

end Smtm
