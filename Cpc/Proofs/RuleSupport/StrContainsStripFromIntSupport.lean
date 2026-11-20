module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport
public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport
public import Cpc.Proofs.RuleSupport.StrContainsConcatSupport
import all Cpc.Proofs.RuleSupport.StrContainsConcatSupport
public import Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-! Shared helpers for `str_contains_strip_from_int_pre` and
`str_contains_strip_from_int_post`. -/

namespace StrContainsStripFromIntSupport

abbrev op : Term := Term.UOp UserOp.str_concat

abbrev concat (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

abbrev fromInt (n : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_from_int) n

abbrev ctn (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y


theorem mk_apply_fun_ne_stuck {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) : f ≠ Term.Stuck := by
  intro hf
  subst f
  cases x <;> simp [__eo_mk_apply] at h

theorem mk_apply_arg_ne_stuck {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) : x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

theorem mk_apply_eq_apply {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hf := mk_apply_fun_ne_stuck h
  have hx := mk_apply_arg_ne_stuck h
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem requires_eq_of_ne_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) : x = y := by
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem requires_body_of_ne_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) : __eo_requires x y z = z := by
  have hxy := requires_eq_of_ne_stuck h
  subst hxy
  unfold __eo_requires at h ⊢
  by_cases hs : x = Term.Stuck
  · subst hs
    simp [native_teq, native_ite, native_not, SmtEval.native_not] at h
  · simp [native_teq, native_ite, native_not, SmtEval.native_not, hs]

theorem digit_values_of_from_int (z : native_Int) :
    ∀ v ∈ (native_str_from_int z).map SmtValue.Char,
      ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨ch, hch, rfl⟩
  have hAll := StrInReFromIntDigRangeProof.native_str_from_int_all_digits z
  rw [List.all_eq_true] at hAll
  exact ⟨ch, rfl, hAll ch hch⟩

theorem no_compat_digits
    (Dv : List SmtValue) (c : SmtValue)
    (hDigits : ∀ v ∈ Dv,
      ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true)
    (hc : impl_native_char_is_digit (impl_native_ssm_char_of_value c) = false) :
    ∀ k, k < Dv.length → ¬ RuleProofs.native_seq_compat (Dv.drop k) [c] := by
  intro k hk hCompat
  rcases hDigits _ (List.getElem_mem hk) with ⟨ch, hv, hch⟩
  have hDrop := List.drop_eq_getElem_cons hk
  generalize Dv.drop k = d at hCompat hDrop
  generalize Dv.drop (k + 1) = d' at hDrop
  subst hDrop
  have hEq : Dv[k] = c := by
    rcases hCompat with h | h
    · rcases (RuleProofs.native_seq_prefix_eq_iff _ _).1 h with ⟨r, hr⟩
      simp only [List.cons_append, List.cons.injEq] at hr
      exact hr.1.symm
    · rcases (RuleProofs.native_seq_prefix_eq_iff _ _).1 h with ⟨r, hr⟩
      simp only [List.cons_append, List.cons.injEq] at hr
      exact hr.1
  rw [← hEq, hv] at hc
  simp [impl_native_ssm_char_of_value, hch] at hc

theorem smtx_eval_str_is_digit_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_is_digit x) =
      __smtx_model_eval_str_is_digit (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_numeral (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

theorem smtx_eval_boolean (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

theorem is_digit_single_true (c : SmtValue) (T : SmtType)
    (hd : impl_native_char_is_digit (impl_native_ssm_char_of_value c) = true) :
    __smtx_model_eval_str_is_digit (SmtValue.Seq (native_pack_seq T [c])) =
      SmtValue.Boolean true := by
  have hValid := StrInReFromIntDigRangeProof.native_char_valid_of_digit _ hd
  have hd' := hd
  simp [impl_native_char_is_digit] at hd'
  simp [__smtx_model_eval_str_is_digit, __smtx_model_eval_str_to_code,
    native_unpack_string, Smtm.native_unpack_pack_seq, native_str_to_code,
    hValid, __smtx_model_eval_leq, __smtx_model_eval_and, native_and,
    SmtEval.native_zleq, hd'.1, hd'.2]

theorem contains_bool_type (x y : Term) (T : SmtType)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (ctn x y)) = SmtType.Bool := by
  change __smtx_typeof
      (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_str_contains_eq]
  simp [hX, hY, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]

theorem seq_eval
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    ∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq T := by
    simpa [hxTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hxTy]
        simp)
  exact seq_value_canonical hValTy

theorem seq_char_smt_type (x : Term)
    (hTrans : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char := by
  simpa using
    StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof x Term.Char hTrans hTy

end StrContainsStripFromIntSupport
