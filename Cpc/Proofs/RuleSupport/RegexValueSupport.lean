module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-!
Value-sequence view of regular-language membership.

The executable model matches regular languages against `List SmtValue`
sequences (`Smtm.native_str_in_re`), while most of the proof layer works with
the string view `RuleProofs.native_str_in_re`.  A value sequence only ever
matches a regular language when all of its elements are valid characters, and
such a sequence is exactly the image of a valid native string; the lemmas here
move between the two views along that observation.
-/

@[simp] theorem model_str_in_re_unpack_eq_string
    (ss : SmtSeq) (r : SmtRegLan)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    Smtm.native_str_in_re (native_unpack_seq ss) r =
      RuleProofs.native_str_in_re (native_unpack_string ss) r := by
  rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTy]
  exact (native_str_in_re_eq_model (native_unpack_string ss) r).symm

@[simp] theorem model_str_in_re_unpack_eq_string_of_value_type
    (ss : SmtSeq) (r : SmtRegLan)
    (hTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char) :
    Smtm.native_str_in_re (native_unpack_seq ss) r =
      RuleProofs.native_str_in_re (native_unpack_string ss) r := by
  apply model_str_in_re_unpack_eq_string ss r
  exact hTy

theorem seq_value_canonical_with_char_type {v : SmtValue}
    (hTy : __smtx_typeof_value v = SmtType.Seq SmtType.Char) :
    ∃ ss : SmtSeq,
      v = SmtValue.Seq ss ∧
        __smtx_typeof_value (SmtValue.Seq ss) =
          SmtType.Seq SmtType.Char := by
  rcases seq_value_canonical hTy with ⟨ss, hEval⟩
  refine ⟨ss, hEval, ?_⟩
  rw [← hEval]
  exact hTy

-- `private`: `RuleProofs.native_unpack_seq_pack_seq` is also declared (with a
-- byte-identical proof) in `RuleSupport/StrInReEvalSupport.lean`, and under
-- v4.33 the generated `._f` auxiliary makes the two collide in any module
-- importing both, e.g. `RuleSupport/ReInclusionSupport.lean`.  Both of this
-- module's consumers reach it through `import all`, so they still see it.
private theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq,
        native_unpack_seq_pack_seq T xs]

/-- The native string underlying a value sequence. -/
def valueSeqString (xs : List SmtValue) : native_String :=
  xs.map impl_native_ssm_char_of_value

theorem native_re_str_valid_cons {x : SmtValue} {xs : List SmtValue}
    (h : native_re_str_valid (x :: xs) = true) :
    native_re_elem_valid x = true ∧ native_re_str_valid xs = true := by
  simpa [native_re_str_valid] using h

/-- A valid value sequence is the image of its underlying string. -/
theorem native_string_to_values_valueSeqString :
    ∀ xs : List SmtValue, native_re_str_valid xs = true ->
      impl_native_string_to_values (valueSeqString xs) = xs
  | [], _ => rfl
  | x :: xs, h => by
      have hx := native_re_str_valid_cons h
      cases x with
      | Char c =>
          simpa [valueSeqString, impl_native_string_to_values,
            impl_native_ssm_char_of_value] using
            native_string_to_values_valueSeqString xs hx.2
      | _ => simp [native_re_elem_valid] at hx

/-- The string underlying a valid value sequence is itself valid. -/
theorem native_string_valid_valueSeqString :
    ∀ xs : List SmtValue, native_re_str_valid xs = true ->
      native_string_valid (valueSeqString xs) = true
  | [], _ => rfl
  | x :: xs, h => by
      have hx := native_re_str_valid_cons h
      cases x with
      | Char c =>
          have hc : native_char_valid c = true := by
            simpa [native_re_elem_valid] using hx.1
          simpa [valueSeqString, native_string_valid, impl_native_ssm_char_of_value,
            hc] using native_string_valid_valueSeqString xs hx.2
      | _ => simp [native_re_elem_valid] at hx

theorem native_re_str_valid_sublist {xs ys : List SmtValue}
    (h : native_re_str_valid xs = true)
    (hsub : ∀ y ∈ ys, y ∈ xs) : native_re_str_valid ys = true := by
  rw [native_re_str_valid, List.all_eq_true] at h ⊢
  intro y hy
  exact h y (hsub y hy)

theorem native_re_str_valid_extract {xs : List SmtValue}
    (h : native_re_str_valid xs = true) (i n : native_Int) :
    native_re_str_valid (native_seq_extract xs i n) = true := by
  unfold native_seq_extract
  dsimp only
  by_cases hOut :
      (decide (i < 0) || decide (n ≤ 0) ||
        decide (i ≥ Int.ofNat xs.length)) = true
  · rw [if_pos hOut]
    rfl
  · rw [if_neg hOut]
    exact native_re_str_valid_sublist h fun _ hy =>
      List.mem_of_mem_drop (List.mem_of_mem_take hy)

/-- A value sequence whose elements are all valid characters is the image of
the string it unpacks to. -/
theorem native_unpack_seq_eq_values_of_valid {ss : SmtSeq}
    (h : native_re_str_valid (native_unpack_seq ss) = true) :
    native_unpack_seq ss = impl_native_string_to_values (native_unpack_string ss) := by
  have := native_string_to_values_valueSeqString (native_unpack_seq ss) h
  simpa [native_unpack_string, valueSeqString] using this.symm

/-- Matching a value sequence is matching its underlying string. -/
theorem model_str_in_re_eq_valueSeqString (xs : List SmtValue)
    (hValid : native_re_str_valid xs = true) (r : SmtRegLan) :
    Smtm.native_str_in_re xs r = native_str_in_re (valueSeqString xs) r := by
  rw [native_str_in_re_eq_model,
    native_string_to_values_valueSeqString xs hValid]

/-- Only valid value sequences match any regular language. -/
theorem native_re_str_valid_of_model_str_in_re_true
    {xs : List SmtValue} {r : SmtRegLan}
    (h : Smtm.native_str_in_re xs r = true) :
    native_re_str_valid xs = true := by
  cases hValid : native_re_str_valid xs with
  | false => simp [Smtm.native_str_in_re, hValid] at h
  | true => rfl

/-- A well-typed character sequence value unpacks to a valid value sequence. -/
theorem native_re_str_valid_unpack_seq_of_typeof_seq_char {ss : SmtSeq}
    (h : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_re_str_valid (native_unpack_seq ss) = true := by
  rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char h,
    native_re_str_valid_string]
  exact native_unpack_string_valid_of_typeof_seq_char h

theorem model_str_in_re_re_inter (xs : List SmtValue) (r s : SmtRegLan) :
    Smtm.native_str_in_re xs (native_re_inter r s) =
      (Smtm.native_str_in_re xs r && Smtm.native_str_in_re xs s) := by
  by_cases hValid : native_re_str_valid xs = true
  · rw [model_str_in_re_eq_valueSeqString xs hValid,
      model_str_in_re_eq_valueSeqString xs hValid,
      model_str_in_re_eq_valueSeqString xs hValid]
    exact native_str_in_re_re_inter _ r s
  · have hInvalid : native_re_str_valid xs = false := by
      cases h : native_re_str_valid xs <;> simp [h] at hValid ⊢
    simp [Smtm.native_str_in_re, hInvalid]

theorem model_str_in_re_mk_inter (xs : List SmtValue) (r s : SmtRegLan) :
    Smtm.native_str_in_re xs (native_re_mk_inter r s) =
      (Smtm.native_str_in_re xs r && Smtm.native_str_in_re xs s) :=
  model_str_in_re_re_inter xs r s

theorem model_str_in_re_re_comp (xs : List SmtValue) (r : SmtRegLan) :
    Smtm.native_str_in_re xs (native_re_comp r) =
      (native_re_str_valid xs && Bool.not (Smtm.native_str_in_re xs r)) := by
  by_cases hValid : native_re_str_valid xs = true
  · rw [model_str_in_re_eq_valueSeqString xs hValid,
      model_str_in_re_eq_valueSeqString xs hValid,
      native_str_in_re_re_comp,
      native_string_valid_valueSeqString xs hValid, hValid]
  · have hInvalid : native_re_str_valid xs = false := by
      cases h : native_re_str_valid xs <;> simp [h] at hValid ⊢
    simp [Smtm.native_str_in_re, hInvalid]

theorem native_re_str_valid_append {xs ys : List SmtValue}
    (hx : native_re_str_valid xs = true) (hy : native_re_str_valid ys = true) :
    native_re_str_valid (xs ++ ys) = true := by
  simpa [native_re_str_valid, hx, hy] using And.intro hx hy

theorem valueSeqString_append (xs ys : List SmtValue) :
    valueSeqString (xs ++ ys) = valueSeqString xs ++ valueSeqString ys := by
  simp [valueSeqString]

theorem model_str_in_re_re_concat_intro (xs ys : List SmtValue)
    (r s : SmtRegLan)
    (hx : Smtm.native_str_in_re xs r = true)
    (hy : Smtm.native_str_in_re ys s = true) :
    Smtm.native_str_in_re (xs ++ ys) (native_re_concat r s) = true := by
  have hxv := native_re_str_valid_of_model_str_in_re_true hx
  have hyv := native_re_str_valid_of_model_str_in_re_true hy
  rw [model_str_in_re_eq_valueSeqString _ (native_re_str_valid_append hxv hyv),
    valueSeqString_append]
  rw [model_str_in_re_eq_valueSeqString xs hxv] at hx
  rw [model_str_in_re_eq_valueSeqString ys hyv] at hy
  exact native_str_in_re_re_concat_intro _ _ _ _ hx hy

/-- Derivatives of the empty language stay empty. -/
theorem native_re_nullable_foldl_empty (xs : List SmtValue) :
    native_re_nullable
        (xs.foldl (fun acc c => native_re_deriv c acc) SmtRegLan.empty) = false := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simpa [native_re_deriv] using ih

theorem model_str_in_re_re_none (xs : List SmtValue) :
    Smtm.native_str_in_re xs native_re_none = false := by
  simp [Smtm.native_str_in_re, native_re_none, native_re_nullable_foldl_empty]

theorem model_str_in_re_re_all (xs : List SmtValue)
    (hValid : native_re_str_valid xs = true) :
    Smtm.native_str_in_re xs native_re_all = true := by
  rw [model_str_in_re_eq_valueSeqString xs hValid]
  exact native_str_in_re_re_all _ (native_string_valid_valueSeqString xs hValid)

/-- Read extensional membership equality off a `RegLan` semantic equality. -/
theorem reglan_str_in_re_eq_of_smt_value_rel {r s : SmtRegLan}
    (h : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s))
    (str : native_String) (hValid : native_string_valid str = true) :
    native_str_in_re str r = native_str_in_re str s := by
  have hModel : ∀ str : native_String,
      native_string_valid str = true ->
        Smtm.native_str_in_re (impl_native_string_to_values str) r =
          Smtm.native_str_in_re (impl_native_string_to_values str) s := by
    change __smtx_model_eval_eq (SmtValue.RegLan r) (SmtValue.RegLan s) =
      SmtValue.Boolean true at h
    simpa [__smtx_model_eval_eq] using h
  rw [native_str_in_re_eq_model str r, native_str_in_re_eq_model str s]
  exact hModel str hValid

end RuleProofs
