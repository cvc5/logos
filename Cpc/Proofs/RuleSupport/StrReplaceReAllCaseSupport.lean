module

public import Cpc.Proofs.RuleSupport.StrReplaceReAllReductionSupport
import all Cpc.Proofs.RuleSupport.StrReplaceReAllReductionSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatSupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatSupport
public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 40000000
set_option maxRecDepth 12000

/-!
The `str_replace_re_all` branch of `string_reduction`.

The generated occurrence-boundary and suffix-result skolems evaluate
directly to the native regex scan.  `StrReplaceReAllReduction.native_scan_spec`
supplies the count, terminal state, and one-step recurrence used below.
-/

namespace StrReplaceReAllCase

open StrReplaceReAllReduction

@[simp] private theorem native_string_to_values_drop
    (s : native_String) (n : Nat) :
    impl_native_string_to_values (s.drop n) =
      (impl_native_string_to_values s).drop n := by
  simp [impl_native_string_to_values, List.map_drop]

/-! ### Stable evaluation equations -/

private theorem eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_var_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_purify_term_eq (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_purify x) =
      __smtx_model_eval__at_purify (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_neg_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__ (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_lt_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt x y) =
      __smtx_model_eval_lt (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_gt_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_str_replace_re_all_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_re_all x y z) =
      __smtx_model_eval_str_replace_re_all
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_str_indexof_re_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof_re x y z) =
      __smtx_model_eval_str_indexof_re
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_str_in_re_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_in_re x y) =
      __smtx_model_eval_str_in_re
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_occur_index_re_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_strings_occur_index_re x y z) =
      __smtx_model_eval__at_strings_occur_index_re
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-! ### Packed-string evaluation -/

private theorem extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i n) =
      native_pack_string (native_str_substr s i n) := by
  have hElem :
      __smtx_elem_typeof_seq_value (native_pack_string s) =
        SmtType.Char := by
    simp [native_pack_string, elem_typeof_pack_seq]
  rw [hElem]
  simp only [native_pack_string, native_seq_extract, native_str_substr,
    native_str_len, Smtm.native_unpack_pack_seq]
  simp only [List.length_map, apply_ite, List.map_nil,
    List.map_take, List.map_drop]
  split <;> simp_all
  -- the `ite` now survives into the goal instead of `simp` having turned it
  -- into an implication, so discharge its condition here
  rcases ‹(0 ≤ i ∧ 0 < n) ∧ i < Int.ofNat s.length› with
    ⟨⟨hi0, hn0⟩, hilt⟩
  rw [if_neg (by
    rintro ((hi | hn) | hlen)
    · exact False.elim ((Int.not_lt_of_ge hi0) hi)
    · exact False.elim ((Int.not_le_of_gt hn0) hn)
    · exact False.elim ((Int.not_le_of_gt hilt) hlen))]
  simp [List.map_take, List.map_drop]

private theorem eval_substr_packed
    (M : SmtModel) (a i n : SmtTerm) (s : native_String)
    (ii nn : native_Int)
    (ha : __smtx_model_eval M a =
      SmtValue.Seq (native_pack_string s))
    (hi : __smtx_model_eval M i = SmtValue.Numeral ii)
    (hn : __smtx_model_eval M n = SmtValue.Numeral nn) :
    __smtx_model_eval M (SmtTerm.str_substr a i n) =
      SmtValue.Seq (native_pack_string (native_str_substr s ii nn)) := by
  rw [StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
    ha, hi, hn]
  simp only [__smtx_model_eval_str_substr]
  exact congrArg SmtValue.Seq (extract_pack_string s ii nn)

private theorem eval_concat_packed
    (M : SmtModel) (a b : SmtTerm) (s t : native_String)
    (ha : __smtx_model_eval M a =
      SmtValue.Seq (native_pack_string s))
    (hb : __smtx_model_eval M b =
      SmtValue.Seq (native_pack_string t)) :
    __smtx_model_eval M (SmtTerm.str_concat a b) =
      SmtValue.Seq (native_pack_string (s ++ t)) := by
  rw [StrSubstrContainsSupport.smtx_eval_str_concat_term_eq, ha, hb]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    native_pack_string, Smtm.native_unpack_pack_seq,
    elem_typeof_pack_seq, List.map_append]

private theorem eval_concat_packed_values
    (M : SmtModel) (a b : SmtTerm) (xs ys : List SmtValue)
    (ha : __smtx_model_eval M a =
      SmtValue.Seq (native_pack_seq SmtType.Char xs))
    (hb : __smtx_model_eval M b =
      SmtValue.Seq (native_pack_seq SmtType.Char ys)) :
    __smtx_model_eval M (SmtTerm.str_concat a b) =
      SmtValue.Seq (native_pack_seq SmtType.Char (xs ++ ys)) := by
  rw [StrSubstrContainsSupport.smtx_eval_str_concat_term_eq, ha, hb]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    RuleProofs.native_unpack_seq_pack_seq, elem_typeof_pack_seq]

private theorem eval_empty_string (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.String []) =
      SmtValue.Seq (native_pack_string []) := by
  rw [__smtx_model_eval.eq_def]

private theorem eval_filtered_re
    (M : SmtModel) (R : SmtTerm) (r : SmtRegLan)
    (hR : __smtx_model_eval M R = SmtValue.RegLan r) :
    __smtx_model_eval M
        (SmtTerm.re_diff R (SmtTerm.str_to_re (SmtTerm.String []))) =
      SmtValue.RegLan (nonemptyRe r) := by
  simp [__smtx_model_eval, __smtx_model_eval_re_diff,
    __smtx_model_eval_str_to_re, hR, nonemptyRe,
    native_str_to_re, impl_native_re_of_list,
    StrLeqConcatSupport.native_unpack_string_pack_string]

private theorem eval_source_len
    (M : SmtModel) (S : SmtTerm) (s : native_String)
    (hS : __smtx_model_eval M S =
      SmtValue.Seq (native_pack_string s)) :
    __smtx_model_eval M (SmtTerm.str_len S) =
      SmtValue.Numeral (Int.ofNat s.length) := by
  rw [smtx_eval_str_len_term_eq, hS]
  simp [__smtx_model_eval_str_len, native_seq_len, native_pack_string,
    Smtm.native_unpack_pack_seq]

private theorem elem_typeof_pack_string (s : native_String) :
    __smtx_elem_typeof_seq_value (native_pack_string s) =
      SmtType.Char := by
  simp [native_pack_string, elem_typeof_pack_seq]

private theorem unpack_seq_pack_string_length (s : native_String) :
    (native_unpack_seq (native_pack_string s)).length = s.length := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

private theorem extract_pack_string_zero_one (s : native_String) :
    native_unpack_string
        (native_pack_seq SmtType.Char
          (native_seq_extract
            (native_unpack_seq (native_pack_string s)) 0 1)) =
      s.take 1 := by
  simp [native_pack_string, native_unpack_string,
    Smtm.native_unpack_pack_seq, native_seq_extract_zero_eq_take,
    List.map_map,
    RuleProofs.map_native_ssm_char_of_value_char]

private theorem extract_pack_string_zero_zero (s : native_String) :
    native_unpack_string
        (native_pack_seq SmtType.Char
          (native_seq_extract
            (native_unpack_seq (native_pack_string s)) 0 0)) =
      [] := by
  simp [native_pack_string, native_unpack_string,
    Smtm.native_unpack_pack_seq, native_seq_extract_zero_eq_take,
    List.map_map,
    RuleProofs.map_native_ssm_char_of_value_char]

private theorem extract_values_pack_string_zero_one (s : native_String) :
    native_seq_extract (native_unpack_seq (native_pack_string s)) 0 1 =
      impl_native_string_to_values (s.take 1) := by
  rw [RuleProofs.native_unpack_seq_pack_string]
  simp [native_seq_extract_zero_eq_take, impl_native_string_to_values,
    List.map_take]

private theorem extract_values_pack_string_zero_zero (s : native_String) :
    native_seq_extract (native_unpack_seq (native_pack_string s)) 0 0 =
      [] := by
  rw [RuleProofs.native_unpack_seq_pack_string]
  simp [native_seq_extract_zero_eq_take]

private theorem extract_zero_one (xs : List SmtValue) :
    native_seq_extract xs 0 1 = xs.take 1 := by
  simpa using native_seq_extract_zero_eq_take xs 1 (by decide)

private theorem extract_zero_zero (xs : List SmtValue) :
    native_seq_extract xs 0 0 = xs.take 0 := by
  simpa using native_seq_extract_zero_eq_take xs 0 (by decide)

private theorem eval_num_occur_re
    (M : SmtModel) (S R : SmtTerm)
    (s : native_String) (r : SmtRegLan)
    (hS : __smtx_model_eval M S =
      SmtValue.Seq (native_pack_string s))
    (hR : __smtx_model_eval M R = SmtValue.RegLan r)
    (hValid : native_string_valid s = true) :
    __smtx_model_eval M
        (SmtTerm.neg
          (SmtTerm.str_len
            (SmtTerm.str_replace_re_all S R
              (SmtTerm.str_substr S (SmtTerm.Numeral 0)
                (SmtTerm.Numeral 1))))
          (SmtTerm.str_len
            (SmtTerm.str_replace_re_all S R
              (SmtTerm.str_substr S (SmtTerm.Numeral 0)
                (SmtTerm.Numeral 0))))) =
      SmtValue.Numeral (Int.ofNat (reEnds r s).length) := by
  have hCount :=
    replace_all_take_one_length_diff_eq_reEnds s r hValid
  rw [eval_neg_term_eq, smtx_eval_str_len_term_eq,
    smtx_eval_str_len_term_eq, eval_str_replace_re_all_term_eq,
    eval_str_replace_re_all_term_eq,
    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
    eval_numeral_term_eq, eval_numeral_term_eq, hS, hR]
  simp only [__smtx_model_eval_str_substr,
    __smtx_model_eval_str_replace_re_all,
    __smtx_model_eval_str_len, __smtx_model_eval__,
    native_seq_len, elem_typeof_pack_string,
    extract_pack_string_zero_one,
    extract_pack_string_zero_zero,
    extract_values_pack_string_zero_one,
    extract_values_pack_string_zero_zero,
    extract_zero_one,
    extract_zero_zero,
    List.take_zero,
    RuleProofs.native_unpack_seq_pack_seq,
    RuleProofs.native_unpack_seq_pack_string,
    StrLeqConcatSupport.native_unpack_string_pack_string]
  simpa [native_zplus, native_zneg, Int.sub_eq_add_neg,
    unpack_seq_pack_string_length] using congrArg SmtValue.Numeral hCount

private theorem eval_occur_index_re
    (M : SmtModel) (S R w : SmtTerm)
    (s : native_String) (r : SmtRegLan) (n : Nat)
    (hS : __smtx_model_eval M S =
      SmtValue.Seq (native_pack_string s))
    (hR : __smtx_model_eval M R = SmtValue.RegLan r)
    (hW : __smtx_model_eval M w = SmtValue.Numeral (Int.ofNat n))
    (hn : n ≤ (reEnds r s).length) :
    __smtx_model_eval M (SmtTerm._at_strings_occur_index_re S R w) =
      SmtValue.Numeral (Int.ofNat (reBound r s n)) := by
  rw [eval_occur_index_re_term_eq, hS, hR, hW]
  simp only [__smtx_model_eval__at_strings_occur_index_re,
    RuleProofs.native_unpack_seq_pack_string,
    StrLeqConcatSupport.native_unpack_string_pack_string]
  rw [occur_index_re_ofNat_eq_reBound]
  simp [hn]

private theorem eval_replace_result
    (M : SmtModel) (S R replacement w : SmtTerm)
    (s repl : native_String) (r : SmtRegLan) (n : Nat)
    (hS : __smtx_model_eval M S =
      SmtValue.Seq (native_pack_string s))
    (hR : __smtx_model_eval M R = SmtValue.RegLan r)
    (hReplacement : __smtx_model_eval M replacement =
      SmtValue.Seq (native_pack_string repl))
    (hValid : native_string_valid s = true)
    (hW : __smtx_model_eval M w = SmtValue.Numeral (Int.ofNat n))
    (hn : n ≤ (reEnds r s).length) :
    __smtx_model_eval M
        (SmtTerm.str_replace_re_all
          (SmtTerm.str_substr S
            (SmtTerm._at_strings_occur_index_re S R w)
            (SmtTerm.str_len S))
          R replacement) =
      SmtValue.Seq
        (native_pack_seq SmtType.Char
          (native_str_replace_re_all
            (impl_native_string_to_values (s.drop (reBound r s n))) r
            (impl_native_string_to_values repl))) := by
  have hOi := eval_occur_index_re M S R w s r n hS hR hW hn
  have hLen := eval_source_len M S s hS
  have hSub := eval_substr_packed M S
    (SmtTerm._at_strings_occur_index_re S R w)
    (SmtTerm.str_len S) s
    (Int.ofNat (reBound r s n)) (Int.ofNat s.length)
    hS hOi hLen
  rw [eval_str_replace_re_all_term_eq, hSub, hR, hReplacement]
  simp only [__smtx_model_eval_str_replace_re_all,
    elem_typeof_pack_string,
    RuleProofs.native_unpack_seq_pack_string,
    StrLeqConcatSupport.native_unpack_string_pack_string]
  rw [full_substr_eq_drop s (reBound r s n)
    (reBound_le_length r s hValid n hn)]

/-! ### Closed arguments and encoded universal quantification -/

private theorem eo_is_closed_of_rec_nil
    (t : Term) (hNe : t ≠ Term.Stuck)
    (hRec :
      __eo_is_closed_rec t Term.__eo_List_nil = Term.Boolean true) :
    __eo_is_closed t = Term.Boolean true := by
  cases t <;> simp [__eo_is_closed] at hNe ⊢
  all_goals exact hRec

private theorem eo_is_closed_ternary_uop_args
    (op : UserOp) (x y z : Term)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNe : x ≠ Term.Stuck) (hYNe : y ≠ Term.Stuck)
    (hZNe : z ≠ Term.Stuck)
    (hClosed :
      __eo_is_closed
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
        Term.Boolean true) :
    __eo_is_closed x = Term.Boolean true ∧
      __eo_is_closed y = Term.Boolean true ∧
        __eo_is_closed z = Term.Boolean true := by
  have hParentRec := eo_is_closed_eq_true_rec_nil hClosed
  have hArgsRec := eo_is_closed_rec_ternary_uop_eq_true_cases
    hNotForall hNotExists
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hParentRec
  exact ⟨eo_is_closed_of_rec_nil x hXNe hArgsRec.1,
    eo_is_closed_of_rec_nil y hYNe hArgsRec.2.1,
    eo_is_closed_of_rec_nil z hZNe hArgsRec.2.2⟩

private theorem eval_forall_encoding_true
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hAll :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T →
        __smtx_value_canonical v = true →
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      SmtValue.Boolean true := by
  classical
  have hNoSat :
      ¬ ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v)
            (SmtTerm.not body) = SmtValue.Boolean true := by
    rintro ⟨v, hvTy, hvCanonical, hvNot⟩
    have hvBody := hAll v hvTy hvCanonical
    simp [__smtx_model_eval, __smtx_model_eval_not, native_not,
      hvBody] at hvNot
  have hExistsEval :
      native_eval_exists M s T (SmtTerm.not body) =
        SmtValue.Boolean false := by
    change (if _h :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v)
              (SmtTerm.not body) = SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean false
    rw [dif_neg hNoSat]
  change __smtx_model_eval_not
      (native_eval_exists M s T (SmtTerm.not body)) =
        SmtValue.Boolean true
  rw [hExistsEval]
  rfl

private theorem eval_exists_is_boolean
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm) :
    ∃ b : native_Bool,
      __smtx_model_eval M (SmtTerm.exists s T body) =
        SmtValue.Boolean b := by
  classical
  change ∃ b : native_Bool,
    (if _h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true then
      SmtValue.Boolean true else SmtValue.Boolean false) =
        SmtValue.Boolean b
  by_cases h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  · exact ⟨true, dif_pos h⟩
  · exact ⟨false, dif_neg h⟩

private theorem var_lookup_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    native_model_var_lookup (native_model_push M s T v) s T = v := by
  simp [native_model_var_lookup, native_model_push]

private theorem var_lookup_push_ne
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v : SmtValue)
    (hNe : s' ≠ s) :
    native_model_var_lookup (native_model_push M s T v) s' T' =
      native_model_var_lookup M s' T' := by
  simp [native_model_var_lookup, native_model_push, SmtModelKey.mk.injEq,
    hNe]

private theorem index_ne_length :
    native_string_lit "@var.str_index" ≠
      native_string_lit "@var.str_length" := by
  decide

private theorem agrees_push_push
    (M : SmtModel) (s₁ : native_String) (T₁ : SmtType) (v₁ : SmtValue)
    (s₂ : native_String) (T₂ : SmtType) (v₂ : SmtValue) :
    model_agrees_on_globals M
      (native_model_push (native_model_push M s₁ T₁ v₁) s₂ T₂ v₂) := by
  refine ⟨?_, ?_⟩
  · intro s' T'
    simp [native_model_lookup, model_key, native_model_push]
  · intro fid A B
    simp [model_fun_lookup, model_key, native_model_push]

/-- The inner generated quantifier says that no positive proper prefix of
the selected match is accepted by the original regex. -/
private theorem eval_shortest_part_true
    (N : SmtModel)
    (tz ty startI matchLen : SmtTerm)
    (lenName : native_String)
    (source : native_String) (regex : SmtRegLan)
    (start len : Nat)
    (hZAt : ∀ v : SmtValue,
      __smtx_model_eval
          (native_model_push N lenName SmtType.Int v) tz =
        SmtValue.Seq (native_pack_string source))
    (hYAt : ∀ v : SmtValue,
      __smtx_model_eval
          (native_model_push N lenName SmtType.Int v) ty =
        SmtValue.RegLan regex)
    (hStartAt : ∀ v : SmtValue,
      __smtx_model_eval
          (native_model_push N lenName SmtType.Int v) startI =
        SmtValue.Numeral (Int.ofNat start))
    (hMatchLenAt : ∀ v : SmtValue,
      __smtx_model_eval
          (native_model_push N lenName SmtType.Int v) matchLen =
        SmtValue.Numeral (Int.ofNat len))
    (hMin : ∀ k : Nat, 0 < k → k < len →
      RuleProofs.native_str_in_re
          (native_str_substr source (Int.ofNat start) (Int.ofNat k))
          regex = false) :
    let lenVar := SmtTerm.Var lenName SmtType.Int
    let shortBody := SmtTerm.or
      (SmtTerm.not (SmtTerm.gt lenVar (SmtTerm.Numeral 0)))
      (SmtTerm.or (SmtTerm.not (SmtTerm.lt lenVar matchLen))
        (SmtTerm.or
          (SmtTerm.not
            (SmtTerm.str_in_re
              (SmtTerm.str_substr tz startI lenVar) ty))
          (SmtTerm.Boolean false)))
    __smtx_model_eval N
        (SmtTerm.not
          (SmtTerm.exists lenName SmtType.Int (SmtTerm.not shortBody))) =
      SmtValue.Boolean true := by
  dsimp only
  apply eval_forall_encoding_true
  intro v hvTy hvCan
  rcases int_value_canonical hvTy with ⟨m, rfl⟩
  let N' := native_model_push N lenName SmtType.Int (SmtValue.Numeral m)
  have hLenVar :
      __smtx_model_eval N' (SmtTerm.Var lenName SmtType.Int) =
        SmtValue.Numeral m := by
    rw [eval_var_term_eq]
    exact var_lookup_push_same N lenName SmtType.Int _
  have hZ := hZAt (SmtValue.Numeral m)
  have hY := hYAt (SmtValue.Numeral m)
  have hStart := hStartAt (SmtValue.Numeral m)
  have hMatchLen := hMatchLenAt (SmtValue.Numeral m)
  dsimp only [N'] at hLenVar hZ hY hStart hMatchLen ⊢
  have hSub :
      __smtx_model_eval
          (native_model_push N lenName SmtType.Int
            (SmtValue.Numeral m))
          (SmtTerm.str_substr tz startI
            (SmtTerm.Var lenName SmtType.Int)) =
        SmtValue.Seq
          (native_pack_string
            (native_str_substr source (Int.ofNat start) m)) := by
    apply eval_substr_packed
    · exact hZ
    · exact hStart
    · exact hLenVar
  have hIn :
      __smtx_model_eval
          (native_model_push N lenName SmtType.Int
            (SmtValue.Numeral m))
          (SmtTerm.str_in_re
            (SmtTerm.str_substr tz startI
              (SmtTerm.Var lenName SmtType.Int)) ty) =
        SmtValue.Boolean
          (RuleProofs.native_str_in_re
            (native_str_substr source (Int.ofNat start) m) regex) := by
    rw [eval_str_in_re_term_eq, hSub, hY]
    simp only [__smtx_model_eval_str_in_re,
      RuleProofs.native_unpack_seq_pack_string]
    rw [RuleProofs.native_str_in_re_eq_model]
  by_cases hmPos : 0 < m
  · by_cases hmLt : m < Int.ofNat len
    · have hmNat : Int.ofNat (Int.toNat m) = m :=
        Int.toNat_of_nonneg (Int.le_of_lt hmPos)
      have hmNatPos : 0 < Int.toNat m := by
        apply Int.ofNat_lt.mp
        rw [Int.toNat_of_nonneg (Int.le_of_lt hmPos)]
        exact hmPos
      have hmNatLt : Int.toNat m < len :=
        (Int.toNat_lt (Int.le_of_lt hmPos)).2 hmLt
      have hMinM :
          RuleProofs.native_str_in_re
              (native_str_substr source (Int.ofNat start) m)
              regex = false := by
        have h := hMin (Int.toNat m) hmNatPos hmNatLt
        rw [hmNat] at h
        exact h
      simp only [smtx_eval_or_term_eq, smtx_eval_not_term_eq,
        eval_gt_term_eq, eval_lt_term_eq, eval_numeral_term_eq,
        eval_boolean_term_eq, hLenVar, hMatchLen, hIn]
      simp only [__smtx_model_eval_or, __smtx_model_eval_not,
        __smtx_model_eval_gt, __smtx_model_eval_lt]
      rw [hMinM]
      simp [native_zlt, native_not, native_or, hmPos, hmLt]
    · simp only [smtx_eval_or_term_eq, smtx_eval_not_term_eq,
        eval_gt_term_eq, eval_lt_term_eq, eval_numeral_term_eq,
        eval_boolean_term_eq, hLenVar, hMatchLen, hIn]
      simp only [__smtx_model_eval_or, __smtx_model_eval_not,
        __smtx_model_eval_gt, __smtx_model_eval_lt]
      simp [native_zlt, native_not, native_or, hmPos, hmLt]
      exact Or.inl (Int.le_of_not_gt hmLt)
  · simp only [smtx_eval_or_term_eq, smtx_eval_not_term_eq,
      eval_gt_term_eq, eval_lt_term_eq, eval_numeral_term_eq,
      eval_boolean_term_eq, hLenVar, hMatchLen, hIn]
    simp only [__smtx_model_eval_or, __smtx_model_eval_not,
      __smtx_model_eval_gt, __smtx_model_eval_lt]
    simp [native_zlt, native_not, native_or, hmPos]

/-! ### The `str_replace_re_all` case -/

set_option maxHeartbeats 40000000 in
/-- The `str_replace_re_all` case of `string_reduction_pred_true`. -/
theorem str_replace_re_all_reduction_pred_true
    (M : SmtModel) (hM : model_wf M) (z y x : Term)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y) x))
    (hClosed : __eo_is_closed
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y) x) =
      Term.Boolean true) :
    eo_interprets M
      (__str_reduction_pred
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y) x))
      true := by
  let tz := __eo_to_smt z
  let ty := __eo_to_smt y
  let tx := __eo_to_smt x
  have hOrigNN :
      term_has_non_none_type (SmtTerm.str_replace_re_all tz ty tx) := by
    have hsimpa := hTrans
    try simp [tz, ty, tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  rcases str_replace_re_args_of_non_none
      (op := SmtTerm.str_replace_re_all)
      (typeof_str_replace_re_all_eq tz ty tx) hOrigNN with
    ⟨hzTy, hyTy, hxTy⟩
  have hZNN : term_has_non_none_type tz := by
    unfold term_has_non_none_type
    rw [hzTy]
    exact seq_ne_none SmtType.Char
  have hYNN : term_has_non_none_type ty := by
    unfold term_has_non_none_type
    rw [hyTy]
    decide
  have hXNN : term_has_non_none_type tx := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact seq_ne_none SmtType.Char
  have hZTermNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z (by
      have hsimpa := hZNN; (try simp [tz, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
  have hYTermNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y (by
      have hsimpa := hYNN; (try simp [ty, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
  have hXTermNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x (by
      have hsimpa := hXNN; (try simp [tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
  have hClosedArgs :
      __eo_is_closed z = Term.Boolean true ∧
        __eo_is_closed y = Term.Boolean true ∧
          __eo_is_closed x = Term.Boolean true := by
    apply eo_is_closed_ternary_uop_args UserOp.str_replace_re_all z y x
    · decide
    · decide
    · exact hZTermNe
    · exact hYTermNe
    · exact hXTermNe
    · exact hClosed
  let idxName := native_string_lit "@var.str_index"
  let lenName := native_string_lit "@var.str_length"
  let idx := SmtTerm.Var idxName SmtType.Int
  let lenVar := SmtTerm.Var lenName SmtType.Int
  let iNext := SmtTerm.plus idx
    (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
  let oi : SmtTerm → SmtTerm := fun w =>
    SmtTerm._at_strings_occur_index_re tz ty w
  let filtered :=
    SmtTerm.re_diff ty (SmtTerm.str_to_re (SmtTerm.String []))
  let startI := SmtTerm.str_indexof_re tz filtered (oi idx)
  let matchLen := SmtTerm.neg (oi iNext) startI
  let matchSeg := SmtTerm.str_substr tz startI matchLen
  let sourceLen := SmtTerm.str_len tz
  let numOcc :=
    SmtTerm.neg
      (SmtTerm.str_len
        (SmtTerm.str_replace_re_all tz ty
          (SmtTerm.str_substr tz (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 1))))
      (SmtTerm.str_len
        (SmtTerm.str_replace_re_all tz ty
          (SmtTerm.str_substr tz (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 0))))
  let rarT : SmtTerm → SmtTerm := fun w =>
    SmtTerm.str_replace_re_all
      (SmtTerm.str_substr tz (oi w) sourceLen) ty tx
  let finalSuffix := SmtTerm.str_substr tz (oi numOcc) sourceLen
  let result :=
    SmtTerm._at_purify (SmtTerm.str_replace_re_all tz ty tx)
  let shortBody := SmtTerm.or
    (SmtTerm.not (SmtTerm.gt lenVar (SmtTerm.Numeral 0)))
    (SmtTerm.or (SmtTerm.not (SmtTerm.lt lenVar matchLen))
      (SmtTerm.or
        (SmtTerm.not
          (SmtTerm.str_in_re
            (SmtTerm.str_substr tz startI lenVar) ty))
        (SmtTerm.Boolean false)))
  let shortestPart := SmtTerm.not
    (SmtTerm.exists lenName SmtType.Int (SmtTerm.not shortBody))
  let stepBody := SmtTerm.or
    (SmtTerm.and (SmtTerm.gt matchLen (SmtTerm.Numeral 0))
      (SmtTerm.and
        (SmtTerm.str_in_re matchSeg filtered)
        (SmtTerm.and shortestPart
          (SmtTerm.and
            (SmtTerm.eq (rarT idx)
              (SmtTerm.str_concat
                (SmtTerm.str_substr tz (oi idx)
                  (SmtTerm.neg startI (oi idx)))
                (SmtTerm.str_concat tx
                  (SmtTerm.str_concat (rarT iNext)
                    (SmtTerm.String [])))))
            (SmtTerm.Boolean true)))))
    (SmtTerm.Boolean false)
  let rangeBody := SmtTerm.or
    (SmtTerm.not (SmtTerm.lt idx numOcc)) stepBody
  let qBody := SmtTerm.or
    (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0))) rangeBody
  let forallPart := SmtTerm.not
    (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
  let noMatch := SmtTerm.eq
    (SmtTerm.str_indexof_re tz filtered (SmtTerm.Numeral 0))
    (SmtTerm.Numeral (-1))
  let formula := SmtTerm.ite noMatch
    (SmtTerm.eq result tz)
    (SmtTerm.and (SmtTerm.gt numOcc (SmtTerm.Numeral 0))
      (SmtTerm.and (SmtTerm.eq result (rarT (SmtTerm.Numeral 0)))
        (SmtTerm.and (SmtTerm.eq (rarT numOcc) finalSuffix)
          (SmtTerm.and
            (SmtTerm.eq (oi (SmtTerm.Numeral 0))
              (SmtTerm.Numeral 0))
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.str_indexof_re finalSuffix filtered
                  (SmtTerm.Numeral 0))
                (SmtTerm.Numeral (-1)))
              (SmtTerm.and forallPart (SmtTerm.Boolean true)))))))
  have hFormulaEq :
      __eo_to_smt
          (__str_reduction_pred
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y)
              x)) =
        formula := by
    simp only [__str_reduction_pred, __eo_mk_apply, hZTermNe,
      hYTermNe, hXTermNe]
    rfl
  have hNumTy : ∀ k : native_Int,
      __smtx_typeof (SmtTerm.Numeral k) = SmtType.Int := by
    intro k
    rw [__smtx_typeof.eq_def] <;> simp only
  have hIdxTy : __smtx_typeof idx = SmtType.Int := by
    dsimp [idx]
    rw [__smtx_typeof.eq_def] <;>
      simp [__smtx_typeof_guard_wf, native_ite, __smtx_type_wf,
        __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  have hLenVarTy : __smtx_typeof lenVar = SmtType.Int := by
    dsimp [lenVar]
    rw [__smtx_typeof.eq_def] <;>
      simp [__smtx_typeof_guard_wf, native_ite, __smtx_type_wf,
        __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  have hBoolTy : ∀ b : native_Bool,
      __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
    intro b
    rw [__smtx_typeof.eq_def] <;> simp only
  have hStringEmptyTy :
      __smtx_typeof (SmtTerm.String []) =
        SmtType.Seq SmtType.Char := by
    rw [__smtx_typeof.eq_def]
    simp [native_string_valid, native_ite]
  have hFilteredTy : __smtx_typeof filtered = SmtType.RegLan := by
    simp [filtered, typeof_re_diff_eq, typeof_str_to_re_eq,
      hStringEmptyTy, hyTy, native_ite, native_Teq]
  have hOiTy : ∀ w : SmtTerm, __smtx_typeof w = SmtType.Int →
      __smtx_typeof (oi w) = SmtType.Int := by
    intro w hw
    simp only [oi]
    rw [__smtx_typeof.eq_def]
    simp [hzTy, hyTy, hw, native_ite, native_Teq]
  have hINextTy : __smtx_typeof iNext = SmtType.Int := by
    simp [iNext, typeof_plus_eq, hIdxTy, hNumTy,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
  have hStartITy : __smtx_typeof startI = SmtType.Int := by
    simp [startI, typeof_str_indexof_re_eq, hzTy, hFilteredTy,
      hOiTy idx hIdxTy, native_ite, native_Teq]
  have hMatchLenTy : __smtx_typeof matchLen = SmtType.Int := by
    simp [matchLen, typeof_neg_eq, hOiTy iNext hINextTy, hStartITy,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
  have hMatchSegTy :
      __smtx_typeof matchSeg = SmtType.Seq SmtType.Char := by
    simp [matchSeg, typeof_str_substr_eq, hzTy, hStartITy, hMatchLenTy,
      __smtx_typeof_str_substr, native_ite, native_Teq]
  have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
    simp [sourceLen, typeof_str_len_eq, hzTy,
      __smtx_typeof_seq_op_1_ret]
  have hNumOccTy : __smtx_typeof numOcc = SmtType.Int := by
    simp [numOcc, typeof_neg_eq,
      typeof_str_len_eq, typeof_str_replace_re_all_eq,
      typeof_str_substr_eq, hzTy, hyTy, hNumTy,
      __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_seq_op_1_ret, native_ite, native_Teq]
  have hRarTy : ∀ w : SmtTerm, __smtx_typeof w = SmtType.Int →
      __smtx_typeof (rarT w) = SmtType.Seq SmtType.Char := by
    intro w hw
    simp [rarT, typeof_str_replace_re_all_eq, typeof_str_substr_eq,
      hzTy, hyTy, hxTy, hOiTy w hw, hSourceLenTy,
      __smtx_typeof_str_substr, native_ite, native_Teq]
  have hFinalSuffixTy :
      __smtx_typeof finalSuffix = SmtType.Seq SmtType.Char := by
    simp [finalSuffix, typeof_str_substr_eq, hzTy,
      hOiTy numOcc hNumOccTy, hSourceLenTy,
      __smtx_typeof_str_substr, native_ite, native_Teq]
  have hResultTy :
      __smtx_typeof result = SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_replace_re_all tz ty tx) =
      SmtType.Seq SmtType.Char
    simp [typeof_str_replace_re_all_eq, hzTy, hyTy, hxTy,
      native_ite, native_Teq]
  have hShortBodyTy : __smtx_typeof shortBody = SmtType.Bool := by
    simp [shortBody, typeof_or_eq, typeof_not_eq, typeof_gt_eq,
      typeof_lt_eq, typeof_str_in_re_eq, typeof_str_substr_eq,
      hLenVarTy, hNumTy, hMatchLenTy, hzTy, hStartITy, hyTy, hBoolTy,
      __smtx_typeof_str_substr, __smtx_typeof_seq_op_2_ret,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      __smtx_typeof_guard_wf, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and, native_ite, native_Teq]
  have hShortestTy : __smtx_typeof shortestPart = SmtType.Bool := by
    simp [shortestPart, typeof_not_eq, smtx_typeof_exists_term_eq,
      hShortBodyTy, __smtx_typeof_guard, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and, native_ite, native_Teq]
  have hGapTy :
      __smtx_typeof
          (SmtTerm.str_substr tz (oi idx)
            (SmtTerm.neg startI (oi idx))) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_substr_eq, typeof_neg_eq, hzTy, hOiTy idx hIdxTy,
      hStartITy, __smtx_typeof_str_substr,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
  have hRecRhsTy :
      __smtx_typeof
          (SmtTerm.str_concat
            (SmtTerm.str_substr tz (oi idx)
              (SmtTerm.neg startI (oi idx)))
            (SmtTerm.str_concat tx
              (SmtTerm.str_concat (rarT iNext) (SmtTerm.String [])))) =
        SmtType.Seq SmtType.Char := by
    simp [typeof_str_concat_eq, hGapTy, hxTy,
      hRarTy iNext hINextTy, hStringEmptyTy,
      __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hStepBodyTy : __smtx_typeof stepBody = SmtType.Bool := by
    simp [stepBody, typeof_or_eq, typeof_and_eq, typeof_not_eq,
      typeof_lt_eq, typeof_gt_eq, typeof_eq_eq,
      typeof_str_in_re_eq, typeof_str_concat_eq, typeof_str_substr_eq,
      typeof_neg_eq, hIdxTy, hNumTy, hNumOccTy, hMatchLenTy,
      hMatchSegTy, hFilteredTy, hShortestTy, hStartITy,
      hOiTy idx hIdxTy, hRarTy idx hIdxTy, hxTy,
      hRarTy iNext hINextTy, hStringEmptyTy, hGapTy, hRecRhsTy, hBoolTy,
      __smtx_typeof_eq, __smtx_typeof_seq_op_2,
      __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      __smtx_typeof_guard_wf, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and, native_ite, native_Teq]
  have hRangeBodyTy : __smtx_typeof rangeBody = SmtType.Bool := by
    simp [rangeBody, typeof_or_eq, typeof_not_eq, typeof_lt_eq,
      hIdxTy, hNumOccTy, hStepBodyTy,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq]
  have hQBodyTy : __smtx_typeof qBody = SmtType.Bool := by
    simp [qBody, typeof_or_eq, typeof_not_eq, typeof_geq_eq,
      hIdxTy, hNumTy, hRangeBodyTy,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq]
  apply RuleProofs.eo_interprets_of_bool_eval M _ true
  · unfold RuleProofs.eo_has_bool_type
    rw [hFormulaEq]
    simp [formula, noMatch, forallPart, typeof_ite_eq, typeof_and_eq,
      typeof_eq_eq, typeof_gt_eq, typeof_str_indexof_re_eq,
      typeof_not_eq, smtx_typeof_exists_term_eq,
      hFilteredTy, hzTy, hNumTy, hResultTy, hRarTy, hNumOccTy,
      hFinalSuffixTy, hOiTy, hQBodyTy, hBoolTy,
      __smtx_typeof_eq, __smtx_typeof_ite,
      __smtx_typeof_arith_overload_op_2_ret,
      __smtx_typeof_guard, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and, native_ite, native_Teq]
  · rw [hFormulaEq]
    have hZValTy :
        __smtx_typeof_value (__smtx_model_eval M tz) =
          SmtType.Seq SmtType.Char := by
      simpa [tz, hzTy] using
        smt_model_eval_preserves_type_of_non_none M hM tz hZNN
    have hYValTy :
        __smtx_typeof_value (__smtx_model_eval M ty) =
          SmtType.RegLan := by
      simpa [ty, hyTy] using
        smt_model_eval_preserves_type_of_non_none M hM ty hYNN
    have hXValTy :
        __smtx_typeof_value (__smtx_model_eval M tx) =
          SmtType.Seq SmtType.Char := by
      simpa [tx, hxTy] using
        smt_model_eval_preserves_type_of_non_none M hM tx hXNN
    rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
    rcases reglan_value_canonical hYValTy with ⟨regex, hYEval⟩
    rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
    have hSzTy :
        __smtx_typeof_seq_value sz =
          SmtType.Seq SmtType.Char := by
      simpa [hZEval, __smtx_typeof_value] using hZValTy
    have hSxTy :
        __smtx_typeof_seq_value sx =
          SmtType.Seq SmtType.Char := by
      simpa [hXEval, __smtx_typeof_value] using hXValTy
    let source := native_unpack_string sz
    let replacement := native_unpack_string sx
    have hSourceValid : native_string_valid source = true :=
      native_unpack_string_valid_of_typeof_seq_char hSzTy
    have hSourcePack : native_pack_string source = sz :=
      StrLeqConcatSupport.native_pack_string_unpack_string_of_typeof_seq_char
        sz hSzTy
    have hReplacementPack : native_pack_string replacement = sx :=
      StrLeqConcatSupport.native_pack_string_unpack_string_of_typeof_seq_char
        sx hSxTy
    have hZEvalString :
        __smtx_model_eval M tz =
          SmtValue.Seq (native_pack_string source) := by
      rw [hSourcePack]
      exact hZEval
    have hXEvalString :
        __smtx_model_eval M tx =
          SmtValue.Seq (native_pack_string replacement) := by
      rw [hReplacementPack]
      exact hXEval
    have hZAt : ∀ N : SmtModel, model_agrees_on_globals M N →
        __smtx_model_eval N tz =
          SmtValue.Seq (native_pack_string source) := by
      intro N hAgree
      rw [← hZEvalString]
      exact
        (smt_model_eval_eq_of_eo_closed z hClosedArgs.1 M N hAgree).symm
    have hYAt : ∀ N : SmtModel, model_agrees_on_globals M N →
        __smtx_model_eval N ty = SmtValue.RegLan regex := by
      intro N hAgree
      rw [← hYEval]
      exact
        (smt_model_eval_eq_of_eo_closed y hClosedArgs.2.1 M N hAgree).symm
    have hXAt : ∀ N : SmtModel, model_agrees_on_globals M N →
        __smtx_model_eval N tx =
          SmtValue.Seq (native_pack_string replacement) := by
      intro N hAgree
      rw [← hXEvalString]
      exact
        (smt_model_eval_eq_of_eo_closed x hClosedArgs.2.2 M N hAgree).symm
    have hFilteredEval :
        __smtx_model_eval M filtered =
          SmtValue.RegLan (nonemptyRe regex) := by
      exact eval_filtered_re M ty regex hYEval
    have hNumOccEval :
        __smtx_model_eval M numOcc =
          SmtValue.Numeral (Int.ofNat (reEnds regex source).length) := by
      exact eval_num_occur_re M tz ty source regex
        hZEvalString hYEval hSourceValid
    have hResultEval :
        __smtx_model_eval M result =
          SmtValue.Seq
            (native_pack_seq SmtType.Char
              (native_str_replace_re_all
                (impl_native_string_to_values source) regex
                (impl_native_string_to_values replacement))) := by
      simp only [result]
      rw [eval_purify_term_eq, eval_str_replace_re_all_term_eq,
        hZEvalString, hYEval, hXEvalString]
      simp [__smtx_model_eval__at_purify,
        __smtx_model_eval_str_replace_re_all,
        elem_typeof_pack_string,
        RuleProofs.native_unpack_seq_pack_string,
        StrLeqConcatSupport.native_unpack_string_pack_string]
    have hScan := native_scan_spec regex source hSourceValid
    rw [smtx_eval_ite_term_eq]
    by_cases hNo :
        native_str_indexof_re source (nonemptyRe regex) 0 = -1
    · have hNoMatchEval :
          __smtx_model_eval M noMatch = SmtValue.Boolean true := by
        simp only [noMatch]
        rw [smtx_eval_eq_term_eq, eval_str_indexof_re_term_eq,
          hZEvalString, hFilteredEval, eval_numeral_term_eq,
          eval_numeral_term_eq]
        simp [__smtx_model_eval_str_indexof_re,
          RuleProofs.native_unpack_seq_pack_string,
          StrLeqConcatSupport.native_unpack_string_pack_string,
          hNo, __smtx_model_eval_eq, native_veq]
      rw [hNoMatchEval]
      simp only [__smtx_model_eval_ite]
      have hReplaceSelf :=
        replace_all_eq_self_of_initial_index_neg_one
          regex source replacement hSourceValid hNo
      rw [smtx_eval_eq_term_eq, hResultEval, hZEvalString, hReplaceSelf]
      simp [__smtx_model_eval_eq, veq_refl_true,
        native_pack_string, impl_native_string_to_values]
    · have hNoMatchEval :
          __smtx_model_eval M noMatch = SmtValue.Boolean false := by
        simp only [noMatch]
        rw [smtx_eval_eq_term_eq, eval_str_indexof_re_term_eq,
          hZEvalString, hFilteredEval, eval_numeral_term_eq,
          eval_numeral_term_eq]
        simp only [__smtx_model_eval_str_indexof_re,
          RuleProofs.native_unpack_seq_pack_string,
          StrLeqConcatSupport.native_unpack_string_pack_string]
        have hNe :
            SmtValue.Numeral
                (native_str_indexof_re source (nonemptyRe regex) 0) ≠
              SmtValue.Numeral (-1) := by
          intro h
          injection h with h'
          exact hNo h'
        have hVeq :
            native_veq
                (SmtValue.Numeral
                  (native_str_indexof_re source (nonemptyRe regex) 0))
                (SmtValue.Numeral (-1)) = false := by
          cases hb :
              native_veq
                (SmtValue.Numeral
                  (native_str_indexof_re source (nonemptyRe regex) 0))
                (SmtValue.Numeral (-1)) with
          | true => exact absurd (eq_of_native_veq_true hb) hNe
          | false => rfl
        simp [__smtx_model_eval_eq, hVeq]
      rw [hNoMatchEval]
      simp only [__smtx_model_eval_ite]
      have hCountPos :
          0 < (reEnds regex source).length :=
        reEnds_length_pos_of_initial_index_ne_neg_one
          regex source hSourceValid hNo
      have hC1 :
          __smtx_model_eval M
              (SmtTerm.gt numOcc (SmtTerm.Numeral 0)) =
            SmtValue.Boolean true := by
        rw [eval_gt_term_eq, hNumOccEval, eval_numeral_term_eq]
        simp only [__smtx_model_eval_gt, __smtx_model_eval_lt,
          native_zlt, SmtValue.Boolean.injEq, decide_eq_true_eq]
        simpa [Int.ofNat_eq_natCast] using
          (Int.natCast_pos.mpr hCountPos)
      have hZeroEval :
          __smtx_model_eval M (SmtTerm.Numeral 0) =
            SmtValue.Numeral (Int.ofNat 0) := by
        simp [eval_numeral_term_eq]
      have hRar0Eval :
        __smtx_model_eval M (rarT (SmtTerm.Numeral 0)) =
            SmtValue.Seq
              (native_pack_seq SmtType.Char
                (native_str_replace_re_all
                  (impl_native_string_to_values source) regex
                  (impl_native_string_to_values replacement))) := by
        have h :=
          eval_replace_result M tz ty tx (SmtTerm.Numeral 0)
            source replacement regex 0 hZEvalString hYEval
            hXEvalString hSourceValid hZeroEval (Nat.zero_le _)
        simpa [rarT, oi, sourceLen, reBound_zero] using h
      have hC2 :
          __smtx_model_eval M
              (SmtTerm.eq result (rarT (SmtTerm.Numeral 0))) =
            SmtValue.Boolean true := by
        rw [smtx_eval_eq_term_eq, hResultEval, hRar0Eval]
        simp [__smtx_model_eval_eq, veq_refl_true]
      have hOiFinalEval :
          __smtx_model_eval M (oi numOcc) =
            SmtValue.Numeral
              (Int.ofNat
                (reBound regex source (reEnds regex source).length)) := by
        have h :=
          eval_occur_index_re M tz ty numOcc source regex
            (reEnds regex source).length hZEvalString hYEval
            hNumOccEval (Nat.le_refl _)
        simpa [oi] using h
      have hRarFinalEval :
          __smtx_model_eval M (rarT numOcc) =
            SmtValue.Seq
              (native_pack_seq SmtType.Char
                (native_str_replace_re_all
                  (impl_native_string_to_values
                    (source.drop
                      (reBound regex source (reEnds regex source).length)))
                  regex (impl_native_string_to_values replacement))) := by
        have h :=
          eval_replace_result M tz ty tx numOcc source replacement regex
            (reEnds regex source).length hZEvalString hYEval
            hXEvalString hSourceValid hNumOccEval (Nat.le_refl _)
        simpa [rarT, oi, sourceLen] using h
      have hSourceLenEval := eval_source_len M tz source hZEvalString
      have hFinalSuffixEval :
          __smtx_model_eval M finalSuffix =
            SmtValue.Seq
              (native_pack_string
                (source.drop
                  (reBound regex source (reEnds regex source).length))) := by
        have hSub :=
          eval_substr_packed M tz (oi numOcc) sourceLen source
            (Int.ofNat
              (reBound regex source (reEnds regex source).length))
            (Int.ofNat source.length) hZEvalString hOiFinalEval
            hSourceLenEval
        rw [full_substr_eq_drop source _
          (reBound_le_length regex source hSourceValid _
            (Nat.le_refl _))] at hSub
        simpa [finalSuffix] using hSub
      have hC3 :
          __smtx_model_eval M
              (SmtTerm.eq (rarT numOcc) finalSuffix) =
            SmtValue.Boolean true := by
        rw [smtx_eval_eq_term_eq, hRarFinalEval, hFinalSuffixEval,
          native_string_to_values_drop,
          replace_all_at_final_reBound_eq_self
            regex source replacement hSourceValid]
        simp [__smtx_model_eval_eq, veq_refl_true,
          native_pack_string, impl_native_string_to_values]
      have hOiZeroEval :
          __smtx_model_eval M (oi (SmtTerm.Numeral 0)) =
            SmtValue.Numeral 0 := by
        have h :=
          eval_occur_index_re M tz ty (SmtTerm.Numeral 0)
            source regex 0 hZEvalString hYEval hZeroEval
            (Nat.zero_le _)
        simpa [oi, reBound_zero] using h
      have hC4 :
          __smtx_model_eval M
              (SmtTerm.eq (oi (SmtTerm.Numeral 0))
                (SmtTerm.Numeral 0)) =
            SmtValue.Boolean true := by
        rw [smtx_eval_eq_term_eq, hOiZeroEval, eval_numeral_term_eq]
        simp [__smtx_model_eval_eq, native_veq]
      have hC5 :
          __smtx_model_eval M
              (SmtTerm.eq
                (SmtTerm.str_indexof_re finalSuffix filtered
                  (SmtTerm.Numeral 0))
                (SmtTerm.Numeral (-1))) =
            SmtValue.Boolean true := by
        rw [smtx_eval_eq_term_eq, eval_str_indexof_re_term_eq,
          hFinalSuffixEval, hFilteredEval, eval_numeral_term_eq,
          eval_numeral_term_eq]
        simp only [__smtx_model_eval_str_indexof_re,
          RuleProofs.native_unpack_seq_pack_string,
          StrLeqConcatSupport.native_unpack_string_pack_string]
        rw [native_string_to_values_drop,
          indexof_nonemptyRe_on_final_suffix_eq_neg_one
          regex source hSourceValid]
        simp [__smtx_model_eval_eq, native_veq]
      have hC6 :
          __smtx_model_eval M forallPart =
            SmtValue.Boolean true := by
        simp only [forallPart]
        apply eval_forall_encoding_true
        intro v hvTy hvCan
        rcases int_value_canonical hvTy with ⟨m, rfl⟩
        let N :=
          native_model_push M idxName SmtType.Int (SmtValue.Numeral m)
        have hNTotal : model_wf N := by
          apply model_total_typed_push hM idxName SmtType.Int
            (SmtValue.Numeral m)
          · simp [__smtx_type_wf, __smtx_type_wf_component,
              __smtx_type_wf_rec, native_and]
          · simp [__smtx_typeof_value]
          · exact hvCan
        have hAgreeN : model_agrees_on_globals M N := by
          simpa [N] using
            (model_agrees_on_globals_push M idxName SmtType.Int
              (SmtValue.Numeral m))
        have hZN := hZAt N hAgreeN
        have hYN := hYAt N hAgreeN
        have hXN := hXAt N hAgreeN
        have hFilteredN :
            __smtx_model_eval N filtered =
              SmtValue.RegLan (nonemptyRe regex) :=
          eval_filtered_re N ty regex hYN
        have hNumN :
            __smtx_model_eval N numOcc =
              SmtValue.Numeral
                (Int.ofNat (reEnds regex source).length) :=
          eval_num_occur_re N tz ty source regex hZN hYN hSourceValid
        have hIdxN :
            __smtx_model_eval N idx = SmtValue.Numeral m := by
          simp only [idx, N]
          rw [eval_var_term_eq]
          exact var_lookup_push_same M idxName SmtType.Int _
        by_cases hm0 : 0 ≤ m
        · by_cases hmK :
              m < Int.ofNat (reEnds regex source).length
          · -- the semantic scan step proves the in-range clause
            let n := Int.toNat m
            have hmNat : Int.ofNat n = m := by
              exact Int.toNat_of_nonneg hm0
            have hn : n < (reEnds regex source).length := by
              exact (Int.toNat_lt hm0).2 hmK
            rcases hScan.step n hn with
              ⟨start, matchLength, hMatchLengthPos, hBoundary,
                hEnd, hIndex, hMatch, hMin, hReplace⟩
            have hIdxNat :
                __smtx_model_eval N idx =
                  SmtValue.Numeral (Int.ofNat n) := by
              rw [hIdxN]
              congr 1
              exact hmNat.symm
            have hINextN :
                __smtx_model_eval N iNext =
                  SmtValue.Numeral (Int.ofNat (n + 1)) := by
              simp only [iNext]
              rw [StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                hIdxN, eval_numeral_term_eq, eval_numeral_term_eq]
              simp only [__smtx_model_eval_plus, native_zplus]
              congr 1
              rw [← hmNat]
              simp [native_zplus]
            have hOiN :
                __smtx_model_eval N (oi idx) =
                  SmtValue.Numeral
                    (Int.ofNat (reBound regex source n)) := by
              have h :=
                eval_occur_index_re N tz ty idx source regex n
                  hZN hYN hIdxNat (Nat.le_of_lt hn)
              simpa [oi] using h
            have hOiNextN :
                __smtx_model_eval N (oi iNext) =
                  SmtValue.Numeral
                    (Int.ofNat (reBound regex source (n + 1))) := by
              have h :=
                eval_occur_index_re N tz ty iNext source regex (n + 1)
                  hZN hYN hINextN (by omega)
              simpa [oi] using h
            have hStartN :
                __smtx_model_eval N startI =
                  SmtValue.Numeral (Int.ofNat start) := by
              simp only [startI]
              rw [eval_str_indexof_re_term_eq, hZN, hFilteredN, hOiN]
              simp only [__smtx_model_eval_str_indexof_re,
                RuleProofs.native_unpack_seq_pack_string,
                StrLeqConcatSupport.native_unpack_string_pack_string]
              rw [hIndex]
            have hMatchLenN :
                __smtx_model_eval N matchLen =
                  SmtValue.Numeral (Int.ofNat matchLength) := by
              simp only [matchLen]
              rw [eval_neg_term_eq, hOiNextN, hStartN]
              simp only [__smtx_model_eval__, native_zplus, native_zneg]
              congr 1
              have hStartLe :
                  start ≤ reBound regex source (n + 1) := by
                omega
              have hDiff :
                  reBound regex source (n + 1) - start =
                    matchLength := by
                omega
              have hCast := Int.ofNat_sub hStartLe
              rw [hDiff] at hCast
              have hsimpa := hCast.symm
              try simp only [Int.sub_eq_add_neg] at hsimpa ⊢
              exact hsimpa
            have hMatchSegN :
                __smtx_model_eval N matchSeg =
                  SmtValue.Seq
                    (native_pack_string
                      (native_str_substr source (Int.ofNat start)
                        (Int.ofNat matchLength))) := by
              have h :=
                eval_substr_packed N tz startI matchLen source
                  (Int.ofNat start) (Int.ofNat matchLength)
                  hZN hStartN hMatchLenN
              simpa [matchSeg] using h
            have hMatchInN :
                __smtx_model_eval N
                    (SmtTerm.str_in_re matchSeg filtered) =
                  SmtValue.Boolean true := by
              rw [eval_str_in_re_term_eq, hMatchSegN, hFilteredN]
              simp only [__smtx_model_eval_str_in_re,
                RuleProofs.native_unpack_seq_pack_string,
                StrLeqConcatSupport.native_unpack_string_pack_string]
              rw [← RuleProofs.native_str_in_re_eq_model, hMatch]
            have hRarN :
                __smtx_model_eval N (rarT idx) =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (native_str_replace_re_all
                        (impl_native_string_to_values
                          (source.drop (reBound regex source n)))
                        regex (impl_native_string_to_values replacement))) := by
              have h :=
                eval_replace_result N tz ty tx idx source replacement
                  regex n hZN hYN hXN hSourceValid hIdxNat
                  (Nat.le_of_lt hn)
              simpa [rarT, oi, sourceLen] using h
            have hRarNextN :
                __smtx_model_eval N (rarT iNext) =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (native_str_replace_re_all
                        (impl_native_string_to_values
                          (source.drop (reBound regex source (n + 1))))
                        regex (impl_native_string_to_values replacement))) := by
              have h :=
                eval_replace_result N tz ty tx iNext source replacement
                  regex (n + 1) hZN hYN hXN hSourceValid hINextN
                  (by omega)
              simpa [rarT, oi, sourceLen] using h
            have hGapLenN :
                __smtx_model_eval N
                    (SmtTerm.neg startI (oi idx)) =
                  SmtValue.Numeral
                    (Int.ofNat (start - reBound regex source n)) := by
              rw [eval_neg_term_eq, hStartN, hOiN]
              simp only [__smtx_model_eval__, native_zplus, native_zneg]
              congr 1
              have hsimpa :=
                (Int.ofNat_sub hBoundary).symm
              try simp only [Int.sub_eq_add_neg] at hsimpa ⊢
              exact hsimpa
            have hGapN :
                __smtx_model_eval N
                    (SmtTerm.str_substr tz (oi idx)
                      (SmtTerm.neg startI (oi idx))) =
                  SmtValue.Seq
                    (native_pack_string
                      (native_str_substr source
                        (Int.ofNat (reBound regex source n))
                        (Int.ofNat
                          (start - reBound regex source n)))) := by
              exact eval_substr_packed N tz (oi idx)
                (SmtTerm.neg startI (oi idx)) source
                (Int.ofNat (reBound regex source n))
                (Int.ofNat (start - reBound regex source n))
                hZN hOiN hGapLenN
            have hEmptyN := eval_empty_string N
            have hEmptyValues :
                __smtx_model_eval N (SmtTerm.String []) =
                  SmtValue.Seq (native_pack_seq SmtType.Char []) := by
              simpa [native_pack_string] using hEmptyN
            have hTailConcatN :
                __smtx_model_eval N
                    (SmtTerm.str_concat (rarT iNext)
                      (SmtTerm.String [])) =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (native_str_replace_re_all
                          (impl_native_string_to_values
                            (source.drop
                              (reBound regex source (n + 1))))
                          regex (impl_native_string_to_values replacement) ++
                        [])) := by
              exact eval_concat_packed_values N (rarT iNext)
                (SmtTerm.String [])
                (native_str_replace_re_all
                  (impl_native_string_to_values
                    (source.drop (reBound regex source (n + 1))))
                  regex (impl_native_string_to_values replacement)) []
                hRarNextN hEmptyValues
            have hReplacementValues :
                __smtx_model_eval N tx =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (impl_native_string_to_values replacement)) := by
              simpa [native_pack_string, impl_native_string_to_values] using hXN
            have hReplacementConcatN :
                __smtx_model_eval N
                    (SmtTerm.str_concat tx
                      (SmtTerm.str_concat (rarT iNext)
                        (SmtTerm.String []))) =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (impl_native_string_to_values replacement ++
                        (native_str_replace_re_all
                            (impl_native_string_to_values
                              (source.drop
                                (reBound regex source (n + 1))))
                            regex (impl_native_string_to_values replacement) ++
                          []))) := by
              exact eval_concat_packed_values N tx
                (SmtTerm.str_concat (rarT iNext) (SmtTerm.String []))
                (impl_native_string_to_values replacement)
                (native_str_replace_re_all
                    (impl_native_string_to_values
                      (source.drop (reBound regex source (n + 1))))
                    regex (impl_native_string_to_values replacement) ++ [])
                hReplacementValues hTailConcatN
            have hGapValues :
                __smtx_model_eval N
                    (SmtTerm.str_substr tz (oi idx)
                      (SmtTerm.neg startI (oi idx))) =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (impl_native_string_to_values
                        (native_str_substr source
                          (Int.ofNat (reBound regex source n))
                          (Int.ofNat
                            (start - reBound regex source n))))) := by
              simpa [native_pack_string, impl_native_string_to_values] using hGapN
            have hRecRhsN :
                __smtx_model_eval N
                    (SmtTerm.str_concat
                      (SmtTerm.str_substr tz (oi idx)
                        (SmtTerm.neg startI (oi idx)))
                      (SmtTerm.str_concat tx
                        (SmtTerm.str_concat (rarT iNext)
                          (SmtTerm.String [])))) =
                  SmtValue.Seq
                    (native_pack_seq SmtType.Char
                      (impl_native_string_to_values
                          (native_str_substr source
                            (Int.ofNat (reBound regex source n))
                            (Int.ofNat
                              (start - reBound regex source n))) ++
                        (impl_native_string_to_values replacement ++
                          (native_str_replace_re_all
                              (impl_native_string_to_values
                                (source.drop
                                  (reBound regex source (n + 1))))
                              regex (impl_native_string_to_values replacement) ++
                            [])))) := by
              exact eval_concat_packed_values N
                (SmtTerm.str_substr tz (oi idx)
                  (SmtTerm.neg startI (oi idx)))
                (SmtTerm.str_concat tx
                  (SmtTerm.str_concat (rarT iNext) (SmtTerm.String [])))
                (impl_native_string_to_values
                  (native_str_substr source
                    (Int.ofNat (reBound regex source n))
                    (Int.ofNat (start - reBound regex source n))))
                (impl_native_string_to_values replacement ++
                  (native_str_replace_re_all
                      (impl_native_string_to_values
                        (source.drop (reBound regex source (n + 1))))
                      regex (impl_native_string_to_values replacement) ++ []))
                hGapValues hReplacementConcatN
            have hNativeRec :
                native_str_replace_re_all
                    (impl_native_string_to_values
                      (source.drop (reBound regex source n)))
                    regex (impl_native_string_to_values replacement) =
                  impl_native_string_to_values
                      (native_str_substr source
                        (Int.ofNat (reBound regex source n))
                        (Int.ofNat (start - reBound regex source n))) ++
                    (impl_native_string_to_values replacement ++
                      (native_str_replace_re_all
                          (impl_native_string_to_values
                            (source.drop
                              (reBound regex source (n + 1))))
                          regex (impl_native_string_to_values replacement) ++
                        [])) := by
              simpa only [List.append_nil, List.append_assoc,
                native_string_to_values_drop] using
                hReplace replacement
            have hRecEqN :
                __smtx_model_eval N
                    (SmtTerm.eq (rarT idx)
                      (SmtTerm.str_concat
                        (SmtTerm.str_substr tz (oi idx)
                          (SmtTerm.neg startI (oi idx)))
                        (SmtTerm.str_concat tx
                          (SmtTerm.str_concat (rarT iNext)
                            (SmtTerm.String []))))) =
                  SmtValue.Boolean true := by
              rw [smtx_eval_eq_term_eq, hRarN, hRecRhsN, hNativeRec]
              simp [__smtx_model_eval_eq, veq_refl_true]
            have hZLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v) tz =
                  SmtValue.Seq (native_pack_string source) := by
              intro v
              exact hZAt _
                (agrees_push_push M idxName SmtType.Int
                  (SmtValue.Numeral m) lenName SmtType.Int v)
            have hYLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v) ty =
                  SmtValue.RegLan regex := by
              intro v
              exact hYAt _
                (agrees_push_push M idxName SmtType.Int
                  (SmtValue.Numeral m) lenName SmtType.Int v)
            have hIdxLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v) idx =
                  SmtValue.Numeral (Int.ofNat n) := by
              intro v
              simp only [idx]
              rw [eval_var_term_eq,
                var_lookup_push_ne N lenName idxName SmtType.Int
                  SmtType.Int v (by
                    simpa [idxName, lenName] using index_ne_length)]
              exact hIdxNat
            have hINextLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v) iNext =
                  SmtValue.Numeral (Int.ofNat (n + 1)) := by
              intro v
              simp only [iNext]
              rw [StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                hIdxLen v, eval_numeral_term_eq,
                eval_numeral_term_eq]
              simp [__smtx_model_eval_plus, native_zplus,
                Int.ofNat_eq_natCast]
            have hOiLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v)
                    (oi idx) =
                  SmtValue.Numeral
                    (Int.ofNat (reBound regex source n)) := by
              intro v
              have h :=
                eval_occur_index_re
                  (native_model_push N lenName SmtType.Int v)
                  tz ty idx source regex n (hZLen v) (hYLen v)
                  (hIdxLen v) (Nat.le_of_lt hn)
              simpa [oi] using h
            have hOiNextLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v)
                    (oi iNext) =
                  SmtValue.Numeral
                    (Int.ofNat (reBound regex source (n + 1))) := by
              intro v
              have h :=
                eval_occur_index_re
                  (native_model_push N lenName SmtType.Int v)
                  tz ty iNext source regex (n + 1) (hZLen v) (hYLen v)
                  (hINextLen v) (by omega)
              simpa [oi] using h
            have hStartLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v) startI =
                  SmtValue.Numeral (Int.ofNat start) := by
              intro v
              have hFilteredLen :=
                eval_filtered_re
                  (native_model_push N lenName SmtType.Int v)
                  ty regex (hYLen v)
              simp only [startI]
              rw [eval_str_indexof_re_term_eq, hZLen v,
                hFilteredLen, hOiLen v]
              simp only [__smtx_model_eval_str_indexof_re,
                RuleProofs.native_unpack_seq_pack_string,
                StrLeqConcatSupport.native_unpack_string_pack_string]
              rw [hIndex]
            have hMatchLenLen : ∀ v : SmtValue,
                __smtx_model_eval
                    (native_model_push N lenName SmtType.Int v)
                    matchLen =
                  SmtValue.Numeral (Int.ofNat matchLength) := by
              intro v
              simp only [matchLen]
              rw [eval_neg_term_eq, hOiNextLen v, hStartLen v]
              simp only [__smtx_model_eval__, native_zplus, native_zneg]
              congr 1
              have hStartLe :
                  start ≤ reBound regex source (n + 1) := by
                omega
              have hDiff :
                  reBound regex source (n + 1) - start =
                    matchLength := by
                omega
              have hCast := Int.ofNat_sub hStartLe
              rw [hDiff] at hCast
              have hsimpa := hCast.symm
              try simp only [Int.sub_eq_add_neg] at hsimpa ⊢
              exact hsimpa
            have hShortestN :
                __smtx_model_eval N shortestPart =
                  SmtValue.Boolean true := by
              have h :=
                eval_shortest_part_true N tz ty startI matchLen lenName
                  source regex start matchLength hZLen hYLen hStartLen
                  hMatchLenLen hMin
              simpa [shortestPart, shortBody, lenVar] using h
            have hMatchLenGtN :
                __smtx_model_eval N
                    (SmtTerm.gt matchLen (SmtTerm.Numeral 0)) =
                  SmtValue.Boolean true := by
              rw [eval_gt_term_eq, hMatchLenN, eval_numeral_term_eq]
              simp only [__smtx_model_eval_gt, __smtx_model_eval_lt,
                native_zlt, SmtValue.Boolean.injEq, decide_eq_true_eq]
              simpa [Int.ofNat_eq_natCast] using
                (Int.natCast_pos.mpr hMatchLengthPos)
            have hStepN :
                __smtx_model_eval N stepBody =
                  SmtValue.Boolean true := by
              simp only [stepBody, smtx_eval_or_term_eq,
                smtx_eval_and_term_eq, hMatchLenGtN, hMatchInN,
                hShortestN, hRecEqN, eval_boolean_term_eq]
              rfl
            have hLtN :
                __smtx_model_eval N (SmtTerm.lt idx numOcc) =
                  SmtValue.Boolean true := by
              rw [eval_lt_term_eq, hIdxN, hNumN]
              simp only [__smtx_model_eval_lt, native_zlt,
                SmtValue.Boolean.injEq, decide_eq_true_eq]
              exact hmK
            have hRangeN :
                __smtx_model_eval N rangeBody =
                  SmtValue.Boolean true := by
              simp only [rangeBody, smtx_eval_or_term_eq,
                smtx_eval_not_term_eq, hLtN, hStepN]
              rfl
            have hGeqN :
                __smtx_model_eval N
                    (SmtTerm.geq idx (SmtTerm.Numeral 0)) =
                  SmtValue.Boolean true := by
              rw [StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                hIdxN, eval_numeral_term_eq]
              simp [__smtx_model_eval_geq, __smtx_model_eval_leq,
                native_zleq, hm0]
            simp only [qBody, smtx_eval_or_term_eq,
              smtx_eval_not_term_eq]
            dsimp only [N] at hGeqN hRangeN ⊢
            rw [hGeqN, hRangeN]
            rfl
          · -- past the count, the second guard discharges the clause
            have hStepPres :
                __smtx_typeof_value (__smtx_model_eval N stepBody) =
                  SmtType.Bool := by
              have h :=
                smt_model_eval_preserves_type_of_non_none N hNTotal
                  stepBody (by
                    unfold term_has_non_none_type
                    rw [hStepBodyTy]
                    decide)
              simpa [hStepBodyTy] using h
            rcases bool_value_canonical hStepPres with
              ⟨stepValue, hStepValue⟩
            have hPast :
                native_zlt m (Int.ofNat (reEnds regex source).length) =
                  false := by
              simp only [native_zlt, decide_eq_false_iff_not]
              exact hmK
            have hLtN :
                __smtx_model_eval N (SmtTerm.lt idx numOcc) =
                  SmtValue.Boolean false := by
              rw [eval_lt_term_eq, hIdxN, hNumN]
              simp [__smtx_model_eval_lt, Int.ofNat_eq_natCast] at hPast ⊢
              exact hPast
            have hRangeN :
                __smtx_model_eval N rangeBody =
                  SmtValue.Boolean true := by
              simp only [rangeBody, smtx_eval_or_term_eq,
                smtx_eval_not_term_eq, hLtN, hStepValue]
              simp [__smtx_model_eval_or, __smtx_model_eval_not,
                native_not, native_or]
            have hGeqN :
                __smtx_model_eval N
                    (SmtTerm.geq idx (SmtTerm.Numeral 0)) =
                  SmtValue.Boolean true := by
              rw [StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                hIdxN, eval_numeral_term_eq]
              simp [__smtx_model_eval_geq, __smtx_model_eval_leq,
                native_zleq, hm0]
            simp only [qBody, smtx_eval_or_term_eq,
              smtx_eval_not_term_eq]
            dsimp only [N] at hGeqN hRangeN ⊢
            rw [hGeqN, hRangeN]
            rfl
        · -- negative index, the first guard discharges the clause
          have hRangePres :
              __smtx_typeof_value (__smtx_model_eval N rangeBody) =
                SmtType.Bool := by
            have h :=
              smt_model_eval_preserves_type_of_non_none N hNTotal
                rangeBody (by
                  unfold term_has_non_none_type
                  rw [hRangeBodyTy]
                  decide)
            simpa [hRangeBodyTy] using h
          rcases bool_value_canonical hRangePres with
            ⟨rangeValue, hRangeValue⟩
          have hNeg : native_zleq 0 m = false := by
            simp only [native_zleq, decide_eq_false_iff_not]
            exact hm0
          have hGeqN :
              __smtx_model_eval N
                  (SmtTerm.geq idx (SmtTerm.Numeral 0)) =
                SmtValue.Boolean false := by
            rw [StrSubstrContainsSupport.smtx_eval_geq_term_eq,
              hIdxN, eval_numeral_term_eq]
            simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hNeg]
          simp only [qBody, smtx_eval_or_term_eq,
            smtx_eval_not_term_eq]
          dsimp only [N] at hGeqN hRangeValue ⊢
          rw [hGeqN, hRangeValue]
          rfl
      rw [smtx_eval_and_term_eq, smtx_eval_and_term_eq,
        smtx_eval_and_term_eq, smtx_eval_and_term_eq,
        smtx_eval_and_term_eq, smtx_eval_and_term_eq,
        hC1, hC2, hC3, hC4, hC5, hC6, eval_boolean_term_eq]
      simp [__smtx_model_eval_and, native_and]

end StrReplaceReAllCase
