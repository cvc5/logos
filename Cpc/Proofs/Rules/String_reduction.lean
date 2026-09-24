module

public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.RegexIndexofSupport
import all Cpc.Proofs.RuleSupport.RegexIndexofSupport
public import Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec
public import Cpc.Proofs.RuleSupport.StrReplaceAllCaseSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllCaseSupport
public import Cpc.Proofs.RuleSupport.StrReplaceReCaseSupport
import all Cpc.Proofs.RuleSupport.StrReplaceReCaseSupport
public import Cpc.Proofs.RuleSupport.StrReplaceReAllCaseSupport
import all Cpc.Proofs.RuleSupport.StrReplaceReAllCaseSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 12000

private theorem sr_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_var_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_purify_term_eq (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_purify x) =
      __smtx_model_eval__at_purify (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_neg_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__ (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_gt_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_lt_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt x y) =
      __smtx_model_eval_lt (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_leq_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_geq_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_str_indexof_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y z) =
      __smtx_model_eval_str_indexof (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_str_update_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_update x y z) =
      __smtx_model_eval_str_update (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_str_indexof_re_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof_re x y z) =
      __smtx_model_eval_str_indexof_re (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sr_eval_str_in_re_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_in_re x y) =
      __smtx_model_eval_str_in_re (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- `seq.nth` at a natural index agrees with list `getD`. -/
private theorem sr_ssm_seq_nth_ofNat (d : SmtValue) :
    ∀ (s : SmtSeq) (j : Nat),
      __smtx_seq_value_nth s (Int.ofNat j) d =
        (native_unpack_seq s).getD j d
  | SmtSeq.empty T, j => by
      simp [__smtx_seq_value_nth, native_unpack_seq]
  | SmtSeq.cons v vs, 0 => by
      simp [__smtx_seq_value_nth, native_unpack_seq]
  | SmtSeq.cons v vs, (j + 1) => by
      have hidx :
          native_zplus (Int.ofNat (j + 1)) (native_zneg 1) =
            Int.ofNat j := by
        show Int.ofNat j + 1 + (-1) = Int.ofNat j
        omega
      have ih := sr_ssm_seq_nth_ofNat d vs j
      simp only [__smtx_seq_value_nth, hidx, ih, native_unpack_seq,
        List.getD_cons_succ]

/-- In bounds, the default supplied to `getD` is irrelevant. -/
private theorem sr_getD_lt_eq (d d' : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : l.getD j d = l.getD j d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h, Option.getD_some, Option.getD_some]

/-- Split a list immediately around an in-bounds element. -/
private theorem sr_take_getD_drop_succ
    (d : SmtValue) (l : List SmtValue) (j : Nat) (h : j < l.length) :
    l.take j ++ [l.getD j d] ++ l.drop (j + 1) = l := by
  induction l generalizing j with
  | nil => simp at h
  | cons a l ih =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simpa [List.take_succ_cons, List.getD_cons_succ,
            List.drop_succ_cons, Nat.succ_eq_add_one, Nat.add_assoc] using
            congrArg (fun xs => a :: xs) (ih j h)

/-- Unpacking a string immediately after packing it recovers its characters. -/
private theorem sr_native_unpack_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp only [native_unpack_string, native_pack_string,
    Smtm.native_unpack_pack_seq, List.map_map]
  induction s with
  | nil => rfl
  | cons c cs ih => simp [impl_native_ssm_char_of_value, ih]

private theorem sr_native_unpack_pack_string_length (s : native_String) :
    (native_unpack_seq (native_pack_string s)).length = s.length := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

@[simp] private theorem sr_native_string_to_values_length
    (s : native_String) :
    (impl_native_string_to_values s).length = s.length := by
  simp [impl_native_string_to_values]

private theorem sr_native_pack_string_injective :
    Function.Injective native_pack_string := by
  intro s t h
  have h' := congrArg native_unpack_string h
  simpa [sr_native_unpack_pack_string] using h'

private theorem sr_native_pack_string_eq_iff
    (s t : native_String) :
    native_pack_string s = native_pack_string t ↔ s = t :=
  sr_native_pack_string_injective.eq_iff

private theorem sr_smt_type_wf_int :
    __smtx_type_wf SmtType.Int = true := by
  native_decide

private theorem sr_not_decide_le_eq_decide_lt (a b : Int) :
    Bool.not (decide (a ≤ b)) = decide (b < a) := by
  by_cases h : a ≤ b
  · have hn : ¬ b < a := Int.not_lt_of_ge h
    simp [h, hn]
  · have hlt : b < a := Int.lt_of_not_ge h
    simp [h, hlt]

private theorem sr_not_decide_lt_eq_decide_le (a b : Int) :
    Bool.not (decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b
  · have hn : ¬ b ≤ a := Int.not_le_of_gt h
    simp [h, hn]
  · have hle : b ≤ a := Int.le_of_not_gt h
    simp [h, hle]

/-- A well-typed character sequence is exactly the packing of its string view. -/
private theorem sr_native_pack_unpack_string
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss := by
    generalize hl : native_unpack_seq ss = l at hTyped ⊢
    clear hl
    induction l with
    | nil => rfl
    | cons v vs ih =>
        rcases hTyped with ⟨hv, hvs⟩
        rcases char_value_canonical hv with ⟨c, rfl, _hc⟩
        simpa [impl_native_ssm_char_of_value] using ih hvs
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  unfold native_pack_string native_unpack_string
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) = ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq ss

/-- String extraction commutes with the sequence encoding used by SMT values. -/
private theorem sr_native_seq_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_pack_seq SmtType.Char
        (native_seq_extract (impl_native_string_to_values s) i n) =
      native_pack_string (native_str_substr s i n) := by
  simp only [native_pack_string, impl_native_string_to_values,
    native_seq_extract, native_str_substr, native_str_len]
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

/-- The generated evaluator retains the packed sequence's inferred element
    type at extraction sites; for strings, that type is `Char`. -/
private theorem sr_native_seq_extract_pack_string_eval
    (s : native_String) (i n : native_Int) :
    native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
        (native_seq_extract (impl_native_string_to_values s) i n) =
      native_pack_string (native_str_substr s i n) := by
  have hElem :
      __smtx_elem_typeof_seq_value (native_pack_string s) =
        SmtType.Char := by
    simp [native_pack_string, elem_typeof_pack_seq]
  rw [hElem]
  exact sr_native_seq_extract_pack_string s i n

/-- The generated `Int.ofNat` constructor and Lean's ordinary natural-number
    cast denote the same integer. -/
private theorem sr_int_natCast_eq_ofNat (j : Nat) :
    (j : Int) = Int.ofNat j := by
  cases j <;> rfl

/-- Unpacking the evaluator's packed extraction gives the corresponding
    native-string substring. -/
private theorem sr_native_unpack_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
          (native_seq_extract (impl_native_string_to_values s) i n)) =
      native_str_substr s i n := by
  have hElem :
      __smtx_elem_typeof_seq_value (native_pack_string s) =
        SmtType.Char := by
    simp [native_pack_string, elem_typeof_pack_seq]
  rw [hElem]
  have h := congrArg native_unpack_string
    (sr_native_seq_extract_pack_string s i n)
  simpa [sr_native_unpack_pack_string] using h

@[simp] private theorem sr_native_unpack_extract_pack_string_char
    (s : native_String) (i n : native_Int) :
    native_unpack_string
        (native_pack_seq SmtType.Char
          (native_seq_extract (impl_native_string_to_values s) i n)) =
      native_str_substr s i n := by
  have h := congrArg native_unpack_string
    (sr_native_seq_extract_pack_string s i n)
  simpa [sr_native_unpack_pack_string] using h

@[simp] private theorem sr_native_unpack_seq_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_unpack_seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
          (native_seq_extract (impl_native_string_to_values s) i n)) =
      impl_native_string_to_values (native_str_substr s i n) := by
  have h := congrArg native_unpack_seq
    (sr_native_seq_extract_pack_string_eval s i n)
  have hsimpa := h
  try simp [native_pack_string, Smtm.native_unpack_pack_seq] at hsimpa ⊢
  exact hsimpa

/-- For an in-bounds natural index, extracting one sequence element is the
    corresponding one-element `drop`/`take` slice. -/
private theorem sr_native_seq_extract_one_nat
    (xs : List SmtValue) (j : Nat) (hj : j < xs.length) :
    native_seq_extract xs (Int.ofNat j) 1 = (xs.drop j).take 1 := by
  have e1 : decide ((Int.ofNat j : native_Int) < 0) = false :=
    decide_eq_false (show ¬ ((j : Int) < 0) by omega)
  have e2 : decide ((1 : native_Int) ≤ 0) = false := by decide
  have e3 :
      decide ((Int.ofNat j : native_Int) ≥ Int.ofNat xs.length) = false :=
    decide_eq_false (show ¬ ((j : Int) ≥ (xs.length : Int)) by omega)
  have h1 : (1 : Int) ≤ (xs.length : Int) - (j : Int) := by omega
  have hmin :
      min (1 : native_Int) (Int.ofNat xs.length - Int.ofNat j) = 1 :=
    Int.min_eq_left h1
  simp only [native_seq_extract]
  rw [e1, e2, e3, hmin]
  simp

/-- Outside the usual positive, in-bounds substring guard, extraction is
    empty. -/
private theorem sr_native_seq_extract_empty_of_inactive
    (xs : List SmtValue) (i n : native_Int)
    (h : ¬ (0 ≤ i ∧ i < Int.ofNat xs.length ∧ 0 < n)) :
    native_seq_extract xs i n = [] := by
  by_cases hi : i < 0
  · simp [native_seq_extract, hi]
  by_cases hn : n ≤ 0
  · exact native_seq_extract_empty_of_len_nonpos xs i n hn
  have hi0 : 0 ≤ i := Int.le_of_not_gt hi
  have hn0 : 0 < n := Int.lt_of_not_ge hn
  have hlen : Int.ofNat xs.length ≤ i := by
    apply Int.le_of_not_gt
    intro hiLen
    exact h ⟨hi0, hiLen, hn0⟩
  unfold native_seq_extract
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hlen)]

/-- The prefix, selected slice, and residual suffix generated by the
    substring reduction reconstruct the source, with the advertised length
    bounds. -/
private theorem sr_native_seq_extract_active_facts
    (xs : List SmtValue) (i n : native_Int)
    (hi : 0 ≤ i) (hiLen : i < Int.ofNat xs.length) (hn : 0 < n) :
    native_seq_extract xs 0 i ++
          native_seq_extract xs i n ++
          native_seq_extract xs (i + n)
            (Int.ofNat xs.length - (i + n)) = xs ∧
      Int.ofNat (native_seq_extract xs 0 i).length = i ∧
      (Int.ofNat
            (native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n))).length =
          Int.ofNat xs.length - (i + n) ∨
        Int.ofNat
            (native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n))).length = 0) ∧
      Int.ofNat (native_seq_extract xs i n).length ≤ n := by
  let I := Int.toNat i
  let N := Int.toNat n
  have hICast : (I : native_Int) = i := Int.toNat_of_nonneg hi
  have hNCast : (N : native_Int) = n :=
    Int.toNat_of_nonneg (Int.le_of_lt hn)
  have hILt : I < xs.length := by
    apply Int.ofNat_lt.mp
    simpa [hICast] using hiLen
  have hILe : I ≤ xs.length := Nat.le_of_lt hILt
  have hPre : native_seq_extract xs 0 i = xs.take I := by
    rw [← hICast]
    exact native_seq_extract_zero_nat xs I hILe
  have hMid : native_seq_extract xs i n = (xs.drop I).take N := by
    rw [native_seq_extract_eq_drop_take xs i n hi hn]
  have hPreLen : Int.ofNat (native_seq_extract xs 0 i).length = i := by
    simpa [hPre, List.length_take, Nat.min_eq_left hILe] using hICast
  have hMidLen : Int.ofNat (native_seq_extract xs i n).length ≤ n := by
    calc
      Int.ofNat (native_seq_extract xs i n).length =
          Int.ofNat ((xs.drop I).take N).length := by rw [hMid]
      _ ≤ Int.ofNat N := Int.ofNat_le.mpr (by
        rw [List.length_take]
        exact Nat.min_le_left _ _)
      _ = n := hNCast
  have hINCast : ((I + N : Nat) : native_Int) = i + n := by
    calc
      ((I + N : Nat) : native_Int) =
          (I : native_Int) + (N : native_Int) :=
        (Int.ofNat_add_ofNat I N).symm
      _ = i + n := by rw [hICast, hNCast]
  by_cases hEnd : i + n ≤ Int.ofNat xs.length
  · have hINLe : I + N ≤ xs.length := by
      apply Int.ofNat_le.mp
      rw [← Int.ofNat_add_ofNat, hICast, hNCast]
      exact hEnd
    have hRemaining :
        Int.ofNat xs.length - (i + n) =
          Int.ofNat (xs.length - (I + N)) := by
      rw [← hINCast]
      exact (Int.ofNat_sub hINLe).symm
    have hSuffix :
        native_seq_extract xs (i + n)
            (Int.ofNat xs.length - (i + n)) =
          xs.drop (I + N) := by
      rw [hRemaining, ← hINCast]
      exact native_seq_extract_to_end_nat xs (I + N) hINLe
    have hDecomp :
        native_seq_extract xs 0 i ++ native_seq_extract xs i n ++
            native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n)) = xs := by
      rw [hPre, hMid, hSuffix]
      calc
        xs.take I ++ (xs.drop I).take N ++ xs.drop (I + N) =
            xs.take I ++
              ((xs.drop I).take N ++ (xs.drop I).drop N) := by
                simp only [List.drop_drop, List.append_assoc]
        _ = xs.take I ++ xs.drop I := by
              rw [List.take_append_drop]
        _ = xs := List.take_append_drop I xs
    have hSuffixLen :
        Int.ofNat
              (native_seq_extract xs (i + n)
                (Int.ofNat xs.length - (i + n))).length =
            Int.ofNat xs.length - (i + n) := by
      rw [hSuffix, List.length_drop, hRemaining]
    exact ⟨hDecomp, hPreLen, Or.inl hSuffixLen, hMidLen⟩
  · have hRemainingNonpos :
        Int.ofNat xs.length - (i + n) ≤ 0 := by
      have hOver : Int.ofNat xs.length < i + n := Int.lt_of_not_ge hEnd
      omega
    have hSuffix :
        native_seq_extract xs (i + n)
            (Int.ofNat xs.length - (i + n)) = [] :=
      native_seq_extract_empty_of_len_nonpos _ _ _ hRemainingNonpos
    have hTailLe : (xs.drop I).length ≤ N := by
      rw [List.length_drop]
      have hNotNat : ¬ I + N ≤ xs.length := by
        intro hLe
        apply hEnd
        rw [← hINCast]
        exact Int.ofNat_le.mpr hLe
      have hNatOver : xs.length < I + N := Nat.lt_of_not_ge hNotNat
      omega
    have hMidTail : (xs.drop I).take N = xs.drop I :=
      List.take_of_length_le hTailLe
    have hDecomp :
        native_seq_extract xs 0 i ++ native_seq_extract xs i n ++
            native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n)) = xs := by
      rw [hPre, hMid, hSuffix, hMidTail]
      simp [List.take_append_drop]
    have hSuffixLen :
        Int.ofNat
              (native_seq_extract xs (i + n)
                (Int.ofNat xs.length - (i + n))).length = 0 := by
      have h := congrArg (fun ys : List SmtValue => Int.ofNat ys.length)
        hSuffix
      simpa using h
    exact ⟨hDecomp, hPreLen, Or.inr hSuffixLen, hMidLen⟩

/-- Extending the prefix before the first occurrence by every element of the
    occurrence except its last one still does not contain the whole pattern. -/
private theorem sr_native_seq_first_prefix_no_contains
    (xs pat : List SmtValue) (hPat : pat ≠ [])
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_contains
        (native_seq_extract xs 0 (native_seq_indexof xs pat 0) ++
          native_seq_extract pat 0 (Int.ofNat pat.length - 1))
        pat = false := by
  let idx := native_seq_indexof xs pat 0
  let J := Int.toNat idx
  let K := pat.length - 1
  have hPatPos : 0 < pat.length := by
    cases pat with
    | nil => contradiction
    | cons => simp
  have hOneLe : 1 ≤ pat.length := hPatPos
  have hIdxCast : (J : native_Int) = idx :=
    Int.toNat_of_nonneg hIdxNonneg
  have hBounds : J + pat.length ≤ xs.length := by
    simpa [idx, J] using
      StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
        xs pat hIdxNonneg
  have hJLe : J ≤ xs.length := by omega
  have hPre : native_seq_extract xs 0 idx = xs.take J := by
    rw [← hIdxCast]
    exact native_seq_extract_zero_nat xs J hJLe
  have hKCast :
      Int.ofNat pat.length - 1 = Int.ofNat K := by
    simpa [K] using (Int.ofNat_sub hOneLe).symm
  have hPatPre :
      native_seq_extract pat 0 (Int.ofNat pat.length - 1) =
        pat.take K := by
    rw [hKCast]
    exact native_seq_extract_zero_nat pat K (Nat.sub_le _ _)
  have hDecomp :
      xs.take J ++ pat ++ xs.drop (J + pat.length) = xs := by
    simpa [idx, J] using
      StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
        xs pat hIdxNonneg
  let short := xs.take J ++ pat.take K
  let suffix := pat.drop K ++ xs.drop (J + pat.length)
  have hAppend : short ++ suffix = xs := by
    calc
      short ++ suffix =
          xs.take J ++ ((pat.take K ++ pat.drop K) ++
            xs.drop (J + pat.length)) := by
        simp only [short, suffix, List.append_assoc]
      _ = xs.take J ++ (pat ++ xs.drop (J + pat.length)) := by
        rw [List.take_append_drop]
      _ = xs := by simpa [List.append_assoc] using hDecomp
  by_cases hContains : native_seq_contains short pat = true
  · exfalso
    have hShortIdxNonneg :
        0 ≤ native_seq_indexof short pat 0 := by
      simpa [native_seq_contains] using hContains
    have hStable := native_seq_indexof_append_of_nonneg
      short pat suffix 0 hShortIdxNonneg
    rw [hAppend] at hStable
    have hShortBounds :=
      StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
        short pat hShortIdxNonneg
    rw [← hStable] at hShortBounds
    have hTakeJLen : (xs.take J).length = J := by
      simp [List.length_take, Nat.min_eq_left hJLe]
    have hKLe : K ≤ pat.length := by
      dsimp [K]
      omega
    have hTakeKLen : (pat.take K).length = K := by
      rw [List.length_take, Nat.min_eq_left hKLe]
    have hIdxToNat : Int.toNat (native_seq_indexof xs pat 0) = J := rfl
    dsimp [short] at hShortBounds
    simp only [List.length_append, hTakeJLen, hTakeKLen, hIdxToNat] at hShortBounds
    dsimp [K] at hShortBounds
    omega
  · have hFalse : native_seq_contains short pat = false := by
      cases h : native_seq_contains short pat
      · rfl
      · exact False.elim (hContains (by simpa using h))
    change native_seq_contains
        (native_seq_extract xs 0 idx ++
          native_seq_extract pat 0 (Int.ofNat pat.length - 1))
        pat = false
    rw [hPre, hPatPre]
    exact hFalse

/-- A successful first replacement can be expressed with the same extracts
    used by the generated string-reduction predicate. -/
private theorem sr_native_seq_replace_eq_extracts_of_indexof_nonneg
    (xs pat repl : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_replace xs pat repl =
      native_seq_extract xs 0 (native_seq_indexof xs pat 0) ++ repl ++
        native_seq_extract xs
          (native_seq_indexof xs pat 0 + Int.ofNat pat.length)
          (Int.ofNat xs.length -
            (native_seq_indexof xs pat 0 + Int.ofNat pat.length)) := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hBounds : j + pat.length ≤ xs.length := by
    simpa [idx, j] using
      StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
        xs pat hIdxNonneg
  have hJLe : j ≤ xs.length := by omega
  have hPre : native_seq_extract xs 0 idx = xs.take j := by
    rw [← hCast]
    exact native_seq_extract_zero_nat xs j hJLe
  have hStart : idx + Int.ofNat pat.length = Int.ofNat (j + pat.length) := by
    rw [← hCast]
    simp
  have hSuf :
      native_seq_extract xs (idx + Int.ofNat pat.length)
          (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
        xs.drop (j + pat.length) := by
    rw [hStart]
    have h := native_seq_extract_to_end_nat xs (j + pat.length) hBounds
    simpa [Int.ofNat_eq_natCast, Int.ofNat_sub hBounds] using h
  rw [StrEqReplSupport.native_seq_replace_of_indexof_nonneg
    xs pat repl hIdxNonneg]
  rw [hPre, hSuf]

private theorem sr_native_seq_replace_nil
    (xs repl : List SmtValue) :
    native_seq_replace xs [] repl = repl ++ xs := by
  simp [StrEqReplSupport.native_seq_replace_eq_indexof,
    StrEqReplSupport.native_seq_indexof_nil_zero]

/-- Search in a dropped suffix, with a successful result shifted back by the
    suffix offset, agrees with search in the original sequence at that offset. -/
private def sr_native_seq_indexof_offset
    (xs pat : List SmtValue) (off : Nat) : native_Int :=
  let r := native_seq_indexof xs pat 0
  if r = (-1 : native_Int) then -1 else r + Int.ofNat off

private theorem sr_native_seq_indexof_zero_eq_rec
    (xs pat : List SmtValue) :
    native_seq_indexof xs pat 0 =
      if h : pat.length ≤ xs.length then
        native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1)
      else
        -1 := by
  simpa using native_seq_indexof_eq_rec xs pat 0

private theorem sr_native_seq_indexof_offset_drop_eq
    (xs pat : List SmtValue) (off : Nat) (hOff : off ≤ xs.length) :
    sr_native_seq_indexof_offset (xs.drop off) pat off =
      native_seq_indexof xs pat (Int.ofNat off) := by
  unfold sr_native_seq_indexof_offset
  rw [sr_native_seq_indexof_zero_eq_rec (xs.drop off) pat]
  rw [native_seq_indexof_eq_rec]
  have hOffNotNeg : ¬ (Int.ofNat off : Int) < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg off)
  rw [if_neg hOffNotNeg]
  change
    (let r :=
      if h : pat.length ≤ (xs.drop off).length then
        native_seq_indexof_rec (xs.drop off) pat 0
          ((xs.drop off).length - pat.length + 1)
      else
        (-1 : native_Int)
     if r = (-1 : native_Int) then -1 else r + Int.ofNat off) =
      if h : off + pat.length ≤ xs.length then
        native_seq_indexof_rec (xs.drop off) pat off
          (xs.length - (off + pat.length) + 1)
      else
        -1
  by_cases hTailFit : pat.length ≤ (xs.drop off).length
  · have hFullFit : off + pat.length ≤ xs.length := by
      rw [List.length_drop] at hTailFit
      omega
    rw [dif_pos hTailFit, dif_pos hFullFit]
    have hFuel :
        (xs.drop off).length - pat.length + 1 =
          xs.length - (off + pat.length) + 1 := by
      rw [List.length_drop]
      omega
    rw [hFuel]
    rw [← RuleProofs.native_seq_indexof_rec_offset
      (xs.drop off) pat 0 off]
    simp
  · have hFullNot : ¬ off + pat.length ≤ xs.length := by
      intro hFull
      apply hTailFit
      rw [List.length_drop]
      omega
    rw [dif_neg hTailFit, dif_neg hFullNot]
    simp

private theorem sr_native_seq_extract_to_end_of_bounds
    (xs : List SmtValue) (i : native_Int)
    (hi : 0 ≤ i) (hiLen : i ≤ Int.ofNat xs.length) :
    native_seq_extract xs i (Int.ofNat xs.length - i) =
      xs.drop (Int.toNat i) := by
  let j := Int.toNat i
  have hCast : Int.ofNat j = i := Int.toNat_of_nonneg hi
  have hJLe : j ≤ xs.length := by
    apply Int.ofNat_le.mp
    calc
      Int.ofNat j = i := hCast
      _ ≤ Int.ofNat xs.length := hiLen
  rw [← hCast]
  have h := native_seq_extract_to_end_nat xs j hJLe
  simpa [Int.ofNat_eq_natCast, Int.ofNat_sub hJLe] using h

/-- Reversing a sequence maps an in-bounds one-element slice to its mirrored
    one-element slice. -/
private theorem sr_native_seq_extract_reverse_one
    (xs : List SmtValue) (j : Nat) (hj : j < xs.length) :
    native_seq_extract xs.reverse (Int.ofNat j) 1 =
      native_seq_extract xs (Int.ofNat (xs.length - (j + 1))) 1 := by
  rw [sr_native_seq_extract_one_nat xs.reverse j (by simpa using hj),
    sr_native_seq_extract_one_nat xs (xs.length - (j + 1)) (by omega)]
  simp only [List.take_one, List.head?_drop]
  have hMirror : xs.length - (j + 1) = xs.length - 1 - j := by omega
  rw [hMirror]
  exact congrArg Option.toList (List.getElem?_reverse hj)

/-- Sequence containment is equivalent to the existence of an in-bounds
    extraction equal to the pattern. -/
private theorem sr_native_seq_contains_iff_extract
    (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔
      ∃ j : Nat,
        j ≤ xs.length - pat.length ∧
          native_seq_extract xs (Int.ofNat j) (Int.ofNat pat.length) = pat := by
  constructor
  · intro hContains
    rcases
        (StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat).1
          hContains with
      ⟨before, after, hXs⟩
    let j := before.length
    have hBound : j ≤ xs.length - pat.length := by
      have hLen := congrArg List.length hXs
      simp [j] at hLen ⊢
      omega
    refine ⟨j, hBound, ?_⟩
    by_cases hPatNil : pat = []
    · subst pat
      simp [native_seq_extract_empty_of_len_nonpos]
    · have hPatLen : 0 < pat.length := by
        cases pat with
        | nil => contradiction
        | cons => simp
      have hPatPos : (0 : Int) < Int.ofNat pat.length := by
        apply Int.ofNat_lt.mpr
        exact hPatLen
      rw [native_seq_extract_eq_drop_take xs (Int.ofNat j)
        (Int.ofNat pat.length) (Int.natCast_nonneg j) hPatPos]
      simp [hXs, j]
  · rintro ⟨j, hBound, hExtract⟩
    apply
      (StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat).2
    by_cases hPatNil : pat = []
    · subst pat
      exact ⟨[], xs, by simp⟩
    · have hPatLen : 0 < pat.length := by
        cases pat with
        | nil => contradiction
        | cons => simp
      have hPatPos : (0 : Int) < Int.ofNat pat.length := by
        apply Int.ofNat_lt.mpr
        exact hPatLen
      have hDropTake : (xs.drop j).take pat.length = pat := by
        rw [native_seq_extract_eq_drop_take xs (Int.ofNat j)
          (Int.ofNat pat.length) (Int.natCast_nonneg j) hPatPos] at hExtract
        simpa using hExtract
      refine ⟨xs.take j, xs.drop (j + pat.length), ?_⟩
      calc
        xs = xs.take j ++ xs.drop j := (List.take_append_drop j xs).symm
        _ = xs.take j ++
              ((xs.drop j).take pat.length ++
                (xs.drop j).drop pat.length) := by
            exact congrArg (fun zs => xs.take j ++ zs)
              (List.take_append_drop pat.length (xs.drop j)).symm
        _ = xs.take j ++ pat ++ xs.drop (j + pat.length) := by
            simp only [hDropTake, List.drop_drop, List.append_assoc]

/-- An in-bounds, length-one substring is the indexed singleton. -/
private theorem sr_native_str_substr_one_nat (s : native_String) (j : Nat)
    (hj : j < s.length) :
    native_str_substr s (Int.ofNat j) 1 = [s[j]] := by
  have e1 : decide ((Int.ofNat j : native_Int) < 0) = false :=
    decide_eq_false (show ¬ ((j : Int) < 0) by omega)
  have e2 : decide ((1 : native_Int) ≤ 0) = false := by decide
  have h1 : (1 : Int) ≤ (s.length : Int) - (j : Int) := by omega
  have hmin : min (1 : native_Int) (Int.ofNat s.length - Int.ofNat j) = 1 :=
    Int.min_eq_left h1
  have htn : (Int.ofNat j : native_Int).toNat = j := rfl
  have htake :
      (min (1 : native_Int) (Int.ofNat s.length - Int.ofNat j)).toNat = 1 := by
    rw [hmin]
    exact Int.toNat_one
  simp only [native_str_substr, native_str_len]
  rw [e1, e2]
  simp only [Bool.false_or, decide_eq_true_eq]
  -- the guard is the `Bool` form `decide _ = true`, and `rw` would additionally
  -- have to match the goal's `Decidable` instance syntactically; `refine`
  -- unifies it up to defeq instead
  refine Eq.trans (if_neg (fun h => absurd (of_decide_eq_true h)
    (show ¬ Int.ofNat j ≥ Int.ofNat s.length by omega))) ?_
  rw [htake, htn]
  have hDrop := congrArg (List.take 1) (List.drop_eq_getElem_cons hj)
  exact hDrop

/-- The code constraint generated for lowercasing matches the native operation. -/
private theorem sr_lower_code_at (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length) :
    native_str_to_code
        (native_str_substr (native_str_to_lower s) (Int.ofNat j) 1) =
      if 65 ≤ native_str_to_code (native_str_substr s (Int.ofNat j) 1) &&
          native_str_to_code (native_str_substr s (Int.ofNat j) 1) ≤ 90 then
        native_str_to_code (native_str_substr s (Int.ofNat j) 1) + 32
      else native_str_to_code (native_str_substr s (Int.ofNat j) 1) := by
  have hc : native_char_valid s[j] = true := by
    rw [native_string_valid, List.all_eq_true] at hValid
    exact hValid s[j] (List.getElem_mem hj)
  have hjMap : j < (native_str_to_lower s).length := by
    simpa [native_str_to_lower] using hj
  rw [sr_native_str_substr_one_nat s j hj]
  rw [sr_native_str_substr_one_nat (native_str_to_lower s) j hjMap]
  simp only [native_str_to_lower, List.getElem_map]
  have hcLower := native_char_valid_to_lower hc
  have hCode : native_str_to_code [s[j]] = Int.ofNat s[j] := by
    simp [native_str_to_code, hc]
  have hLowerCode :
      native_str_to_code [impl_native_char_to_lower s[j]] =
        Int.ofNat (impl_native_char_to_lower s[j]) := by
    simp [native_str_to_code, hcLower]
  rw [hCode, hLowerCode]
  by_cases hRange : 65 ≤ s[j] ∧ s[j] ≤ 90
  · have hRangeInt : (65 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 90 := by
      exact ⟨Int.ofNat_le.mpr hRange.1, Int.ofNat_le.mpr hRange.2⟩
    have hRangeBool :
        (decide ((65 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 90)) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hRangeInt
    rw [if_pos hRangeBool]
    simp [impl_native_char_to_lower, hRange]
  · have hRangeInt : ¬ ((65 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 90) := by
      intro h
      exact hRange ⟨Int.ofNat_le.mp h.1, Int.ofNat_le.mp h.2⟩
    have hRangeBool :
        (decide ((65 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 90)) ≠ true := by
      simpa [Bool.and_eq_true] using hRangeInt
    rw [if_neg hRangeBool]
    simp [impl_native_char_to_lower, hRange]

/-- The code constraint generated for uppercasing matches the native operation. -/
private theorem sr_upper_code_at (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length) :
    native_str_to_code
        (native_str_substr (native_str_to_upper s) (Int.ofNat j) 1) =
      if 97 ≤ native_str_to_code (native_str_substr s (Int.ofNat j) 1) &&
          native_str_to_code (native_str_substr s (Int.ofNat j) 1) ≤ 122 then
        native_str_to_code (native_str_substr s (Int.ofNat j) 1) + (-32)
      else native_str_to_code (native_str_substr s (Int.ofNat j) 1) := by
  have hc : native_char_valid s[j] = true := by
    rw [native_string_valid, List.all_eq_true] at hValid
    exact hValid s[j] (List.getElem_mem hj)
  have hjMap : j < (native_str_to_upper s).length := by
    simpa [native_str_to_upper] using hj
  rw [sr_native_str_substr_one_nat s j hj]
  rw [sr_native_str_substr_one_nat (native_str_to_upper s) j hjMap]
  simp only [native_str_to_upper, List.getElem_map]
  have hcUpper := native_char_valid_to_upper hc
  have hCode : native_str_to_code [s[j]] = Int.ofNat s[j] := by
    simp [native_str_to_code, hc]
  have hUpperCode :
      native_str_to_code [impl_native_char_to_upper s[j]] =
        Int.ofNat (impl_native_char_to_upper s[j]) := by
    simp [native_str_to_code, hcUpper]
  rw [hCode, hUpperCode]
  by_cases hRange : 97 ≤ s[j] ∧ s[j] ≤ 122
  · have hRangeInt : (97 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 122 := by
      exact ⟨Int.ofNat_le.mpr hRange.1, Int.ofNat_le.mpr hRange.2⟩
    have hRangeBool :
        (decide ((97 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 122)) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hRangeInt
    rw [if_pos hRangeBool]
    simp [impl_native_char_to_upper, hRange]
    have h32 : 32 ≤ s[j] :=
      Nat.le_trans (by decide) hRange.1
    rw [Int.ofNat_sub h32]
    rw [Int.sub_eq_add_neg]
    have h32cast : Int.ofNat 32 = (32 : Int) := by decide
    exact congrArg (fun z : Int => Int.ofNat s[j] + -z) h32cast
  · have hRangeInt : ¬ ((97 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 122) := by
      intro h
      exact hRange ⟨Int.ofNat_le.mp h.1, Int.ofNat_le.mp h.2⟩
    have hRangeBool :
        (decide ((97 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 122)) ≠ true := by
      simpa [Bool.and_eq_true] using hRangeInt
    rw [if_neg hRangeBool]
    simp [impl_native_char_to_upper, hRange]

private def sr_native_str_leq_bool (s t : native_String) : Bool :=
  native_or (decide (s = t)) (native_str_lt s t)

private theorem sr_native_str_substr_at_length (s : native_String) :
    native_str_substr s (Int.ofNat s.length) 1 = [] := by
  simp [native_str_substr, native_str_len]

private theorem sr_native_str_substr_zero_nat
    (s : native_String) (j : Nat) (hj : j ≤ s.length) :
    native_str_substr s 0 (Int.ofNat j) = s.take j := by
  by_cases hj0 : j = 0
  · subst j
    simp [native_str_substr, native_str_len]
  by_cases hs0 : s = []
  · subst s
    have : j = 0 := by simpa using hj
    exact False.elim (hj0 this)
  have hmin :
      min (Int.ofNat j) (Int.ofNat s.length) = Int.ofNat j :=
    Int.min_eq_left (Int.ofNat_le.mpr hj)
  simp [native_str_substr, native_str_len, hj0, hs0]
  omega

private theorem sr_digitChar_toNat_sub (n : Nat) (h : n < 10) :
    Char.toNat (Nat.digitChar n) - 48 = n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => native_decide
  | n + 10 => omega

private theorem sr_decimal_append (xs : native_String) (c : native_Char) :
    impl_native_decimal_digits_to_nat (xs ++ [c]) =
      10 * impl_native_decimal_digits_to_nat xs + (c - 48) := by
  simp [impl_native_decimal_digits_to_nat, List.foldl_append]

private theorem sr_all_digits_take (xs : native_String) (j : Nat)
    (h : xs.all impl_native_char_is_digit = true) :
    (xs.take j).all impl_native_char_is_digit = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_take hc)

private theorem sr_all_digits_drop (xs : native_String) (j : Nat)
    (h : xs.all impl_native_char_is_digit = true) :
    (xs.drop j).all impl_native_char_is_digit = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_drop hc)

private theorem sr_fold_digits_ge (acc : Nat) : ∀ xs : native_String,
    xs.all impl_native_char_is_digit = true →
    acc ≤ xs.foldl (fun a c => 10 * a + (c - 48)) acc
  | [], _ => by simp
  | c :: cs, h => by
      have hp : impl_native_char_is_digit c = true ∧
          cs.all impl_native_char_is_digit = true := by
        simpa [Bool.and_eq_true] using h
      have hbounds : 48 ≤ c ∧ c ≤ 57 := by
        unfold impl_native_char_is_digit at hp
        simpa [Bool.and_eq_true] using hp.1
      simp only [List.foldl]
      exact Nat.le_trans (by omega)
        (sr_fold_digits_ge (10 * acc + (c - 48)) cs hp.2)

private theorem sr_decimal_take_le (xs : native_String) (j : Nat)
    (h : xs.all impl_native_char_is_digit = true) :
    impl_native_decimal_digits_to_nat (xs.take j) ≤
      impl_native_decimal_digits_to_nat xs := by
  let acc := impl_native_decimal_digits_to_nat (xs.take j)
  calc
    impl_native_decimal_digits_to_nat (xs.take j) = acc := rfl
    _ ≤ (xs.drop j).foldl (fun a c => 10 * a + (c - 48)) acc :=
      sr_fold_digits_ge acc (xs.drop j) (sr_all_digits_drop xs j h)
    _ = impl_native_decimal_digits_to_nat (xs.take j ++ xs.drop j) := by
      rw [show acc = (xs.take j).foldl
        (fun a c => 10 * a + (c - 48)) 0 by rfl]
      rw [← List.foldl_append]
      rfl
    _ = impl_native_decimal_digits_to_nat xs := by rw [List.take_append_drop]

private theorem sr_decimal_take_succ (xs : native_String) (j : Nat)
    (hj : j < xs.length) :
    impl_native_decimal_digits_to_nat (xs.take (j + 1)) =
      10 * impl_native_decimal_digits_to_nat (xs.take j) + (xs[j] - 48) := by
  rw [List.take_succ_eq_append_getElem hj, sr_decimal_append]

private theorem sr_decimal_toDigits (n : Nat) :
    impl_native_decimal_digits_to_nat ((Nat.toDigits 10 n).map Char.toNat) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [Nat.toDigits_eq_if (by omega)]
      split
      · rename_i hn
        simp only [List.map_cons, List.map_nil, impl_native_decimal_digits_to_nat,
          List.foldl]
        simpa using sr_digitChar_toNat_sub n hn
      · rename_i hn
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [sr_decimal_append,
          ih (n / 10) (Nat.div_lt_self (by omega) (by omega))]
        rw [sr_digitChar_toNat_sub (n % 10) (Nat.mod_lt n (by omega))]
        exact Nat.div_add_mod n 10

private theorem sr_digitChar_toNat_bounds (n : Nat)
    (hpos : 0 < n) (hlt : n < 10) :
    49 ≤ Char.toNat (Nat.digitChar n) ∧
      Char.toNat (Nat.digitChar n) ≤ 57 := by
  match n with
  | 0 => omega
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => native_decide
  | n + 10 => omega

private theorem sr_toDigits_head_nonzero (n : Nat) (hn : 0 < n) :
    ∃ c cs,
      (Nat.toDigits 10 n).map Char.toNat = c :: cs ∧
        49 ≤ c ∧ c ≤ 57 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [Nat.toDigits_eq_if (by omega)]
      split
      · rename_i hlt
        refine ⟨Char.toNat (Nat.digitChar n), [], rfl, ?_⟩
        exact sr_digitChar_toNat_bounds n hn hlt
      · rename_i hlt
        have hqPos : 0 < n / 10 := Nat.div_pos (by omega) (by omega)
        have hqLt : n / 10 < n := Nat.div_lt_self hn (by omega)
        rcases ih (n / 10) hqLt hqPos with ⟨c, cs, hrepr, hc⟩
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [hrepr]
        exact ⟨c, cs ++ [Char.toNat (Nat.digitChar (n % 10))], rfl, hc⟩

private theorem sr_decimal_string_toNat (n : Nat) :
    impl_native_decimal_digits_to_nat (native_string_lit (toString n)) = n := by
  unfold native_string_lit
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  exact sr_decimal_toDigits n

private theorem sr_native_string_lit_nat_toString_ne_nil (n : Nat) :
    native_string_lit (toString n) ≠ [] := by
  intro h
  have hlen : 0 < (Nat.toDigits 10 n).length := Nat.length_toDigits_pos
  unfold native_string_lit at h
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at h
  have hlen0 : ((Nat.toDigits 10 n).map Char.toNat).length = 0 := by
    simp [h]
  simp only [List.length_map] at hlen0
  omega

private theorem sr_native_str_to_int_of_ne_nil_all (s : native_String)
    (hs : s ≠ []) (hAll : s.all impl_native_char_is_digit = true) :
    native_str_to_int s = Int.ofNat (impl_native_decimal_digits_to_nat s) := by
  cases s with
  | nil => contradiction
  | cons c cs => simp [native_str_to_int, hAll]

private theorem sr_native_str_to_int_from_int (i : native_Int)
    (hi : 0 ≤ i) :
    native_str_to_int (native_str_from_int i) = i := by
  cases i with
  | negSucc n => simp at hi
  | ofNat n =>
      have hNonneg : ¬ (Int.ofNat n < 0) := Int.not_lt_of_ge hi
      have hAll : (native_string_lit (toString n)).all
          impl_native_char_is_digit = true := by
        have hsimpa :=
          (StrInReFromIntDigRangeProof.native_str_from_int_all_digits
            (Int.ofNat n))
        try simp [native_str_from_int, hNonneg] at hsimpa ⊢
        exact hsimpa
      rw [native_str_from_int, if_neg hNonneg]
      change native_str_to_int (native_string_lit (toString n)) = Int.ofNat n
      rw [sr_native_str_to_int_of_ne_nil_all _
        (sr_native_string_lit_nat_toString_ne_nil n) hAll]
      exact congrArg Int.ofNat (sr_decimal_string_toNat n)

private theorem sr_native_str_from_int_ne_nil (i : native_Int)
    (hi : 0 ≤ i) :
    native_str_from_int i ≠ [] := by
  cases i with
  | negSucc n => simp at hi
  | ofNat n =>
      have hNonneg : ¬ (Int.ofNat n < 0) := Int.not_lt_of_ge hi
      have hsimpa :=
        sr_native_string_lit_nat_toString_ne_nil n
      try simp [native_str_from_int, hNonneg] at hsimpa ⊢
      exact hsimpa

private theorem sr_native_str_from_int_head_pos (i : native_Int)
    (hi : 0 ≤ i) (hLen : 1 < (native_str_from_int i).length) :
    (1 : native_Int) ≤ Int.ofNat (native_str_from_int i)[0] - 48 := by
  cases i with
  | negSucc n => simp at hi
  | ofNat n =>
      have hNonneg : ¬ (Int.ofNat n < 0) := Int.not_lt_of_ge hi
      have hnPos : 0 < n := by
        by_cases hn : n = 0
        · subst n
          have hOne : (native_str_from_int (Int.ofNat 0)).length = 1 := by
            native_decide
          rw [hOne] at hLen
          omega
        · exact Nat.pos_of_ne_zero hn
      rcases sr_toDigits_head_nonzero n hnPos with ⟨c, cs, hrepr, hc⟩
      have hString : native_str_from_int (Int.ofNat n) = c :: cs := by
        simp only [native_str_from_int, if_neg hNonneg]
        change native_string_lit (toString n) = c :: cs
        unfold native_string_lit
        rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList, hrepr]
      have hcLower : (49 : Int) ≤ Int.ofNat c := Int.ofNat_le.mpr hc.1
      have hBound : (1 : Int) ≤ Int.ofNat c - 48 := by omega
      simpa only [hString, List.getElem_cons_zero] using hBound

private def sr_native_stoi_result
    (s : native_String) (k : native_Int) : native_Int :=
  if k = 0 then 0 else native_str_to_int (native_str_substr s 0 k)

private theorem sr_take_ne_nil (s : native_String) (j : Nat)
    (hjPos : 0 < j) (hj : j ≤ s.length) : s.take j ≠ [] := by
  intro h
  have hlen : (s.take j).length = j := by
    simp [List.length_take, Nat.min_eq_left hj]
  simp [h] at hlen
  omega

private theorem sr_native_stoi_result_ofNat (s : native_String) (j : Nat)
    (hj : j ≤ s.length)
    (hAll : s.all impl_native_char_is_digit = true) :
    sr_native_stoi_result s (Int.ofNat j) =
      Int.ofNat (impl_native_decimal_digits_to_nat (s.take j)) := by
  by_cases hj0 : j = 0
  · subst j
    simp [sr_native_stoi_result, impl_native_decimal_digits_to_nat]
  have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
  have hInt : (Int.ofNat j : native_Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr hj0
  rw [sr_native_stoi_result, if_neg hInt]
  rw [sr_native_str_substr_zero_nat s j hj]
  exact sr_native_str_to_int_of_ne_nil_all _
    (sr_take_ne_nil s j hjPos hj) (sr_all_digits_take s j hAll)

private theorem sr_native_stoi_result_recurrence
    (s : native_String) (j : Nat) (hj : j < s.length)
    (hAll : s.all impl_native_char_is_digit = true) :
    sr_native_stoi_result s (Int.ofNat (j + 1)) =
      Int.ofNat (s[j] - 48) +
        10 * sr_native_stoi_result s (Int.ofNat j) := by
  rw [sr_native_stoi_result_ofNat s (j + 1) (by omega) hAll]
  rw [sr_native_stoi_result_ofNat s j (by omega) hAll]
  rw [sr_decimal_take_succ s j hj]
  let a := impl_native_decimal_digits_to_nat (s.take j)
  let b := s[j] - 48
  change Int.ofNat (10 * a + b) = Int.ofNat b + 10 * Int.ofNat a
  rw [show Int.ofNat (10 * a + b) =
      Int.ofNat (10 * a) + Int.ofNat b from Int.natCast_add _ _]
  rw [show Int.ofNat (10 * a) =
      Int.ofNat 10 * Int.ofNat a from Int.natCast_mul _ _]
  change 10 * Int.ofNat a + Int.ofNat b =
    Int.ofNat b + 10 * Int.ofNat a
  omega

private theorem sr_native_stoi_result_le_total
    (s : native_String) (j : Nat) (hj : j ≤ s.length)
    (hAll : s.all impl_native_char_is_digit = true) :
    sr_native_stoi_result s (Int.ofNat j) ≤
      Int.ofNat (impl_native_decimal_digits_to_nat s) := by
  rw [sr_native_stoi_result_ofNat s j hj hAll]
  exact Int.ofNat_le.mpr (sr_decimal_take_le s j hAll)

private theorem sr_digit_at (s : native_String) (j : Nat)
    (hj : j < s.length) (hAll : s.all impl_native_char_is_digit = true) :
    impl_native_char_is_digit s[j] = true := by
  rw [List.all_eq_true] at hAll
  exact hAll s[j] (List.getElem_mem hj)

private theorem sr_str_to_int_nonneg_data (s : native_String)
    (hNonneg : 0 ≤ native_str_to_int s) :
    s ≠ [] ∧ s.all impl_native_char_is_digit = true ∧
      native_str_to_int s = Int.ofNat (impl_native_decimal_digits_to_nat s) := by
  have hs : s ≠ [] := by
    intro hs
    subst s
    simp [native_str_to_int] at hNonneg
  have hAll : s.all impl_native_char_is_digit = true := by
    cases s with
    | nil => contradiction
    | cons c cs =>
        simp only [native_str_to_int] at hNonneg
        by_cases hAll : (c :: cs).all impl_native_char_is_digit = true
        · exact hAll
        · rw [if_neg hAll] at hNonneg
          simp at hNonneg
  refine ⟨hs, hAll, ?_⟩
  exact sr_native_str_to_int_of_ne_nil_all s hs hAll

private theorem sr_str_to_int_neg_data (s : native_String)
    (hNeg : native_str_to_int s < 0) :
    native_str_to_int s = -1 ∧
      (s = [] ∨ s.all impl_native_char_is_digit ≠ true) := by
  by_cases hs : s = []
  · subst s
    simp [native_str_to_int]
  · by_cases hAll : s.all impl_native_char_is_digit = true
    · have hEq := sr_native_str_to_int_of_ne_nil_all s hs hAll
      rw [hEq] at hNeg
      exact False.elim (Int.not_lt_of_ge (Int.natCast_nonneg _) hNeg)
    · simp [native_str_to_int, hs, hAll]

private theorem sr_str_to_code_at (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length) :
    native_str_to_code (native_str_substr s (Int.ofNat j) 1) =
      Int.ofNat s[j] := by
  have hc : native_char_valid s[j] = true := by
    rw [native_string_valid, List.all_eq_true] at hValid
    exact hValid s[j] (List.getElem_mem hj)
  rw [sr_native_str_substr_one_nat s j hj]
  simp [native_str_to_code, hc]

private theorem sr_digit_code_value (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length)
    (hAll : s.all impl_native_char_is_digit = true) :
    Int.ofNat (s[j] - 48) =
      native_str_to_code (native_str_substr s (Int.ofNat j) 1) - 48 := by
  have hd : impl_native_char_is_digit s[j] = true := sr_digit_at s j hj hAll
  have hb := StrInReFromIntDigRangeProof.native_digit_bounds s[j] hd
  rw [sr_str_to_code_at s j hValid hj]
  simpa using Int.ofNat_sub hb.1

private theorem sr_digit_code_bounds (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length)
    (hAll : s.all impl_native_char_is_digit = true) :
    0 ≤ native_str_to_code
          (native_str_substr s (Int.ofNat j) 1) - 48 ∧
      native_str_to_code
          (native_str_substr s (Int.ofNat j) 1) - 48 < 10 := by
  let c := s[j]
  have hd : impl_native_char_is_digit c = true := by
    simpa [c] using sr_digit_at s j hj hAll
  have hb := StrInReFromIntDigRangeProof.native_digit_bounds c hd
  have hCode :
      native_str_to_code (native_str_substr s (Int.ofNat j) 1) =
        Int.ofNat c := by
    simpa [c] using sr_str_to_code_at s j hValid hj
  rw [hCode]
  constructor
  · have hb' : (48 : Int) ≤ Int.ofNat c := Int.ofNat_le.mpr hb.1
    exact Int.sub_nonneg.mpr hb'
  · have hb' : Int.ofNat c ≤ (57 : Int) := Int.ofNat_le.mpr hb.2
    apply (Int.add_lt_add_iff_right (a := Int.ofNat c - 48)
      (b := 10) 48).mp
    rw [Int.sub_add_cancel]
    simpa using Int.lt_add_one_iff.mpr hb'

private theorem sr_nondigit_code_outside (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length)
    (hNotDigit : impl_native_char_is_digit s[j] ≠ true) :
    native_str_to_code (native_str_substr s (Int.ofNat j) 1) - 48 < 0 ∨
      10 ≤ native_str_to_code
        (native_str_substr s (Int.ofNat j) 1) - 48 := by
  let c := s[j]
  have hNotDigit' : impl_native_char_is_digit c ≠ true := by
    simpa [c] using hNotDigit
  have hOutside : ¬ (48 ≤ c ∧ c ≤ 57) := by
    intro h
    apply hNotDigit'
    unfold impl_native_char_is_digit
    simpa [Bool.and_eq_true] using h
  have hCode :
      native_str_to_code (native_str_substr s (Int.ofNat j) 1) =
        Int.ofNat c := by
    simpa [c] using sr_str_to_code_at s j hValid hj
  rw [hCode]
  by_cases hLo : c < 48
  · left
    have hLo' : Int.ofNat c < 48 := Int.ofNat_lt.mpr hLo
    apply (Int.add_lt_add_iff_right (a := Int.ofNat c - 48)
      (b := 0) 48).mp
    rw [Int.sub_add_cancel]
    simpa using hLo'
  · right
    have hHi : 57 < c := by
      apply Nat.lt_of_not_ge
      intro hc
      exact hOutside ⟨Nat.le_of_not_gt hLo, hc⟩
    have hHi' : (57 : Int) < Int.ofNat c := Int.ofNat_lt.mpr hHi
    apply (Int.add_le_add_iff_right (a := 10)
      (b := Int.ofNat c - 48) 48).mp
    rw [Int.sub_add_cancel]
    simpa using Int.add_one_le_iff.mpr hHi'

private def sr_nondigit_re : SmtRegLan :=
  native_re_inter native_re_allchar
    (native_re_comp
      (native_re_range (native_string_lit "0") (native_string_lit "9")))

private theorem sr_prefix_empty (xs : native_String) (n : Nat) :
    impl_native_re_prefix_match_len_go SmtRegLan.empty xs n = none := by
  simpa using
    native_re_prefix_go_empty (impl_native_string_to_values xs) n

private theorem sr_prefix_digit_dead (xs : native_String) (n : Nat) :
    impl_native_re_prefix_match_len_go
        (SmtRegLan.inter SmtRegLan.epsilon (SmtRegLan.comp SmtRegLan.epsilon))
        xs n = none := by
  cases xs with
  | nil => simp [impl_native_re_prefix_match_len_go, native_re_nullable]
  | cons c cs =>
      change impl_native_re_prefix_match_len_go
        (SmtRegLan.inter SmtRegLan.epsilon
          (SmtRegLan.comp SmtRegLan.epsilon))
        (SmtValue.Char c :: impl_native_string_to_values cs) n = none
      rw [impl_native_re_prefix_match_len_go.eq_2]
      simp [native_re_nullable, native_re_deriv, native_re_mk_inter,
        native_re_mk_comp, native_re_inter, native_re_comp,
        native_re_prefix_go_empty, sr_prefix_empty]

private theorem sr_prefix_nondigit_live (xs : native_String) (n : Nat) :
    impl_native_re_prefix_match_len_go
        (SmtRegLan.inter SmtRegLan.epsilon (SmtRegLan.comp SmtRegLan.empty))
        xs n = some n := by
  cases xs <;> simp [impl_native_re_prefix_match_len_go, native_re_nullable]

private theorem sr_nondigit_prefix (c : native_Char) (cs : native_String)
    (hc : native_char_valid c = true) :
    native_re_prefix_match_len? sr_nondigit_re (c :: cs) =
      if impl_native_char_is_digit c then none else some 1 := by
  unfold sr_nondigit_re native_re_prefix_match_len? native_re_allchar
    native_re_comp native_re_inter native_re_range native_string_lit
  rw [impl_native_re_prefix_match_len_go.eq_2]
  by_cases hd : 48 ≤ c ∧ c ≤ 57
  · have h48 : native_char_valid 48 = true := by native_decide
    have h57 : native_char_valid 57 = true := by native_decide
    simp [native_re_nullable, native_re_deriv, native_re_mk_inter,
      native_re_mk_comp, native_re_elem_valid, impl_native_re_elem_le,
      native_re_inter, native_re_comp, hc, h48, h57, hd,
      impl_native_char_is_digit, sr_prefix_digit_dead]
  · have h48 : native_char_valid 48 = true := by native_decide
    have h57 : native_char_valid 57 = true := by native_decide
    simp [native_re_nullable, native_re_deriv, native_re_mk_inter,
      native_re_mk_comp, native_re_elem_valid, impl_native_re_elem_le,
      native_re_inter, native_re_comp, hc, h48, h57, hd,
      impl_native_char_is_digit, sr_prefix_nondigit_live]

private theorem sr_nondigit_find_aux :
    ∀ (xs : native_String) (idx : Nat),
      native_string_valid xs = true →
      xs.all impl_native_char_is_digit ≠ true →
      ∃ j : Nat, ∃ c : native_Char, ∃ pre post : native_String,
        xs = pre ++ (c :: post) ∧ pre.length = j ∧
        impl_native_char_is_digit c ≠ true ∧
        impl_native_re_find_idx_aux sr_nondigit_re xs idx = some (idx + j, 1)
  | [], idx, _hv, h => by simp at h
  | c :: cs, idx, hv, h => by
      have hp : native_char_valid c = true ∧
          native_string_valid cs = true := by
        simpa [native_string_valid, Bool.and_eq_true] using hv
      simp only [impl_native_string_to_values, List.map_cons]
      have hPrefix :
          native_re_prefix_match_len? sr_nondigit_re
              (SmtValue.Char c :: List.map SmtValue.Char cs) =
            if impl_native_char_is_digit c then none else some 1 := by
        simpa [impl_native_string_to_values] using
          sr_nondigit_prefix c cs hp.1
      rw [impl_native_re_find_idx_aux.eq_def, hPrefix]
      by_cases hc : impl_native_char_is_digit c = true
      · simp [hc]
        have htail : cs.all impl_native_char_is_digit ≠ true := by
          intro ht
          apply h
          simp [hc, ht]
        rcases sr_nondigit_find_aux cs (idx + 1) hp.2 htail with
          ⟨j, d, pre, post, hcs, hlen, hd, hfind⟩
        refine ⟨j + 1, d, c :: pre, ?_⟩
        refine ⟨⟨post, by simp [hcs]⟩, by simpa using hlen,
          by simpa using hd, ?_⟩
        have hsimpa := hfind
        try simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hsimpa ⊢
        exact hsimpa
      · simp [hc]
        exact ⟨0, c, [], ⟨⟨cs, by simp⟩, by simp,
          by simpa using hc, by simp⟩⟩

private theorem sr_nondigit_index_data (s : native_String)
    (hValid : native_string_valid s = true)
    (hNotAll : s.all impl_native_char_is_digit ≠ true) :
    ∃ j c pre post,
      s = pre ++ c :: post ∧ pre.length = j ∧
      impl_native_char_is_digit c ≠ true ∧
      native_str_indexof_re s sr_nondigit_re 0 = Int.ofNat j ∧
      j < s.length := by
  rcases sr_nondigit_find_aux s 0 hValid hNotAll with
    ⟨j, c, pre, post, hs, hlen, hc, hfind⟩
  refine ⟨j, c, pre, post, hs, hlen, hc, ?_, ?_⟩
  · simp [native_str_indexof_re, hValid, native_re_find_idx_from, hfind]
  · subst s
    simp only [List.length_append, List.length_cons]
    omega

/-- An update at an invalid index leaves the source sequence unchanged. -/
private theorem sr_native_seq_update_eq_self_of_invalid
    (xs ys : List SmtValue) (i : native_Int)
    (hInvalid : i < 0 ∨ Int.ofNat xs.length ≤ i) :
    native_seq_update xs i ys = xs := by
  unfold native_seq_update
  rcases hInvalid with hNeg | hHigh
  · change (if (decide (i < 0) ||
        decide (Int.ofNat xs.length ≤ i)) = true then xs else _) = xs
    simp [hNeg]
  · change (if (decide (i < 0) ||
        decide (Int.ofNat xs.length ≤ i)) = true then xs else _) = xs
    have hHigh' : (xs.length : Int) ≤ i := by
      simpa [Int.ofNat_eq_natCast] using hHigh
    simp [hHigh']

/-- Extracting a natural number of elements at an in-bounds integer offset is
    the corresponding list slice, including the zero-length case. -/
private theorem sr_native_seq_extract_valid_ofNat
    (xs : List SmtValue) (i : native_Int) (k : Nat)
    (hNonneg : 0 ≤ i) (hLt : i < Int.ofNat xs.length) :
    native_seq_extract xs i (Int.ofNat k) =
      (xs.drop (Int.toNat i)).take k := by
  by_cases hk : k = 0
  · subst k
    simp [native_seq_extract]
  · have hkPos : 0 < (Int.ofNat k : native_Int) :=
      Int.ofNat_lt.mpr (Nat.pos_of_ne_zero hk)
    simpa using native_seq_extract_eq_drop_take xs i (Int.ofNat k)
      hNonneg hkPos

/-- A true generated syntactic-equality test identifies its operands. -/
private theorem sr_eq_of_eo_is_eq_true (a b : Term)
    (h : __eo_is_eq a b = Term.Boolean true) : a = b := by
  simp [__eo_is_eq, native_teq, native_and, native_not,
    SmtEval.native_and, SmtEval.native_not] at h
  exact h.2.2.symm

/-- At an in-bounds index, native update has exactly the decomposition used by
    the generated string-reduction predicate. -/
private theorem sr_native_seq_update_active_facts
    (xs ys : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ i) (hLt : i < Int.ofNat xs.length) :
    let j := Int.toNat i
    let selected := ys.take (xs.length - j)
    native_seq_update xs i ys =
        xs.take j ++ selected ++ xs.drop (j + selected.length) ∧
      xs = xs.take j ++ (xs.drop j).take selected.length ++
        xs.drop (j + selected.length) ∧
      (xs.take j).length = Int.toNat i ∧
      selected.length = ((xs.drop j).take selected.length).length := by
  dsimp
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
  have hNotHigh : ¬ Int.ofNat xs.length ≤ i := Int.not_le_of_gt hLt
  have hCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hNonneg
  have hJlt : Int.toNat i < xs.length := by
    apply Int.ofNat_lt.mp
    calc
      Int.ofNat (Int.toNat i) = i := hCast
      _ < Int.ofNat xs.length := hLt
  have hJle : Int.toNat i ≤ xs.length := Nat.le_of_lt hJlt
  have hSelectedLe :
      (ys.take (xs.length - Int.toNat i)).length ≤ xs.length - Int.toNat i := by
    exact List.length_take_le _ _
  have hDropLen : (xs.drop (Int.toNat i)).length =
      xs.length - Int.toNat i := by simp
  have hSource :
      xs = xs.take (Int.toNat i) ++
          (xs.drop (Int.toNat i)).take
            (ys.take (xs.length - Int.toNat i)).length ++
          xs.drop
            (Int.toNat i + (ys.take (xs.length - Int.toNat i)).length) := by
    let j := Int.toNat i
    let k := (ys.take (xs.length - Int.toNat i)).length
    calc
      xs = xs.take j ++ xs.drop j := (List.take_append_drop j xs).symm
      _ = xs.take j ++
          ((xs.drop j).take k ++ (xs.drop j).drop k) := by
        exact congrArg (fun tail => xs.take j ++ tail)
          (List.take_append_drop k (xs.drop j)).symm
      _ = xs.take j ++ (xs.drop j).take k ++ xs.drop (j + k) := by
        rw [List.drop_drop]
        simp only [List.append_assoc]
  have hUpdate :
      native_seq_update xs i ys =
        xs.take (Int.toNat i) ++ ys.take (xs.length - Int.toNat i) ++
          xs.drop
            (Int.toNat i + (ys.take (xs.length - Int.toNat i)).length) := by
    unfold native_seq_update
    change (if (decide (i < 0) ||
        decide (Int.ofNat xs.length ≤ i)) = true then xs
      else xs.take (Int.toNat i) ++ ys.take (xs.length - Int.toNat i) ++
        xs.drop (Int.toNat i + ys.length)) = _
    rw [show decide (i < 0) = false from decide_eq_false hNotNeg]
    rw [show decide (Int.ofNat xs.length ≤ i) = false from
      decide_eq_false hNotHigh]
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    by_cases hFits : ys.length ≤ xs.length - Int.toNat i
    · rw [List.take_of_length_le hFits]
    · have hRemLe : xs.length - Int.toNat i ≤ ys.length := by omega
      have hDropYs : xs.drop (Int.toNat i + ys.length) = [] := by
        apply List.drop_eq_nil_of_le
        omega
      have hDropSelected :
          xs.drop
              (Int.toNat i +
                (ys.take (xs.length - Int.toNat i)).length) = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_take]
        rw [Nat.min_eq_left hRemLe]
        omega
      rw [hDropYs, hDropSelected]
  refine ⟨hUpdate, hSource, ?_, ?_⟩
  · simp [hJle]
  · exact (List.length_take_of_le (by
      simpa [hDropLen] using hSelectedLe)).symm

/-- The syntactic constant-length shortcut used by `str_update` is sound with
    respect to model evaluation in its only special case, length one. -/
private theorem sr_str_value_len_one_eval_length
    (M : SmtModel) (x : Term) (T : SmtType) (sx : SmtSeq)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hLen : __str_value_len x = Term.Numeral 1) :
    (native_unpack_seq sx).length = 1 := by
  rcases RuleProofs.value_len_numeral_cases x 1 hLen with
      ⟨w, rfl⟩ | ⟨e, ss, rfl⟩ | ⟨U, rfl⟩ | ⟨e, rfl⟩
  · change __smtx_model_eval M (SmtTerm.String w) = SmtValue.Seq sx at hxEval
    rw [__smtx_model_eval.eq_4] at hxEval
    injection hxEval with hsx
    rw [← hsx, RuleProofs.unpack_pack_string_map, List.length_map]
    simp [__str_value_len, __eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_len, native_teq, native_and, native_not, native_ite,
      SmtEval.native_ite] at hLen
    exact Int.ofNat_inj.mp hLen
  · let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    obtain ⟨⟨shead, hHeadEval⟩, ⟨stail, hTailEval⟩⟩ :=
      strConcat_args_eval_seq_of_concat_eval_seq M head ss ⟨sx, by simpa [head] using hxEval⟩
    obtain ⟨swhole, hWholeEval, hWholeUnpack⟩ :=
      RuleProofs.concat_unpack M head ss shead stail hHeadEval hTailEval
    have hsx : sx = swhole := by
      rw [hxEval] at hWholeEval
      injection hWholeEval
    obtain ⟨shead', hHeadEval', hHeadUnpack⟩ :=
      RuleProofs.eval_seqUnitAtom M e
    have hHeadSeq : shead = shead' := by
      rw [hHeadEval] at hHeadEval'
      injection hHeadEval'
    have hTailEmpty : __str_is_empty ss = Term.Boolean true :=
      RuleProofs.concatSeqUnit_len_one_tail_empty e ss hLen
    have hTailUnpack : native_unpack_seq stail = [] :=
      RuleProofs.str_is_empty_eval_unpack_nil M ss stail hTailEmpty hTailEval
    rw [hsx, hWholeUnpack, hHeadSeq, hHeadUnpack, hTailUnpack]
    simp
  · have hZero :
        __str_value_len
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) U)) = Term.Numeral 0 := by
      simp [__str_value_len, __is_seq_const, __is_seq_const_rec,
        __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not,
        __eo_requires, __eo_list_len,
        RuleProofs.strConcat_is_list_explicit_seq_empty_seq,
        __eo_list_len_rec]
    rw [hZero] at hLen
    cases hLen
  · obtain ⟨sx', hxEval', hxUnpack⟩ := RuleProofs.eval_seqUnitAtom M e
    have hsx : sx = sx' := by
      rw [hxEval] at hxEval'
      injection hxEval'
    rw [hsx, hxUnpack]
    simp

private theorem sr_native_str_substr_cons_succ
    (a : native_Char) (s : native_String) (j : Nat) (hj : j ≤ s.length) :
    native_str_substr (a :: s) (Int.ofNat (j + 1)) 1 =
      native_str_substr s (Int.ofNat j) 1 := by
  by_cases hlt : j < s.length
  · rw [sr_native_str_substr_one_nat s j hlt]
    rw [sr_native_str_substr_one_nat (a :: s) (j + 1) (by simpa using hlt)]
    simp
  · have heq : j = s.length := by omega
    subst j
    rw [sr_native_str_substr_at_length s]
    simpa using sr_native_str_substr_at_length (a :: s)

/-- Unequal strings have a first lexicographically decisive position. -/
private theorem sr_native_str_leq_witness :
    ∀ (s t : native_String),
      native_string_valid s = true →
      native_string_valid t = true →
      s ≠ t →
      ∃ j : Nat,
        j ≤ s.length ∧ j ≤ t.length ∧
        s.take j = t.take j ∧
        (if sr_native_str_leq_bool s t = true then
          native_str_to_code (native_str_substr s (Int.ofNat j) 1) <
            native_str_to_code (native_str_substr t (Int.ofNat j) 1)
        else
          native_str_to_code (native_str_substr t (Int.ofNat j) 1) <
            native_str_to_code (native_str_substr s (Int.ofNat j) 1))
  | [], [], _hs, _ht, hne => False.elim (hne rfl)
  | [], b :: bs, _hs, ht, _hne => by
      have hb : native_char_valid b = true := by
        have h := (show native_char_valid b = true ∧
            native_string_valid bs = true by
          simpa [native_string_valid, Bool.and_eq_true] using ht)
        exact h.1
      refine ⟨0, by simp, by simp, by simp, ?_⟩
      have hSub : native_str_substr (b :: bs) 0 1 = [b] := by
        have hsimpa := sr_native_str_substr_one_nat (b :: bs) 0 (by simp)
        try simp at hsimpa ⊢
        exact hsimpa
      have hEmpty : native_str_substr [] 0 1 = [] := by
        simp [native_str_substr, native_str_len]
      simp [sr_native_str_leq_bool, native_str_lt, native_or,
        hSub, hEmpty, native_str_to_code, hb]
      have hb0 : (0 : Int) ≤ Int.ofNat b := Int.natCast_nonneg b
      exact Int.lt_of_lt_of_le (by decide) hb0
  | a :: as, [], hs, _ht, _hne => by
      have ha : native_char_valid a = true := by
        have h := (show native_char_valid a = true ∧
            native_string_valid as = true by
          simpa [native_string_valid, Bool.and_eq_true] using hs)
        exact h.1
      refine ⟨0, by simp, by simp, by simp, ?_⟩
      have hSub : native_str_substr (a :: as) 0 1 = [a] := by
        have hsimpa := sr_native_str_substr_one_nat (a :: as) 0 (by simp)
        try simp at hsimpa ⊢
        exact hsimpa
      have hEmpty : native_str_substr [] 0 1 = [] := by
        simp [native_str_substr, native_str_len]
      simp [sr_native_str_leq_bool, native_str_lt, native_or,
        hSub, hEmpty, native_str_to_code, ha]
      have ha0 : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
      exact Int.lt_of_lt_of_le (by decide) ha0
  | a :: as, b :: bs, hs, ht, hne => by
      have ha : native_char_valid a = true := by
        have h := (show native_char_valid a = true ∧
            native_string_valid as = true by
          simpa [native_string_valid, Bool.and_eq_true] using hs)
        exact h.1
      have hb : native_char_valid b = true := by
        have h := (show native_char_valid b = true ∧
            native_string_valid bs = true by
          simpa [native_string_valid, Bool.and_eq_true] using ht)
        exact h.1
      have has : native_string_valid as = true := by
        have h := (show native_char_valid a = true ∧
            native_string_valid as = true by
          simpa [native_string_valid, Bool.and_eq_true] using hs)
        exact h.2
      have hbs : native_string_valid bs = true := by
        have h := (show native_char_valid b = true ∧
            native_string_valid bs = true by
          simpa [native_string_valid, Bool.and_eq_true] using ht)
        exact h.2
      by_cases hab : a = b
      · subst b
        have hTailNe : as ≠ bs := by
          intro h
          exact hne (by rw [h])
        rcases sr_native_str_leq_witness as bs has hbs hTailNe with
          ⟨j, hjas, hjbs, hpre, hcmp⟩
        refine ⟨j + 1, by simpa using hjas, by simpa using hjbs, ?_, ?_⟩
        · simpa [List.take_succ_cons] using
            congrArg (fun xs => a :: xs) hpre
        · rw [sr_native_str_substr_cons_succ a as j hjas,
            sr_native_str_substr_cons_succ a bs j hjbs]
          simpa [sr_native_str_leq_bool, native_str_lt, native_or,
            List.cons_lt_cons_iff] using hcmp
      · refine ⟨0, by simp, by simp, by simp, ?_⟩
        rw [sr_native_str_substr_one_nat (a :: as) 0 (by simp),
          sr_native_str_substr_one_nat (b :: bs) 0 (by simp)]
        by_cases hlt : a < b
        · simp [sr_native_str_leq_bool, native_str_lt, native_or,
            List.cons_lt_cons_iff, hab, hlt, native_str_to_code, ha, hb]
        · have hba : b < a :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hab)
          simp [sr_native_str_leq_bool, native_str_lt, native_or,
            List.cons_lt_cons_iff, hab, hlt, hba,
            native_str_to_code, ha, hb]

private abbrev srMkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev srMkAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

private abbrev srPurify (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_purify) x

private abbrev stringReductionBody (s : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and) (__str_reduction_pred s))
    (srMkAnd (srMkEq s (srPurify s)) (Term.Boolean true))

/-- Recover top-level closedness from the recursive empty-environment form. -/
private theorem sr_eo_is_closed_of_rec_nil
    (t : Term) (hNe : t ≠ Term.Stuck)
    (hRec :
      __eo_is_closed_rec t Term.__eo_List_nil = Term.Boolean true) :
    __eo_is_closed t = Term.Boolean true := by
  cases t <;> simp [__eo_is_closed] at hNe ⊢
  all_goals exact hRec

/-- Closedness of a unary operator application implies closedness of its argument. -/
private theorem sr_eo_is_closed_apply_uop_arg
    (op : UserOp) (x : Term) (hNe : x ≠ Term.Stuck)
    (hClosed :
      __eo_is_closed (Term.Apply (Term.UOp op) x) = Term.Boolean true) :
    __eo_is_closed x = Term.Boolean true := by
  have hParentRec := eo_is_closed_eq_true_rec_nil hClosed
  have hArgRec := eo_is_closed_rec_apply_uop_arg_eq_true
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hParentRec
  exact sr_eo_is_closed_of_rec_nil x hNe hArgRec

/-- Closedness of a binary operator application splits over its arguments. -/
private theorem sr_eo_is_closed_binary_uop_args
    (op : UserOp) (x y : Term)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNe : x ≠ Term.Stuck) (hYNe : y ≠ Term.Stuck)
    (hClosed :
      __eo_is_closed (Term.Apply (Term.Apply (Term.UOp op) x) y) =
        Term.Boolean true) :
    __eo_is_closed x = Term.Boolean true ∧
      __eo_is_closed y = Term.Boolean true := by
  have hParentRec := eo_is_closed_eq_true_rec_nil hClosed
  have hArgsRec := eo_is_closed_rec_binary_uop_eq_true_cases
    hNotForall hNotExists
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hParentRec
  exact ⟨sr_eo_is_closed_of_rec_nil x hXNe hArgsRec.1,
    sr_eo_is_closed_of_rec_nil y hYNe hArgsRec.2⟩

/-- Closedness of a ternary operator application splits over its arguments. -/
private theorem sr_eo_is_closed_ternary_uop_args
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
  exact ⟨sr_eo_is_closed_of_rec_nil x hXNe hArgsRec.1,
    sr_eo_is_closed_of_rec_nil y hYNe hArgsRec.2.1,
    sr_eo_is_closed_of_rec_nil z hZNe hArgsRec.2.2⟩

/-- The SMT encoding used for EO `forall` is true when its body is true
for every typed canonical value. -/
private theorem sr_eval_forall_encoding_true
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

/-- The two-variable SMT encoding emitted for an EO `forall` list is true
when its body is true for every pair of typed canonical values. -/
private theorem sr_eval_forall2_encoding_true
    (M : SmtModel) (s₁ s₂ : native_String) (T₁ T₂ : SmtType)
    (body : SmtTerm)
    (hAll :
      ∀ v₁ v₂ : SmtValue,
        __smtx_typeof_value v₁ = T₁ →
        __smtx_value_canonical v₁ = true →
        __smtx_typeof_value v₂ = T₂ →
        __smtx_value_canonical v₂ = true →
        __smtx_model_eval
            (native_model_push (native_model_push M s₁ T₁ v₁) s₂ T₂ v₂)
            body = SmtValue.Boolean true) :
    __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.exists s₁ T₁
            (SmtTerm.exists s₂ T₂ (SmtTerm.not body)))) =
      SmtValue.Boolean true := by
  classical
  have hNoSat :
      ¬ ∃ v₁ : SmtValue,
        __smtx_typeof_value v₁ = T₁ ∧
        __smtx_value_canonical v₁ = true ∧
        __smtx_model_eval (native_model_push M s₁ T₁ v₁)
            (SmtTerm.exists s₂ T₂ (SmtTerm.not body)) =
          SmtValue.Boolean true := by
    rintro ⟨v₁, hv₁Ty, hv₁Canonical, hv₁Exists⟩
    change (if _h :
        ∃ v₂ : SmtValue,
          __smtx_typeof_value v₂ = T₂ ∧
          __smtx_value_canonical v₂ = true ∧
          __smtx_model_eval
              (native_model_push (native_model_push M s₁ T₁ v₁)
                s₂ T₂ v₂) (SmtTerm.not body) =
            SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean true at hv₁Exists
    split at hv₁Exists
    · rename_i hWitness
      rcases hWitness with ⟨v₂, hv₂Ty, hv₂Canonical, hv₂Not⟩
      have hvBody := hAll v₁ v₂ hv₁Ty hv₁Canonical
        hv₂Ty hv₂Canonical
      simp [__smtx_model_eval, __smtx_model_eval_not, native_not,
        hvBody] at hv₂Not
    · simp at hv₁Exists
  have hExistsEval :
      native_eval_exists M s₁ T₁
          (SmtTerm.exists s₂ T₂ (SmtTerm.not body)) =
        SmtValue.Boolean false := by
    change (if _h :
        ∃ v₁ : SmtValue,
          __smtx_typeof_value v₁ = T₁ ∧
          __smtx_value_canonical v₁ = true ∧
          __smtx_model_eval (native_model_push M s₁ T₁ v₁)
              (SmtTerm.exists s₂ T₂ (SmtTerm.not body)) =
            SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean false
    rw [dif_neg hNoSat]
  change __smtx_model_eval_not
      (native_eval_exists M s₁ T₁
        (SmtTerm.exists s₂ T₂ (SmtTerm.not body))) =
      SmtValue.Boolean true
  rw [hExistsEval]
  rfl

/-- A typed canonical counterexample makes the SMT encoding of EO `forall`
false. -/
private theorem sr_eval_forall_encoding_false
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (v : SmtValue)
    (hvTy : __smtx_typeof_value v = T)
    (hvCanonical : __smtx_value_canonical v = true)
    (hvBody :
      __smtx_model_eval (native_model_push M s T v) body =
        SmtValue.Boolean false) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      SmtValue.Boolean false := by
  classical
  have hvNot :
      __smtx_model_eval (native_model_push M s T v)
          (SmtTerm.not body) = SmtValue.Boolean true := by
    simp [__smtx_model_eval, __smtx_model_eval_not, native_not, hvBody]
  have hSat :
      ∃ w : SmtValue,
        __smtx_typeof_value w = T ∧
        __smtx_value_canonical w = true ∧
        __smtx_model_eval (native_model_push M s T w)
            (SmtTerm.not body) = SmtValue.Boolean true :=
    ⟨v, hvTy, hvCanonical, hvNot⟩
  have hExistsEval :
      native_eval_exists M s T (SmtTerm.not body) =
        SmtValue.Boolean true := by
    change (if _h :
        ∃ w : SmtValue,
          __smtx_typeof_value w = T ∧
          __smtx_value_canonical w = true ∧
          __smtx_model_eval (native_model_push M s T w)
              (SmtTerm.not body) = SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean true
    rw [dif_pos hSat]
  change __smtx_model_eval_not
      (native_eval_exists M s T (SmtTerm.not body)) =
        SmtValue.Boolean false
  rw [hExistsEval]
  rfl

/-- The purification marker is semantically the identity. -/
private theorem eo_interprets_purify_eq_self
    (M : SmtModel) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s) :
    eo_interprets M (srMkEq s (srPurify s)) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · exact hTrans
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt s)))
    simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using
      RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt s))

/-- Once its generated predicate holds, the common string-reduction shell holds. -/
private theorem string_reduction_body_true
    (M : SmtModel) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hPred : eo_interprets M (__str_reduction_pred s) true) :
    eo_interprets M (stringReductionBody s) true := by
  have hPredNe : __str_reduction_pred s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (RuleProofs.eo_has_bool_type_of_interprets_true M _ hPred))
  simp only [stringReductionBody, __eo_mk_apply, hPredNe]
  apply RuleProofs.eo_interprets_and_intro M
  · exact hPred
  · apply RuleProofs.eo_interprets_and_intro M
    · exact eo_interprets_purify_eq_self M s hTrans
    · exact RuleProofs.eo_interprets_true M

/-- Semantic obligations specific to the individual string-reduction cases. -/
private theorem string_reduction_pred_true
    (M : SmtModel) (hM : model_wf M) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hClosed : __eo_is_closed s = Term.Boolean true)
    (hBodyTy : __eo_typeof (stringReductionBody s) = Term.Bool) :
    eo_interprets M (__str_reduction_pred s) true := by
  have hPredNe : __str_reduction_pred s ≠ Term.Stuck := by
    intro hPred
    have hBodyNe : stringReductionBody s ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hBodyTy
    apply hBodyNe
    simp [stringReductionBody, hPred, __eo_mk_apply]
  cases s <;>
    simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
  all_goals try
    (change Term.Stuck = Term.Bool at hBodyTy
     exact False.elim (Term.noConfusion hBodyTy))
  case Apply f x =>
    cases f <;> try
      simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
    all_goals try
      (change Term.Stuck = Term.Bool at hBodyTy
       exact False.elim (Term.noConfusion hBodyTy))
    case UOp op =>
      cases op <;> try
        simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
      all_goals try
        (change Term.Stuck = Term.Bool at hBodyTy
         exact False.elim (Term.noConfusion hBodyTy))
      case str_to_int =>
        have hToNN : term_has_non_none_type
            (SmtTerm.str_to_int (__eo_to_smt x)) := by
          have hsimpa := hTrans
          try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
          exact hsimpa
        have hxTy : __smtx_typeof (__eo_to_smt x) =
            SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
            (typeof_str_to_int_eq (__eo_to_smt x)) hToNN
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none SmtType.Char
        let tx := __eo_to_smt x
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let result := SmtTerm._at_purify (SmtTerm.str_to_int tx)
        let sourceLen := SmtTerm.str_len tx
        let prefixAt := fun k => SmtTerm.ite
          (SmtTerm.eq k (SmtTerm.Numeral 0)) (SmtTerm.Numeral 0)
          (SmtTerm.str_to_int
            (SmtTerm.str_substr tx (SmtTerm.Numeral 0) k))
        let nextIdx := SmtTerm.plus idx
          (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
        let digit := SmtTerm.neg
          (SmtTerm.str_to_code
            (SmtTerm.str_substr tx idx (SmtTerm.Numeral 1)))
          (SmtTerm.Numeral 48)
        let recurrence := SmtTerm.eq (prefixAt nextIdx)
          (SmtTerm.plus digit
            (SmtTerm.plus
              (SmtTerm.mult (SmtTerm.Numeral 10)
                (SmtTerm.mult (prefixAt idx) (SmtTerm.Numeral 1)))
              (SmtTerm.Numeral 0)))
        let digitBounds := SmtTerm.and
          (SmtTerm.geq digit (SmtTerm.Numeral 0))
          (SmtTerm.and (SmtTerm.lt digit (SmtTerm.Numeral 10))
            (SmtTerm.Boolean true))
        let validClause := SmtTerm.and recurrence
          (SmtTerm.and digitBounds
            (SmtTerm.and (SmtTerm.geq result (prefixAt nextIdx))
              (SmtTerm.Boolean true)))
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx sourceLen))
            (SmtTerm.or validClause (SmtTerm.Boolean false)))
        let forallPart := SmtTerm.not
          (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
        let success := SmtTerm.and
          (SmtTerm.eq result (prefixAt sourceLen))
          (SmtTerm.and
            (SmtTerm.eq (SmtTerm.Numeral 0)
              (prefixAt (SmtTerm.Numeral 0)))
            (SmtTerm.and (SmtTerm.gt sourceLen (SmtTerm.Numeral 0))
              (SmtTerm.and forallPart (SmtTerm.Boolean true))))
        let nondigitRegex := SmtTerm.re_inter SmtTerm.re_allchar
          (SmtTerm.re_comp
            (SmtTerm.re_range
              (SmtTerm.String (native_string_lit "0"))
              (SmtTerm.String (native_string_lit "9"))))
        let nonDigit := SmtTerm.str_indexof_re tx nondigitRegex
          (SmtTerm.Numeral 0)
        let badDigit := SmtTerm.neg
          (SmtTerm.str_to_code
            (SmtTerm.str_substr tx nonDigit (SmtTerm.Numeral 1)))
          (SmtTerm.Numeral 48)
        let badBounds := SmtTerm.or
          (SmtTerm.lt badDigit (SmtTerm.Numeral 0))
          (SmtTerm.or (SmtTerm.geq badDigit (SmtTerm.Numeral 10))
            (SmtTerm.Boolean false))
        let badWitness := SmtTerm.and
          (SmtTerm.geq nonDigit (SmtTerm.Numeral 0))
          (SmtTerm.and (SmtTerm.lt nonDigit sourceLen)
            (SmtTerm.and badBounds (SmtTerm.Boolean true)))
        let failure := SmtTerm.and
          (SmtTerm.eq result (SmtTerm.Numeral (-1)))
          (SmtTerm.and
            (SmtTerm.or (SmtTerm.eq tx (SmtTerm.String []))
              (SmtTerm.or badWitness (SmtTerm.Boolean false)))
            (SmtTerm.Boolean true))
        let formula := SmtTerm.ite
          (SmtTerm.lt result (SmtTerm.Numeral 0)) failure success
        have hResultTy : __smtx_typeof result = SmtType.Int := by
          simp [result, tx, typeof_str_to_int_eq, hxTy,
            __smtx_typeof, native_ite, native_Teq]
        have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
          simp [sourceLen, tx, typeof_str_len_eq, hxTy,
            __smtx_typeof_seq_op_1_ret]
        have hPrefixTy : ∀ k, __smtx_typeof k = SmtType.Int →
            __smtx_typeof (prefixAt k) = SmtType.Int := by
          intro k hk
          simp [prefixAt, tx, typeof_ite_eq, typeof_eq_eq,
            typeof_str_to_int_eq, typeof_str_substr_eq, hxTy, hk,
            sr_smt_type_wf_int, __smtx_typeof_ite,
            __smtx_typeof_eq, __smtx_typeof_str_substr,
            __smtx_typeof_seq_op_1_ret, __smtx_typeof_guard_wf,
            __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
        have hNextTy : __smtx_typeof nextIdx = SmtType.Int := by
          simp [nextIdx, idx, typeof_plus_eq,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_guard_wf, __smtx_typeof_guard,
            sr_smt_type_wf_int, __smtx_typeof, native_ite, native_Teq]
        have hDigitTy : __smtx_typeof digit = SmtType.Int := by
          simp [digit, idx, tx, typeof_str_to_code_eq,
            typeof_str_substr_eq, hxTy,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_guard_wf, __smtx_typeof_guard,
            sr_smt_type_wf_int, __smtx_typeof, native_ite, native_Teq]
        have hIdxTy : __smtx_typeof idx = SmtType.Int := by
          simp [idx, __smtx_typeof, __smtx_typeof_guard_wf,
            sr_smt_type_wf_int, native_ite]
        have hPrefixIdxTy : __smtx_typeof (prefixAt idx) = SmtType.Int :=
          hPrefixTy idx hIdxTy
        have hPrefixNextTy : __smtx_typeof (prefixAt nextIdx) = SmtType.Int :=
          hPrefixTy nextIdx hNextTy
        have hRecurrenceTy : __smtx_typeof recurrence = SmtType.Bool := by
          simp [recurrence, typeof_eq_eq, typeof_plus_eq, typeof_mult_eq,
            hPrefixIdxTy, hPrefixNextTy, hDigitTy,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_guard_wf, __smtx_typeof_guard,
            sr_smt_type_wf_int, __smtx_typeof_eq, __smtx_typeof,
            native_ite, native_Teq]
        have hDigitBoundsTy : __smtx_typeof digitBounds = SmtType.Bool := by
          simp [digitBounds, typeof_and_eq, typeof_geq_eq, typeof_lt_eq,
            hDigitTy, __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof, native_ite, native_Teq]
        have hValidClauseTy : __smtx_typeof validClause = SmtType.Bool := by
          simp [validClause, typeof_and_eq, typeof_geq_eq,
            hRecurrenceTy, hDigitBoundsTy, hResultTy, hPrefixNextTy,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof, native_ite, native_Teq]
        have hBadWitnessTy : __smtx_typeof badWitness = SmtType.Bool := by
          have hZeroValid :
              native_string_valid (native_string_lit "0") = true := by
            native_decide
          have hNineValid :
              native_string_valid (native_string_lit "9") = true := by
            native_decide
          simp [badWitness, badBounds, badDigit, nonDigit,
            nondigitRegex, sourceLen, tx, typeof_and_eq, typeof_or_eq,
            typeof_geq_eq, typeof_lt_eq, typeof_str_len_eq,
            typeof_str_to_code_eq, typeof_str_substr_eq,
            typeof_str_indexof_re_eq, typeof_re_inter_eq,
            typeof_re_comp_eq, typeof_re_range_eq, hxTy,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_guard_wf, __smtx_typeof_guard,
            sr_smt_type_wf_int, __smtx_typeof, native_ite, native_Teq,
            hZeroValid, hNineValid]
        have hFormulaEq :
            __eo_to_smt
                (__str_reduction_pred
                  (Term.Apply (Term.UOp UserOp.str_to_int) x)) = formula := by
          simp only [__str_reduction_pred, __eo_mk_apply]
          rfl
        change eo_interprets M
          (__str_reduction_pred
            (Term.Apply (Term.UOp UserOp.str_to_int) x)) true
        apply RuleProofs.eo_interprets_of_bool_eval M _ true
        · unfold RuleProofs.eo_has_bool_type
          rw [hFormulaEq]
          have hEmptyValid : native_string_valid [] = true := by
            native_decide
          have hZeroValid : native_string_valid (native_string_lit "0") = true := by
            native_decide
          have hNineValid : native_string_valid (native_string_lit "9") = true := by
            native_decide
          simp [formula, failure, badWitness, badBounds, badDigit,
            nonDigit, nondigitRegex, success, forallPart, qBody,
            validClause, digitBounds, recurrence, digit, nextIdx, idx,
            sourceLen, result, prefixAt, tx, typeof_ite_eq,
            typeof_and_eq, typeof_or_eq, typeof_not_eq, typeof_eq_eq,
            typeof_geq_eq, typeof_gt_eq, typeof_lt_eq, typeof_plus_eq,
            typeof_mult_eq, typeof_str_len_eq, typeof_str_to_code_eq,
            typeof_str_substr_eq, typeof_str_to_int_eq,
            typeof_str_indexof_re_eq, typeof_re_inter_eq,
            typeof_re_comp_eq, typeof_re_range_eq,
            smtx_typeof_exists_term_eq, hxTy, hResultTy, hSourceLenTy,
            hPrefixTy, sr_smt_type_wf_int, __smtx_typeof_ite,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_eq, __smtx_typeof_guard_wf,
            __smtx_typeof_guard, __smtx_typeof, native_ite,
            native_Teq, hEmptyValid, hZeroValid, hNineValid]
        · rw [hFormulaEq]
          have hXValTy :
              __smtx_typeof_value (__smtx_model_eval M tx) =
                SmtType.Seq SmtType.Char := by
            simpa [tx, hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM
                (__eo_to_smt x) hXNN
          rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
          have hSxTy : __smtx_typeof_seq_value sx =
              SmtType.Seq SmtType.Char := by
            simpa [hXEval, __smtx_typeof_value] using hXValTy
          let w := native_unpack_string sx
          have hValid : native_string_valid w = true :=
            native_unpack_string_valid_of_typeof_seq_char hSxTy
          have hPack : native_pack_string w = sx :=
            sr_native_pack_unpack_string sx hSxTy
          have hXEvalString : __smtx_model_eval M tx =
              SmtValue.Seq (native_pack_string w) := by
            rw [hPack]
            exact hXEval
          have hXClosed : __eo_is_closed x = Term.Boolean true := by
            apply sr_eo_is_closed_apply_uop_arg UserOp.str_to_int x
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              have hsimpa := hXNN
              try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            · exact hClosed
          let r := native_str_to_int w
          have hResultEval : __smtx_model_eval M result =
              SmtValue.Numeral r := by
            simp [result, tx, r, __smtx_model_eval,
              __smtx_model_eval_str_to_int,
              __smtx_model_eval__at_purify, hXEvalString,
              sr_native_unpack_pack_string]
          have hSourceLenEval : __smtx_model_eval M sourceLen =
              SmtValue.Numeral (Int.ofNat w.length) := by
            simp [sourceLen, tx, __smtx_model_eval,
              __smtx_model_eval_str_len, hXEvalString, native_seq_len,
              sr_native_unpack_pack_string_length]
          have hPrefixEval : ∀ (N : SmtModel) (kTerm : SmtTerm) (k : Int),
              __smtx_model_eval N tx =
                  SmtValue.Seq (native_pack_string w) →
              __smtx_model_eval N kTerm = SmtValue.Numeral k →
              __smtx_model_eval N (prefixAt kTerm) =
                SmtValue.Numeral (sr_native_stoi_result w k) := by
            intro N kTerm k hTxEval hkEval
            by_cases hk : k = 0 <;>
            simp [prefixAt, tx, sr_native_stoi_result, hk,
              __smtx_model_eval, __smtx_model_eval_eq,
              __smtx_model_eval_ite, __smtx_model_eval_str_substr,
              __smtx_model_eval_str_to_int, native_ite, native_veq,
              hTxEval, hkEval, sr_native_seq_extract_pack_string_eval,
              sr_native_unpack_extract_pack_string,
              sr_native_unpack_pack_string]
          by_cases hr : 0 ≤ r
          · rcases sr_str_to_int_nonneg_data w hr with
              ⟨hNonempty, hAllDigits, hResultEq⟩
            have hLenPos : 0 < w.length := by
              apply Nat.pos_of_ne_zero
              intro hLen
              apply hNonempty
              exact List.eq_nil_of_length_eq_zero hLen
            have hPrefixLen :
                sr_native_stoi_result w (Int.ofNat w.length) = r := by
              rw [sr_native_stoi_result_ofNat w w.length (by simp)
                hAllDigits]
              simpa [r] using hResultEq.symm
            have hForallEval : __smtx_model_eval M forallPart =
                SmtValue.Boolean true := by
              change __smtx_model_eval M
                (SmtTerm.not
                  (SmtTerm.exists idxName SmtType.Int
                    (SmtTerm.not qBody))) = SmtValue.Boolean true
              have hAll : ∀ v : SmtValue,
                  __smtx_typeof_value v = SmtType.Int →
                  __smtx_value_canonical v = true →
                  __smtx_model_eval
                      (native_model_push M idxName SmtType.Int v) qBody =
                    SmtValue.Boolean true := by
                intro v hvTy hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hIdxEval : native_model_var_lookup Mk idxName
                    SmtType.Int = SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hTxEvalPush : __smtx_model_eval Mk tx =
                    SmtValue.Seq (native_pack_string w) := by
                  rw [← hXEvalString]
                  simpa [tx] using
                    (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                      (model_agrees_on_globals_push M idxName SmtType.Int
                        (SmtValue.Numeral k))).symm
                have hResultEvalPush : __smtx_model_eval Mk result =
                    SmtValue.Numeral r := by
                  simp [result, tx, r, __smtx_model_eval,
                    __smtx_model_eval_str_to_int,
                    __smtx_model_eval__at_purify, hTxEvalPush,
                    sr_native_unpack_pack_string]
                have hSourceLenEvalPush : __smtx_model_eval Mk sourceLen =
                    SmtValue.Numeral (Int.ofNat w.length) := by
                  simp [sourceLen, tx, __smtx_model_eval,
                    __smtx_model_eval_str_len, hTxEvalPush, native_seq_len,
                    sr_native_unpack_pack_string_length]
                have hMkTotal : model_wf Mk :=
                  model_total_typed_push hM idxName SmtType.Int
                    (SmtValue.Numeral k) sr_smt_type_wf_int hvTy hvCanonical
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hklt : k < Int.ofNat w.length
                  · let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      have hsimpa := Int.toNat_of_nonneg hk0
                      try simp only [j] at hsimpa ⊢
                      exact hsimpa
                    have hj : j < w.length := by
                      rw [← hCast] at hklt
                      exact Int.ofNat_lt.mp hklt
                    have hIdxTermEval : __smtx_model_eval Mk idx =
                        SmtValue.Numeral k := by
                      simp [idx, __smtx_model_eval, hIdxEval]
                    have hNextEval : __smtx_model_eval Mk nextIdx =
                        SmtValue.Numeral (Int.ofNat (j + 1)) := by
                      simp [nextIdx, idx, __smtx_model_eval,
                        __smtx_model_eval_plus, hIdxEval, native_zplus]
                      exact hCast.symm
                    have hPrefixNext := hPrefixEval Mk nextIdx
                      (Int.ofNat (j + 1)) hTxEvalPush hNextEval
                    have hPrefixIdx := hPrefixEval Mk idx k hTxEvalPush
                      hIdxTermEval
                    have hRec := sr_native_stoi_result_recurrence
                      w j hj hAllDigits
                    rw [hCast] at hRec
                    have hBounds := sr_digit_code_bounds
                      w j hValid hj hAllDigits
                    have hDigitValue := sr_digit_code_value
                      w j hValid hj hAllDigits
                    rw [hCast] at hBounds hDigitValue
                    have hTotal :
                        sr_native_stoi_result w (Int.ofNat (j + 1)) ≤ r := by
                      have hLe := sr_native_stoi_result_le_total w (j + 1)
                        (by omega) hAllDigits
                      rw [← hResultEq] at hLe
                      exact hLe
                    have hDigitEval : __smtx_model_eval Mk digit =
                        SmtValue.Numeral
                          (native_str_to_code
                            (native_str_substr w k 1) - 48) := by
                      simp [digit, tx, __smtx_model_eval,
                        __smtx_model_eval__, __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_to_code, hTxEvalPush,
                        hIdxTermEval, sr_native_seq_extract_pack_string_eval,
                        sr_native_unpack_extract_pack_string,
                        sr_native_unpack_pack_string, native_zplus,
                        native_zneg, Int.sub_eq_add_neg]
                    have hRecEval : __smtx_model_eval Mk recurrence =
                        SmtValue.Boolean true := by
                      rw [hDigitValue] at hRec
                      simp [recurrence, __smtx_model_eval,
                        __smtx_model_eval_eq, __smtx_model_eval_plus,
                        __smtx_model_eval_mult, hPrefixNext, hPrefixIdx,
                        hDigitEval, native_zplus, native_zmult, native_veq]
                      simpa using hRec
                    have hBoundsEval : __smtx_model_eval Mk digitBounds =
                        SmtValue.Boolean true := by
                      have hLower : (48 : Int) ≤
                          native_str_to_code
                            (native_str_substr w k 1) := by
                        exact Int.sub_nonneg.mp hBounds.1
                      simp [digitBounds, __smtx_model_eval,
                        __smtx_model_eval_geq, __smtx_model_eval_leq,
                        __smtx_model_eval_lt, __smtx_model_eval_and,
                        hDigitEval, native_zleq, native_zlt, native_and,
                        hBounds, hLower]
                    have hTotalEval : __smtx_model_eval Mk
                        (SmtTerm.geq result (prefixAt nextIdx)) =
                          SmtValue.Boolean true := by
                      simp [__smtx_model_eval, __smtx_model_eval_geq,
                        __smtx_model_eval_leq, hResultEvalPush,
                        hPrefixNext, native_zleq, hTotal]
                      exact hTotal
                    have hValidEval : __smtx_model_eval Mk validClause =
                        SmtValue.Boolean true := by
                      change __smtx_model_eval_and
                        (__smtx_model_eval Mk recurrence)
                        (__smtx_model_eval_and
                          (__smtx_model_eval Mk digitBounds)
                          (__smtx_model_eval_and
                            (__smtx_model_eval Mk
                              (SmtTerm.geq result (prefixAt nextIdx)))
                            (SmtValue.Boolean true))) =
                        SmtValue.Boolean true
                      rw [hRecEval, hBoundsEval, hTotalEval]
                      rfl
                    simp [qBody, __smtx_model_eval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, hIdxTermEval,
                      hSourceLenEvalPush, hValidEval, native_zlt,
                      native_zleq, native_or, native_not, hk0, hklt]
                  · have hLenLe : Int.ofNat w.length ≤ k :=
                      Int.le_of_not_gt hklt
                    rcases smt_model_eval_bool_is_boolean Mk hMkTotal
                      validClause hValidClauseTy with ⟨b, hValidBool⟩
                    simp [qBody, idx, sourceLen, __smtx_model_eval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_lt,
                      __smtx_model_eval_leq, hValidBool, hIdxEval,
                      hSourceLenEvalPush, hTxEvalPush,
                      __smtx_model_eval_str_len, native_seq_len,
                      sr_native_unpack_pack_string_length,
                      native_zlt, native_zleq,
                      native_or, native_not, hk0, hklt, hLenLe]
                    exact Or.inl hLenLe
                · have hkNeg : k < 0 := Int.lt_of_not_ge hk0
                  rcases smt_model_eval_bool_is_boolean Mk hMkTotal
                    validClause hValidClauseTy with ⟨b, hValidBool⟩
                  simp [qBody, idx, sourceLen, __smtx_model_eval,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, __smtx_model_eval_lt,
                    __smtx_model_eval_leq, hValidBool, hIdxEval,
                    hSourceLenEvalPush, hTxEvalPush,
                    __smtx_model_eval_str_len, native_seq_len,
                    sr_native_unpack_pack_string_length,
                    native_zlt, native_zleq,
                    native_or, native_not, hk0, hkNeg]
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
            have hPrefixLenEval := hPrefixEval M sourceLen
              (Int.ofNat w.length) hXEvalString hSourceLenEval
            have hPrefixZeroEval := hPrefixEval M (SmtTerm.Numeral 0) 0
              hXEvalString (by simp [__smtx_model_eval])
            have hrNot : ¬ r < 0 := Int.not_lt_of_ge hr
            have hPrefixEq :
                r = if w = [] then 0
                  else native_str_to_int
                    (native_str_substr w 0 (Int.ofNat w.length)) := by
              simpa [sr_native_stoi_result, hNonempty] using hPrefixLen.symm
            have hPrefixEvalEq :
                (if w = [] then 0
                  else native_str_to_int
                    (native_str_substr w 0 (Int.ofNat w.length))) = r :=
              hPrefixEq.symm
            simp [formula, success,
              __smtx_model_eval, __smtx_model_eval_ite,
              __smtx_model_eval_lt, __smtx_model_eval_eq,
              __smtx_model_eval_gt, __smtx_model_eval_and,
              hResultEval, hSourceLenEval, hPrefixLenEval,
              hPrefixZeroEval, hForallEval, native_zlt, native_veq,
              native_and, hr, hrNot, hLenPos, hPrefixLen, hPrefixEvalEq,
              sr_native_stoi_result]
            exact hPrefixEq
          · have hrNeg : r < 0 := Int.lt_of_not_ge hr
            rcases sr_str_to_int_neg_data w hrNeg with
              ⟨hResultNegOne, hEmptyOrBad⟩
            have hResultNeg : r < 0 := hrNeg
            rcases hEmptyOrBad with hEmpty | hNotAll
            · rcases smt_model_eval_bool_is_boolean M hM
                  badWitness hBadWitnessTy with ⟨b, hBadBool⟩
              simp [formula, failure,
                __smtx_model_eval, __smtx_model_eval_ite,
                __smtx_model_eval_lt, __smtx_model_eval_eq,
                __smtx_model_eval_and, __smtx_model_eval_or,
                hResultEval, hXEvalString, hBadBool,
                sr_native_pack_string_eq_iff,
                native_zlt, native_veq, native_and, native_or,
                hResultNeg, hResultNegOne, hEmpty]
              exact hResultNegOne
            · rcases sr_nondigit_index_data w hValid hNotAll with
                ⟨j, c, pre, post, hw, hpreLen, hc, hIndex, hj⟩
              have hAt : w[j] = c := by
                have hGet : w[j]? = some c := by
                  rw [hw, ← hpreLen]
                  simp
                exact Option.some.inj
                  ((List.getElem?_eq_getElem hj).symm.trans hGet)
              have hNotDigitAt : impl_native_char_is_digit w[j] ≠ true := by
                simpa [hAt] using hc
              have hOutside := sr_nondigit_code_outside
                w j hValid hj hNotDigitAt
              have hNonDigitEval : __smtx_model_eval M nonDigit =
                  SmtValue.Numeral (Int.ofNat j) := by
                simp [nonDigit, nondigitRegex, tx, __smtx_model_eval,
                  __smtx_model_eval_str_indexof_re,
                  __smtx_model_eval_re_inter,
                  __smtx_model_eval_re_comp,
                  __smtx_model_eval_re_range, hXEvalString,
                  sr_native_unpack_pack_string, sr_nondigit_re]
                simpa [sr_nondigit_re] using hIndex
              have hBadDigitEval : __smtx_model_eval M badDigit =
                  SmtValue.Numeral
                    (native_str_to_code
                      (native_str_substr w (Int.ofNat j) 1) - 48) := by
                simp [badDigit, tx, __smtx_model_eval,
                  __smtx_model_eval__, __smtx_model_eval_str_substr,
                  __smtx_model_eval_str_to_code, hXEvalString,
                  hNonDigitEval, sr_native_seq_extract_pack_string_eval,
                  sr_native_unpack_extract_pack_string,
                  sr_native_unpack_pack_string, native_zplus,
                  native_zneg, Int.sub_eq_add_neg]
              simp [formula, failure, badWitness, badBounds,
                __smtx_model_eval, __smtx_model_eval_ite,
                __smtx_model_eval_lt, __smtx_model_eval_eq,
                __smtx_model_eval_and, __smtx_model_eval_or,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                hResultEval, hSourceLenEval, hNonDigitEval,
                hBadDigitEval, native_zlt, native_zleq, native_veq,
                native_and, native_or, hResultNeg, hResultNegOne, hj]
              exact ⟨hResultNegOne, Or.inr hOutside⟩
      case str_from_int =>
        have hFromNN : term_has_non_none_type
            (SmtTerm.str_from_int (__eo_to_smt x)) := by
          have hsimpa := hTrans
          try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
          exact hsimpa
        have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
          int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
            (typeof_str_from_int_eq (__eo_to_smt x)) hFromNN
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          decide
        let tx := __eo_to_smt x
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let output := SmtTerm._at_purify (SmtTerm.str_from_int tx)
        let outputLen := SmtTerm.str_len output
        let prefixAt := fun k => SmtTerm.ite
          (SmtTerm.eq k (SmtTerm.Numeral 0)) (SmtTerm.Numeral 0)
          (SmtTerm.str_to_int
            (SmtTerm.str_substr (SmtTerm.str_from_int tx)
              (SmtTerm.Numeral 0) k))
        let nextIdx := SmtTerm.plus idx
          (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
        let digit := SmtTerm.neg
          (SmtTerm.str_to_code
            (SmtTerm.str_substr output idx (SmtTerm.Numeral 1)))
          (SmtTerm.Numeral 48)
        let nonneg := fun k => SmtTerm.geq tx k
        let leadingCond := SmtTerm.and
          (SmtTerm.eq idx (SmtTerm.Numeral 0))
          (SmtTerm.and (SmtTerm.gt outputLen (SmtTerm.Numeral 1))
            (SmtTerm.Boolean true))
        let digitMin := SmtTerm.ite leadingCond
          (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)
        let recurrence := SmtTerm.eq (prefixAt nextIdx)
          (SmtTerm.plus digit
            (SmtTerm.plus
                (SmtTerm.mult (SmtTerm.Numeral 10)
                (SmtTerm.mult (prefixAt idx) (SmtTerm.Numeral 1)))
              (SmtTerm.Numeral 0)))
        let digitBounds := SmtTerm.and
          (SmtTerm.geq digit digitMin)
          (SmtTerm.and (SmtTerm.lt digit (SmtTerm.Numeral 10))
            (SmtTerm.Boolean true))
        let validClause := SmtTerm.and recurrence
          (SmtTerm.and digitBounds
            (SmtTerm.and (nonneg (prefixAt nextIdx))
              (SmtTerm.Boolean true)))
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx outputLen))
            (SmtTerm.or validClause (SmtTerm.Boolean false)))
        let forallPart := SmtTerm.not
          (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
        let success := SmtTerm.and
          (SmtTerm.geq outputLen (SmtTerm.Numeral 1))
          (SmtTerm.and (SmtTerm.eq tx (prefixAt outputLen))
            (SmtTerm.and
              (SmtTerm.eq (SmtTerm.Numeral 0)
                (prefixAt (SmtTerm.Numeral 0)))
              (SmtTerm.and forallPart (SmtTerm.Boolean true))))
        let formula := SmtTerm.ite (nonneg (SmtTerm.Numeral 0)) success
          (SmtTerm.eq output (SmtTerm.String []))
        have hOutputTy : __smtx_typeof output =
            SmtType.Seq SmtType.Char := by
          simp [output, tx, typeof_str_from_int_eq, hxTy,
            __smtx_typeof, __smtx_typeof_seq_op_1_ret,
            native_ite, native_Teq]
        have hOutputLenTy : __smtx_typeof outputLen = SmtType.Int := by
          simp [outputLen, typeof_str_len_eq, hOutputTy,
            __smtx_typeof_seq_op_1_ret]
        have hPrefixTy : ∀ k, __smtx_typeof k = SmtType.Int →
            __smtx_typeof (prefixAt k) = SmtType.Int := by
          intro k hk
          simp [prefixAt, tx, typeof_ite_eq, typeof_eq_eq,
            typeof_str_to_int_eq, typeof_str_substr_eq,
            typeof_str_from_int_eq, hxTy, hk, sr_smt_type_wf_int,
            __smtx_typeof_ite, __smtx_typeof_eq,
            __smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_guard_wf, __smtx_typeof_guard,
            __smtx_typeof, native_ite, native_Teq]
        have hValidClauseTy :
            __smtx_typeof validClause = SmtType.Bool := by
          simp [validClause, recurrence, digitBounds, digitMin,
            leadingCond, nonneg, digit, nextIdx, idx, outputLen,
            output, prefixAt, tx, typeof_ite_eq, typeof_and_eq,
            typeof_eq_eq, typeof_geq_eq, typeof_gt_eq, typeof_lt_eq,
            typeof_plus_eq, typeof_mult_eq, typeof_str_len_eq,
            typeof_str_to_code_eq, typeof_str_substr_eq,
            typeof_str_to_int_eq, typeof_str_from_int_eq, hxTy,
            hOutputTy, hOutputLenTy, hPrefixTy, sr_smt_type_wf_int,
            __smtx_typeof_ite, __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_eq, __smtx_typeof_guard_wf,
            __smtx_typeof_guard, __smtx_typeof, native_ite,
            native_Teq]
        have hFormulaEq :
            __eo_to_smt
                (__str_reduction_pred
                  (Term.Apply (Term.UOp UserOp.str_from_int) x)) = formula := by
          simp only [__str_reduction_pred, __eo_mk_apply]
          rfl
        change eo_interprets M
          (__str_reduction_pred
            (Term.Apply (Term.UOp UserOp.str_from_int) x)) true
        apply RuleProofs.eo_interprets_of_bool_eval M _ true
        · unfold RuleProofs.eo_has_bool_type
          rw [hFormulaEq]
          have hEmptyValid : native_string_valid [] = true := by
            native_decide
          simp [formula, success, forallPart, qBody, validClause, digitBounds,
            recurrence, digitMin, leadingCond, nonneg, digit, nextIdx,
            idx, outputLen, output, prefixAt, tx, typeof_ite_eq,
            typeof_and_eq, typeof_or_eq, typeof_not_eq, typeof_eq_eq,
            typeof_geq_eq, typeof_gt_eq, typeof_lt_eq, typeof_plus_eq,
            typeof_mult_eq, typeof_str_len_eq, typeof_str_to_code_eq,
            typeof_str_substr_eq, typeof_str_to_int_eq,
            typeof_str_from_int_eq, smtx_typeof_exists_term_eq,
            hxTy, hOutputTy, hOutputLenTy, hPrefixTy,
            sr_smt_type_wf_int, __smtx_typeof_ite,
            __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_eq, __smtx_typeof_guard_wf,
            __smtx_typeof_guard, __smtx_typeof, native_ite,
            native_Teq, hEmptyValid]
        · rw [hFormulaEq]
          have hXValTy :
              __smtx_typeof_value (__smtx_model_eval M tx) = SmtType.Int := by
            simpa [tx, hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM
                (__eo_to_smt x) hXNN
          rcases int_value_canonical hXValTy with ⟨n, hXEval⟩
          have hXClosed : __eo_is_closed x = Term.Boolean true := by
            apply sr_eo_is_closed_apply_uop_arg UserOp.str_from_int x
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              have hsimpa := hXNN
              try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            · exact hClosed
          let w := native_str_from_int n
          have hValid : native_string_valid w = true := by
            exact native_str_from_int_valid n
          have hAllDigits : w.all impl_native_char_is_digit = true := by
            exact StrInReFromIntDigRangeProof.native_str_from_int_all_digits n
          have hOutputEval :
              __smtx_model_eval M output =
                SmtValue.Seq (native_pack_string w) := by
            simp [output, tx, w, __smtx_model_eval,
              __smtx_model_eval_str_from_int,
              __smtx_model_eval__at_purify, hXEval]
          have hPrefixEval : ∀ (N : SmtModel) (kTerm : SmtTerm) (k : Int),
              __smtx_model_eval N tx = SmtValue.Numeral n →
              __smtx_model_eval N kTerm = SmtValue.Numeral k →
              __smtx_model_eval N (prefixAt kTerm) =
                SmtValue.Numeral (sr_native_stoi_result w k) := by
            intro N kTerm k hTxEval hkEval
            by_cases hk : k = 0 <;>
            simp [prefixAt, tx, w, sr_native_stoi_result, hk,
              __smtx_model_eval, __smtx_model_eval_eq,
              __smtx_model_eval_ite, __smtx_model_eval_str_from_int,
              __smtx_model_eval_str_substr, __smtx_model_eval_str_to_int,
              native_ite, native_veq, hTxEval, hkEval,
              sr_native_seq_extract_pack_string_eval,
              sr_native_unpack_extract_pack_string,
              sr_native_unpack_pack_string]
          by_cases hn : 0 ≤ n
          · have hNonempty := sr_native_str_from_int_ne_nil n hn
            have hNonemptyW : w ≠ [] := by simpa [w] using hNonempty
            have hLenPos : 0 < w.length := by
              apply Nat.pos_of_ne_zero
              intro hLen
              apply hNonemptyW
              exact List.eq_nil_of_length_eq_zero hLen
            have hLenOne : (1 : Int) ≤ Int.ofNat w.length := by
              exact Int.ofNat_le.mpr hLenPos
            have hTotalEq :
                Int.ofNat (impl_native_decimal_digits_to_nat w) = n := by
              have hRound := sr_native_str_to_int_from_int n hn
              have hDecimal := sr_native_str_to_int_of_ne_nil_all
                w hNonempty hAllDigits
              simpa [w, hDecimal] using hRound
            have hPrefixLen :
                sr_native_stoi_result w (Int.ofNat w.length) = n := by
              rw [sr_native_stoi_result_ofNat w w.length (by simp)
                hAllDigits]
              simpa [hTotalEq]
            have hForallEval :
                __smtx_model_eval M forallPart = SmtValue.Boolean true := by
              change __smtx_model_eval M
                (SmtTerm.not
                  (SmtTerm.exists idxName SmtType.Int
                    (SmtTerm.not qBody))) = SmtValue.Boolean true
              have hAll : ∀ v : SmtValue,
                  __smtx_typeof_value v = SmtType.Int →
                  __smtx_value_canonical v = true →
                  __smtx_model_eval
                      (native_model_push M idxName SmtType.Int v) qBody =
                    SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hTxEvalPush :
                    __smtx_model_eval Mk tx = SmtValue.Numeral n := by
                  rw [← hXEval]
                  simpa [tx] using
                    (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                      (model_agrees_on_globals_push M idxName SmtType.Int
                        (SmtValue.Numeral k))).symm
                have hOutputEvalPush :
                    __smtx_model_eval Mk output =
                      SmtValue.Seq (native_pack_string w) := by
                  simp [output, tx, w, __smtx_model_eval,
                    __smtx_model_eval_str_from_int,
                    __smtx_model_eval__at_purify, hTxEvalPush]
                have hOutputLenEvalPush :
                    __smtx_model_eval Mk outputLen =
                      SmtValue.Numeral (Int.ofNat w.length) := by
                  simp [outputLen, __smtx_model_eval,
                    __smtx_model_eval_str_len, hOutputEvalPush,
                    native_seq_len, sr_native_unpack_pack_string_length]
                have hMkTotal : model_wf Mk :=
                  model_total_typed_push hM idxName SmtType.Int
                    (SmtValue.Numeral k) sr_smt_type_wf_int hvTy
                    _hvCanonical
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hklt : k < Int.ofNat w.length
                  · let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      rw [← hCast] at hklt
                      exact Int.ofNat_lt.mp hklt
                    have hNextEval :
                        __smtx_model_eval Mk nextIdx =
                          SmtValue.Numeral (Int.ofNat (j + 1)) := by
                      simp [nextIdx, idx, __smtx_model_eval,
                        __smtx_model_eval_plus, hIdxEval,
                        native_zplus]
                      exact hCast.symm
                    have hIdxTermEval :
                        __smtx_model_eval Mk idx = SmtValue.Numeral k := by
                      simp [idx, __smtx_model_eval, hIdxEval]
                    have hPrefixNext := hPrefixEval Mk nextIdx
                      (Int.ofNat (j + 1)) hTxEvalPush hNextEval
                    have hPrefixIdx := hPrefixEval Mk idx k hTxEvalPush
                      hIdxTermEval
                    have hRec := sr_native_stoi_result_recurrence
                      w j hj hAllDigits
                    rw [hCast] at hRec
                    have hBounds := sr_digit_code_bounds
                      w j hValid hj hAllDigits
                    have hTotal :
                        sr_native_stoi_result w (Int.ofNat (j + 1)) ≤ n := by
                      have hLe := sr_native_stoi_result_le_total w (j + 1)
                        (by omega) hAllDigits
                      rw [hTotalEq] at hLe
                      exact hLe
                    have hCode := sr_str_to_code_at w j hValid hj
                    rw [hCast] at hCode hBounds
                    have hDigitValue := sr_digit_code_value
                      w j hValid hj hAllDigits
                    rw [hCast] at hDigitValue
                    have hLeading :
                        (if k = 0 ∧ 1 < w.length then 1 else 0) ≤
                          native_str_to_code
                            (native_str_substr w k 1) - 48 := by
                      split
                      · rename_i hLead
                        have hj0 : j = 0 := by
                          rw [← hCast] at hLead
                          exact Int.ofNat_eq_zero.mp hLead.1
                        subst j
                        have hkZero : k = (0 : Int) := hLead.1
                        have hCodeZero :
                            native_str_to_code
                                (native_str_substr w 0 1) =
                              Int.ofNat w[0] := by
                          simpa [hkZero] using hCode
                        rw [hkZero, hCodeZero]
                        have hHead :=
                          sr_native_str_from_int_head_pos n hn hLead.2
                        change (1 : Int) ≤ Int.ofNat w[0] - 48 at hHead
                        exact hHead
                      · exact hBounds.1
                    have hDigitEval : __smtx_model_eval Mk digit =
                        SmtValue.Numeral
                          (native_str_to_code (native_str_substr w k 1) -
                            48) := by
                      simp [digit, __smtx_model_eval,
                        __smtx_model_eval__,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_to_code, hOutputEvalPush,
                        hIdxTermEval, sr_native_seq_extract_pack_string_eval,
                        sr_native_unpack_extract_pack_string,
                        sr_native_unpack_pack_string,
                        native_zplus, native_zneg, Int.sub_eq_add_neg]
                    have hRecEval :
                        __smtx_model_eval Mk recurrence =
                          SmtValue.Boolean true := by
                      rw [hDigitValue] at hRec
                      simp [recurrence, __smtx_model_eval,
                        __smtx_model_eval_eq, __smtx_model_eval_plus,
                        __smtx_model_eval_mult, hPrefixNext, hPrefixIdx,
                        hDigitEval, native_zplus, native_zmult, native_veq]
                      simpa using hRec
                    have hDigitMinEval :
                        __smtx_model_eval Mk digitMin =
                          SmtValue.Numeral
                            (if k = 0 ∧ 1 < w.length then 1 else 0) := by
                      have hLeadingCondEval :
                          __smtx_model_eval Mk leadingCond =
                            SmtValue.Boolean
                              (decide (k = 0) &&
                                decide ((1 : Int) < Int.ofNat w.length)) := by
                        simp [leadingCond, __smtx_model_eval,
                          __smtx_model_eval_and, __smtx_model_eval_eq,
                          __smtx_model_eval_gt, __smtx_model_eval_lt,
                          hIdxTermEval,
                          hOutputLenEvalPush, native_and, native_veq,
                          native_zlt]
                      by_cases hkZero : k = 0
                      · by_cases hLong : 1 < w.length
                        · have hLongInt :
                              (1 : Int) < Int.ofNat w.length :=
                            Int.ofNat_lt.mpr hLong
                          have hkDec : decide (k = 0) = true :=
                            decide_eq_true hkZero
                          have hLongDec :
                              decide ((1 : Int) < Int.ofNat w.length) =
                                true := decide_eq_true hLongInt
                          have hCondTrue :
                              (decide (k = 0) &&
                                  decide ((1 : Int) < Int.ofNat w.length)) =
                                true := by
                            rw [hkDec, hLongDec]
                            rfl
                          have hLeadTrue := hLeadingCondEval
                          rw [hCondTrue] at hLeadTrue
                          simp [digitMin, __smtx_model_eval,
                            __smtx_model_eval_ite, hLeadTrue,
                            native_ite, hkZero, hLong, hLongInt]
                        · have hLongInt :
                              ¬ ((1 : Int) < Int.ofNat w.length) := by
                            intro h
                            exact hLong (Int.ofNat_lt.mp h)
                          have hkDec : decide (k = 0) = true :=
                            decide_eq_true hkZero
                          have hLongDec :
                              decide ((1 : Int) < Int.ofNat w.length) =
                                false := decide_eq_false hLongInt
                          have hCondFalse :
                              (decide (k = 0) &&
                                  decide ((1 : Int) < Int.ofNat w.length)) =
                                false := by
                            rw [hkDec, hLongDec]
                            rfl
                          have hLeadFalse := hLeadingCondEval
                          rw [hCondFalse] at hLeadFalse
                          simp [digitMin, __smtx_model_eval,
                            __smtx_model_eval_ite, hLeadFalse,
                            native_ite, hkZero, hLong, hLongInt]
                      · have hCondFalse :
                            (decide (k = 0) &&
                                decide ((1 : Int) < Int.ofNat w.length)) =
                              false := by
                          rw [decide_eq_false hkZero]
                          rfl
                        have hLeadFalse := hLeadingCondEval
                        rw [hCondFalse] at hLeadFalse
                        simp [digitMin, __smtx_model_eval,
                          __smtx_model_eval_ite, hLeadFalse,
                          native_ite, hkZero]
                    have hBoundsEval :
                        __smtx_model_eval Mk digitBounds =
                          SmtValue.Boolean true := by
                      simp [digitBounds, __smtx_model_eval,
                        __smtx_model_eval_geq, __smtx_model_eval_leq,
                        __smtx_model_eval_lt, __smtx_model_eval_and,
                        hDigitEval, hDigitMinEval, native_zleq, native_zlt,
                        native_and, hLeading, hBounds]
                    have hTotalEval :
                        __smtx_model_eval Mk (nonneg (prefixAt nextIdx)) =
                          SmtValue.Boolean true := by
                      simp [nonneg, __smtx_model_eval,
                        __smtx_model_eval_geq, __smtx_model_eval_leq,
                        hTxEvalPush, hPrefixNext, native_zleq, hTotal]
                      exact hTotal
                    have hValidEval :
                        __smtx_model_eval Mk validClause =
                          SmtValue.Boolean true := by
                      simp [validClause, __smtx_model_eval,
                        __smtx_model_eval_and, hRecEval, hBoundsEval,
                        hTotalEval, native_and]
                    simp [qBody, __smtx_model_eval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, hIdxTermEval, hOutputEvalPush,
                      hOutputLenEvalPush, hValidEval,
                      sr_native_unpack_pack_string_length,
                      native_seq_len, native_zlt, native_zleq,
                      native_or, native_not, hk0, hklt]
                  · have hLenLe : Int.ofNat w.length ≤ k :=
                      Int.le_of_not_gt hklt
                    rcases smt_model_eval_bool_is_boolean Mk hMkTotal
                      validClause hValidClauseTy with ⟨b, hValidBool⟩
                    simp [qBody, idx, outputLen, __smtx_model_eval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_lt,
                      __smtx_model_eval_leq,
                      __smtx_model_eval_str_len, hValidBool,
                      hIdxEval, hOutputEvalPush, hOutputLenEvalPush,
                      sr_native_unpack_pack_string_length,
                      native_seq_len, native_zlt, native_zleq,
                      native_or, native_not, hk0, hklt, hLenLe]
                    exact Or.inl hLenLe
                · have hkNeg : k < 0 := Int.lt_of_not_ge hk0
                  rcases smt_model_eval_bool_is_boolean Mk hMkTotal
                    validClause hValidClauseTy with ⟨b, hValidBool⟩
                  simp [qBody, idx, outputLen, __smtx_model_eval,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, __smtx_model_eval_lt,
                    __smtx_model_eval_leq,
                    __smtx_model_eval_str_len, hValidBool,
                    hIdxEval, hOutputEvalPush, hOutputLenEvalPush,
                    sr_native_unpack_pack_string_length, native_seq_len,
                    native_zlt, native_zleq, native_or, native_not,
                    hk0, hkNeg]
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
            have hPrefixLenEval := hPrefixEval M outputLen
              (Int.ofNat w.length) hXEval (by
                simp [outputLen, hOutputEval, __smtx_model_eval,
                  __smtx_model_eval_str_len, native_seq_len,
                  sr_native_unpack_pack_string_length])
            have hPrefixZeroEval := hPrefixEval M (SmtTerm.Numeral 0) 0
              hXEval (by simp [__smtx_model_eval])
            simp [formula, success, nonneg, outputLen, output, tx,
              __smtx_model_eval, __smtx_model_eval_ite,
              __smtx_model_eval_geq, __smtx_model_eval_leq,
              __smtx_model_eval_and,
              __smtx_model_eval_eq, __smtx_model_eval_str_len,
              __smtx_model_eval_str_from_int,
              __smtx_model_eval__at_purify, hXEval, hOutputEval,
              hPrefixLenEval, hPrefixZeroEval, hForallEval,
              sr_native_unpack_pack_string_length, native_seq_len,
              native_zleq, native_and, native_veq, hn, hLenPos,
              hLenOne, hPrefixLen, sr_native_stoi_result]
            constructor
            · simpa [w] using hLenOne
            · simpa [sr_native_stoi_result, hNonemptyW] using hPrefixLen.symm
          · have hnNeg : n < 0 := Int.lt_of_not_ge hn
            have hEmpty : w = [] := by
              simp [w, native_str_from_int, native_string_lit, hnNeg]
            simp [formula, success, nonneg, outputLen, output, tx,
              __smtx_model_eval, __smtx_model_eval_ite,
              __smtx_model_eval_geq, __smtx_model_eval_leq,
              __smtx_model_eval_eq,
              __smtx_model_eval_str_from_int,
              __smtx_model_eval__at_purify, hXEval, hOutputEval,
              native_zleq, native_veq, hn, hnNeg, hEmpty,
              sr_native_unpack_pack_string]
            simpa [w] using congrArg native_pack_string hEmpty
      case str_to_lower =>
        have hOrigNN :
            term_has_non_none_type
              (SmtTerm.str_to_lower (__eo_to_smt x)) := by
          have hsimpa := hTrans
          try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
          exact hsimpa
        have hxTy :
            __smtx_typeof (__eo_to_smt x) =
              SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
            (typeof_str_to_lower_eq (__eo_to_smt x)) hOrigNN
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none SmtType.Char
        have hTWf :
            __smtx_type_wf (SmtType.Seq SmtType.Char) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none
            (__eo_to_smt x) hXNN hxTy
        have hLowerTy :
            __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          rw [typeof_str_to_lower_eq, hxTy]
          simp [native_ite, native_Teq]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy :
            __smtx_typeof_seq_value sx =
              SmtType.Seq SmtType.Char := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        let w := native_unpack_string sx
        have hValid : native_string_valid w = true := by
          exact native_unpack_string_valid_of_typeof_seq_char hSxTy
        have hPack : native_pack_string w = sx :=
          sr_native_pack_unpack_string sx hSxTy
        have hXEvalString :
            __smtx_model_eval M (__eo_to_smt x) =
              SmtValue.Seq (native_pack_string w) := by
          rw [hPack]
          exact hXEval
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          apply sr_eo_is_closed_apply_uop_arg UserOp.str_to_lower x
          · apply RuleProofs.term_ne_stuck_of_has_smt_translation
            have hsimpa := hXNN
            try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
            exact hsimpa
          · exact hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let lowerS :=
          SmtTerm._at_purify (SmtTerm.str_to_lower (__eo_to_smt x))
        let lowerLen := SmtTerm.str_len lowerS
        let origCode := SmtTerm.str_to_code
          (SmtTerm.str_substr (__eo_to_smt x) idx (SmtTerm.Numeral 1))
        let lowerCode := SmtTerm.str_to_code
          (SmtTerm.str_substr lowerS idx (SmtTerm.Numeral 1))
        let isUpper := SmtTerm.and
          (SmtTerm.leq (SmtTerm.Numeral 65) origCode)
          (SmtTerm.and (SmtTerm.leq origCode (SmtTerm.Numeral 90))
            (SmtTerm.Boolean true))
        let expected := SmtTerm.ite isUpper
          (SmtTerm.plus origCode
            (SmtTerm.plus (SmtTerm.Numeral 32) (SmtTerm.Numeral 0)))
          origCode
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx lowerLen))
            (SmtTerm.or (SmtTerm.eq lowerCode expected)
              (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len lowerS)) = SmtType.Bool
            simp [lowerS, typeof_eq_eq, typeof_str_len_eq, hxTy,
              hLowerTy, __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof,
              native_ite, native_Teq]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len lowerS)) = SmtValue.Boolean true
            simp [lowerS, __smtx_model_eval, hXEvalString,
              __smtx_model_eval_str_len, __smtx_model_eval_str_to_lower,
              __smtx_model_eval__at_purify, __smtx_model_eval_eq,
              native_seq_len, native_str_to_lower,
              Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
              sr_native_unpack_pack_string_length, List.length_map,
              native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtType.Bool
              simp [qBody, expected, isUpper, lowerCode, origCode,
                lowerLen, lowerS, idx, smtx_typeof_exists_term_eq,
                typeof_or_eq, typeof_not_eq, typeof_geq_eq, typeof_lt_eq,
                typeof_eq_eq, typeof_str_len_eq, typeof_str_substr_eq,
                typeof_str_to_code_eq, typeof_leq_eq, typeof_and_eq,
                typeof_ite_eq, typeof_plus_eq, hxTy, hLowerTy,
                __smtx_typeof, __smtx_typeof_seq_op_1,
                __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_eq, __smtx_typeof_guard_wf,
                __smtx_typeof_guard, __smtx_typeof_ite, hTWf,
                sr_smt_type_wf_int,
                native_ite, native_Teq]
            · change __smtx_model_eval M
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq (native_pack_string w) := by
                  rw [← hXEvalString]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hklt : k < Int.ofNat w.length
                  · let j := Int.toNat k
                    have hNotLenLe : ¬ Int.ofNat w.length ≤ k :=
                      Int.not_le_of_gt hklt
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hCode := sr_lower_code_at w j hValid hj
                    rw [hCast] at hCode
                    simp [qBody, expected, isUpper, lowerCode, origCode,
                      lowerLen, lowerS, idx, __smtx_model_eval,
                      hXEvalPush, hIdxEval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, __smtx_model_eval_eq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_lower,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code,
                      __smtx_model_eval__at_purify,
                      __smtx_model_eval_and, __smtx_model_eval_ite,
                      __smtx_model_eval_plus, native_seq_len,
                      native_str_to_lower, native_zleq, native_zlt,
                      native_zplus, native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hCode, hk0, hklt,
                      hNotLenLe]
                    right
                    rw [show List.map impl_native_char_to_lower w =
                      native_str_to_lower w by rfl]
                    let c := native_str_to_code (native_str_substr w k 1)
                    by_cases hLo : 65 ≤ c
                    · by_cases hHi : c ≤ 90
                      · simpa [c, native_veq, hLo, hHi] using hCode
                      · simpa [c, native_veq, hLo, hHi] using hCode
                    · simpa [c, native_veq, hLo] using hCode
                  · have hLenLe : Int.ofNat w.length ≤ k :=
                      Int.le_of_not_gt hklt
                    simp [qBody, expected, isUpper, lowerCode, origCode,
                      lowerLen, lowerS, idx,
                      __smtx_model_eval, hXEvalPush,
                      hIdxEval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, __smtx_model_eval_eq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_lower,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code,
                      __smtx_model_eval__at_purify,
                      __smtx_model_eval_and, __smtx_model_eval_ite,
                      __smtx_model_eval_plus, native_seq_len,
                      native_str_to_lower, native_zleq, native_zlt,
                      native_zplus, native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hk0, hklt, hLenLe]
                    left
                    simpa using hLenLe
                · have hkNeg : k < 0 := Int.lt_of_not_ge hk0
                  simp [qBody, expected, isUpper, lowerCode, origCode,
                    lowerLen, lowerS, idx, __smtx_model_eval,
                    hXEvalPush, hIdxEval,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, __smtx_model_eval_leq,
                    __smtx_model_eval_lt, __smtx_model_eval_eq,
                    __smtx_model_eval_str_len,
                    __smtx_model_eval_str_to_lower,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_to_code,
                    __smtx_model_eval__at_purify,
                    __smtx_model_eval_and, __smtx_model_eval_ite,
                    __smtx_model_eval_plus, native_seq_len,
                    native_str_to_lower, native_zleq, native_zlt,
                    native_zplus, native_and, native_or, native_not,
                    Smtm.native_unpack_pack_seq,
                    sr_native_unpack_pack_string,
                    sr_native_unpack_pack_string_length, List.length_map,
                    sr_native_seq_extract_pack_string,
                    sr_native_unpack_extract_pack_string,
                    hk0, hkNeg]
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
          · exact RuleProofs.eo_interprets_true M
      case str_to_upper =>
        have hOrigNN :
            term_has_non_none_type
              (SmtTerm.str_to_upper (__eo_to_smt x)) := by
          have hsimpa := hTrans
          try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
          exact hsimpa
        have hxTy :
            __smtx_typeof (__eo_to_smt x) =
              SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
            (typeof_str_to_upper_eq (__eo_to_smt x)) hOrigNN
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none SmtType.Char
        have hTWf :
            __smtx_type_wf (SmtType.Seq SmtType.Char) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none
            (__eo_to_smt x) hXNN hxTy
        have hUpperTy :
            __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          rw [typeof_str_to_upper_eq, hxTy]
          simp [native_ite, native_Teq]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy :
            __smtx_typeof_seq_value sx =
              SmtType.Seq SmtType.Char := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        let w := native_unpack_string sx
        have hValid : native_string_valid w = true := by
          exact native_unpack_string_valid_of_typeof_seq_char hSxTy
        have hPack : native_pack_string w = sx :=
          sr_native_pack_unpack_string sx hSxTy
        have hXEvalString :
            __smtx_model_eval M (__eo_to_smt x) =
              SmtValue.Seq (native_pack_string w) := by
          rw [hPack]
          exact hXEval
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          apply sr_eo_is_closed_apply_uop_arg UserOp.str_to_upper x
          · apply RuleProofs.term_ne_stuck_of_has_smt_translation
            have hsimpa := hXNN
            try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
            exact hsimpa
          · exact hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let upperS :=
          SmtTerm._at_purify (SmtTerm.str_to_upper (__eo_to_smt x))
        let upperLen := SmtTerm.str_len upperS
        let origCode := SmtTerm.str_to_code
          (SmtTerm.str_substr (__eo_to_smt x) idx (SmtTerm.Numeral 1))
        let upperCode := SmtTerm.str_to_code
          (SmtTerm.str_substr upperS idx (SmtTerm.Numeral 1))
        let isLower := SmtTerm.and
          (SmtTerm.leq (SmtTerm.Numeral 97) origCode)
          (SmtTerm.and (SmtTerm.leq origCode (SmtTerm.Numeral 122))
            (SmtTerm.Boolean true))
        let expected := SmtTerm.ite isLower
          (SmtTerm.plus origCode
            (SmtTerm.plus (SmtTerm.Numeral (-32)) (SmtTerm.Numeral 0)))
          origCode
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx upperLen))
            (SmtTerm.or (SmtTerm.eq upperCode expected)
              (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len upperS)) = SmtType.Bool
            simp [upperS, typeof_eq_eq, typeof_str_len_eq, hxTy,
              hUpperTy, __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof,
              native_ite, native_Teq]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len upperS)) = SmtValue.Boolean true
            simp [upperS, __smtx_model_eval, hXEvalString,
              __smtx_model_eval_str_len, __smtx_model_eval_str_to_upper,
              __smtx_model_eval__at_purify, __smtx_model_eval_eq,
              native_seq_len, native_str_to_upper,
              Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
              sr_native_unpack_pack_string_length, List.length_map,
              native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtType.Bool
              simp [qBody, expected, isLower, upperCode, origCode,
                upperLen, upperS, idx, smtx_typeof_exists_term_eq,
                typeof_or_eq, typeof_not_eq, typeof_geq_eq, typeof_lt_eq,
                typeof_eq_eq, typeof_str_len_eq, typeof_str_substr_eq,
                typeof_str_to_code_eq, typeof_leq_eq, typeof_and_eq,
                typeof_ite_eq, typeof_plus_eq, hxTy, hUpperTy,
                __smtx_typeof, __smtx_typeof_seq_op_1,
                __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_eq, __smtx_typeof_guard_wf,
                __smtx_typeof_guard, __smtx_typeof_ite, hTWf,
                sr_smt_type_wf_int,
                native_ite, native_Teq]
            · change __smtx_model_eval M
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq (native_pack_string w) := by
                  rw [← hXEvalString]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hklt : k < Int.ofNat w.length
                  · let j := Int.toNat k
                    have hNotLenLe : ¬ Int.ofNat w.length ≤ k :=
                      Int.not_le_of_gt hklt
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hCode := sr_upper_code_at w j hValid hj
                    rw [hCast] at hCode
                    simp [qBody, expected, isLower, upperCode, origCode,
                      upperLen, upperS, idx, __smtx_model_eval,
                      hXEvalPush, hIdxEval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, __smtx_model_eval_eq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_upper,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code,
                      __smtx_model_eval__at_purify,
                      __smtx_model_eval_and, __smtx_model_eval_ite,
                      __smtx_model_eval_plus, native_seq_len,
                      native_str_to_upper, native_zleq, native_zlt,
                      native_zplus, native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hCode, hk0, hklt,
                      hNotLenLe]
                    right
                    rw [show List.map impl_native_char_to_upper w =
                      native_str_to_upper w by rfl]
                    let c := native_str_to_code (native_str_substr w k 1)
                    by_cases hLo : 97 ≤ c
                    · by_cases hHi : c ≤ 122
                      · simpa [c, native_veq, hLo, hHi] using hCode
                      · simpa [c, native_veq, hLo, hHi] using hCode
                    · simpa [c, native_veq, hLo] using hCode
                  · have hLenLe : Int.ofNat w.length ≤ k :=
                      Int.le_of_not_gt hklt
                    simp [qBody, expected, isLower, upperCode, origCode,
                      upperLen, upperS, idx,
                      __smtx_model_eval, hXEvalPush,
                      hIdxEval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, __smtx_model_eval_eq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_upper,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code,
                      __smtx_model_eval__at_purify,
                      __smtx_model_eval_and, __smtx_model_eval_ite,
                      __smtx_model_eval_plus, native_seq_len,
                      native_str_to_upper, native_zleq, native_zlt,
                      native_zplus, native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hk0, hklt, hLenLe]
                    left
                    simpa using hLenLe
                · have hkNeg : k < 0 := Int.lt_of_not_ge hk0
                  simp [qBody, expected, isLower, upperCode, origCode,
                    upperLen, upperS, idx, __smtx_model_eval,
                    hXEvalPush, hIdxEval,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, __smtx_model_eval_leq,
                    __smtx_model_eval_lt, __smtx_model_eval_eq,
                    __smtx_model_eval_str_len,
                    __smtx_model_eval_str_to_upper,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_to_code,
                    __smtx_model_eval__at_purify,
                    __smtx_model_eval_and, __smtx_model_eval_ite,
                    __smtx_model_eval_plus, native_seq_len,
                    native_str_to_upper, native_zleq, native_zlt,
                    native_zplus, native_and, native_or, native_not,
                    Smtm.native_unpack_pack_seq,
                    sr_native_unpack_pack_string,
                    sr_native_unpack_pack_string_length, List.length_map,
                    sr_native_seq_extract_pack_string,
                    sr_native_unpack_extract_pack_string,
                    hk0, hkNeg]
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
          · exact RuleProofs.eo_interprets_true M
      case str_rev =>
        have hOrigNN :
            term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) := by
          have hsimpa := hTrans
          try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
          exact hsimpa
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
            (typeof_str_rev_eq (__eo_to_smt x)) hOrigNN with ⟨T, hxTy⟩
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none T
        have hTWf : __smtx_type_wf (SmtType.Seq T) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt x) hXNN hxTy
        have hRevTy :
            __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) =
              SmtType.Seq T := by
          rw [typeof_str_rev_eq, hxTy]
          simp [__smtx_typeof_seq_op_1, __smtx_typeof_guard_wf, hTWf,
            native_ite]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq T := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        have hElemTy : __smtx_elem_typeof_seq_value sx = T :=
          elem_typeof_seq_value_of_typeof_seq_value hSxTy
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          apply sr_eo_is_closed_apply_uop_arg UserOp.str_rev x
          · apply RuleProofs.term_ne_stuck_of_has_smt_translation
            have hsimpa := hXNN
            try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
            exact hsimpa
          · exact hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let revS := SmtTerm._at_purify (SmtTerm.str_rev (__eo_to_smt x))
        let revLen := SmtTerm.str_len revS
        let mirrorStart := SmtTerm.neg (SmtTerm.str_len (__eo_to_smt x))
          (SmtTerm.plus idx
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)))
        let sliceEq := SmtTerm.eq
          (SmtTerm.str_substr revS idx (SmtTerm.Numeral 1))
          (SmtTerm.str_substr (__eo_to_smt x) mirrorStart
            (SmtTerm.Numeral 1))
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx revLen))
            (SmtTerm.or sliceEq (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len
                    (SmtTerm._at_purify
                      (SmtTerm.str_rev (__eo_to_smt x))))) = SmtType.Bool
            simp [typeof_eq_eq, typeof_str_len_eq, hxTy, hRevTy,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq, native_ite,
              native_Teq, __smtx_typeof, __smtx_typeof_seq_op_1,
              __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len
                    (SmtTerm._at_purify
                      (SmtTerm.str_rev (__eo_to_smt x))))) =
                SmtValue.Boolean true
            simp [__smtx_model_eval, hXEval, __smtx_model_eval_str_len,
              __smtx_model_eval_str_rev, __smtx_model_eval__at_purify,
              __smtx_model_eval_eq, native_seq_len, native_seq_rev,
              Smtm.native_unpack_pack_seq, native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtType.Bool
              simp [qBody, sliceEq, mirrorStart, revLen, revS, idx,
                smtx_typeof_exists_term_eq, typeof_or_eq, typeof_not_eq,
                typeof_geq_eq, typeof_lt_eq, typeof_eq_eq,
                typeof_str_len_eq, typeof_str_substr_eq, typeof_neg_eq,
                typeof_plus_eq, hxTy, hRevTy, __smtx_typeof,
                __smtx_typeof_seq_op_1, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf,
                sr_smt_type_wf_int,
                native_ite, native_Teq]
            · change __smtx_model_eval M
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                simp [qBody, sliceEq, mirrorStart, revLen, revS, idx,
                  __smtx_model_eval, hXEvalPush, hIdxEval,
                  __smtx_model_eval_or,
                  __smtx_model_eval_not, __smtx_model_eval_geq,
                  __smtx_model_eval_leq, __smtx_model_eval_lt,
                  __smtx_model_eval_eq, __smtx_model_eval_str_len,
                  __smtx_model_eval_str_rev, __smtx_model_eval_str_substr,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, native_seq_len, native_seq_rev,
                  native_zleq, native_zlt, native_zplus, native_zneg,
                  native_and, native_or, native_not,
                  Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  hElemTy, native_veq]
                by_cases hk0 : 0 ≤ k
                · by_cases hklt :
                      k < Int.ofNat (native_unpack_seq sx).length
                  · right
                    right
                    let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      have hsimpa := Int.toNat_of_nonneg hk0
                      try simp only [j] at hsimpa ⊢
                      exact hsimpa
                    have hj : j < (native_unpack_seq sx).length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hjSuccLe :
                        j + 1 ≤ (native_unpack_seq sx).length := by omega
                    have hMirrorCast :
                        Int.ofNat ((native_unpack_seq sx).length - (j + 1)) =
                          Int.ofNat (native_unpack_seq sx).length + -(k + 1) := by
                      calc
                        Int.ofNat ((native_unpack_seq sx).length - (j + 1)) =
                            Int.ofNat (native_unpack_seq sx).length -
                              Int.ofNat (j + 1) :=
                          Int.ofNat_sub hjSuccLe
                        _ = Int.ofNat (native_unpack_seq sx).length +
                              -(k + 1) := by
                          have hSuccCast :
                              Int.ofNat (j + 1) = Int.ofNat j + 1 := by
                            cases j <;> rfl
                          rw [hSuccCast, hCast, Int.sub_eq_add_neg]
                    apply congrArg (native_pack_seq T)
                    calc
                      native_seq_extract (native_unpack_seq sx).reverse k 1 =
                          native_seq_extract (native_unpack_seq sx).reverse
                            (Int.ofNat j) 1 := by rw [hCast]
                      _ = native_seq_extract (native_unpack_seq sx)
                            (Int.ofNat ((native_unpack_seq sx).length -
                              (j + 1))) 1 :=
                        sr_native_seq_extract_reverse_one
                          (native_unpack_seq sx) j hj
                      _ = native_seq_extract (native_unpack_seq sx)
                            (Int.ofNat (native_unpack_seq sx).length +
                              -(k + 1)) 1 := by rw [hMirrorCast]
                  · right
                    left
                    exact Int.le_of_not_gt hklt
                · left
                  exact Int.lt_of_not_ge hk0
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
          · exact RuleProofs.eo_interprets_true M
    case Apply g y =>
      cases g <;> try
        simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
      all_goals try
        (change Term.Stuck = Term.Bool at hBodyTy
         exact False.elim (Term.noConfusion hBodyTy))
      case UOp op =>
        cases op <;> try
          simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
        all_goals try
          (change Term.Stuck = Term.Bool at hBodyTy
           exact False.elim (Term.noConfusion hBodyTy))
        case str_contains =>
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          have hOrigNN :
              term_has_non_none_type (SmtTerm.str_contains ty tx) := by
            have hsimpa := hTrans
            try simp [ty, tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
            exact hsimpa
          rcases seq_binop_args_of_non_none_ret
              (op := SmtTerm.str_contains)
              (typeof_str_contains_eq ty tx) hOrigNN with
            ⟨T, hyTy, hxTy⟩
          have hYNN : term_has_non_none_type ty := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none T
          have hXNN : term_has_non_none_type tx := by
            unfold term_has_non_none_type
            rw [hxTy]
            exact seq_ne_none T
          have hContainsTy :
              __smtx_typeof (SmtTerm.str_contains ty tx) = SmtType.Bool := by
            rw [typeof_str_contains_eq, hyTy, hxTy]
            simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
          have hYValTy :
              __smtx_typeof_value (__smtx_model_eval M ty) =
                SmtType.Seq T := by
            simpa [hyTy] using
              smt_model_eval_preserves_type_of_non_none M hM ty hYNN
          have hXValTy :
              __smtx_typeof_value (__smtx_model_eval M tx) =
                SmtType.Seq T := by
            simpa [hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM tx hXNN
          rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
          rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
          have hSyTy :
              __smtx_typeof_seq_value sy =
                SmtType.Seq T := by
            simpa [hYEval, __smtx_typeof_value] using hYValTy
          have hSxTy :
              __smtx_typeof_seq_value sx =
                SmtType.Seq T := by
            simpa [hXEval, __smtx_typeof_value] using hXValTy
          have hSyElem :
              __smtx_elem_typeof_seq_value sy = T :=
            elem_typeof_seq_value_of_typeof_seq_value hSyTy
          have hSxElem :
              __smtx_elem_typeof_seq_value sx = T :=
            elem_typeof_seq_value_of_typeof_seq_value hSxTy
          let ys := native_unpack_seq sy
          let xs := native_unpack_seq sx
          have hPackXAtY :
              native_pack_seq (__smtx_elem_typeof_seq_value sy) xs = sx := by
            rw [hSyElem, ← hSxElem]
            simpa [xs] using native_pack_unpack_seq sx
          have hClosedArgs :
              __eo_is_closed y = Term.Boolean true ∧
                __eo_is_closed x = Term.Boolean true := by
            apply sr_eo_is_closed_binary_uop_args UserOp.str_contains y x
            · decide
            · decide
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              have hsimpa := hYNN
              try simp [ty, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              have hsimpa := hXNN
              try simp [tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            · exact hClosed
          let idxName := native_string_lit "@var.str_index"
          let idx := SmtTerm.Var idxName SmtType.Int
          let needleLen := SmtTerm.str_len tx
          let limit := SmtTerm.neg (SmtTerm.str_len ty) needleLen
          let slice := SmtTerm.str_substr ty idx needleLen
          let qBody := SmtTerm.or
            (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
            (SmtTerm.or (SmtTerm.not (SmtTerm.leq idx limit))
              (SmtTerm.or (SmtTerm.not (SmtTerm.eq slice tx))
                (SmtTerm.Boolean false)))
          let forallEncoding :=
            SmtTerm.not
              (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
          let containsResult :=
            SmtTerm._at_purify (SmtTerm.str_contains ty tx)
          let formula := SmtTerm.eq containsResult
            (SmtTerm.not forallEncoding)
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof formula = SmtType.Bool
            simp [formula, containsResult, forallEncoding, qBody, slice,
              limit, needleLen, idx, typeof_eq_eq, typeof_not_eq,
              smtx_typeof_exists_term_eq, typeof_or_eq, typeof_geq_eq,
              typeof_leq_eq, typeof_str_substr_eq, typeof_str_len_eq,
              typeof_neg_eq, hyTy, hxTy, hContainsTy,
              __smtx_typeof, __smtx_typeof_str_substr,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2_ret,
              __smtx_typeof_arith_overload_op_2,
              __smtx_typeof_arith_overload_op_2_ret,
              __smtx_typeof_eq, __smtx_typeof_guard_wf,
              __smtx_typeof_guard, sr_smt_type_wf_int,
              native_ite, native_Teq]
          · change __smtx_model_eval M formula = SmtValue.Boolean true
            have hContainsEval :
                __smtx_model_eval M containsResult =
                  SmtValue.Boolean (native_seq_contains ys xs) := by
              simp [containsResult, ty, tx, ys, xs, __smtx_model_eval,
                hYEval, hXEval, __smtx_model_eval__at_purify,
                __smtx_model_eval_str_contains]
            by_cases hContains : native_seq_contains ys xs = true
            · rcases (sr_native_seq_contains_iff_extract ys xs).1 hContains with
                ⟨j, hBound, hExtract⟩
              have hForallFalse :
                  __smtx_model_eval M forallEncoding =
                    SmtValue.Boolean false := by
                let Mj := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral (Int.ofNat j))
                have hIdxEval :
                    native_model_var_lookup Mj idxName SmtType.Int =
                      SmtValue.Numeral (Int.ofNat j) := by
                  simp [Mj, native_model_var_lookup, native_model_push]
                have hYEvalPush :
                    __smtx_model_eval Mj ty = SmtValue.Seq sy := by
                  rw [← hYEval]
                  exact (smt_model_eval_eq_of_eo_closed y hClosedArgs.1 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hXEvalPush :
                    __smtx_model_eval Mj tx = SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hClosedArgs.2 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hPatLe : xs.length ≤ ys.length := by
                  rcases
                      (StrContainsReplCharSupport.native_seq_contains_iff_decomp
                        ys xs).1 hContains with
                    ⟨before, after, hYs⟩
                  rw [hYs]
                  simp
                  omega
                have hLimitCast :
                    Int.ofNat ys.length - Int.ofNat xs.length =
                      Int.ofNat (ys.length - xs.length) :=
                  (Int.ofNat_sub hPatLe).symm
                have hIdxLe :
                    Int.ofNat j ≤
                      Int.ofNat ys.length - Int.ofNat xs.length := by
                  rw [hLimitCast]
                  exact Int.ofNat_le.mpr hBound
                have hIdxLeCast :
                    (j : Int) ≤
                      (ys.length : Int) + -(xs.length : Int) := by
                  rw [sr_int_natCast_eq_ofNat j,
                    sr_int_natCast_eq_ofNat ys.length,
                    sr_int_natCast_eq_ofNat xs.length,
                    ← Int.sub_eq_add_neg]
                  exact hIdxLe
                have hSliceEqEval :
                    __smtx_model_eval Mj (SmtTerm.eq slice tx) =
                      SmtValue.Boolean true := by
                  simp [slice, needleLen, idx, ys, xs, __smtx_model_eval,
                    hYEvalPush, hXEvalPush, hIdxEval,
                    __smtx_model_eval_eq, __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_len, native_seq_len,
                    hExtract, hPackXAtY, native_veq]
                  rw [sr_int_natCast_eq_ofNat j,
                    sr_int_natCast_eq_ofNat xs.length, hExtract, hPackXAtY]
                have hSliceEqEval' :
                    __smtx_model_eval_eq (__smtx_model_eval Mj slice)
                        (SmtValue.Seq sx) = SmtValue.Boolean true := by
                  simpa [__smtx_model_eval, hXEvalPush] using hSliceEqEval
                have hAtFalse :
                    __smtx_model_eval Mj qBody =
                      SmtValue.Boolean false := by
                  simp [qBody, limit, needleLen, idx, ys, xs,
                    __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                    hSliceEqEval', __smtx_model_eval_or,
                    __smtx_model_eval_not, __smtx_model_eval_geq,
                    __smtx_model_eval_leq, __smtx_model_eval_str_len,
                    __smtx_model_eval__, native_seq_len, native_zleq,
                    native_zplus, native_zneg, native_and, native_or,
                    native_not, hIdxLe, hIdxLeCast]
                exact sr_eval_forall_encoding_false M idxName SmtType.Int
                  qBody (SmtValue.Numeral (Int.ofNat j)) rfl
                  (by simp [__smtx_value_canonical]) hAtFalse
              simp [formula, __smtx_model_eval, hContainsEval, hContains,
                hForallFalse, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not]
            · have hContainsFalse : native_seq_contains ys xs = false := by
                cases h : native_seq_contains ys xs
                · rfl
                · exact False.elim (hContains h)
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hYEvalPush :
                    __smtx_model_eval Mk ty = SmtValue.Seq sy := by
                  rw [← hYEval]
                  exact (smt_model_eval_eq_of_eo_closed y hClosedArgs.1 M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                have hXEvalPush :
                    __smtx_model_eval Mk tx = SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hClosedArgs.2 M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hkLe :
                      k ≤ Int.ofNat ys.length - Int.ofNat xs.length
                  · let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hPatLe : xs.length ≤ ys.length := by
                      apply Nat.le_of_not_gt
                      intro hNotLe
                      have hNeg :
                          Int.ofNat ys.length - Int.ofNat xs.length < 0 := by
                        rw [← sr_int_natCast_eq_ofNat ys.length,
                          ← sr_int_natCast_eq_ofNat xs.length]
                        omega
                      exact Int.not_lt_of_ge hk0
                        (Int.lt_of_le_of_lt hkLe hNeg)
                    have hLimitCast :
                        Int.ofNat ys.length - Int.ofNat xs.length =
                          Int.ofNat (ys.length - xs.length) :=
                      (Int.ofNat_sub hPatLe).symm
                    have hBound : j ≤ ys.length - xs.length := by
                      apply Nat.le_of_not_gt
                      intro hNotLe
                      have hLt :
                          Int.ofNat (ys.length - xs.length) <
                            Int.ofNat j := Int.ofNat_lt.mpr hNotLe
                      rw [hCast, ← hLimitCast] at hLt
                      exact Int.not_lt_of_ge hkLe hLt
                    have hkLeCast :
                        k ≤ (ys.length : Int) + -(xs.length : Int) := by
                      rw [sr_int_natCast_eq_ofNat ys.length,
                        sr_int_natCast_eq_ofNat xs.length,
                        ← Int.sub_eq_add_neg]
                      exact hkLe
                    have hExtractNe :
                        native_seq_extract ys (Int.ofNat j)
                            (Int.ofNat xs.length) ≠ xs := by
                      intro hEq
                      have hTrue :=
                        (sr_native_seq_contains_iff_extract ys xs).2
                          ⟨j, hBound, hEq⟩
                      rw [hTrue] at hContainsFalse
                      contradiction
                    have hSliceEqEval :
                        __smtx_model_eval Mk (SmtTerm.eq slice tx) =
                          SmtValue.Boolean false := by
                      simp [slice, needleLen, idx, ys, xs,
                        __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                        __smtx_model_eval_eq, __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_len, native_seq_len,
                        ← hCast, hExtractNe, hPackXAtY, native_veq]
                      rw [sr_int_natCast_eq_ofNat j,
                        sr_int_natCast_eq_ofNat xs.length]
                      intro hEq
                      apply hExtractNe
                      have hUnpack := congrArg native_unpack_seq hEq
                      simpa [xs, Smtm.native_unpack_pack_seq] using hUnpack
                    have hSliceEqEval' :
                        __smtx_model_eval_eq (__smtx_model_eval Mk slice)
                            (SmtValue.Seq sx) = SmtValue.Boolean false := by
                      simpa [__smtx_model_eval, hXEvalPush] using hSliceEqEval
                    simp [qBody, limit, needleLen, idx, ys, xs,
                      __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                      hSliceEqEval', __smtx_model_eval_or,
                      __smtx_model_eval_not, __smtx_model_eval_geq,
                      __smtx_model_eval_leq, __smtx_model_eval_str_len,
                      __smtx_model_eval__, native_seq_len, native_zleq,
                      native_zplus, native_zneg, native_and, native_or,
                      native_not, hk0, hkLe, hkLeCast]
                  · simp [qBody, limit, needleLen, idx, ys, xs,
                      __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_eq, __smtx_model_eval_str_len,
                      __smtx_model_eval_str_substr, __smtx_model_eval__,
                      native_seq_len, native_zleq, native_zplus,
                      native_zneg, native_and, native_or, native_not,
                      hk0, hkLe]
                    left
                    rw [sr_int_natCast_eq_ofNat ys.length,
                      sr_int_natCast_eq_ofNat xs.length]
                    simpa [Int.sub_eq_add_neg] using Int.lt_of_not_ge hkLe
                · simp [qBody, limit, needleLen, idx, ys, xs,
                  __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                  __smtx_model_eval_or, __smtx_model_eval_not,
                  __smtx_model_eval_geq, __smtx_model_eval_leq,
                  __smtx_model_eval_eq, __smtx_model_eval_str_len,
                  __smtx_model_eval_str_substr, __smtx_model_eval__,
                  native_seq_len, native_zleq, native_zplus, native_zneg,
                  native_and, native_or, native_not, hk0]
              have hForallTrue :
                  __smtx_model_eval M forallEncoding =
                    SmtValue.Boolean true :=
                sr_eval_forall_encoding_true M idxName SmtType.Int qBody hAll
              simp [formula, __smtx_model_eval, hContainsEval,
                hContainsFalse, hForallTrue, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not]
        case seq_nth =>
          have hOrigNN :
              term_has_non_none_type
                (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
            have hsimpa := hTrans
            try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
            exact hsimpa
          rcases seq_nth_args_of_non_none hOrigNN with ⟨T, hyTy, hxTy⟩
          let pre := srPurify
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) y)
                (Term.Numeral 0)) x)
          have hPreTy :
              __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
            change __smtx_typeof
                (SmtTerm._at_purify
                  (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                    (__eo_to_smt x))) = SmtType.Seq T
            simp [__smtx_typeof, typeof_str_substr_eq, hyTy, hxTy,
              __smtx_typeof_str_substr, native_ite, native_Teq]
          have hNilNe :
              __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                Term.Stuck :=
            nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreTy
          have hNilNe' :
              __eo_nil (Term.UOp UserOp.str_concat)
                  (__eo_typeof
                    (srPurify
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_substr) y)
                          (Term.Numeral 0)) x))) ≠
                Term.Stuck := by
            simpa [pre] using hNilNe
          simp only [hNilNe', __eo_mk_apply] at hBodyTy ⊢
          have hTWf : __smtx_type_wf T = true :=
            (smt_seq_component_wf_of_non_none_type (__eo_to_smt y) T hyTy).2
          have hYNN : term_has_non_none_type (__eo_to_smt y) := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none T
          have hSeqTWf : __smtx_type_wf (SmtType.Seq T) = true :=
            Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt y) hYNN hyTy
          have hNthTy :
              __smtx_typeof
                  (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) = T := by
            rw [typeof_seq_nth_eq, hyTy, hxTy]
            simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hTWf,
              native_ite]
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let len := SmtTerm.str_len ty
          let next := SmtTerm.plus tx
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
          let remaining := SmtTerm.neg len next
          let preS := SmtTerm._at_purify
            (SmtTerm.str_substr ty (SmtTerm.Numeral 0) tx)
          let nthS := SmtTerm._at_purify (SmtTerm.seq_nth ty tx)
          let suffixS := SmtTerm._at_purify
            (SmtTerm.str_substr ty next remaining)
          let nilS := __eo_to_smt
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
          let decomposition := SmtTerm.str_concat preS
            (SmtTerm.str_concat (SmtTerm.seq_unit nthS)
              (SmtTerm.str_concat suffixS nilS))
          let cond := SmtTerm.and (SmtTerm.geq tx (SmtTerm.Numeral 0))
            (SmtTerm.and (SmtTerm.gt len tx) (SmtTerm.Boolean true))
          let rhs := SmtTerm.and (SmtTerm.eq ty decomposition)
            (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) tx)
              (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len suffixS) remaining)
                (SmtTerm.Boolean true)))
          have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
            simpa [nilS, pre] using
              smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
          have hLenTy : __smtx_typeof len = SmtType.Int := by
            simp [len, ty, typeof_str_len_eq, hyTy,
              __smtx_typeof_seq_op_1_ret]
          have hNextTy : __smtx_typeof next = SmtType.Int := by
            simp [next, tx, hxTy, typeof_plus_eq,
              __smtx_typeof_arith_overload_op_2, __smtx_typeof]
          have hRemainingTy : __smtx_typeof remaining = SmtType.Int := by
            simp [remaining, hLenTy, hNextTy, typeof_neg_eq,
              __smtx_typeof_arith_overload_op_2]
          have hPreSTy : __smtx_typeof preS = SmtType.Seq T := by
            have hsimpa := hPreTy
            try simp [preS, ty, tx, pre] at hsimpa ⊢
            exact hsimpa
          have hNthSTy : __smtx_typeof nthS = T := by
            simpa [nthS, ty, tx, __smtx_typeof] using hNthTy
          have hSuffixTy : __smtx_typeof suffixS = SmtType.Seq T := by
            change __smtx_typeof (SmtTerm.str_substr ty next remaining) =
              SmtType.Seq T
            simp [typeof_str_substr_eq, ty, hNextTy, hRemainingTy, hyTy,
              __smtx_typeof_str_substr]
          have hUnitTy :
              __smtx_typeof (SmtTerm.seq_unit nthS) = SmtType.Seq T := by
            rw [smtx_typeof_seq_unit_term_eq, hNthSTy]
            simp [__smtx_typeof_guard_wf, hSeqTWf, native_ite]
          have hDecompositionTy :
              __smtx_typeof decomposition = SmtType.Seq T := by
            simp [decomposition, typeof_str_concat_eq, hPreSTy, hUnitTy,
              hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
              native_Teq]
          have hCondTy : __smtx_typeof cond = SmtType.Bool := by
            simp [cond, typeof_and_eq, typeof_geq_eq, typeof_gt_eq, hLenTy,
              tx, hxTy, __smtx_typeof_arith_overload_op_2_ret,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          have hRhsTy : __smtx_typeof rhs = SmtType.Bool := by
            simp [rhs, typeof_and_eq, typeof_eq_eq, typeof_str_len_eq, ty,
              tx, hyTy, hxTy, hDecompositionTy, hPreSTy, hSuffixTy,
              hRemainingTy, __smtx_typeof_seq_op_1_ret,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof (SmtTerm.imp cond rhs) = SmtType.Bool
            simp [typeof_imp_eq, hCondTy, hRhsTy, __smtx_typeof_guard,
              native_ite, native_Teq]
          · change __smtx_model_eval M (SmtTerm.imp cond rhs) =
              SmtValue.Boolean true
            have hYValTy :
                __smtx_typeof_value (__smtx_model_eval M ty) =
                  SmtType.Seq T := by
              simpa [ty, hyTy] using
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt y) hYNN
            rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
            have hXNN : term_has_non_none_type tx := by
              unfold term_has_non_none_type
              rw [show __smtx_typeof tx = SmtType.Int by simpa [tx] using hxTy]
              decide
            have hXValTy :
                __smtx_typeof_value (__smtx_model_eval M tx) =
                  SmtType.Int := by
              simpa [tx, hxTy] using
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt x) (by simpa [tx] using hXNN)
            rcases int_value_canonical hXValTy with ⟨i, hXEval⟩
            have hNilEval :
                __smtx_model_eval M nilS = SmtValue.Seq (SmtSeq.empty T) := by
              simpa [nilS, pre] using
                eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
            have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
              simpa [hYEval, __smtx_typeof_value] using hYValTy
            have hElemTy : __smtx_elem_typeof_seq_value sy = T :=
              elem_typeof_seq_value_of_typeof_seq_value hSyTy
            rw [smtx_eval_imp_term_eq]
            simp [cond, rhs, decomposition, suffixS, nthS, preS, remaining,
              next, len, __smtx_model_eval, __smtx_model_eval_imp,
              __smtx_model_eval_and, __smtx_model_eval_eq,
              __smtx_model_eval_geq, __smtx_model_eval_gt,
              __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
              __smtx_model_eval_str_concat, __smtx_model_eval__at_purify,
              __smtx_model_eval_plus, __smtx_model_eval__,
              hYEval, hXEval, hNilEval, native_seq_len, native_seq_concat,
              native_and, native_or, native_not, native_zleq, native_zlt,
              native_zplus, native_zneg]
            by_cases hi : 0 ≤ i
            · by_cases hlt : i < Int.ofNat (native_unpack_seq sy).length
              · let xs := native_unpack_seq sy
                let j := Int.toNat i
                have hCast : Int.ofNat j = i := by
                  simpa [j] using Int.toNat_of_nonneg hi
                have hjlt : j < xs.length := by
                  have hlt' := hlt
                  rw [← hCast] at hlt'
                  exact Int.ofNat_lt.mp (by simpa [xs] using hlt')
                have hjSuccLe : j + 1 ≤ xs.length := by omega
                have hNextCast : i + 1 = Int.ofNat (j + 1) := by
                  rw [← hCast]
                  simp
                have hRemainingCast :
                    Int.ofNat xs.length + -(i + 1) =
                      Int.ofNat (xs.length - (j + 1)) := by
                  rw [hNextCast]
                  have hsimpa := (Int.ofNat_sub hjSuccLe).symm
                  try simp at hsimpa ⊢
                  exact hsimpa
                have hRemainingNatCast :
                    Int.ofNat xs.length + -Int.ofNat (j + 1) =
                      Int.ofNat (xs.length - (j + 1)) := by
                  have hsimpa := (Int.ofNat_sub hjSuccLe).symm
                  try simp at hsimpa ⊢
                  exact hsimpa
                have hPreExtract :
                    native_seq_extract xs 0 i = xs.take j := by
                  rw [← hCast]
                  exact native_seq_extract_zero_nat xs j (Nat.le_of_lt hjlt)
                have hSuffixExtract :
                    native_seq_extract xs (i + 1)
                        (Int.ofNat xs.length + -(i + 1)) =
                      xs.drop (j + 1) := by
                  rw [hNextCast, hRemainingNatCast]
                  exact native_seq_extract_to_end_nat xs (j + 1) hjSuccLe
                have hNthEval :
                    __smtx_seq_nth M (SmtValue.Seq sy) (SmtValue.Numeral i) =
                      xs.getD j SmtValue.NotValue := by
                  simp only [__smtx_seq_nth]
                  rw [← hCast, sr_ssm_seq_nth_ofNat]
                  exact sr_getD_lt_eq _ _ _ _ hjlt
                have hDecomp :
                    native_seq_extract xs 0 i ++
                        [__smtx_seq_nth M (SmtValue.Seq sy)
                          (SmtValue.Numeral i)] ++
                        native_seq_extract xs (i + 1)
                          (Int.ofNat xs.length + -(i + 1)) = xs := by
                  rw [hPreExtract, hNthEval, hSuffixExtract]
                  exact sr_take_getD_drop_succ SmtValue.NotValue xs j hjlt
                have hPreLen :
                    Int.ofNat (native_seq_extract xs 0 i).length = i := by
                  rw [hPreExtract, List.length_take,
                    Nat.min_eq_left (Nat.le_of_lt hjlt), hCast]
                have hSuffixLen :
                    Int.ofNat
                        (native_seq_extract xs (i + 1)
                          (Int.ofNat xs.length + -(i + 1))).length =
                      Int.ofNat xs.length + -(i + 1) := by
                  rw [hSuffixExtract, List.length_drop, hRemainingCast]
                have hPack : native_pack_seq T xs = sy := by
                  rw [← hElemTy]
                  exact native_pack_unpack_seq sy
                simp only [__smtx_model_eval_leq, __smtx_model_eval_lt,
                  native_zleq, native_zlt, decide_eq_true_eq.mpr hi,
                  decide_eq_true_eq.mpr hlt, native_and, native_not,
                  __smtx_model_eval_not, __smtx_model_eval_or]
                simp only [Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  native_unpack_seq]
                simp [xs] at hDecomp hPreLen hSuffixLen hPack
                simp [hElemTy, hDecomp, hPreLen, hSuffixLen, hPack,
                  native_veq, native_and, native_or]
              · simp [__smtx_model_eval_or, __smtx_model_eval_not,
                  __smtx_model_eval_leq, __smtx_model_eval_lt,
                  native_zleq, native_zlt, native_and, native_not,
                  native_or, hi, hlt, Int.le_of_not_gt hlt]
                exact Or.inl (Int.le_of_not_gt hlt)
            · simp [__smtx_model_eval_or, __smtx_model_eval_not,
                __smtx_model_eval_leq, __smtx_model_eval_lt, native_zleq,
                native_zlt, native_and, native_not, native_or, hi]
        case str_leq =>
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          have hOrigNN :
              term_has_non_none_type (SmtTerm.str_leq ty tx) := by
            have hsimpa := hTrans
            try simp [ty, tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
            exact hsimpa
          have hArgs := seq_char_binop_args_of_non_none
            (op := SmtTerm.str_leq) (typeof_str_leq_eq ty tx) hOrigNN
          have hyTy : __smtx_typeof ty = SmtType.Seq SmtType.Char := hArgs.1
          have hxTy : __smtx_typeof tx = SmtType.Seq SmtType.Char := hArgs.2
          have hYNN : term_has_non_none_type ty := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none SmtType.Char
          have hXNN : term_has_non_none_type tx := by
            unfold term_has_non_none_type
            rw [hxTy]
            exact seq_ne_none SmtType.Char
          have hLeqTy :
              __smtx_typeof (SmtTerm.str_leq ty tx) = SmtType.Bool := by
            rw [typeof_str_leq_eq, hyTy, hxTy]
            simp [native_ite, native_Teq]
          have hYValTy :
              __smtx_typeof_value (__smtx_model_eval M ty) =
                SmtType.Seq SmtType.Char := by
            simpa [hyTy] using
              smt_model_eval_preserves_type_of_non_none M hM ty hYNN
          have hXValTy :
              __smtx_typeof_value (__smtx_model_eval M tx) =
                SmtType.Seq SmtType.Char := by
            simpa [hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM tx hXNN
          rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
          rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
          have hSyTy :
              __smtx_typeof_seq_value sy =
                SmtType.Seq SmtType.Char := by
            simpa [hYEval, __smtx_typeof_value] using hYValTy
          have hSxTy :
              __smtx_typeof_seq_value sx =
                SmtType.Seq SmtType.Char := by
            simpa [hXEval, __smtx_typeof_value] using hXValTy
          let ys := native_unpack_string sy
          let xs := native_unpack_string sx
          have hYValid : native_string_valid ys = true :=
            native_unpack_string_valid_of_typeof_seq_char hSyTy
          have hXValid : native_string_valid xs = true :=
            native_unpack_string_valid_of_typeof_seq_char hSxTy
          have hYPack : native_pack_string ys = sy :=
            sr_native_pack_unpack_string sy hSyTy
          have hXPack : native_pack_string xs = sx :=
            sr_native_pack_unpack_string sx hSxTy
          have hYEvalString :
              __smtx_model_eval M ty =
                SmtValue.Seq (native_pack_string ys) := by
            rw [hYPack]
            exact hYEval
          have hXEvalString :
              __smtx_model_eval M tx =
                SmtValue.Seq (native_pack_string xs) := by
            rw [hXPack]
            exact hXEval
          have hClosedArgs :
              __eo_is_closed y = Term.Boolean true ∧
                __eo_is_closed x = Term.Boolean true := by
            apply sr_eo_is_closed_binary_uop_args UserOp.str_leq y x
            · decide
            · decide
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              have hsimpa := hYNN
              try simp [ty, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              have hsimpa := hXNN
              try simp [tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            · exact hClosed
          let idxName := native_string_lit "@var.str_index"
          let idx := SmtTerm.Var idxName SmtType.Int
          let sCode := SmtTerm.str_to_code
            (SmtTerm.str_substr ty idx (SmtTerm.Numeral 1))
          let tCode := SmtTerm.str_to_code
            (SmtTerm.str_substr tx idx (SmtTerm.Numeral 1))
          let leqResult := SmtTerm._at_purify (SmtTerm.str_leq ty tx)
          let prefixEq := SmtTerm.eq
            (SmtTerm.str_substr ty (SmtTerm.Numeral 0) idx)
            (SmtTerm.str_substr tx (SmtTerm.Numeral 0) idx)
          let cmp := SmtTerm.ite leqResult
            (SmtTerm.geq sCode tCode) (SmtTerm.geq tCode sCode)
          let qBody := SmtTerm.or
            (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
            (SmtTerm.or
              (SmtTerm.not (SmtTerm.leq idx (SmtTerm.str_len ty)))
              (SmtTerm.or
                (SmtTerm.not (SmtTerm.leq idx (SmtTerm.str_len tx)))
                (SmtTerm.or (SmtTerm.not prefixEq)
                  (SmtTerm.or cmp (SmtTerm.Boolean false)))))
          let forallEncoding :=
            SmtTerm.not
              (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
          let formula := SmtTerm.ite (SmtTerm.eq ty tx) leqResult
            (SmtTerm.not forallEncoding)
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof formula = SmtType.Bool
            simp [formula, forallEncoding, qBody, cmp, prefixEq, leqResult, tCode,
              sCode, idx, typeof_ite_eq, typeof_eq_eq, typeof_not_eq,
              smtx_typeof_exists_term_eq, typeof_or_eq, typeof_geq_eq,
              typeof_leq_eq, typeof_str_len_eq, typeof_str_substr_eq,
              typeof_str_to_code_eq, hyTy, hxTy, hLeqTy,
              __smtx_typeof, __smtx_typeof_seq_op_1,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard_wf, __smtx_typeof_guard,
              __smtx_typeof_ite, sr_smt_type_wf_int,
              native_ite, native_Teq]
          · change __smtx_model_eval M formula = SmtValue.Boolean true
            have hLeqEval :
                __smtx_model_eval M leqResult =
                  SmtValue.Boolean (sr_native_str_leq_bool ys xs) := by
              simp [leqResult, __smtx_model_eval, hYEvalString,
                hXEvalString, __smtx_model_eval__at_purify,
                __smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
                __smtx_model_eval_eq, __smtx_model_eval_or,
                sr_native_str_leq_bool, sr_native_unpack_pack_string,
                sr_native_pack_string_eq_iff,
                native_veq, native_or]
            by_cases hEq : ys = xs
            · simp [formula, __smtx_model_eval, hYEvalString,
                hXEvalString, hLeqEval, __smtx_model_eval_ite,
                __smtx_model_eval_eq, sr_native_str_leq_bool,
                sr_native_pack_string_eq_iff,
                native_str_lt, native_veq, native_or, hEq]
            · rcases sr_native_str_leq_witness ys xs hYValid hXValid hEq with
                ⟨j, hjY, hjX, hPrefix, hCmp⟩
              have hForallFalse :
                  __smtx_model_eval M forallEncoding =
                    SmtValue.Boolean false := by
                let Mj := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral (Int.ofNat j))
                have hIdxEval :
                    native_model_var_lookup Mj idxName SmtType.Int =
                      SmtValue.Numeral (Int.ofNat j) := by
                  simp [Mj, native_model_var_lookup, native_model_push]
                have hYEvalPush :
                    __smtx_model_eval Mj ty =
                      SmtValue.Seq (native_pack_string ys) := by
                  rw [← hYEvalString]
                  exact (smt_model_eval_eq_of_eo_closed y hClosedArgs.1 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hXEvalPush :
                    __smtx_model_eval Mj tx =
                      SmtValue.Seq (native_pack_string xs) := by
                  rw [← hXEvalString]
                  exact (smt_model_eval_eq_of_eo_closed x hClosedArgs.2 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hLeqEvalPush :
                    __smtx_model_eval Mj leqResult =
                      SmtValue.Boolean (sr_native_str_leq_bool ys xs) := by
                  simp [leqResult, __smtx_model_eval, hYEvalPush,
                    hXEvalPush, __smtx_model_eval__at_purify,
                    __smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
                    __smtx_model_eval_eq, __smtx_model_eval_or,
                    sr_native_str_leq_bool, sr_native_unpack_pack_string,
                    sr_native_pack_string_eq_iff,
                    native_veq, native_or]
                have hPrefixStringY :=
                  sr_native_str_substr_zero_nat ys j hjY
                have hPrefixStringX :=
                  sr_native_str_substr_zero_nat xs j hjX
                have hPrefixEval :
                    __smtx_model_eval Mj prefixEq =
                      SmtValue.Boolean true := by
                  simp [prefixEq, idx, __smtx_model_eval, hYEvalPush,
                    hXEvalPush, hIdxEval, __smtx_model_eval_eq,
                    __smtx_model_eval_str_substr,
                    Smtm.native_unpack_pack_seq,
                    sr_native_unpack_pack_string,
                    sr_native_pack_string_eq_iff,
                    sr_native_seq_extract_pack_string,
                    sr_native_seq_extract_pack_string_eval,
                    sr_native_unpack_extract_pack_string,
                    hPrefixStringY, hPrefixStringX, hPrefix, native_veq]
                  rw [sr_int_natCast_eq_ofNat j, hPrefixStringY,
                    hPrefixStringX, hPrefix]
                have hCmpEval :
                    __smtx_model_eval Mj cmp =
                      SmtValue.Boolean false := by
                  by_cases hLeqB : sr_native_str_leq_bool ys xs = true
                  · have hLt :
                        native_str_to_code
                            (native_str_substr ys (Int.ofNat j) 1) <
                          native_str_to_code
                            (native_str_substr xs (Int.ofNat j) 1) := by
                      simpa [hLeqB] using hCmp
                    have hNotLe := Int.not_le_of_gt hLt
                    simp [cmp, tCode, sCode, idx, __smtx_model_eval,
                      hYEvalPush, hXEvalPush, hLeqEvalPush, hIdxEval,
                      __smtx_model_eval_ite, __smtx_model_eval_geq,
                      __smtx_model_eval_leq,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code, native_zleq,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hLeqB, hNotLe]
                    rw [sr_int_natCast_eq_ofNat j]
                    exact hLt
                  · have hLt :
                        native_str_to_code
                            (native_str_substr xs (Int.ofNat j) 1) <
                          native_str_to_code
                            (native_str_substr ys (Int.ofNat j) 1) := by
                      simpa [hLeqB] using hCmp
                    have hNotLe := Int.not_le_of_gt hLt
                    simp [cmp, tCode, sCode, idx, __smtx_model_eval,
                      hYEvalPush, hXEvalPush, hLeqEvalPush, hIdxEval,
                      __smtx_model_eval_ite, __smtx_model_eval_geq,
                      __smtx_model_eval_leq,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code, native_zleq,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hLeqB, hNotLe]
                    rw [sr_int_natCast_eq_ofNat j]
                    exact hLt
                have hAtFalse :
                    __smtx_model_eval Mj qBody =
                      SmtValue.Boolean false := by
                  simp [qBody, idx, __smtx_model_eval, hYEvalPush,
                    hXEvalPush, hIdxEval, hPrefixEval, hCmpEval,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, __smtx_model_eval_leq,
                    __smtx_model_eval_str_len,
                    native_seq_len,
                    native_zleq, native_and, native_or, native_not,
                    Smtm.native_unpack_pack_seq,
                    sr_native_unpack_pack_string_length, List.length_map,
                    hjY, hjX]
                exact sr_eval_forall_encoding_false M idxName SmtType.Int
                  qBody (SmtValue.Numeral (Int.ofNat j)) rfl
                  (by simp [__smtx_value_canonical]) hAtFalse
              simp [formula, __smtx_model_eval, hYEvalString,
                hXEvalString, hLeqEval, hForallFalse,
                __smtx_model_eval_ite, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not,
                sr_native_unpack_pack_string,
                sr_native_pack_string_eq_iff, hEq]
      case Apply h z =>
        cases h <;> try
          simp [__str_reduction_pred, stringReductionBody,
            __eo_mk_apply] at hBodyTy ⊢
        all_goals try
          (change Term.Stuck = Term.Bool at hBodyTy
           exact False.elim (Term.noConfusion hBodyTy))
        case UOp op =>
          cases op <;> try
            simp [__str_reduction_pred, stringReductionBody,
              __eo_mk_apply] at hBodyTy ⊢
          all_goals try
            (change Term.Stuck = Term.Bool at hBodyTy
             exact False.elim (Term.noConfusion hBodyTy))
          case str_substr =>
            have hOrigNN :
                term_has_non_none_type
                  (SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y)
                    (__eo_to_smt x)) := by
              have hsimpa := hTrans
              try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            rcases str_substr_args_of_non_none hOrigNN with
              ⟨T, hzTy, hyTy, hxTy⟩
            let pre := srPurify
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z)
                  (Term.Numeral 0)) y)
            have hPreTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm._at_purify
                    (SmtTerm.str_substr (__eo_to_smt z) (SmtTerm.Numeral 0)
                      (__eo_to_smt y))) = SmtType.Seq T
              simp [__smtx_typeof, typeof_str_substr_eq, hzTy, hyTy,
                __smtx_typeof_str_substr, native_ite, native_Teq]
            have hNilNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                  Term.Stuck :=
              nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreTy
            have hNilNe' :
                __eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (srPurify
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_substr) z)
                            (Term.Numeral 0)) y))) ≠
                  Term.Stuck := by
              simpa [pre] using hNilNe
            have hEmptyNe :
                __seq_empty (__eo_typeof z) ≠ Term.Stuck :=
              seq_empty_typeof_ne_stuck_of_smt_type_seq z T hzTy
            simp only [hNilNe', hEmptyNe, __eo_mk_apply] at hBodyTy ⊢
            have hTWf : __smtx_type_wf T = true :=
              (smt_seq_component_wf_of_non_none_type (__eo_to_smt z) T
                hzTy).2
            have hTInh : type_inhabited T :=
              (smt_seq_component_wf_of_non_none_type (__eo_to_smt z) T
                hzTy).1
            have hZNN : term_has_non_none_type (__eo_to_smt z) := by
              unfold term_has_non_none_type
              rw [hzTy]
              exact seq_ne_none T
            let tz := __eo_to_smt z
            let tn := __eo_to_smt y
            let tm := __eo_to_smt x
            let len := SmtTerm.str_len tz
            let mid := SmtTerm._at_purify (SmtTerm.str_substr tz tn tm)
            let next := SmtTerm.plus tn
              (SmtTerm.plus tm (SmtTerm.Numeral 0))
            let remaining := SmtTerm.neg len next
            let suffix := SmtTerm._at_purify
              (SmtTerm.str_substr tz next remaining)
            let preS := SmtTerm._at_purify
              (SmtTerm.str_substr tz (SmtTerm.Numeral 0) tn)
            let nilS := __eo_to_smt
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
            let emptyS := __eo_to_smt (__seq_empty (__eo_typeof z))
            let decomposition := SmtTerm.str_concat preS
              (SmtTerm.str_concat mid (SmtTerm.str_concat suffix nilS))
            let cond := SmtTerm.and (SmtTerm.geq tn (SmtTerm.Numeral 0))
              (SmtTerm.and (SmtTerm.gt len tn)
                (SmtTerm.and (SmtTerm.gt tm (SmtTerm.Numeral 0))
                  (SmtTerm.Boolean true)))
            let rhs := SmtTerm.and (SmtTerm.eq tz decomposition)
              (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) tn)
                (SmtTerm.and
                  (SmtTerm.or
                    (SmtTerm.eq (SmtTerm.str_len suffix) remaining)
                    (SmtTerm.or
                      (SmtTerm.eq (SmtTerm.str_len suffix)
                        (SmtTerm.Numeral 0))
                      (SmtTerm.Boolean false)))
                  (SmtTerm.and
                    (SmtTerm.leq (SmtTerm.str_len mid) tm)
                    (SmtTerm.Boolean true))))
            let formula := SmtTerm.ite cond rhs (SmtTerm.eq mid emptyS)
            have hEmptyNN : term_has_non_none_type emptyS := by
              have hsimpa :=
                seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                  z T hzTy hTInh hTWf
              try simp [emptyS] at hsimpa ⊢
              exact hsimpa
            have hEmptyTy : __smtx_typeof emptyS = SmtType.Seq T := by
              simpa [emptyS] using
                smt_typeof_seq_empty_typeof z T hzTy hEmptyNN
            have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
              simpa [nilS, pre] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
            have hLenTy : __smtx_typeof len = SmtType.Int := by
              simp [len, tz, typeof_str_len_eq, hzTy,
                __smtx_typeof_seq_op_1_ret]
            have hNextTy : __smtx_typeof next = SmtType.Int := by
              simp [next, tn, tm, hyTy, hxTy, typeof_plus_eq,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hRemainingTy : __smtx_typeof remaining = SmtType.Int := by
              simp [remaining, hLenTy, hNextTy, typeof_neg_eq,
                __smtx_typeof_arith_overload_op_2]
            have hMidTy : __smtx_typeof mid = SmtType.Seq T := by
              change __smtx_typeof (SmtTerm.str_substr tz tn tm) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, tn, tm, hzTy, hyTy, hxTy,
                __smtx_typeof_str_substr]
            have hPrefixTy : __smtx_typeof preS = SmtType.Seq T := by
              have hsimpa := hPreTy
              try simp [preS, tz, tn, pre] at hsimpa ⊢
              exact hsimpa
            have hSuffixTy : __smtx_typeof suffix = SmtType.Seq T := by
              change __smtx_typeof (SmtTerm.str_substr tz next remaining) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, hzTy, hNextTy,
                hRemainingTy, __smtx_typeof_str_substr]
            have hDecompositionTy :
                __smtx_typeof decomposition = SmtType.Seq T := by
              simp [decomposition, typeof_str_concat_eq, hPrefixTy, hMidTy,
                hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hCondTy : __smtx_typeof cond = SmtType.Bool := by
              simp [cond, typeof_and_eq, typeof_geq_eq, typeof_gt_eq,
                hLenTy, tn, tm, hyTy, hxTy,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hRhsTy : __smtx_typeof rhs = SmtType.Bool := by
              simp [rhs, typeof_and_eq, typeof_or_eq, typeof_eq_eq,
                typeof_leq_eq, typeof_str_len_eq, tz, tn, tm, hzTy, hyTy,
                hxTy, hDecompositionTy, hPrefixTy, hMidTy, hSuffixTy,
                hRemainingTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof formula = SmtType.Bool
              simp [formula, typeof_ite_eq, typeof_eq_eq, hCondTy, hRhsTy,
                hMidTy, hEmptyTy, __smtx_typeof_ite, __smtx_typeof_eq,
                __smtx_typeof_guard, native_ite, native_Teq]
            · change __smtx_model_eval M formula = SmtValue.Boolean true
              have hZValTy :
                  __smtx_typeof_value (__smtx_model_eval M tz) =
                    SmtType.Seq T := by
                simpa [tz, hzTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt z) hZNN
              rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
              have hNNN : term_has_non_none_type tn := by
                unfold term_has_non_none_type
                rw [show __smtx_typeof tn = SmtType.Int by
                  simpa [tn] using hyTy]
                decide
              have hNValTy :
                  __smtx_typeof_value (__smtx_model_eval M tn) =
                    SmtType.Int := by
                simpa [tn, hyTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt y) (by simpa [tn] using hNNN)
              rcases int_value_canonical hNValTy with ⟨n, hNEval⟩
              have hMNN : term_has_non_none_type tm := by
                unfold term_has_non_none_type
                rw [show __smtx_typeof tm = SmtType.Int by
                  simpa [tm] using hxTy]
                decide
              have hMValTy :
                  __smtx_typeof_value (__smtx_model_eval M tm) =
                    SmtType.Int := by
                simpa [tm, hxTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt x) (by simpa [tm] using hMNN)
              rcases int_value_canonical hMValTy with ⟨m, hMEval⟩
              have hNilEval :
                  __smtx_model_eval M nilS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [nilS, pre] using
                  eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
              have hEmptyEval :
                  __smtx_model_eval M emptyS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [emptyS] using eval_seq_empty_typeof M z T hzTy
              have hSzTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
                simpa [hZEval, __smtx_typeof_value] using hZValTy
              have hElemTy : __smtx_elem_typeof_seq_value sz = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSzTy
              let xs := native_unpack_seq sz
              have hPack : native_pack_seq T xs = sz := by
                simpa [xs, hElemTy] using native_pack_unpack_seq sz
              dsimp [xs] at hPack
              by_cases hi : 0 ≤ n
              · by_cases hiLen : n < Int.ofNat xs.length
                · by_cases hm : 0 < m
                  · rcases sr_native_seq_extract_active_facts xs n m
                        hi hiLen hm with
                      ⟨hDecomp, hPreLen, hSuffixLen, hMidLen⟩
                    dsimp [xs] at hiLen hDecomp hPreLen hSuffixLen hMidLen
                    rcases hSuffixLen with hSuffixLen | hSuffixLen
                    all_goals
                      simp [formula, cond, rhs, decomposition, preS, mid,
                        suffix, remaining, next, len, __smtx_model_eval,
                        __smtx_model_eval_ite, __smtx_model_eval_and,
                        __smtx_model_eval_or, __smtx_model_eval_eq,
                        __smtx_model_eval_geq, __smtx_model_eval_gt,
                        __smtx_model_eval_lt, __smtx_model_eval_leq,
                        __smtx_model_eval_str_len,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_concat,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_plus, __smtx_model_eval__, hZEval,
                        hNEval, hMEval, hNilEval, hEmptyEval, native_seq_len,
                        native_seq_concat, native_and, native_or, native_not,
                        native_zleq, native_zlt, native_zplus, native_zneg,
                        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                        native_unpack_seq, xs, hElemTy, hi, hiLen, hm, hPack,
                        hDecomp, hPreLen, hSuffixLen, hMidLen, native_veq,
                        native_pack_seq]
                    all_goals
                      constructor
                      · simpa [List.append_assoc, Int.sub_eq_add_neg] using
                          hPack.symm.trans
                            (congrArg (native_pack_seq T) hDecomp.symm)
                      · first
                        | left
                          simpa [Int.sub_eq_add_neg] using hSuffixLen
                        | right
                          simpa [Int.sub_eq_add_neg] using hSuffixLen
                  · have hInactive :
                        ¬ (0 ≤ n ∧ n < Int.ofNat xs.length ∧ 0 < m) := by
                      rintro ⟨_hi, _hiLen, hm'⟩
                      exact hm hm'
                    have hExtract :=
                      sr_native_seq_extract_empty_of_inactive xs n m hInactive
                    dsimp [xs] at hiLen hExtract
                    simp [formula, cond, rhs, decomposition, preS, mid,
                      suffix, remaining, next, len, __smtx_model_eval,
                      __smtx_model_eval_ite, __smtx_model_eval_and,
                      __smtx_model_eval_or, __smtx_model_eval_eq,
                      __smtx_model_eval_geq, __smtx_model_eval_gt,
                      __smtx_model_eval_lt, __smtx_model_eval_leq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_concat,
                      __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                      __smtx_model_eval__, hZEval, hNEval, hMEval, hNilEval,
                      hEmptyEval, native_seq_len, native_seq_concat,
                      native_and, native_or, native_not, native_zleq,
                      native_zlt, native_zplus, native_zneg,
                      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                      native_unpack_seq, xs, hElemTy, hi, hiLen, hm,
                      hExtract, native_veq, native_pack_seq]
                · have hInactive :
                      ¬ (0 ≤ n ∧ n < Int.ofNat xs.length ∧ 0 < m) := by
                    rintro ⟨_hi, hiLen', _hm⟩
                    exact hiLen hiLen'
                  have hExtract :=
                    sr_native_seq_extract_empty_of_inactive xs n m hInactive
                  dsimp [xs] at hiLen hExtract
                  simp [formula, cond, rhs, decomposition, preS, mid, suffix,
                    remaining, next, len, __smtx_model_eval,
                    __smtx_model_eval_ite, __smtx_model_eval_and,
                    __smtx_model_eval_or, __smtx_model_eval_eq,
                    __smtx_model_eval_geq, __smtx_model_eval_gt,
                    __smtx_model_eval_lt, __smtx_model_eval_leq,
                    __smtx_model_eval_str_len,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_concat,
                    __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                    __smtx_model_eval__, hZEval, hNEval, hMEval, hNilEval,
                    hEmptyEval, native_seq_len, native_seq_concat,
                    native_and, native_or, native_not, native_zleq,
                    native_zlt, native_zplus, native_zneg,
                    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                    native_unpack_seq, xs, hElemTy, hi, hiLen, hExtract,
                    native_veq, native_pack_seq]
              · have hInactive :
                    ¬ (0 ≤ n ∧ n < Int.ofNat xs.length ∧ 0 < m) := by
                  rintro ⟨hi', _hiLen, _hm⟩
                  exact hi hi'
                have hExtract :=
                  sr_native_seq_extract_empty_of_inactive xs n m hInactive
                dsimp [xs] at hExtract
                simp [formula, cond, rhs, decomposition, preS, mid, suffix,
                  remaining, next, len, __smtx_model_eval,
                  __smtx_model_eval_ite, __smtx_model_eval_and,
                  __smtx_model_eval_or, __smtx_model_eval_eq,
                  __smtx_model_eval_geq, __smtx_model_eval_gt,
                  __smtx_model_eval_lt, __smtx_model_eval_leq,
                  __smtx_model_eval_str_len,
                  __smtx_model_eval_str_substr,
                  __smtx_model_eval_str_concat,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, hZEval, hNEval, hMEval, hNilEval,
                  hEmptyEval, native_seq_len, native_seq_concat, native_and,
                  native_or, native_not, native_zleq, native_zlt,
                  native_zplus, native_zneg, Smtm.native_unpack_pack_seq,
                  elem_typeof_pack_seq, native_unpack_seq, xs, hElemTy, hi,
                  hExtract, native_veq, native_pack_seq]
          case str_replace =>
            let tz := __eo_to_smt z
            let ty := __eo_to_smt y
            let tx := __eo_to_smt x
            have hOrigNN :
                term_has_non_none_type (SmtTerm.str_replace tz ty tx) := by
              have hsimpa := hTrans
              try simp [tz, ty, tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
                (typeof_str_replace_eq tz ty tx) hOrigNN with
              ⟨T, hzTy, hyTy, hxTy⟩
            have hZNN : term_has_non_none_type tz := by
              unfold term_has_non_none_type
              rw [hzTy]
              exact seq_ne_none T
            have hYNN : term_has_non_none_type ty := by
              unfold term_has_non_none_type
              rw [hyTy]
              exact seq_ne_none T
            have hXNN : term_has_non_none_type tx := by
              unfold term_has_non_none_type
              rw [hxTy]
              exact seq_ne_none T
            have hZTermNe : z ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation z (by
                have hsimpa := hZNN; (try simp [tz, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hYTermNe : y ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation y (by
                have hsimpa := hYNN; (try simp [ty, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hXTermNe : x ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation x (by
                have hsimpa := hXNN; (try simp [tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hTWf : __smtx_type_wf T = true :=
              (smt_seq_component_wf_of_non_none_type tz T hzTy).2
            have hTInh : type_inhabited T :=
              (smt_seq_component_wf_of_non_none_type tz T hzTy).1
            let idx := SmtTerm.str_indexof tz ty (SmtTerm.Numeral 0)
            let pre := srPurify
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z)
                  (Term.Numeral 0))
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_indexof) z) y)
                  (Term.Numeral 0)))
            let preS := SmtTerm._at_purify
              (SmtTerm.str_substr tz (SmtTerm.Numeral 0) idx)
            have hIdxTy : __smtx_typeof idx = SmtType.Int := by
              simp [idx, typeof_str_indexof_eq, tz, ty, hzTy, hyTy,
                __smtx_typeof_str_indexof, __smtx_typeof, native_ite,
                native_Teq]
            have hPreTy : __smtx_typeof preS = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tz (SmtTerm.Numeral 0) idx) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, hzTy, hIdxTy,
                __smtx_typeof_str_substr, __smtx_typeof, native_ite,
                native_Teq]
            have hPreEoTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              have hsimpa := hPreTy
              try simp [pre, preS, idx, tz, ty] at hsimpa ⊢
              exact hsimpa
            have hNilPreNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                  Term.Stuck :=
              nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreEoTy
            have hNilPreNe' :
                __eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (srPurify
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_substr) z)
                            (Term.Numeral 0))
                          (Term.Apply
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_indexof) z) y)
                            (Term.Numeral 0))))) ≠
                  Term.Stuck := by
              simpa [pre] using hNilPreNe
            have hNilReplNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x) ≠
                  Term.Stuck :=
              nil_str_concat_typeof_ne_stuck_of_smt_type_seq x T
                (by simpa [tx] using hxTy)
            have hEmptyNe :
                __seq_empty (__eo_typeof y) ≠ Term.Stuck :=
              seq_empty_typeof_ne_stuck_of_smt_type_seq y T
                (by simpa [ty] using hyTy)
            simp [hNilPreNe', hNilReplNe, hEmptyNe, __eo_mk_apply] at hBodyTy
            let result := SmtTerm._at_purify (SmtTerm.str_replace tz ty tx)
            let nilPreS := __eo_to_smt
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
            let nilReplS := __eo_to_smt
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))
            let emptyS := __eo_to_smt (__seq_empty (__eo_typeof y))
            let needleLen := SmtTerm.str_len ty
            let sourceLen := SmtTerm.str_len tz
            let cut := SmtTerm.plus (SmtTerm.str_len preS)
              (SmtTerm.plus needleLen (SmtTerm.Numeral 0))
            let suffix := SmtTerm._at_purify
              (SmtTerm.str_substr tz cut (SmtTerm.neg sourceLen cut))
            let sourceDecomp := SmtTerm.str_concat preS
              (SmtTerm.str_concat ty (SmtTerm.str_concat suffix nilPreS))
            let resultDecomp := SmtTerm.str_concat preS
              (SmtTerm.str_concat tx (SmtTerm.str_concat suffix nilPreS))
            let emptyResult := SmtTerm.str_concat tx
              (SmtTerm.str_concat tz nilReplS)
            let needlePre := SmtTerm.str_substr ty (SmtTerm.Numeral 0)
              (SmtTerm.neg needleLen (SmtTerm.Numeral 1))
            let priorHay := SmtTerm.str_concat preS
              (SmtTerm.str_concat needlePre nilPreS)
            let contains := SmtTerm.str_contains tz ty
            let foundCase := SmtTerm.and (SmtTerm.eq tz sourceDecomp)
              (SmtTerm.and (SmtTerm.eq result resultDecomp)
                (SmtTerm.and
                  (SmtTerm.not (SmtTerm.str_contains priorHay ty))
                  (SmtTerm.Boolean true)))
            let formula := SmtTerm.ite (SmtTerm.eq ty emptyS)
              (SmtTerm.eq result emptyResult)
              (SmtTerm.ite contains foundCase (SmtTerm.eq result tz))
            have hEmptyNN : term_has_non_none_type emptyS := by
              have hsimpa :=
                seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                  y T (by simpa [ty] using hyTy) hTInh hTWf
              try simp [emptyS, ty] at hsimpa ⊢
              exact hsimpa
            have hEmptyTy : __smtx_typeof emptyS = SmtType.Seq T := by
              simpa [emptyS, ty] using
                smt_typeof_seq_empty_typeof y T (by simpa [ty] using hyTy)
                  hEmptyNN
            have hNilPreTy : __smtx_typeof nilPreS = SmtType.Seq T := by
              simpa [nilPreS] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T
                  hPreEoTy
            have hNilReplTy : __smtx_typeof nilReplS = SmtType.Seq T := by
              simpa [nilReplS, tx] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq x T
                  (by simpa [tx] using hxTy)
            have hResultTy : __smtx_typeof result = SmtType.Seq T := by
              change __smtx_typeof (SmtTerm.str_replace tz ty tx) =
                SmtType.Seq T
              simp [typeof_str_replace_eq, tz, ty, tx, hzTy, hyTy, hxTy,
                __smtx_typeof_seq_op_3, native_ite, native_Teq]
            have hNeedleLenTy : __smtx_typeof needleLen = SmtType.Int := by
              simp [needleLen, ty, typeof_str_len_eq, hyTy,
                __smtx_typeof_seq_op_1_ret]
            have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
              simp [sourceLen, tz, typeof_str_len_eq, hzTy,
                __smtx_typeof_seq_op_1_ret]
            have hCutTy : __smtx_typeof cut = SmtType.Int := by
              simp [cut, typeof_plus_eq, typeof_str_len_eq, hPreTy,
                hNeedleLenTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hRemainingTy :
                __smtx_typeof (SmtTerm.neg sourceLen cut) = SmtType.Int := by
              simp [typeof_neg_eq, hSourceLenTy, hCutTy,
                __smtx_typeof_arith_overload_op_2]
            have hSuffixTy : __smtx_typeof suffix = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tz cut (SmtTerm.neg sourceLen cut)) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, hzTy, hCutTy, hRemainingTy,
                __smtx_typeof_str_substr]
            have hNeedlePreTy :
                __smtx_typeof needlePre = SmtType.Seq T := by
              simp [needlePre, typeof_str_substr_eq, ty, hyTy, hNeedleLenTy,
                typeof_neg_eq, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hSourceDecompTy :
                __smtx_typeof sourceDecomp = SmtType.Seq T := by
              simp [sourceDecomp, typeof_str_concat_eq, hPreTy, hyTy,
                hSuffixTy, hNilPreTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hResultDecompTy :
                __smtx_typeof resultDecomp = SmtType.Seq T := by
              simp [resultDecomp, typeof_str_concat_eq, hPreTy, hxTy,
                hSuffixTy, hNilPreTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hEmptyResultTy :
                __smtx_typeof emptyResult = SmtType.Seq T := by
              simp [emptyResult, typeof_str_concat_eq, hxTy, hzTy,
                hNilReplTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
            have hPriorHayTy : __smtx_typeof priorHay = SmtType.Seq T := by
              simp [priorHay, typeof_str_concat_eq, hPreTy, hNeedlePreTy,
                hNilPreTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
            have hContainsTy : __smtx_typeof contains = SmtType.Bool := by
              dsimp [contains]
              rw [typeof_str_contains_eq, hzTy, hyTy]
              simp [__smtx_typeof_seq_op_2_ret, native_ite]
            have hPriorContainsTy :
                __smtx_typeof (SmtTerm.str_contains priorHay ty) =
                  SmtType.Bool := by
              rw [typeof_str_contains_eq, hPriorHayTy, hyTy]
              simp [__smtx_typeof_seq_op_2_ret, native_ite]
            have hNoPriorTy :
                __smtx_typeof
                    (SmtTerm.not (SmtTerm.str_contains priorHay ty)) =
                  SmtType.Bool := by
              rw [typeof_not_eq, hPriorContainsTy]
              simp [__smtx_typeof_guard, native_ite]
            have hNoPriorTailTy :
                __smtx_typeof
                    (SmtTerm.and
                      (SmtTerm.not (SmtTerm.str_contains priorHay ty))
                      (SmtTerm.Boolean true)) = SmtType.Bool := by
              rw [typeof_and_eq, hNoPriorTy]
              simp [__smtx_typeof, native_ite]
            have hResultEqTy :
                __smtx_typeof (SmtTerm.eq result resultDecomp) =
                  SmtType.Bool := by
              rw [typeof_eq_eq, hResultTy, hResultDecompTy]
              simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq]
            have hResultTailTy :
                __smtx_typeof
                    (SmtTerm.and (SmtTerm.eq result resultDecomp)
                      (SmtTerm.and
                        (SmtTerm.not (SmtTerm.str_contains priorHay ty))
                        (SmtTerm.Boolean true))) = SmtType.Bool := by
              simp [typeof_and_eq, hResultEqTy, hNoPriorTailTy,
                __smtx_typeof_guard, native_ite]
            have hSourceEqTy :
                __smtx_typeof (SmtTerm.eq tz sourceDecomp) =
                  SmtType.Bool := by
              rw [typeof_eq_eq, hzTy, hSourceDecompTy]
              simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq]
            have hFoundTy : __smtx_typeof foundCase = SmtType.Bool := by
              simp [foundCase, typeof_and_eq, hSourceEqTy, hResultTailTy,
                __smtx_typeof_guard, native_ite]
            have hFormulaEq :
                __eo_to_smt
                    (__str_reduction_pred
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_replace) z) y) x)) =
                  formula := by
              simp only [__str_reduction_pred, __eo_mk_apply, hZTermNe,
                hYTermNe, hXTermNe, hNilPreNe', hNilReplNe, hEmptyNe]
              rfl
            change eo_interprets M
              (__str_reduction_pred
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_replace) z) y) x)) true
            apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              rw [hFormulaEq]
              simp [formula, typeof_ite_eq, typeof_eq_eq, hEmptyTy, hyTy,
                hResultTy, hEmptyResultTy, hContainsTy, hFoundTy, hzTy,
                __smtx_typeof_ite, __smtx_typeof_eq, __smtx_typeof_guard,
                native_ite, native_Teq]
            · rw [hFormulaEq]
              have hZValTy :
                  __smtx_typeof_value (__smtx_model_eval M tz) =
                    SmtType.Seq T := by
                simpa [tz, hzTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt z) hZNN
              have hYValTy :
                  __smtx_typeof_value (__smtx_model_eval M ty) =
                    SmtType.Seq T := by
                simpa [ty, hyTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt y) hYNN
              have hXValTy :
                  __smtx_typeof_value (__smtx_model_eval M tx) =
                    SmtType.Seq T := by
                simpa [tx, hxTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt x) hXNN
              rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
              rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
              rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
              have hSzTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
                simpa [hZEval, __smtx_typeof_value] using hZValTy
              have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
                simpa [hYEval, __smtx_typeof_value] using hYValTy
              have hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
                simpa [hXEval, __smtx_typeof_value] using hXValTy
              have hElemZ : __smtx_elem_typeof_seq_value sz = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSzTy
              have hElemY : __smtx_elem_typeof_seq_value sy = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSyTy
              have hElemX : __smtx_elem_typeof_seq_value sx = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSxTy
              let zs := native_unpack_seq sz
              let ys := native_unpack_seq sy
              let rs := native_unpack_seq sx
              have hZPack : native_pack_seq T zs = sz := by
                simpa [zs, hElemZ] using native_pack_unpack_seq sz
              have hYPack : native_pack_seq T ys = sy := by
                simpa [ys, hElemY] using native_pack_unpack_seq sy
              have hSyEmptyIff : sy = SmtSeq.empty T ↔ ys = [] := by
                constructor
                · intro hEmpty
                  dsimp [ys]
                  rw [hEmpty]
                  rfl
                · intro hEmpty
                  rw [← hYPack, hEmpty]
                  rfl
              have hXPack : native_pack_seq T rs = sx := by
                simpa [rs, hElemX] using native_pack_unpack_seq sx
              have hNilPreEval :
                  __smtx_model_eval M nilPreS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [nilPreS] using
                  eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreEoTy
              have hNilReplEval :
                  __smtx_model_eval M nilReplS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [nilReplS] using
                  eval_nil_str_concat_typeof_of_smt_type_seq M x T
                    (by simpa [tx] using hxTy)
              have hEmptyEval :
                  __smtx_model_eval M emptyS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [emptyS] using eval_seq_empty_typeof M y T
                  (by simpa [ty] using hyTy)
              by_cases hYs : ys = []
              · simp [formula, result, emptyResult, contains, foundCase,
                  sourceDecomp, resultDecomp, priorHay, needlePre, suffix, cut,
                  sourceLen, needleLen, preS, idx, sr_eval_boolean_term_eq,
                  sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                  smtx_eval_and_term_eq, smtx_eval_eq_term_eq,
                  smtx_eval_not_term_eq, sr_eval_str_replace_term_eq,
                  sr_eval_str_contains_term_eq, sr_eval_str_indexof_term_eq,
                  StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                  StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                  smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                  StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                  sr_eval_neg_term_eq,
                  __smtx_model_eval_ite, __smtx_model_eval_and,
                  __smtx_model_eval_eq, __smtx_model_eval_not,
                  __smtx_model_eval_str_replace,
                  __smtx_model_eval_str_contains,
                  __smtx_model_eval_str_indexof,
                  __smtx_model_eval_str_substr,
                  __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, hZEval, hYEval, hXEval, hNilPreEval,
                  hNilReplEval, hEmptyEval, sr_native_seq_replace_nil,
                  native_seq_contains, native_seq_len, native_seq_concat,
                  native_and, native_not, native_zplus, native_zneg,
                  Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  native_unpack_seq, zs, ys, rs, hElemZ, hElemY, hElemX,
                  hZPack, hYPack, hXPack, hSyEmptyIff, hYs, native_veq,
                  native_pack_seq]
              · by_cases hContains : native_seq_contains zs ys = true
                · have hIdxNonneg :
                      0 ≤ native_seq_indexof zs ys 0 := by
                    simpa [native_seq_contains] using hContains
                  have hDecomp :=
                    native_seq_indexof_zero_decomp zs ys hIdxNonneg
                  have hPreLen :=
                    native_seq_extract_prefix_length_of_indexof_nonneg
                      zs ys hIdxNonneg
                  have hMinimal :=
                    sr_native_seq_first_prefix_no_contains
                      zs ys hYs hIdxNonneg
                  have hReplace :=
                    sr_native_seq_replace_eq_extracts_of_indexof_nonneg
                      zs ys rs hIdxNonneg
                  have hSourcePacked :
                      native_pack_seq T
                          (native_seq_extract zs 0
                              (native_seq_indexof zs ys 0) ++
                            (ys ++
                              native_seq_extract zs
                                (Int.ofNat
                                    (native_seq_extract zs 0
                                      (native_seq_indexof zs ys 0)).length +
                                  Int.ofNat ys.length)
                                (Int.ofNat zs.length +
                                  -(Int.ofNat
                                      (native_seq_extract zs 0
                                        (native_seq_indexof zs ys 0)).length +
                                    Int.ofNat ys.length)))) =
                        sz := by
                    rw [hPreLen, ← List.append_assoc,
                      ← Int.sub_eq_add_neg]
                    rw [hDecomp, hZPack]
                  dsimp [zs, ys, rs] at hSourcePacked hPreLen hMinimal hReplace
                  have hPreLen' :
                      ((native_seq_extract zs 0
                          (native_seq_indexof zs ys 0)).length : native_Int) =
                        native_seq_indexof zs ys 0 := by
                    simpa [Int.ofNat_eq_natCast] using hPreLen
                  have hSourcePacked' :
                      sz =
                        native_pack_seq T
                          (native_seq_extract zs 0
                              (native_seq_indexof zs ys 0) ++
                            (ys ++
                              native_seq_extract zs
                                (((native_seq_extract zs 0
                                    (native_seq_indexof zs ys 0)).length :
                                    native_Int) +
                                  (ys.length : native_Int))
                                ((zs.length : native_Int) +
                                  -(((native_seq_extract zs 0
                                      (native_seq_indexof zs ys 0)).length :
                                      native_Int) +
                                    (ys.length : native_Int))))) := by
                    simpa [Int.ofNat_eq_natCast] using hSourcePacked.symm
                  have hMinimal' :
                      native_seq_contains
                          (native_seq_extract zs 0
                              (native_seq_indexof zs ys 0) ++
                            native_seq_extract ys 0
                              ((ys.length : native_Int) + -1)) ys = false := by
                    simpa [Int.ofNat_eq_natCast, Int.sub_eq_add_neg] using
                      hMinimal
                  simp [formula, result, emptyResult, contains, foundCase,
                    sourceDecomp, resultDecomp, priorHay, needlePre, suffix,
                    cut, sourceLen, needleLen, preS, idx,
                    sr_eval_boolean_term_eq, sr_eval_numeral_term_eq,
                    smtx_eval_ite_term_eq, smtx_eval_and_term_eq,
                    smtx_eval_eq_term_eq, smtx_eval_not_term_eq,
                    sr_eval_str_replace_term_eq,
                    sr_eval_str_contains_term_eq,
                    sr_eval_str_indexof_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                    smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                    StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                    sr_eval_neg_term_eq,
                    __smtx_model_eval_ite, __smtx_model_eval_and,
                    __smtx_model_eval_eq, __smtx_model_eval_not,
                    __smtx_model_eval_str_replace,
                    __smtx_model_eval_str_contains,
                    __smtx_model_eval_str_indexof,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
                    __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                    __smtx_model_eval__, hZEval, hYEval, hXEval,
                    hNilPreEval, hNilReplEval, hEmptyEval, native_seq_len,
                    native_seq_concat, native_and, native_not, native_zplus,
                    native_zneg, Smtm.native_unpack_pack_seq,
                    elem_typeof_pack_seq, native_unpack_seq, zs, ys, rs,
                    hElemZ, hElemY, hElemX, hZPack, hYPack, hXPack, hYs,
                    hSyEmptyIff, hContains, hIdxNonneg, hDecomp,
                    hPreLen, hPreLen',
                    hMinimal, hMinimal', hReplace, native_veq,
                    native_pack_seq,
                    Int.ofNat_eq_natCast, Int.sub_eq_add_neg,
                    List.append_assoc]
                  simpa [hPreLen] using hSourcePacked.symm
                · have hContainsFalse : native_seq_contains zs ys = false := by
                    cases h : native_seq_contains zs ys
                    · rfl
                    · exact False.elim (hContains (by simpa using h))
                  have hReplace :=
                    StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
                      zs ys rs hContainsFalse
                  simp [formula, result, emptyResult, contains, foundCase,
                    sourceDecomp, resultDecomp, priorHay, needlePre, suffix,
                    cut, sourceLen, needleLen, preS, idx,
                    sr_eval_boolean_term_eq, sr_eval_numeral_term_eq,
                    smtx_eval_ite_term_eq, smtx_eval_and_term_eq,
                    smtx_eval_eq_term_eq, smtx_eval_not_term_eq,
                    sr_eval_str_replace_term_eq,
                    sr_eval_str_contains_term_eq,
                    sr_eval_str_indexof_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                    smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                    StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                    sr_eval_neg_term_eq,
                    __smtx_model_eval_ite, __smtx_model_eval_and,
                    __smtx_model_eval_eq, __smtx_model_eval_not,
                    __smtx_model_eval_str_replace,
                    __smtx_model_eval_str_contains,
                    __smtx_model_eval_str_indexof,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
                    __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                    __smtx_model_eval__, hZEval, hYEval, hXEval,
                    hNilPreEval, hNilReplEval, hEmptyEval, native_seq_len,
                    native_seq_concat, native_and, native_not, native_zplus,
                    native_zneg, Smtm.native_unpack_pack_seq,
                    elem_typeof_pack_seq, native_unpack_seq, zs, ys, rs,
                    hElemZ, hElemY, hElemX, hZPack, hYPack, hXPack, hYs,
                    hSyEmptyIff, hContains, hContainsFalse, hReplace, native_veq,
                    native_pack_seq]
          case str_indexof =>
            let tz := __eo_to_smt z
            let ty := __eo_to_smt y
            let tx := __eo_to_smt x
            have hOrigNN :
                term_has_non_none_type (SmtTerm.str_indexof tz ty tx) := by
              have hsimpa := hTrans
              try simp [tz, ty, tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            rcases str_indexof_args_of_non_none hOrigNN with
              ⟨T, hzTy, hyTy, hxTy⟩
            have hZNN : term_has_non_none_type tz := by
              unfold term_has_non_none_type
              rw [hzTy]
              exact seq_ne_none T
            have hYNN : term_has_non_none_type ty := by
              unfold term_has_non_none_type
              rw [hyTy]
              exact seq_ne_none T
            have hXNN : term_has_non_none_type tx := by
              unfold term_has_non_none_type
              rw [hxTy]
              decide
            have hZTermNe : z ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation z (by
                have hsimpa := hZNN; (try simp [tz, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hYTermNe : y ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation y (by
                have hsimpa := hYNN; (try simp [ty, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hXTermNe : x ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation x (by
                have hsimpa := hXNN; (try simp [tx, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hTWf : __smtx_type_wf T = true :=
              (smt_seq_component_wf_of_non_none_type tz T hzTy).2
            have hTInh : type_inhabited T :=
              (smt_seq_component_wf_of_non_none_type tz T hzTy).1
            let sourceLen := SmtTerm.str_len tz
            let tail := SmtTerm.str_substr tz tx (SmtTerm.neg sourceLen tx)
            let tailLen := SmtTerm.str_len tail
            let tailIdx := SmtTerm.str_indexof tail ty (SmtTerm.Numeral 0)
            let pre := srPurify
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_substr)
                    (Term.Apply
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_substr) z) x)
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.neg)
                          (Term.Apply (Term.UOp UserOp.str_len) z)) x)))
                  (Term.Numeral 0))
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_indexof)
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_substr) z) x)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.neg)
                            (Term.Apply (Term.UOp UserOp.str_len) z)) x))) y)
                  (Term.Numeral 0)))
            let preS := SmtTerm._at_purify
              (SmtTerm.str_substr tail (SmtTerm.Numeral 0) tailIdx)
            have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
              simp [sourceLen, tz, typeof_str_len_eq, hzTy,
                __smtx_typeof_seq_op_1_ret]
            have hRemainingTy :
                __smtx_typeof (SmtTerm.neg sourceLen tx) = SmtType.Int := by
              simp [typeof_neg_eq, hSourceLenTy, tx, hxTy,
                __smtx_typeof_arith_overload_op_2]
            have hTailTy : __smtx_typeof tail = SmtType.Seq T := by
              simp [tail, typeof_str_substr_eq, tz, tx, hzTy, hxTy,
                hRemainingTy, __smtx_typeof_str_substr]
            have hTailLenTy : __smtx_typeof tailLen = SmtType.Int := by
              simp [tailLen, typeof_str_len_eq, hTailTy,
                __smtx_typeof_seq_op_1_ret]
            have hTailIdxTy : __smtx_typeof tailIdx = SmtType.Int := by
              simp [tailIdx, typeof_str_indexof_eq, hTailTy, hyTy,
                __smtx_typeof_str_indexof, __smtx_typeof, native_ite,
                native_Teq]
            have hPreTy : __smtx_typeof preS = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tail (SmtTerm.Numeral 0) tailIdx) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, hTailTy, hTailIdxTy,
                __smtx_typeof_str_substr, __smtx_typeof]
            have hPreEoTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              have hsimpa := hPreTy
              try simp [pre, preS, tailIdx, tail, sourceLen, tz, ty, tx] at hsimpa ⊢
              exact hsimpa
            have hNilNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                  Term.Stuck :=
              nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreEoTy
            have hNilNe' :
                __eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (srPurify
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_substr)
                              (Term.Apply
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.str_substr) z) x)
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.neg)
                                    (Term.Apply (Term.UOp UserOp.str_len) z)) x)))
                            (Term.Numeral 0))
                          (Term.Apply
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_indexof)
                                (Term.Apply
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.str_substr) z) x)
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.neg)
                                      (Term.Apply (Term.UOp UserOp.str_len) z)) x))) y)
                            (Term.Numeral 0))))) ≠ Term.Stuck := by
              simpa [pre] using hNilNe
            have hEmptyNe :
                __seq_empty (__eo_typeof z) ≠ Term.Stuck :=
              seq_empty_typeof_ne_stuck_of_smt_type_seq z T
                (by simpa [tz] using hzTy)
            simp [hNilNe', hEmptyNe, __eo_mk_apply] at hBodyTy
            let result := SmtTerm._at_purify
              (SmtTerm.str_indexof tz ty tx)
            let nilS := __eo_to_smt
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
            let emptyS := __eo_to_smt (__seq_empty (__eo_typeof z))
            let needleLen := SmtTerm.str_len ty
            let cut := SmtTerm.plus (SmtTerm.str_len preS)
              (SmtTerm.plus needleLen (SmtTerm.Numeral 0))
            let suffix := SmtTerm._at_purify
              (SmtTerm.str_substr tail cut (SmtTerm.neg tailLen cut))
            let tailDecomp := SmtTerm.str_concat preS
              (SmtTerm.str_concat ty (SmtTerm.str_concat suffix nilS))
            let needlePre := SmtTerm.str_substr ty (SmtTerm.Numeral 0)
              (SmtTerm.neg needleLen (SmtTerm.Numeral 1))
            let priorHay := SmtTerm.str_concat preS
              (SmtTerm.str_concat needlePre nilS)
            let contains := SmtTerm.str_contains tail ty
            let invalid := SmtTerm.or (SmtTerm.not contains)
              (SmtTerm.or (SmtTerm.gt tx sourceLen)
                (SmtTerm.or (SmtTerm.gt (SmtTerm.Numeral 0) tx)
                  (SmtTerm.Boolean false)))
            let resultEq := SmtTerm.eq result
            let resultFound := SmtTerm.plus tx
              (SmtTerm.plus (SmtTerm.str_len preS) (SmtTerm.Numeral 0))
            let foundCase := SmtTerm.and (SmtTerm.eq tail tailDecomp)
              (SmtTerm.and
                (SmtTerm.not (SmtTerm.str_contains priorHay ty))
                (SmtTerm.and (resultEq resultFound) (SmtTerm.Boolean true)))
            let formula := SmtTerm.ite invalid
              (resultEq (SmtTerm.Numeral (-1)))
              (SmtTerm.ite (SmtTerm.eq ty emptyS) (resultEq tx) foundCase)
            have hEmptyNN : term_has_non_none_type emptyS := by
              have hsimpa :=
                seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                  z T (by simpa [tz] using hzTy) hTInh hTWf
              try simp [emptyS, tz] at hsimpa ⊢
              exact hsimpa
            have hEmptyTy : __smtx_typeof emptyS = SmtType.Seq T := by
              simpa [emptyS, tz] using
                smt_typeof_seq_empty_typeof z T (by simpa [tz] using hzTy)
                  hEmptyNN
            have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
              simpa [nilS] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreEoTy
            have hResultTy : __smtx_typeof result = SmtType.Int := by
              change __smtx_typeof (SmtTerm.str_indexof tz ty tx) = SmtType.Int
              simp [typeof_str_indexof_eq, tz, ty, tx, hzTy, hyTy, hxTy,
                __smtx_typeof_str_indexof, native_ite, native_Teq]
            have hNeedleLenTy : __smtx_typeof needleLen = SmtType.Int := by
              simp [needleLen, ty, typeof_str_len_eq, hyTy,
                __smtx_typeof_seq_op_1_ret]
            have hCutTy : __smtx_typeof cut = SmtType.Int := by
              simp [cut, typeof_plus_eq, typeof_str_len_eq, hPreTy,
                hNeedleLenTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hSuffixRemainingTy :
                __smtx_typeof (SmtTerm.neg tailLen cut) = SmtType.Int := by
              simp [typeof_neg_eq, hTailLenTy, hCutTy,
                __smtx_typeof_arith_overload_op_2]
            have hSuffixTy : __smtx_typeof suffix = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tail cut (SmtTerm.neg tailLen cut)) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, hTailTy, hCutTy,
                hSuffixRemainingTy, __smtx_typeof_str_substr]
            have hTailDecompTy :
                __smtx_typeof tailDecomp = SmtType.Seq T := by
              simp [tailDecomp, typeof_str_concat_eq, hPreTy, hyTy,
                hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hNeedlePreTy :
                __smtx_typeof needlePre = SmtType.Seq T := by
              simp [needlePre, typeof_str_substr_eq, ty, hyTy, hNeedleLenTy,
                typeof_neg_eq, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hPriorHayTy : __smtx_typeof priorHay = SmtType.Seq T := by
              simp [priorHay, typeof_str_concat_eq, hPreTy, hNeedlePreTy,
                hNilTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
            have hContainsTy : __smtx_typeof contains = SmtType.Bool := by
              dsimp [contains]
              rw [typeof_str_contains_eq, hTailTy, hyTy]
              simp [__smtx_typeof_seq_op_2_ret, native_ite]
            have hInvalidTy : __smtx_typeof invalid = SmtType.Bool := by
              simp [invalid, typeof_or_eq, typeof_not_eq, typeof_gt_eq,
                hContainsTy, tx, hxTy, hSourceLenTy,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hResultEqNegTy :
                __smtx_typeof (resultEq (SmtTerm.Numeral (-1))) =
                  SmtType.Bool := by
              dsimp [resultEq]
              rw [typeof_eq_eq, hResultTy]
              simp [__smtx_typeof_eq, __smtx_typeof_guard,
                __smtx_typeof, native_ite, native_Teq]
            have hResultEqStartTy : __smtx_typeof (resultEq tx) =
                SmtType.Bool := by
              dsimp [resultEq]
              rw [typeof_eq_eq, hResultTy, hxTy]
              simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq]
            have hResultFoundTy : __smtx_typeof resultFound = SmtType.Int := by
              simp [resultFound, typeof_plus_eq, tx, hxTy, typeof_str_len_eq,
                hPreTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hPriorContainsTy :
                __smtx_typeof (SmtTerm.str_contains priorHay ty) =
                  SmtType.Bool := by
              rw [typeof_str_contains_eq, hPriorHayTy, hyTy]
              simp [__smtx_typeof_seq_op_2_ret, native_ite]
            have hNoPriorTy :
                __smtx_typeof
                    (SmtTerm.not (SmtTerm.str_contains priorHay ty)) =
                  SmtType.Bool := by
              rw [typeof_not_eq, hPriorContainsTy]
              simp [__smtx_typeof_guard, native_ite]
            have hResultFoundEqTy :
                __smtx_typeof (resultEq resultFound) = SmtType.Bool := by
              dsimp [resultEq]
              rw [typeof_eq_eq, hResultTy, hResultFoundTy]
              simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq]
            have hTailEqTy :
                __smtx_typeof (SmtTerm.eq tail tailDecomp) =
                  SmtType.Bool := by
              rw [typeof_eq_eq, hTailTy, hTailDecompTy]
              simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq]
            have hResultFoundTailTy :
                __smtx_typeof
                    (SmtTerm.and (resultEq resultFound)
                      (SmtTerm.Boolean true)) = SmtType.Bool := by
              rw [typeof_and_eq, hResultFoundEqTy]
              simp [__smtx_typeof, native_ite]
            have hNoPriorTailTy :
                __smtx_typeof
                    (SmtTerm.and
                      (SmtTerm.not (SmtTerm.str_contains priorHay ty))
                      (SmtTerm.and (resultEq resultFound)
                        (SmtTerm.Boolean true))) = SmtType.Bool := by
              rw [typeof_and_eq, hNoPriorTy, hResultFoundTailTy]
              simp [native_ite]
            have hFoundTy : __smtx_typeof foundCase = SmtType.Bool := by
              dsimp [foundCase]
              rw [typeof_and_eq, hTailEqTy, hNoPriorTailTy]
              simp [native_ite]
            have hFormulaEq :
                __eo_to_smt
                    (__str_reduction_pred
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
                  formula := by
              simp only [__str_reduction_pred, __eo_mk_apply, hZTermNe,
                hYTermNe, hXTermNe, hNilNe', hEmptyNe]
              rfl
            change eo_interprets M
              (__str_reduction_pred
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) true
            apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              rw [hFormulaEq]
              simp [formula, typeof_ite_eq, typeof_eq_eq, hInvalidTy,
                hResultEqNegTy, hEmptyTy, hyTy, hResultEqStartTy, hFoundTy,
                __smtx_typeof_ite, __smtx_typeof_eq, __smtx_typeof_guard,
                native_ite, native_Teq]
            · rw [hFormulaEq]
              have hZValTy :
                  __smtx_typeof_value (__smtx_model_eval M tz) =
                    SmtType.Seq T := by
                simpa [tz, hzTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt z) hZNN
              have hYValTy :
                  __smtx_typeof_value (__smtx_model_eval M ty) =
                    SmtType.Seq T := by
                simpa [ty, hyTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt y) hYNN
              have hXValTy :
                  __smtx_typeof_value (__smtx_model_eval M tx) =
                    SmtType.Int := by
                simpa [tx, hxTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt x) hXNN
              rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
              rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
              rcases int_value_canonical hXValTy with ⟨n, hXEval⟩
              have hSzTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
                simpa [hZEval, __smtx_typeof_value] using hZValTy
              have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
                simpa [hYEval, __smtx_typeof_value] using hYValTy
              have hElemZ : __smtx_elem_typeof_seq_value sz = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSzTy
              have hElemY : __smtx_elem_typeof_seq_value sy = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSyTy
              let zs := native_unpack_seq sz
              let ys := native_unpack_seq sy
              have hZPack : native_pack_seq T zs = sz := by
                simpa [zs, hElemZ] using native_pack_unpack_seq sz
              have hYPack : native_pack_seq T ys = sy := by
                simpa [ys, hElemY] using native_pack_unpack_seq sy
              have hSyEmptyIff : sy = SmtSeq.empty T ↔ ys = [] := by
                constructor
                · intro hEmpty
                  dsimp [ys]
                  rw [hEmpty]
                  rfl
                · intro hEmpty
                  rw [← hYPack, hEmpty]
                  rfl
              have hNilEval :
                  __smtx_model_eval M nilS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [nilS] using
                  eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreEoTy
              have hEmptyEval :
                  __smtx_model_eval M emptyS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [emptyS] using eval_seq_empty_typeof M z T
                  (by simpa [tz] using hzTy)
              by_cases hnNeg : n < 0
              · have hIndex : native_seq_indexof zs ys n = -1 := by
                  rw [native_seq_indexof_eq_rec]
                  simp [hnNeg]
                simp [formula, invalid, resultEq, result, resultFound,
                  foundCase, tailDecomp, priorHay, needlePre, suffix, cut,
                  needleLen, preS, tailIdx, tailLen, tail, sourceLen, contains,
                  sr_eval_boolean_term_eq, sr_eval_numeral_term_eq,
                  smtx_eval_ite_term_eq, smtx_eval_or_term_eq,
                  smtx_eval_and_term_eq, smtx_eval_eq_term_eq,
                  smtx_eval_not_term_eq, sr_eval_gt_term_eq,
                  sr_eval_str_contains_term_eq, sr_eval_str_indexof_term_eq,
                  StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                  StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                  smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                  StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                  sr_eval_neg_term_eq, __smtx_model_eval_ite,
                  __smtx_model_eval_or, __smtx_model_eval_and,
                  __smtx_model_eval_eq, __smtx_model_eval_not,
                  __smtx_model_eval_gt, __smtx_model_eval_lt,
                  __smtx_model_eval_str_contains,
                  __smtx_model_eval_str_indexof,
                  __smtx_model_eval_str_substr,
                  __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, hZEval, hYEval, hXEval, hNilEval,
                  hEmptyEval, native_seq_len, native_seq_concat, native_or,
                  native_and, native_not, native_zlt, native_zplus,
                  native_zneg, Smtm.native_unpack_pack_seq,
                  elem_typeof_pack_seq, native_unpack_seq, zs, ys, hElemZ,
                  hElemY, hZPack, hYPack, hSyEmptyIff, hnNeg, hIndex, native_veq,
                  native_pack_seq, Int.ofNat_eq_natCast]
              · have hnNonneg : 0 ≤ n := int_nonneg_of_not_neg hnNeg
                by_cases hnGt : Int.ofNat zs.length < n
                · have hIndex : native_seq_indexof zs ys n = -1 := by
                    rw [native_seq_indexof_eq_rec, if_neg hnNeg]
                    have hCast : (Int.toNat n : Int) = n :=
                      Int.toNat_of_nonneg hnNonneg
                    have hStartGt : zs.length < Int.toNat n := by
                      apply Int.ofNat_lt.mp
                      simpa [hCast] using hnGt
                    rw [dif_neg (by omega)]
                  have hnGt' : (zs.length : native_Int) < n := by
                    simpa [Int.ofNat_eq_natCast] using hnGt
                  simp [formula, invalid, resultEq, result, resultFound,
                    foundCase, tailDecomp, priorHay, needlePre, suffix, cut,
                    needleLen, preS, tailIdx, tailLen, tail, sourceLen,
                    contains, sr_eval_boolean_term_eq,
                    sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                    smtx_eval_or_term_eq, smtx_eval_and_term_eq,
                    smtx_eval_eq_term_eq, smtx_eval_not_term_eq,
                    sr_eval_gt_term_eq, sr_eval_str_contains_term_eq,
                    sr_eval_str_indexof_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                    smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                    StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                    sr_eval_neg_term_eq, __smtx_model_eval_ite,
                    __smtx_model_eval_or, __smtx_model_eval_and,
                    __smtx_model_eval_eq, __smtx_model_eval_not,
                    __smtx_model_eval_gt, __smtx_model_eval_lt,
                    __smtx_model_eval_str_contains,
                    __smtx_model_eval_str_indexof,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
                    __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                    __smtx_model_eval__, hZEval, hYEval, hXEval, hNilEval,
                    hEmptyEval, native_seq_len, native_seq_concat, native_or,
                    native_and, native_not, native_zlt, native_zplus,
                    native_zneg, Smtm.native_unpack_pack_seq,
                    elem_typeof_pack_seq, native_unpack_seq, zs, ys, hElemZ,
                    hElemY, hZPack, hYPack, hSyEmptyIff, hnNeg, hnNonneg,
                    hnGt, hnGt', hIndex,
                    native_veq, native_pack_seq, Int.ofNat_eq_natCast]
                · have hnLe : n ≤ Int.ofNat zs.length :=
                    Int.le_of_not_gt hnGt
                  have hnLe' : n ≤ (zs.length : native_Int) := by
                    simpa [Int.ofNat_eq_natCast] using hnLe
                  let j := Int.toNat n
                  have hCast : Int.ofNat j = n :=
                    Int.toNat_of_nonneg hnNonneg
                  have hCast' : (j : native_Int) = n := by
                    simpa [Int.ofNat_eq_natCast] using hCast
                  have hJLe : j ≤ zs.length := by
                    apply Int.ofNat_le.mp
                    calc
                      Int.ofNat j = n := hCast
                      _ ≤ Int.ofNat zs.length := hnLe
                  let ts := zs.drop j
                  have hTail :
                      native_seq_extract zs n (Int.ofNat zs.length - n) =
                        ts := by
                    simpa [ts, j] using
                      sr_native_seq_extract_to_end_of_bounds zs n hnNonneg hnLe
                  have hTail' :
                      native_seq_extract zs n ((zs.length : native_Int) + -n) =
                        ts := by
                    simpa [Int.ofNat_eq_natCast, Int.sub_eq_add_neg] using hTail
                  have hOffset :=
                    sr_native_seq_indexof_offset_drop_eq zs ys j hJLe
                  by_cases hContains : native_seq_contains ts ys = true
                  · by_cases hYs : ys = []
                    · have hTailIndex : native_seq_indexof ts ys 0 = 0 := by
                        simp [hYs, StrEqReplSupport.native_seq_indexof_nil_zero]
                      have hContains' :
                          native_seq_contains (List.drop j zs) ys = true := by
                        simpa [ts] using hContains
                      have hIndex : native_seq_indexof zs ys n = n := by
                        calc
                          native_seq_indexof zs ys n =
                              native_seq_indexof zs ys (Int.ofNat j) := by
                                rw [hCast]
                          _ = sr_native_seq_indexof_offset ts ys j := by
                            simpa [ts] using hOffset.symm
                          _ = Int.ofNat j := by
                            simp [sr_native_seq_indexof_offset, hTailIndex]
                          _ = n := hCast
                      have hInvalidFalse :
                          (!native_seq_contains (List.drop j zs) ys ||
                              decide ((zs.length : native_Int) < n)) = false := by
                        rw [hContains']
                        simp [hnLe']
                      have hInvalidFalse' :
                          (!native_seq_contains
                                (List.drop j (native_unpack_seq sz)) [] ||
                              decide
                                (((native_unpack_seq sz).length : native_Int) <
                                  n)) = false := by
                        simpa [zs, ys, hYs] using hInvalidFalse
                      have hIndex' :
                          native_seq_indexof (native_unpack_seq sz) [] n = n := by
                        simpa [zs, ys, hYs] using hIndex
                      simp [formula, invalid, resultEq, result, resultFound,
                        foundCase, tailDecomp, priorHay, needlePre, suffix, cut,
                        needleLen, preS, tailIdx, tailLen, tail, sourceLen,
                        contains, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                        smtx_eval_or_term_eq, smtx_eval_and_term_eq,
                        smtx_eval_eq_term_eq, smtx_eval_not_term_eq,
                        sr_eval_gt_term_eq, sr_eval_str_contains_term_eq,
                        sr_eval_str_indexof_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                        smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                        StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                        sr_eval_neg_term_eq, __smtx_model_eval_ite,
                        __smtx_model_eval_or, __smtx_model_eval_and,
                        __smtx_model_eval_eq, __smtx_model_eval_not,
                        __smtx_model_eval_gt, __smtx_model_eval_lt,
                        __smtx_model_eval_str_contains,
                        __smtx_model_eval_str_indexof,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_concat,
                        __smtx_model_eval_str_len,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_plus, __smtx_model_eval__, hZEval,
                        hYEval, hXEval, hNilEval, hEmptyEval, native_seq_len,
                        native_seq_concat, native_or, native_and, native_not,
                        native_zlt, native_zplus, native_zneg,
                        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                        native_unpack_seq, zs, ys, ts, hElemZ, hElemY, hZPack,
                        hYPack, hSyEmptyIff, hnNeg, hnNonneg, hnGt, hnLe,
                        hnLe', hCast', hTail, hTail', hContains, hContains',
                        hInvalidFalse, hInvalidFalse',
                        hYs, hTailIndex, hIndex, hIndex', native_veq,
                        native_pack_seq,
                        Int.ofNat_eq_natCast]
                    · have hTailIdxNonneg :
                          0 ≤ native_seq_indexof ts ys 0 := by
                        simpa [native_seq_contains] using hContains
                      have hTailIndexNe :
                          native_seq_indexof ts ys 0 ≠ -1 := by
                        intro hEq
                        have hBad : (0 : native_Int) ≤ -1 := by
                          rw [← hEq]
                          exact hTailIdxNonneg
                        exact (by decide : ¬ ((0 : native_Int) ≤ -1)) hBad
                      have hIndex :
                          native_seq_indexof zs ys n =
                            native_seq_indexof ts ys 0 + n := by
                        calc
                          native_seq_indexof zs ys n =
                              native_seq_indexof zs ys (Int.ofNat j) := by
                                rw [hCast]
                          _ = sr_native_seq_indexof_offset ts ys j := by
                            simpa [ts] using hOffset.symm
                          _ = native_seq_indexof ts ys 0 + Int.ofNat j := by
                            simp [sr_native_seq_indexof_offset, hTailIndexNe]
                          _ = native_seq_indexof ts ys 0 + n := by rw [hCast]
                      have hDecomp := native_seq_indexof_zero_decomp
                        ts ys hTailIdxNonneg
                      have hPreLen :=
                        native_seq_extract_prefix_length_of_indexof_nonneg
                          ts ys hTailIdxNonneg
                      have hMinimal :=
                        sr_native_seq_first_prefix_no_contains
                          ts ys hYs hTailIdxNonneg
                      have hContains' :
                          native_seq_contains (List.drop j zs) ys = true := by
                        simpa [ts] using hContains
                      have hDecomp' :
                          native_seq_extract (List.drop j zs) 0
                                (native_seq_indexof (List.drop j zs) ys 0) ++
                              ys ++
                              native_seq_extract (List.drop j zs)
                                (native_seq_indexof (List.drop j zs) ys 0 +
                                  Int.ofNat ys.length)
                                (Int.ofNat (List.drop j zs).length -
                                  (native_seq_indexof (List.drop j zs) ys 0 +
                                    Int.ofNat ys.length)) =
                            List.drop j zs := by
                        simpa [ts] using hDecomp
                      have hResultFound :
                          native_seq_indexof ts ys 0 + n =
                            n + Int.ofNat
                              (native_seq_extract ts 0
                                (native_seq_indexof ts ys 0)).length := by
                        rw [hPreLen]
                        exact Int.add_comm _ _
                      have hResultNonneg :
                          0 ≤ n + Int.ofNat
                            (native_seq_extract ts 0
                              (native_seq_indexof ts ys 0)).length :=
                        Int.add_nonneg hnNonneg (Int.natCast_nonneg _)
                      have hResultNe :
                          n + Int.ofNat
                              (native_seq_extract ts 0
                                (native_seq_indexof ts ys 0)).length ≠ -1 := by
                        intro hEq
                        have hBad : (0 : native_Int) ≤ -1 := by
                          rw [← hEq]
                          exact hResultNonneg
                        exact (by decide : ¬ ((0 : native_Int) ≤ -1)) hBad
                      have hInvalidFalse :
                          (!native_seq_contains (List.drop j zs) ys ||
                              decide ((zs.length : native_Int) < n)) = false := by
                        rw [hContains']
                        simp [hnLe']
                      have hTailPacked :
                          native_pack_seq T (List.drop j zs) =
                            native_pack_seq T
                              (native_seq_extract (List.drop j zs) 0
                                  (native_seq_indexof (List.drop j zs) ys 0) ++
                                (ys ++
                                  native_seq_extract (List.drop j zs)
                                    (((native_seq_extract (List.drop j zs) 0
                                        (native_seq_indexof (List.drop j zs) ys
                                          0)).length : native_Int) +
                                      (ys.length : native_Int))
                                    (((List.drop j zs).length : native_Int) +
                                      -(((native_seq_extract (List.drop j zs) 0
                                          (native_seq_indexof (List.drop j zs)
                                            ys 0)).length : native_Int) +
                                        (ys.length : native_Int))))) := by
                        have hPreLenDrop :
                            ((native_seq_extract (List.drop j zs) 0
                                (native_seq_indexof (List.drop j zs) ys 0)).length :
                                native_Int) =
                              native_seq_indexof (List.drop j zs) ys 0 := by
                          simpa [ts, Int.ofNat_eq_natCast] using hPreLen
                        apply congrArg (native_pack_seq T)
                        rw [hPreLenDrop, ← List.append_assoc,
                          ← Int.sub_eq_add_neg]
                        exact hDecomp'.symm
                      have hMinimal' :
                          native_seq_contains
                              (native_seq_extract (List.drop j zs) 0
                                  (native_seq_indexof (List.drop j zs) ys 0) ++
                                native_seq_extract ys 0
                                  ((ys.length : native_Int) + -1)) ys =
                            false := by
                        simpa [Int.ofNat_eq_natCast, Int.sub_eq_add_neg] using
                          hMinimal
                      have hInvalidFalse' :
                          (!native_seq_contains
                                (List.drop j (native_unpack_seq sz))
                                (native_unpack_seq sy) ||
                              decide
                                (((native_unpack_seq sz).length : native_Int) <
                                  n)) = false := by
                        simpa [zs, ys] using hInvalidFalse
                      have hTailPacked' :
                          native_pack_seq T
                              (List.drop j (native_unpack_seq sz)) =
                            native_pack_seq T
                              (native_seq_extract
                                  (List.drop j (native_unpack_seq sz)) 0
                                  (native_seq_indexof
                                    (List.drop j (native_unpack_seq sz))
                                    (native_unpack_seq sy) 0) ++
                                ((native_unpack_seq sy) ++
                                  native_seq_extract
                                    (List.drop j (native_unpack_seq sz))
                                    (((native_seq_extract
                                        (List.drop j (native_unpack_seq sz)) 0
                                        (native_seq_indexof
                                          (List.drop j (native_unpack_seq sz))
                                          (native_unpack_seq sy) 0)).length :
                                        native_Int) +
                                      ((native_unpack_seq sy).length :
                                        native_Int))
                                    (((List.drop j
                                        (native_unpack_seq sz)).length :
                                        native_Int) +
                                      -(((native_seq_extract
                                          (List.drop j (native_unpack_seq sz)) 0
                                          (native_seq_indexof
                                            (List.drop j (native_unpack_seq sz))
                                            (native_unpack_seq sy) 0)).length :
                                          native_Int) +
                                        ((native_unpack_seq sy).length :
                                          native_Int))))) := by
                        simpa [zs, ys] using hTailPacked
                      have hMinimal'' :
                          native_seq_contains
                              (native_seq_extract
                                  (List.drop j (native_unpack_seq sz)) 0
                                  (native_seq_indexof
                                    (List.drop j (native_unpack_seq sz))
                                    (native_unpack_seq sy) 0) ++
                                native_seq_extract (native_unpack_seq sy) 0
                                  (((native_unpack_seq sy).length :
                                    native_Int) + -1))
                              (native_unpack_seq sy) = false := by
                        simpa [zs, ys] using hMinimal'
                      have hnNotLtNative :
                          ¬ (((native_unpack_seq sz).length : native_Int) < n) := by
                        simpa [zs] using Int.not_lt_of_ge hnLe'
                      have hResultNeNative :
                          n +
                              ((native_seq_extract
                                (List.drop j (native_unpack_seq sz)) 0
                                (native_seq_indexof
                                  (List.drop j (native_unpack_seq sz))
                                  (native_unpack_seq sy) 0)).length :
                                native_Int) ≠ -1 := by
                        simpa [zs, ys, ts, Int.ofNat_eq_natCast] using
                          hResultNe
                      simp [formula, invalid, resultEq, result, resultFound,
                        foundCase, tailDecomp, priorHay, needlePre, suffix, cut,
                        needleLen, preS, tailIdx, tailLen, tail, sourceLen,
                        contains, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                        smtx_eval_or_term_eq, smtx_eval_and_term_eq,
                        smtx_eval_eq_term_eq, smtx_eval_not_term_eq,
                        sr_eval_gt_term_eq, sr_eval_str_contains_term_eq,
                        sr_eval_str_indexof_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                        smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                        StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                        sr_eval_neg_term_eq, __smtx_model_eval_ite,
                        __smtx_model_eval_or, __smtx_model_eval_and,
                        __smtx_model_eval_eq, __smtx_model_eval_not,
                        __smtx_model_eval_gt, __smtx_model_eval_lt,
                        __smtx_model_eval_str_contains,
                        __smtx_model_eval_str_indexof,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_concat,
                        __smtx_model_eval_str_len,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_plus, __smtx_model_eval__, hZEval,
                        hYEval, hXEval, hNilEval, hEmptyEval, native_seq_len,
                        native_seq_concat, native_or, native_and, native_not,
                        native_zlt, native_zplus, native_zneg,
                        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                        native_unpack_seq, zs, ys, ts, hElemZ, hElemY, hZPack,
                        hYPack, hSyEmptyIff, hnNeg, hnNonneg, hnGt, hnLe,
                        hnLe', hCast', hTail, hTail', hContains, hContains',
                        hInvalidFalse, hInvalidFalse',
                        hYs, hTailIdxNonneg, hIndex, hDecomp, hDecomp',
                        hPreLen, hResultFound, hResultNonneg, hResultNe,
                        hMinimal, hMinimal', hMinimal'', native_veq,
                        native_pack_seq,
                        Int.ofNat_eq_natCast, Int.sub_eq_add_neg,
                        List.append_assoc]
                      simp [hnNotLtNative, hResultNeNative, hTailPacked']
                  · have hContainsFalse : native_seq_contains ts ys = false := by
                      cases h : native_seq_contains ts ys
                      · rfl
                      · exact False.elim (hContains (by simpa using h))
                    have hTailIndex : native_seq_indexof ts ys 0 = -1 := by
                      rcases native_seq_indexof_eq_neg_one_or_ge ts ys 0 with
                        hNegOne | hGe
                      · exact hNegOne
                      · have hNonneg : 0 ≤ native_seq_indexof ts ys 0 := by
                          simpa using hGe
                        have : native_seq_contains ts ys = true := by
                          simpa [native_seq_contains] using hNonneg
                        rw [hContainsFalse] at this
                        contradiction
                    have hIndex : native_seq_indexof zs ys n = -1 := by
                      calc
                        native_seq_indexof zs ys n =
                            native_seq_indexof zs ys (Int.ofNat j) := by
                              rw [hCast]
                        _ = sr_native_seq_indexof_offset ts ys j := by
                          simpa [ts] using hOffset.symm
                        _ = -1 := by
                          simp [sr_native_seq_indexof_offset, hTailIndex]
                    simp [formula, invalid, resultEq, result, resultFound,
                      foundCase, tailDecomp, priorHay, needlePre, suffix, cut,
                      needleLen, preS, tailIdx, tailLen, tail, sourceLen,
                      contains, sr_eval_boolean_term_eq,
                      sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                      smtx_eval_or_term_eq, smtx_eval_and_term_eq,
                      smtx_eval_eq_term_eq, smtx_eval_not_term_eq,
                      sr_eval_gt_term_eq, sr_eval_str_contains_term_eq,
                      sr_eval_str_indexof_term_eq,
                      StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                      smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                      sr_eval_neg_term_eq, __smtx_model_eval_ite,
                      __smtx_model_eval_or, __smtx_model_eval_and,
                      __smtx_model_eval_eq, __smtx_model_eval_not,
                      __smtx_model_eval_gt, __smtx_model_eval_lt,
                      __smtx_model_eval_str_contains,
                      __smtx_model_eval_str_indexof,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
                      __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                      __smtx_model_eval__, hZEval, hYEval, hXEval, hNilEval,
                      hEmptyEval, native_seq_len, native_seq_concat, native_or,
                      native_and, native_not, native_zlt, native_zplus,
                      native_zneg, Smtm.native_unpack_pack_seq,
                      elem_typeof_pack_seq, native_unpack_seq, zs, ys, ts,
                      hElemZ, hElemY, hZPack, hYPack, hSyEmptyIff, hnNeg, hnNonneg, hnGt,
                      hnLe, hnLe', hCast', hTail, hTail', hContains,
                      hContainsFalse,
                      hTailIndex,
                      hIndex, native_veq, native_pack_seq,
                      Int.ofNat_eq_natCast, Int.sub_eq_add_neg]
          case str_update =>
            let selectedEo :=
              __eo_ite (__eo_is_eq (__str_value_len x) (Term.Numeral 1)) x
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_substr) x)
                    (Term.Numeral 0))
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.neg)
                      (Term.Apply (Term.UOp UserOp.str_len) z)) y))
            have hSelectedNe : selectedEo ≠ Term.Stuck := by
              intro hSelected
              apply hPredNe
              simp [__str_reduction_pred, selectedEo, hSelected,
                __eo_mk_apply]
            obtain ⟨shortcut, hShortcut⟩ :
                ∃ b : Bool,
                  __eo_is_eq (__str_value_len x) (Term.Numeral 1) =
                    Term.Boolean b := by
              rcases eo_ite_cases_of_ne_stuck
                  (__eo_is_eq (__str_value_len x) (Term.Numeral 1)) x
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_substr) x)
                      (Term.Numeral 0))
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.neg)
                        (Term.Apply (Term.UOp UserOp.str_len) z)) y))
                  hSelectedNe with hTrue | hFalse
              · exact ⟨true, hTrue⟩
              · exact ⟨false, hFalse⟩
            let tz := __eo_to_smt z
            let tn := __eo_to_smt y
            let tr := __eo_to_smt x
            have hOrigNN :
                term_has_non_none_type (SmtTerm.str_update tz tn tr) := by
              have hsimpa :=
                hTrans
              try simp [tz, tn, tr, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            rcases str_update_args_of_non_none hOrigNN with
              ⟨T, hzTy, hyTy, hxTy⟩
            have hZNN : term_has_non_none_type tz := by
              unfold term_has_non_none_type
              rw [hzTy]
              exact seq_ne_none T
            have hYNN : term_has_non_none_type tn := by
              unfold term_has_non_none_type
              rw [hyTy]
              decide
            have hXNN : term_has_non_none_type tr := by
              unfold term_has_non_none_type
              rw [hxTy]
              exact seq_ne_none T
            have hZTermNe : z ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation z (by
                have hsimpa := hZNN; (try simp [tz, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hYTermNe : y ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation y (by
                have hsimpa := hYNN; (try simp [tn, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hXTermNe : x ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation x (by
                have hsimpa := hXNN; (try simp [tr, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hTWf : __smtx_type_wf T = true :=
              (smt_seq_component_wf_of_non_none_type tz T hzTy).2
            have hTInh : type_inhabited T :=
              (smt_seq_component_wf_of_non_none_type tz T hzTy).1
            let sourceLen := SmtTerm.str_len tz
            let remaining := SmtTerm.neg sourceLen tn
            let selectedS := __eo_to_smt selectedEo
            let selectedLen := SmtTerm.str_len selectedS
            let mid := SmtTerm._at_purify
              (SmtTerm.str_substr tz tn selectedLen)
            let pre := srPurify
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z)
                  (Term.Numeral 0)) y)
            let preS := SmtTerm._at_purify
              (SmtTerm.str_substr tz (SmtTerm.Numeral 0) tn)
            have hPreTy : __smtx_typeof preS = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tz (SmtTerm.Numeral 0) tn) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, tn, hzTy, hyTy,
                __smtx_typeof_str_substr, __smtx_typeof, native_ite,
                native_Teq]
            have hPreEoTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              have hsimpa := hPreTy
              try simp [pre, preS, tz, tn] at hsimpa ⊢
              exact hsimpa
            have hNilNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                  Term.Stuck :=
              nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreEoTy
            have hNilNe' :
                __eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (srPurify
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_substr) z)
                            (Term.Numeral 0)) y))) ≠ Term.Stuck := by
              simpa [pre] using hNilNe
            let nilS := __eo_to_smt
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
            let next := SmtTerm.plus tn
              (SmtTerm.plus selectedLen (SmtTerm.Numeral 0))
            let suffix := SmtTerm._at_purify
              (SmtTerm.str_substr tz next (SmtTerm.neg sourceLen next))
            let result := SmtTerm._at_purify
              (SmtTerm.str_update tz tn tr)
            let updated := SmtTerm.str_concat preS
              (SmtTerm.str_concat selectedS
                (SmtTerm.str_concat suffix nilS))
            let original := SmtTerm.str_concat preS
              (SmtTerm.str_concat mid (SmtTerm.str_concat suffix nilS))
            let cond := SmtTerm.and (SmtTerm.geq tn (SmtTerm.Numeral 0))
              (SmtTerm.and (SmtTerm.gt sourceLen tn)
                (SmtTerm.Boolean true))
            let rhs := SmtTerm.and (SmtTerm.eq result updated)
              (SmtTerm.and (SmtTerm.eq tz original)
                (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) tn)
                  (SmtTerm.and
                    (SmtTerm.eq selectedLen (SmtTerm.str_len mid))
                    (SmtTerm.Boolean true))))
            let formula := SmtTerm.ite cond rhs (SmtTerm.eq result tz)
            have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
              simp [sourceLen, tz, typeof_str_len_eq, hzTy,
                __smtx_typeof_seq_op_1_ret]
            have hRemainingTy : __smtx_typeof remaining = SmtType.Int := by
              simp [remaining, hSourceLenTy, tn, hyTy, typeof_neg_eq,
                __smtx_typeof_arith_overload_op_2]
            have hSelectedTy : __smtx_typeof selectedS = SmtType.Seq T := by
              cases shortcut
              · have hSelectedEoEq :
                    selectedEo =
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_substr) x)
                          (Term.Numeral 0))
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.neg)
                            (Term.Apply (Term.UOp UserOp.str_len) z)) y)) := by
                  simp [selectedEo, hShortcut, __eo_ite, native_ite,
                    native_teq, SmtEval.native_ite]
                have hSelectedSEq :
                    selectedS =
                      SmtTerm.str_substr tr (SmtTerm.Numeral 0) remaining := by
                  rw [show selectedS = __eo_to_smt selectedEo from rfl,
                    hSelectedEoEq]
                  rfl
                rw [hSelectedSEq]
                rw [typeof_str_substr_eq, hxTy, hRemainingTy]
                rfl
              · simpa [selectedS, selectedEo, hShortcut, tr, __eo_ite,
                  native_ite, native_teq, SmtEval.native_ite] using hxTy
            have hSelectedLenTy :
                __smtx_typeof selectedLen = SmtType.Int := by
              simp [selectedLen, typeof_str_len_eq, hSelectedTy,
                __smtx_typeof_seq_op_1_ret]
            have hMidTy : __smtx_typeof mid = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tz tn selectedLen) = SmtType.Seq T
              simp [typeof_str_substr_eq, tz, hzTy, tn, hyTy,
                hSelectedLenTy, __smtx_typeof_str_substr]
            have hNextTy : __smtx_typeof next = SmtType.Int := by
              simp [next, tn, hyTy, hSelectedLenTy, typeof_plus_eq,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hSuffixRemainingTy :
                __smtx_typeof (SmtTerm.neg sourceLen next) = SmtType.Int := by
              simp [typeof_neg_eq, hSourceLenTy, hNextTy,
                __smtx_typeof_arith_overload_op_2]
            have hSuffixTy : __smtx_typeof suffix = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm.str_substr tz next (SmtTerm.neg sourceLen next)) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, hzTy, hNextTy,
                hSuffixRemainingTy, __smtx_typeof_str_substr]
            have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
              simpa [nilS] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T
                  hPreEoTy
            have hResultTy : __smtx_typeof result = SmtType.Seq T := by
              change __smtx_typeof (SmtTerm.str_update tz tn tr) =
                SmtType.Seq T
              simp [typeof_str_update_eq, tz, tn, tr, hzTy, hyTy, hxTy,
                __smtx_typeof_str_update, native_ite, native_Teq]
            have hUpdatedTy : __smtx_typeof updated = SmtType.Seq T := by
              simp [updated, typeof_str_concat_eq, hPreTy, hSelectedTy,
                hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hOriginalTy : __smtx_typeof original = SmtType.Seq T := by
              simp [original, typeof_str_concat_eq, hPreTy, hMidTy,
                hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hCondTy : __smtx_typeof cond = SmtType.Bool := by
              simp [cond, typeof_and_eq, typeof_geq_eq, typeof_gt_eq,
                tn, hyTy, hSourceLenTy,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hRhsTy : __smtx_typeof rhs = SmtType.Bool := by
              simp [rhs, typeof_and_eq, typeof_eq_eq, hResultTy, hUpdatedTy,
                tz, hzTy, hOriginalTy, hPreTy, tn, hyTy, hSelectedLenTy,
                hMidTy, __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hSelectedRawNe :
                __eo_ite (__eo_is_eq (__str_value_len x) (Term.Numeral 1)) x
                    (Term.Apply
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_substr) x)
                        (Term.Numeral 0))
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.neg)
                          (Term.Apply (Term.UOp UserOp.str_len) z)) y)) ≠
                  Term.Stuck := by
              simpa [selectedEo] using hSelectedNe
            have hFormulaEq :
                __eo_to_smt
                    (__str_reduction_pred
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
                  formula := by
              simp only [__str_reduction_pred, __eo_mk_apply, hZTermNe,
                hYTermNe, hXTermNe, hSelectedNe, hSelectedRawNe, hNilNe']
              rfl
            cases shortcut
            all_goals
              simp [hNilNe', hShortcut, __eo_ite, native_ite,
                native_teq, SmtEval.native_ite, __eo_mk_apply] at hBodyTy
              change eo_interprets M
                (__str_reduction_pred
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) true
              apply RuleProofs.eo_interprets_of_bool_eval M _ true
              · unfold RuleProofs.eo_has_bool_type
                rw [hFormulaEq]
                simp [formula, typeof_ite_eq, typeof_eq_eq, hCondTy, hRhsTy,
                  hResultTy, tz, hzTy, __smtx_typeof_ite,
                  __smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                  native_Teq]
              · rw [hFormulaEq]
                have hZValTy :
                    __smtx_typeof_value (__smtx_model_eval M tz) =
                      SmtType.Seq T := by
                  simpa [tz, hzTy] using
                    smt_model_eval_preserves_type_of_non_none M hM tz hZNN
                rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
                have hYValTy :
                    __smtx_typeof_value (__smtx_model_eval M tn) =
                      SmtType.Int := by
                  simpa [tn, hyTy] using
                    smt_model_eval_preserves_type_of_non_none M hM tn hYNN
                rcases int_value_canonical hYValTy with ⟨n, hNEval⟩
                have hXValTy :
                    __smtx_typeof_value (__smtx_model_eval M tr) =
                      SmtType.Seq T := by
                  simpa [tr, hxTy] using
                    smt_model_eval_preserves_type_of_non_none M hM tr hXNN
                rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
                have hSzTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
                  simpa [hZEval, __smtx_typeof_value] using hZValTy
                have hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
                  simpa [hXEval, __smtx_typeof_value] using hXValTy
                have hElemZ : __smtx_elem_typeof_seq_value sz = T :=
                  elem_typeof_seq_value_of_typeof_seq_value hSzTy
                have hElemX : __smtx_elem_typeof_seq_value sx = T :=
                  elem_typeof_seq_value_of_typeof_seq_value hSxTy
                let zs := native_unpack_seq sz
                let ys := native_unpack_seq sx
                have hZPack : native_pack_seq T zs = sz := by
                  simpa [zs, hElemZ] using native_pack_unpack_seq sz
                have hXPack : native_pack_seq T ys = sx := by
                  simpa [ys, hElemX] using native_pack_unpack_seq sx
                have hNilEval :
                    __smtx_model_eval M nilS =
                      SmtValue.Seq (SmtSeq.empty T) := by
                  simpa [nilS] using
                    eval_nil_str_concat_typeof_of_smt_type_seq M pre T
                      hPreEoTy
                by_cases hn0 : 0 ≤ n
                · by_cases hnLt : n < Int.ofNat zs.length
                  · let j := Int.toNat n
                    let chosen := ys.take (zs.length - j)
                    have hCast : Int.ofNat j = n := by
                      simpa [j] using Int.toNat_of_nonneg hn0
                    have hjLt : j < zs.length := by
                      apply Int.ofNat_lt.mp
                      calc
                        Int.ofNat j = n := hCast
                        _ < Int.ofNat zs.length := hnLt
                    have hRemaining :
                        Int.ofNat zs.length - n =
                          Int.ofNat (zs.length - j) := by
                      rw [← hCast]
                      exact (Int.ofNat_sub (Nat.le_of_lt hjLt)).symm
                    rcases sr_native_seq_update_active_facts zs ys n hn0 hnLt
                        with ⟨hUpdate, hSource, hPreLen, hChosenMidLen⟩
                    change native_seq_update zs n ys =
                        zs.take j ++ chosen ++ zs.drop (j + chosen.length)
                      at hUpdate
                    change zs = zs.take j ++
                        (zs.drop j).take chosen.length ++
                        zs.drop (j + chosen.length) at hSource
                    change (zs.take j).length = j at hPreLen
                    change chosen.length =
                        ((zs.drop j).take chosen.length).length
                      at hChosenMidLen
                    have hChosenLenLe : j + chosen.length ≤ zs.length := by
                      dsimp [chosen]
                      simp only [List.length_take]
                      omega
                    have hPrefixExtract :
                        native_seq_extract zs 0 n = zs.take j := by
                      rw [native_seq_extract_zero_eq_take zs n hn0]
                    have hMidExtract :
                        native_seq_extract zs n (Int.ofNat chosen.length) =
                          (zs.drop j).take chosen.length := by
                      simpa [j] using sr_native_seq_extract_valid_ofNat zs n
                        chosen.length hn0 hnLt
                    have hSuffixExtract :
                        native_seq_extract zs
                            (n + Int.ofNat chosen.length)
                            (Int.ofNat zs.length -
                              (n + Int.ofNat chosen.length)) =
                          zs.drop (j + chosen.length) := by
                      have hStartNonneg :
                          0 ≤ n + Int.ofNat chosen.length :=
                        Int.add_nonneg hn0 (Int.natCast_nonneg _)
                      have hStartLe :
                          n + Int.ofNat chosen.length ≤
                            Int.ofNat zs.length := by
                        rw [← hCast]
                        exact Int.ofNat_le.mpr hChosenLenLe
                      rw [sr_native_seq_extract_to_end_of_bounds zs
                        (n + Int.ofNat chosen.length) hStartNonneg hStartLe]
                      congr 1
                      have hSumCast :
                          Int.ofNat (j + chosen.length) =
                            n + Int.ofNat chosen.length := by
                        calc
                          Int.ofNat (j + chosen.length) =
                              Int.ofNat j + Int.ofNat chosen.length :=
                            (Int.ofNat_add_ofNat j chosen.length).symm
                          _ = n + Int.ofNat chosen.length := by rw [hCast]
                      apply Int.ofNat_inj.mp
                      calc
                        Int.ofNat
                            (Int.toNat (n + Int.ofNat chosen.length)) =
                            n + Int.ofNat chosen.length :=
                          Int.toNat_of_nonneg hStartNonneg
                        _ = Int.ofNat (j + chosen.length) := hSumCast.symm
                    have hSelectedEval :
                        __smtx_model_eval M selectedS =
                          SmtValue.Seq (native_pack_seq T chosen) := by
                      first
                      | have hLenEq :
                            __str_value_len x = Term.Numeral 1 :=
                          sr_eq_of_eo_is_eq_true
                            (__str_value_len x) (Term.Numeral 1) hShortcut
                        have hYsLen : ys.length = 1 := by
                          simpa [tr, ys, hXEval] using
                            sr_str_value_len_one_eval_length M x T sx
                              (by simpa [tr] using hxTy)
                              (by simpa [tr] using hXEval) hLenEq
                        have hChosenEq : chosen = ys := by
                          dsimp [chosen]
                          apply List.take_of_length_le
                          omega
                        simpa [selectedS, selectedEo, hShortcut, tr,
                          hChosenEq, hXPack, __eo_ite, native_ite,
                          native_teq, SmtEval.native_ite] using hXEval
                      | have hSelectedEoEq :
                            selectedEo =
                              (Term.Apply
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.str_substr) x)
                                  (Term.Numeral 0))
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.neg)
                                    (Term.Apply (Term.UOp UserOp.str_len) z))
                                  y)) := by
                          simp [selectedEo, hShortcut, __eo_ite, native_ite,
                            native_teq, SmtEval.native_ite]
                        rw [show selectedS = __eo_to_smt selectedEo from rfl,
                          hSelectedEoEq]
                        have hXEval' :
                            __smtx_model_eval M (__eo_to_smt x) =
                              SmtValue.Seq sx := by
                          simpa [tr] using hXEval
                        have hZEval' :
                            __smtx_model_eval M (__eo_to_smt z) =
                              SmtValue.Seq sz := by
                          simpa [tz] using hZEval
                        have hNEval' :
                            __smtx_model_eval M (__eo_to_smt y) =
                              SmtValue.Numeral n := by
                          simpa [tn] using hNEval
                        have hRemaining' :
                            (zs.length : native_Int) + -n =
                              Int.ofNat (zs.length - j) := by
                          simpa [Int.ofNat_eq_natCast, Int.sub_eq_add_neg]
                            using hRemaining
                        change __smtx_model_eval M
                            (SmtTerm.str_substr tr (SmtTerm.Numeral 0)
                              remaining) =
                          SmtValue.Seq (native_pack_seq T chosen)
                        rw [StrSubstrContainsSupport.smtx_eval_str_substr_term_eq]
                        simp [remaining, sourceLen, tr, tz, tn, hXEval,
                          hZEval, hNEval, hXEval', hZEval', hNEval',
                          __smtx_model_eval, __smtx_model_eval_str_substr,
                          __smtx_model_eval__, __smtx_model_eval_str_len,
                          native_seq_len, native_zplus, native_zneg,
                          native_seq_extract_zero_eq_take, hRemaining',
                          hElemX, chosen, zs, ys,
                          Smtm.native_unpack_pack_seq]
                    dsimp [zs, ys] at hnLt hUpdate hSource hPreLen hChosenMidLen hPrefixExtract hMidExtract hSuffixExtract hSelectedEval hZPack hXPack hChosenLenLe
                    have hCondEval :
                        __smtx_model_eval M cond = SmtValue.Boolean true := by
                      simp [cond, sourceLen, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, smtx_eval_and_term_eq,
                        StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                        sr_eval_gt_term_eq, smtx_eval_str_len_term_eq,
                        __smtx_model_eval_and, __smtx_model_eval_geq,
                        __smtx_model_eval_leq, __smtx_model_eval_gt,
                        __smtx_model_eval_lt, __smtx_model_eval_str_len,
                        hZEval, hNEval, native_seq_len, native_and,
                        native_zleq, native_zlt, hn0, hnLt,
                        Int.ofNat_eq_natCast]
                    change __smtx_model_eval M
                        (SmtTerm.ite cond rhs (SmtTerm.eq result tz)) =
                      SmtValue.Boolean true
                    rw [smtx_eval_ite_term_eq, hCondEval]
                    simp only [__smtx_model_eval_ite]
                    have hPreEval :
                        __smtx_model_eval M preS =
                          SmtValue.Seq (native_pack_seq T (zs.take j)) := by
                      simp [preS, sr_eval_purify_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                        sr_eval_numeral_term_eq, __smtx_model_eval__at_purify,
                        __smtx_model_eval_str_substr, hZEval, hNEval,
                        hPrefixExtract, hElemZ, zs]
                    have hMidEval :
                        __smtx_model_eval M mid =
                          SmtValue.Seq
                            (native_pack_seq T
                              ((zs.drop j).take chosen.length)) := by
                      simp [mid, selectedLen, sr_eval_purify_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                        smtx_eval_str_len_term_eq,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_len, hZEval, hNEval,
                        hSelectedEval, hMidExtract, hElemZ, zs,
                        native_seq_len, Smtm.native_unpack_pack_seq,
                        elem_typeof_pack_seq]
                    have hSuffixEval :
                        __smtx_model_eval M suffix =
                          SmtValue.Seq
                            (native_pack_seq T
                              (zs.drop (j + chosen.length))) := by
                      simp [suffix, next, selectedLen, sourceLen,
                        sr_eval_purify_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                        StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                        sr_eval_neg_term_eq, smtx_eval_str_len_term_eq,
                        sr_eval_numeral_term_eq,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_plus, __smtx_model_eval__,
                        __smtx_model_eval_str_len, hZEval, hNEval,
                        hSelectedEval, hSuffixExtract, hElemZ, zs,
                        native_seq_len, native_zplus, native_zneg,
                        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                        Int.ofNat_eq_natCast, Int.sub_eq_add_neg]
                      apply congrArg (native_pack_seq T)
                      simpa [Int.sub_eq_add_neg] using hSuffixExtract
                    have hResultEval :
                        __smtx_model_eval M result =
                          SmtValue.Seq
                            (native_pack_seq T
                              (zs.take j ++ chosen ++
                                zs.drop (j + chosen.length))) := by
                      simp [result, sr_eval_purify_term_eq,
                        sr_eval_str_update_term_eq,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_str_update, hZEval, hNEval,
                        hXEval, hUpdate, hElemZ, zs, ys]
                    have hUpdatedEval :
                        __smtx_model_eval M updated =
                          SmtValue.Seq
                            (native_pack_seq T
                              (zs.take j ++ chosen ++
                                zs.drop (j + chosen.length))) := by
                      simp [updated,
                        StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                        __smtx_model_eval_str_concat, hPreEval,
                        hSelectedEval, hSuffixEval, hNilEval,
                        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                        native_unpack_seq, native_seq_concat,
                        List.append_assoc]
                    have hOriginalEval :
                        __smtx_model_eval M original = SmtValue.Seq sz := by
                      simp [original,
                        StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                        __smtx_model_eval_str_concat, hPreEval, hMidEval,
                        hSuffixEval, hNilEval, Smtm.native_unpack_pack_seq,
                        elem_typeof_pack_seq, native_unpack_seq,
                        native_seq_concat, hSource, hZPack,
                        List.append_assoc]
                      calc
                        native_pack_seq T
                            (zs.take j ++
                              ((zs.drop j).take chosen.length ++
                                zs.drop (j + chosen.length))) =
                            native_pack_seq T zs := by
                          apply congrArg (native_pack_seq T)
                          simpa [List.append_assoc, zs] using hSource.symm
                        _ = sz := hZPack
                    have hPreLenEval :
                        __smtx_model_eval M (SmtTerm.str_len preS) =
                          SmtValue.Numeral n := by
                      simp [smtx_eval_str_len_term_eq,
                        __smtx_model_eval_str_len, hPreEval, native_seq_len,
                        Smtm.native_unpack_pack_seq, hPreLen, hCast,
                        Int.ofNat_eq_natCast]
                      have hTakeLen :
                          Int.ofNat (min j zs.length) = n := by
                        calc
                          Int.ofNat (min j zs.length) = Int.ofNat j := by
                            exact congrArg Int.ofNat (by
                              simpa [List.length_take] using hPreLen)
                          _ = n := hCast
                      exact hTakeLen
                    have hSelectedLenEval :
                        __smtx_model_eval M selectedLen =
                          SmtValue.Numeral (Int.ofNat chosen.length) := by
                      simp [selectedLen, smtx_eval_str_len_term_eq,
                        __smtx_model_eval_str_len, hSelectedEval,
                        native_seq_len, Smtm.native_unpack_pack_seq]
                    have hMidLenEval :
                        __smtx_model_eval M (SmtTerm.str_len mid) =
                          SmtValue.Numeral (Int.ofNat chosen.length) := by
                      rw [smtx_eval_str_len_term_eq, hMidEval]
                      have hUnpack :
                          native_unpack_seq
                              (native_pack_seq T
                                ((zs.drop j).take chosen.length)) =
                            (zs.drop j).take chosen.length := by
                        simp [Smtm.native_unpack_pack_seq,
                          elem_typeof_pack_seq]
                      simp only [__smtx_model_eval_str_len, hUnpack,
                        native_seq_len]
                      rw [← hChosenMidLen]
                    have hResultEqEval :
                        __smtx_model_eval M (SmtTerm.eq result updated) =
                          SmtValue.Boolean true := by
                      simp [smtx_eval_eq_term_eq, __smtx_model_eval_eq,
                        hResultEval, hUpdatedEval, native_veq]
                    have hSourceEqEval :
                        __smtx_model_eval M (SmtTerm.eq tz original) =
                          SmtValue.Boolean true := by
                      simp [smtx_eval_eq_term_eq, __smtx_model_eval_eq,
                        hZEval, hOriginalEval, native_veq]
                    have hPreLenEqEval :
                        __smtx_model_eval M
                            (SmtTerm.eq (SmtTerm.str_len preS) tn) =
                          SmtValue.Boolean true := by
                      simp [smtx_eval_eq_term_eq, __smtx_model_eval_eq,
                        hPreLenEval, hNEval, native_veq]
                    have hMidLenEqEval :
                        __smtx_model_eval M
                            (SmtTerm.eq selectedLen (SmtTerm.str_len mid)) =
                          SmtValue.Boolean true := by
                      simp [smtx_eval_eq_term_eq, __smtx_model_eval_eq,
                        hSelectedLenEval, hMidLenEval, native_veq]
                    simp [rhs, smtx_eval_and_term_eq,
                      sr_eval_boolean_term_eq, __smtx_model_eval_and,
                      hResultEqEval, hSourceEqEval, hPreLenEqEval,
                      hMidLenEqEval, native_and]
                  · have hHigh : Int.ofNat zs.length ≤ n :=
                      Int.le_of_not_gt hnLt
                    have hHigh' : (zs.length : native_Int) ≤ n := by
                      simpa [Int.ofNat_eq_natCast] using hHigh
                    have hUpdate :=
                      sr_native_seq_update_eq_self_of_invalid zs ys n
                        (Or.inr hHigh)
                    dsimp [zs, ys] at hHigh hHigh' hUpdate hZPack hXPack
                    have hCondEval :
                        __smtx_model_eval M cond = SmtValue.Boolean false := by
                      simp [cond, sourceLen, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, smtx_eval_and_term_eq,
                        StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                        sr_eval_gt_term_eq, smtx_eval_str_len_term_eq,
                        __smtx_model_eval_and, __smtx_model_eval_geq,
                        __smtx_model_eval_leq, __smtx_model_eval_gt,
                        __smtx_model_eval_lt, __smtx_model_eval_str_len,
                        hZEval, hNEval, native_seq_len, native_and,
                        native_zleq, native_zlt, hHigh',
                        Int.ofNat_eq_natCast]
                    change __smtx_model_eval M
                        (SmtTerm.ite cond rhs (SmtTerm.eq result tz)) =
                      SmtValue.Boolean true
                    rw [smtx_eval_ite_term_eq, hCondEval]
                    simp only [__smtx_model_eval_ite]
                    simp [result,
                      preS, mid, suffix, next, selectedLen, sourceLen,
                      selectedS, nilS, sr_eval_boolean_term_eq,
                      sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                      smtx_eval_and_term_eq, smtx_eval_eq_term_eq,
                      StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                      sr_eval_gt_term_eq, sr_eval_str_update_term_eq,
                      StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                      smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                      sr_eval_neg_term_eq,
                      __smtx_model_eval_ite, __smtx_model_eval_and,
                      __smtx_model_eval_eq, __smtx_model_eval_geq,
                      __smtx_model_eval_leq, __smtx_model_eval_gt,
                      __smtx_model_eval_lt, __smtx_model_eval_str_update,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval__at_purify, hZEval, hNEval, hXEval,
                      hElemZ, hHigh, hHigh', hUpdate, hZPack, native_seq_len,
                      native_and, native_zleq, native_zlt, native_veq,
                      Int.ofNat_eq_natCast]
                · have hnNeg : n < 0 := Int.lt_of_not_ge hn0
                  have hUpdate :=
                    sr_native_seq_update_eq_self_of_invalid zs ys n
                      (Or.inl hnNeg)
                  dsimp [zs, ys] at hUpdate hZPack hXPack
                  have hCondEval :
                      __smtx_model_eval M cond = SmtValue.Boolean false := by
                    simp [cond, sourceLen, sr_eval_boolean_term_eq,
                      sr_eval_numeral_term_eq, smtx_eval_and_term_eq,
                      StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                      sr_eval_gt_term_eq, smtx_eval_str_len_term_eq,
                      __smtx_model_eval_and, __smtx_model_eval_geq,
                      __smtx_model_eval_leq, __smtx_model_eval_gt,
                      __smtx_model_eval_lt, __smtx_model_eval_str_len,
                      hZEval, hNEval, native_seq_len, native_and,
                      native_zleq, native_zlt, hn0, hnNeg]
                  change __smtx_model_eval M
                      (SmtTerm.ite cond rhs (SmtTerm.eq result tz)) =
                    SmtValue.Boolean true
                  rw [smtx_eval_ite_term_eq, hCondEval]
                  simp only [__smtx_model_eval_ite]
                  simp [result,
                    preS, mid, suffix, next, selectedLen, sourceLen,
                    selectedS, nilS, sr_eval_boolean_term_eq,
                    sr_eval_numeral_term_eq, smtx_eval_ite_term_eq,
                    smtx_eval_and_term_eq, smtx_eval_eq_term_eq,
                    StrSubstrContainsSupport.smtx_eval_geq_term_eq,
                    sr_eval_gt_term_eq, sr_eval_str_update_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                    StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
                    smtx_eval_str_len_term_eq, sr_eval_purify_term_eq,
                    StrSubstrContainsSupport.smtx_eval_plus_term_eq,
                    sr_eval_neg_term_eq,
                    __smtx_model_eval_ite, __smtx_model_eval_and,
                    __smtx_model_eval_eq, __smtx_model_eval_geq,
                    __smtx_model_eval_leq, __smtx_model_eval_gt,
                    __smtx_model_eval_lt, __smtx_model_eval_str_update,
                    __smtx_model_eval_str_len,
                    __smtx_model_eval__at_purify, hZEval, hNEval, hXEval,
                    hElemZ, hnNeg, hUpdate, hZPack, native_seq_len,
                    native_and, native_zleq, native_zlt, native_veq,
                    Int.ofNat_eq_natCast]
          case str_replace_all =>
            exact StrReplaceAllCase.str_replace_all_reduction_pred_true
              M hM z y x hTrans hClosed
          case str_replace_re =>
            exact StrReplaceReCase.str_replace_re_reduction_pred_true
              M hM z y x hTrans hClosed
          case str_replace_re_all =>
            exact StrReplaceReAllCase.str_replace_re_all_reduction_pred_true
              M hM z y x hTrans hClosed
          case str_indexof_re =>
            let ts := __eo_to_smt z
            let tr := __eo_to_smt y
            let tn := __eo_to_smt x
            have hOrigNN :
                term_has_non_none_type (SmtTerm.str_indexof_re ts tr tn) := by
              have hsimpa := hTrans
              try simp [ts, tr, tn, RuleProofs.eo_has_smt_translation] at hsimpa ⊢
              exact hsimpa
            rcases str_indexof_re_args_of_non_none hOrigNN with
              ⟨hsTy, hrTy, hnTy⟩
            have hSNN : term_has_non_none_type ts := by
              unfold term_has_non_none_type
              rw [hsTy]
              exact seq_ne_none SmtType.Char
            have hRNN : term_has_non_none_type tr := by
              unfold term_has_non_none_type
              rw [hrTy]
              decide
            have hNNN : term_has_non_none_type tn := by
              unfold term_has_non_none_type
              rw [hnTy]
              decide
            have hSTermNe : z ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation z (by
                have hsimpa := hSNN; (try simp [ts, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hRTermNe : y ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation y (by
                have hsimpa := hRNN; (try simp [tr, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hNTermNe : x ≠ Term.Stuck :=
              RuleProofs.term_ne_stuck_of_has_smt_translation x (by
                have hsimpa := hNNN; (try simp [tn, RuleProofs.eo_has_smt_translation] at hsimpa ⊢); exact hsimpa)
            have hClosedArgs :
                __eo_is_closed z = Term.Boolean true ∧
                  __eo_is_closed y = Term.Boolean true ∧
                    __eo_is_closed x = Term.Boolean true := by
              apply sr_eo_is_closed_ternary_uop_args UserOp.str_indexof_re z y x
              · decide
              · decide
              · exact hSTermNe
              · exact hRTermNe
              · exact hNTermNe
              · exact hClosed
            let idxName := native_string_lit "@var.str_index"
            let lenName := native_string_lit "@var.str_length"
            let ivar := SmtTerm.Var idxName SmtType.Int
            let lvar := SmtTerm.Var lenName SmtType.Int
            let result := SmtTerm._at_purify
              (SmtTerm.str_indexof_re ts tr tn)
            let sourceLen := SmtTerm.str_len ts
            let resultEq := SmtTerm.eq result
            let notFound := resultEq (SmtTerm.Numeral (-1))
            let endIndex := SmtTerm.ite notFound sourceLen result
            let qMatch := SmtTerm.str_in_re
              (SmtTerm.str_substr ts ivar lvar) tr
            let qBody := SmtTerm.or (SmtTerm.not (SmtTerm.geq ivar tn))
              (SmtTerm.or (SmtTerm.not (SmtTerm.lt ivar endIndex))
                (SmtTerm.or (SmtTerm.not (SmtTerm.gt lvar (SmtTerm.Numeral 0)))
                  (SmtTerm.or
                    (SmtTerm.not
                      (SmtTerm.leq lvar (SmtTerm.neg sourceLen ivar)))
                    (SmtTerm.or (SmtTerm.not qMatch)
                      (SmtTerm.Boolean false)))))
            let minimal := SmtTerm.not
              (SmtTerm.exists idxName SmtType.Int
                (SmtTerm.exists lenName SmtType.Int (SmtTerm.not qBody)))
            let foundMatch := SmtTerm.str_in_re
              (SmtTerm.str_substr ts result lvar) tr
            let foundBody := SmtTerm.or
              (SmtTerm.not (SmtTerm.geq lvar (SmtTerm.Numeral 0)))
              (SmtTerm.or
                (SmtTerm.not
                  (SmtTerm.leq lvar (SmtTerm.neg sourceLen result)))
                (SmtTerm.or (SmtTerm.not foundMatch)
                  (SmtTerm.Boolean false)))
            let foundForall := SmtTerm.not
              (SmtTerm.exists lenName SmtType.Int (SmtTerm.not foundBody))
            let foundClause := SmtTerm.or notFound
              (SmtTerm.or
                (SmtTerm.and (SmtTerm.geq result tn)
                  (SmtTerm.and (SmtTerm.not foundForall)
                    (SmtTerm.Boolean true)))
                (SmtTerm.Boolean false))
            let characterized := SmtTerm.and minimal
              (SmtTerm.and foundClause (SmtTerm.Boolean true))
            let invalid := SmtTerm.or (SmtTerm.gt tn sourceLen)
              (SmtTerm.or (SmtTerm.gt (SmtTerm.Numeral 0) tn)
                (SmtTerm.Boolean false))
            let emptyMatch := SmtTerm.str_in_re (SmtTerm.String []) tr
            let formula := SmtTerm.ite invalid notFound
              (SmtTerm.ite emptyMatch (resultEq tn) characterized)
            have hResultTy : __smtx_typeof result = SmtType.Int := by
              change __smtx_typeof (SmtTerm.str_indexof_re ts tr tn) =
                SmtType.Int
              simp [typeof_str_indexof_re_eq, hsTy, hrTy, hnTy,
                native_ite, native_Teq]
            have hSourceLenTy : __smtx_typeof sourceLen = SmtType.Int := by
              simp [sourceLen, typeof_str_len_eq, hsTy,
                __smtx_typeof_seq_op_1_ret]
            have hNotFoundTy : __smtx_typeof notFound = SmtType.Bool := by
              simp [notFound, resultEq, typeof_eq_eq, hResultTy,
                __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof,
                native_ite, native_Teq]
            have hEndIndexTy : __smtx_typeof endIndex = SmtType.Int := by
              simp [endIndex, typeof_ite_eq, hNotFoundTy, hSourceLenTy,
                hResultTy, __smtx_typeof_ite, native_ite, native_Teq]
            have hQMatchTy : __smtx_typeof qMatch = SmtType.Bool := by
              simp [qMatch, typeof_str_in_re_eq, typeof_str_substr_eq,
                hsTy, hrTy, ivar, lvar, __smtx_typeof_str_substr,
                __smtx_typeof_seq_op_2_ret, __smtx_typeof_guard_wf,
                __smtx_type_wf, __smtx_type_wf_component,
                __smtx_type_wf_rec,
                __smtx_typeof, native_and, native_ite, native_Teq]
            have hQBodyTy : __smtx_typeof qBody = SmtType.Bool := by
              simp [qBody, typeof_or_eq, typeof_not_eq, typeof_geq_eq,
                typeof_lt_eq, typeof_gt_eq, typeof_leq_eq, typeof_neg_eq,
                ivar, lvar, hnTy, hEndIndexTy, hSourceLenTy, hQMatchTy,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof_guard,
                __smtx_typeof_guard_wf, __smtx_type_wf,
                __smtx_type_wf_component, __smtx_type_wf_rec,
                __smtx_typeof, native_and,
                native_ite, native_Teq]
            have hMinimalTy : __smtx_typeof minimal = SmtType.Bool := by
              simp [minimal, typeof_not_eq, smtx_typeof_exists_term_eq,
                typeof_not_eq, hQBodyTy, sr_smt_type_wf_int,
                __smtx_typeof_guard_wf, __smtx_typeof_guard, native_ite]
            have hFoundMatchTy : __smtx_typeof foundMatch = SmtType.Bool := by
              simp [foundMatch, typeof_str_in_re_eq, typeof_str_substr_eq,
                hsTy, hrTy, hResultTy, lvar, __smtx_typeof_str_substr,
                __smtx_typeof_seq_op_2_ret, __smtx_typeof_guard_wf,
                __smtx_type_wf, __smtx_type_wf_component,
                __smtx_type_wf_rec,
                __smtx_typeof, native_and, native_ite, native_Teq]
            have hFoundBodyTy : __smtx_typeof foundBody = SmtType.Bool := by
              simp [foundBody, typeof_or_eq, typeof_not_eq, typeof_geq_eq,
                typeof_leq_eq, typeof_neg_eq, lvar, hSourceLenTy, hResultTy,
                hFoundMatchTy, __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof_guard,
                __smtx_typeof_guard_wf, __smtx_type_wf,
                __smtx_type_wf_component, __smtx_type_wf_rec,
                __smtx_typeof, native_and,
                native_ite, native_Teq]
            have hFoundForallTy :
                __smtx_typeof foundForall = SmtType.Bool := by
              simp [foundForall, typeof_not_eq, smtx_typeof_exists_term_eq,
                hFoundBodyTy, sr_smt_type_wf_int, __smtx_typeof_guard_wf,
                __smtx_typeof_guard, native_ite]
            have hFoundClauseTy :
                __smtx_typeof foundClause = SmtType.Bool := by
              simp [foundClause, typeof_or_eq, typeof_and_eq, typeof_not_eq,
                typeof_geq_eq, hNotFoundTy, hResultTy, hnTy,
                hFoundForallTy, __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hCharacterizedTy :
                __smtx_typeof characterized = SmtType.Bool := by
              simp [characterized, typeof_and_eq, hMinimalTy,
                hFoundClauseTy, __smtx_typeof, native_ite]
            have hInvalidTy : __smtx_typeof invalid = SmtType.Bool := by
              simp [invalid, typeof_or_eq, typeof_gt_eq, hnTy,
                hSourceLenTy, __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hEmptyMatchTy :
                __smtx_typeof emptyMatch = SmtType.Bool := by
              have hEmptyValid : native_string_valid [] = true := by
                native_decide
              simp [emptyMatch, typeof_str_in_re_eq, hrTy,
                __smtx_typeof_seq_op_2_ret, __smtx_typeof, hEmptyValid,
                native_ite, native_Teq]
            have hResultStartTy :
                __smtx_typeof (resultEq tn) = SmtType.Bool := by
              simp [resultEq, typeof_eq_eq, hResultTy, hnTy,
                __smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq]
            have hFormulaEq :
                __eo_to_smt
                    (__str_reduction_pred
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
                  formula := by
              simp only [__str_reduction_pred, __eo_mk_apply, hSTermNe,
                hRTermNe, hNTermNe]
              rfl
            change eo_interprets M
              (__str_reduction_pred
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) true
            apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              rw [hFormulaEq]
              simp [formula, typeof_ite_eq, hInvalidTy, hNotFoundTy,
                hEmptyMatchTy, hResultStartTy, hCharacterizedTy,
                __smtx_typeof_ite, native_ite, native_Teq]
            · rw [hFormulaEq]
              have hSValTy :
                  __smtx_typeof_value (__smtx_model_eval M ts) =
                    SmtType.Seq SmtType.Char := by
                simpa [ts, hsTy] using
                  smt_model_eval_preserves_type_of_non_none M hM ts hSNN
              rcases seq_value_canonical hSValTy with ⟨ss, hSEval⟩
              have hSsTy :
                  __smtx_typeof_seq_value ss =
                    SmtType.Seq SmtType.Char := by
                simpa [hSEval, __smtx_typeof_value] using hSValTy
              let source := native_unpack_string ss
              have hSourceValid : native_string_valid source = true :=
                native_unpack_string_valid_of_typeof_seq_char hSsTy
              have hSourcePack : native_pack_string source = ss :=
                sr_native_pack_unpack_string ss hSsTy
              have hSEvalString :
                  __smtx_model_eval M ts =
                    SmtValue.Seq (native_pack_string source) := by
                rw [hSourcePack]
                exact hSEval
              have hRValTy :
                  __smtx_typeof_value (__smtx_model_eval M tr) =
                    SmtType.RegLan := by
                simpa [tr, hrTy] using
                  smt_model_eval_preserves_type_of_non_none M hM tr hRNN
              rcases reglan_value_canonical hRValTy with ⟨regex, hREval⟩
              have hNValTy :
                  __smtx_typeof_value (__smtx_model_eval M tn) =
                    SmtType.Int := by
                simpa [tn, hnTy] using
                  smt_model_eval_preserves_type_of_non_none M hM tn hNNN
              rcases int_value_canonical hNValTy with ⟨start, hNEval⟩
              let nativeResult := native_str_indexof_re source regex start
              have hResultEval :
                  __smtx_model_eval M result =
                    SmtValue.Numeral nativeResult := by
                simp [result, nativeResult, sr_eval_purify_term_eq,
                  sr_eval_str_indexof_re_term_eq,
                  __smtx_model_eval__at_purify,
                  __smtx_model_eval_str_indexof_re, hSEvalString, hREval,
                  hNEval, sr_native_unpack_pack_string]
              have hSourceLenEval :
                  __smtx_model_eval M sourceLen =
                    SmtValue.Numeral (source.length : Int) := by
                simp [sourceLen, smtx_eval_str_len_term_eq,
                  __smtx_model_eval_str_len, hSEvalString, native_seq_len,
                  sr_native_unpack_pack_string_length, source]
              have hEmptyMatchEval :
                  __smtx_model_eval M emptyMatch =
                    SmtValue.Boolean (native_str_in_re [] regex) := by
                have hEmptyStringEval :
                    __smtx_model_eval M (SmtTerm.String []) =
                      SmtValue.Seq (native_pack_string []) := by
                  rw [__smtx_model_eval.eq_def]
                simp [emptyMatch, sr_eval_str_in_re_term_eq,
                  __smtx_model_eval_str_in_re, hREval, hEmptyStringEval,
                  sr_native_unpack_pack_string]
              have hSem := StringReductionRegex.search_semantics_int
                source regex start hSourceValid
              change (if start > (source.length : Int) ∨ 0 > start then
                  nativeResult = -1
                else if native_str_in_re [] regex then
                  nativeResult = start
                else
                  (∀ j k : Int,
                    ¬ start ≤ j ∨
                    ¬ j < (if nativeResult = -1 then
                      (source.length : Int) else nativeResult) ∨
                    ¬ 0 < k ∨
                    ¬ k ≤ (source.length : Int) - j ∨
                    native_str_in_re (native_str_substr source j k) regex =
                      false) ∧
                  (nativeResult = -1 ∨
                    start ≤ nativeResult ∧
                      ∃ k : Int, 0 ≤ k ∧
                        k ≤ (source.length : Int) - nativeResult ∧
                        native_str_in_re
                          (native_str_substr source nativeResult k) regex =
                            true)) at hSem
              by_cases hInvalid :
                  start > (source.length : Int) ∨ 0 > start
              · rw [if_pos hInvalid] at hSem
                have hInvalidEval :
                    __smtx_model_eval M invalid = SmtValue.Boolean true := by
                  rcases hInvalid with hHigh | hNeg
                  · simp [invalid, sr_eval_gt_term_eq,
                      smtx_eval_or_term_eq, sr_eval_numeral_term_eq,
                      sr_eval_boolean_term_eq,
                      __smtx_model_eval_gt, __smtx_model_eval_lt,
                      __smtx_model_eval_or, hNEval, hSourceLenEval,
                      native_zlt, native_or, hHigh]
                  · simp [invalid, sr_eval_gt_term_eq,
                      smtx_eval_or_term_eq, sr_eval_numeral_term_eq,
                      sr_eval_boolean_term_eq,
                      __smtx_model_eval_gt, __smtx_model_eval_lt,
                      __smtx_model_eval_or, hNEval, hSourceLenEval,
                      native_zlt, native_or, hNeg]
                rw [smtx_eval_ite_term_eq, hInvalidEval]
                simp [notFound, resultEq, smtx_eval_eq_term_eq,
                  __smtx_model_eval_ite, __smtx_model_eval_eq,
                  hResultEval, hSem, sr_eval_numeral_term_eq, native_veq,
                  nativeResult]
              · rw [if_neg hInvalid] at hSem
                have hInvalidEval :
                    __smtx_model_eval M invalid = SmtValue.Boolean false := by
                  have hNotHigh : ¬ (source.length : Int) < start := by
                    exact fun h => hInvalid (Or.inl h)
                  have hNotNeg : ¬ start < 0 := by
                    exact fun h => hInvalid (Or.inr h)
                  simp [invalid, sr_eval_gt_term_eq,
                    smtx_eval_or_term_eq, sr_eval_numeral_term_eq,
                    sr_eval_boolean_term_eq,
                    __smtx_model_eval_gt, __smtx_model_eval_lt,
                    __smtx_model_eval_or, hNEval, hSourceLenEval,
                    native_zlt, native_or, hNotHigh, hNotNeg]
                rw [smtx_eval_ite_term_eq, hInvalidEval]
                simp only [__smtx_model_eval_ite]
                by_cases hEmpty : native_str_in_re [] regex = true
                · rw [if_pos hEmpty] at hSem
                  rw [smtx_eval_ite_term_eq, hEmptyMatchEval, hEmpty]
                  simp [resultEq, smtx_eval_eq_term_eq,
                    __smtx_model_eval_ite, __smtx_model_eval_eq,
                    hResultEval, hNEval, hSem, native_veq, nativeResult]
                · have hEmptyFalse : native_str_in_re [] regex = false := by
                    cases hVal : native_str_in_re [] regex with
                    | false => rfl
                    | true => exact False.elim (hEmpty hVal)
                  rw [if_neg hEmpty] at hSem
                  rw [smtx_eval_ite_term_eq, hEmptyMatchEval, hEmptyFalse]
                  simp only [__smtx_model_eval_ite]
                  rcases hSem with ⟨hMinimalNative, hFoundNative⟩
                  have hMinimalEval :
                      __smtx_model_eval M minimal =
                        SmtValue.Boolean true := by
                    apply sr_eval_forall2_encoding_true M idxName lenName
                      SmtType.Int SmtType.Int qBody
                    intro vj vk hvjTy _hvjCanonical hvkTy _hvkCanonical
                    rcases int_value_canonical hvjTy with ⟨j, rfl⟩
                    rcases int_value_canonical hvkTy with ⟨k, rfl⟩
                    let Mj := native_model_push M idxName SmtType.Int
                      (SmtValue.Numeral j)
                    let Mjk := native_model_push Mj lenName SmtType.Int
                      (SmtValue.Numeral k)
                    have hNames : idxName ≠ lenName := by
                      native_decide
                    have hIdxEval :
                        native_model_var_lookup Mjk idxName SmtType.Int =
                          SmtValue.Numeral j := by
                      simp [Mj, Mjk, native_model_var_lookup,
                        native_model_push, hNames]
                    have hLenEval :
                        native_model_var_lookup Mjk lenName SmtType.Int =
                          SmtValue.Numeral k := by
                      simp [Mjk, native_model_var_lookup, native_model_push]
                    have hAgree : model_agrees_on_globals M Mjk :=
                      model_agrees_on_globals_trans
                        (model_agrees_on_globals_push M idxName SmtType.Int
                          (SmtValue.Numeral j))
                        (model_agrees_on_globals_push Mj lenName SmtType.Int
                          (SmtValue.Numeral k))
                    have hSEvalPush :
                        __smtx_model_eval Mjk ts =
                          SmtValue.Seq (native_pack_string source) := by
                      rw [← hSEvalString]
                      exact (smt_model_eval_eq_of_eo_closed z hClosedArgs.1
                        M Mjk hAgree).symm
                    have hREvalPush :
                        __smtx_model_eval Mjk tr =
                          SmtValue.RegLan regex := by
                      rw [← hREval]
                      exact (smt_model_eval_eq_of_eo_closed y
                        hClosedArgs.2.1 M Mjk hAgree).symm
                    have hNEvalPush :
                        __smtx_model_eval Mjk tn =
                          SmtValue.Numeral start := by
                      rw [← hNEval]
                      exact (smt_model_eval_eq_of_eo_closed x
                        hClosedArgs.2.2 M Mjk hAgree).symm
                    have hResultEvalPush :
                        __smtx_model_eval Mjk result =
                          SmtValue.Numeral nativeResult := by
                      simp [result, nativeResult, sr_eval_purify_term_eq,
                        sr_eval_str_indexof_re_term_eq,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_str_indexof_re, hSEvalPush,
                        hREvalPush, hNEvalPush,
                        sr_native_unpack_pack_string]
                    have hSourceLenEvalPush :
                        __smtx_model_eval Mjk sourceLen =
                          SmtValue.Numeral (source.length : Int) := by
                      simp [sourceLen, smtx_eval_str_len_term_eq,
                        __smtx_model_eval_str_len, hSEvalPush,
                        native_seq_len, sr_native_unpack_pack_string_length]
                    have hQMatchEval :
                        __smtx_model_eval Mjk qMatch =
                          SmtValue.Boolean
                            (native_str_in_re
                              (native_str_substr source j k) regex) := by
                      simp [qMatch, sr_eval_str_in_re_term_eq,
                        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                        __smtx_model_eval_str_in_re,
                        __smtx_model_eval_str_substr, ivar, lvar,
                        hSEvalPush, hREvalPush, hIdxEval, hLenEval,
                        sr_native_seq_extract_pack_string,
                        sr_native_unpack_extract_pack_string,
                        sr_native_unpack_pack_string, __smtx_model_eval]
                    have hEndEval :
                        __smtx_model_eval Mjk endIndex =
                          SmtValue.Numeral
                            (if nativeResult = -1 then
                              (source.length : Int) else nativeResult) := by
                      by_cases hResultNeg : nativeResult = -1
                      · simp [endIndex, notFound, resultEq,
                          smtx_eval_ite_term_eq, smtx_eval_eq_term_eq,
                          __smtx_model_eval_ite, __smtx_model_eval_eq,
                          hResultEvalPush, hSourceLenEvalPush,
                          sr_eval_numeral_term_eq, native_veq, hResultNeg]
                      · simp [endIndex, notFound, resultEq,
                          smtx_eval_ite_term_eq, smtx_eval_eq_term_eq,
                          __smtx_model_eval_ite, __smtx_model_eval_eq,
                          hResultEvalPush, hSourceLenEvalPush,
                          sr_eval_numeral_term_eq, native_veq, hResultNeg]
                    have hQBodyNative :
                        __smtx_model_eval Mjk qBody =
                          SmtValue.Boolean
                            (decide
                              (¬ start ≤ j ∨
                                ¬ j < (if nativeResult = -1 then
                                  (source.length : Int) else nativeResult) ∨
                                ¬ 0 < k ∨
                                ¬ k ≤ (source.length : Int) - j ∨
                                native_str_in_re
                                    (native_str_substr source j k) regex =
                                  false)) := by
                      simp [qBody, ivar, lvar, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, sr_eval_var_term_eq,
                        smtx_eval_or_term_eq,
                        smtx_eval_not_term_eq,
                        sr_eval_geq_term_eq, sr_eval_lt_term_eq,
                        sr_eval_gt_term_eq, sr_eval_leq_term_eq,
                        sr_eval_neg_term_eq, hIdxEval, hLenEval, hNEvalPush,
                        hEndEval, hSourceLenEvalPush, hQMatchEval,
                        __smtx_model_eval_or, __smtx_model_eval_not,
                        __smtx_model_eval_geq, __smtx_model_eval_leq,
                        __smtx_model_eval_lt, __smtx_model_eval_gt,
                        __smtx_model_eval__, native_or, native_not,
                        native_zleq, native_zlt, native_zneg,
                        sr_not_decide_le_eq_decide_lt,
                        sr_not_decide_lt_eq_decide_le,
                        native_zplus, Int.sub_eq_add_neg]
                    rw [hQBodyNative]
                    have hMinimalOrder :
                        j < start ∨
                          (if nativeResult = -1 then
                            (source.length : Int) else nativeResult) ≤ j ∨
                          k ≤ 0 ∨
                          (source.length : Int) - j < k ∨
                          native_str_in_re
                              (native_str_substr source j k) regex = false := by
                      rcases hMinimalNative j k with hLo | hHi | hKPos | hKHi | hNo
                      · exact Or.inl (Int.lt_of_not_ge hLo)
                      · exact Or.inr (Or.inl (Int.le_of_not_gt hHi))
                      · exact Or.inr (Or.inr (Or.inl (Int.le_of_not_gt hKPos)))
                      · exact Or.inr (Or.inr (Or.inr
                          (Or.inl (Int.lt_of_not_ge hKHi))))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hNo)))
                    simp [hMinimalOrder]
                  have hFoundClauseEval :
                      __smtx_model_eval M foundClause =
                        SmtValue.Boolean true := by
                    rcases hFoundNative with hNotFound |
                      ⟨hResultLo, k, hkNonneg, hkBound, hkMatch⟩
                    · have hFoundForallNN :
                          term_has_non_none_type foundForall := by
                        unfold term_has_non_none_type
                        rw [hFoundForallTy]
                        decide
                      have hFoundForallValTy :
                          __smtx_typeof_value
                              (__smtx_model_eval M foundForall) =
                            SmtType.Bool := by
                        simpa [hFoundForallTy] using
                          smt_model_eval_preserves_type_of_non_none M hM
                            foundForall hFoundForallNN
                      rcases bool_value_canonical hFoundForallValTy with
                        ⟨b, hFoundForallEval⟩
                      simp [foundClause, notFound, resultEq,
                        smtx_eval_or_term_eq, smtx_eval_and_term_eq,
                        smtx_eval_not_term_eq, smtx_eval_eq_term_eq,
                        sr_eval_geq_term_eq, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, __smtx_model_eval_or,
                        __smtx_model_eval_and, __smtx_model_eval_not,
                        __smtx_model_eval_eq, __smtx_model_eval_geq,
                        __smtx_model_eval_leq, hResultEval, hNEval,
                        hFoundForallEval, hNotFound, native_or, native_and,
                        native_not, native_veq, native_zleq]
                    · let Mk := native_model_push M lenName SmtType.Int
                          (SmtValue.Numeral k)
                      have hLenEval :
                          native_model_var_lookup Mk lenName SmtType.Int =
                            SmtValue.Numeral k := by
                        simp [Mk, native_model_var_lookup, native_model_push]
                      have hAgree : model_agrees_on_globals M Mk :=
                        model_agrees_on_globals_push M lenName SmtType.Int
                          (SmtValue.Numeral k)
                      have hSEvalPush :
                          __smtx_model_eval Mk ts =
                            SmtValue.Seq (native_pack_string source) := by
                        rw [← hSEvalString]
                        exact (smt_model_eval_eq_of_eo_closed z
                          hClosedArgs.1 M Mk hAgree).symm
                      have hREvalPush :
                          __smtx_model_eval Mk tr =
                            SmtValue.RegLan regex := by
                        rw [← hREval]
                        exact (smt_model_eval_eq_of_eo_closed y
                          hClosedArgs.2.1 M Mk hAgree).symm
                      have hNEvalPush :
                          __smtx_model_eval Mk tn =
                            SmtValue.Numeral start := by
                        rw [← hNEval]
                        exact (smt_model_eval_eq_of_eo_closed x
                          hClosedArgs.2.2 M Mk hAgree).symm
                      have hResultEvalPush :
                          __smtx_model_eval Mk result =
                            SmtValue.Numeral nativeResult := by
                        simp [result, nativeResult, sr_eval_purify_term_eq,
                          sr_eval_str_indexof_re_term_eq,
                          __smtx_model_eval__at_purify,
                          __smtx_model_eval_str_indexof_re, hSEvalPush,
                          hREvalPush, hNEvalPush,
                          sr_native_unpack_pack_string]
                      have hSourceLenEvalPush :
                          __smtx_model_eval Mk sourceLen =
                            SmtValue.Numeral (source.length : Int) := by
                        simp [sourceLen, smtx_eval_str_len_term_eq,
                          __smtx_model_eval_str_len, hSEvalPush,
                          native_seq_len,
                          sr_native_unpack_pack_string_length]
                      have hFoundMatchEval :
                          __smtx_model_eval Mk foundMatch =
                            SmtValue.Boolean
                              (native_str_in_re
                                (native_str_substr source nativeResult k)
                                regex) := by
                        simp [foundMatch, sr_eval_str_in_re_term_eq,
                          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
                          __smtx_model_eval_str_in_re,
                          __smtx_model_eval_str_substr, lvar, hSEvalPush,
                          hREvalPush, hResultEvalPush, hLenEval,
                          sr_native_seq_extract_pack_string,
                          sr_native_unpack_extract_pack_string,
                          sr_native_unpack_pack_string,
                          __smtx_model_eval]
                      have hFoundBodyFalse :
                          __smtx_model_eval Mk foundBody =
                            SmtValue.Boolean false := by
                        have hkBound' :
                            k ≤ (source.length : Int) + -nativeResult := by
                          simpa [Int.sub_eq_add_neg] using hkBound
                        simp [foundBody, lvar, sr_eval_boolean_term_eq,
                          sr_eval_numeral_term_eq, sr_eval_var_term_eq,
                          smtx_eval_or_term_eq, smtx_eval_not_term_eq,
                          sr_eval_geq_term_eq, sr_eval_leq_term_eq,
                          sr_eval_neg_term_eq, hLenEval, hResultEvalPush,
                          hSourceLenEvalPush, hFoundMatchEval,
                          __smtx_model_eval_or, __smtx_model_eval_not,
                          __smtx_model_eval_geq, __smtx_model_eval_leq,
                          __smtx_model_eval__, native_or, native_not,
                          native_zleq, native_zneg, native_zplus,
                          Int.sub_eq_add_neg, hkNonneg, hkBound', hkMatch]
                      have hFoundForallFalse :
                          __smtx_model_eval M foundForall =
                            SmtValue.Boolean false := by
                        simpa [foundForall] using
                          sr_eval_forall_encoding_false M lenName SmtType.Int
                            foundBody (SmtValue.Numeral k) rfl
                            (by simp [__smtx_value_canonical])
                            hFoundBodyFalse
                      have hResultNotFound : nativeResult ≠ -1 := by
                        have hStartNonneg : 0 ≤ start :=
                          Int.le_of_not_gt (fun hNeg => hInvalid (Or.inr hNeg))
                        intro hEq
                        have hBad : start ≤ -1 := by
                          simpa [hEq] using hResultLo
                        have hMinusOneLt : (-1 : Int) < start :=
                          Int.lt_of_lt_of_le (by decide) hStartNonneg
                        exact (Int.not_le_of_gt hMinusOneLt) hBad
                      simp [foundClause, notFound, resultEq,
                        smtx_eval_or_term_eq, smtx_eval_and_term_eq,
                        smtx_eval_not_term_eq, smtx_eval_eq_term_eq,
                        sr_eval_geq_term_eq, sr_eval_boolean_term_eq,
                        sr_eval_numeral_term_eq, __smtx_model_eval_or,
                        __smtx_model_eval_and, __smtx_model_eval_not,
                        __smtx_model_eval_eq, __smtx_model_eval_geq,
                        __smtx_model_eval_leq, hResultEval, hNEval,
                        hFoundForallFalse, hResultNotFound, hResultLo,
                        native_or, native_and, native_not, native_veq,
                        native_zleq]
                  simp [characterized, smtx_eval_and_term_eq,
                    sr_eval_boolean_term_eq, __smtx_model_eval_and,
                    hMinimalEval, hFoundClauseEval, native_and]
/-- The complete generated result is true whenever its guard succeeds. -/
private theorem string_reduction_true
    (M : SmtModel) (hM : model_wf M) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (__eo_prog_string_reduction s) = Term.Bool) :
    eo_interprets M (__eo_prog_string_reduction s) true := by
  have hProg : __eo_prog_string_reduction s ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hsNe : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hTrans
  have hProgEq :
      __eo_prog_string_reduction s =
        __eo_requires (__is_closed_rec s Term.__eo_List_nil)
          (Term.Boolean true) (stringReductionBody s) := by
    cases s <;> simp [__eo_prog_string_reduction, stringReductionBody] at hsNe ⊢
  have hReqNe :
      __eo_requires (__is_closed_rec s Term.__eo_List_nil)
          (Term.Boolean true) (stringReductionBody s) ≠ Term.Stuck := by
    simpa [hProgEq] using hProg
  have hReduce :
      __eo_prog_string_reduction s = stringReductionBody s := by
    rw [hProgEq]
    exact eo_requires_eq_result_of_ne_stuck _ _ _ hReqNe
  have hClosedRec :
      __is_closed_rec s Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck _ _ _ hReqNe
  have hClosed : __eo_is_closed s = Term.Boolean true := by
    rw [← is_closed_rec_eq_eo_is_closed_of_has_smt_translation hTrans]
    exact hClosedRec
  have hBodyTy : __eo_typeof (stringReductionBody s) = Term.Bool := by
    simpa [hReduce] using hTy
  rw [hReduce]
  exact string_reduction_body_true M s hTrans
    (string_reduction_pred_true M hM s hTrans hClosed hBodyTy)

public theorem cmd_step_string_reduction_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_reduction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.string_reduction args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | cons _ _ =>
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              exact False.elim (hProg rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
                  hCmdTrans.1
              have hTrue : eo_interprets M (__eo_prog_string_reduction a) true := by
                exact string_reduction_true M hM a hATrans hResultTy
              refine ⟨?_, ?_⟩
              · intro _
                exact hTrue
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue)
