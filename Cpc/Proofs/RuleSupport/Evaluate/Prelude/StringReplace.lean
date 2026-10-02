module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringIndexof
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringIndexof

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.native_str_replace_eval_result
    (s pat repl : native_String) : native_String :=
  let idx := native_str_indexof s pat 0
  if idx < 0 then
    s
  else
    s.take (Int.toNat idx) ++ repl ++ s.drop (Int.toNat idx + pat.length)

theorem EvaluateProofInternal.native_str_substr_prefix_take_local
    (s : native_String) (idx : Nat) :
    native_str_substr s 0 (Int.ofNat idx) = s.take idx := by
  cases s with
  | nil =>
      simp [native_str_substr, native_str_len]
  | cons c cs =>
      cases idx with
      | zero =>
          simp [native_str_substr, native_str_len]
      | succ k =>
          by_cases hk : k ≤ cs.length
          · have hki : (↑k : Int) ≤ (↑cs.length : Int) :=
              Int.ofNat_le.mpr hk
            have hMinInt :
                min (↑k : Int) (↑cs.length : Int) = (↑k : Int) :=
              Int.min_eq_left hki
            simp [native_str_substr, native_str_len]
            rw [hMinInt]
            simp
          · have hkge : cs.length ≤ k := Nat.le_of_not_ge hk
            have hki : (↑cs.length : Int) ≤ (↑k : Int) :=
              Int.ofNat_le.mpr hkge
            have hMinInt :
                min (↑k : Int) (↑cs.length : Int) = (↑cs.length : Int) :=
              Int.min_eq_right hki
            have hTake : cs.take k = cs := List.take_of_length_le hkge
            simp [native_str_substr, native_str_len]
            rw [hMinInt]
            simp [hTake]

theorem EvaluateProofInternal.native_str_substr_suffix_drop_local
    (s : native_String) (start : Nat) :
    native_str_substr s (Int.ofNat start)
        (Int.ofNat s.length - Int.ofNat start + 1) =
      s.drop start := by
  unfold native_str_substr native_str_len
  by_cases hlt : start < s.length
  · have hnot1 : ¬((↑start : Int) < 0) := by omega
    have hnot2 : ¬((↑s.length : Int) - ↑start + 1 <= 0) := by omega
    have hnot3 : ¬((↑start : Int) >= ↑s.length) := by omega
    simp [hnot1, hnot2, hnot3]
    have hMin :
        min ((↑s.length : Int) - ↑start + 1)
            ((↑s.length : Int) - ↑start) =
          (↑s.length : Int) - ↑start := by
      apply Int.min_eq_right
      omega
    rw [hMin]
    have hToNat :
        Int.toNat ((↑s.length : Int) - ↑start) = s.length - start := by
      apply Int.ofNat.inj
      change (↑(((↑s.length : Int) - ↑start).toNat) : Int) =
        ↑(s.length - start)
      rw [Int.toNat_of_nonneg]
      · rw [Int.ofNat_sub (Nat.le_of_lt hlt)]
      · omega
    rw [hToNat]
    exact List.take_of_length_le (by rw [List.length_drop]; omega)
  · have hge : s.length ≤ start := Nat.le_of_not_gt hlt
    have hdrop : s.drop start = [] := List.drop_eq_nil_of_le hge
    simp [hdrop]

theorem EvaluateProofInternal.native_str_indexof_suffix_offset
    (s t : native_String) (i : native_Int)
    (hNonneg : 0 ≤ i) (hLe : i ≤ native_str_len s) :
    native_str_indexof s t i =
      (let r :=
        native_str_indexof
          (native_str_substr s i (native_str_len s - i + 1)) t 0
       if r = (-1 : native_Int) then (-1 : native_Int) else i + r) := by
  let start := Int.toNat i
  have hiEq : i = Int.ofNat start := by
    exact (Int.toNat_of_nonneg hNonneg).symm
  have hStartLe : start ≤ s.length := by
    rw [hiEq] at hLe
    have hLe' : (start : native_Int) ≤ Int.ofNat s.length := by
      simpa [native_str_len] using hLe
    exact Int.ofNat_le.mp hLe'
  rw [hiEq]
  have hSubstr :
      native_str_substr s (Int.ofNat start)
          (native_str_len s - Int.ofNat start + 1) =
        s.drop start := by
    simpa [native_str_len] using
      EvaluateProofInternal.native_str_substr_suffix_drop_local s start
  rw [hSubstr]
  unfold native_str_indexof
  have hStartNotNeg : ¬ ((Int.ofNat start : Int) < 0) := by
    exact Int.not_lt_of_ge (Int.natCast_nonneg start)
  by_cases hBound : start + t.length ≤ s.length
  · have hDropBound : t.length ≤ (s.drop start).length := by
      rw [List.length_drop]
      omega
    have hDropBoundNat : t.length ≤ s.length - start := by
      omega
    simp [hBound, hDropBoundNat, native_str_len]
    have hTakeLen : (s.take start).length = start := by
      simp [List.length_take, hStartLe]
    have hAppend : s.take start ++ s.drop start = s :=
      List.take_append_drop start s
    let fuel := s.length - (start + t.length) + 1
    have hFuelDrop :
        (s.drop start).length - t.length + 1 = fuel := by
      rw [List.length_drop]
      omega
    have hHead :=
      EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix (s.take start) (s.drop start)
        t fuel
    have hTail :=
      EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([] : native_String)
        (s.drop start) t fuel
    have hTail' :
        native_seq_indexof_rec ((s.drop start).map SmtValue.Char)
            (t.map SmtValue.Char) 0 fuel =
          impl_native_str_indexof_rec (s.drop start) t 0 fuel := by
      simpa using hTail
    have hOffset :=
      EvaluateProofInternal.native_seq_indexof_rec_offset_local
        ((s.drop start).map SmtValue.Char) (t.map SmtValue.Char)
        0 start fuel
    have hOffset' :
        native_seq_indexof_rec ((s.drop start).map SmtValue.Char)
            (t.map SmtValue.Char) start fuel =
          (let r :=
            native_seq_indexof_rec ((s.drop start).map SmtValue.Char)
              (t.map SmtValue.Char) 0 fuel
           if r = (-1 : native_Int) then (-1 : native_Int)
           else r + Int.ofNat start) := by
      simpa using hOffset
    rw [hTakeLen, hAppend] at hHead
    rw [show ([] : native_String) ++ s.drop start = s.drop start by rfl]
      at hTail
    rw [show s.length - start - t.length + 1 = fuel by omega]
    rw [← hHead, hOffset', hTail']
    simp [Int.add_comm]
    intro hBad _
    exact False.elim (hStartNotNeg hBad)
  · have hDropBound : ¬ t.length ≤ (s.drop start).length := by
      rw [List.length_drop]
      omega
    have hDropBoundNat : ¬ t.length ≤ s.length - start := by
      omega
    simp [hBound, hDropBoundNat, native_str_len]

theorem EvaluateProofInternal.str_indexof_result_strings
    (s pat : native_String) (i : native_Int) :
    let runLen := __eo_len (Term.String s)
    let runFind :=
      __eo_find
        (__eo_to_str (__eo_extract (Term.String s) (Term.Numeral i) runLen))
        (__eo_to_str (Term.String pat))
    __eo_ite (__eo_is_neg (Term.Numeral i))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_gt (Term.Numeral i) runLen)
        (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_is_neg runFind) runFind
          (__eo_add (Term.Numeral i) runFind))) =
      Term.Numeral (native_str_indexof s pat i) := by
  dsimp
  by_cases hiNeg : i < 0
  · have hLt : native_zlt i 0 = true := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_true hiNeg
    rw [show __eo_is_neg (Term.Numeral i) = Term.Boolean true by
      simp [__eo_is_neg, hLt]]
    rw [eo_ite_true]
    rw [EvaluateProofInternal.native_str_indexof_neg s pat hiNeg]
  · have hiNonneg : 0 ≤ i := Int.le_of_not_gt hiNeg
    have hLt : native_zlt i 0 = false := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_false hiNeg
    rw [show __eo_is_neg (Term.Numeral i) = Term.Boolean false by
      simp [__eo_is_neg, hLt]]
    rw [eo_ite_false]
    by_cases hGt : native_str_len s < i
    · have hGtBool : native_zlt (native_str_len s) i = true := by
        rw [show native_zlt (native_str_len s) i =
            decide (native_str_len s < i) by rfl]
        exact decide_eq_true hGt
      rw [show
          __eo_gt (Term.Numeral i) (__eo_len (Term.String s)) =
            Term.Boolean true by
        simp [__eo_gt, __eo_len, hGtBool]]
      rw [eo_ite_true]
      rw [EvaluateProofInternal.native_str_indexof_gt_len s pat hGt]
    · have hLe : i ≤ native_str_len s := Int.le_of_not_gt hGt
      have hGtBool : native_zlt (native_str_len s) i = false := by
        rw [show native_zlt (native_str_len s) i =
            decide (native_str_len s < i) by rfl]
        exact decide_eq_false hGt
      rw [show
          __eo_gt (Term.Numeral i) (__eo_len (Term.String s)) =
            Term.Boolean false by
        simp [__eo_gt, __eo_len, hGtBool]]
      rw [eo_ite_false]
      let suffix := native_str_substr s i (native_str_len s - i + 1)
      have hFind :
          __eo_find
              (__eo_to_str
                (__eo_extract (Term.String s) (Term.Numeral i)
                  (__eo_len (Term.String s))))
              (__eo_to_str (Term.String pat)) =
            Term.Numeral (native_str_indexof suffix pat 0) := by
        dsimp [suffix]
        simp [__eo_extract, __eo_len, __eo_to_str, __eo_find,
          native_zplus, native_zneg, native_str_len, Int.sub_eq_add_neg]
      rw [hFind]
      by_cases hFoundNeg : native_str_indexof suffix pat 0 < 0
      · have hFoundLt :
            native_zlt (native_str_indexof suffix pat 0) 0 = true := by
          rw [show native_zlt (native_str_indexof suffix pat 0) 0 =
              decide (native_str_indexof suffix pat 0 < 0) by rfl]
          exact decide_eq_true hFoundNeg
        rw [show
            __eo_is_neg (Term.Numeral (native_str_indexof suffix pat 0)) =
              Term.Boolean true by
          simp [__eo_is_neg, hFoundLt]]
        rw [eo_ite_true]
        have hFoundEq :
            native_str_indexof suffix pat 0 = -1 :=
          EvaluateProofInternal.native_str_indexof_eq_neg_one_of_neg suffix pat hFoundNeg
        have hSuffix :=
          EvaluateProofInternal.native_str_indexof_suffix_offset s pat i hiNonneg hLe
        dsimp [suffix] at hSuffix
        rw [hFoundEq] at hSuffix
        simp at hSuffix
        rw [hFoundEq, hSuffix]
      · have hFoundLt :
            native_zlt (native_str_indexof suffix pat 0) 0 = false := by
          rw [show native_zlt (native_str_indexof suffix pat 0) 0 =
              decide (native_str_indexof suffix pat 0 < 0) by rfl]
          exact decide_eq_false hFoundNeg
        rw [show
            __eo_is_neg (Term.Numeral (native_str_indexof suffix pat 0)) =
              Term.Boolean false by
          simp [__eo_is_neg, hFoundLt]]
        rw [eo_ite_false]
        have hFoundNe :
            native_str_indexof suffix pat 0 ≠ (-1 : native_Int) := by
          intro hEq
          apply hFoundNeg
          rw [hEq]
          decide
        have hSuffix :=
          EvaluateProofInternal.native_str_indexof_suffix_offset s pat i hiNonneg hLe
        dsimp [suffix] at hSuffix
        rw [ite_eq_right hFoundNe] at hSuffix
        change
          Term.Numeral (i + native_str_indexof suffix pat 0) =
            Term.Numeral (native_str_indexof s pat i)
        rw [hSuffix]

theorem EvaluateProofInternal.str_indexof_result_strings_of_index_numeral
    (s pat : native_String) (n : Term) (i : native_Int)
    (hn : n = Term.Numeral i) :
    let runLen := __eo_len (Term.String s)
    let runFind :=
      __eo_find
        (__eo_to_str (__eo_extract (Term.String s) n runLen))
        (__eo_to_str (Term.String pat))
    __eo_ite (__eo_is_neg (Term.Numeral i))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_gt (Term.Numeral i) runLen)
        (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_is_neg runFind) runFind
          (__eo_add n runFind))) =
      Term.Numeral (native_str_indexof s pat i) := by
  subst n
  exact EvaluateProofInternal.str_indexof_result_strings s pat i

theorem EvaluateProofInternal.native_seq_replace_pack_string
    (s pat repl : native_String) :
    native_pack_seq SmtType.Char
        (native_seq_replace (native_unpack_seq (native_pack_string s))
          (native_unpack_seq (native_pack_string pat))
          (native_unpack_seq (native_pack_string repl))) =
      native_pack_string (EvaluateProofInternal.native_str_replace_eval_result s pat repl) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string pat) =
      pat.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string repl) =
      repl.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [StrEqReplSupport.native_seq_replace_eq_indexof]
  rw [EvaluateProofInternal.native_seq_indexof_map_char_zero]
  by_cases hNeg : native_str_indexof s pat 0 < 0
  · simp [EvaluateProofInternal.native_str_replace_eval_result, hNeg,
      native_pack_string]
  · simp [EvaluateProofInternal.native_str_replace_eval_result, hNeg,
      native_pack_string, List.map_append, List.map_take, List.map_drop]

theorem EvaluateProofInternal.str_replace_result_strings
    (s pat repl : native_String) :
    __eo_ite (__eo_is_neg
          (__eo_find (__eo_to_str (Term.String s))
            (__eo_to_str (Term.String pat))))
        (Term.String s)
        (__eo_concat
          (__eo_concat
            (__eo_extract (Term.String s) (Term.Numeral 0)
              (__eo_add
                (__eo_find (__eo_to_str (Term.String s))
                  (__eo_to_str (Term.String pat)))
                (Term.Numeral (-1 : native_Int))))
            (Term.String repl))
          (__eo_extract (Term.String s)
            (__eo_add
              (__eo_find (__eo_to_str (Term.String s))
                (__eo_to_str (Term.String pat)))
              (__eo_len (Term.String pat)))
            (__eo_len (Term.String s)))) =
      Term.String (EvaluateProofInternal.native_str_replace_eval_result s pat repl) := by
  let idx := native_str_indexof s pat 0
  simp only [__eo_find, __eo_to_str]
  unfold EvaluateProofInternal.native_str_replace_eval_result
  by_cases hNeg : idx < 0
  · have hGuard :
        __eo_is_neg (Term.Numeral (native_str_indexof s pat 0)) =
          Term.Boolean true := by
      have hLt : native_zlt (native_str_indexof s pat 0) 0 = true := by
        rw [show native_zlt (native_str_indexof s pat 0) 0 =
          decide (native_str_indexof s pat 0 < 0) by rfl]
        exact decide_eq_true (by simpa [idx] using hNeg)
      simp [__eo_is_neg, hLt]
    rw [hGuard, eo_ite_true]
    simp [idx, hNeg]
  · have hNonneg : 0 ≤ idx := Int.le_of_not_gt hNeg
    let n := Int.toNat idx
    have hIdxNat : Int.ofNat n = idx := Int.toNat_of_nonneg hNonneg
    have hStart :
        idx + native_str_len pat = Int.ofNat (n + pat.length) := by
      rw [← hIdxNat]
      simp [native_str_len]
    have hGuard :
        __eo_is_neg (Term.Numeral (native_str_indexof s pat 0)) =
          Term.Boolean false := by
      have hLt : native_zlt (native_str_indexof s pat 0) 0 = false := by
        rw [show native_zlt (native_str_indexof s pat 0) 0 =
          decide (native_str_indexof s pat 0 < 0) by rfl]
        exact decide_eq_false (by simpa [idx] using hNeg)
      simp [__eo_is_neg, hLt]
    rw [hGuard, eo_ite_false]
    simp [__eo_extract, __eo_add, __eo_len, __eo_concat,
      native_zplus, native_zneg, native_str_len]
    rw [show native_str_indexof s pat 0 + -1 + 1 =
        native_str_indexof s pat 0 by
      rw [Int.add_assoc]
      simp]
    rw [show native_str_substr s 0 (native_str_indexof s pat 0) =
        s.take n by
      change native_str_substr s 0 idx = s.take n
      rw [← hIdxNat]
      exact EvaluateProofInternal.native_str_substr_prefix_take_local s n]
    rw [show
        native_str_substr s
            (native_str_indexof s pat 0 + ↑pat.length)
            (↑s.length + -(native_str_indexof s pat 0 + ↑pat.length) + 1) =
          s.drop (n + pat.length) by
      rw [show native_str_indexof s pat 0 + ↑pat.length =
          Int.ofNat (n + pat.length) by
        simpa [idx, native_str_len] using hStart]
      change
        native_str_substr s (Int.ofNat (n + pat.length))
            (Int.ofNat s.length - Int.ofNat (n + pat.length) + 1) =
          s.drop (n + pat.length)
      exact EvaluateProofInternal.native_str_substr_suffix_drop_local s (n + pat.length)]
    rw [ite_eq_right (by simpa [idx] using hNeg)]
    simp [n, idx, native_str_concat, List.append_assoc]

