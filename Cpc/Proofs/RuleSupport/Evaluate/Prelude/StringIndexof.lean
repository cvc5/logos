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

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.native_unpack_pack_seq_local (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq,
        EvaluateProofInternal.native_unpack_pack_seq_local T xs]

theorem EvaluateProofInternal.elem_typeof_pack_seq_local (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        EvaluateProofInternal.elem_typeof_pack_seq_local T xs]

theorem EvaluateProofInternal.native_seq_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_pack_seq SmtType.Char
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i n) =
      native_pack_string (native_str_substr s i n) := by
  simp only [native_pack_string, native_seq_extract, native_str_substr,
    native_str_len, EvaluateProofInternal.native_unpack_pack_seq_local]
  by_cases h : (i < 0 ∨ n ≤ 0) ∨ ↑s.length ≤ i
  · simp [h]
  · simp [h, List.map_take, List.map_drop]

theorem EvaluateProofInternal.native_seq_extract_pack_string_one
    (s : native_String) (i : native_Int) :
    native_pack_seq SmtType.Char
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i 1) =
      native_pack_string (native_str_substr s i 1) :=
  EvaluateProofInternal.native_seq_extract_pack_string s i 1

theorem EvaluateProofInternal.native_pack_string_injective :
    Function.Injective native_pack_string := by
  intro s t h
  have hUnpack := congrArg native_unpack_string h
  simpa [RuleProofs.native_unpack_string_pack_string] using hUnpack

theorem EvaluateProofInternal.smtx_model_eval_str_leq_pack_string
    (s t : native_String) :
    __smtx_model_eval_str_leq
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string t)) =
      SmtValue.Boolean (native_or (decide (s = t)) (native_str_lt s t)) := by
  unfold __smtx_model_eval_str_leq
  simp only [__smtx_model_eval_str_lt,
    RuleProofs.native_unpack_string_pack_string]
  by_cases hEq : s = t
  · subst t
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
      native_or]
  · have hPackNe : native_pack_string s ≠ native_pack_string t := by
      intro hPack
      exact hEq (EvaluateProofInternal.native_pack_string_injective hPack)
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
      native_or, hEq, hPackNe]

theorem EvaluateProofInternal.native_seq_prefix_eq_map_char
    (a b : native_String) :
    native_seq_prefix_eq (a.map SmtValue.Char) (b.map SmtValue.Char) =
      native_string_prefix_eq a b := by
  induction a generalizing b with
  | nil =>
      simp [native_seq_prefix_eq, native_string_prefix_eq]
  | cons c cs ih =>
      cases b with
      | nil =>
          simp [native_seq_prefix_eq, native_string_prefix_eq]
      | cons d ds =>
          simp [native_seq_prefix_eq, native_string_prefix_eq, native_veq,
            ih]

theorem EvaluateProofInternal.native_string_prefix_eq_length_le
    (pat s : native_String)
    (hPrefix : native_string_prefix_eq pat s = true) :
    pat.length ≤ s.length := by
  induction pat generalizing s with
  | nil =>
      simp
  | cons p ps ih =>
      cases s with
      | nil =>
          simp [native_string_prefix_eq] at hPrefix
      | cons c cs =>
          have hTail :
              native_string_prefix_eq ps cs = true := by
            by_cases hpc : p = c
            · subst c
              simpa [native_string_prefix_eq] using hPrefix
            · have hcp : c ≠ p := by
                intro h
                exact hpc h.symm
              simp [native_string_prefix_eq, hpc] at hPrefix
          have hLe := ih cs hTail
          simp [hLe]

theorem EvaluateProofInternal.native_str_indexof_rec_past_end_nonempty
    (s pat : native_String) (i fuel : Nat)
    (hLen : s.length ≤ i) (hPat : pat ≠ []) :
    impl_native_str_indexof_rec s pat i fuel = -1 := by
  induction fuel generalizing i with
  | zero =>
      simp [impl_native_str_indexof_rec]
  | succ fuel ih =>
      unfold impl_native_str_indexof_rec
      have hDrop : s.drop i = [] := List.drop_eq_nil_of_le hLen
      have hPrefix : native_string_prefix_eq pat (s.drop i) = false := by
        cases pat with
        | nil =>
            contradiction
        | cons p ps =>
            simp [native_string_prefix_eq, hDrop]
      simp [hPrefix, ih (i + 1) (by omega)]

theorem EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix
    (pre cur pat : native_String) (fuel : Nat) :
    native_seq_indexof_rec (cur.map SmtValue.Char)
        (pat.map SmtValue.Char) pre.length fuel =
      impl_native_str_indexof_rec (pre ++ cur) pat pre.length fuel := by
  induction fuel generalizing pre cur with
  | zero =>
      simp [native_seq_indexof_rec, impl_native_str_indexof_rec]
  | succ fuel ih =>
      rw [Smtm.native_seq_indexof_rec.eq_def, impl_native_str_indexof_rec]
      rw [EvaluateProofInternal.native_seq_prefix_eq_map_char]
      rw [show (pre ++ cur).drop pre.length = cur by simp]
      by_cases hPrefix : native_string_prefix_eq pat cur = true
      · simp [hPrefix]
      · simp [hPrefix]
        cases cur with
        | nil =>
            cases pat with
            | nil =>
                simp [native_string_prefix_eq] at hPrefix
            | cons p ps =>
                simpa using (EvaluateProofInternal.native_str_indexof_rec_past_end_nonempty pre
                  (p :: ps) (pre.length + 1) fuel
                  (by simp) (by simp)).symm
        | cons c cs =>
            have hAppend : pre ++ c :: cs = (pre ++ [c]) ++ cs := by
              simp [List.append_assoc]
            rw [hAppend]
            simpa [List.length_append] using ih (pre ++ [c]) cs

theorem EvaluateProofInternal.native_seq_indexof_rec_offset_local
    (xs pat : List SmtValue) :
    ∀ (i off fuel : Nat),
      native_seq_indexof_rec xs pat (i + off) fuel =
        (let r := native_seq_indexof_rec xs pat i fuel
         if r = (-1 : native_Int) then (-1 : native_Int)
         else r + Int.ofNat off)
  | _i, _off, 0 => by
      simp [native_seq_indexof_rec]
  | i, off, fuel + 1 => by
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · unfold native_seq_indexof_rec
        rw [ite_eq_left hPrefix, ite_eq_left hPrefix]
        have hne : (Int.ofNat i : native_Int) ≠ -1 := by
          intro h
          have hNonneg : (0 : native_Int) ≤ Int.ofNat i :=
            Int.natCast_nonneg i
          have hNeg : ¬ (0 : native_Int) ≤ -1 := by decide
          have hBad : (0 : native_Int) ≤ -1 := by
            rw [← h]
            exact hNonneg
          exact hNeg hBad
        rw [ite_eq_right hne]
        simp
      · unfold native_seq_indexof_rec
        rw [ite_eq_right hPrefix, ite_eq_right hPrefix]
        cases xs with
        | nil =>
            simp
        | cons _ xs =>
            rw [show i + off + 1 = (i + 1) + off by omega]
            exact EvaluateProofInternal.native_seq_indexof_rec_offset_local xs pat
              (i + 1) off fuel

theorem EvaluateProofInternal.native_str_indexof_rec_cons_offset
    (c : native_Char) (cs pat : native_String) (fuel : Nat) :
    impl_native_str_indexof_rec (c :: cs) pat 1 fuel =
      (let r := impl_native_str_indexof_rec cs pat 0 fuel
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1) := by
  have hHead :=
    EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([c] : native_String) cs pat
      fuel
  have hTail :=
    EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([] : native_String) cs pat
      fuel
  have hOffset :=
    EvaluateProofInternal.native_seq_indexof_rec_offset_local
      (cs.map SmtValue.Char) (pat.map SmtValue.Char) 0 1 fuel
  rw [show ([c] : native_String).length = 1 by rfl] at hHead
  rw [show ([] : native_String).length = 0 by rfl] at hTail
  change
    impl_native_str_indexof_rec (([c] : native_String) ++ cs) pat 1 fuel =
      (let r := impl_native_str_indexof_rec (([] : native_String) ++ cs) pat 0 fuel
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1)
  rw [← hHead, hOffset, hTail]
  simp

theorem EvaluateProofInternal.native_str_indexof_cons_not_prefix
    (c p : native_Char) (cs ps : native_String)
    (hPrefix :
      native_string_prefix_eq (p :: ps) (c :: cs) = false) :
    native_str_indexof (c :: cs) (p :: ps) 0 =
      (let r := native_str_indexof cs (p :: ps) 0
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1) := by
  unfold native_str_indexof
  by_cases hTail : ps.length + 1 ≤ cs.length
  · have hParent : ps.length + 1 ≤ cs.length + 1 := by omega
    simp [native_str_len, hParent, hTail]
    have hFuel :
        cs.length - ps.length + 1 =
          (cs.length - (ps.length + 1) + 1) + 1 := by
      omega
    rw [hFuel]
    unfold impl_native_str_indexof_rec
    simp [hPrefix]
    exact EvaluateProofInternal.native_str_indexof_rec_cons_offset c cs (p :: ps)
      (cs.length - (ps.length + 1) + 1)
  · by_cases hParent : ps.length + 1 ≤ cs.length + 1
    · simp [native_str_len, hParent, hTail]
      have hFuel :
          cs.length - ps.length + 1 = 1 := by
        omega
      rw [hFuel]
      unfold impl_native_str_indexof_rec
      simp [hPrefix, impl_native_str_indexof_rec]
    · simp [native_str_len, hParent, hTail]

theorem EvaluateProofInternal.native_seq_indexof_le_len_sub_pat_of_pat_le_len_local
    (xs pat : List SmtValue) (i : native_Int) :
    pat.length ≤ xs.length →
      native_seq_indexof xs pat i ≤
        Int.ofNat xs.length - Int.ofNat pat.length := by
  intro hPatLe
  rw [native_seq_indexof_eq_rec]
  split
  · have hNonneg :
        (0 : native_Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
      exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
    exact Int.le_trans (by decide : (-1 : native_Int) ≤ 0) hNonneg
  · dsimp
    split
    · rename_i _hStart _hBounds
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat
          (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          have hNonneg :
              (0 : native_Int) ≤
                Int.ofNat xs.length - Int.ofNat pat.length := by
            exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
          exact Int.le_trans (by decide : (-1 : native_Int) ≤ 0) hNonneg
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          have hNat :
              Int.toNat i + j ≤ xs.length - pat.length := by
            omega
          calc
            Int.ofNat (Int.toNat i + j) ≤
                Int.ofNat (xs.length - pat.length) :=
              Int.ofNat_le.mpr hNat
            _ = Int.ofNat xs.length - Int.ofNat pat.length :=
              Int.ofNat_sub hPatLe
    · have hNonneg :
          (0 : native_Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
        exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
      exact Int.le_trans (by decide : (-1 : native_Int) ≤ 0) hNonneg

theorem EvaluateProofInternal.native_seq_indexof_zero_nonneg_pat_le_len_local
    (xs pat : List SmtValue)
    (hIdx : 0 ≤ native_seq_indexof xs pat 0) :
    pat.length ≤ xs.length := by
  rw [native_seq_indexof_eq_rec] at hIdx
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add] at hIdx
  split at hIdx
  · assumption
  · have hContr : ¬ ((0 : native_Int) ≤ -1) := by decide
    exact False.elim (hContr hIdx)

theorem EvaluateProofInternal.native_seq_indexof_zero_nonneg_toNat_add_pat_le_len_local
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤ xs.length := by
  have hPatLe : pat.length ≤ xs.length :=
    EvaluateProofInternal.native_seq_indexof_zero_nonneg_pat_le_len_local xs pat hIdxNonneg
  have hIdxLe :=
    EvaluateProofInternal.native_seq_indexof_le_len_sub_pat_of_pat_le_len_local xs pat 0 hPatLe
  rw [← Int.ofNat_le]
  have hAdd := Int.add_le_of_le_sub_right hIdxLe
  have hMax :
      max (native_seq_indexof xs pat 0) 0 =
        native_seq_indexof xs pat 0 :=
    Int.max_eq_left hIdxNonneg
  simpa [Int.ofNat_toNat, hMax] using hAdd

theorem EvaluateProofInternal.native_seq_indexof_map_char_zero
    (s t : native_String) :
    native_seq_indexof (s.map SmtValue.Char) (t.map SmtValue.Char) 0 =
      native_str_indexof s t 0 := by
  rw [native_seq_indexof_eq_rec]
  unfold native_str_indexof
  simp [native_str_len]
  by_cases hBound : t.length ≤ s.length
  · simp [hBound]
    have hRec :=
      EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([] : native_String) s t
        (s.length - t.length + 1)
    simpa using hRec
  · simp [hBound]

theorem EvaluateProofInternal.native_str_indexof_eq_neg_one_of_neg
    (s pat : native_String)
    (hNeg : native_str_indexof s pat 0 < 0) :
    native_str_indexof s pat 0 = -1 := by
  have hCases :=
    native_seq_indexof_eq_neg_one_or_ge (s.map SmtValue.Char)
      (pat.map SmtValue.Char) (0 : native_Int)
  rw [EvaluateProofInternal.native_seq_indexof_map_char_zero] at hCases
  rcases hCases with hEq | hGe
  · exact hEq
  · have hNot : ¬ native_str_indexof s pat 0 < 0 :=
      Int.not_lt_of_ge hGe
    exact False.elim (hNot hNeg)

theorem EvaluateProofInternal.native_str_indexof_zero_nonneg_toNat_add_pat_le_len
    (s pat : native_String)
    (hIdxNonneg : 0 ≤ native_str_indexof s pat 0) :
    Int.toNat (native_str_indexof s pat 0) + pat.length ≤ s.length := by
  have hSeqNonneg :
      0 ≤ native_seq_indexof (s.map SmtValue.Char)
        (pat.map SmtValue.Char) 0 := by
    simpa [EvaluateProofInternal.native_seq_indexof_map_char_zero] using hIdxNonneg
  have hSeq :=
    EvaluateProofInternal.native_seq_indexof_zero_nonneg_toNat_add_pat_le_len_local
      (s.map SmtValue.Char) (pat.map SmtValue.Char) hSeqNonneg
  simpa [EvaluateProofInternal.native_seq_indexof_map_char_zero] using hSeq

theorem EvaluateProofInternal.native_seq_indexof_map_char
    (s t : native_String) (i : native_Int) :
    native_seq_indexof (s.map SmtValue.Char) (t.map SmtValue.Char) i =
      native_str_indexof s t i := by
  rw [native_seq_indexof_eq_rec]
  unfold native_str_indexof
  by_cases hi : i < 0
  · simp [hi]
  · simp [hi, List.length_map]
    let start := Int.toNat i
    by_cases hBound : start + t.length ≤ s.length
    · have hStartLe : start ≤ s.length := by omega
      have hBoundLeft : Int.toNat i + t.length ≤ s.length := by
        simpa [start] using hBound
      have hBound' :
          Int.toNat i + Int.toNat (native_str_len t) ≤
            Int.toNat (native_str_len s) := by
        simpa [start, native_str_len] using hBound
      rw [ite_eq_left hBoundLeft]
      rw [ite_eq_left hBound']
      have hDropMap :
          (s.map SmtValue.Char).drop start =
            (s.drop start).map SmtValue.Char := by
        simp [List.map_drop]
      rw [hDropMap]
      have hTakeLen : (s.take start).length = start := by
        simp [List.length_take, hStartLe]
      have hAppend : s.take start ++ s.drop start = s :=
        List.take_append_drop start s
      have hRec :=
        EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix (s.take start) (s.drop start)
          t (s.length - (start + t.length) + 1)
      rw [hTakeLen, hAppend] at hRec
      simpa [start, native_str_len] using hRec
    · have hBoundLeft : ¬ Int.toNat i + t.length ≤ s.length := by
        simpa [start] using hBound
      have hBound' :
          ¬ Int.toNat i + Int.toNat (native_str_len t) ≤
            Int.toNat (native_str_len s) := by
        simpa [start, native_str_len] using hBound
      rw [ite_eq_right hBoundLeft]
      rw [ite_eq_right hBound']

theorem EvaluateProofInternal.native_seq_indexof_pack_string
    (s t : native_String) (i : native_Int) :
    native_seq_indexof (native_unpack_seq (native_pack_string s))
        (native_unpack_seq (native_pack_string t)) i =
      native_str_indexof s t i := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string t) =
      t.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  simpa [impl_native_string_to_values] using
    EvaluateProofInternal.native_seq_indexof_map_char s t i

theorem EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string
    (s t : native_String) (i : native_Int) :
    __smtx_model_eval_str_indexof
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string t))
        (SmtValue.Numeral i) =
      SmtValue.Numeral (native_str_indexof s t i) := by
  simp only [__smtx_model_eval_str_indexof]
  rw [EvaluateProofInternal.native_seq_indexof_pack_string]

theorem EvaluateProofInternal.native_str_indexof_neg
    (s t : native_String) {i : native_Int}
    (hi : i < 0) :
    native_str_indexof s t i = -1 := by
  simp [native_str_indexof, hi]

theorem EvaluateProofInternal.native_str_indexof_gt_len
    (s t : native_String) {i : native_Int}
    (hi : native_str_len s < i) :
    native_str_indexof s t i = -1 := by
  unfold native_str_indexof
  have hLenNonneg : 0 ≤ native_str_len s := by
    simp [native_str_len]
  have hiNonneg : 0 ≤ i := Int.le_trans hLenNonneg (Int.le_of_lt hi)
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hiNonneg
  have hStartGt : s.length < Int.toNat i := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hiNonneg]
    simpa [native_str_len] using hi
  have hBound :
      ¬ Int.toNat i + Int.toNat (native_str_len t) ≤
        Int.toNat (native_str_len s) := by
    intro h
    have hLenEq : Int.toNat (native_str_len s) = s.length := by
      simp [native_str_len]
    rw [hLenEq] at h
    omega
  rw [ite_eq_right hNotNeg]
  dsimp
  rw [ite_eq_right hBound]

theorem EvaluateProofInternal.native_seq_indexof_neg_local
    (xs pat : List SmtValue) {i : native_Int}
    (hi : i < 0) :
    native_seq_indexof xs pat i = -1 := by
  simp [native_seq_indexof_eq_rec, hi]

theorem EvaluateProofInternal.native_seq_indexof_gt_len_local
    (xs pat : List SmtValue) {i : native_Int}
    (hi : Int.ofNat xs.length < i) :
    native_seq_indexof xs pat i = -1 := by
  rw [native_seq_indexof_eq_rec]
  have hLenNonneg : 0 ≤ (Int.ofNat xs.length : native_Int) := by
    exact Int.natCast_nonneg xs.length
  have hiNonneg : 0 ≤ i := Int.le_trans hLenNonneg (Int.le_of_lt hi)
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hiNonneg
  have hStartGt : xs.length < Int.toNat i := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hiNonneg]
    exact hi
  have hBound : ¬ Int.toNat i + pat.length ≤ xs.length := by
    intro h
    omega
  rw [ite_eq_right hNotNeg]
  dsimp
  rw [ite_eq_right hBound]

theorem EvaluateProofInternal.native_str_indexof_zero_of_prefix
    (s pat : native_String)
    (hPrefix : native_string_prefix_eq pat s = true) :
    native_str_indexof s pat 0 = 0 := by
  cases pat with
  | nil =>
      simp [native_str_indexof, impl_native_str_indexof_rec,
        native_string_prefix_eq, native_str_len]
  | cons p ps =>
      have hPatLe : (p :: ps).length ≤ s.length :=
        EvaluateProofInternal.native_string_prefix_eq_length_le (p :: ps) s hPrefix
      have hPatLe' : ps.length + 1 ≤ s.length := by
        simpa using hPatLe
      unfold native_str_indexof
      simp [native_str_len, hPatLe']
      unfold impl_native_str_indexof_rec
      simp [hPrefix]

theorem EvaluateProofInternal.native_seq_contains_pack_string
    (s t : native_String) :
    native_seq_contains (native_unpack_seq (native_pack_string s))
        (native_unpack_seq (native_pack_string t)) =
      native_not (native_zlt (native_str_indexof s t 0) 0) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string t) =
      t.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  unfold native_seq_contains
  rw [EvaluateProofInternal.native_seq_indexof_map_char_zero]
  by_cases hNeg : native_str_indexof s t 0 < 0
  · simp [native_zlt, native_not, hNeg]
  · have hNonneg : 0 ≤ native_str_indexof s t 0 :=
      Int.le_of_not_gt hNeg
    simp [native_zlt, native_not, hNeg, hNonneg]

