module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StrConcatSupport
import all Cpc.Proofs.RuleSupport.StrConcatSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
public import Cpc.Proofs.RuleSupport.DistinctTermsSupport
import all Cpc.Proofs.RuleSupport.DistinctTermsSupport
public import Cpc.Proofs.Translation.EoTypeof
import all Cpc.Proofs.Translation.EoTypeof

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-- Model-evaluation characterization of `str.contains`: when both arguments
    evaluate to sequence values, `str.contains x y` evaluates to the Boolean
    `native_seq_contains` of the underlying element lists. -/
theorem strContains_eval_eq (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y)) =
      SmtValue.Boolean
        (native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy)) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) =
      SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y) by rfl]
  rw [show __smtx_model_eval M (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_str_contains (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) by simp only [__smtx_model_eval]]
  rw [hx, hy]
  rfl

/-- Model-evaluation characterization of `str.++`: when both arguments evaluate
    to sequence values, `str.++ x y` evaluates to a sequence whose underlying
    element list is the concatenation of the two argument element lists. -/
theorem strConcat_unpack_eval (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    ∃ sxy,
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq sxy ∧
      native_unpack_seq sxy = native_unpack_seq sx ++ native_unpack_seq sy := by
  have h := smtx_model_eval_str_concat_term_eq M x y
  simp only [mkConcat] at h
  rw [h, hx, hy]
  refine ⟨_, rfl, ?_⟩
  simp [native_seq_concat, Smtm.native_unpack_pack_seq]

/-- Exact model-evaluation form of `str.++` on sequence-valued terms. -/
theorem strConcat_eval_eq (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx ++ native_unpack_seq sy)) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
      SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) by rfl]
  simp [__smtx_model_eval, hx, hy, __smtx_model_eval_str_concat,
    native_seq_concat]

/-- Exact model-evaluation form of `str.replace` on sequence-valued terms. -/
theorem strReplace_eval_eq (M : SmtModel) (x pat repl : Term)
    (sx spat srepl : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hpat : __smtx_model_eval M (__eo_to_smt pat) = SmtValue.Seq spat)
    (hrepl : __smtx_model_eval M (__eo_to_smt repl) = SmtValue.Seq srepl) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x)
            pat) repl)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx)
            (native_unpack_seq spat) (native_unpack_seq srepl))) := by
  rw [show __eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x)
        pat) repl) =
      SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
        (__eo_to_smt repl) by rfl]
  simp [__smtx_model_eval, hx, hpat, hrepl, __smtx_model_eval_str_replace]

/-! ### Native `contains` characterization and monotonicity -/

/-- A pattern is a prefix of itself followed by anything. -/
theorem native_seq_prefix_eq_append (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

/-- If `pat` occurs in `before ++ pat ++ after`, the bounded search does not
    return `-1` (provided there is enough fuel to reach the occurrence). -/
theorem native_seq_indexof_rec_append_ne_neg
    (pat after : List SmtValue) :
    ∀ (before : List SmtValue) (i fuel : Nat),
      before.length < fuel →
      native_seq_indexof_rec (before ++ pat ++ after) pat i fuel ≠ -1 := by
  intro before
  induction before with
  | nil =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          simp only [List.nil_append]
          unfold native_seq_indexof_rec
          rw [if_pos (native_seq_prefix_eq_append pat after)]
          simp
  | cons b bs ih =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          have hbs : bs.length < f := by
            simp only [List.length_cons] at hFuel; omega
          unfold native_seq_indexof_rec
          by_cases hPre : native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [if_pos hPre]; simp
          · rw [if_neg hPre]
            have hxs : (b :: bs) ++ pat ++ after = b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

/-- Occurrence direction: if `xs` decomposes as `before ++ pat ++ after`, then
    `native_seq_contains xs pat` holds. -/
theorem native_seq_contains_of_decomp (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  have hLen : pat.length ≤ (before ++ pat ++ after).length := by
    simp [List.length_append]; omega
  have hNe :
      native_seq_indexof (before ++ pat ++ after) pat 0 ≠ -1 := by
    rw [native_seq_indexof_eq_rec]
    simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
    rw [dif_pos hLen]
    have hFuel :
        before.length <
          (before ++ pat ++ after).length - pat.length + 1 := by
      simp [List.length_append]; omega
    simpa using
      native_seq_indexof_rec_append_ne_neg pat after before 0
        ((before ++ pat ++ after).length - pat.length + 1) hFuel
  have hGe :
      0 ≤ native_seq_indexof (before ++ pat ++ after) pat 0 := by
    rcases native_seq_indexof_eq_neg_one_or_ge (before ++ pat ++ after) pat 0 with h | h
    · exact absurd h hNe
    · exact h
  unfold native_seq_contains
  exact decide_eq_true hGe

/-- Forward direction: a positive `contains` yields an explicit decomposition. -/
theorem native_seq_contains_decomp_exists (xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    ∃ before after, xs = before ++ pat ++ after := by
  have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at h
    exact of_decide_eq_true h
  exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩

/-- `contains` characterization in terms of list decomposition. -/
theorem native_seq_contains_iff_decomp (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔ ∃ before after, xs = before ++ pat ++ after := by
  constructor
  · exact native_seq_contains_decomp_exists xs pat
  · rintro ⟨before, after, rfl⟩
    exact native_seq_contains_of_decomp before pat after

/-- Appending on the right preserves `contains`. -/
theorem native_seq_contains_append_right (xs rest pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    native_seq_contains (xs ++ rest) pat = true := by
  rcases native_seq_contains_decomp_exists xs pat h with ⟨before, after, rfl⟩
  have : before ++ pat ++ after ++ rest = before ++ pat ++ (after ++ rest) := by
    simp [List.append_assoc]
  rw [this]
  exact native_seq_contains_of_decomp before pat (after ++ rest)

/-- Appending on the left preserves `contains`. -/
theorem native_seq_contains_append_left (pre xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    native_seq_contains (pre ++ xs) pat = true := by
  rcases native_seq_contains_decomp_exists xs pat h with ⟨before, after, rfl⟩
  have : pre ++ (before ++ pat ++ after) = (pre ++ before) ++ pat ++ after := by
    simp [List.append_assoc]
  rw [this]
  exact native_seq_contains_of_decomp (pre ++ before) pat after

/-! ### Prefix / compatibility lemmas -/

/-- `native_seq_prefix_eq a b` holds iff `a` is a list-prefix of `b`. -/
theorem native_seq_prefix_eq_iff (a b : List SmtValue) :
    native_seq_prefix_eq a b = true ↔ ∃ r, b = a ++ r := by
  constructor
  · intro h
    exact ⟨b.drop a.length, (native_seq_prefix_eq_append_drop a b h).symm⟩
  · rintro ⟨r, rfl⟩
    exact native_seq_prefix_eq_append a r

/-- Two lists are *overlap-compatible* if one is a prefix of the other. -/
def native_seq_compat (a b : List SmtValue) : Prop :=
  native_seq_prefix_eq a b = true ∨ native_seq_prefix_eq b a = true

/-- If two lists agree after appending (aligned at the front), then one of their
    heads is a prefix of the other. -/
theorem native_seq_compat_of_append_eq (a s d t : List SmtValue)
    (h : a ++ s = d ++ t) : native_seq_compat a d := by
  rcases Nat.le_total a.length d.length with hle | hle
  · left
    rw [native_seq_prefix_eq_iff]
    have h1 : (a ++ s).take a.length = (d ++ t).take a.length := by rw [h]
    rw [List.take_left, List.take_append_of_le_length hle] at h1
    refine ⟨d.drop a.length, ?_⟩
    have h2 : d.take a.length ++ d.drop a.length = d := List.take_append_drop a.length d
    rw [← h1] at h2
    exact h2.symm
  · right
    rw [native_seq_prefix_eq_iff]
    have h1 : (d ++ t).take d.length = (a ++ s).take d.length := by rw [h]
    rw [List.take_left, List.take_append_of_le_length hle] at h1
    refine ⟨a.drop d.length, ?_⟩
    have h2 : a.take d.length ++ a.drop d.length = a := List.take_append_drop d.length a
    rw [← h1] at h2
    exact h2.symm

/-! ### Window lemmas: occurrence survives `take`/`drop` -/

/-- An occurrence wholly contained in a `take k` prefix survives the truncation. -/
theorem native_seq_contains_take_of_decomp
    (before pat after : List SmtValue) (k : Nat)
    (hk : before.length + pat.length ≤ k) :
    native_seq_contains ((before ++ pat ++ after).take k) pat = true := by
  obtain ⟨m, hm⟩ : ∃ m, k = (before ++ pat).length + m :=
    ⟨k - (before ++ pat).length, by simp [List.length_append] at hk ⊢; omega⟩
  rw [hm, List.take_length_add_append]
  exact native_seq_contains_of_decomp before pat (after.take m)

/-- An occurrence wholly after the first `k` elements survives `drop k`. -/
theorem native_seq_contains_drop_of_decomp
    (before pat after : List SmtValue) (k : Nat)
    (hk : k ≤ before.length) :
    native_seq_contains ((before ++ pat ++ after).drop k) pat = true := by
  rw [List.append_assoc, List.drop_append_of_le_length hk, ← List.append_assoc]
  exact native_seq_contains_of_decomp (before.drop k) pat after

/-! ### The combinatorial core: no cross-boundary occurrence -/

/-- **Overlap split for `contains`.**

If no nonempty suffix of `C` is overlap-compatible with `D` (`hA`), and no
nonempty suffix of `D` is overlap-compatible with `C` (`hB`), then `D` cannot
occur straddling the middle block `C`: any occurrence of `D` in `T ++ C ++ S`
lies entirely within `T` or entirely within `S`. -/
theorem native_seq_contains_split_of_no_overlap
    (T C S D : List SmtValue)
    (hA : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D)
    (hB : ∀ k, k < D.length → ¬ native_seq_compat (D.drop k) C)
    (h : native_seq_contains (T ++ C ++ S) D = true) :
    native_seq_contains T D = true ∨ native_seq_contains S D = true := by
  rcases native_seq_contains_decomp_exists (T ++ C ++ S) D h with ⟨before, after, hEq⟩
  -- The occurrence starts at position `before.length`.
  have e1 : (before ++ D ++ after).drop before.length = D ++ after := by
    rw [List.append_assoc before D after]; exact List.drop_left
  have hdropT : (T ++ C ++ S).drop T.length = C ++ S := by
    rw [List.append_assoc]; exact List.drop_left
  by_cases h1 : before.length + D.length ≤ T.length
  · -- window within `T`
    left
    have hTtake : (before ++ D ++ after).take T.length = T := by
      rw [← hEq, List.append_assoc]; exact List.take_left
    have hwin := native_seq_contains_take_of_decomp before D after T.length h1
    rw [hTtake] at hwin
    exact hwin
  · by_cases h2 : T.length + C.length ≤ before.length
    · -- window within `S`
      right
      have hSdrop : (before ++ D ++ after).drop (T.length + C.length) = S := by
        rw [← hEq,
          show T.length + C.length = (T ++ C).length by rw [List.length_append]]
        exact List.drop_left
      have hwin := native_seq_contains_drop_of_decomp before D after (T.length + C.length) h2
      rw [hSdrop] at hwin
      exact hwin
    · -- window straddles `C`: contradiction
      exfalso
      by_cases hpT : T.length ≤ before.length
      · -- starts inside `C`
        obtain ⟨j, hpj⟩ : ∃ j, before.length = T.length + j :=
          ⟨before.length - T.length, by omega⟩
        have hjlt : j < C.length := by omega
        have e2 : (before ++ D ++ after).drop before.length = C.drop j ++ S := by
          rw [← hEq, hpj, ← List.drop_drop, hdropT,
            List.drop_append_of_le_length (Nat.le_of_lt hjlt)]
        have hAppend : C.drop j ++ S = D ++ after := by rw [← e2]; exact e1
        exact hA j hjlt (native_seq_compat_of_append_eq (C.drop j) S D after hAppend)
      · -- starts inside `T`, extends into `C`
        obtain ⟨m, hTm⟩ : ∃ m, T.length = before.length + m :=
          ⟨T.length - before.length, by omega⟩
        have hmlt : m < D.length := by omega
        have e3 : (before ++ D ++ after).drop T.length = D.drop m ++ after := by
          rw [hTm, ← List.drop_drop, e1,
            List.drop_append_of_le_length (Nat.le_of_lt hmlt)]
        have hAppend : D.drop m ++ after = C ++ S := by
          rw [← e3, ← hEq]; exact hdropT
        exact hB m hmlt (native_seq_compat_of_append_eq (D.drop m) after C S hAppend)

/-- Full `contains` split equivalence under the no-overlap conditions. -/
theorem native_seq_contains_split_iff_of_no_overlap
    (T C S D : List SmtValue)
    (hA : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D)
    (hB : ∀ k, k < D.length → ¬ native_seq_compat (D.drop k) C) :
    native_seq_contains (T ++ C ++ S) D = true ↔
      (native_seq_contains T D = true ∨ native_seq_contains S D = true) := by
  constructor
  · exact native_seq_contains_split_of_no_overlap T C S D hA hB
  · rintro (hT | hS)
    · rw [List.append_assoc]
      exact native_seq_contains_append_right T (C ++ S) D hT
    · exact native_seq_contains_append_left (T ++ C) S D hS

/-! ### Bridge: `value_len` / `flatten` / `overlap_rec` term-computations

The rule's side conditions are EO term-level computations on the (flattened)
word arguments.  `__str_flatten (__str_nary_intro ·)` normalizes a word literal
into a canonical single-character `str.++`-chain (`charChainTerm`), on which
`__str_overlap_rec` computes the overlap "drop count" (`overlapDrop`) and
`__str_is_compatible` computes list prefix-compatibility. -/

/-- Canonical single-character `str.++` chain produced by `flatten`. -/
def charChainTerm : native_String → Term
  | [] => Term.String []
  | ch :: rest =>
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [ch]))
        (charChainTerm rest)

/-- Char-list overlap-compatibility: one is a prefix of the other. -/
def strCompat (x y : native_String) : Bool :=
  native_string_prefix_eq x y || native_string_prefix_eq y x

/-- The "overlap drop count": leading chars dropped from `x` until a suffix is
    compatible with `y`. -/
def overlapDrop : native_String → native_String → Nat
  | [], _ => 0
  | a :: x, y => if strCompat (a :: x) y then 0 else 1 + overlapDrop x y

theorem strChar_typeof (a : Nat) :
    __eo_typeof (Term.String [a]) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  rw [show __eo_typeof (Term.String [a]) = __eo_lit_type_String (Term.String [a]) from rfl]
  simp [__eo_lit_type_String]

theorem strChar_is_str (a : Nat) : __eo_is_str (Term.String [a]) = Term.Boolean true := by
  simp [__eo_is_str, __eo_is_str_internal, native_teq, SmtEval.native_and, SmtEval.native_not]

theorem strChar_eq (a b : Nat) :
    __eo_eq (Term.String [a]) (Term.String [b]) = Term.Boolean (decide (a = b)) := by
  simp [__eo_eq, native_teq]; rw [eq_comm]

theorem charChainTerm_ne_stuck (y : native_String) : charChainTerm y ≠ Term.Stuck := by
  cases y <;> simp [charChainTerm]

theorem overlap_rec_concat (s s1 t : Term) (ht : t ≠ Term.Stuck) :
    __str_overlap_rec (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) s1) t =
      __eo_ite (__str_is_compatible (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) s1) t)
        (Term.Numeral 0) (__eo_add (Term.Numeral 1) (__str_overlap_rec s1 t)) := by
  cases t <;> simp_all [__str_overlap_rec]

theorem overlap_rec_emptyfirst (t : Term) (ht : t ≠ Term.Stuck) :
    __str_overlap_rec (Term.String []) t = Term.Numeral 0 := by
  cases t <;> simp_all [__str_overlap_rec]

/-- `is_compatible` on char-chains computes list prefix-compatibility. -/
theorem str_is_compatible_charChain (x y : native_String) :
    __str_is_compatible (charChainTerm x) (charChainTerm y) =
      Term.Boolean (native_string_prefix_eq x y || native_string_prefix_eq y x) := by
  induction x generalizing y with
  | nil =>
      cases y <;>
        simp [charChainTerm, __str_is_compatible, __eo_l_1___str_is_compatible,
          __str_is_empty, __eo_or, native_string_prefix_eq,
          SmtEval.native_or]
  | cons a x ih =>
      cases y with
      | nil =>
          simp [charChainTerm, __str_is_compatible, __eo_l_1___str_is_compatible,
            __str_is_empty, __eo_or, native_string_prefix_eq,
            SmtEval.native_or]
      | cons b y =>
          by_cases hab : a = b
          · subst hab
            simp [charChainTerm, __str_is_compatible, strChar_eq, native_teq,
              SmtEval.native_ite, ih y, native_string_prefix_eq]
          · have hba : b ≠ a := fun h => hab h.symm
            simp [charChainTerm, __str_is_compatible, strChar_eq, decide_eq_false hab,
              native_teq, SmtEval.native_ite, __eo_l_1___str_is_compatible, __eo_requires,
              strChar_typeof, __are_distinct_terms_type, __eo_and, strChar_is_str,
              native_string_prefix_eq, SmtEval.native_and, SmtEval.native_not, hba]

/-- `overlap_rec` on char-chains computes the overlap drop count. -/
theorem str_overlap_rec_charChain (x y : native_String) :
    __str_overlap_rec (charChainTerm x) (charChainTerm y) =
      Term.Numeral (Int.ofNat (overlapDrop x y)) := by
  induction x with
  | nil => simp [charChainTerm, overlapDrop, overlap_rec_emptyfirst _ (charChainTerm_ne_stuck y)]
  | cons a x ih =>
      rw [show charChainTerm (a :: x) =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [a]))
              (charChainTerm x) from rfl,
        overlap_rec_concat _ _ _ (charChainTerm_ne_stuck y),
        show (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [a]))
              (charChainTerm x)) = charChainTerm (a :: x) from rfl,
        str_is_compatible_charChain (a :: x) y,
        show (native_string_prefix_eq (a :: x) y || native_string_prefix_eq y (a :: x)) =
          strCompat (a :: x) y from rfl]
      cases hbc : strCompat (a :: x) y with
      | true => simp [__eo_ite, native_teq, SmtEval.native_ite, overlapDrop, hbc]
      | false =>
          simp only [overlapDrop, hbc]
          simp [__eo_ite, native_teq, SmtEval.native_ite, ih, __eo_add, native_zplus]

/-- `value_len` of a string literal is its length. -/
theorem str_value_len_string (w : native_String) :
    __str_value_len (Term.String w) = Term.Numeral (Int.ofNat w.length) := by
  simp [__str_value_len, __eo_requires, __eo_is_str, __eo_is_str_internal, __eo_len,
    native_str_len, native_teq, SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not]

theorem overlapDrop_le (x y : native_String) : overlapDrop x y ≤ x.length := by
  induction x with
  | nil => simp [overlapDrop]
  | cons a x ih => simp only [overlapDrop, List.length_cons]; split <;> omega

/-- If the overlap drop count equals the full length, no nonempty suffix of `x`
    is compatible with `y`. -/
theorem overlapDrop_full_no_compat :
    ∀ (x y : native_String), overlapDrop x y = x.length →
      ∀ k, k < x.length → strCompat (x.drop k) y = false
  | [], y, h, k, hk => by simp at hk
  | a :: x, y, h, k, hk => by
      have hbc : strCompat (a :: x) y = false := by
        rcases hbcc : strCompat (a :: x) y with _ | _
        · rfl
        · exfalso; simp [overlapDrop, hbcc, List.length_cons] at h
      have hx : overlapDrop x y = x.length := by
        have h2 := h; simp [overlapDrop, hbc, List.length_cons] at h2; omega
      cases k with
      | zero => simpa using hbc
      | succ j =>
          have hj : j < x.length := by simp only [List.length_cons] at hk; omega
          simpa [List.drop_succ_cons] using overlapDrop_full_no_compat x y hx j hj

/-- The element list of an evaluated string literal is its chars tagged as
    `SmtValue.Char`. -/
theorem unpack_pack_string_map (w : native_String) :
    native_unpack_seq (native_pack_string w) = w.map SmtValue.Char := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

/-- Prefix-equality is preserved (both ways) by the injective `SmtValue.Char` tag. -/
theorem prefix_eq_map_char (a b : native_String) :
    native_seq_prefix_eq (a.map SmtValue.Char) (b.map SmtValue.Char) =
      native_string_prefix_eq a b := by
  induction a generalizing b with
  | nil => simp [native_seq_prefix_eq, native_string_prefix_eq]
  | cons c cs ih =>
      cases b with
      | nil => simp [native_seq_prefix_eq, native_string_prefix_eq]
      | cons d ds => simp [native_seq_prefix_eq, native_string_prefix_eq, native_veq, ih]

/-- The native no-overlap condition `(A)`, at the `SmtValue` level, from a full
    overlap drop count. -/
theorem no_compat_of_overlap_full (w w' : native_String)
    (hov : overlapDrop w w' = w.length) :
    ∀ k, k < (w.map SmtValue.Char).length →
      ¬ native_seq_compat ((w.map SmtValue.Char).drop k) (w'.map SmtValue.Char) := by
  intro k hk
  rw [List.length_map] at hk
  rw [← List.map_drop]
  intro hcompat
  have hsq := overlapDrop_full_no_compat w w' hov k hk
  unfold strCompat at hsq
  rw [Bool.or_eq_false_iff] at hsq
  unfold native_seq_compat at hcompat
  rw [prefix_eq_map_char, prefix_eq_map_char] at hcompat
  rcases hcompat with h | h
  · rw [hsq.1] at h; exact absurd h (by simp)
  · rw [hsq.2] at h; exact absurd h (by simp)

/-! ### Flatten structure: `flatten (nary_intro (String w))` is the char-chain -/

theorem extractString_cons_zero (c : native_Char) (cs : native_String) :
    extractString (c :: cs) 0 = [c] := by
  have h : native_str_len (c :: cs) = Int.ofNat (cs.length + 1) := by simp [native_str_len]
  have hge : (1:Int) ≤ native_str_len (c :: cs) - 0 := by
    rw [h, Int.sub_zero, Int.ofNat_eq_natCast]; omega
  unfold extractString native_str_substr
  rw [if_neg (by simp [native_str_len, native_zplus, native_zneg])]
  rw [show native_zplus (native_zplus 0 (native_zneg 0)) 1 = 1 from by simp [native_zplus, native_zneg]]
  rw [Int.min_eq_left hge]
  simp

theorem substrWord_eq_charChainTerm (w : native_String) :
    substrWord w 0 w.length = charChainTerm w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
      rw [show (c :: cs).length = cs.length + 1 from rfl, substrWord,
        show ((0:Int) + 1) = 1 from by omega, substrWord_cons_tail c cs, ih,
        extractString_cons_zero c cs]
      rfl

/-- `flatten (nary_intro (String w))` is exactly the canonical char-chain. -/
theorem flatten_nary_intro_string (w : native_String) :
    __str_flatten (__str_nary_intro (Term.String w)) = charChainTerm w := by
  cases w with
  | nil => rw [str_flatten_nary_intro_empty]; rfl
  | cons c cs => rw [str_flatten_nary_intro_cons, substrWord_eq_charChainTerm]

/-- The rule's `gt` side condition (`= false`) forces a full overlap drop count. -/
theorem overlap_cond_implies_overlapDrop_full (w w' : native_String)
    (hcond : __eo_gt (__str_value_len (Term.String w))
        (__str_overlap_rec (__str_flatten (__str_nary_intro (Term.String w)))
          (__str_flatten (__str_nary_intro (Term.String w')))) = Term.Boolean false) :
    overlapDrop w w' = w.length := by
  rw [str_value_len_string, flatten_nary_intro_string, flatten_nary_intro_string,
    str_overlap_rec_charChain] at hcond
  simp only [__eo_gt, native_zlt] at hcond
  have hd : decide (Int.ofNat (overlapDrop w w') < Int.ofNat w.length) = false := by
    injection hcond
  have hnlt : ¬ (Int.ofNat (overlapDrop w w') < Int.ofNat w.length) := of_decide_eq_false hd
  simp only [Int.ofNat_eq_natCast] at hnlt
  have hle := overlapDrop_le w w'
  omega

/-! ### General atom-chains (handles `seq_unit` words, not just `String` literals)

A flattened word is a `str.++` chain of *atoms* (each a single-element term:
`String[ch]` for `Seq Char` literals, `seq_unit v` for general sequences),
terminated by an "empty".  `is_compatible`/`overlap_rec` compare atoms with the
*syntactic* `__eo_eq`; under the rule's guards (no comparison is `Stuck`), this
matches a syntactic list prefix-compatibility on the atom list. -/

/-- Syntactic list prefix on terms. -/
def listPrefixEq : List Term → List Term → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a = b) && listPrefixEq as bs

/-- Syntactic overlap-compatibility on term lists. -/
def listCompat (x y : List Term) : Bool := listPrefixEq x y || listPrefixEq y x

/-- Overlap drop count on term lists. -/
def listOverlapDrop : List Term → List Term → Nat
  | [], _ => 0
  | a :: x, y => if listCompat (a :: x) y then 0 else 1 + listOverlapDrop x y

theorem listOverlapDrop_le (x y : List Term) : listOverlapDrop x y ≤ x.length := by
  induction x with
  | nil => simp [listOverlapDrop]
  | cons a x ih => simp only [listOverlapDrop, List.length_cons]; split <;> omega

theorem listOverlapDrop_full_no_compat :
    ∀ (x y : List Term), listOverlapDrop x y = x.length →
      ∀ k, k < x.length → listCompat (x.drop k) y = false
  | [], y, h, k, hk => by simp at hk
  | a :: x, y, h, k, hk => by
      have hbc : listCompat (a :: x) y = false := by
        rcases hbcc : listCompat (a :: x) y with _ | _
        · rfl
        · exfalso; simp [listOverlapDrop, hbcc, List.length_cons] at h
      have hx : listOverlapDrop x y = x.length := by
        have h2 := h; simp [listOverlapDrop, hbc, List.length_cons] at h2; omega
      cases k with
      | zero => simpa using hbc
      | succ j =>
          have hj : j < x.length := by simp only [List.length_cons] at hk; omega
          simpa [List.drop_succ_cons] using listOverlapDrop_full_no_compat x y hx j hj

/-- `__eo_eq` is syntactic term equality (away from `Stuck`). -/
theorem eo_eq_val (a b : Term) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_eq a b = Term.Boolean (native_teq b a) := by
  unfold __eo_eq; split <;> simp_all

/-- The `str.++`-chain of atoms terminated by `e`. -/
def atomChainTerm (atoms : List Term) (e : Term) : Term :=
  atoms.foldr (fun a acc => Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) acc) e

end RuleProofs
end

open Eo
open SmtEval
open Smtm

namespace RuleProofs

theorem atomChainTerm_cons (a : Term) (xs : List Term) (e : Term) :
    atomChainTerm (a :: xs) e =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) (atomChainTerm xs e) := rfl

end RuleProofs

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem atomChainTerm_ne_stuck (xs : List Term) (e : Term) (he : e ≠ Term.Stuck) :
    atomChainTerm xs e ≠ Term.Stuck := by
  cases xs with
  | nil => exact he
  | cons a xs => rw [atomChainTerm_cons]; simp

theorem atomChainTerm_append (xs ys : List Term) (e : Term) :
    atomChainTerm (xs ++ ys) e = atomChainTerm xs (atomChainTerm ys e) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.cons_append, atomChainTerm_cons, ih, atomChainTerm_cons]

/-- `is_compatible` on atom-chains computes syntactic list compatibility, under
    the resolution guard (every atom pair is syntactically equal or provably
    distinct — i.e. comparisons never get `Stuck`). -/
theorem is_compatible_atomChain (ex ey : Term)
    (hexL : ∀ Z, __str_is_compatible ex Z = Term.Boolean true)
    (heyR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) ey = Term.Boolean true) :
    ∀ (xs ys : List Term),
      (∀ a ∈ xs, a ≠ Term.Stuck) → (∀ b ∈ ys, b ≠ Term.Stuck) →
      (∀ a ∈ xs, ∀ b ∈ ys,
        a = b ∨ __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true) →
      __str_is_compatible (atomChainTerm xs ex) (atomChainTerm ys ey) =
        Term.Boolean (listCompat xs ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ _
      simp only [atomChainTerm, List.foldr_nil, hexL, listCompat, listPrefixEq, Bool.true_or]
  | cons a xs ih =>
      intro ys hxne hyne hg
      cases ys with
      | nil =>
          rw [atomChainTerm_cons, show atomChainTerm [] ey = ey from rfl, heyR]
          simp [listCompat, listPrefixEq]
      | cons b ys =>
          have ha : a ≠ Term.Stuck := hxne a (by simp)
          have hb : b ≠ Term.Stuck := hyne b (by simp)
          rw [atomChainTerm_cons, atomChainTerm_cons]
          simp only [__str_is_compatible]
          by_cases hab : a = b
          · subst hab
            rw [eo_eq_val a a ha ha]
            have htt : native_teq a a = true := by simp [native_teq]
            simp only [__eo_ite, native_teq, SmtEval.native_ite]
            rw [ih ys (fun a' h' => hxne a' (by simp [h'])) (fun b' h' => hyne b' (by simp [h']))
              (fun a' ha' b' hb' => hg a' (by simp [ha']) b' (by simp [hb']))]
            simp [listCompat, listPrefixEq]
          · have hba : b ≠ a := fun h => hab h.symm
            have heqab : __eo_eq a b = Term.Boolean false := by
              rw [eo_eq_val a b ha hb]; congr 1
              simp only [native_teq]; exact decide_eq_false hba
            have hdist : __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true := by
              rcases hg a (by simp) b (by simp) with h | h
              · exact absurd h hab
              · exact h
            simp [__eo_ite, __eo_l_1___str_is_compatible, __eo_requires, heqab, native_teq,
              SmtEval.native_ite, SmtEval.native_not, hdist, listCompat, listPrefixEq, hab, hba]

/-- `overlap_rec` on atom-chains computes the list overlap drop count. -/
theorem overlap_rec_atomChain (ex ey : Term)
    (heyne : ey ≠ Term.Stuck)
    (hexL : ∀ Z, __str_is_compatible ex Z = Term.Boolean true)
    (heyR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) ey = Term.Boolean true)
    (hexO : ∀ Z, __str_overlap_rec ex Z = Term.Numeral 0) :
    ∀ (xs ys : List Term),
      (∀ a ∈ xs, a ≠ Term.Stuck) → (∀ b ∈ ys, b ≠ Term.Stuck) →
      (∀ a ∈ xs, ∀ b ∈ ys,
        a = b ∨ __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true) →
      __str_overlap_rec (atomChainTerm xs ex) (atomChainTerm ys ey) =
        Term.Numeral (Int.ofNat (listOverlapDrop xs ys)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ _
      rw [show atomChainTerm [] ex = ex from rfl, hexO]
      simp [listOverlapDrop]
  | cons a xs ih =>
      intro ys hxne hyne hg
      rw [atomChainTerm_cons,
        overlap_rec_concat _ _ _ (atomChainTerm_ne_stuck ys ey heyne),
        ← atomChainTerm_cons,
        is_compatible_atomChain ex ey hexL heyR (a :: xs) ys hxne hyne hg]
      have ihres := ih ys (fun a' h' => hxne a' (by simp [h'])) hyne
        (fun a' ha' b' hb' => hg a' (by simp [ha']) b' hb')
      cases hbc : listCompat (a :: xs) ys with
      | true => simp [__eo_ite, native_teq, SmtEval.native_ite, listOverlapDrop, hbc]
      | false =>
          simp only [listOverlapDrop, hbc]
          simp [__eo_ite, native_teq, SmtEval.native_ite, ihres, __eo_add, native_zplus]

/-! ### Atom → value mapping

Under atom→value injectivity (distinct atoms have distinct values — from the
resolution guard plus `are_distinct` soundness), syntactic list compatibility on
atoms determines native value compatibility on the underlying value lists. -/

theorem listPrefixEq_of_map_prefix (f : Term → SmtValue) :
    ∀ (As Bs : List Term),
      (∀ a ∈ As, ∀ b ∈ Bs, f a = f b → a = b) →
      native_seq_prefix_eq (As.map f) (Bs.map f) = true → listPrefixEq As Bs = true := by
  intro As
  induction As with
  | nil => intro Bs _ _; rfl
  | cons a As ih =>
      intro Bs hinj h
      cases Bs with
      | nil => simp [native_seq_prefix_eq] at h
      | cons b Bs =>
          simp only [List.map_cons, native_seq_prefix_eq, native_veq, Bool.and_eq_true,
            decide_eq_true_eq] at h
          have hab : a = b := hinj a (by simp) b (by simp) h.1
          subst hab
          simp only [listPrefixEq, decide_true, Bool.true_and]
          exact ih Bs (fun a' ha' b' hb' => hinj a' (by simp [ha']) b' (by simp [hb']))
            (by simpa using h.2)

/-- Native value compatibility implies syntactic atom compatibility (so its
    negation transfers from atoms to values). -/
theorem native_seq_compat_to_listCompat (f : Term → SmtValue) (As Bs : List Term)
    (hinj : ∀ a ∈ As, ∀ b ∈ Bs, f a = f b → a = b)
    (h : native_seq_compat (As.map f) (Bs.map f)) : listCompat As Bs = true := by
  unfold native_seq_compat at h
  unfold listCompat
  rcases h with h | h
  · rw [listPrefixEq_of_map_prefix f As Bs hinj h]; simp
  · rw [listPrefixEq_of_map_prefix f Bs As (fun b hb a ha hba => (hinj a ha b hb hba.symm).symm) h]
    simp

/-- `__eo_eq` is syntactic term equality (when it yields `true`). -/
theorem eq_of_eo_eq (x y : Term) (h : __eo_eq x y = Term.Boolean true) : y = x := by
  cases x <;> cases y <;> simp_all [__eo_eq, native_teq]

/-- Splitting a true `__eo_and` into its two true conjuncts. -/
theorem eo_and_true_split (a b : Term) (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;> simp_all [__eo_and, native_and, SmtEval.native_and]
  -- every branch of the guard yields a non-`Boolean` constructor, so a full
  -- `simp at h` derives `False` directly; `split` no longer fires on the
  -- `decide _ = true` conditions these guards now carry.
  all_goals (simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h)
  all_goals (split at h <;> exact Term.noConfusion h)

/-- An empty word evaluates to a sequence with empty underlying element list. -/
theorem str_is_empty_eval_unpack_nil (M : SmtModel) (e : Term) (s : SmtSeq)
    (hemp : __str_is_empty e = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt e) = SmtValue.Seq s) :
    native_unpack_seq s = [] := by
  unfold __str_is_empty at hemp
  split at hemp
  · exact Term.noConfusion hemp
  · rename_i U
    rw [show __eo_to_smt (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
        __eo_to_smt_seq_empty (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U)) from rfl] at hev
    simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at hev
    split at hev
    · simp only [__eo_to_smt_seq_empty, __smtx_model_eval] at hev
      exact SmtValue.noConfusion hev
    · rw [show __eo_to_smt_seq_empty (SmtType.Seq (__eo_to_smt_type U)) =
          SmtTerm.seq_empty (__eo_to_smt_type U) from rfl,
        show __smtx_model_eval M (SmtTerm.seq_empty (__eo_to_smt_type U)) =
          SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) from by simp only [__smtx_model_eval]] at hev
      injection hev with hev; rw [← hev]; rfl
  · rw [show __eo_to_smt (Term.String []) = SmtTerm.String [] from rfl,
      show __smtx_model_eval M (SmtTerm.String []) = SmtValue.Seq (native_pack_string []) from by
        simp only [__smtx_model_eval]] at hev
    injection hev with hev; rw [← hev]
    simp [native_pack_string, native_pack_seq, native_unpack_seq]
  · simp at hemp

/-- `__eo_mk_apply` on non-`Stuck` arguments is plain application. -/
theorem mk_apply_eq (x y : Term) (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  cases x <;> cases y <;> simp_all [__eo_mk_apply]

/-- `flatten` keeps a non-`String`, non-concat head atom (e.g. a `seq_unit`) in
    place. -/
theorem flatten_concat_nonstr (a rest : Term) (ha : __eo_is_str a = Term.Boolean false)
    (hconcat : ∀ t tail, a ≠
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)
    (hrest : __str_flatten rest ≠ Term.Stuck) :
    __str_flatten (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) rest) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) (__str_flatten rest) := by
  cases a with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op
              case str_concat => exact False.elim (hconcat y x rfl)
              all_goals
                change
                  __eo_ite (__eo_is_str _) _
                      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) _)
                        (__str_flatten rest)) =
                    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) _)
                      (__str_flatten rest)
                rw [ha]
                simp [__eo_ite]
                exact mk_apply_eq _ _ (by simp) hrest
          | _ =>
              change
                __eo_ite (__eo_is_str _) _
                    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) _)
                      (__str_flatten rest)) =
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) _)
                    (__str_flatten rest)
              rw [ha]
              simp [__eo_ite]
              exact mk_apply_eq _ _ (by simp) hrest
      | _ =>
          change
            __eo_ite (__eo_is_str _) _
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) _)
                  (__str_flatten rest)) =
              Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) _)
                (__str_flatten rest)
          rw [ha]
          simp [__eo_ite]
          exact mk_apply_eq _ _ (by simp) hrest
  | _ =>
      change
        __eo_ite (__eo_is_str _) _
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) _)
              (__str_flatten rest)) =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) _)
            (__str_flatten rest)
      rw [ha]
      simp [__eo_ite]
      exact mk_apply_eq _ _ (by simp) hrest

/-- The no-overlap `(A)` condition for `String`-literal arguments, from the `gt`
    side-condition (composes the committed String bridge). -/
theorem no_compat_string (wc wd : native_String)
    (hgt : __eo_gt (__str_value_len (Term.String wc))
        (__str_overlap_rec (__str_flatten (__str_nary_intro (Term.String wc)))
          (__str_flatten (__str_nary_intro (Term.String wd)))) = Term.Boolean false) :
    ∀ k, k < (wc.map SmtValue.Char).length →
      ¬ native_seq_compat ((wc.map SmtValue.Char).drop k) (wd.map SmtValue.Char) :=
  no_compat_of_overlap_full wc wd (overlap_cond_implies_overlapDrop_full wc wd hgt)

theorem atomChainTerm_charAtoms (w : native_String) :
    atomChainTerm (w.map (fun ch => Term.String [ch])) (Term.String []) =
      charChainTerm w := by
  induction w with
  | nil => rfl
  | cons ch rest ih =>
      change atomChainTerm (Term.String [ch] :: rest.map (fun ch => Term.String [ch]))
          (Term.String []) = charChainTerm (ch :: rest)
      rw [atomChainTerm_cons]
      simp [charChainTerm, ih]

/-! ### Model-eval of the rule equation -/

/-- `contains` evaluating to a Boolean forces both arguments to evaluate to
    sequence values. -/
theorem contains_args_seq_of_eval_bool (M : SmtModel) (x y : Term) (b : Bool)
    (h : __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y))
      = SmtValue.Boolean b) :
    (∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) ∧
      (∃ sy, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) =
      SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y) from rfl] at h
  rw [show __smtx_model_eval M (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_str_contains (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) from by simp only [__smtx_model_eval]] at h
  cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
    cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
    simp_all [__smtx_model_eval_str_contains]

/-- Model-evaluation of an `or`. -/
theorem model_eval_or_eq (M : SmtModel) (A B : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)) =
      __smtx_model_eval_or (__smtx_model_eval M (__eo_to_smt A))
        (__smtx_model_eval M (__eo_to_smt B)) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) =
      SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) from rfl]
  simp only [__smtx_model_eval]

/-- The rule's two sides evaluate equally, given the operands' sequence values,
    `emp` empty, and the no-overlap conditions `(A)/(B)` on the middle/needle. -/
theorem overlap_split_eval (M : SmtModel) (t c sw emp d : Term)
    (St Sc Ss Se Sd : SmtSeq)
    (ht : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq St)
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hsw : __smtx_model_eval M (__eo_to_smt sw) = SmtValue.Seq Ss)
    (hemp : __smtx_model_eval M (__eo_to_smt emp) = SmtValue.Seq Se)
    (hd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hempnil : native_unpack_seq Se = [])
    (hA : ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd))
    (hB : ∀ k, k < (native_unpack_seq Sd).length →
      ¬ native_seq_compat ((native_unpack_seq Sd).drop k) (native_unpack_seq Sc)) :
    __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)))) d)) =
      __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) t) d))
          (Term.Apply (Term.Apply (Term.UOp UserOp.or)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) sw) d))
            (Term.Boolean false)))) := by
  obtain ⟨s1, hs1, hu1⟩ := strConcat_unpack_eval M sw emp Ss Se hsw hemp
  obtain ⟨s2, hs2, hu2⟩ := strConcat_unpack_eval M c
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp) Sc s1 hc hs1
  obtain ⟨s3, hs3, hu3⟩ := strConcat_unpack_eval M t
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)) St s2 ht hs2
  have hfalse : __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) = SmtValue.Boolean false := by
    rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false from rfl]
    simp only [__smtx_model_eval]
  rw [strContains_eval_eq M _ d s3 Sd hs3 hd]
  rw [model_eval_or_eq, model_eval_or_eq,
    strContains_eval_eq M t d St Sd ht hd, strContains_eval_eq M sw d Ss Sd hsw hd, hfalse]
  simp only [__smtx_model_eval_or]
  have hcs : native_unpack_seq s3 =
      native_unpack_seq St ++ native_unpack_seq Sc ++ native_unpack_seq Ss := by
    rw [hu3, hu2, hu1, hempnil]; simp [List.append_assoc]
  rw [hcs]
  have hsplit := native_seq_contains_split_iff_of_no_overlap
    (native_unpack_seq St) (native_unpack_seq Sc) (native_unpack_seq Ss) (native_unpack_seq Sd) hA hB
  congr 1
  rw [show native_or (native_seq_contains (native_unpack_seq St) (native_unpack_seq Sd))
        (native_or (native_seq_contains (native_unpack_seq Ss) (native_unpack_seq Sd)) false) =
      (native_seq_contains (native_unpack_seq St) (native_unpack_seq Sd) ||
        native_seq_contains (native_unpack_seq Ss) (native_unpack_seq Sd)) from by simp [native_or]]
  rw [Bool.eq_iff_iff, Bool.or_eq_true]
  exact hsplit

/-! ### Endpoint overlap lemmas for `contains` -/

theorem native_seq_compat_of_compat_append_right
    (A D R : List SmtValue)
    (h : native_seq_compat A (D ++ R)) :
    native_seq_compat A D := by
  unfold native_seq_compat at h ⊢
  rcases h with h | h
  · rw [native_seq_prefix_eq_iff] at h
    rcases h with ⟨r, hEq⟩
    exact native_seq_compat_of_append_eq A r D R hEq.symm
  · right
    rw [native_seq_prefix_eq_iff] at h ⊢
    rcases h with ⟨r, hEq⟩
    refine ⟨R ++ r, ?_⟩
    rw [hEq]
    simp [List.append_assoc]

theorem native_seq_contains_drop_left_of_no_endpoint_overlap
    (C S D R : List SmtValue)
    (hNo : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D)
    (h : native_seq_contains (C ++ S) (D ++ R) = true) :
    native_seq_contains S (D ++ R) = true := by
  rcases native_seq_contains_decomp_exists (C ++ S) (D ++ R) h with
    ⟨before, after, hEq⟩
  by_cases hStart : before.length < C.length
  · exfalso
    have hdropOcc :
        (before ++ (D ++ R) ++ after).drop before.length =
          (D ++ R) ++ after := by
      rw [List.append_assoc]
      exact List.drop_left
    have hdropCS :
        (C ++ S).drop before.length = C.drop before.length ++ S := by
      exact List.drop_append_of_le_length (Nat.le_of_lt hStart)
    have hAppend : C.drop before.length ++ S = (D ++ R) ++ after := by
      rw [← hdropCS, hEq, hdropOcc]
    have hCompatWhole :
        native_seq_compat (C.drop before.length) (D ++ R) :=
      native_seq_compat_of_append_eq (C.drop before.length) S (D ++ R) after
        hAppend
    have hCompatD : native_seq_compat (C.drop before.length) D :=
      native_seq_compat_of_compat_append_right (C.drop before.length) D R
        hCompatWhole
    exact hNo before.length hStart hCompatD
  · have hWithinS : C.length ≤ before.length := Nat.le_of_not_gt hStart
    have hwin :=
      native_seq_contains_drop_of_decomp before (D ++ R) after C.length hWithinS
    have hdrop : (before ++ (D ++ R) ++ after).drop C.length = S := by
      rw [← hEq]
      exact List.drop_left
    rw [hdrop] at hwin
    exact hwin

theorem native_seq_contains_reverse_iff
    (xs pat : List SmtValue) :
    native_seq_contains xs.reverse pat.reverse = true ↔
      native_seq_contains xs pat = true := by
  constructor
  · intro h
    rcases native_seq_contains_decomp_exists xs.reverse pat.reverse h with
      ⟨before, after, hEq⟩
    have hx : xs = after.reverse ++ pat ++ before.reverse := by
      calc
        xs = xs.reverse.reverse := by simp
        _ = (before ++ pat.reverse ++ after).reverse := by rw [hEq]
        _ = after.reverse ++ pat ++ before.reverse := by simp [List.append_assoc]
    rw [hx]
    exact native_seq_contains_of_decomp after.reverse pat before.reverse
  · intro h
    rcases native_seq_contains_decomp_exists xs pat h with
      ⟨before, after, hEq⟩
    have hx : xs.reverse = after.reverse ++ pat.reverse ++ before.reverse := by
      calc
        xs.reverse = (before ++ pat ++ after).reverse := by rw [hEq]
        _ = after.reverse ++ pat.reverse ++ before.reverse := by
          simp [List.append_assoc]
    rw [hx]
    exact native_seq_contains_of_decomp after.reverse pat.reverse before.reverse

theorem native_seq_contains_drop_right_of_no_endpoint_overlap
    (S C L D : List SmtValue)
    (hNo : ∀ k, k < C.reverse.length →
      ¬ native_seq_compat (C.reverse.drop k) D.reverse)
    (h : native_seq_contains (S ++ C) (L ++ D) = true) :
    native_seq_contains S (L ++ D) = true := by
  have hRev0 :
      native_seq_contains (S ++ C).reverse (L ++ D).reverse = true :=
    (native_seq_contains_reverse_iff (S ++ C) (L ++ D)).2 h
  have hRev :
      native_seq_contains (C.reverse ++ S.reverse) (D.reverse ++ L.reverse) =
        true := by
    simpa [List.reverse_append, List.append_assoc] using hRev0
  have hLeft :=
    native_seq_contains_drop_left_of_no_endpoint_overlap
      C.reverse S.reverse D.reverse L.reverse hNo hRev
  have hBack :
      native_seq_contains S.reverse (L ++ D).reverse = true := by
    simpa [List.reverse_append] using hLeft
  exact (native_seq_contains_reverse_iff S (L ++ D)).1 hBack

theorem native_seq_contains_endpoints_iff_of_no_overlap
    (C1 S C2 D1 T D2 : List SmtValue)
    (hLeft : ∀ k, k < C1.length →
      ¬ native_seq_compat (C1.drop k) D1)
    (hRight : ∀ k, k < C2.reverse.length →
      ¬ native_seq_compat (C2.reverse.drop k) D2.reverse) :
    native_seq_contains (C1 ++ S ++ C2) (D1 ++ T ++ D2) = true ↔
      native_seq_contains S (D1 ++ T ++ D2) = true := by
  constructor
  · intro h
    have hLeftTrim :
        native_seq_contains (S ++ C2) (D1 ++ (T ++ D2)) = true := by
      have h' :
          native_seq_contains (C1 ++ (S ++ C2)) (D1 ++ (T ++ D2)) = true := by
        simpa [List.append_assoc] using h
      exact native_seq_contains_drop_left_of_no_endpoint_overlap
        C1 (S ++ C2) D1 (T ++ D2) hLeft h'
    have hLeftTrim' :
        native_seq_contains (S ++ C2) ((D1 ++ T) ++ D2) = true := by
      simpa [List.append_assoc] using hLeftTrim
    exact native_seq_contains_drop_right_of_no_endpoint_overlap
      S C2 (D1 ++ T) D2 hRight hLeftTrim'
  · intro h
    have hRightAppend :
        native_seq_contains (S ++ C2) (D1 ++ T ++ D2) = true :=
      native_seq_contains_append_right S C2 (D1 ++ T ++ D2) h
    have hLeftAppend :
        native_seq_contains (C1 ++ (S ++ C2)) (D1 ++ T ++ D2) = true :=
      native_seq_contains_append_left C1 (S ++ C2) (D1 ++ T ++ D2)
        hRightAppend
    simpa [List.append_assoc] using hLeftAppend

/-- The endpoint-overlap `contains` rule at the model-evaluation level. -/
theorem overlap_endpoints_contains_eval (M : SmtModel)
    (c1 sw c2 emp d1 t d2 : Term)
    (Sc1 Ss Sc2 Se Sd1 St Sd2 : SmtSeq)
    (hc1 : __smtx_model_eval M (__eo_to_smt c1) = SmtValue.Seq Sc1)
    (hsw : __smtx_model_eval M (__eo_to_smt sw) = SmtValue.Seq Ss)
    (hc2 : __smtx_model_eval M (__eo_to_smt c2) = SmtValue.Seq Sc2)
    (hemp : __smtx_model_eval M (__eo_to_smt emp) = SmtValue.Seq Se)
    (hd1 : __smtx_model_eval M (__eo_to_smt d1) = SmtValue.Seq Sd1)
    (ht : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq St)
    (hd2 : __smtx_model_eval M (__eo_to_smt d2) = SmtValue.Seq Sd2)
    (hempnil : native_unpack_seq Se = [])
    (hLeft : ∀ k, k < (native_unpack_seq Sc1).length →
      ¬ native_seq_compat ((native_unpack_seq Sc1).drop k)
        (native_unpack_seq Sd1))
    (hRight : ∀ k, k < (native_unpack_seq Sc2).reverse.length →
      ¬ native_seq_compat ((native_unpack_seq Sc2).reverse.drop k)
        (native_unpack_seq Sd2).reverse) :
    __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) =
      __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) sw)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) := by
  obtain ⟨sD2E, hsD2E, huD2E⟩ :=
    strConcat_unpack_eval M d2 emp Sd2 Se hd2 hemp
  obtain ⟨sTD2E, hsTD2E, huTD2E⟩ :=
    strConcat_unpack_eval M t
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)
      St sD2E ht hsD2E
  obtain ⟨sNeedle, hsNeedle, huNeedle⟩ :=
    strConcat_unpack_eval M d1
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))
      Sd1 sTD2E hd1 hsTD2E
  obtain ⟨sC2E, hsC2E, huC2E⟩ :=
    strConcat_unpack_eval M c2 emp Sc2 Se hc2 hemp
  obtain ⟨sSC2E, hsSC2E, huSC2E⟩ :=
    strConcat_unpack_eval M sw
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp)
      Ss sC2E hsw hsC2E
  obtain ⟨sHay, hsHay, huHay⟩ :=
    strConcat_unpack_eval M c1
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))
      Sc1 sSC2E hc1 hsSC2E
  rw [strContains_eval_eq M _ _ sHay sNeedle hsHay hsNeedle]
  rw [strContains_eval_eq M sw _ Ss sNeedle hsw hsNeedle]
  have hHay :
      native_unpack_seq sHay =
        native_unpack_seq Sc1 ++ native_unpack_seq Ss ++ native_unpack_seq Sc2 := by
    rw [huHay, huSC2E, huC2E, hempnil]
    simp [List.append_assoc]
  have hNeedle :
      native_unpack_seq sNeedle =
        native_unpack_seq Sd1 ++ native_unpack_seq St ++ native_unpack_seq Sd2 := by
    rw [huNeedle, huTD2E, huD2E, hempnil]
    simp [List.append_assoc]
  rw [hHay, hNeedle]
  congr 1
  rw [Bool.eq_iff_iff]
  exact native_seq_contains_endpoints_iff_of_no_overlap
    (native_unpack_seq Sc1) (native_unpack_seq Ss) (native_unpack_seq Sc2)
    (native_unpack_seq Sd1) (native_unpack_seq St) (native_unpack_seq Sd2)
    hLeft hRight

theorem eo_add_one_inv (R : Term) (N : Int)
    (h : __eo_add (Term.Numeral 1) R = Term.Numeral N) :
    R = Term.Numeral (N - 1) := by
  cases R with
  | Numeral m =>
      simp only [__eo_add, native_zplus] at h; injection h with h
      congr 1; rw [← h, Int.add_comm, Int.add_sub_cancel]
  | _ => simp_all [__eo_add]

/-- If the overlap recursion runs to "full" on an atom chain, then every suffix of
the chain is incompatible with `W`. -/
theorem overlap_full_is_compat_false (ex W : Term) (hW : W ≠ Term.Stuck) :
    ∀ (xs : List Term),
      __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral (Int.ofNat xs.length) →
      ∀ k, k < xs.length →
        __str_is_compatible (atomChainTerm (xs.drop k) ex) W = Term.Boolean false := by
  intro xs
  induction xs with
  | nil => intro _ k hk; simp at hk
  | cons a xs ih =>
      intro hov k hk
      rw [atomChainTerm_cons, overlap_rec_concat _ _ _ hW, ← atomChainTerm_cons] at hov
      have hcompat : __str_is_compatible (atomChainTerm (a :: xs) ex) W = Term.Boolean false := by
        clear hk ih
        cases hc : __str_is_compatible (atomChainTerm (a :: xs) ex) W with
        | Boolean b =>
            cases b with
            | true =>
                exfalso; rw [hc, eo_ite_true] at hov; injection hov with hov
                rw [show (a :: xs).length = xs.length + 1 from rfl] at hov
                simp only [native_Int, Int.ofNat_eq_natCast] at hov; omega
            | false => rfl
        | _ => rw [hc] at hov; simp [__eo_ite, native_teq, SmtEval.native_ite] at hov
      have hrec : __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral (Int.ofNat xs.length) := by
        clear hk ih
        rw [hcompat, eo_ite_false] at hov
        rw [eo_add_one_inv _ _ hov]; congr 1
        rw [show (a :: xs).length = xs.length + 1 from rfl]
        simp only [native_Int, Int.ofNat_eq_natCast]; omega
      cases k with
      | zero => simpa using hcompat
      | succ j =>
          have hj : j < xs.length := by simp only [List.length_cons] at hk; omega
          simpa [List.drop_succ_cons] using ih hrec j hj

theorem nveq_self (v : SmtValue) : native_veq v v = true := by simp [native_veq]

theorem nveq_symm {v1 v2 : SmtValue} (h : native_veq v1 v2 = false) :
    native_veq v2 v1 = false := by
  simp only [native_veq, decide_eq_false_iff_not] at h ⊢; exact fun he => h he.symm

/-- The key inversion: when `is_compatible` of two atom-chains is *Boolean false*
(so the comparison never got `Stuck`), the underlying value lists are not
overlap-compatible.  The distinctness facts are extracted *locally* from each
head comparison (via `are_distinct` soundness, supplied as `hsound`), so no
global distinctness guard is needed. -/
theorem is_compat_false_no_compat
    (val : Term → SmtValue) (exX exY : Term)
    (hExYne : exY ≠ Term.Stuck)
    (hExX : ∀ ys', __str_is_compatible exX (atomChainTerm ys' exY) = Term.Boolean true)
    (hExY : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) exY = Term.Boolean true) :
    ∀ (xs ys : List Term),
      (∀ a ∈ xs, ∀ b ∈ ys, __eo_eq a b = Term.Boolean false →
        __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
        native_veq (val a) (val b) = false) →
      __str_is_compatible (atomChainTerm xs exX) (atomChainTerm ys exY) = Term.Boolean false →
      ¬ native_seq_compat (xs.map val) (ys.map val) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ hfalse
      rw [show atomChainTerm [] exX = exX from rfl, hExX ys] at hfalse
      simp at hfalse
  | cons a xs ih =>
      intro ys hsound hfalse
      cases ys with
      | nil =>
          rw [atomChainTerm_cons, show atomChainTerm [] exY = exY from rfl, hExY] at hfalse
          simp at hfalse
      | cons b ys =>
          rw [atomChainTerm_cons, atomChainTerm_cons] at hfalse
          simp only [__str_is_compatible] at hfalse
          by_cases hab : __eo_eq a b = Term.Boolean true
          · have hba : b = a := eq_of_eo_eq a b hab
            subst hba
            rw [hab, eo_ite_true] at hfalse
            have ihres := ih ys (fun a' ha' b' hb' heq' hd' => hsound a' (List.mem_cons_of_mem _ ha')
              b' (List.mem_cons_of_mem _ hb') heq' hd') hfalse
            intro hcompat; apply ihres
            unfold native_seq_compat at hcompat ⊢
            simp only [List.map_cons, native_seq_prefix_eq, nveq_self, Bool.true_and] at hcompat
            exact hcompat
          · have habf : __eo_eq a b = Term.Boolean false := by
              cases h : __eo_eq a b with
              | Boolean bb => cases bb with
                | true => exact absurd h hab
                | false => rfl
              | _ => rw [h] at hfalse; simp [__eo_ite, native_teq, SmtEval.native_ite] at hfalse
            rw [habf] at hfalse
            simp only [__eo_ite, native_teq, SmtEval.native_ite,
              __eo_l_1___str_is_compatible, __eo_requires, habf] at hfalse
            have hdist : __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true := by
              revert hfalse
              cases h : __are_distinct_terms_type a b (__eo_typeof a) with
              | Boolean bb => cases bb with
                | true => intro _; rfl
                | false => intro hf; simp at hf
              | _ => intro hf; simp at hf
            have hvf := hsound a (by simp) b (by simp) habf hdist
            have hvf2 := nveq_symm hvf
            intro hcompat
            unfold native_seq_compat at hcompat
            simp only [List.map_cons, native_seq_prefix_eq, hvf, hvf2,
              Bool.false_and] at hcompat
            rcases hcompat with h | h <;> exact Bool.noConfusion h

/-- The overlap-recursion count is bounded by the number of atoms. -/
theorem overlap_rec_le_len (ex W : Term) (hW : W ≠ Term.Stuck)
    (hexz : __str_overlap_rec ex W = Term.Numeral 0) :
    ∀ (xs : List Term) (m : Int),
      __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral m → m ≤ Int.ofNat xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro m h
      rw [show atomChainTerm [] ex = ex from rfl, hexz] at h
      injection h with h; simp only [native_Int, List.length_nil, Int.ofNat_eq_natCast] at h ⊢; omega
  | cons a xs ih =>
      intro m h
      rw [atomChainTerm_cons, overlap_rec_concat _ _ _ hW, ← atomChainTerm_cons] at h
      cases hc : __str_is_compatible (atomChainTerm (a :: xs) ex) W with
      | Boolean bb =>
          cases bb with
          | true =>
              rw [hc, eo_ite_true] at h; injection h with h
              simp only [native_Int] at h ⊢
              rw [show (a :: xs).length = xs.length + 1 from rfl]
              simp only [Int.ofNat_eq_natCast]; omega
          | false =>
              rw [hc, eo_ite_false] at h
              have key : __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral (m - 1) :=
                eo_add_one_inv _ _ h
              have ihres := ih (m - 1) key
              rw [show (a :: xs).length = xs.length + 1 from rfl]
              simp only [Int.ofNat_eq_natCast] at ihres ⊢; omega
      | _ => rw [hc] at h; simp [__eo_ite, native_teq, SmtEval.native_ite] at h

/-- Unified no-overlap `(A)` derivation from a word characterization of `c`/`d`.
Given that `c`/`d` flatten to atom-chains with terminators `exX`/`exY`, whose
evaluated element lists are `xs.map val`/`ys.map val`, the `gt` side-condition
forces every nonempty suffix of `c`'s value to be incompatible with `d`'s. -/
theorem no_compat_of_word
    (val : Term → SmtValue) (c d : Term) (Sc Sd : SmtSeq)
    (xs ys : List Term) (exX exY : Term)
    (hflatc : __str_flatten (__str_nary_intro c) = atomChainTerm xs exX)
    (hflatd : __str_flatten (__str_nary_intro d) = atomChainTerm ys exY)
    (hlenc : __str_value_len c = Term.Numeral (Int.ofNat xs.length))
    (hunpc : native_unpack_seq Sc = xs.map val)
    (hunpd : native_unpack_seq Sd = ys.map val)
    (hexXne : exX ≠ Term.Stuck) (hexYne : exY ≠ Term.Stuck)
    (hexXcompatL : ∀ ys', __str_is_compatible exX (atomChainTerm ys' exY) = Term.Boolean true)
    (hexYcompatR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) exY = Term.Boolean true)
    (hexXz : ∀ W, W ≠ Term.Stuck → __str_overlap_rec exX W = Term.Numeral 0)
    (hsound : ∀ a ∈ xs, ∀ b ∈ ys, __eo_eq a b = Term.Boolean false →
      __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
      native_veq (val a) (val b) = false)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
          (__str_flatten (__str_nary_intro d))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
  rw [hlenc, hflatc, hflatd] at hgt
  have hWne : atomChainTerm ys exY ≠ Term.Stuck := atomChainTerm_ne_stuck ys exY hexYne
  have hrec : ∃ N2, __str_overlap_rec (atomChainTerm xs exX) (atomChainTerm ys exY)
      = Term.Numeral N2 ∧ Int.ofNat xs.length ≤ N2 := by
    revert hgt
    cases hb : __str_overlap_rec (atomChainTerm xs exX) (atomChainTerm ys exY) with
    | Numeral N2 =>
        intro hgt; refine ⟨N2, rfl, ?_⟩
        simp only [__eo_gt, native_zlt] at hgt; injection hgt with hgt
        have hnlt := of_decide_eq_false hgt
        simp only [native_Int, Int.ofNat_eq_natCast] at hnlt ⊢; omega
    | _ => intro hgt; simp [__eo_gt] at hgt
  obtain ⟨N2, hN2eq, hN2ge⟩ := hrec
  have hN2le := overlap_rec_le_len exX (atomChainTerm ys exY) hWne
    (hexXz _ hWne) xs N2 hN2eq
  have hN2 : N2 = Int.ofNat xs.length := by
    simp only [native_Int, Int.ofNat_eq_natCast] at hN2le hN2ge ⊢; omega
  rw [hN2] at hN2eq
  have hfull := overlap_full_is_compat_false exX (atomChainTerm ys exY) hWne xs hN2eq
  intro k hk
  rw [hunpc, List.length_map] at hk
  rw [hunpc, hunpd, ← List.map_drop]
  exact is_compat_false_no_compat val exX exY hexYne hexXcompatL hexYcompatR
    (xs.drop k) ys
    (fun a' ha' b' hb' heq' hd' => hsound a' (List.mem_of_mem_drop ha') b' hb' heq' hd')
    (hfull k hk)

theorem no_compat_of_word_values
    (val : Term → SmtValue) (lenTerm X Y : Term)
    (Cvals Dvals : List SmtValue)
    (xs ys : List Term) (exX exY : Term)
    (hX : X = atomChainTerm xs exX)
    (hY : Y = atomChainTerm ys exY)
    (hlen : lenTerm = Term.Numeral (Int.ofNat xs.length))
    (hunpc : Cvals = xs.map val)
    (hunpd : Dvals = ys.map val)
    (hexXne : exX ≠ Term.Stuck) (hexYne : exY ≠ Term.Stuck)
    (hexXcompatL : ∀ ys', __str_is_compatible exX (atomChainTerm ys' exY) = Term.Boolean true)
    (hexYcompatR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) exY = Term.Boolean true)
    (hexXz : ∀ W, W ≠ Term.Stuck → __str_overlap_rec exX W = Term.Numeral 0)
    (hsound : ∀ a ∈ xs, ∀ b ∈ ys, __eo_eq a b = Term.Boolean false →
      __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
      native_veq (val a) (val b) = false)
    (hgt : __eo_gt lenTerm (__str_overlap_rec X Y) = Term.Boolean false) :
    ∀ k, k < Cvals.length →
      ¬ native_seq_compat (Cvals.drop k) Dvals := by
  rw [hlen, hX, hY] at hgt
  have hWne : atomChainTerm ys exY ≠ Term.Stuck := atomChainTerm_ne_stuck ys exY hexYne
  have hrec : ∃ N2, __str_overlap_rec (atomChainTerm xs exX) (atomChainTerm ys exY)
      = Term.Numeral N2 ∧ Int.ofNat xs.length ≤ N2 := by
    revert hgt
    cases hb : __str_overlap_rec (atomChainTerm xs exX) (atomChainTerm ys exY) with
    | Numeral N2 =>
        intro hgt; refine ⟨N2, rfl, ?_⟩
        simp only [__eo_gt, native_zlt] at hgt; injection hgt with hgt
        have hnlt := of_decide_eq_false hgt
        simp only [native_Int, Int.ofNat_eq_natCast] at hnlt ⊢; omega
    | _ => intro hgt; simp [__eo_gt] at hgt
  obtain ⟨N2, hN2eq, hN2ge⟩ := hrec
  have hN2le := overlap_rec_le_len exX (atomChainTerm ys exY) hWne
    (hexXz _ hWne) xs N2 hN2eq
  have hN2 : N2 = Int.ofNat xs.length := by
    simp only [native_Int, Int.ofNat_eq_natCast] at hN2le hN2ge ⊢; omega
  rw [hN2] at hN2eq
  have hfull := overlap_full_is_compat_false exX (atomChainTerm ys exY) hWne xs hN2eq
  intro k hk
  rw [hunpc, List.length_map] at hk
  rw [hunpc, hunpd, ← List.map_drop]
  exact is_compat_false_no_compat val exX exY hexYne hexXcompatL hexYcompatR
    (xs.drop k) ys
    (fun a' ha' b' hb' heq' hd' => hsound a' (List.mem_of_mem_drop ha') b' hb' heq' hd')
    (hfull k hk)

/-! ### seq_unit word building blocks (towards the seq_unit case of `no_compat_dispatch`) -/

/-- `concat` evaluation appends the two element lists. -/
theorem concat_unpack (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    ∃ sxy, __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) = SmtValue.Seq sxy ∧
      native_unpack_seq sxy = native_unpack_seq sx ++ native_unpack_seq sy := by
  rw [smtx_model_eval_str_concat_term_eq, hx, hy]
  simp only [__smtx_model_eval_str_concat]
  exact ⟨_, rfl, by rw [Smtm.native_unpack_pack_seq]; rfl⟩

/-- Top-down chain unpack: from the chain evaluating to a `Seq`, its element list is
`xs.map val`, given each atom's element value and an empty-like terminator. -/
theorem chain_unpack_td (M : SmtModel) (val : Term → SmtValue) (ex : Term)
    (htermempty : __str_is_empty ex = Term.Boolean true) :
    ∀ (xs : List Term) (sc : SmtSeq),
      __smtx_model_eval M (__eo_to_smt (atomChainTerm xs ex)) = SmtValue.Seq sc →
      (∀ a ∈ xs, ∀ sa, __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa →
        native_unpack_seq sa = [val a]) →
      native_unpack_seq sc = xs.map val := by
  intro xs
  induction xs with
  | nil =>
      intro sc hc _
      rw [show atomChainTerm [] ex = ex from rfl] at hc
      simpa using str_is_empty_eval_unpack_nil M ex sc htermempty hc
  | cons a xs ih =>
      intro sc hc hatoms
      rw [atomChainTerm_cons] at hc
      obtain ⟨⟨sa, hsa⟩, ⟨sc', hsc'⟩⟩ := strConcat_args_eval_seq_of_concat_eval_seq M a
        (atomChainTerm xs ex) ⟨sc, hc⟩
      obtain ⟨sxy, hsxy, hsxynil⟩ := concat_unpack M a (atomChainTerm xs ex) sa sc' hsa hsc'
      have heq : sc = sxy := by rw [hc] at hsxy; injection hsxy
      rw [heq, hsxynil, hatoms a (by simp) sa hsa, ih sc' hsc' (fun a' h' => hatoms a' (by simp [h']))]
      simp

/-- The element value of a `seq_unit` atom. -/
noncomputable def seqElemVal (M : SmtModel) (a : Term) : SmtValue :=
  match a with
  | Term.Apply (Term.UOp UserOp.seq_unit) e => __smtx_model_eval M (__eo_to_smt e)
  | Term.String [ch] => SmtValue.Char ch
  | _ => SmtValue.NotValue

theorem charAtoms_unpack (M : SmtModel) (w : native_String) :
    w.map SmtValue.Char =
      (w.map (fun ch => Term.String [ch])).map (seqElemVal M) := by
  induction w with
  | nil => rfl
  | cons ch rest ih =>
      simp [seqElemVal, ih]

theorem eval_seqUnitAtom (M : SmtModel) (e : Term) :
    ∃ sa, __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) = SmtValue.Seq sa ∧
      native_unpack_seq sa = [seqElemVal M (Term.Apply (Term.UOp UserOp.seq_unit) e)] := by
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e) = SmtTerm.seq_unit (__eo_to_smt e) from rfl]
  rw [show __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
      SmtValue.Seq (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
        (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e))))) from by
        simp only [__smtx_model_eval]]
  exact ⟨_, rfl, by simp [native_unpack_seq, seqElemVal]⟩

theorem eval_charAtom (M : SmtModel) (ch : native_Char) :
    ∃ sa, __smtx_model_eval M (__eo_to_smt (Term.String [ch])) = SmtValue.Seq sa ∧
      native_unpack_seq sa = [seqElemVal M (Term.String [ch])] := by
  rw [show __eo_to_smt (Term.String [ch]) = SmtTerm.String [ch] from rfl]
  simp only [__smtx_model_eval]
  exact ⟨native_pack_string [ch], rfl, by simp [seqElemVal, native_pack_string,
    native_pack_seq, native_unpack_seq]⟩

theorem char_valid_of_charAtom_seq_type (ch : native_Char) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String [ch])) = SmtType.Seq T) :
    native_char_valid ch = true := by
  rw [show __eo_to_smt (Term.String [ch]) = SmtTerm.String [ch] from rfl] at hTy
  rw [__smtx_typeof.eq_4] at hTy
  cases hvalid : native_char_valid ch
  · simp [native_string_valid, hvalid, native_ite] at hTy
  · rfl

theorem atom_eval_eq_of_seqElemVal_veq_true (M : SmtModel) (T : SmtType)
    (a b : Term)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (haShape : (∃ ch, a = Term.String [ch]) ∨
      (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e))
    (hbShape : (∃ ch, b = Term.String [ch]) ∨
      (∃ e, b = Term.Apply (Term.UOp UserOp.seq_unit) e))
    (hveq : native_veq (seqElemVal M a) (seqElemVal M b) = true) :
    __smtx_model_eval M (__eo_to_smt a) =
      __smtx_model_eval M (__eo_to_smt b) := by
  rcases haShape with ⟨cha, rfl⟩ | ⟨ea, rfl⟩
  · rcases hbShape with ⟨chb, rfl⟩ | ⟨eb, rfl⟩
    · have hval : SmtValue.Char cha = SmtValue.Char chb := by
        simpa [native_veq, seqElemVal] using hveq
      injection hval with hch
      subst hch
      rfl
    · have hvalid : native_char_valid cha = true :=
        char_valid_of_charAtom_seq_type cha T haTy
      have hval : SmtValue.Char cha = __smtx_model_eval M (__eo_to_smt eb) := by
        have hsimpa := hveq
        try simp [native_veq, seqElemVal] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      rw [show __eo_to_smt (Term.String [cha]) = SmtTerm.String [cha] from rfl,
        show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) eb) =
          SmtTerm.seq_unit (__eo_to_smt eb) from rfl]
      simp only [__smtx_model_eval]
      rw [← hval]
      simp [native_pack_string, native_pack_seq, __smtx_typeof_value, hvalid, native_ite]
  · rcases hbShape with ⟨chb, rfl⟩ | ⟨eb, rfl⟩
    · have hvalid : native_char_valid chb = true :=
        char_valid_of_charAtom_seq_type chb T hbTy
      have hval : __smtx_model_eval M (__eo_to_smt ea) = SmtValue.Char chb := by
        have hsimpa := hveq
        try simp [native_veq, seqElemVal] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) ea) =
          SmtTerm.seq_unit (__eo_to_smt ea) from rfl,
        show __eo_to_smt (Term.String [chb]) = SmtTerm.String [chb] from rfl]
      simp only [__smtx_model_eval]
      rw [hval]
      simp [native_pack_string, native_pack_seq, __smtx_typeof_value, hvalid, native_ite]
    · have hval : __smtx_model_eval M (__eo_to_smt ea) =
          __smtx_model_eval M (__eo_to_smt eb) := by
        have hsimpa := hveq
        try simp [native_veq, seqElemVal] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) ea) =
          SmtTerm.seq_unit (__eo_to_smt ea) from rfl,
        show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) eb) =
          SmtTerm.seq_unit (__eo_to_smt eb) from rfl]
      simp only [__smtx_model_eval]
      rw [hval]

theorem shaped_atoms_sound (M : SmtModel) (hM : model_wf M) (T : SmtType)
    (xs ys : List Term)
    (hxTy : ∀ a ∈ xs, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hyTy : ∀ b ∈ ys, __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (hxShape : ∀ a ∈ xs, (∃ ch, a = Term.String [ch]) ∨
      (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e))
    (hyShape : ∀ b ∈ ys, (∃ ch, b = Term.String [ch]) ∨
      (∃ e, b = Term.Apply (Term.UOp UserOp.seq_unit) e)) :
    ∀ a ∈ xs, ∀ b ∈ ys, __eo_eq a b = Term.Boolean false →
      __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
      native_veq (seqElemVal M a) (seqElemVal M b) = false := by
  intro a ha b hb heq hdist
  have haTrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxTy a ha]
    exact seq_ne_none T
  have hbTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hyTy b hb]
    exact seq_ne_none T
  have hSeqFalse :=
    are_distinct_terms_type_model_eval_eq_false M hM a b haTrans hbTrans heq hdist
  by_cases hv : native_veq (seqElemVal M a) (seqElemVal M b) = false
  · exact hv
  · have hvtrue : native_veq (seqElemVal M a) (seqElemVal M b) = true := by
      cases h : native_veq (seqElemVal M a) (seqElemVal M b) <;> simp [h] at hv ⊢
    have hEvalEq := atom_eval_eq_of_seqElemVal_veq_true M T a b
      (hxTy a ha) (hyTy b hb) (hxShape a ha) (hyShape b hb) hvtrue
    exfalso
    rw [hEvalEq, smtx_model_eval_eq_refl] at hSeqFalse
    cases hSeqFalse

structure FlatWordView (M : SmtModel) (t : Term) (S : SmtSeq) (T : SmtType) where
  atoms : List Term
  ex : Term
  hflat : __str_flatten t = atomChainTerm atoms ex
  hlen : __str_value_len t = Term.Numeral (Int.ofNat atoms.length)
  hunp : native_unpack_seq S = atoms.map (seqElemVal M)
  hexEmpty : __str_is_empty ex = Term.Boolean true
  hAtomTy : ∀ a ∈ atoms, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T
  hAtomShape : ∀ a ∈ atoms, (∃ ch, a = Term.String [ch]) ∨
    (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)

structure IntroWordView (M : SmtModel) (t : Term) (S : SmtSeq) (T : SmtType) where
  atoms : List Term
  ex : Term
  hflat : __str_flatten (__str_nary_intro t) = atomChainTerm atoms ex
  hlen : __str_value_len t = Term.Numeral (Int.ofNat atoms.length)
  hunp : native_unpack_seq S = atoms.map (seqElemVal M)
  hexEmpty : __str_is_empty ex = Term.Boolean true
  hAtomTy : ∀ a ∈ atoms, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T
  hAtomShape : ∀ a ∈ atoms, (∃ ch, a = Term.String [ch]) ∨
    (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)

theorem str_flatten_string_nil_of_ne_stuck (w : native_String)
    (h : __str_flatten (Term.String w) ≠ Term.Stuck) : w = [] := by
  cases w with
  | nil => rfl
  | cons ch rest =>
      exfalso
      apply h
      simp [__str_flatten, __eo_requires, __seq_empty,
        native_teq, native_ite]
      intro hEq
      cases hEq

theorem charAtoms_type (w : native_String) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String w)) = SmtType.Seq T) :
    ∀ a ∈ w.map (fun ch => Term.String [ch]),
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
  have hT : T = SmtType.Char := by
    rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl] at hTy
    rw [__smtx_typeof.eq_4] at hTy
    cases hvalid : native_string_valid w
    · simp [hvalid, native_ite] at hTy
    · simp [hvalid, native_ite] at hTy
      exact hTy.symm
  intro a ha
  rw [hT]
  rcases List.mem_map.1 ha with ⟨ch, _hch, rfl⟩
  rw [show __eo_to_smt (Term.String [ch]) = SmtTerm.String [ch] from rfl]
  rw [__smtx_typeof.eq_4]
  have hvalid : native_char_valid ch = true := by
    have hwvalid : native_string_valid w = true := by
      rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl] at hTy
      rw [__smtx_typeof.eq_4] at hTy
      cases hv : native_string_valid w
      · simp [hv, native_ite] at hTy
      · rfl
    unfold native_string_valid at hwvalid
    exact List.all_eq_true.1 hwvalid ch _hch
  simp [native_string_valid, hvalid, native_ite]

theorem charAtoms_shape (w : native_String) :
    ∀ a ∈ w.map (fun ch => Term.String [ch]),
      (∃ ch, a = Term.String [ch]) ∨
        (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e) := by
  intro a ha
  rcases List.mem_map.1 ha with ⟨ch, _hch, rfl⟩
  exact Or.inl ⟨ch, rfl⟩

def introWordView_string (M : SmtModel) (w : native_String) (S : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String w)) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt (Term.String w)) = SmtValue.Seq S) :
    IntroWordView M (Term.String w) S T := by
  refine {
    atoms := w.map (fun ch => Term.String [ch]),
    ex := Term.String [],
    hflat := ?_,
    hlen := ?_,
    hunp := ?_,
    hexEmpty := by simp [__str_is_empty],
    hAtomTy := charAtoms_type w T hTy,
    hAtomShape := charAtoms_shape w
  }
  · rw [flatten_nary_intro_string, ← atomChainTerm_charAtoms]
  · rw [str_value_len_string]
    simp
  · rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl] at hEval
    simp only [__smtx_model_eval] at hEval
    injection hEval with hS
    rw [← hS, unpack_pack_string_map, charAtoms_unpack]

theorem seqUnit_atoms_sound (M : SmtModel) (hM : model_wf M) (T : SmtType)
    (xs ys : List Term)
    (hxUnit : ∀ a ∈ xs, ∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)
    (hyUnit : ∀ b ∈ ys, ∃ e, b = Term.Apply (Term.UOp UserOp.seq_unit) e)
    (hxTy : ∀ a ∈ xs, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hyTy : ∀ b ∈ ys, __smtx_typeof (__eo_to_smt b) = SmtType.Seq T) :
    ∀ a ∈ xs, ∀ b ∈ ys, __eo_eq a b = Term.Boolean false →
      __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
      native_veq (seqElemVal M a) (seqElemVal M b) = false := by
  intro a ha b hb heq hdist
  obtain ⟨ea, rfl⟩ := hxUnit a ha
  obtain ⟨eb, rfl⟩ := hyUnit b hb
  have haTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) ea) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxTy (Term.Apply (Term.UOp UserOp.seq_unit) ea) ha]
    exact seq_ne_none T
  have hbTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) eb) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hyTy (Term.Apply (Term.UOp UserOp.seq_unit) eb) hb]
    exact seq_ne_none T
  have hSeqFalse :=
    are_distinct_terms_type_model_eval_eq_false M hM
      (Term.Apply (Term.UOp UserOp.seq_unit) ea)
      (Term.Apply (Term.UOp UserOp.seq_unit) eb)
      haTrans hbTrans heq hdist
  by_cases hv : native_veq (__smtx_model_eval M (__eo_to_smt ea))
      (__smtx_model_eval M (__eo_to_smt eb)) = false
  · simpa [seqElemVal] using hv
  · have hvtrue : native_veq (__smtx_model_eval M (__eo_to_smt ea))
        (__smtx_model_eval M (__eo_to_smt eb)) = true := by
      cases hveq : native_veq (__smtx_model_eval M (__eo_to_smt ea))
          (__smtx_model_eval M (__eo_to_smt eb)) <;> simp [hveq] at hv ⊢
    have hHeadEq :
        __smtx_model_eval M (__eo_to_smt ea) =
          __smtx_model_eval M (__eo_to_smt eb) := by
      simpa [native_veq] using hvtrue
    have hSeqEq :
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) ea)) =
          __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) eb)) := by
      rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) ea) =
          SmtTerm.seq_unit (__eo_to_smt ea) from rfl,
        show __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) eb) =
          SmtTerm.seq_unit (__eo_to_smt eb) from rfl]
      simp only [__smtx_model_eval]
      rw [hHeadEq]
    exfalso
    rw [hSeqEq, smtx_model_eval_eq_refl] at hSeqFalse
    cases hSeqFalse

theorem str_is_empty_seq_empty (T : Term) :
    __str_is_empty (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) = Term.Boolean true := by
  simp [__str_is_empty]

theorem seqEmpty_compatL_chain (T T' : Term) :
    ∀ ys', __str_is_compatible (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T))
      (atomChainTerm ys' (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T'))) = Term.Boolean true := by
  intro ys'
  cases ys' with
  | nil => simp [atomChainTerm, __str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty,
            __eo_or, SmtEval.native_or]
  | cons b ys'' =>
      rw [atomChainTerm_cons]
      simp [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty, __eo_or, SmtEval.native_or]

theorem seqEmpty_compatR (T a W : Term) :
    __str_is_compatible (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W)
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) = Term.Boolean true := by
  simp [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty, __eo_or, SmtEval.native_or]

theorem seqEmpty_overlap_zero (T W : Term) (hW : W ≠ Term.Stuck) :
    __str_overlap_rec (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) W
      = Term.Numeral 0 := by
  cases W with
  | Stuck => exact absurd rfl hW
  | _ => simp [__str_overlap_rec]

theorem strEmpty_compatL_chain (T' : Term) :
    ∀ ys', __str_is_compatible (Term.String [])
      (atomChainTerm ys' (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T'))) =
        Term.Boolean true := by
  intro ys'
  cases ys' with
  | nil => simp [atomChainTerm, __str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty,
            __eo_or, SmtEval.native_or]
  | cons b ys'' =>
      rw [atomChainTerm_cons]
      simp [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty, __eo_or,
        SmtEval.native_or]

theorem strEmpty_compatR (a W : Term) :
    __str_is_compatible (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W)
      (Term.String []) = Term.Boolean true := by
  simp [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty, __eo_or,
    SmtEval.native_or]

theorem strEmpty_overlap_zero (W : Term) (hW : W ≠ Term.Stuck) :
    __str_overlap_rec (Term.String []) W = Term.Numeral 0 := by
  cases W with
  | Stuck => exact absurd rfl hW
  | _ => simp [__str_overlap_rec]

theorem seqEmptyOfSeq_is_empty (U : Term) :
    __str_is_empty (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      Term.Boolean true := by
  by_cases hU : U = Term.UOp UserOp.Char
  · subst hU
    simp [__seq_empty, __str_is_empty]
  · simp [__seq_empty, hU, __str_is_empty]

theorem seqEmptyOfSeq_ne_stuck (U : Term) :
    __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) ≠ Term.Stuck := by
  by_cases hU : U = Term.UOp UserOp.Char
  · subst hU
    simp [__seq_empty]
  · simp [__seq_empty, hU]

theorem seqEmptyOfSeq_compatL_chain (U V : Term) :
    ∀ ys', __str_is_compatible (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))
      (atomChainTerm ys' (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) V))) =
        Term.Boolean true := by
  intro ys'
  by_cases hU : U = Term.UOp UserOp.Char
  · subst hU
    by_cases hV : V = Term.UOp UserOp.Char
    · subst hV
      cases ys' with
      | nil =>
          simp [atomChainTerm, __seq_empty, __str_is_compatible,
            __eo_l_1___str_is_compatible, __str_is_empty, __eo_or, SmtEval.native_or]
      | cons b ys'' =>
          rw [atomChainTerm_cons]
          simp [__seq_empty, __str_is_compatible, __eo_l_1___str_is_compatible,
            __str_is_empty, __eo_or, SmtEval.native_or]
    · cases ys' with
      | nil =>
          simp [atomChainTerm, __seq_empty, hV, __str_is_compatible,
            __eo_l_1___str_is_compatible, __str_is_empty, __eo_or, SmtEval.native_or]
      | cons b ys'' =>
          rw [atomChainTerm_cons]
          simp [__seq_empty, hV, __str_is_compatible, __eo_l_1___str_is_compatible,
            __str_is_empty, __eo_or, SmtEval.native_or]
  · by_cases hV : V = Term.UOp UserOp.Char
    · subst hV
      cases ys' with
      | nil =>
          simp [atomChainTerm, __seq_empty, hU, __str_is_compatible,
            __eo_l_1___str_is_compatible, __str_is_empty, __eo_or, SmtEval.native_or]
      | cons b ys'' =>
          rw [atomChainTerm_cons]
          simp [__seq_empty, hU, __str_is_compatible, __eo_l_1___str_is_compatible,
            __str_is_empty, __eo_or, SmtEval.native_or]
    · cases ys' with
      | nil =>
          simp [atomChainTerm, __seq_empty, hU, hV, __str_is_compatible,
            __eo_l_1___str_is_compatible, __str_is_empty, __eo_or, SmtEval.native_or]
      | cons b ys'' =>
          rw [atomChainTerm_cons]
          simp [__seq_empty, hU, hV, __str_is_compatible, __eo_l_1___str_is_compatible,
            __str_is_empty, __eo_or, SmtEval.native_or]

theorem seqEmptyOfSeq_compatR (U a W : Term) :
    __str_is_compatible (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W)
      (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) = Term.Boolean true := by
  by_cases hU : U = Term.UOp UserOp.Char
  · subst hU
    simp [__seq_empty, __str_is_compatible, __eo_l_1___str_is_compatible,
      __str_is_empty, __eo_or, SmtEval.native_or]
  · simp [__seq_empty, hU, __str_is_compatible, __eo_l_1___str_is_compatible,
      __str_is_empty, __eo_or, SmtEval.native_or]

theorem seqEmptyOfSeq_overlap_zero (U W : Term) (hW : W ≠ Term.Stuck) :
    __str_overlap_rec (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) W =
      Term.Numeral 0 := by
  by_cases hU : U = Term.UOp UserOp.Char
  · subst hU
    cases W with
    | Stuck => exact absurd rfl hW
    | _ => simp [__seq_empty, __str_overlap_rec]
  · cases W with
    | Stuck => exact absurd rfl hW
    | _ => simp [__seq_empty, hU, __str_overlap_rec]

theorem str_is_empty_ne_stuck {e : Term}
    (he : __str_is_empty e = Term.Boolean true) : e ≠ Term.Stuck := by
  intro h
  subst h
  simp [__str_is_empty] at he

theorem str_is_empty_cases (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    (∃ U, e = Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ∨
      e = Term.String [] := by
  unfold __str_is_empty at he
  split at he
  · cases he
  · next U => exact Or.inl ⟨U, rfl⟩
  · exact Or.inr rfl
  · cases he

theorem eo_is_list_nil_str_concat_of_str_is_empty (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) e = Term.Boolean true := by
  rcases str_is_empty_cases e he with ⟨U, rfl⟩ | rfl
  · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat]
  · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq, native_teq]

theorem eo_get_nil_rec_atomChain (xs : List Term) (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat) (atomChainTerm xs e) = e := by
  induction xs with
  | nil =>
      exact eo_get_nil_rec_str_concat_eq_of_nil_true e
        (eo_is_list_nil_str_concat_of_str_is_empty e he)
  | cons a xs ih =>
      rw [atomChainTerm_cons]
      change __eo_requires (Term.UOp UserOp.str_concat)
          (Term.UOp UserOp.str_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) (atomChainTerm xs e)) = e
      rw [ih]
      exact eo_requires_self_eq_of_ne_stuck (Term.UOp UserOp.str_concat) e (by simp)

theorem eo_is_list_atomChain (xs : List Term) (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) (atomChainTerm xs e) =
      Term.Boolean true := by
  exact eo_is_list_true_of_get_nil_rec_ne_stuck (Term.UOp UserOp.str_concat)
    (atomChainTerm xs e) (by
      rw [eo_get_nil_rec_atomChain xs e he]
      exact str_is_empty_ne_stuck he)

theorem eo_list_rev_rec_atomChain (xs : List Term) (e acc : Term)
    (he : __str_is_empty e = Term.Boolean true) (hacc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (atomChainTerm xs e) acc =
      atomChainTerm xs.reverse acc := by
  induction xs generalizing acc with
  | nil =>
      rcases str_is_empty_cases e he with ⟨U, rfl⟩ | rfl
      · simp [atomChainTerm, __eo_list_rev_rec]
      · simp [atomChainTerm, __eo_list_rev_rec]
  | cons a xs ih =>
      rw [atomChainTerm_cons]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) a
        (atomChainTerm xs e) acc hacc]
      rw [ih (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) acc) (by simp)]
      rw [List.reverse_cons, atomChainTerm_append]
      rfl

theorem eo_list_rev_atomChain (xs : List Term) (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (atomChainTerm xs e) =
      atomChainTerm xs.reverse e := by
  have hList := eo_is_list_atomChain xs e he
  have hGet := eo_get_nil_rec_atomChain xs e he
  rw [__eo_list_rev, hList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec (atomChainTerm xs e)
      (__eo_get_nil_rec (Term.UOp UserOp.str_concat) (atomChainTerm xs e))) (by decide)]
  rw [hGet]
  exact eo_list_rev_rec_atomChain xs e e he (str_is_empty_ne_stuck he)

theorem str_is_empty_boolean_of_ne_stuck (e : Term) (he : e ≠ Term.Stuck) :
    ∃ b, __str_is_empty e = Term.Boolean b := by
  cases e with
  | Stuck => exact False.elim (he rfl)
  | UOp1 op x =>
      cases op <;> try exact ⟨false, rfl⟩
      case seq_empty =>
        cases x with
        | Apply f U =>
            cases f with
            | UOp op =>
                cases op <;> exact ⟨_, rfl⟩
            | _ => exact ⟨false, rfl⟩
        | _ => exact ⟨false, rfl⟩
  | String w =>
      cases w with
      | nil => exact ⟨true, rfl⟩
      | cons ch rest => exact ⟨false, rfl⟩
  | _ => exact ⟨false, rfl⟩

theorem str_is_empty_compatL_chain (ex ey : Term)
    (hex : __str_is_empty ex = Term.Boolean true) (hey : ey ≠ Term.Stuck) :
    ∀ ys', __str_is_compatible ex (atomChainTerm ys' ey) = Term.Boolean true := by
  intro ys'
  rcases str_is_empty_cases ex hex with ⟨U, rfl⟩ | rfl
  · cases ys' with
    | nil =>
        obtain ⟨b, hb⟩ := str_is_empty_boolean_of_ne_stuck ey hey
        rw [show atomChainTerm [] ey = ey from rfl]
        simp only [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty]
        change __eo_or (Term.Boolean true) (__str_is_empty ey) = Term.Boolean true
        rw [hb]
        simp [__eo_or, SmtEval.native_or]
    | cons b ys'' =>
        rw [atomChainTerm_cons]
        simp [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty,
          __eo_or, SmtEval.native_or]
  · cases ys' with
    | nil =>
        obtain ⟨b, hb⟩ := str_is_empty_boolean_of_ne_stuck ey hey
        rw [show atomChainTerm [] ey = ey from rfl]
        simp only [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty]
        change __eo_or (Term.Boolean true) (__str_is_empty ey) = Term.Boolean true
        rw [hb]
        simp [__eo_or, SmtEval.native_or]
    | cons b ys'' =>
        rw [atomChainTerm_cons]
        simp [__str_is_compatible, __eo_l_1___str_is_compatible, __str_is_empty,
          __eo_or, SmtEval.native_or]

theorem str_is_empty_compatR (ex a W : Term)
    (hex : __str_is_empty ex = Term.Boolean true) :
    __str_is_compatible (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) ex =
      Term.Boolean true := by
  rcases str_is_empty_cases ex hex with ⟨U, rfl⟩ | rfl
  · exact seqEmpty_compatR U a W
  · exact strEmpty_compatR a W

theorem str_is_empty_overlap_zero (ex W : Term)
    (hex : __str_is_empty ex = Term.Boolean true) (hW : W ≠ Term.Stuck) :
    __str_overlap_rec ex W = Term.Numeral 0 := by
  rcases str_is_empty_cases ex hex with ⟨U, rfl⟩ | rfl
  · exact seqEmpty_overlap_zero U W hW
  · exact strEmpty_overlap_zero W hW

theorem overlap_rec_ne_stuck_args (x y : Term)
    (h : __str_overlap_rec x y ≠ Term.Stuck) : x ≠ Term.Stuck ∧ y ≠ Term.Stuck := by
  constructor
  · intro hx
    subst hx
    simp [__str_overlap_rec] at h
  · intro hy
    subst hy
    cases x <;> simp [__str_overlap_rec] at h

theorem str_flatten_empty_is_empty (e : Term)
    (he : __str_is_empty e = Term.Boolean true)
    (hf : __str_flatten e ≠ Term.Stuck) :
    __str_is_empty (__str_flatten e) = Term.Boolean true := by
  rcases str_is_empty_cases e he with ⟨U, rfl⟩ | rfl
  · change __str_is_empty
        (__eo_requires
          (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))
          (__seq_empty (__eo_typeof
            (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))))
          (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) =
        Term.Boolean true
    rw [eo_requires_eq_result_of_ne_stuck
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))
      (__seq_empty (__eo_typeof
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))))
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) hf]
    simp [__str_is_empty]
  · change __str_is_empty
        (__eo_requires (Term.String []) (__seq_empty (__eo_typeof (Term.String [])))
          (Term.String [])) = Term.Boolean true
    rw [eo_requires_eq_result_of_ne_stuck (Term.String [])
      (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) hf]
    simp [__str_is_empty]

theorem seqUnit_ne_seq_empty_typeof (e : Term) :
    Term.Apply (Term.UOp UserOp.seq_unit) e ≠
      __seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e)) := by
  intro h
  cases hTy : __eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e) <;>
    rw [hTy] at h
  case Apply f a =>
    cases f <;> try simp [__seq_empty] at h
    case UOp op =>
      cases op <;> try simp at h
      case Seq =>
        cases a <;> try simp at h
        case UOp op =>
          cases op <;> simp at h
  all_goals
    cases h

theorem str_flatten_seqUnit_eq_stuck (e : Term) :
    __str_flatten (Term.Apply (Term.UOp UserOp.seq_unit) e) = Term.Stuck := by
  simp [__str_flatten, __eo_requires, native_teq, native_ite,
    seqUnit_ne_seq_empty_typeof]

theorem seqUnit_typeof_eq_of_arg_ne_stuck (e : Term)
    (heTy : __eo_typeof e ≠ Term.Stuck) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e) =
      Term.Apply (Term.UOp UserOp.Seq) (__eo_typeof e) := by
  change __eo_typeof_seq_unit (__eo_typeof e) =
    Term.Apply (Term.UOp UserOp.Seq) (__eo_typeof e)
  cases hTy : __eo_typeof e <;>
    simp [__eo_typeof_seq_unit, hTy] at heTy ⊢

theorem seqUnit_typeof_eq_stuck_of_arg_stuck (e : Term)
    (heTy : __eo_typeof e = Term.Stuck) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e) = Term.Stuck := by
  change __eo_typeof_seq_unit (__eo_typeof e) = Term.Stuck
  rw [heTy]
  rfl

theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply (Term.UOp UserOp.Seq) T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty]
  case UOp op =>
    cases op <;> simp

theorem str_is_empty_seq_empty_seq (T : Term) :
    __str_is_empty (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) =
      Term.Boolean true := by
  cases T <;> simp [__seq_empty, __str_is_empty]
  case UOp op =>
    cases op <;> simp

theorem strConcat_is_list_seq_empty_seq (T : Term) :
    __eo_is_list (Term.UOp UserOp.str_concat)
      (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) =
    Term.Boolean true := by
  cases T <;>
    simp [__seq_empty, __eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_is_ok, __eo_requires,
      native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]
  case UOp op =>
    cases op <;>
      simp [__eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
        native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]

theorem strConcat_is_list_explicit_seq_empty_seq (T : Term) :
    __eo_is_list (Term.UOp UserOp.str_concat)
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) =
    Term.Boolean true := by
  cases T <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_is_ok, __eo_requires,
      native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]

theorem is_seq_const_rec_true_is_str_concat_list :
    ∀ ss : Term, __is_seq_const_rec ss = Term.Boolean true →
      __eo_is_list (Term.UOp UserOp.str_concat) ss = Term.Boolean true := by
  intro ss
  induction ss using __is_seq_const_rec.induct with
  | case1 =>
      intro h
      simp [__is_seq_const_rec] at h
  | case2 e tail ih =>
      intro h
      have hTail : __is_seq_const_rec tail = Term.Boolean true := by
        simpa [__is_seq_const_rec] using h
      have hTailList := ih hTail
      exact eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
        (Term.Apply (Term.UOp UserOp.seq_unit) e) tail (by decide) hTailList
  | case3 T =>
      intro _h
      exact strConcat_is_list_explicit_seq_empty_seq T
  | case4 ss _hStuck _hCons _hEmpty =>
      intro h
      simp [__is_seq_const_rec] at h

theorem is_seq_const_rec_true_cases (ss : Term)
    (h : __is_seq_const_rec ss = Term.Boolean true) :
    (∃ e tail, ss =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
        (Term.Apply (Term.UOp UserOp.seq_unit) e)) tail) ∨
    (∃ T, ss =
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) := by
  induction ss using __is_seq_const_rec.induct with
  | case1 =>
      simp [__is_seq_const_rec] at h
  | case2 e tail _ih =>
      exact Or.inl ⟨e, tail, rfl⟩
  | case3 T =>
      exact Or.inr ⟨T, rfl⟩
  | case4 ss _hStuck _hCons _hEmpty =>
      simp [__is_seq_const_rec] at h

theorem str_value_len_eq_list_len_rec_of_seq_const_rec_true :
    ∀ ss : Term, __is_seq_const_rec ss = Term.Boolean true →
      __str_value_len ss = __eo_list_len_rec ss := by
  intro ss
  induction ss using __is_seq_const_rec.induct with
  | case1 =>
      intro h
      simp [__is_seq_const_rec] at h
  | case2 e tail ih =>
      intro h
      have hTail : __is_seq_const_rec tail = Term.Boolean true := by
        simpa [__is_seq_const_rec] using h
      have hTailEq := ih hTail
      have hTailList := is_seq_const_rec_true_is_str_concat_list tail hTail
      have hRawList :
          __eo_is_list (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.UOp UserOp.seq_unit) e)) tail) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e) tail (by decide) hTailList
      simp [__str_value_len, __is_seq_const, __is_seq_const_rec, hTail,
        __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not,
        __eo_requires, __eo_list_len, hRawList]
  | case3 T =>
      intro _h
      have hList := strConcat_is_list_explicit_seq_empty_seq T
      simp [__str_value_len, __is_seq_const, __is_seq_const_rec,
        __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not,
        __eo_requires, __eo_list_len, hList, __eo_list_len_rec]
  | case4 ss _hStuck _hCons _hEmpty =>
      intro h
      simp [__is_seq_const_rec] at h

theorem eo_list_len_rec_numeral_of_seq_const_rec_true :
    ∀ ss : Term, __is_seq_const_rec ss = Term.Boolean true →
      ∃ n : Int, __eo_list_len_rec ss = Term.Numeral n := by
  intro ss
  induction ss using __is_seq_const_rec.induct with
  | case1 =>
      intro h
      simp [__is_seq_const_rec] at h
  | case2 e tail ih =>
      intro h
      have hTail : __is_seq_const_rec tail = Term.Boolean true := by
        simpa [__is_seq_const_rec] using h
      obtain ⟨m, hTailLen⟩ := ih hTail
      refine ⟨native_zplus 1 m, ?_⟩
      simp [__eo_list_len_rec, hTailLen, __eo_add]
  | case3 T =>
      intro _h
      exact ⟨0, by simp [__eo_list_len_rec]⟩
  | case4 ss _hStuck _hCons _hEmpty =>
      intro h
      simp [__is_seq_const_rec] at h

theorem eo_list_len_rec_numeral_nonneg_of_seq_const_rec_true :
    ∀ ss : Term, __is_seq_const_rec ss = Term.Boolean true →
      ∀ n : Int, __eo_list_len_rec ss = Term.Numeral n → 0 ≤ n := by
  intro ss
  induction ss using __is_seq_const_rec.induct with
  | case1 =>
      intro h
      simp [__is_seq_const_rec] at h
  | case2 e tail ih =>
      intro h n hLen
      have hTail : __is_seq_const_rec tail = Term.Boolean true := by
        simpa [__is_seq_const_rec] using h
      obtain ⟨m, hTailLen⟩ :=
        eo_list_len_rec_numeral_of_seq_const_rec_true tail hTail
      have hm : 0 ≤ m := ih hTail m hTailLen
      simp [__eo_list_len_rec, hTailLen, __eo_add] at hLen
      rw [← hLen]
      exact Int.add_nonneg (show (0 : Int) ≤ 1 by decide) hm
  | case3 T =>
      intro _h n hLen
      change Term.Numeral 0 = Term.Numeral n at hLen
      injection hLen with hn
      rw [← hn]
      decide
  | case4 ss _hStuck _hCons _hEmpty =>
      intro h
      simp [__is_seq_const_rec] at h

theorem str_value_len_numeral_of_seq_const_rec_true (ss : Term)
    (h : __is_seq_const_rec ss = Term.Boolean true) :
    ∃ n : Int, __str_value_len ss = Term.Numeral n := by
  obtain ⟨n, hLen⟩ := eo_list_len_rec_numeral_of_seq_const_rec_true ss h
  refine ⟨n, ?_⟩
  rw [str_value_len_eq_list_len_rec_of_seq_const_rec_true ss h, hLen]

theorem seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral
    (e ss : Term) (n : Int)
    (hLen : __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) =
      Term.Numeral n) :
    __is_seq_const_rec ss = Term.Boolean true := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  let raw := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) ss
  have hLenReq :
      __eo_requires (__is_seq_const_rec ss) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) raw) =
        Term.Numeral n := by
    simpa [raw, head, __str_value_len, __is_seq_const, __is_seq_const_rec,
      __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq, native_ite,
      SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not] using hLen
  have hReqNe :
      __eo_requires (__is_seq_const_rec ss) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) raw) ≠ Term.Stuck := by
    rw [hLenReq]
    simp
  exact eo_requires_eq_of_ne_stuck (__is_seq_const_rec ss) (Term.Boolean true)
    (__eo_list_len (Term.UOp UserOp.str_concat) raw) hReqNe

theorem value_len_tail_numeral_of_concat_seqUnit (e ss : Term) (n : Int)
    (h : __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) = Term.Numeral n) :
    ∃ m, __str_value_len ss = Term.Numeral m :=
  str_value_len_numeral_of_seq_const_rec_true ss
    (seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral e ss n h)

theorem str_value_len_concat_seqUnit_eq_add_tail (e ss : Term) (m : Int)
    (hTailSeq : __is_seq_const_rec ss = Term.Boolean true)
    (hTailLen : __str_value_len ss = Term.Numeral m) :
    __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) =
      Term.Numeral (native_zplus 1 m) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  let raw := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) ss
  have hRawSeq : __is_seq_const_rec raw = Term.Boolean true := by
    simpa [raw, head, __is_seq_const_rec] using hTailSeq
  have hRawEq := str_value_len_eq_list_len_rec_of_seq_const_rec_true raw hRawSeq
  have hTailEq := str_value_len_eq_list_len_rec_of_seq_const_rec_true ss hTailSeq
  have hTailRec : __eo_list_len_rec ss = Term.Numeral m := by
    rw [← hTailEq]
    exact hTailLen
  rw [hRawEq]
  simp [raw, __eo_list_len_rec, hTailRec, __eo_add]

theorem eo_list_len_rec_stuck_or_numeral :
    ∀ xs : Term, __eo_list_len_rec xs = Term.Stuck ∨
      ∃ n : Int, __eo_list_len_rec xs = Term.Numeral n := by
  intro xs
  induction xs using __eo_list_len_rec.induct with
  | case1 =>
      exact Or.inl rfl
  | case2 f x y ih =>
      rcases ih with hStuck | ⟨n, hNum⟩
      · left
        simp [__eo_list_len_rec, hStuck, __eo_add]
      · right
        refine ⟨native_zplus 1 n, ?_⟩
        simp [__eo_list_len_rec, hNum, __eo_add]
  | case3 nil _hStuck _hCons =>
      exact Or.inr ⟨0, by simp [__eo_list_len_rec]⟩

theorem eo_list_len_stuck_or_numeral (f xs : Term) :
    __eo_list_len f xs = Term.Stuck ∨
      ∃ n : Int, __eo_list_len f xs = Term.Numeral n := by
  cases hList : __eo_is_list f xs with
  | Boolean b =>
      cases b
      · left
        simp [__eo_list_len, hList, __eo_requires, native_teq, native_ite,
          SmtEval.native_ite]
      · rcases eo_list_len_rec_stuck_or_numeral xs with hStuck | ⟨n, hNum⟩
        · left
          simp [__eo_list_len, hList, __eo_requires, hStuck, native_teq,
            native_ite, SmtEval.native_ite, SmtEval.native_not]
        · right
          refine ⟨n, ?_⟩
          simp [__eo_list_len, hList, __eo_requires, hNum, native_teq,
            native_ite, SmtEval.native_ite, SmtEval.native_not]
  | Stuck =>
      left
      simp [__eo_list_len, hList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite]
  | _ =>
      left
      simp [__eo_list_len, hList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite]

theorem strConcat_is_list_seqUnit_false (e : Term) :
    __eo_is_list (Term.UOp UserOp.str_concat)
      (Term.Apply (Term.UOp UserOp.seq_unit) e) =
    Term.Boolean false := by
  simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
    __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq, __eo_requires,
    native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]

theorem seqUnit_arg_ne_stuck_of_intro_flatten_ne_stuck (e : Term)
    (hflatNe : __str_flatten (__str_nary_intro
        (Term.Apply (Term.UOp UserOp.seq_unit) e)) ≠ Term.Stuck) :
    __eo_typeof e ≠ Term.Stuck := by
  intro heTy
  have hHeadTy := seqUnit_typeof_eq_stuck_of_arg_stuck e heTy
  apply hflatNe
  simp [__str_nary_intro, __eo_list_singleton_intro,
    hHeadTy, __eo_nil, __eo_is_list,
    __eo_get_nil_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
    __eo_is_ok, __eo_eq, __eo_requires, __eo_ite, __str_flatten, native_teq,
    native_ite, SmtEval.native_ite, SmtEval.native_not]

theorem str_nary_intro_seqEmpty_eq_self (U : Term) :
    __str_nary_intro
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) := by
  simp [__str_nary_intro, __eo_list_singleton_intro, __eo_is_list,
    __eo_get_nil_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
    __eo_is_ok, __eo_requires, __eo_ite, native_teq, native_ite,
    SmtEval.native_ite, SmtEval.native_not]

theorem seq_empty_eq_explicit_seq_type (A U : Term)
    (h : __seq_empty A =
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) :
    A = Term.Apply (Term.UOp UserOp.Seq) U := by
  cases A
  case Apply f a =>
    cases f
    case UOp op =>
      cases op
      case Seq =>
        cases a
        case UOp op =>
          cases op
          case Char =>
            simp [__seq_empty] at h
          all_goals
            simp [__seq_empty] at h
            cases h
            rfl
        all_goals
          simp [__seq_empty] at h
          cases h
          rfl
      all_goals simp [__seq_empty] at h
    all_goals simp [__seq_empty] at h
  all_goals simp [__seq_empty] at h

theorem flatten_concat_seqUnit_tail_ne_stuck (e ss : Term)
    (h : __str_flatten
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) ≠ Term.Stuck) :
    __str_flatten ss ≠ Term.Stuck := by
  intro htail
  apply h
  simp [__str_flatten, htail, __eo_is_str, __eo_is_str_internal, native_teq,
    SmtEval.native_and, SmtEval.native_not, __eo_mk_apply, __eo_ite, native_ite]

theorem eo_is_str_false_of_not_string (c : Term)
    (h : ¬ ∃ w, c = Term.String w) :
    __eo_is_str c = Term.Boolean false := by
  cases c <;> simp [__eo_is_str, __eo_is_str_internal, native_teq,
    SmtEval.native_and, SmtEval.native_not] at h ⊢

theorem eo_is_str_true_cases (t : Term)
    (h : __eo_is_str t = Term.Boolean true) :
    ∃ w, t = Term.String w := by
  cases t <;> simp [__eo_is_str, __eo_is_str_internal, native_teq,
    SmtEval.native_and, SmtEval.native_not] at h
  · rename_i w
    exact ⟨w, rfl⟩

theorem eo_is_str_boolean_of_ne_stuck (t : Term) (ht : t ≠ Term.Stuck) :
    ∃ b, __eo_is_str t = Term.Boolean b := by
  unfold __eo_is_str
  exact ⟨native_and (native_not (native_teq t Term.Stuck))
    (native_teq (__eo_is_str_internal t) (Term.Boolean true)), rfl⟩

theorem str_value_len_ne_rational (c : Term) (r : native_Rat) :
    __str_value_len c ≠ Term.Rational r := by
  intro h
  by_cases hStuck : c = Term.Stuck
  · subst c
    simp [__str_value_len] at h
  by_cases hUnit : ∃ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    simp [__str_value_len] at h
  have hNotUnit : ∀ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
    intro e he
    exact hUnit ⟨e, he⟩
  rw [__str_value_len.eq_3 c hStuck hNotUnit] at h
  obtain ⟨b, hStrBool⟩ := eo_is_str_boolean_of_ne_stuck c hStuck
  cases b
  · rcases eo_list_len_stuck_or_numeral (Term.UOp UserOp.str_concat) c with
        hListLen | ⟨n, hListLen⟩
    · cases hSeq : __is_seq_const c <;>
        simp [hStrBool, eo_ite_false, __eo_requires, hSeq, hListLen,
          native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not] at h
    · cases hSeq : __is_seq_const c
      all_goals
        simp [hStrBool, eo_ite_false, __eo_requires, hSeq, hListLen,
          native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not] at h
      all_goals
        split at h <;> simp at h
  · obtain ⟨w, rfl⟩ := eo_is_str_true_cases c hStrBool
    simp [hStrBool, __eo_len, native_teq, native_ite, SmtEval.native_ite] at h

theorem str_value_len_ne_binary (c : Term) (w n : native_Int) :
    __str_value_len c ≠ Term.Binary w n := by
  intro h
  by_cases hStuck : c = Term.Stuck
  · subst c
    simp [__str_value_len] at h
  by_cases hUnit : ∃ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    simp [__str_value_len] at h
  have hNotUnit : ∀ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
    intro e he
    exact hUnit ⟨e, he⟩
  rw [__str_value_len.eq_3 c hStuck hNotUnit] at h
  obtain ⟨b, hStrBool⟩ := eo_is_str_boolean_of_ne_stuck c hStuck
  cases b
  · rcases eo_list_len_stuck_or_numeral (Term.UOp UserOp.str_concat) c with
        hListLen | ⟨m, hListLen⟩
    · cases hSeq : __is_seq_const c <;>
        simp [hStrBool, eo_ite_false, __eo_requires, hSeq, hListLen,
          native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not] at h
    · cases hSeq : __is_seq_const c
      all_goals
        simp [hStrBool, eo_ite_false, __eo_requires, hSeq, hListLen,
          native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not] at h
      all_goals
        split at h <;> simp at h
  · obtain ⟨str, rfl⟩ := eo_is_str_true_cases c hStrBool
    simp [hStrBool, __eo_len, native_teq, native_ite, SmtEval.native_ite] at h

/-- `value_len c = Numeral` forces `c` to be one of the four constant-like word forms. -/
theorem value_len_numeral_cases (c : Term) (n : Int) (h : __str_value_len c = Term.Numeral n) :
    (∃ w, c = Term.String w) ∨
    (∃ e ss, c = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) ∨
    (∃ T, c = Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) ∨
    (∃ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e) := by
  by_cases hString : ∃ w, c = Term.String w
  · exact Or.inl hString
  by_cases hUnit : ∃ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e
  · exact Or.inr (Or.inr (Or.inr hUnit))
  by_cases hStuck : c = Term.Stuck
  · subst c
    simp [__str_value_len] at h
  have hNotUnit : ∀ e, c = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
    intro e he
    exact hUnit ⟨e, he⟩
  have hIsStrFalse : __eo_is_str c = Term.Boolean false :=
    eo_is_str_false_of_not_string c hString
  have hLenReq :
      __eo_requires (__is_seq_const c) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) c) =
        Term.Numeral n := by
    rw [__str_value_len.eq_3 c hStuck hNotUnit] at h
    simpa [hIsStrFalse, eo_ite_false] using h
  have hReqNe :
      __eo_requires (__is_seq_const c) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) c) ≠ Term.Stuck := by
    rw [hLenReq]
    simp
  have hSeq : __is_seq_const c = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__is_seq_const c) (Term.Boolean true)
      (__eo_list_len (Term.UOp UserOp.str_concat) c) hReqNe
  have hSeqRec : __is_seq_const_rec c = Term.Boolean true := by
    rw [__is_seq_const.eq_3 c hStuck hNotUnit] at hSeq
    exact hSeq
  rcases is_seq_const_rec_true_cases c hSeqRec with
      ⟨e, tail, hEq⟩ | ⟨T, hEq⟩
  · exact Or.inr (Or.inl ⟨e, tail, hEq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨T, hEq⟩))

theorem str_value_len_numeral_nonneg :
    ∀ t : Term, ∀ n : Int, __str_value_len t = Term.Numeral n -> 0 ≤ n := by
  intro t n h
  rcases value_len_numeral_cases t n h with
      ⟨w, rfl⟩ | ⟨e, ss, hConcat⟩ | ⟨U, hEmpty⟩ | ⟨e, hUnit⟩
  · simp [str_value_len_string] at h
    rw [← h]
    exact Int.natCast_nonneg _
  · subst hConcat
    have hTailSeq :=
      seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral e ss n h
    let raw := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
      (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss
    have hRawSeq : __is_seq_const_rec raw = Term.Boolean true := by
      simpa [raw, __is_seq_const_rec] using hTailSeq
    have hRawEq :=
      str_value_len_eq_list_len_rec_of_seq_const_rec_true raw hRawSeq
    have hRec : __eo_list_len_rec raw = Term.Numeral n := by
      rw [← hRawEq]
      exact h
    exact eo_list_len_rec_numeral_nonneg_of_seq_const_rec_true raw hRawSeq n hRec
  · subst hEmpty
    simp [__str_value_len, __is_seq_const, __is_seq_const_rec,
      __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq, native_ite,
      SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not,
      __eo_requires, __eo_list_len, strConcat_is_list_explicit_seq_empty_seq,
      __eo_list_len_rec] at h
    rw [← h]
    decide
  · subst hUnit
    simp [__str_value_len] at h
    rw [← h]
    decide

theorem string_nil_of_value_len_zero (w : native_String)
    (h : __str_value_len (Term.String w) = Term.Numeral 0) :
    w = [] := by
  cases w with
  | nil => rfl
  | cons ch rest =>
      simp [str_value_len_string] at h
      exfalso
      have hpos : (0 : Int) < Int.ofNat rest.length + 1 :=
        Int.add_pos_of_nonneg_of_pos (Int.natCast_nonneg _)
          (show (0 : Int) < 1 by decide)
      change (0 : Int) < ↑rest.length + 1 at hpos
      rw [h] at hpos
      exact (show ¬ (0 : Int) < 0 by decide) hpos

theorem str_value_len_zero_is_empty (t : Term)
    (hLen0 : __str_value_len t = Term.Numeral 0) :
    __str_is_empty t = Term.Boolean true := by
  rcases value_len_numeral_cases t 0 hLen0 with
      ⟨w, rfl⟩ | ⟨e, ss, hConcat⟩ | ⟨U, rfl⟩ | ⟨e, rfl⟩
  · have hw : w = [] := string_nil_of_value_len_zero w hLen0
    subst hw
    simp [__str_is_empty]
  · subst hConcat
    have hTailSeq :=
      seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral e ss 0 hLen0
    obtain ⟨m, hTail⟩ :=
      value_len_tail_numeral_of_concat_seqUnit e ss 0 hLen0
    have hm : 0 ≤ m := str_value_len_numeral_nonneg ss m hTail
    have hConcatLen :=
      str_value_len_concat_seqUnit_eq_add_tail e ss m hTailSeq hTail
    rw [hConcatLen] at hLen0
    injection hLen0 with hLen0
    have hpos : (0 : Int) < 1 + m :=
      Int.add_pos_of_pos_of_nonneg (show (0 : Int) < 1 by decide) hm
    rw [show 1 + m = 0 by simpa [native_zplus] using hLen0] at hpos
    exact False.elim ((show ¬ (0 : Int) < 0 by decide) hpos)
  · simp [__str_is_empty]
  · simp [__str_value_len] at hLen0

theorem concatSeqUnit_len_one_tail_empty (e ss : Term)
    (hLen1 : __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) =
      Term.Numeral 1) :
    __str_is_empty ss = Term.Boolean true := by
  obtain ⟨m, hTail⟩ :=
    value_len_tail_numeral_of_concat_seqUnit e ss 1 hLen1
  have hm : 0 ≤ m := str_value_len_numeral_nonneg ss m hTail
  have hTailSeq :=
    seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral e ss 1 hLen1
  have hConcatLen :=
    str_value_len_concat_seqUnit_eq_add_tail e ss m hTailSeq hTail
  rw [hConcatLen] at hLen1
  injection hLen1 with hLen1
  have hm0 : m = 0 := by
    have hEq : 1 + m = 1 := by
      simpa [native_zplus] using hLen1
    have hEq0 : 1 + m = 1 + 0 := by
      simpa using hEq
    exact Int.add_left_cancel hEq0
  subst hm0
  exact str_value_len_zero_is_empty ss hTail

theorem str_is_empty_seq_empty_typeof_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_is_empty (__seq_empty (__eo_typeof x)) = Term.Boolean true := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rcases TranslationProofs.eo_to_smt_type_eq_seq hA with
    ⟨U, hType, _hU⟩
  rw [hType]
  cases U <;> simp [__seq_empty, __str_is_empty]
  case UOp op =>
    cases op <;> simp

theorem str_flatten_seq_empty_seq_of_type_eq
    (U : Term)
    (hUType : __eo_typeof U = Term.Type) :
    __str_flatten (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) := by
  by_cases hChar : U = Term.UOp UserOp.Char
  · subst U
    change __str_flatten (Term.String []) = Term.String []
    change __eo_requires (Term.String [])
      (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
      Term.String []
    change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
      Term.String []
    exact eo_requires_self_eq_of_ne_stuck (Term.String []) (Term.String [])
      (by intro h; cases h)
  · have hSeqEmpty :
        __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) U) := by
      cases U <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        exact False.elim (hChar rfl)
    rw [hSeqEmpty]
    let empty :=
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
    have hEmptyNe : empty ≠ Term.Stuck := by
      dsimp [empty]
      intro h
      cases h
    have hTypeEmpty :
        __eo_typeof empty = Term.Apply (Term.UOp UserOp.Seq) U := by
      dsimp [empty]
      change
        __eo_typeof_seq_empty
            (__eo_typeof (Term.Apply (Term.UOp UserOp.Seq) U))
            (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Apply (Term.UOp UserOp.Seq) U
      change
        __eo_typeof_seq_empty (__eo_typeof_Seq (__eo_typeof U))
            (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Apply (Term.UOp UserOp.Seq) U
      rw [hUType]
      rfl
    change __str_flatten empty = empty
    change __eo_requires empty (__seq_empty (__eo_typeof empty)) empty = empty
    rw [hTypeEmpty]
    have hSeqEmpty' :
        __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) = empty := by
      exact hSeqEmpty
    rw [hSeqEmpty']
    exact eo_requires_self_eq_of_ne_stuck empty empty hEmptyNe

theorem str_flatten_seq_empty_typeof_eq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_flatten (__seq_empty (__eo_typeof x)) =
      __seq_empty (__eo_typeof x) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rcases TranslationProofs.eo_to_smt_type_eq_seq hA with
    ⟨U, hType, hU⟩
  have hSeqWF :
      __smtx_type_wf (SmtType.Seq T) = true :=
    smt_term_seq_type_wf_of_non_none (__eo_to_smt x) hTrans hxTy
  have hSeqComp :
      __smtx_type_wf_component (SmtType.Seq T) = true := by
    simpa [__smtx_type_wf] using hSeqWF
  have hSeqRec :
      __smtx_type_wf_rec (SmtType.Seq T) = true :=
    (smtx_type_wf_component_parts hSeqComp).2
  have hTParts :
      native_inhabited_type T = true ∧
        __smtx_type_wf_rec T = true := by
    simpa [__smtx_type_wf_rec, native_and] using hSeqRec
  have hTRec : __smtx_type_wf_rec T = true :=
    hTParts.2
  have hUType : __eo_typeof U = Term.Type :=
    TranslationProofs.eo_typeof_type_of_smt_type_wf_rec U (by
      rw [hU]
      exact hTRec)
  rw [hType]
  exact str_flatten_seq_empty_seq_of_type_eq U hUType

theorem str_nary_intro_eq_singleton_of_is_list_false_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean false) :
    __str_nary_intro x = mkConcat x (__seq_empty (__eo_typeof x)) := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy :
      __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let empty := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hEmptyEq : empty = __seq_empty (__eo_typeof x) := by
    simpa [empty] using strConcat_nil_eq_seq_empty_of_type hTy
  have hEmptyNe : empty ≠ Term.Stuck := by
    rw [hEmptyEq]
    exact seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  have hEmptyList :
      __eo_is_list (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    rw [hEmptyEq]
    exact eo_is_list_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
      (seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy)
  have hApplyNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty ≠
        Term.Stuck := by
    cases hEmptyCases : empty <;>
      simp [__eo_mk_apply, hEmptyCases] at hEmptyNe ⊢
  have hApplyEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty =
        mkConcat x empty :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNe
  change
    __eo_ite (__eo_is_list (Term.UOp UserOp.str_concat) x) x
        (__eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) empty)
          (Term.Boolean true)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty)) =
      mkConcat x (__seq_empty (__eo_typeof x))
  rw [hList, eo_ite_false]
  rw [hEmptyList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
    (by decide)]
  rw [hApplyEq, hEmptyEq]

theorem str_flatten_str_nary_intro_of_is_list_false_non_string_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxNotString : ¬ ∃ s : native_String, x = Term.String s)
    (hxNotConcat : ∀ t tail, x ≠
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean false) :
    __str_flatten (__str_nary_intro x) = __str_nary_intro x := by
  have hxNe : x ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq x T hxTy
  have hIntroEq :=
    str_nary_intro_eq_singleton_of_is_list_false_seq x T hxTy hList
  have hIsStr : __eo_is_str x = Term.Boolean false := by
    cases x <;> simp [__eo_is_str, __eo_is_str_internal, native_teq,
      SmtEval.native_and, SmtEval.native_not] at hxNe ⊢
    case String w =>
      exact False.elim (hxNotString ⟨w, rfl⟩)
  have hFlatEmpty :
      __str_flatten (__seq_empty (__eo_typeof x)) =
        __seq_empty (__eo_typeof x) :=
    str_flatten_seq_empty_typeof_eq x T hxTy
  have hEmptyNe :
      __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  have hFlatEmptyNe :
      __str_flatten (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
    rw [hFlatEmpty]
    exact hEmptyNe
  have hApplySeq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
        mkConcat x (__seq_empty (__eo_typeof x)) := by
    apply eo_mk_apply_eq_apply_of_ne_stuck
    cases hEmpty : __seq_empty (__eo_typeof x) <;>
      simp [__eo_mk_apply, hEmpty] at hEmptyNe ⊢
  rw [hIntroEq]
  change
    __str_flatten
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))
  rw [flatten_concat_nonstr x (__seq_empty (__eo_typeof x)) hIsStr
    hxNotConcat hFlatEmptyNe]
  rw [hFlatEmpty]

theorem overlap_rec_singleton_le_one (a ex W : Term) (m : Int)
    (hex : __str_is_empty ex = Term.Boolean true)
    (hrec : __str_overlap_rec (mkConcat a ex) W = Term.Numeral m) :
    m ≤ 1 := by
  have hRecNe : __str_overlap_rec (mkConcat a ex) W ≠ Term.Stuck := by
    rw [hrec]
    simp
  have hWne : W ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args (mkConcat a ex) W hRecNe).2
  have hle :=
    overlap_rec_le_len ex W hWne
      (str_is_empty_overlap_zero ex W hex hWne) [a] m (by
        simpa [atomChainTerm] using hrec)
  simpa using hle

theorem flatWordView_of_len_nonempty (M : SmtModel) (t : Term) (S : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq S)
    (hflatNe : __str_flatten t ≠ Term.Stuck)
    (hlenEx : ∃ n, __str_value_len t = Term.Numeral n) :
    Nonempty (FlatWordView M t S T) := by
  obtain ⟨n, hlen⟩ := hlenEx
  rcases value_len_numeral_cases t n hlen with
      ⟨w, rfl⟩ | ⟨e, ss, rfl⟩ | ⟨U, rfl⟩ | ⟨e, rfl⟩
  · have hw : w = [] := str_flatten_string_nil_of_ne_stuck w hflatNe
    subst hw
    refine ⟨{
      atoms := [],
      ex := Term.String [],
      hflat := ?_,
      hlen := ?_,
      hunp := ?_,
      hexEmpty := by simp [__str_is_empty],
      hAtomTy := by simp,
      hAtomShape := by simp
    }⟩
    · change __eo_requires (Term.String []) (__seq_empty (__eo_typeof (Term.String [])))
          (Term.String []) = Term.String []
      exact eo_requires_eq_result_of_ne_stuck (Term.String [])
        (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) hflatNe
    · rw [str_value_len_string]
      simp
    · exact str_is_empty_eval_unpack_nil M (Term.String []) S (by simp [__str_is_empty]) hEval
  · let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    obtain ⟨hHeadTy, hTailTy⟩ := strConcat_args_of_seq_type head ss T hTy
    obtain ⟨⟨Shead, hHeadEval⟩, ⟨Stail, hTailEval⟩⟩ :=
      strConcat_args_eval_seq_of_concat_eval_seq M head ss ⟨S, hEval⟩
    have htailFlatNe : __str_flatten ss ≠ Term.Stuck :=
      flatten_concat_seqUnit_tail_ne_stuck e ss hflatNe
    have htailLenEx : ∃ m, __str_value_len ss = Term.Numeral m :=
      value_len_tail_numeral_of_concat_seqUnit e ss n hlen
    obtain ⟨tailView⟩ :=
      flatWordView_of_len_nonempty M ss Stail T hTailTy hTailEval htailFlatNe htailLenEx
    refine ⟨{
      atoms := head :: tailView.atoms,
      ex := tailView.ex,
      hflat := ?_,
      hlen := ?_,
      hunp := ?_,
      hexEmpty := tailView.hexEmpty,
      hAtomTy := ?_,
      hAtomShape := ?_
    }⟩
    · have hHeadNotStr : __eo_is_str head = Term.Boolean false := by
        simp [head, __eo_is_str, __eo_is_str_internal, native_teq,
          SmtEval.native_and, SmtEval.native_not]
      have hHeadNotConcat :
          ∀ t tail, head ≠
            Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail := by
        intro t tail h
        simp [head] at h
      rw [flatten_concat_nonstr head ss hHeadNotStr hHeadNotConcat htailFlatNe,
        tailView.hflat,
        atomChainTerm_cons]
    · have hTailSeq :=
        seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral e ss n hlen
      have hConcatLen :=
        str_value_len_concat_seqUnit_eq_add_tail e ss
          (Int.ofNat tailView.atoms.length) hTailSeq tailView.hlen
      rw [hConcatLen]
      simp [native_zplus, Int.add_comm]
    · have hHeadUnp : native_unpack_seq Shead = [seqElemVal M head] := by
        obtain ⟨Shead', hHeadEval', hHeadUnp'⟩ := eval_seqUnitAtom M e
        rw [hHeadEval] at hHeadEval'
        injection hHeadEval' with hSeq
        rw [hSeq]
        exact hHeadUnp'
      obtain ⟨Sxy, hxy, hunpxy⟩ := concat_unpack M head ss Shead Stail hHeadEval hTailEval
      have hSxy : S = Sxy := by
        rw [hEval] at hxy
        injection hxy
      rw [hSxy, hunpxy, hHeadUnp, tailView.hunp]
      simp
    · intro a ha
      have ha' := ha
      simp at ha'
      rcases ha' with rfl | haTail
      · exact hHeadTy
      · exact tailView.hAtomTy a haTail
    · intro a ha
      have ha' := ha
      simp at ha'
      rcases ha' with rfl | haTail
      · exact Or.inr ⟨e, rfl⟩
      · exact tailView.hAtomShape a haTail
  · refine ⟨{
      atoms := [],
      ex := __str_flatten
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)),
      hflat := rfl,
      hlen := by
        have hList := strConcat_is_list_explicit_seq_empty_seq U
        simp [__str_value_len, __is_seq_const, __is_seq_const_rec,
          __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq,
          native_ite, SmtEval.native_ite, SmtEval.native_and,
          SmtEval.native_not, __eo_requires, __eo_list_len, hList,
          __eo_list_len_rec],
      hunp := ?_,
      hexEmpty := ?_,
      hAtomTy := by simp,
      hAtomShape := by simp
    }⟩
    · exact str_is_empty_eval_unpack_nil M
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) S
        (by simp [__str_is_empty]) hEval
    · exact str_flatten_empty_is_empty
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))
        (by simp [__str_is_empty]) hflatNe
  · exfalso
    exact hflatNe (str_flatten_seqUnit_eq_stuck e)
termination_by t

noncomputable def flatWordView_of_len (M : SmtModel) (t : Term) (S : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq S)
    (hflatNe : __str_flatten t ≠ Term.Stuck)
    (hlenEx : ∃ n, __str_value_len t = Term.Numeral n) :
    FlatWordView M t S T :=
  Classical.choice (flatWordView_of_len_nonempty M t S T hTy hEval hflatNe hlenEx)

noncomputable def introWordView_concatSeqUnit (M : SmtModel) (e ss : Term) (S : SmtSeq) (T : SmtType)
    (hTailList : __eo_is_list (Term.UOp UserOp.str_concat) ss = Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss)) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss)) = SmtValue.Seq S)
    (hflatNe : __str_flatten (__str_nary_intro
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss)) ≠ Term.Stuck)
    (hlenEx : ∃ n, __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) = Term.Numeral n) :
    IntroWordView M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
        (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) S T := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  let raw := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) ss
  have hIntro : __str_nary_intro raw = raw :=
    str_nary_intro_concat_eq head ss hTailList
  have hRawFlatNe : __str_flatten raw ≠ Term.Stuck := by
    intro hFlat
    have hFlat' : __str_flatten (__str_nary_intro raw) = Term.Stuck := by
      rw [hIntro]
      exact hFlat
    exact hflatNe (by simpa [raw, head] using hFlat')
  let v : FlatWordView M raw S T :=
    flatWordView_of_len M raw S T hTy hEval hRawFlatNe hlenEx
  exact {
    atoms := v.atoms,
    ex := v.ex,
    hflat := by
      change __str_flatten (__str_nary_intro raw) = atomChainTerm v.atoms v.ex
      rw [hIntro]
      exact v.hflat,
    hlen := v.hlen,
    hunp := v.hunp,
    hexEmpty := v.hexEmpty,
    hAtomTy := v.hAtomTy,
    hAtomShape := v.hAtomShape
  }

theorem str_nary_intro_seqUnit_eq (e : Term) (heTy : __eo_typeof e ≠ Term.Stuck) :
    __str_nary_intro (Term.Apply (Term.UOp UserOp.seq_unit) e) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
        (Term.Apply (Term.UOp UserOp.seq_unit) e))
        (__seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e))) := by
  have hTy := seqUnit_typeof_eq_of_arg_ne_stuck e heTy
  have hArgList := strConcat_is_list_seqUnit_false e
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat)
        (__seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e))) =
      Term.Boolean true := by
    rw [hTy]
    exact strConcat_is_list_seq_empty_seq (__eo_typeof e)
  have hNilNe :
      __seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e)) ≠
        Term.Stuck := by
    rw [hTy]
    exact seq_empty_seq_ne_stuck (__eo_typeof e)
  have hNilEq :
      __eo_nil (Term.UOp UserOp.str_concat)
          (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        __seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e)) := by
    rw [hTy]
    rfl
  have hMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e))) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e))
          (__seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e))) := by
    rw [hNilEq]
    exact mk_apply_eq _ _ (by simp) hNilNe
  have hMkSeq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e))
          (__seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e))) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e))
          (__seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e))) :=
    mk_apply_eq _ _ (by simp) hNilNe
  simp [__str_nary_intro, __eo_list_singleton_intro, hArgList, hNilEq,
    hNilList, hMkSeq, __eo_ite, __eo_requires, native_teq, native_ite,
    SmtEval.native_ite, SmtEval.native_not]

def introWordView_seqUnit (M : SmtModel) (e : Term) (S : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtValue.Seq S)
    (hflatNe : __str_flatten (__str_nary_intro
        (Term.Apply (Term.UOp UserOp.seq_unit) e)) ≠ Term.Stuck) :
    IntroWordView M (Term.Apply (Term.UOp UserOp.seq_unit) e) S T := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  have heTy : __eo_typeof e ≠ Term.Stuck :=
    seqUnit_arg_ne_stuck_of_intro_flatten_ne_stuck e hflatNe
  have hHeadTy := seqUnit_typeof_eq_of_arg_ne_stuck e heTy
  have hIntro := str_nary_intro_seqUnit_eq e heTy
  let nil := __seq_empty (__eo_typeof head)
  have hHeadNotStr : __eo_is_str head = Term.Boolean false := by
    simp [head, __eo_is_str, __eo_is_str_internal, native_teq,
      SmtEval.native_and, SmtEval.native_not]
  have hIntroFlatNe :
      __str_flatten
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) nil) ≠
        Term.Stuck := by
    simpa [head, nil, hIntro] using hflatNe
  have hMkNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
          (__str_flatten nil) ≠ Term.Stuck := by
    simpa [head, nil, __str_flatten, hHeadNotStr, __eo_ite, native_teq,
      native_ite, SmtEval.native_ite] using hIntroFlatNe
  have hNilFlatNe : __str_flatten nil ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMkNe
  have hNilEmpty : __str_is_empty nil = Term.Boolean true := by
    rw [show nil = __seq_empty (__eo_typeof head) from rfl, hHeadTy]
    exact str_is_empty_seq_empty_seq (__eo_typeof e)
  refine {
    atoms := [head],
    ex := __str_flatten nil,
    hflat := ?_,
    hlen := ?_,
    hunp := ?_,
    hexEmpty := str_flatten_empty_is_empty nil hNilEmpty hNilFlatNe,
    hAtomTy := ?_,
    hAtomShape := ?_
  }
  · rw [show __str_nary_intro head =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) nil by
        simpa [head, nil] using hIntro]
    have hHeadNotConcat :
        ∀ t tail, head ≠
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail := by
      intro t tail h
      simp [head] at h
    rw [flatten_concat_nonstr head nil hHeadNotStr hHeadNotConcat hNilFlatNe]
    rfl
  · simp [head, __str_value_len]
  · obtain ⟨Shead, hHeadEval, hHeadUnp⟩ := eval_seqUnitAtom M e
    rw [hEval] at hHeadEval
    injection hHeadEval with hSeq
    rw [hSeq]
    simpa [head] using hHeadUnp
  · intro a ha
    simp [head] at ha
    subst a
    exact hTy
  · intro a ha
    simp [head] at ha
    subst a
    exact Or.inr ⟨e, rfl⟩

def introWordView_seqEmpty_self (M : SmtModel) (U : Term) (S : SmtSeq) (T : SmtType)
    (hEval : __smtx_model_eval M
        (__eo_to_smt (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) =
      SmtValue.Seq S)
    (hIntro : __str_nary_intro
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
    )
    (hflatNe : __str_flatten (__str_nary_intro
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) ≠
      Term.Stuck) :
    IntroWordView M (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) S T := by
  let emp := Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
  have hemp : __str_is_empty emp = Term.Boolean true := by
    simp [emp, __str_is_empty]
  have hflatNe' : __str_flatten emp ≠ Term.Stuck := by
    simpa [emp, hIntro] using hflatNe
  refine {
    atoms := [],
    ex := __str_flatten emp,
    hflat := ?_,
    hlen := by
      have hList := strConcat_is_list_explicit_seq_empty_seq U
      simp [__str_value_len, __is_seq_const, __is_seq_const_rec,
        __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq,
        native_ite, SmtEval.native_ite, SmtEval.native_and,
        SmtEval.native_not, __eo_requires, __eo_list_len, hList,
        __eo_list_len_rec],
    hunp := ?_,
    hexEmpty := str_flatten_empty_is_empty emp hemp hflatNe',
    hAtomTy := by simp,
    hAtomShape := by simp
  }
  · rw [hIntro]
    rfl
  · exact str_is_empty_eval_unpack_nil M emp S hemp (by simpa [emp] using hEval)

theorem seqEmpty_typeof_eq_of_intro_flatten_ne_stuck (U : Term)
    (hflatNe : __str_flatten (__str_nary_intro
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) ≠
      Term.Stuck) :
    __eo_typeof (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  let emp := Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
  have hReqNe :
      __eo_requires emp (__seq_empty (__eo_typeof emp)) emp ≠ Term.Stuck := by
    simpa [emp, str_nary_intro_seqEmpty_eq_self U, __str_flatten] using hflatNe
  have hEq : emp = __seq_empty (__eo_typeof emp) :=
    eo_requires_eq_of_ne_stuck emp (__seq_empty (__eo_typeof emp)) emp hReqNe
  exact seq_empty_eq_explicit_seq_type (__eo_typeof emp) U (by
    simpa [emp] using hEq.symm)

theorem str_nary_intro_seqEmpty_eq_self_of_nonChar (U : Term)
    (hflatNe : __str_flatten (__str_nary_intro
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) ≠
      Term.Stuck)
    (hU : U ≠ Term.UOp UserOp.Char) :
    __str_nary_intro
        (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) := by
  exact str_nary_intro_seqEmpty_eq_self U

theorem explicitCharEmpty_typeof :
    __eo_typeof
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  change __eo_typeof_seq_empty
      (__eo_typeof_Seq (__eo_typeof (Term.UOp UserOp.Char)))
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
    Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  change __eo_typeof_seq_empty (__eo_typeof_Seq Term.Type)
      (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
    Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  rfl

theorem explicitCharEmpty_smt_type :
    __smtx_typeof (__eo_to_smt
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
      SmtType.Seq SmtType.Char := by
  change __smtx_typeof
      (__eo_to_smt_seq_empty
        (__eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
    SmtType.Seq SmtType.Char
  change __smtx_typeof
      (__eo_to_smt_seq_empty
        (__smtx_typeof_guard SmtType.Char (SmtType.Seq SmtType.Char))) =
    SmtType.Seq SmtType.Char
  change __smtx_typeof (__eo_to_smt_seq_empty (SmtType.Seq SmtType.Char)) =
    SmtType.Seq SmtType.Char
  change __smtx_typeof (SmtTerm.seq_empty SmtType.Char) =
    SmtType.Seq SmtType.Char
  exact TranslationProofs.smtx_typeof_seq_empty_of_non_none SmtType.Char (by
    unfold __smtx_typeof
    simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and, native_ite,
      native_inhabited_type_seq, native_inhabited_type_char])

theorem str_flatten_string_empty :
    __str_flatten (Term.String []) = Term.String [] := by
  change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
    Term.String []
  simp [__eo_requires, native_teq, native_ite, SmtEval.native_not]

theorem explicitCharEmpty_distinct_string_false_type (ch : native_Char) :
    __are_distinct_terms_type
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))
        (Term.String [ch])
        (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
      Term.Boolean false := by
  simp [__are_distinct_terms_type, __eo_is_str, __eo_is_str_internal,
    native_teq, SmtEval.native_and, SmtEval.native_not, __eo_and]

theorem explicitCharEmpty_distinct_string_false (ch : native_Char) :
    __are_distinct_terms_type
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))
        (Term.String [ch])
        (__eo_typeof
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
      Term.Boolean false := by
  rw [explicitCharEmpty_typeof]
  exact explicitCharEmpty_distinct_string_false_type ch

theorem explicitCharEmpty_distinct_seqUnit_false_type (e : Term) :
    __are_distinct_terms_type
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))
        (Term.Apply (Term.UOp UserOp.seq_unit) e)
        (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
      Term.Boolean false := by
  simp [__are_distinct_terms_type, __eo_is_str, __eo_is_str_internal,
    native_teq, SmtEval.native_and, SmtEval.native_not, __eo_and]

theorem explicitCharEmpty_distinct_seqUnit_false (e : Term) :
    __are_distinct_terms_type
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))
        (Term.Apply (Term.UOp UserOp.seq_unit) e)
        (__eo_typeof
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
      Term.Boolean false := by
  rw [explicitCharEmpty_typeof]
  exact explicitCharEmpty_distinct_seqUnit_false_type e

theorem str_flatten_nary_intro_explicitCharEmpty_stuck :
    __str_flatten (__str_nary_intro
        (Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
      Term.Stuck := by
  native_decide

theorem str_is_compatible_explicitCharEmpty_cons_stuck (a : Term) (xs : List Term)
    (ex : Term)
    (hShape : (∃ ch, a = Term.String [ch]) ∨
      (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)) :
    __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))))
          (Term.String []))
        (atomChainTerm (a :: xs) ex) =
      Term.Stuck := by
  rw [atomChainTerm_cons]
  rcases hShape with ⟨ch, rfl⟩ | ⟨e, rfl⟩
  · simp [__str_is_compatible, __eo_l_1___str_is_compatible,
      explicitCharEmpty_typeof, explicitCharEmpty_distinct_string_false_type,
      __eo_eq, __eo_ite, native_teq, native_ite, __eo_requires]
  · simp [__str_is_compatible, __eo_l_1___str_is_compatible,
      explicitCharEmpty_typeof, explicitCharEmpty_distinct_seqUnit_false_type,
      __eo_eq, __eo_ite, native_teq, native_ite, __eo_requires]

theorem overlap_explicitCharEmpty_cons_stuck (a : Term) (xs : List Term) (ex : Term)
    (hEx : ex ≠ Term.Stuck)
    (hShape : (∃ ch, a = Term.String [ch]) ∨
      (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)) :
    __str_overlap_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))))
          (Term.String []))
        (atomChainTerm (a :: xs) ex) =
      Term.Stuck := by
  rw [overlap_rec_concat]
  · rw [str_is_compatible_explicitCharEmpty_cons_stuck a xs ex hShape]
    rfl
  · exact atomChainTerm_ne_stuck (a :: xs) ex hEx

theorem eo_typeof_char_of_smt_char (e : Term)
    (hTy : __smtx_typeof (__eo_to_smt e) = SmtType.Char) :
    __eo_typeof e = Term.UOp UserOp.Char := by
  have hSmtTy : __eo_to_smt_type (__eo_typeof e) = SmtType.Char :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type e hTy (by simp)
  exact TranslationProofs.eo_to_smt_type_eq_char hSmtTy

theorem seqUnit_arg_eo_type_char_of_smt_seq_char (e : Term)
    (hTy : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtType.Seq SmtType.Char) :
    __eo_typeof e = Term.UOp UserOp.Char := by
  change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt e)) =
    SmtType.Seq SmtType.Char at hTy
  exact eo_typeof_char_of_smt_char e
    (seq_unit_type_eq_arg_of_eq hTy).1

theorem str_is_compatible_cons_explicitCharEmpty_stuck (a : Term) (xs : List Term)
    (ex : Term)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char)
    (hShape : (∃ ch, a = Term.String [ch]) ∨
      (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)) :
    __str_is_compatible
        (atomChainTerm (a :: xs) ex)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))))
          (Term.String [])) =
      Term.Stuck := by
  rw [atomChainTerm_cons]
  rcases hShape with ⟨ch, rfl⟩ | ⟨e, rfl⟩
  · have hEq :
        __eo_eq (Term.String [ch])
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))) =
          Term.Boolean false := by
      simp [__eo_eq, native_teq]
    have hDistinct :
        __are_distinct_terms_type (Term.String [ch])
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))
          (__eo_typeof (Term.String [ch])) =
          Term.Boolean false := by
      have hType :
          __eo_typeof (Term.String [ch]) =
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
        exact strChar_typeof ch
      rw [hType]
      rw [__are_distinct_terms_type.eq_def]
      change __eo_and (__eo_is_str (Term.String [ch]))
          (__eo_is_str
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
        Term.Boolean false
      have hStringStr : __eo_is_str (Term.String [ch]) = Term.Boolean true :=
        strChar_is_str ch
      have hEmpNotStr :
          __eo_is_str
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))) =
            Term.Boolean false := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq,
          SmtEval.native_and, SmtEval.native_not]
      simp [hStringStr, hEmpNotStr, __eo_and, native_and]
    simp [__str_is_compatible, __eo_l_1___str_is_compatible,
      hEq, hDistinct, __eo_ite, native_ite, native_teq, __eo_requires]
  · have hEChar := seqUnit_arg_eo_type_char_of_smt_seq_char e hTy
    have hEq :
        __eo_eq (Term.Apply (Term.UOp UserOp.seq_unit) e)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))) =
          Term.Boolean false := by
      simp [__eo_eq, native_teq]
    have hDistinct :
        __are_distinct_terms_type (Term.Apply (Term.UOp UserOp.seq_unit) e)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))
          (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
          Term.Boolean false := by
      have hType :
          __eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e) =
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
        change __eo_typeof_seq_unit (__eo_typeof e) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
        rw [hEChar]
        rfl
      rw [hType]
      rw [__are_distinct_terms_type.eq_def]
      change __eo_and (__eo_is_str (Term.Apply (Term.UOp UserOp.seq_unit) e))
          (__eo_is_str
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))) =
        Term.Boolean false
      have hUnitNotStr :
          __eo_is_str (Term.Apply (Term.UOp UserOp.seq_unit) e) =
            Term.Boolean false := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq,
          SmtEval.native_and, SmtEval.native_not]
      have hEmpNotStr :
          __eo_is_str
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))) =
            Term.Boolean false := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq,
          SmtEval.native_and, SmtEval.native_not]
      simp [hUnitNotStr, hEmpNotStr, __eo_and, native_and]
    simp [__str_is_compatible, __eo_l_1___str_is_compatible,
      hEq, hDistinct, __eo_ite, native_ite, native_teq, __eo_requires]

theorem overlap_cons_explicitCharEmpty_stuck (a : Term) (xs : List Term) (ex : Term)
    (hEx : ex ≠ Term.Stuck)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char)
    (hShape : (∃ ch, a = Term.String [ch]) ∨
      (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)) :
    __str_overlap_rec
        (atomChainTerm (a :: xs) ex)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))))
          (Term.String [])) =
      Term.Stuck := by
  rw [atomChainTerm_cons]
  rw [overlap_rec_concat _ _ _ (by simp)]
  rw [← atomChainTerm_cons,
    str_is_compatible_cons_explicitCharEmpty_stuck a xs ex hTy hShape]
  rfl

theorem value_len_numeral_of_gt_false (c W : Term)
    (h : __eo_gt (__str_value_len c) W = Term.Boolean false) :
    ∃ n, __str_value_len c = Term.Numeral n := by
  cases hLen : __str_value_len c with
  | Numeral n => exact ⟨n, rfl⟩
  | Rational r => exact False.elim (str_value_len_ne_rational c r hLen)
  | Binary w n => exact False.elim (str_value_len_ne_binary c w n hLen)
  | _ =>
      rw [hLen] at h
      cases W <;> simp [__eo_gt] at h

theorem value_len_numeral_of_is_z (c : Term)
    (h : __eo_is_z (__str_value_len c) = Term.Boolean true) :
    ∃ n, __str_value_len c = Term.Numeral n := by
  cases hLen : __str_value_len c <;>
    simp [hLen, __eo_is_z, __eo_is_z_internal, native_teq,
      native_and, native_not] at h ⊢

theorem concatSeqUnit_tail_list_of_value_len_numeral (e ss : Term) (n : Int)
    (hLen : __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) =
      Term.Numeral n) :
    __eo_is_list (Term.UOp UserOp.str_concat) ss = Term.Boolean true := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  let raw := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) ss
  have hHeadNotStr : __eo_is_str raw = Term.Boolean false := by
    simp [raw, head, __eo_is_str, __eo_is_str_internal, native_teq,
      SmtEval.native_and, SmtEval.native_not]
  have hLenReq :
      __eo_requires (__is_seq_const raw) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) raw) =
        Term.Numeral n := by
    simpa [raw, head, __str_value_len, hHeadNotStr, eo_ite_false] using hLen
  have hReqNe :
      __eo_requires (__is_seq_const raw) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) raw) ≠ Term.Stuck := by
    rw [hLenReq]
    simp
  have hListLenNe :
      __eo_list_len (Term.UOp UserOp.str_concat) raw ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__is_seq_const raw)
      (Term.Boolean true) (__eo_list_len (Term.UOp UserOp.str_concat) raw)
      hReqNe
  have hListReqNe :
      __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) raw)
          (Term.Boolean true) (__eo_list_len_rec raw) ≠ Term.Stuck := by
    simpa [__eo_list_len] using hListLenNe
  have hRawList :
      __eo_is_list (Term.UOp UserOp.str_concat) raw = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_list (Term.UOp UserOp.str_concat) raw)
      (Term.Boolean true) (__eo_list_len_rec raw) hListReqNe
  exact eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
    head ss (by simpa [raw, head] using hRawList)

theorem numeral_gt_false_right_numeral (n : Int) (W : Term)
    (h : __eo_gt (Term.Numeral n) W = Term.Boolean false) :
    ∃ r : Int, W = Term.Numeral r ∧ n ≤ r := by
  cases W <;> simp [__eo_gt] at h
  case Numeral r =>
    refine ⟨r, rfl, ?_⟩
    have hnlt := of_decide_eq_false h
    exact Int.le_of_not_gt hnlt

theorem concatSeqUnit_tail_list_of_gt_false (e ss Y : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss)) = SmtType.Seq T)
    (hgt : __eo_gt (__str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss))
        (__str_overlap_rec
          (__str_flatten (__str_nary_intro
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss)))
          Y) = Term.Boolean false) :
    __eo_is_list (Term.UOp UserOp.str_concat) ss = Term.Boolean true := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  let raw := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) ss
  have hRawNe : raw ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq raw T hTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat)
      raw (by decide) hRawNe with ⟨isList, hRawList⟩
  cases isList
  · have hgtRaw : __eo_gt (__str_value_len raw)
        (__str_overlap_rec (__str_flatten (__str_nary_intro raw)) Y) =
        Term.Boolean false := by
      simpa [raw, head] using hgt
    obtain ⟨n, hLen⟩ :=
      value_len_numeral_of_gt_false raw
        (__str_overlap_rec (__str_flatten (__str_nary_intro raw)) Y)
        hgtRaw
    have hLenRaw : __str_value_len
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)) ss) =
        Term.Numeral n := by
      simpa [raw, head] using hLen
    exact concatSeqUnit_tail_list_of_value_len_numeral e ss n hLenRaw
  · exact eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
      head ss (by simpa [raw, head] using hRawList)

/-- A `String` literal evaluates to the packed string value. -/
theorem eval_string (M : SmtModel) (w : native_String) :
    __smtx_model_eval M (__eo_to_smt (Term.String w)) = SmtValue.Seq (native_pack_string w) := by
  rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl]; simp only [__smtx_model_eval]

theorem no_compat_of_introWordViews (M : SmtModel) (hM : model_wf M)
    (c d : Term) (Sc Sd : SmtSeq) (T : SmtType)
    (vc : IntroWordView M c Sc T) (vd : IntroWordView M d Sd T)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
          (__str_flatten (__str_nary_intro d))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) :=
  no_compat_of_word (seqElemVal M) c d Sc Sd vc.atoms vd.atoms vc.ex vd.ex
    vc.hflat vd.hflat vc.hlen vc.hunp vd.hunp
    (str_is_empty_ne_stuck vc.hexEmpty) (str_is_empty_ne_stuck vd.hexEmpty)
    (str_is_empty_compatL_chain vc.ex vd.ex vc.hexEmpty
      (str_is_empty_ne_stuck vd.hexEmpty))
    (fun a W => str_is_empty_compatR vd.ex a W vd.hexEmpty)
    (fun W hW => str_is_empty_overlap_zero vc.ex W vc.hexEmpty hW)
    (shaped_atoms_sound M hM T vc.atoms vd.atoms vc.hAtomTy vd.hAtomTy
      vc.hAtomShape vd.hAtomShape)
    hgt

theorem no_compat_of_introWordViews_reversed (M : SmtModel) (hM : model_wf M)
    (c d : Term) (Sc Sd : SmtSeq) (T : SmtType)
    (vc : IntroWordView M c Sc T) (vd : IntroWordView M d Sd T)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro c)))
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro d)))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).reverse.length →
      ¬ native_seq_compat ((native_unpack_seq Sc).reverse.drop k)
        (native_unpack_seq Sd).reverse := by
  have hRevC :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro c)) =
        atomChainTerm vc.atoms.reverse vc.ex := by
    rw [vc.hflat]
    exact eo_list_rev_atomChain vc.atoms vc.ex vc.hexEmpty
  have hRevD :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro d)) =
        atomChainTerm vd.atoms.reverse vd.ex := by
    rw [vd.hflat]
    exact eo_list_rev_atomChain vd.atoms vd.ex vd.hexEmpty
  have hlenRev :
      __str_value_len c =
        Term.Numeral (Int.ofNat vc.atoms.reverse.length) := by
    simpa using vc.hlen
  have hunpC :
      (native_unpack_seq Sc).reverse =
        vc.atoms.reverse.map (seqElemVal M) := by
    rw [vc.hunp]
    simp
  have hunpD :
      (native_unpack_seq Sd).reverse =
        vd.atoms.reverse.map (seqElemVal M) := by
    rw [vd.hunp]
    simp
  exact no_compat_of_word_values (seqElemVal M)
    (__str_value_len c)
    (__eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__str_nary_intro c)))
    (__eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__str_nary_intro d)))
    (native_unpack_seq Sc).reverse (native_unpack_seq Sd).reverse
    vc.atoms.reverse vd.atoms.reverse vc.ex vd.ex
    hRevC hRevD hlenRev hunpC hunpD
    (str_is_empty_ne_stuck vc.hexEmpty) (str_is_empty_ne_stuck vd.hexEmpty)
    (str_is_empty_compatL_chain vc.ex vd.ex vc.hexEmpty
      (str_is_empty_ne_stuck vd.hexEmpty))
    (fun a W => str_is_empty_compatR vd.ex a W vd.hexEmpty)
    (fun W hW => str_is_empty_overlap_zero vc.ex W vc.hexEmpty hW)
    (fun a ha b hb heq hdist =>
      shaped_atoms_sound M hM T vc.atoms vd.atoms vc.hAtomTy vd.hAtomTy
        vc.hAtomShape vd.hAtomShape
        a (by simpa using ha) b (by simpa using hb) heq hdist)
    hgt

/-- The no-overlap `(A)` condition, dispatching on the representation of the
constant-like words `c`/`d`.  The `String`-literal case is closed via the
committed char-chain bridge `no_compat_string`. -/
theorem no_compat_dispatch (M : SmtModel) (hM : model_wf M)
    (c d : Term) (Sc Sd : SmtSeq) (T : SmtType)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T)
    (hdTy : __smtx_typeof (__eo_to_smt d) = SmtType.Seq T)
    (hSc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hSd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
          (__str_flatten (__str_nary_intro d))) = Term.Boolean false)
  (hgtRev : __eo_gt (__str_value_len d)
        (__str_overlap_rec (__str_flatten (__str_nary_intro d))
          (__str_flatten (__str_nary_intro c))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
  have hrecNe : __str_overlap_rec (__str_flatten (__str_nary_intro c))
      (__str_flatten (__str_nary_intro d)) ≠ Term.Stuck := by
    intro hs
    rw [hs] at hgt
    cases __str_value_len c <;> simp [__eo_gt] at hgt
  have hcflatNe : __str_flatten (__str_nary_intro c) ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args _ _ hrecNe).1
  have hdflatNe : __str_flatten (__str_nary_intro d) ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args _ _ hrecNe).2
  have hlenCEx : ∃ n, __str_value_len c = Term.Numeral n :=
    value_len_numeral_of_gt_false c
      (__str_overlap_rec (__str_flatten (__str_nary_intro c))
        (__str_flatten (__str_nary_intro d))) hgt
  have hlenDEx : ∃ n, __str_value_len d = Term.Numeral n :=
    value_len_numeral_of_gt_false d
      (__str_overlap_rec (__str_flatten (__str_nary_intro d))
        (__str_flatten (__str_nary_intro c))) hgtRev
  have finish :
      IntroWordView M c Sc T → IntroWordView M d Sd T →
        ∀ k, k < (native_unpack_seq Sc).length →
          ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
    intro vc vd
    exact no_compat_of_introWordViews M hM c d Sc Sd T vc vd hgt
  have dispatchD :
      IntroWordView M c Sc T →
        ∀ k, k < (native_unpack_seq Sc).length →
          ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
    intro vc
    obtain ⟨nD, hLenD⟩ := hlenDEx
    rcases value_len_numeral_cases d nD hLenD with
        ⟨wd, rfl⟩ | ⟨ed, ssd, rfl⟩ | ⟨Ud, rfl⟩ | ⟨ed, rfl⟩
    · exact finish vc (introWordView_string M wd Sd T hdTy hSd)
    · have hTailListD :
          __eo_is_list (Term.UOp UserOp.str_concat) ssd = Term.Boolean true :=
        concatSeqUnit_tail_list_of_gt_false ed ssd
          (__str_flatten (__str_nary_intro c)) T hdTy hgtRev
      exact finish vc
        (introWordView_concatSeqUnit M ed ssd Sd T hTailListD hdTy hSd hdflatNe
          ⟨nD, hLenD⟩)
    · by_cases hUd : Ud = Term.UOp UserOp.Char
      · subst hUd
        exact False.elim (hdflatNe str_flatten_nary_intro_explicitCharEmpty_stuck)
      · have hIntro := str_nary_intro_seqEmpty_eq_self_of_nonChar Ud hdflatNe hUd
        exact finish vc (introWordView_seqEmpty_self M Ud Sd T hSd hIntro hdflatNe)
    · exact finish vc (introWordView_seqUnit M ed Sd T hdTy hSd hdflatNe)
  obtain ⟨nC, hLenC⟩ := hlenCEx
  rcases value_len_numeral_cases c nC hLenC with
      ⟨wc, rfl⟩ | ⟨ec, ssc, rfl⟩ | ⟨Uc, rfl⟩ | ⟨ec, rfl⟩
  · exact dispatchD (introWordView_string M wc Sc T hcTy hSc)
  · have hTailListC :
        __eo_is_list (Term.UOp UserOp.str_concat) ssc = Term.Boolean true :=
      concatSeqUnit_tail_list_of_gt_false ec ssc
        (__str_flatten (__str_nary_intro d)) T hcTy hgt
    exact dispatchD
      (introWordView_concatSeqUnit M ec ssc Sc T hTailListC hcTy hSc hcflatNe
        ⟨nC, hLenC⟩)
  · intro k hk
    have hnil := str_is_empty_eval_unpack_nil M
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) Uc)) Sc
      (by simp [__str_is_empty]) hSc
    rw [hnil] at hk
    simp at hk
  · exact dispatchD (introWordView_seqUnit M ec Sc T hcTy hSc hcflatNe)

theorem no_compat_dispatch_endpoint_left (M : SmtModel) (hM : model_wf M)
    (c d : Term) (Sc Sd : SmtSeq) (T : SmtType)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T)
    (hdTy : __smtx_typeof (__eo_to_smt d) = SmtType.Seq T)
    (hSc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hSd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hLenDIsZ : __eo_is_z (__str_value_len d) = Term.Boolean true)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
          (__str_flatten (__str_nary_intro d))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
  have hrecNe : __str_overlap_rec (__str_flatten (__str_nary_intro c))
      (__str_flatten (__str_nary_intro d)) ≠ Term.Stuck := by
    intro hs
    rw [hs] at hgt
    cases __str_value_len c <;> simp [__eo_gt] at hgt
  have hcflatNe : __str_flatten (__str_nary_intro c) ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args _ _ hrecNe).1
  have hdflatNe : __str_flatten (__str_nary_intro d) ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args _ _ hrecNe).2
  have hlenCEx : ∃ n, __str_value_len c = Term.Numeral n :=
    value_len_numeral_of_gt_false c
      (__str_overlap_rec (__str_flatten (__str_nary_intro c))
        (__str_flatten (__str_nary_intro d))) hgt
  have hlenDEx : ∃ n, __str_value_len d = Term.Numeral n :=
    value_len_numeral_of_is_z d hLenDIsZ
  have finish :
      IntroWordView M c Sc T → IntroWordView M d Sd T →
        ∀ k, k < (native_unpack_seq Sc).length →
          ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
    intro vc vd
    exact no_compat_of_introWordViews M hM c d Sc Sd T vc vd hgt
  have dispatchD :
      IntroWordView M c Sc T →
        ∀ k, k < (native_unpack_seq Sc).length →
          ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
    intro vc
    obtain ⟨nD, hLenD⟩ := hlenDEx
    rcases value_len_numeral_cases d nD hLenD with
        ⟨wd, rfl⟩ | ⟨ed, ssd, rfl⟩ | ⟨Ud, rfl⟩ | ⟨ed, rfl⟩
    · exact finish vc (introWordView_string M wd Sd T hdTy hSd)
    · have hTailListD :
          __eo_is_list (Term.UOp UserOp.str_concat) ssd = Term.Boolean true :=
        concatSeqUnit_tail_list_of_value_len_numeral ed ssd nD hLenD
      exact finish vc
        (introWordView_concatSeqUnit M ed ssd Sd T hTailListD hdTy hSd hdflatNe
          ⟨nD, hLenD⟩)
    · by_cases hUd : Ud = Term.UOp UserOp.Char
      · subst hUd
        exact False.elim (hdflatNe str_flatten_nary_intro_explicitCharEmpty_stuck)
      · have hIntro := str_nary_intro_seqEmpty_eq_self_of_nonChar Ud hdflatNe hUd
        exact finish vc (introWordView_seqEmpty_self M Ud Sd T hSd hIntro hdflatNe)
    · exact finish vc (introWordView_seqUnit M ed Sd T hdTy hSd hdflatNe)
  obtain ⟨nC, hLenC⟩ := hlenCEx
  rcases value_len_numeral_cases c nC hLenC with
      ⟨wc, rfl⟩ | ⟨ec, ssc, rfl⟩ | ⟨Uc, rfl⟩ | ⟨ec, rfl⟩
  · exact dispatchD (introWordView_string M wc Sc T hcTy hSc)
  · have hTailListC :
        __eo_is_list (Term.UOp UserOp.str_concat) ssc = Term.Boolean true :=
      concatSeqUnit_tail_list_of_gt_false ec ssc
        (__str_flatten (__str_nary_intro d)) T hcTy hgt
    exact dispatchD
      (introWordView_concatSeqUnit M ec ssc Sc T hTailListC hcTy hSc hcflatNe
        ⟨nC, hLenC⟩)
  · intro k hk
    have hnil := str_is_empty_eval_unpack_nil M
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) Uc)) Sc
      (by simp [__str_is_empty]) hSc
    rw [hnil] at hk
    simp at hk
  · exact dispatchD (introWordView_seqUnit M ec Sc T hcTy hSc hcflatNe)

theorem no_compat_dispatch_endpoint_right (M : SmtModel) (hM : model_wf M)
    (c d : Term) (Sc Sd : SmtSeq) (T : SmtType)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T)
    (hdTy : __smtx_typeof (__eo_to_smt d) = SmtType.Seq T)
    (hSc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hSd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hLenDIsZ : __eo_is_z (__str_value_len d) = Term.Boolean true)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro c)))
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__str_nary_intro d)))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).reverse.length →
      ¬ native_seq_compat ((native_unpack_seq Sc).reverse.drop k)
        (native_unpack_seq Sd).reverse := by
  have hrecNe : __str_overlap_rec
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__str_nary_intro c)))
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__str_nary_intro d))) ≠ Term.Stuck := by
    intro hs
    rw [hs] at hgt
    cases __str_value_len c <;> simp [__eo_gt] at hgt
  have hrevCNe : __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__str_nary_intro c)) ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args _ _ hrecNe).1
  have hrevDNe : __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__str_nary_intro d)) ≠ Term.Stuck :=
    (overlap_rec_ne_stuck_args _ _ hrecNe).2
  have hcflatNe : __str_flatten (__str_nary_intro c) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_flatten (__str_nary_intro c)) hrevCNe
  have hdflatNe : __str_flatten (__str_nary_intro d) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_flatten (__str_nary_intro d)) hrevDNe
  have hlenCEx : ∃ n, __str_value_len c = Term.Numeral n :=
    value_len_numeral_of_gt_false c
      (__str_overlap_rec
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro c)))
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro d)))) hgt
  have hlenDEx : ∃ n, __str_value_len d = Term.Numeral n :=
    value_len_numeral_of_is_z d hLenDIsZ
  have finish :
      IntroWordView M c Sc T → IntroWordView M d Sd T →
        ∀ k, k < (native_unpack_seq Sc).reverse.length →
          ¬ native_seq_compat ((native_unpack_seq Sc).reverse.drop k)
            (native_unpack_seq Sd).reverse := by
    intro vc vd
    exact no_compat_of_introWordViews_reversed M hM c d Sc Sd T vc vd hgt
  have dispatchD :
      IntroWordView M c Sc T →
        ∀ k, k < (native_unpack_seq Sc).reverse.length →
          ¬ native_seq_compat ((native_unpack_seq Sc).reverse.drop k)
            (native_unpack_seq Sd).reverse := by
    intro vc
    obtain ⟨nD, hLenD⟩ := hlenDEx
    rcases value_len_numeral_cases d nD hLenD with
        ⟨wd, rfl⟩ | ⟨ed, ssd, rfl⟩ | ⟨Ud, rfl⟩ | ⟨ed, rfl⟩
    · exact finish vc (introWordView_string M wd Sd T hdTy hSd)
    · have hTailListD :
          __eo_is_list (Term.UOp UserOp.str_concat) ssd = Term.Boolean true :=
        concatSeqUnit_tail_list_of_value_len_numeral ed ssd nD hLenD
      exact finish vc
        (introWordView_concatSeqUnit M ed ssd Sd T hTailListD hdTy hSd hdflatNe
          ⟨nD, hLenD⟩)
    · by_cases hUd : Ud = Term.UOp UserOp.Char
      · subst hUd
        exact False.elim (hdflatNe str_flatten_nary_intro_explicitCharEmpty_stuck)
      · have hIntro := str_nary_intro_seqEmpty_eq_self_of_nonChar Ud hdflatNe hUd
        exact finish vc (introWordView_seqEmpty_self M Ud Sd T hSd hIntro hdflatNe)
    · exact finish vc (introWordView_seqUnit M ed Sd T hdTy hSd hdflatNe)
  obtain ⟨nC, hLenC⟩ := hlenCEx
  rcases value_len_numeral_cases c nC hLenC with
      ⟨wc, rfl⟩ | ⟨ec, ssc, rfl⟩ | ⟨Uc, rfl⟩ | ⟨ec, rfl⟩
  · exact dispatchD (introWordView_string M wc Sc T hcTy hSc)
  · have hTailListC :
        __eo_is_list (Term.UOp UserOp.str_concat) ssc = Term.Boolean true :=
      concatSeqUnit_tail_list_of_value_len_numeral ec ssc nC hLenC
    exact dispatchD
      (introWordView_concatSeqUnit M ec ssc Sc T hTailListC hcTy hSc hcflatNe
        ⟨nC, hLenC⟩)
  · intro k hk
    have hnil := str_is_empty_eval_unpack_nil M
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) Uc)) Sc
      (by simp [__str_is_empty]) hSc
    rw [hnil] at hk
    simp at hk
  · exact dispatchD (introWordView_seqUnit M ec Sc T hcTy hSc hcflatNe)

/-- Prefixes are preserved by appending extra elements on the right. -/
theorem native_seq_prefix_eq_append_right_of_prefix
    (pat xs rest : List SmtValue)
    (h : native_seq_prefix_eq pat xs = true) :
    native_seq_prefix_eq pat (xs ++ rest) = true := by
  rw [native_seq_prefix_eq_iff] at h ⊢
  rcases h with ⟨r, hEq⟩
  refine ⟨r ++ rest, ?_⟩
  rw [hEq]
  simp [List.append_assoc]

/-- Under the endpoint no-overlap condition, a prefix match in `S ++ C` was
already a prefix match in `S`; otherwise the match would straddle the right
endpoint. -/
theorem native_seq_prefix_eq_of_append_right_no_endpoint_overlap
    (S C L D : List SmtValue)
    (hNo : ∀ k, k < C.reverse.length →
      ¬ native_seq_compat (C.reverse.drop k) D.reverse)
    (h : native_seq_prefix_eq (L ++ D) (S ++ C) = true) :
    native_seq_prefix_eq (L ++ D) S = true := by
  by_cases hLen : (L ++ D).length ≤ S.length
  · rw [native_seq_prefix_eq_iff] at h ⊢
    rcases h with ⟨r, hEq⟩
    refine ⟨S.drop (L ++ D).length, ?_⟩
    have hTake : S.take (L ++ D).length = L ++ D := by
      calc
        S.take (L ++ D).length = (S ++ C).take (L ++ D).length := by
          rw [List.take_append_of_le_length hLen]
        _ = ((L ++ D) ++ r).take (L ++ D).length := by rw [hEq]
        _ = L ++ D := by rw [List.take_left]
    calc
      S = S.take (L ++ D).length ++ S.drop (L ++ D).length := by
        rw [List.take_append_drop]
      _ = (L ++ D) ++ S.drop (L ++ D).length := by rw [hTake]
  · exfalso
    have hContainsHay :
        native_seq_contains (S ++ C) (L ++ D) = true := by
      rw [native_seq_contains_iff_decomp]
      rw [native_seq_prefix_eq_iff] at h
      rcases h with ⟨r, hEq⟩
      exact ⟨[], r, by simpa using hEq⟩
    have hContainsS :
        native_seq_contains S (L ++ D) = true :=
      native_seq_contains_drop_right_of_no_endpoint_overlap S C L D hNo
        hContainsHay
    rcases native_seq_contains_decomp_exists S (L ++ D) hContainsS with
      ⟨before, after, hEq⟩
    have hPatLe : (L ++ D).length ≤ S.length := by
      rw [hEq]
      simp [List.length_append]
      omega
    exact hLen hPatLe

/-- A successful bounded recursive search witnesses `contains`. -/
theorem native_seq_contains_of_indexof_rec_ne_neg
    (xs pat : List SmtValue) (i fuel : Nat)
    (h : native_seq_indexof_rec xs pat i fuel ≠ -1) :
    native_seq_contains xs pat = true := by
  rcases native_seq_indexof_rec_bound xs pat i fuel with hNeg | hHit
  · exact False.elim (h hNeg)
  · rcases hHit with ⟨j, hRec, _hj⟩
    rcases native_seq_indexof_rec_decomp xs pat i fuel (i + j) hRec with
      ⟨_hLe, before, after, hXs, _hBeforeLen⟩
    rw [hXs]
    exact native_seq_contains_of_decomp before pat after

/-- Appending a right endpoint that cannot participate in an endpoint overlap
does not change the zero-start `indexof` result. -/
theorem native_seq_indexof_append_right_of_no_endpoint_overlap
    (S C L D : List SmtValue)
    (hNo : ∀ k, k < C.reverse.length →
      ¬ native_seq_compat (C.reverse.drop k) D.reverse) :
    native_seq_indexof (S ++ C) (L ++ D) 0 =
      native_seq_indexof S (L ++ D) 0 := by
  let P := L ++ D
  have hSearch :
      ∀ (S' : List SmtValue) (i : Nat),
        (if h : P.length ≤ (S' ++ C).length then
            native_seq_indexof_rec (S' ++ C) P i
              ((S' ++ C).length - P.length + 1)
          else
            (-1 : native_Int)) =
        (if h : P.length ≤ S'.length then
            native_seq_indexof_rec S' P i (S'.length - P.length + 1)
          else
            (-1 : native_Int)) := by
    intro S'
    induction S' with
    | nil =>
        intro i
        by_cases hEmpty : P = []
        · have hLenZero : P.length = 0 := by rw [hEmpty]; rfl
          simp [hEmpty]
          change native_seq_indexof_rec C [] i (C.length + 1) = Int.ofNat i
          change native_seq_indexof_rec C [] i (Nat.succ C.length) = Int.ofNat i
          unfold native_seq_indexof_rec
          simp [native_seq_prefix_eq]
        · have hLenNe : P.length ≠ 0 := by
            intro hLenZero
            exact hEmpty (List.eq_nil_of_length_eq_zero hLenZero)
          have hPos : 0 < P.length := Nat.pos_of_ne_zero hLenNe
          simp only [List.nil_append, List.length_nil]
          by_cases hBounds : P.length ≤ C.length
          · rw [dif_pos hBounds]
            rw [dif_neg (by omega : ¬ P.length ≤ 0)]
            by_cases hRec : native_seq_indexof_rec C P i
                (C.length - P.length + 1) = -1
            · exact hRec
            · exfalso
              have hContainsC :
                  native_seq_contains C P = true :=
                native_seq_contains_of_indexof_rec_ne_neg C P i
                  (C.length - P.length + 1) hRec
              have hContainsNil :
                  native_seq_contains ([] : List SmtValue) P = true :=
                native_seq_contains_drop_right_of_no_endpoint_overlap
                  ([] : List SmtValue) C L D (by simpa [P] using hNo)
                  (by simpa [P] using hContainsC)
              rcases native_seq_contains_decomp_exists ([] : List SmtValue) P
                  hContainsNil with ⟨before, after, hEq⟩
              have hLenEq := congrArg List.length hEq
              simp [List.length_append] at hLenEq
              omega
          · rw [dif_neg hBounds]
            rw [dif_neg (by omega : ¬ P.length ≤ 0)]
        | cons a S ih =>
        intro i
        by_cases hLeft : P.length ≤ ((a :: S) ++ C).length
        · by_cases hRight : P.length ≤ (a :: S).length
          · rw [dif_pos hLeft, dif_pos hRight]
            unfold native_seq_indexof_rec
            have hPref :
                native_seq_prefix_eq P ((a :: S) ++ C) =
                  native_seq_prefix_eq P (a :: S) := by
              apply Bool.eq_iff_iff.mpr
              constructor
              · intro hp
                exact native_seq_prefix_eq_of_append_right_no_endpoint_overlap
                  (a :: S) C L D (by simpa [P] using hNo) (by simpa [P] using hp)
              · intro hp
                simpa using native_seq_prefix_eq_append_right_of_prefix P (a :: S) C hp
            rw [hPref]
            by_cases hp : native_seq_prefix_eq P (a :: S) = true
            · simp [hp]
            · simp [hp]
              have hTail := ih (i + 1)
              by_cases hTailLeft : P.length ≤ (S ++ C).length
              · by_cases hTailRight : P.length ≤ S.length
                · have hTailLeftLen : P.length ≤ S.length + C.length := by
                    simpa [List.length_append] using hTailLeft
                  have hTailRightLen : P.length ≤ S.length := hTailRight
                  have hFuelLeft :
                      S.length + C.length + 1 - P.length =
                        S.length + C.length - P.length + 1 := by omega
                  have hFuelRight :
                      S.length + 1 - P.length =
                        S.length - P.length + 1 := by omega
                  have hTail' := hTail
                  rw [dif_pos hTailLeft, dif_pos hTailRight] at hTail'
                  rw [hFuelLeft, hFuelRight]
                  simpa [P] using hTail'
                · have hTailLeftLen : P.length ≤ S.length + C.length := by
                    simpa [List.length_append] using hTailLeft
                  have hRightLen : P.length ≤ S.length + 1 := by
                    simpa using hRight
                  have hFuelLeft :
                      S.length + C.length + 1 - P.length =
                        S.length + C.length - P.length + 1 := by omega
                  have hFuelRightZero :
                      S.length + 1 - P.length = 0 := by omega
                  have hRightRec :
                      native_seq_indexof_rec S P (i + 1)
                          (S.length + 1 - P.length) =
                        -1 := by
                    rw [hFuelRightZero]
                    simp [native_seq_indexof_rec]
                  have hTail' := hTail
                  rw [dif_pos hTailLeft, dif_neg hTailRight] at hTail'
                  rw [hRightRec]
                  rw [hFuelLeft]
                  simpa [P] using hTail'
              · have hLeftLen : P.length ≤ S.length + C.length + 1 := by
                  simpa [List.length_append] using hLeft
                have hRightLen : P.length ≤ S.length + 1 := by
                  simpa using hRight
                have hTailLeftFalseLen : ¬ P.length ≤ S.length + C.length := by
                  intro hLen
                  exact hTailLeft (by simpa [List.length_append] using hLen)
                have hTailRightFalse : ¬ P.length ≤ S.length := by
                  intro hTailRight
                  exact hTailLeft (Nat.le_trans hTailRight (by simp))
                have hFuelLeftZero :
                    S.length + C.length + 1 - P.length = 0 := by omega
                have hFuelRightZero :
                    S.length + 1 - P.length = 0 := by omega
                rw [hFuelLeftZero, hFuelRightZero]
                simp [native_seq_indexof_rec]
          · rw [dif_pos hLeft, dif_neg hRight]
            by_cases hRec : native_seq_indexof_rec ((a :: S) ++ C) P i
                (((a :: S) ++ C).length - P.length + 1) = -1
            · exact hRec
            · exfalso
              have hContainsHay :
                  native_seq_contains ((a :: S) ++ C) P = true :=
                native_seq_contains_of_indexof_rec_ne_neg ((a :: S) ++ C) P i
                  (((a :: S) ++ C).length - P.length + 1) hRec
              have hContainsS :
                  native_seq_contains (a :: S) P = true :=
                native_seq_contains_drop_right_of_no_endpoint_overlap
                  (a :: S) C L D (by simpa [P] using hNo)
                  (by simpa [P] using hContainsHay)
              rcases native_seq_contains_decomp_exists (a :: S) P hContainsS with
                ⟨before, after, hEq⟩
              have hPatLe : P.length ≤ (a :: S).length := by
                rw [hEq]
                simp [List.length_append]
                omega
              exact hRight hPatLe
        · have hRightFalse : ¬ P.length ≤ (a :: S).length := by
            intro hRight
            exact hLeft (Nat.le_trans hRight (by simp))
          rw [dif_neg hLeft, dif_neg hRightFalse]
  rw [native_seq_indexof_eq_rec, native_seq_indexof_eq_rec]
  simp
  simpa [P] using hSearch S 0

theorem native_seq_indexof_le_len_sub_pat_of_pat_le_len
    (xs pat : List SmtValue) (i : native_Int) :
    pat.length ≤ xs.length →
      native_seq_indexof xs pat i ≤
        Int.ofNat xs.length - Int.ofNat pat.length := by
  intro hPatLe
  rw [native_seq_indexof_eq_rec]
  split
  · have hNonneg :
        (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
      exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
    exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg
  · dsimp
    split
    · rename_i hStart h
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          have hNonneg :
              (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
            exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
          exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          have hNat :
              Int.toNat i + j ≤ xs.length - pat.length := by
            omega
          calc
            Int.ofNat (Int.toNat i + j) ≤ Int.ofNat (xs.length - pat.length) :=
              Int.ofNat_le.mpr hNat
            _ = Int.ofNat xs.length - Int.ofNat pat.length :=
              Int.ofNat_sub hPatLe
    · have hNonneg :
          (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
        exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
      exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg

theorem native_seq_indexof_zero_nonneg_pat_le_len
    (xs pat : List SmtValue) :
    0 ≤ native_seq_indexof xs pat 0 →
      pat.length ≤ xs.length := by
  intro hIdx
  rw [native_seq_indexof_eq_rec] at hIdx
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add] at hIdx
  split at hIdx
  · assumption
  · have hContr : ¬ ((0 : Int) ≤ -1) := by decide
    exact False.elim (hContr hIdx)

theorem native_seq_indexof_zero_nonneg_toNat_add_pat_le_len
    (xs pat : List SmtValue) :
    0 ≤ native_seq_indexof xs pat 0 →
      Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤ xs.length := by
  intro hIdxNonneg
  have hPatLe : pat.length ≤ xs.length :=
    native_seq_indexof_zero_nonneg_pat_le_len xs pat hIdxNonneg
  have hIdxLe :=
    native_seq_indexof_le_len_sub_pat_of_pat_le_len xs pat 0 hPatLe
  rw [← Int.ofNat_le]
  have hAdd := Int.add_le_of_le_sub_right hIdxLe
  have hMax :
      max (native_seq_indexof xs pat 0) 0 =
        native_seq_indexof xs pat 0 :=
    Int.max_eq_left hIdxNonneg
  simpa [Int.ofNat_toNat, hMax] using hAdd

theorem native_seq_indexof_rec_offset
    (xs pat : List SmtValue) :
    ∀ (i off fuel : Nat),
      native_seq_indexof_rec xs pat (i + off) fuel =
        (let r := native_seq_indexof_rec xs pat i fuel
         if r = (-1 : Int) then (-1 : Int) else r + Int.ofNat off)
  | i, off, 0 => by
      simp [native_seq_indexof_rec]
  | i, off, fuel + 1 => by
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · unfold native_seq_indexof_rec
        rw [if_pos hPrefix, if_pos hPrefix]
        have hne : (Int.ofNat i : Int) ≠ -1 := by
          intro h
          have hNonneg : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
          omega
        rw [if_neg hne]
        simp
      · unfold native_seq_indexof_rec
        rw [if_neg hPrefix, if_neg hPrefix]
        cases xs with
        | nil =>
            simp
        | cons _ xs =>
            rw [show i + off + 1 = (i + 1) + off by omega]
            exact native_seq_indexof_rec_offset xs pat (i + 1) off fuel

theorem native_seq_prefix_eq_false_of_left_endpoint_no_overlap
    (C S D R : List SmtValue)
    (hNo : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D)
    (hC : C ≠ []) :
    native_seq_prefix_eq (D ++ R) (C ++ S) ≠ true := by
  intro hPrefix
  rw [native_seq_prefix_eq_iff] at hPrefix
  rcases hPrefix with ⟨after, hEq⟩
  have hCompatD : native_seq_compat C D :=
    native_seq_compat_of_append_eq C S D (R ++ after) (by
      rw [hEq]
      simp [List.append_assoc])
  have hLen : 0 < C.length := by
    cases C <;> simp at hC ⊢
  exact hNo 0 hLen hCompatD

theorem native_seq_indexof_rec_append_left_skip
    (C S D R : List SmtValue)
    (hNo : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D) :
    ∀ (i fuel : Nat),
      native_seq_indexof_rec (C ++ S) (D ++ R) i (C.length + fuel) =
        native_seq_indexof_rec S (D ++ R) (i + C.length) fuel := by
  induction C with
  | nil =>
      intro i fuel
      simp
  | cons a C ih =>
      intro i fuel
      have hNoTail : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D := by
        intro k hk
        simpa [List.drop_succ_cons] using hNo (k + 1) (by simp [hk])
      have hPrefix :
          native_seq_prefix_eq (D ++ R) ((a :: C) ++ S) ≠ true :=
        native_seq_prefix_eq_false_of_left_endpoint_no_overlap
          (a :: C) S D R hNo (by simp)
      conv =>
        lhs
        rw [show (a :: C).length + fuel = C.length + fuel + 1 by
          simp [Nat.add_assoc]
          omega]
        unfold native_seq_indexof_rec
      rw [if_neg hPrefix]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using ih hNoTail (i + 1) fuel

theorem native_seq_indexof_append_left_of_no_endpoint_overlap
    (C S D R : List SmtValue)
    (hNo : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D) :
    native_seq_indexof (C ++ S) (D ++ R) 0 =
      if native_seq_indexof S (D ++ R) 0 < 0 then
        (-1 : Int)
      else
        Int.ofNat (C.length + Int.toNat (native_seq_indexof S (D ++ R) 0)) := by
  let P := D ++ R
  by_cases hSneg : native_seq_indexof S P 0 < 0
  · have hSidx : native_seq_indexof S P 0 = -1 := by
      rcases native_seq_indexof_eq_neg_one_or_ge S P 0 with h | h
      · exact h
      · exact False.elim ((Int.not_lt.mpr h) hSneg)
    have hNoContains : native_seq_contains (C ++ S) P = false := by
      apply Bool.eq_false_iff.mpr
      intro hContains
      have hContainsS :
          native_seq_contains S P = true :=
        native_seq_contains_drop_left_of_no_endpoint_overlap C S D R hNo
          (by simpa [P] using hContains)
      have hSnonneg : 0 ≤ native_seq_indexof S P 0 := by
        unfold native_seq_contains at hContainsS
        exact of_decide_eq_true hContainsS
      rw [hSidx] at hSnonneg
      have hBad : ¬ (0 ≤ (-1 : Int)) := by decide
      exact False.elim (hBad hSnonneg)
    rw [if_pos hSneg]
    rcases native_seq_indexof_eq_neg_one_or_ge (C ++ S) P 0 with h | h
    · simpa [P] using h
    · exfalso
      have hContains : native_seq_contains (C ++ S) P = true := by
        unfold native_seq_contains
        exact decide_eq_true h
      rw [hNoContains] at hContains
      cases hContains
  · have hSnonneg : 0 ≤ native_seq_indexof S P 0 := Int.le_of_not_gt hSneg
    have hPatLe : P.length ≤ S.length :=
      native_seq_indexof_zero_nonneg_pat_le_len S P hSnonneg
    have hTotalLe : P.length ≤ (C ++ S).length := by
      simp [List.length_append]
      omega
    have hSidxRec :
        native_seq_indexof S P 0 =
          native_seq_indexof_rec S P 0 (S.length - P.length + 1) := by
      rw [native_seq_indexof_eq_rec]
      simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
      rw [dif_pos hPatLe]
      simp
    have hTotalIdxRec :
        native_seq_indexof (C ++ S) P 0 =
          native_seq_indexof_rec (C ++ S) P 0 ((C ++ S).length - P.length + 1) := by
      rw [native_seq_indexof_eq_rec]
      simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
      rw [dif_pos hTotalLe]
      simp
    rw [if_neg hSneg]
    rw [hTotalIdxRec]
    have hFuel :
        (C ++ S).length - P.length + 1 =
          C.length + (S.length - P.length + 1) := by
      rw [List.length_append]
      omega
    rw [hFuel]
    rw [native_seq_indexof_rec_append_left_skip C S D R hNo 0
      (S.length - P.length + 1)]
    rw [native_seq_indexof_rec_offset S P 0 C.length
      (S.length - P.length + 1)]
    have hRecNe :
        native_seq_indexof_rec S P 0 (S.length - P.length + 1) ≠ (-1 : Int) := by
      intro hRec
      rw [hSidxRec, hRec] at hSnonneg
      have hBad : ¬ (0 ≤ (-1 : Int)) := by decide
      exact False.elim (hBad hSnonneg)
    rw [if_neg hRecNe]
    have hCast :
        Int.ofNat (Int.toNat (native_seq_indexof S P 0)) =
          native_seq_indexof S P 0 :=
      Int.toNat_of_nonneg hSnonneg
    rw [hSidxRec] at hCast
    rw [← hCast]
    rw [hSidxRec]
    exact Int.add_comm _ _

theorem native_seq_replace_append_right_of_no_endpoint_overlap
    (S C L D repl : List SmtValue)
    (hNo : ∀ k, k < C.reverse.length →
      ¬ native_seq_compat (C.reverse.drop k) D.reverse) :
    native_seq_replace (S ++ C) (L ++ D) repl =
      native_seq_replace S (L ++ D) repl ++ C := by
  by_cases hPnil : L ++ D = []
  · have hCnil : C = [] := by
      cases hC : C with
      | nil => rfl
      | cons x xs =>
          exfalso
          have hLen : 0 < (x :: xs).reverse.length := by simp
          have hCompat :
              native_seq_compat ((x :: xs).reverse.drop 0) D.reverse := by
            have hDnil : D = [] := by
              have hParts : L = [] ∧ D = [] := by simpa using hPnil
              exact hParts.2
            subst D
            unfold native_seq_compat
            right
            simp [native_seq_prefix_eq]
          have hLenC : 0 < C.reverse.length := by simp [hC]
          have hCompatC :
              native_seq_compat (C.reverse.drop 0) D.reverse := by
            simpa [hC] using hCompat
          exact hNo 0 hLenC hCompatC
    subst C
    simp [StrEqReplSupport.native_seq_replace_eq_indexof, hPnil]
  · cases hPat : L ++ D with
    | nil => exact False.elim (hPnil hPat)
    | cons p ps =>
        have hIdx :
            native_seq_indexof (S ++ C) (L ++ D) 0 =
              native_seq_indexof S (L ++ D) 0 :=
            native_seq_indexof_append_right_of_no_endpoint_overlap S C L D hNo
        have hIdxPat :
            native_seq_indexof (S ++ C) (p :: ps) 0 =
              native_seq_indexof S (p :: ps) 0 := by
          simpa [hPat] using hIdx
        by_cases hNeg : native_seq_indexof S (L ++ D) 0 < 0
        · have hNegPat : native_seq_indexof S (p :: ps) 0 < 0 := by
            simpa [hPat] using hNeg
          simp [StrEqReplSupport.native_seq_replace_eq_indexof,
            hIdxPat, hNegPat]
        · have hNonneg : 0 ≤ native_seq_indexof S (L ++ D) 0 :=
            Int.le_of_not_gt hNeg
          have hBound :
              Int.toNat (native_seq_indexof S (L ++ D) 0) + (L ++ D).length ≤
                S.length :=
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len
              S (L ++ D) hNonneg
          have hBoundPat :
              Int.toNat (native_seq_indexof S (p :: ps) 0) + (p :: ps).length ≤
                S.length := by
            simpa [hPat] using hBound
          have hTake :
              Int.toNat (native_seq_indexof S (L ++ D) 0) ≤ S.length := by
            omega
          have hTakePat :
              Int.toNat (native_seq_indexof S (p :: ps) 0) ≤ S.length := by
            simpa [hPat] using hTake
          have hNegPat : ¬ native_seq_indexof S (p :: ps) 0 < 0 := by
            simpa [hPat] using hNeg
          have hBoundPs :
              Int.toNat (native_seq_indexof S (p :: ps) 0) +
                  (ps.length + 1) ≤ S.length := by
            simpa using hBoundPat
          simp [StrEqReplSupport.native_seq_replace_eq_indexof,
            hIdxPat, hNegPat]
          rw [List.take_append_of_le_length hTakePat]
          rw [List.drop_append_of_le_length hBoundPs]

theorem native_seq_replace_append_left_of_no_endpoint_overlap
    (C S D R repl : List SmtValue)
    (hNo : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D) :
    native_seq_replace (C ++ S) (D ++ R) repl =
      C ++ native_seq_replace S (D ++ R) repl := by
  by_cases hPnil : D ++ R = []
  · have hCnil : C = [] := by
      cases hC : C with
      | nil => rfl
      | cons x xs =>
          exfalso
          have hLen : 0 < (x :: xs).length := by simp
          have hCompat : native_seq_compat ((x :: xs).drop 0) D := by
            have hDnil : D = [] := by
              have hParts : D = [] ∧ R = [] := by simpa using hPnil
              exact hParts.1
            subst D
            unfold native_seq_compat
            right
            simp [native_seq_prefix_eq]
          have hLenC : 0 < C.length := by simp [hC]
          have hCompatC : native_seq_compat (C.drop 0) D := by
            simpa [hC] using hCompat
          exact hNo 0 hLenC hCompatC
    subst C
    simp [StrEqReplSupport.native_seq_replace_eq_indexof, hPnil]
  · cases hPat : D ++ R with
    | nil => exact False.elim (hPnil hPat)
    | cons p ps =>
        have hIdx :=
          native_seq_indexof_append_left_of_no_endpoint_overlap C S D R hNo
        by_cases hNeg : native_seq_indexof S (D ++ R) 0 < 0
        · have hIdxNeg :
              native_seq_indexof (C ++ S) (D ++ R) 0 = -1 := by
            simpa [hNeg] using hIdx
          have hIdxNegPat :
              native_seq_indexof (C ++ S) (p :: ps) 0 = -1 := by
            simpa [hPat] using hIdxNeg
          have hNegPat : native_seq_indexof S (p :: ps) 0 < 0 := by
            simpa [hPat] using hNeg
          simp [StrEqReplSupport.native_seq_replace_eq_indexof,
            hIdxNegPat, hNegPat]
        · have hSnonneg : 0 ≤ native_seq_indexof S (D ++ R) 0 :=
            Int.le_of_not_gt hNeg
          have hIdxOffset :
              native_seq_indexof (C ++ S) (D ++ R) 0 =
                Int.ofNat
                  (C.length + Int.toNat (native_seq_indexof S (D ++ R) 0)) := by
            simpa [hNeg] using hIdx
          have hBound :
              Int.toNat (native_seq_indexof S (D ++ R) 0) + (D ++ R).length ≤
                S.length :=
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len
              S (D ++ R) hSnonneg
          have hBoundPat :
              Int.toNat (native_seq_indexof S (p :: ps) 0) + (p :: ps).length ≤
                S.length := by
            simpa [hPat] using hBound
          have hTake :
              Int.toNat (native_seq_indexof S (D ++ R) 0) ≤ S.length := by
            omega
          have hTakePat :
              Int.toNat (native_seq_indexof S (p :: ps) 0) ≤ S.length := by
            simpa [hPat] using hTake
          have hIdxOffsetPat :
              native_seq_indexof (C ++ S) (p :: ps) 0 =
                Int.ofNat
                  (C.length + Int.toNat (native_seq_indexof S (p :: ps) 0)) := by
            simpa [hPat] using hIdxOffset
          have hNegPat : ¬ native_seq_indexof S (p :: ps) 0 < 0 := by
            simpa [hPat] using hNeg
          have hTotalNonneg :
              ¬ Int.ofNat
                (C.length + Int.toNat (native_seq_indexof S (p :: ps) 0)) < 0 := by
            exact Int.not_lt_of_ge (Int.natCast_nonneg _)
          have hToNatCast :
              Int.toNat
                  (Int.ofNat
                    (C.length + Int.toNat (native_seq_indexof S (p :: ps) 0))) =
                C.length + Int.toNat (native_seq_indexof S (p :: ps) 0) := by
            simpa [Int.ofNat_eq_natCast] using
              Int.toNat_natCast
                (C.length + Int.toNat (native_seq_indexof S (p :: ps) 0))
          simp only [StrEqReplSupport.native_seq_replace_eq_indexof]
          rw [hIdxOffsetPat]
          rw [if_neg hTotalNonneg]
          rw [hToNatCast]
          rw [if_neg hNegPat]
          rw [List.take_append]
          rw [List.drop_append]
          have hDropC :
              List.drop
                  (C.length + Int.toNat (native_seq_indexof S (p :: ps) 0) +
                    (p :: ps).length) C = [] := by
            apply List.drop_eq_nil_of_le
            omega
          rw [hDropC]
          have hTakeC :
              List.take
                  (C.length + Int.toNat (native_seq_indexof S (p :: ps) 0)) C =
                C := by
            rw [List.take_of_length_le]
            omega
          rw [hTakeC]
          have hSubTake :
              C.length + Int.toNat (native_seq_indexof S (p :: ps) 0) -
                  C.length =
                Int.toNat (native_seq_indexof S (p :: ps) 0) := by
            omega
          have hSubDrop :
              C.length + Int.toNat (native_seq_indexof S (p :: ps) 0) +
                  (p :: ps).length - C.length =
                Int.toNat (native_seq_indexof S (p :: ps) 0) +
                  (p :: ps).length := by
            omega
          rw [hSubTake, hSubDrop]
          simp [List.append_assoc]

theorem native_seq_replace_endpoints_of_no_overlap
    (C1 S C2 D1 T D2 repl : List SmtValue)
    (hLeft : ∀ k, k < C1.length →
      ¬ native_seq_compat (C1.drop k) D1)
    (hRight : ∀ k, k < C2.reverse.length →
      ¬ native_seq_compat (C2.reverse.drop k) D2.reverse) :
    native_seq_replace (C1 ++ S ++ C2) (D1 ++ T ++ D2) repl =
      C1 ++ native_seq_replace S (D1 ++ T ++ D2) repl ++ C2 := by
  have hRightRepl :=
    native_seq_replace_append_right_of_no_endpoint_overlap
      (C1 ++ S) C2 (D1 ++ T) D2 repl hRight
  have hLeftRepl :=
    native_seq_replace_append_left_of_no_endpoint_overlap
      C1 S D1 (T ++ D2) repl hLeft
  calc
    native_seq_replace (C1 ++ S ++ C2) (D1 ++ T ++ D2) repl
        = native_seq_replace ((C1 ++ S) ++ C2) ((D1 ++ T) ++ D2) repl := by
            simp [List.append_assoc]
    _ = native_seq_replace (C1 ++ S) ((D1 ++ T) ++ D2) repl ++ C2 := by
            rw [hRightRepl]
    _ = (C1 ++ native_seq_replace S (D1 ++ (T ++ D2)) repl) ++ C2 := by
            rw [show ((D1 ++ T) ++ D2) = D1 ++ (T ++ D2) by
              simp [List.append_assoc]]
            exact congrArg (fun x => x ++ C2) hLeftRepl
    _ = C1 ++ native_seq_replace S (D1 ++ T ++ D2) repl ++ C2 := by
            simp [List.append_assoc]

/-- Model-evaluation form of the endpoint-overlap `replace` rule. -/
theorem overlap_endpoints_replace_eval (M : SmtModel)
    (c1 sw c2 emp d1 t d2 r : Term)
    (Sc1 Ss Sc2 Se Sd1 St Sd2 Sr : SmtSeq) (T : SmtType)
    (hc1 : __smtx_model_eval M (__eo_to_smt c1) = SmtValue.Seq Sc1)
    (hsw : __smtx_model_eval M (__eo_to_smt sw) = SmtValue.Seq Ss)
    (hc2 : __smtx_model_eval M (__eo_to_smt c2) = SmtValue.Seq Sc2)
    (hemp : __smtx_model_eval M (__eo_to_smt emp) = SmtValue.Seq Se)
    (hd1 : __smtx_model_eval M (__eo_to_smt d1) = SmtValue.Seq Sd1)
    (ht : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq St)
    (hd2 : __smtx_model_eval M (__eo_to_smt d2) = SmtValue.Seq Sd2)
    (hr : __smtx_model_eval M (__eo_to_smt r) = SmtValue.Seq Sr)
    (hempnil : native_unpack_seq Se = [])
    (hSc1Elem : __smtx_elem_typeof_seq_value Sc1 = T)
    (hSsElem : __smtx_elem_typeof_seq_value Ss = T)
    (hLeft : ∀ k, k < (native_unpack_seq Sc1).length →
      ¬ native_seq_compat ((native_unpack_seq Sc1).drop k)
        (native_unpack_seq Sd1))
      (hRight : ∀ k, k < (native_unpack_seq Sc2).reverse.length →
        ¬ native_seq_compat ((native_unpack_seq Sc2).reverse.drop k)
          (native_unpack_seq Sd2).reverse) :
      __smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))
            r)) =
        __smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) sw)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))
                r))
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp)))) := by
  let c2emp : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp
  let swc2emp : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) c2emp
  let hay : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1) swc2emp
  let d2emp : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp
  let td2emp : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) d2emp
  let needle : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1) td2emp
  let replSw : Term :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) sw)
      needle) r
  let rhsTail : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) replSw) c2emp
  let sD2E :=
    native_pack_seq (__smtx_elem_typeof_seq_value Sd2)
      (native_unpack_seq Sd2 ++ native_unpack_seq Se)
  have hsD2E :
      __smtx_model_eval M (__eo_to_smt d2emp) = SmtValue.Seq sD2E := by
    dsimp only [d2emp, sD2E]
    rw [strConcat_eval_eq M d2 emp Sd2 Se hd2 hemp]
  let sTD2E :=
    native_pack_seq (__smtx_elem_typeof_seq_value St)
      (native_unpack_seq St ++ native_unpack_seq sD2E)
  have hsTD2E :
      __smtx_model_eval M (__eo_to_smt td2emp) = SmtValue.Seq sTD2E := by
    dsimp only [td2emp, sTD2E]
    rw [strConcat_eval_eq M t d2emp St sD2E ht hsD2E]
  let sNeedle :=
    native_pack_seq (__smtx_elem_typeof_seq_value Sd1)
      (native_unpack_seq Sd1 ++ native_unpack_seq sTD2E)
  have hsNeedle :
      __smtx_model_eval M (__eo_to_smt needle) = SmtValue.Seq sNeedle := by
    dsimp only [needle, sNeedle]
    rw [strConcat_eval_eq M d1 td2emp Sd1 sTD2E hd1 hsTD2E]
  let sC2E :=
    native_pack_seq (__smtx_elem_typeof_seq_value Sc2)
      (native_unpack_seq Sc2 ++ native_unpack_seq Se)
  have hsC2E :
      __smtx_model_eval M (__eo_to_smt c2emp) = SmtValue.Seq sC2E := by
    dsimp only [c2emp, sC2E]
    rw [strConcat_eval_eq M c2 emp Sc2 Se hc2 hemp]
  let sSWC2E :=
    native_pack_seq (__smtx_elem_typeof_seq_value Ss)
      (native_unpack_seq Ss ++ native_unpack_seq sC2E)
  have hsSWC2E :
      __smtx_model_eval M (__eo_to_smt swc2emp) = SmtValue.Seq sSWC2E := by
    dsimp only [swc2emp, sSWC2E]
    rw [strConcat_eval_eq M sw c2emp Ss sC2E hsw hsC2E]
  let sHay :=
    native_pack_seq (__smtx_elem_typeof_seq_value Sc1)
      (native_unpack_seq Sc1 ++ native_unpack_seq sSWC2E)
  have hsHay :
      __smtx_model_eval M (__eo_to_smt hay) = SmtValue.Seq sHay := by
    dsimp only [hay, sHay]
    rw [strConcat_eval_eq M c1 swc2emp Sc1 sSWC2E hc1 hsSWC2E]
  let sRepl :=
    native_pack_seq (__smtx_elem_typeof_seq_value Ss)
      (native_seq_replace (native_unpack_seq Ss)
        (native_unpack_seq sNeedle) (native_unpack_seq Sr))
  have hsRepl :
      __smtx_model_eval M (__eo_to_smt replSw) = SmtValue.Seq sRepl := by
    dsimp [replSw, sRepl]
    rw [strReplace_eval_eq M sw needle r Ss sNeedle Sr hsw hsNeedle hr]
  let sRhsTail :=
    native_pack_seq (__smtx_elem_typeof_seq_value sRepl)
      (native_unpack_seq sRepl ++ native_unpack_seq sC2E)
  have hsRhsTail :
      __smtx_model_eval M (__eo_to_smt rhsTail) = SmtValue.Seq sRhsTail := by
    dsimp only [rhsTail, sRhsTail]
    rw [strConcat_eval_eq M replSw c2emp sRepl sC2E hsRepl hsC2E]
  let sRhs :=
    native_pack_seq (__smtx_elem_typeof_seq_value Sc1)
      (native_unpack_seq Sc1 ++ native_unpack_seq sRhsTail)
  have hsRhs :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
              rhsTail)) = SmtValue.Seq sRhs := by
    dsimp only [rhsTail, sRhs]
    rw [strConcat_eval_eq M c1 rhsTail Sc1 sRhsTail hc1 hsRhsTail]
  have hList :=
    native_seq_replace_endpoints_of_no_overlap
      (native_unpack_seq Sc1) (native_unpack_seq Ss) (native_unpack_seq Sc2)
      (native_unpack_seq Sd1) (native_unpack_seq St) (native_unpack_seq Sd2)
      (native_unpack_seq Sr) hLeft hRight
  have hList' :
      native_seq_replace
          (native_unpack_seq Sc1 ++
            (native_unpack_seq Ss ++ native_unpack_seq Sc2))
          (native_unpack_seq Sd1 ++
            (native_unpack_seq St ++ native_unpack_seq Sd2))
          (native_unpack_seq Sr) =
        native_unpack_seq Sc1 ++
          (native_seq_replace (native_unpack_seq Ss)
            (native_unpack_seq Sd1 ++
              (native_unpack_seq St ++ native_unpack_seq Sd2))
            (native_unpack_seq Sr) ++ native_unpack_seq Sc2) := by
    simpa [List.append_assoc] using hList
  change
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace)
              hay) needle) r)) =
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1) rhsTail))
  rw [strReplace_eval_eq M hay needle r sHay sNeedle Sr hsHay hsNeedle hr]
  rw [hsRhs]
  dsimp [sHay, sSWC2E, sC2E, sNeedle, sTD2E, sD2E, sRepl, sRhsTail, sRhs]
  simp [Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, hempnil, hList']

/-- Model-evaluation form of the endpoint-overlap `indexof` rule. -/
theorem overlap_endpoints_indexof_eval (M : SmtModel)
    (sw c emp t d : Term)
    (Ss Sc Se St Sd : SmtSeq)
    (hsw : __smtx_model_eval M (__eo_to_smt sw) = SmtValue.Seq Ss)
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hemp : __smtx_model_eval M (__eo_to_smt emp) = SmtValue.Seq Se)
    (ht : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq St)
    (hd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hempnil : native_unpack_seq Se = [])
    (hRight : ∀ k, k < (native_unpack_seq Sc).reverse.length →
      ¬ native_seq_compat ((native_unpack_seq Sc).reverse.drop k)
        (native_unpack_seq Sd).reverse) :
    __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) emp)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)))
          (Term.Numeral 0))) =
      __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) sw)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)))
          (Term.Numeral 0))) := by
  obtain ⟨sDE, hsDE, huDE⟩ :=
    strConcat_unpack_eval M d emp Sd Se hd hemp
  obtain ⟨sNeedle, hsNeedle, huNeedle⟩ :=
    strConcat_unpack_eval M t
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)
      St sDE ht hsDE
  obtain ⟨sCE, hsCE, huCE⟩ :=
    strConcat_unpack_eval M c emp Sc Se hc hemp
  obtain ⟨sHay, hsHay, huHay⟩ :=
    strConcat_unpack_eval M sw
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) emp)
      Ss sCE hsw hsCE
  rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) emp)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)))
          (Term.Numeral 0)) =
        SmtTerm.str_indexof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) emp)))
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)))
          (SmtTerm.Numeral 0) from rfl]
  rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) sw)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)))
          (Term.Numeral 0)) =
        SmtTerm.str_indexof (__eo_to_smt sw)
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)))
          (SmtTerm.Numeral 0) from rfl]
  simp only [__smtx_model_eval, hsHay, hsNeedle, hsw]
  simp [__smtx_model_eval_str_indexof]
  have hHay :
      native_unpack_seq sHay =
        native_unpack_seq Ss ++ native_unpack_seq Sc := by
    rw [huHay, huCE, hempnil]
    simp
  have hNeedle :
      native_unpack_seq sNeedle =
        native_unpack_seq St ++ native_unpack_seq Sd := by
    rw [huNeedle, huDE, hempnil]
    simp
  rw [hHay, hNeedle]
  exact native_seq_indexof_append_right_of_no_endpoint_overlap
    (native_unpack_seq Ss) (native_unpack_seq Sc)
    (native_unpack_seq St) (native_unpack_seq Sd) hRight

end RuleProofs
