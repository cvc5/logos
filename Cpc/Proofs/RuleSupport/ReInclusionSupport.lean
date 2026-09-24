module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import all Cpc.Proofs.RuleSupport.ReConcatStarSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.ReUnfoldNegSupport
import all Cpc.Proofs.RuleSupport.ReUnfoldNegSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def NativeIncludes (sup sub : SmtRegLan) : Prop :=
  ∀ str : native_String,
    native_string_valid str = true ->
      native_str_in_re str sub = true ->
        native_str_in_re str sup = true

private def NativePrefixClosed (r : SmtRegLan) : Prop :=
  ∀ pre suf : native_String,
    native_string_valid (pre ++ suf) = true ->
      native_str_in_re suf r = true ->
        native_str_in_re (pre ++ suf) r = true

theorem native_includes_refl (r : SmtRegLan) :
    NativeIncludes r r := by
  intro _str _hValid hMem
  exact hMem

theorem native_includes_trans {r s t : SmtRegLan}
    (hrs : NativeIncludes r s) (hst : NativeIncludes s t) :
    NativeIncludes r t := by
  intro str hValid hMem
  exact hrs str hValid (hst str hValid hMem)

theorem native_includes_of_smt_value_rel {r s : SmtRegLan}
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan s)) :
    NativeIncludes r s := by
  intro str hValid hMem
  rw [native_str_in_re_eq_model] at hMem ⊢
  rwa [smt_value_rel_reglan_valid_eq hRel hValid]

private theorem native_includes_congr
    {sup sub flatSup flatSub : SmtRegLan}
    (hSupRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatSup)
        (SmtValue.RegLan sup))
    (hSubRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatSub)
        (SmtValue.RegLan sub))
    (hFlat : NativeIncludes flatSup flatSub) :
    NativeIncludes sup sub := by
  have hSupToFlat : NativeIncludes sup flatSup :=
    native_includes_of_smt_value_rel
      (RuleProofs.smt_value_rel_symm _ _ hSupRel)
  have hFlatSub : NativeIncludes flatSub sub :=
    native_includes_of_smt_value_rel hSubRel
  exact native_includes_trans hSupToFlat
    (native_includes_trans hFlat hFlatSub)

theorem smt_value_rel_of_native_includes
    {r s : SmtRegLan}
    (hrs : NativeIncludes r s) (hsr : NativeIncludes s r) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str r,
    ← native_str_in_re_eq_model str s]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    exact hsr str hValid hMem
  · intro hMem
    exact hrs str hValid hMem

theorem native_includes_inter_left (r s : SmtRegLan) :
    NativeIncludes r (native_re_inter r s) := by
  intro str _hValid hMem
  rw [native_str_in_re_re_inter] at hMem
  simp only [Bool.and_eq_true] at hMem
  exact hMem.1

theorem native_includes_inter_right (r s : SmtRegLan) :
    NativeIncludes s (native_re_inter r s) := by
  intro str _hValid hMem
  rw [native_str_in_re_re_inter] at hMem
  simp only [Bool.and_eq_true] at hMem
  exact hMem.2

theorem native_includes_re_all (r : SmtRegLan) :
    NativeIncludes native_re_all r := by
  intro str hValid _hMem
  exact native_str_in_re_re_all str hValid

private theorem native_re_concat_right_empty (r : SmtRegLan) :
    native_re_concat r (native_str_to_re []) = r := by
  cases r <;> simp [native_re_concat, native_str_to_re, impl_native_re_of_list,
    ]

private theorem native_re_concat_left_empty (r : SmtRegLan) :
    native_re_concat (native_str_to_re []) r = r := by
  cases r <;> simp [native_re_concat, native_str_to_re, impl_native_re_of_list,
    ]

theorem native_includes_concat
    {r1 r2 s1 s2 : SmtRegLan}
    (h1 : NativeIncludes r1 s1) (h2 : NativeIncludes r2 s2) :
    NativeIncludes (native_re_concat r1 r2) (native_re_concat s1 s2) := by
  intro str hValid hMem
  have hListMem :
      nativeListInRe str (native_re_mk_concat s1 s2) = true := by
    have hsimpa := hMem
    try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
    exact hsimpa
  rcases (nativeListInRe_mk_concat_true_iff_exists_append str s1 s2).1 hListMem with
    ⟨xs1, xs2, hAppend, hLeft, hRight⟩
  have hValid1 : native_string_valid xs1 = true :=
    native_string_valid_append_left xs1 xs2 (by simpa [hAppend] using hValid)
  have hValid2 : native_string_valid xs2 = true :=
    native_string_valid_append_right xs1 xs2 (by simpa [hAppend] using hValid)
  have hLeft' : nativeListInRe xs1 r1 = true := by
    have hMemLeft : native_str_in_re xs1 s1 = true := by
      simpa [native_str_in_re, hValid1, nativeListInRe] using hLeft
    have hMemLeft' := h1 xs1 hValid1 hMemLeft
    simpa [native_str_in_re, hValid1, nativeListInRe] using hMemLeft'
  have hRight' : nativeListInRe xs2 r2 = true := by
    have hMemRight : native_str_in_re xs2 s2 = true := by
      simpa [native_str_in_re, hValid2, nativeListInRe] using hRight
    have hMemRight' := h2 xs2 hValid2 hMemRight
    simpa [native_str_in_re, hValid2, nativeListInRe] using hMemRight'
  have hConcat :
      nativeListInRe str (native_re_mk_concat r1 r2) = true :=
    (nativeListInRe_mk_concat_true_iff_exists_append str r1 r2).2
      ⟨xs1, xs2, hAppend, hLeft', hRight'⟩
  have hsimpa := hConcat
  try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
  exact hsimpa

private theorem native_includes_concat_left_of_prefix_closed
    {sup tail r : SmtRegLan}
    (hClosed : NativePrefixClosed sup)
    (hTail : NativeIncludes sup tail) :
    NativeIncludes sup (native_re_concat r tail) := by
  intro str hValid hMem
  have hListMem :
      nativeListInRe str (native_re_mk_concat r tail) = true := by
    have hsimpa := hMem
    try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
    exact hsimpa
  rcases (nativeListInRe_mk_concat_true_iff_exists_append str r tail).1
      hListMem with
    ⟨xs1, xs2, hAppend, hLeft, hRight⟩
  have hXs2Valid : native_string_valid xs2 = true :=
    native_string_valid_append_right xs1 xs2 (by simpa [hAppend] using hValid)
  have hTailMem : native_str_in_re xs2 tail = true := by
    simpa [native_str_in_re, hXs2Valid, nativeListInRe] using hRight
  have hSupXs2 : native_str_in_re xs2 sup = true :=
    hTail xs2 hXs2Valid hTailMem
  simpa [hAppend] using hClosed xs1 xs2 (by simpa [hAppend] using hValid)
    hSupXs2

private theorem native_prefix_closed_all_concat (tail : SmtRegLan) :
    NativePrefixClosed (native_re_concat native_re_all tail) := by
  intro pre suf hValid hMem
  have hSufValid : native_string_valid suf = true :=
    native_string_valid_append_right pre suf hValid
  have hListMem :
      nativeListInRe suf (native_re_mk_concat native_re_all tail) = true := by
    have hsimpa := hMem
    try simp [native_str_in_re, hSufValid, native_re_concat] at hsimpa ⊢
    exact hsimpa
  rcases (nativeListInRe_mk_concat_true_iff_exists_append suf
      native_re_all tail).1 hListMem with
    ⟨xs1, xs2, hAppend, hLeft, hRight⟩
  have hPrefixValid :
      native_string_valid (pre ++ xs1) = true := by
    have hAll : native_string_valid ((pre ++ xs1) ++ xs2) = true := by
      rw [List.append_assoc, hAppend]
      exact hValid
    exact native_string_valid_append_left (pre ++ xs1) xs2 hAll
  have hAllPrefix :
      nativeListInRe (pre ++ xs1) native_re_all = true := by
    apply nativeListInRe_re_all
    simpa [native_string_valid] using hPrefixValid
  have hConcat :
      nativeListInRe ((pre ++ xs1) ++ xs2)
          (native_re_mk_concat native_re_all tail) = true :=
    (nativeListInRe_mk_concat_true_iff_exists_append ((pre ++ xs1) ++ xs2)
      native_re_all tail).2
      ⟨pre ++ xs1, xs2, rfl, hAllPrefix, hRight⟩
  have hsimpa := hConcat
  try simp [native_str_in_re, hValid, native_re_concat, List.append_assoc, hAppend] at hsimpa ⊢
  exact hsimpa

private theorem native_includes_all_concat_tail (tail : SmtRegLan) :
    NativeIncludes (native_re_concat native_re_all tail) tail := by
  intro str hValid hMem
  have hEmptyValid : native_string_valid ([] : native_String) = true := by
    rfl
  have hEmptyAll : native_str_in_re ([] : native_String) native_re_all = true :=
    native_str_in_re_re_all [] hEmptyValid
  simpa using
    native_str_in_re_re_concat_intro ([] : native_String) str native_re_all
      tail hEmptyAll hMem

private theorem native_prefix_closed_allchar_concat
    {tail : SmtRegLan}
    (hTail : NativePrefixClosed tail) :
    NativePrefixClosed (native_re_concat native_re_allchar tail) := by
  intro pre suf hValid hMem
  cases pre with
  | nil =>
      simpa using hMem
  | cons c cs =>
      have hTailValidAll : native_string_valid (cs ++ suf) = true := by
        rcases native_string_valid_cons_parts (by simpa using hValid) with
          ⟨_hc, hRest⟩
        exact hRest
      have hSufValid : native_string_valid suf = true :=
        native_string_valid_append_right cs suf hTailValidAll
      have hListMem :
          nativeListInRe suf (native_re_mk_concat native_re_allchar tail) =
            true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hSufValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf
          native_re_allchar tail).1 hListMem with
        ⟨xs1, xs2, hAppend, hLeft, hRight⟩
      have hLeftParts := (nativeListInRe_allchar_true_iff xs1).1 hLeft
      have hTailMem : native_str_in_re xs2 tail = true := by
        have hXs2Valid : native_string_valid xs2 = true := by
          have hSufValid' : native_string_valid (xs1 ++ xs2) = true := by
            simpa [hAppend] using hSufValid
          exact native_string_valid_append_right xs1 xs2 hSufValid'
        simpa [native_str_in_re, hXs2Valid, nativeListInRe] using hRight
      have hTailClosed :
          native_str_in_re ((cs ++ xs1) ++ xs2) tail = true := by
        have hClosedValid : native_string_valid ((cs ++ xs1) ++ xs2) = true := by
          rw [List.append_assoc, hAppend]
          exact hTailValidAll
        exact hTail (cs ++ xs1) xs2 hClosedValid hTailMem
      have hcValid : native_char_valid c = true :=
        (native_string_valid_cons_parts (by simpa using hValid)).1
      have hAllchar :
          native_str_in_re [c] native_re_allchar = true := by
        have hValidOne : native_string_valid [c] = true := by
          change native_char_valid c && true = true
          simp [hcValid]
        have hList :
            nativeListInRe [c] native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff [c]).2 (by
            simp [hcValid])
        simpa [native_str_in_re, hValidOne, nativeListInRe] using hList
      have hConcatMem :=
        native_str_in_re_re_concat_intro [c] ((cs ++ xs1) ++ xs2)
          native_re_allchar tail hAllchar hTailClosed
      simpa [native_re_concat, List.append_assoc, hAppend] using hConcatMem

private theorem native_string_valid_cons_of_parts
    {c : native_Char} {cs : native_String}
    (hc : native_char_valid c = true)
    (hcs : native_string_valid cs = true) :
    native_string_valid (c :: cs) = true := by
  change (native_char_valid c && native_string_valid cs) = true
  simp [hc, hcs]

private theorem nativeListInRe_raw_star_once :
    (xs : List native_Char) -> (r : SmtRegLan) ->
      nativeListInRe xs r = true ->
        nativeListInRe xs (SmtRegLan.star r) = true
  | [], r, _hMem => by
      simp [nativeListInRe, native_re_nullable]
  | c :: cs, r, hMem => by
      have hDer : nativeListInRe cs (native_re_deriv c r) = true := by
        simpa [nativeListInRe] using hMem
      have hNil : nativeListInRe [] (SmtRegLan.star r) = true := by
        simp [nativeListInRe, native_re_nullable]
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
            true :=
        (nativeListInRe_mk_concat_true_iff_exists_append cs
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨cs, [], by simp, hDer, hNil⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat

private theorem nativeListInRe_mk_star_once
    (xs : List native_Char) (r : SmtRegLan)
    (hMem : nativeListInRe xs r = true) :
    nativeListInRe xs (native_re_mk_star r) = true := by
  cases r with
  | empty =>
      have hFalse := nativeListInRe_empty xs
      rw [hFalse] at hMem
      cases hMem
  | epsilon =>
      have hNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 hMem
      subst xs
      simp [native_re_mk_star, native_re_mult, nativeListInRe,
        native_re_nullable]
  | star r =>
      have hsimpa := hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | char c =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs (SmtRegLan.char c) hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | range lo hi =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs (SmtRegLan.range lo hi) hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | allchar =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs SmtRegLan.allchar hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | concat r s =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs (SmtRegLan.concat r s) hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | union r s =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs (SmtRegLan.union r s) hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | inter r s =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs (SmtRegLan.inter r s) hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa
  | comp r =>
      have hsimpa :=
        nativeListInRe_raw_star_once xs (SmtRegLan.comp r) hMem
      try simp [native_re_mk_star] at hsimpa ⊢
      exact hsimpa

private theorem nativeListInRe_raw_star_mono :
    (xs : List native_Char) -> (rSup rSub : SmtRegLan) ->
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys rSub = true ->
            nativeListInRe ys rSup = true) ->
      nativeListInRe xs (SmtRegLan.star rSub) = true ->
        nativeListInRe xs (native_re_mk_star rSup) = true
  | [], rSup, _rSub, _hValid, _hIncl, _hMem => by
      exact nativeListInRe_nil_mk_star rSup
  | c :: cs, rSup, rSub, hValid, hIncl, hMem => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c rSub)
                (SmtRegLan.star rSub)) = true := by
        simpa [nativeListInRe, native_re_deriv] using hMem
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c rSub) (SmtRegLan.star rSub)).1 hConcat with
        ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
      have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
        rw [hAppend]
        exact hcs
      have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
      have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
      have hChunkSub : nativeListInRe (c :: xs₁) rSub = true := by
        simpa [nativeListInRe] using hLeft
      have hChunkValid : native_string_valid (c :: xs₁) = true :=
        native_string_valid_cons_of_parts hc hValid₁
      have hChunkSup : nativeListInRe (c :: xs₁) rSup = true :=
        hIncl (c :: xs₁) hChunkValid hChunkSub
      have hChunkStar :
          nativeListInRe (c :: xs₁) (native_re_mk_star rSup) = true :=
        nativeListInRe_mk_star_once (c :: xs₁) rSup hChunkSup
      have hTailStar :
          nativeListInRe xs₂ (native_re_mk_star rSup) = true :=
        nativeListInRe_raw_star_mono xs₂ rSup rSub hValid₂ hIncl hRight
      have hJoin :
          nativeListInRe ((c :: xs₁) ++ xs₂) (native_re_mk_star rSup) = true :=
        nativeListInRe_mk_star_append (c :: xs₁) xs₂ rSup hChunkStar hTailStar
      simpa [hAppend] using hJoin
termination_by xs _ _ _ _ _ => xs.length
decreasing_by
  all_goals
    have hLenEq := congrArg List.length hAppend
    simp at hLenEq ⊢
    omega

private theorem nativeListInRe_mk_star_mono
    (xs : List native_Char) (rSup rSub : SmtRegLan)
    (hValid : native_string_valid xs = true)
    (hIncl :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys rSub = true ->
            nativeListInRe ys rSup = true)
    (hMem : nativeListInRe xs (native_re_mk_star rSub) = true) :
    nativeListInRe xs (native_re_mk_star rSup) = true := by
  cases rSub with
  | empty =>
      have hNil : xs = [] := by
        cases xs with
        | nil => rfl
        | cons c cs =>
            simp [native_re_mk_star, native_re_mult, nativeListInRe,
              native_re_deriv] at hMem
            rw [nativeListInRe_empty cs] at hMem
            cases hMem
      subst xs
      exact nativeListInRe_nil_mk_star rSup
  | epsilon =>
      have hNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 (by
        have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
      subst xs
      exact nativeListInRe_nil_mk_star rSup
  | star r =>
      have hAsSub : nativeListInRe xs (SmtRegLan.star r) = true := by
        have hsimpa := hMem
        try simp [native_re_mk_star] at hsimpa ⊢
        exact hsimpa
      exact nativeListInRe_mk_star_once xs rSup (hIncl xs hValid hAsSub)
  | char c =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.char c) hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
  | range lo hi =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.range lo hi) hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
  | allchar =>
      exact nativeListInRe_raw_star_mono xs rSup SmtRegLan.allchar hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
  | concat r s =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.concat r s) hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
  | union r s =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.union r s) hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
  | inter r s =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.inter r s) hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)
  | comp r =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.comp r) hValid
        hIncl (by have hsimpa := hMem; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa)

theorem native_includes_star_self (r : SmtRegLan) :
    NativeIncludes (native_re_mult r) r := by
  intro str hValid hMem
  have hList : nativeListInRe str r = true := by
    simpa [native_str_in_re, hValid, nativeListInRe] using hMem
  have hStar := nativeListInRe_mk_star_once str r hList
  have hsimpa := hStar
  try simp [native_str_in_re, hValid, native_re_mult] at hsimpa ⊢
  exact hsimpa

theorem native_includes_star_mono {rSup rSub : SmtRegLan}
    (hIncl : NativeIncludes rSup rSub) :
    NativeIncludes (native_re_mult rSup) (native_re_mult rSub) := by
  intro str hValid hMem
  have hList :
      nativeListInRe str (native_re_mk_star rSub) = true := by
    have hsimpa := hMem
    try simp [native_str_in_re, hValid, native_re_mult] at hsimpa ⊢
    exact hsimpa
  have hInclList :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys rSub = true ->
            nativeListInRe ys rSup = true := by
    intro ys hys hysMem
    have hNative : native_str_in_re ys rSub = true := by
      simpa [native_str_in_re, hys, nativeListInRe] using hysMem
    have hNative' := hIncl ys hys hNative
    simpa [native_str_in_re, hys, nativeListInRe] using hNative'
  have hStar := nativeListInRe_mk_star_mono str rSup rSub hValid hInclList hList
  have hsimpa := hStar
  try simp [native_str_in_re, hValid, native_re_mult] at hsimpa ⊢
  exact hsimpa

private theorem nativeListInRe_char_true_eq
    (xs : List native_Char) (c : native_Char)
    (hMem : nativeListInRe xs (SmtRegLan.char c) = true) :
    xs = [c] := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable] at hMem
  | cons d ds =>
      cases ds with
      | nil =>
          by_cases hd : native_char_valid d = true <;>
            by_cases hc : native_char_valid c = true <;>
            by_cases hdc : d = c <;>
            simp [nativeListInRe, native_re_deriv, native_re_nullable,
              hdc] at hMem
          all_goals
            subst d
            rfl
      | cons e es =>
          by_cases hd : native_char_valid d = true <;>
            by_cases hc : native_char_valid c = true <;>
            by_cases hdc : d = c <;>
            simp [nativeListInRe, native_re_deriv, hdc] at hMem
          all_goals
            rw [nativeListInRe_empty es] at hMem
            cases hMem

private theorem nativeListInRe_re_of_list_true_eq :
    (pat xs : List native_Char) ->
      nativeListInRe xs (impl_native_re_of_list pat) = true ->
        xs = pat
  | [], xs, hMem => by
      exact (nativeListInRe_epsilon_iff xs).1 (by
        simpa [impl_native_re_of_list] using hMem)
  | c :: pat, xs, hMem => by
      have hConcat :
          nativeListInRe xs
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list pat)) = true := by
        simpa [impl_native_re_of_list] using hMem
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (SmtRegLan.char c) (impl_native_re_of_list pat)).1 hConcat with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftEq : left = [c] :=
        nativeListInRe_char_true_eq left c hLeft
      have hRightEq : right = pat :=
        nativeListInRe_re_of_list_true_eq pat right hRight
      subst left
      subst right
      simpa using hAppend.symm

theorem native_str_in_re_str_to_re_eq
    {str pat : native_String}
    (hValid : native_string_valid str = true)
    (hMem : native_str_in_re str (native_str_to_re pat) = true) :
    str = pat := by
  have hList : nativeListInRe str (impl_native_re_of_list pat) = true := by
    simpa [native_str_in_re, hValid, native_str_to_re, nativeListInRe] using hMem
  exact nativeListInRe_re_of_list_true_eq pat str hList

private theorem nativeListInRe_char_self
    (c : native_Char) (hc : native_char_valid c = true) :
    nativeListInRe [c] (SmtRegLan.char c) = true := by
  simp [nativeListInRe, native_re_deriv, native_re_nullable]

private theorem nativeListInRe_re_of_list_self :
    ∀ pat : native_String,
      native_string_valid pat = true ->
        nativeListInRe pat (impl_native_re_of_list pat) = true
  | [], _ => by
      simp [impl_native_re_of_list, nativeListInRe, native_re_nullable]
  | c :: cs, hValid => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHead : nativeListInRe [c] (SmtRegLan.char c) = true :=
        nativeListInRe_char_self c hc
      have hTail : nativeListInRe cs (impl_native_re_of_list cs) = true :=
        nativeListInRe_re_of_list_self cs hcs
      have hConcat :
          nativeListInRe (c :: cs)
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list cs)) = true :=
        (nativeListInRe_mk_concat_true_iff_exists_append (c :: cs)
          (SmtRegLan.char c) (impl_native_re_of_list cs)).2
          ⟨[c], cs, rfl, hHead, hTail⟩
      simpa [impl_native_re_of_list] using hConcat

private theorem native_str_in_re_str_to_re_self
    (pat : native_String)
    (hValid : native_string_valid pat = true) :
    native_str_in_re pat (native_str_to_re pat) = true := by
  simpa [native_str_in_re, hValid, native_str_to_re, nativeListInRe] using
    nativeListInRe_re_of_list_self pat hValid

theorem smt_value_rel_str_to_re_append
    (xs ys : native_String) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat (native_str_to_re xs) (native_str_to_re ys)))
      (SmtValue.RegLan (native_str_to_re (xs ++ ys))) := by
  apply smt_value_rel_of_native_includes
  · intro str hValid hMem
    have hEq : str = xs ++ ys :=
      native_str_in_re_str_to_re_eq (pat := xs ++ ys) hValid (by
        simpa [impl_native_string_to_values, List.map_append] using hMem)
    subst str
    exact native_str_in_re_re_concat_intro xs ys
      (native_str_to_re xs) (native_str_to_re ys)
      (native_str_in_re_str_to_re_self xs
        (native_string_valid_append_left xs ys hValid))
      (native_str_in_re_str_to_re_self ys
        (native_string_valid_append_right xs ys hValid))
  · intro str hValid hMem
    have hListMem :
        nativeListInRe str
            (native_re_mk_concat (native_str_to_re xs)
              (native_str_to_re ys)) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append str
          (native_str_to_re xs) (native_str_to_re ys)).1 hListMem with
      ⟨left, right, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (left ++ right) = true := by
      rw [hAppend]
      exact hValid
    have hLeftValid := native_string_valid_append_left left right hAppendValid
    have hRightValid := native_string_valid_append_right left right hAppendValid
    have hLeftMem :
        native_str_in_re left (native_str_to_re xs) = true := by
      simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
    have hRightMem :
        native_str_in_re right (native_str_to_re ys) = true := by
      simpa [native_str_in_re, hRightValid, nativeListInRe] using hRight
    have hLeftEq : left = xs :=
      native_str_in_re_str_to_re_eq hLeftValid hLeftMem
    have hRightEq : right = ys :=
      native_str_in_re_str_to_re_eq hRightValid hRightMem
    subst left
    subst right
    subst str
    simpa [impl_native_string_to_values, List.map_append] using
      native_str_in_re_str_to_re_self (xs ++ ys) hValid

private theorem native_includes_range_singleton
    {loSup hiSup loSub hiSub : native_Char}
    (hLoSup : native_char_valid loSup = true)
    (hHiSup : native_char_valid hiSup = true)
    (hLoSub : native_char_valid loSub = true)
    (hHiSub : native_char_valid hiSub = true)
    (hLo : loSup ≤ loSub)
    (hHi : hiSub ≤ hiSup) :
    NativeIncludes
      (native_re_range [loSup] [hiSup])
      (native_re_range [loSub] [hiSub]) := by
  intro str hValid hMem
  cases str with
  | nil =>
      simp [native_re_range, native_str_in_re, hValid,
        nativeListInRe, native_re_nullable] at hMem
  | cons c rest =>
      rcases native_string_valid_cons_parts hValid with ⟨hc, hRestValid⟩
      cases rest with
      | nil =>
          have hBounds : loSub ≤ c ∧ c ≤ hiSub := by
            by_cases hb : loSub ≤ c ∧ c ≤ hiSub
            · exact hb
            · simp [native_re_range, native_str_in_re, hValid,
                nativeListInRe, native_re_deriv, native_re_nullable,
                native_re_elem_valid, impl_native_re_elem_le, hc, hLoSub,
                hHiSub, hb] at hMem
          have hSupBounds : loSup ≤ c ∧ c ≤ hiSup := by
            exact ⟨Nat.le_trans hLo hBounds.1, Nat.le_trans hBounds.2 hHi⟩
          simp [native_re_range, native_str_in_re, hValid,
            nativeListInRe, native_re_deriv, native_re_nullable, hc,
            native_re_elem_valid, impl_native_re_elem_le, hLoSup, hHiSup,
            hSupBounds.1, hSupBounds.2]
      | cons d ds =>
          by_cases hb : loSub ≤ c ∧ c ≤ hiSub
          · simp [native_re_range, native_str_in_re, hValid,
              nativeListInRe, native_re_deriv, native_re_elem_valid,
              impl_native_re_elem_le, nativeListInRe_empty, hc, hLoSub,
              hHiSub, hb] at hMem
          · simp [native_re_range, native_str_in_re, hValid,
              nativeListInRe, native_re_deriv, native_re_elem_valid,
              impl_native_re_elem_le, nativeListInRe_empty, hc, hLoSub,
              hHiSub, hb] at hMem

theorem native_str_in_re_re_none (str : native_String) :
    native_str_in_re str native_re_none = false := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, native_re_none, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_union
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · have hsimpa := nativeListInRe_mk_union str r s; (try simp [native_str_in_re, hValid, native_re_union] at hsimpa ⊢); exact hsimpa
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_includes_union_left (r s : SmtRegLan) :
    NativeIncludes (native_re_union r s) r := by
  intro str _hValid hMem
  rw [native_str_in_re_re_union]
  simp [hMem]

theorem native_includes_union_right (r s : SmtRegLan) :
    NativeIncludes (native_re_union r s) s := by
  intro str _hValid hMem
  rw [native_str_in_re_re_union]
  simp [hMem]

theorem smt_value_rel_re_inter_self_comp_all_none (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter r (native_re_inter (native_re_comp r) native_re_all)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_re_comp, native_str_in_re_re_all _ hValid,
    native_str_in_re_re_none]
  cases hMem : native_str_in_re str r <;> simp [hValid]

theorem smt_value_rel_re_inter_subset_comp_all_none
    (r1 r2 : SmtRegLan)
    (hSub : NativeIncludes r2 r1) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter r1 (native_re_inter (native_re_comp r2) native_re_all)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_re_comp, native_str_in_re_re_all _ hValid,
    native_str_in_re_re_none]
  cases hMem1 : native_str_in_re str r1
  · simp [hValid]
  · have hMem2 : native_str_in_re str r2 = true :=
      hSub str hValid hMem1
    simp [hValid, hMem2]

theorem smt_value_rel_re_union_self_comp_none_all (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union r (native_re_union (native_re_comp r) native_re_none)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_comp, native_str_in_re_re_none,
    native_str_in_re_re_all _ hValid]
  cases hMem : native_str_in_re str r <;> simp [hValid]

theorem smt_value_rel_re_union_subset_comp_none_all
    (r1 r2 : SmtRegLan)
    (hSub : NativeIncludes r1 r2) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union r1 (native_re_union (native_re_comp r2) native_re_none)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_comp, native_str_in_re_re_none,
    native_str_in_re_re_all _ hValid]
  cases hMem2 : native_str_in_re str r2
  · simp [hValid]
  · have hMem1 : native_str_in_re str r1 = true :=
      hSub str hValid hMem2
    simp [hValid, hMem1]

theorem smtx_model_eval_re_mult_allchar :
    __smtx_model_eval_re_mult (SmtValue.RegLan native_re_allchar) =
      SmtValue.RegLan native_re_all := by
  simp [__smtx_model_eval_re_mult, native_re_mult, native_re_allchar,
    native_re_all]

private theorem smtx_model_eval_sigma_star_concat_eps (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.re_mult)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) =
      SmtValue.RegLan native_re_all := by
  change __smtx_model_eval M
      (SmtTerm.re_mult
        (SmtTerm.re_concat SmtTerm.re_allchar
          (SmtTerm.str_to_re (SmtTerm.String [])))) =
    SmtValue.RegLan native_re_all
  simp [__smtx_model_eval, __smtx_model_eval_re_mult,
    __smtx_model_eval_re_concat, __smtx_model_eval_str_to_re,
    native_re_mult, native_re_concat,
    native_re_allchar, native_re_all, native_str_to_re, impl_native_re_of_list,
    ]

private theorem smtx_model_eval_re_empty_string (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      SmtValue.RegLan (native_str_to_re []) := by
  change __smtx_model_eval M
      (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtValue.RegLan (native_str_to_re [])
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
    ]

private theorem smtx_typeof_re_empty_string :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq, __smtx_typeof.eq_4]
  simp [native_string_valid, native_ite, native_Teq]

theorem smt_model_eval_reglan_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.RegLan) :
    ∃ r : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact reglan_value_canonical hEvalTy

private theorem eo_ite_true_result
    (c e : Term)
    (h : __eo_ite c (Term.Boolean true) e = Term.Boolean true) :
    c = Term.Boolean true ∨
      c = Term.Boolean false ∧ e = Term.Boolean true := by
  have hNe : __eo_ite c (Term.Boolean true) e ≠ Term.Stuck := by
    rw [h]
    decide
  rcases eo_ite_cases_of_ne_stuck c (Term.Boolean true) e hNe with hc | hc
  · exact Or.inl hc
  · exact Or.inr ⟨hc, by simpa [hc, eo_ite_false] using h⟩

private theorem eo_ite_false_else_true
    (c x : Term)
    (h : __eo_ite c x (Term.Boolean false) = Term.Boolean true) :
    c = Term.Boolean true ∧ x = Term.Boolean true := by
  have hNe : __eo_ite c x (Term.Boolean false) ≠ Term.Stuck := by
    rw [h]
    decide
  rcases eo_ite_cases_of_ne_stuck c x (Term.Boolean false) hNe with hc | hc
  · exact ⟨hc, by simpa [hc, eo_ite_true] using h⟩
  · simp [hc, eo_ite_false] at h

private theorem eo_and_eq_true
    (a b : Term)
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    try simp [__eo_and] at h
  case Boolean.Boolean x y =>
    simpa [__eo_and, SmtEval.native_and] using h
  case Binary.Binary w1 n1 w2 n2 =>
    simp [__eo_requires, native_ite, native_teq, native_not] at h
    split at h <;> cases h

private theorem eo_requires_true_parts
    (x y z : Term)
    (h : __eo_requires x y z = Term.Boolean true) :
    x = y ∧ z = Term.Boolean true := by
  have hNe : __eo_requires x y z ≠ Term.Stuck := by
    rw [h]
    decide
  have hxy := eo_requires_eq_of_ne_stuck x y z hNe
  have hres := eo_requires_eq_result_of_ne_stuck x y z hNe
  exact ⟨hxy, by simpa [hres] using h⟩

private theorem int_ge_of_eo_eq_or_gt_true
    (a b : native_Int)
    (h :
      __eo_ite (__eo_eq (Term.Numeral a) (Term.Numeral b))
          (Term.Boolean true)
          (__eo_gt (Term.Numeral a) (Term.Numeral b)) =
        Term.Boolean true) :
    b ≤ a := by
  rcases eo_ite_true_result (__eo_eq (Term.Numeral a) (Term.Numeral b))
      (__eo_gt (Term.Numeral a) (Term.Numeral b)) h with hEq | hElse
  · have hTerm := eq_of_eo_eq_true (Term.Numeral a) (Term.Numeral b) hEq
    cases hTerm
    exact Int.le_refl _
  · have hGt : __eo_gt (Term.Numeral a) (Term.Numeral b) =
        Term.Boolean true := hElse.2
    simp [__eo_gt, native_zlt] at hGt
    exact Int.le_of_lt hGt

private theorem native_includes_of_same_term_eval
    (M : SmtModel) (t : Term) (rv1 rv2 : SmtRegLan)
    (hEval1 : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv1)
    (hEval2 : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv2) :
    NativeIncludes rv1 rv2 := by
  rw [hEval1] at hEval2
  cases hEval2
  exact native_includes_refl rv1

private theorem eval_re_union_reglan
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
      SmtValue.RegLan (native_re_union ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_union ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_union, hA, hB]

private theorem eval_re_inter_reglan
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
      SmtValue.RegLan (native_re_inter ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_inter ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_inter, hA, hB]

private theorem eval_re_concat_reglan
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
      SmtValue.RegLan (native_re_concat ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_concat ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_concat, hA, hB]

private theorem eval_re_mult_reglan
    (M : SmtModel) (a : Term) (ra : SmtRegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a)) =
      SmtValue.RegLan (native_re_mult ra) := by
  change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt a)) =
    SmtValue.RegLan (native_re_mult ra)
  simp [__smtx_model_eval, __smtx_model_eval_re_mult, hA]

private theorem re_union_arg_types_of_reglan (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan at hTy
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt a) (__eo_to_smt b)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem re_inter_arg_types_of_reglan (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan at hTy
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
    (typeof_re_inter_eq (__eo_to_smt a) (__eo_to_smt b)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem re_concat_arg_types_of_reglan (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  exact RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_args_of_reglan
    a b hTy

private theorem re_mult_arg_type_of_reglan (a : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan := by
  exact RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan a hTy

private theorem str_to_re_arg_type_of_reglan (s : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
        SmtType.RegLan) :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan at hTy
  exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
    (typeof_str_to_re_eq (__eo_to_smt s)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem re_range_arg_types_of_reglan (lo hi : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) lo) hi)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt lo) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt hi) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof
      (SmtTerm.re_range (__eo_to_smt lo) (__eo_to_smt hi)) =
    SmtType.RegLan at hTy
  exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
    (typeof_re_range_eq (__eo_to_smt lo) (__eo_to_smt hi)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem seq_char_term_to_z_singleton
    (s : Term)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hNonneg : __eo_is_neg (__eo_to_z s) = Term.Boolean false) :
    ∃ c : native_Char,
      s = Term.String [c] ∧
        native_char_valid c = true ∧
        __eo_to_z s = Term.Numeral (Int.ofNat c) := by
  cases s with
  | Numeral n =>
      have hTo :
          __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n := rfl
      rw [hTo] at hTy
      rw [__smtx_typeof.eq_2] at hTy
      cases hTy
  | Rational q =>
      have hTo :
          __eo_to_smt (Term.Rational q) = SmtTerm.Rational q := rfl
      rw [hTo] at hTy
      rw [__smtx_typeof.eq_3] at hTy
      cases hTy
  | Binary w n =>
      have hTo :
          __eo_to_smt (Term.Binary w n) = SmtTerm.Binary w n := rfl
      rw [hTo] at hTy
      rw [__smtx_typeof.eq_5] at hTy
      cases hOk :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hOk] at hTy
  | String xs =>
    cases xs with
    | nil =>
        simp [__eo_to_z, __eo_is_neg, native_ite, native_zeq,
          native_str_len] at hNonneg
    | cons c rest =>
        cases rest with
        | nil =>
            have hStringValid :
                native_string_valid [c] = true :=
              native_string_valid_of_smtx_typeof_eo_string [c]
                (by simpa using hTy)
            have hc : native_char_valid c = true :=
              (native_string_valid_cons_parts hStringValid).1
            refine ⟨c, rfl, hc, ?_⟩
            simp [__eo_to_z, native_ite, native_zeq, native_str_len,
              native_str_to_code, hc]
        | cons d ds =>
            have hLenNe :
                ¬ (1 : native_Int) = (↑ds.length + 1 + 1 : native_Int) := by
              intro hEq
              have hEqNat : (1 : Nat) = ds.length + 1 + 1 := by
                exact_mod_cast hEq
              omega
            simp [__eo_to_z, __eo_is_neg, native_ite, native_zeq, native_str_len,
              hLenNe] at hNonneg
  | _ =>
      simp [__eo_to_z, __eo_is_neg] at hNonneg

private theorem native_includes_str_to_re_of_eval_side
    (M : SmtModel) (hM : model_wf M)
    (r : Term) (pat : native_String) (rv : SmtRegLan)
    (hSTy :
      __smtx_typeof (__eo_to_smt (Term.String pat)) =
        SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSide :
      __str_eval_str_in_re_rec
          (__str_flatten (__str_nary_intro (Term.String pat))) r =
        Term.Boolean true) :
    NativeIncludes rv (native_str_to_re pat) := by
  let side :=
    __str_eval_str_in_re_rec
      (__str_flatten (__str_nary_intro (Term.String pat))) r
  have hSideNe : side ≠ Term.Stuck := by
    dsimp [side]
    rw [hSide]
    decide
  have hEvalSide :=
    smtx_model_eval_str_in_re_eval_side M hM pat r side rv hSTy hRTy
      hREval rfl hSideNe
  have hPatMem : native_str_in_re pat rv = true := by
    dsimp [side] at hEvalSide
    rw [hSide] at hEvalSide
    rw [native_str_in_re_eq_model]
    simpa [__smtx_model_eval] using hEvalSide
  intro str hValid hMem
  have hEq : str = pat :=
    native_str_in_re_str_to_re_eq hValid hMem
  subst str
  exact hPatMem

private theorem native_includes_range_of_side
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s4 : Term) (rvSup rvSub : SmtRegLan)
    (hSupTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s1) s2)) =
        SmtType.RegLan)
    (hSubTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s4)) =
        SmtType.RegLan)
    (hSupEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s1) s2)) =
        SmtValue.RegLan rvSup)
    (hSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s4)) =
        SmtValue.RegLan rvSub)
    (hSide :
      (let _v0 := (__eo_to_z s1)
       let _v1 := (__eo_to_z s4)
       let _v2 := (__eo_to_z s2)
       let _v3 := (__eo_to_z s3)
       (__eo_requires (__eo_is_neg _v0) (Term.Boolean false)
        (__eo_requires (__eo_is_neg _v2) (Term.Boolean false)
        (__eo_requires (__eo_is_neg _v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg _v1) (Term.Boolean false)
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_ite (__eo_eq _v2 _v3) (Term.Boolean true)
                (__eo_gt _v2 _v3))
              (__eo_ite (__eo_eq _v3 _v0) (Term.Boolean true)
                (__eo_gt _v3 _v0)))
            (__eo_ite (__eo_eq _v2 _v1) (Term.Boolean true)
              (__eo_gt _v2 _v1)))
          (__eo_ite (__eo_eq _v1 _v0) (Term.Boolean true)
            (__eo_gt _v1 _v0)))))))) =
        Term.Boolean true) :
    NativeIncludes rvSup rvSub := by
  let v0 := __eo_to_z s1
  let v1 := __eo_to_z s4
  let v2 := __eo_to_z s2
  let v3 := __eo_to_z s3
  let core :=
    __eo_and
      (__eo_and
        (__eo_and
          (__eo_ite (__eo_eq v2 v3) (Term.Boolean true) (__eo_gt v2 v3))
          (__eo_ite (__eo_eq v3 v0) (Term.Boolean true) (__eo_gt v3 v0)))
        (__eo_ite (__eo_eq v2 v1) (Term.Boolean true) (__eo_gt v2 v1)))
      (__eo_ite (__eo_eq v1 v0) (Term.Boolean true) (__eo_gt v1 v0))
  have hSide' :
      __eo_requires (__eo_is_neg v0) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v2) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core))) =
        Term.Boolean true := by
    simpa [v0, v1, v2, v3, core] using hSide
  rcases eo_requires_true_parts (__eo_is_neg v0) (Term.Boolean false)
      (__eo_requires (__eo_is_neg v2) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core)))
      hSide' with ⟨hNeg0, hRest0⟩
  rcases eo_requires_true_parts (__eo_is_neg v2) (Term.Boolean false)
      (__eo_requires (__eo_is_neg v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core))
      hRest0 with ⟨hNeg2, hRest2⟩
  rcases eo_requires_true_parts (__eo_is_neg v3) (Term.Boolean false)
      (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core)
      hRest2 with ⟨hNeg3, hRest3⟩
  rcases eo_requires_true_parts (__eo_is_neg v1) (Term.Boolean false) core
      hRest3 with ⟨hNeg1, hCore⟩
  have hSupArgs := re_range_arg_types_of_reglan s1 s2 hSupTy
  have hSubArgs := re_range_arg_types_of_reglan s3 s4 hSubTy
  rcases seq_char_term_to_z_singleton s1 hSupArgs.1 (by
      simpa [v0] using hNeg0) with
    ⟨loSup, rfl, hLoSupValid, hToLoSup⟩
  rcases seq_char_term_to_z_singleton s2 hSupArgs.2 (by
      simpa [v2] using hNeg2) with
    ⟨hiSup, rfl, hHiSupValid, hToHiSup⟩
  rcases seq_char_term_to_z_singleton s3 hSubArgs.1 (by
      simpa [v3] using hNeg3) with
    ⟨loSub, rfl, hLoSubValid, hToLoSub⟩
  rcases seq_char_term_to_z_singleton s4 hSubArgs.2 (by
      simpa [v1] using hNeg1) with
    ⟨hiSub, rfl, hHiSubValid, hToHiSub⟩
  dsimp [core, v0, v1, v2, v3] at hCore
  simp [__eo_to_z, native_ite, native_zeq, native_str_len,
    native_str_to_code, hLoSupValid, hHiSupValid, hLoSubValid,
    hHiSubValid] at hCore
  rcases eo_and_eq_true _ _ hCore with ⟨hLeft3, _hHiSubLoSup⟩
  rcases eo_and_eq_true _ _ hLeft3 with ⟨hLeft2, hHiSupHiSubTerm⟩
  rcases eo_and_eq_true _ _ hLeft2 with
    ⟨_hHiSupLoSub, hLoSubLoSupTerm⟩
  have hLoInt :
      (Int.ofNat loSup : native_Int) ≤ Int.ofNat loSub :=
    int_ge_of_eo_eq_or_gt_true (Int.ofNat loSub) (Int.ofNat loSup)
      hLoSubLoSupTerm
  have hHiInt :
      (Int.ofNat hiSub : native_Int) ≤ Int.ofNat hiSup :=
    int_ge_of_eo_eq_or_gt_true (Int.ofNat hiSup) (Int.ofNat hiSub)
      hHiSupHiSubTerm
  have hLo : loSup ≤ loSub := by
    exact Int.ofNat_le.mp hLoInt
  have hHi : hiSub ≤ hiSup := by
    exact Int.ofNat_le.mp hHiInt
  change __smtx_model_eval M
      (SmtTerm.re_range (SmtTerm.String [loSup]) (SmtTerm.String [hiSup])) =
    SmtValue.RegLan rvSup at hSupEval
  simp [__smtx_model_eval, __smtx_model_eval_re_range,
    ] at hSupEval
  cases hSupEval
  change __smtx_model_eval M
      (SmtTerm.re_range (SmtTerm.String [loSub]) (SmtTerm.String [hiSub])) =
    SmtValue.RegLan rvSub at hSubEval
  simp [__smtx_model_eval, __smtx_model_eval_re_range,
    ] at hSubEval
  cases hSubEval
  exact native_includes_range_singleton hLoSupValid hHiSupValid hLoSubValid
    hHiSubValid hLo hHi

private theorem re_unbound_base_prefix_closed
    (M : SmtModel) (hM : model_wf M)
    (tail : Term) (rv : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.UOp UserOp.re_allchar))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))))
              tail)) =
        SmtType.RegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.UOp UserOp.re_allchar))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))))
              tail)) =
        SmtValue.RegLan rv) :
    NativePrefixClosed rv := by
  let sigmaStar :=
    Term.Apply (Term.UOp UserOp.re_mult)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.UOp UserOp.re_allchar))
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
  have hArgs := re_concat_arg_types_of_reglan sigmaStar tail (by
    simpa [sigmaStar] using hTy)
  rcases smt_model_eval_reglan_of_type M hM tail hArgs.2 with
    ⟨rtail, hTailEval⟩
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) sigmaStar)
              tail)) =
        SmtValue.RegLan (native_re_concat native_re_all rtail) :=
    eval_re_concat_reglan M sigmaStar tail native_re_all rtail
      (by simpa [sigmaStar] using smtx_model_eval_sigma_star_concat_eps M)
      hTailEval
  rw [show
      Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) sigmaStar) tail =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.UOp UserOp.re_allchar))
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])))))
          tail by rfl] at hFullEval
  rw [hFullEval] at hEval
  cases hEval
  exact native_prefix_closed_all_concat rtail

private theorem re_unbound_allchar_prefix_closed
    (M : SmtModel) (hM : model_wf M)
    (tail : Term) (rv rtail : SmtRegLan)
    (hTailEval :
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.RegLan rtail)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              tail)) =
        SmtValue.RegLan rv)
    (hTailClosed : NativePrefixClosed rtail) :
    NativePrefixClosed rv := by
  have hAllcharEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_allchar)) =
        SmtValue.RegLan native_re_allchar := by
    change __smtx_model_eval M SmtTerm.re_allchar =
      SmtValue.RegLan native_re_allchar
    rw [__smtx_model_eval.eq_104]
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              tail)) =
        SmtValue.RegLan (native_re_concat native_re_allchar rtail) :=
    eval_re_concat_reglan M (Term.UOp UserOp.re_allchar) tail
      native_re_allchar rtail hAllcharEval hTailEval
  rw [hFullEval] at hEval
  cases hEval
  exact native_prefix_closed_allchar_concat hTailClosed

private theorem re_is_unbound_wildcard_prefix_closed
    (M : SmtModel) (hM : model_wf M) :
    (t : Term) -> (rv : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv ->
      __re_is_unbound_wildcard t = Term.Boolean true ->
        NativePrefixClosed rv
  | t, rv, hTy, hEval, hWild => by
      cases t <;> try simp [__re_is_unbound_wildcard] at hWild
      case Apply f tail =>
        cases f <;> try simp [__re_is_unbound_wildcard] at hWild
        case Apply g left =>
          cases g <;> try simp [__re_is_unbound_wildcard] at hWild
          case UOp op =>
            cases op <;> try simp [__re_is_unbound_wildcard] at hWild
            case re_concat =>
              cases left <;> try simp [__re_is_unbound_wildcard] at hWild
              case UOp leftOp =>
                cases leftOp <;> try simp [__re_is_unbound_wildcard] at hWild
                case re_allchar =>
                  have hTailWild :
                      __re_is_unbound_wildcard tail = Term.Boolean true := by
                    simpa [__re_is_unbound_wildcard] using hWild
                  have hArgs :=
                    re_concat_arg_types_of_reglan
                      (Term.UOp UserOp.re_allchar) tail hTy
                  rcases smt_model_eval_reglan_of_type M hM tail hArgs.2 with
                    ⟨rtail, hTailEval⟩
                  exact
                    re_unbound_allchar_prefix_closed M hM tail rv rtail
                      hTailEval hEval
                      (re_is_unbound_wildcard_prefix_closed M hM tail rtail
                        hArgs.2 hTailEval hTailWild)
              case Apply lf lx =>
                cases lf <;> try simp [__re_is_unbound_wildcard] at hWild
                case UOp leftOp =>
                  cases leftOp <;> try simp [__re_is_unbound_wildcard] at hWild
                  case re_mult =>
                    cases lx <;> try simp [__re_is_unbound_wildcard] at hWild
                    case Apply sf sx =>
                      cases sf <;> try simp [__re_is_unbound_wildcard] at hWild
                      case Apply sg sy =>
                        cases sg <;> try simp [__re_is_unbound_wildcard] at hWild
                        case UOp sop =>
                          cases sop <;> try simp [__re_is_unbound_wildcard] at hWild
                          case re_concat =>
                            cases sy <;> try simp [__re_is_unbound_wildcard] at hWild
                            case UOp syop =>
                              cases syop <;> try simp [__re_is_unbound_wildcard] at hWild
                              case re_allchar =>
                                cases sx <;> try simp [__re_is_unbound_wildcard] at hWild
                                case Apply epsF epsX =>
                                  cases epsF <;> try simp [__re_is_unbound_wildcard] at hWild
                                  case UOp epsOp =>
                                    cases epsOp <;> try simp [__re_is_unbound_wildcard] at hWild
                                    case str_to_re =>
                                      cases epsX <;> try simp [__re_is_unbound_wildcard] at hWild
                                      case String xs =>
                                        cases xs <;> try simp [__re_is_unbound_wildcard] at hWild
                                        case nil =>
                                          exact re_unbound_base_prefix_closed M hM tail rv
                                            hTy hEval
termination_by t _ _ _ _ => sizeOf t

private theorem native_includes_concat_rhs_of_unbound
    (M : SmtModel) (hM : model_wf M)
    (lhs : Term) (rvLhs rvHead rvTail : SmtRegLan)
    (hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan)
    (hLhsEval :
      __smtx_model_eval M (__eo_to_smt lhs) = SmtValue.RegLan rvLhs)
    (hWild : __re_is_unbound_wildcard lhs = Term.Boolean true)
    (hTailIncl : NativeIncludes rvLhs rvTail) :
    NativeIncludes rvLhs (native_re_concat rvHead rvTail) := by
  exact native_includes_concat_left_of_prefix_closed
    (re_is_unbound_wildcard_prefix_closed M hM lhs rvLhs hLhsTy hLhsEval
      hWild)
    hTailIncl

private def ReIncludesCheckerSound
    (checker : Term -> Term -> Term)
    (M : SmtModel) (_hM : model_wf M)
    (sup sub : Term) : Prop :=
  ∀ (rvSup rvSub : SmtRegLan),
    __smtx_typeof (__eo_to_smt sup) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt sub) = SmtType.RegLan ->
    __smtx_model_eval M (__eo_to_smt sup) = SmtValue.RegLan rvSup ->
    __smtx_model_eval M (__eo_to_smt sub) = SmtValue.RegLan rvSub ->
    checker sup sub = Term.Boolean true ->
      NativeIncludes rvSup rvSub

private theorem str_re_includes_sound_mutual
    (M : SmtModel) (hM : model_wf M) :
    (∀ sup sub,
      ReIncludesCheckerSound __str_re_includes_lhs_union M hM sup sub) ∧
    (∀ sup sub,
      ReIncludesCheckerSound __str_re_includes_rec M hM sup sub) ∧
    (∀ sup sub,
      ReIncludesCheckerSound __str_re_includes_base_rec M hM sup sub) ∧
    (∀ sup sub,
      ReIncludesCheckerSound __str_re_includes_lhs_star M hM sup sub) ∧
    (∀ sup sub,
      ReIncludesCheckerSound __str_re_includes_rhs_inter M hM sup sub) := by
  refine __str_re_includes_lhs_union.mutual_induct
    (ReIncludesCheckerSound __str_re_includes_lhs_union M hM)
    (ReIncludesCheckerSound __str_re_includes_rec M hM)
    (ReIncludesCheckerSound __str_re_includes_base_rec M hM)
    (ReIncludesCheckerSound __str_re_includes_lhs_star M hM)
    (ReIncludesCheckerSound __str_re_includes_rhs_inter M hM)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · intro x rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp [__str_re_includes_lhs_union] at hSide
  · intro x _hNe rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp_all [__str_re_includes_lhs_union]
  · intro r1 r2 r3 _hR3Ne ihRec ihUnion
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hSide' :
        __eo_ite
            (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
              (__str_re_includes_rec r1 r3))
            (Term.Boolean true)
            (__str_re_includes_lhs_union r2 r3) =
          Term.Boolean true := by
      simpa [__str_re_includes_lhs_union] using hSide
    have hSupArgs := re_union_arg_types_of_reglan r1 r2 hSupTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArgs.1 with
      ⟨rv1, hR1Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r2 hSupArgs.2 with
      ⟨rv2, hR2Eval⟩
    have hUnionEval :=
      eval_re_union_reglan M r1 r2 rv1 rv2 hR1Eval hR2Eval
    rw [hUnionEval] at hSupEval
    cases hSupEval
    rcases eo_ite_true_result
        (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
          (__str_re_includes_rec r1 r3))
        (__str_re_includes_lhs_union r2 r3) hSide' with
      hFirst | hTail
    · have hFirstIncl :
          NativeIncludes rv1 rvSub := by
        rcases eo_ite_true_result (__eo_eq r1 r3)
            (__str_re_includes_rec r1 r3) hFirst with hEq | hRec
        · have hTerm := eq_of_eo_eq_true r1 r3 hEq
          subst r3
          exact native_includes_of_same_term_eval M r1 rv1 rvSub
            hR1Eval hSubEval
        · exact ihRec rv1 rvSub hSupArgs.1 hSubTy hR1Eval hSubEval
            hRec.2
      exact native_includes_trans (native_includes_union_left rv1 rv2)
        hFirstIncl
    · have hTailIncl :
          NativeIncludes rv2 rvSub :=
        ihUnion rv2 rvSub hSupArgs.2 hSubTy hR2Eval hSubEval
          hTail.2
      exact native_includes_trans (native_includes_union_right rv1 rv2)
        hTailIncl
  · intro r1 r3 _hR1Ne _hR3Ne _hNotUnion
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_lhs_union at hSide
    simp_all
  · intro x rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp [__str_re_includes_rec] at hSide
  · intro x _hNe rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp_all [__str_re_includes_rec]
  · intro r1 r3 ihBase
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hSide' :
        __eo_ite (__eo_eq r1 r3) (Term.Boolean true)
            (__str_re_includes_base_rec r1 r3) =
          Term.Boolean true := by
      simpa [__str_re_includes_rec] using hSide
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    have hSupArgs := re_concat_arg_types_of_reglan r1 eps hSupTy
    have hSubArgs := re_concat_arg_types_of_reglan r3 eps hSubTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArgs.1 with
      ⟨rv1, hR1Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r3 hSubArgs.1 with
      ⟨rv3, hR3Eval⟩
    have hEpsEval :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      dsimp [eps]
      exact smtx_model_eval_re_empty_string M
    have hSupFull :=
      eval_re_concat_reglan M r1 eps rv1 (native_str_to_re [])
        hR1Eval hEpsEval
    have hSubFull :=
      eval_re_concat_reglan M r3 eps rv3 (native_str_to_re [])
        hR3Eval hEpsEval
    rw [hSupFull] at hSupEval
    rw [hSubFull] at hSubEval
    cases hSupEval
    cases hSubEval
    have hHead : NativeIncludes rv1 rv3 := by
      rcases eo_ite_true_result (__eo_eq r1 r3)
          (__str_re_includes_base_rec r1 r3) hSide' with hEq | hRec
      · have hTerm := eq_of_eo_eq_true r1 r3 hEq
        subst r3
        exact native_includes_of_same_term_eval M r1 rv1 rv3
          hR1Eval hR3Eval
      · exact ihBase rv1 rv3 hSupArgs.1 hSubArgs.1 hR1Eval hR3Eval
          hRec.2
    exact native_includes_concat hHead
      (native_includes_refl (native_str_to_re []))
  · intro r1 r3 _hR3Ne _hR3NotEps ihBase
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hSide' :
        __eo_ite (__eo_eq r1 r3) (Term.Boolean true)
            (__str_re_includes_base_rec r1 r3) =
          Term.Boolean true := by
      simpa [__str_re_includes_rec] using hSide
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    have hSupArgs := re_concat_arg_types_of_reglan r1 eps hSupTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArgs.1 with
      ⟨rv1, hR1Eval⟩
    have hEpsEval :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      dsimp [eps]
      exact smtx_model_eval_re_empty_string M
    have hSupFull :=
      eval_re_concat_reglan M r1 eps rv1 (native_str_to_re [])
        hR1Eval hEpsEval
    rw [hSupFull] at hSupEval
    cases hSupEval
    have hHead : NativeIncludes rv1 rvSub := by
      rcases eo_ite_true_result (__eo_eq r1 r3)
          (__str_re_includes_base_rec r1 r3) hSide' with hEq | hRec
      · have hTerm := eq_of_eo_eq_true r1 r3 hEq
        subst r3
        exact native_includes_of_same_term_eval M r1 rv1 rvSub
          hR1Eval hSubEval
      · exact ihBase rv1 rvSub hSupArgs.1 hSubTy hR1Eval hSubEval
          hRec.2
    simpa [native_re_concat_right_empty] using hHead
  · intro r1 r3 _hR1Ne _hR1NotEps ihBase
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hSide' :
        __eo_ite (__eo_eq r1 r3) (Term.Boolean true)
            (__str_re_includes_base_rec r1 r3) =
          Term.Boolean true := by
      simpa [__str_re_includes_rec] using hSide
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    have hSubArgs := re_concat_arg_types_of_reglan r3 eps hSubTy
    rcases smt_model_eval_reglan_of_type M hM r3 hSubArgs.1 with
      ⟨rv3, hR3Eval⟩
    have hEpsEval :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      dsimp [eps]
      exact smtx_model_eval_re_empty_string M
    have hSubFull :=
      eval_re_concat_reglan M r3 eps rv3 (native_str_to_re [])
        hR3Eval hEpsEval
    rw [hSubFull] at hSubEval
    cases hSubEval
    have hHead : NativeIncludes rvSup rv3 := by
      rcases eo_ite_true_result (__eo_eq r1 r3)
          (__str_re_includes_base_rec r1 r3) hSide' with hEq | hRec
      · have hTerm := eq_of_eo_eq_true r1 r3 hEq
        subst r3
        exact native_includes_of_same_term_eval M r1 rvSup rv3
          hSupEval hR3Eval
      · exact ihBase rvSup rv3 hSupTy hSubArgs.1 hSupEval hR3Eval
          hRec.2
    simpa [native_re_concat_right_empty] using hHead
  · intro r1 r2 r3 r4 _hNoBothEps _hR2Ne _hR4Ne
      _v0 _v1 ihBase ihTail ihWild ihSigma
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_rec at hSide
    let lhs :=
      Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2
    let rhs :=
      Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r3) r4
    let sigma :=
      Term.Apply (Term.UOp UserOp.re_mult)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.UOp UserOp.re_allchar))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
    let eqTail := __eo_eq lhs r4
    have hSupArgs := re_concat_arg_types_of_reglan r1 r2 hSupTy
    have hSubArgs := re_concat_arg_types_of_reglan r3 r4 hSubTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArgs.1 with
      ⟨rv1, hR1Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r2 hSupArgs.2 with
      ⟨rv2, hR2Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r3 hSubArgs.1 with
      ⟨rv3, hR3Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r4 hSubArgs.2 with
      ⟨rv4, hR4Eval⟩
    have hLhsEval :
        __smtx_model_eval M (__eo_to_smt lhs) =
          SmtValue.RegLan (native_re_concat rv1 rv2) := by
      dsimp [lhs]
      exact eval_re_concat_reglan M r1 r2 rv1 rv2 hR1Eval hR2Eval
    have hRhsEval :
        __smtx_model_eval M (__eo_to_smt rhs) =
          SmtValue.RegLan (native_re_concat rv3 rv4) := by
      dsimp [rhs]
      exact eval_re_concat_reglan M r3 r4 rv3 rv4 hR3Eval hR4Eval
    rw [hLhsEval] at hSupEval
    rw [hRhsEval] at hSubEval
    cases hSupEval
    cases hSubEval
    have hSide' :
        __eo_ite
            (__eo_ite
              (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
                (__str_re_includes_base_rec r1 r3))
              (__eo_ite (__eo_eq r2 r4) (Term.Boolean true)
                (__str_re_includes_rec r2 r4))
              (Term.Boolean false))
            (Term.Boolean true)
            (__eo_ite
              (__eo_ite (__re_is_unbound_wildcard lhs)
                (__eo_ite eqTail (Term.Boolean true)
                  (__eo_ite eqTail (Term.Boolean true)
                    (__str_re_includes_rec lhs r4)))
                (Term.Boolean false))
              (Term.Boolean true)
              (__eo_ite
                (__eo_ite (__eo_eq r1 sigma)
                  (__eo_ite (__eo_eq r2 rhs) (Term.Boolean true)
                    (__str_re_includes_rec r2 rhs))
                  (Term.Boolean false))
                (Term.Boolean true) (Term.Boolean false))) =
          Term.Boolean true := by
      simpa [lhs, rhs, sigma, eqTail] using hSide
    rcases eo_ite_true_result
        (__eo_ite
          (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
            (__str_re_includes_base_rec r1 r3))
          (__eo_ite (__eo_eq r2 r4) (Term.Boolean true)
            (__str_re_includes_rec r2 r4))
          (Term.Boolean false))
        (__eo_ite
          (__eo_ite (__re_is_unbound_wildcard lhs)
            (__eo_ite eqTail (Term.Boolean true)
              (__eo_ite eqTail (Term.Boolean true)
                (__str_re_includes_rec lhs r4)))
            (Term.Boolean false))
          (Term.Boolean true)
          (__eo_ite
            (__eo_ite (__eo_eq r1 sigma)
              (__eo_ite (__eo_eq r2 rhs) (Term.Boolean true)
                (__str_re_includes_rec r2 rhs))
              (Term.Boolean false))
            (Term.Boolean true) (Term.Boolean false)))
        hSide' with hHeadTail | hFallback
    · rcases eo_ite_false_else_true
          (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
            (__str_re_includes_base_rec r1 r3))
          (__eo_ite (__eo_eq r2 r4) (Term.Boolean true)
            (__str_re_includes_rec r2 r4))
          hHeadTail with ⟨hHeadSide, hTailSide⟩
      have hHeadIncl :
          NativeIncludes rv1 rv3 := by
        rcases eo_ite_true_result (__eo_eq r1 r3)
            (__str_re_includes_base_rec r1 r3) hHeadSide with hEq | hRec
        · have hTerm := eq_of_eo_eq_true r1 r3 hEq
          subst r3
          exact native_includes_of_same_term_eval M r1 rv1 rv3
            hR1Eval hR3Eval
        · exact ihBase rv1 rv3 hSupArgs.1 hSubArgs.1 hR1Eval hR3Eval
            hRec.2
      have hTailIncl :
          NativeIncludes rv2 rv4 := by
        rcases eo_ite_true_result (__eo_eq r2 r4)
            (__str_re_includes_rec r2 r4) hTailSide with hEq | hRec
        · have hTerm := eq_of_eo_eq_true r2 r4 hEq
          subst r4
          exact native_includes_of_same_term_eval M r2 rv2 rv4
            hR2Eval hR4Eval
        · exact ihTail rv2 rv4 hSupArgs.2 hSubArgs.2 hR2Eval
            hR4Eval hRec.2
      exact native_includes_concat hHeadIncl hTailIncl
    · rcases eo_ite_true_result
          (__eo_ite (__re_is_unbound_wildcard lhs)
            (__eo_ite eqTail (Term.Boolean true)
              (__eo_ite eqTail (Term.Boolean true)
                (__str_re_includes_rec lhs r4)))
            (Term.Boolean false))
          (__eo_ite
            (__eo_ite (__eo_eq r1 sigma)
              (__eo_ite (__eo_eq r2 rhs) (Term.Boolean true)
                (__str_re_includes_rec r2 rhs))
              (Term.Boolean false))
            (Term.Boolean true) (Term.Boolean false))
          hFallback.2 with hWildBranch | hSigmaBranch
      · rcases eo_ite_false_else_true (__re_is_unbound_wildcard lhs)
            (__eo_ite eqTail (Term.Boolean true)
              (__eo_ite eqTail (Term.Boolean true)
                (__str_re_includes_rec lhs r4)))
            hWildBranch with ⟨hWild, hTailSide⟩
        have hTailIncl :
            NativeIncludes (native_re_concat rv1 rv2) rv4 := by
          rcases eo_ite_true_result eqTail
              (__eo_ite eqTail (Term.Boolean true)
                (__str_re_includes_rec lhs r4))
              hTailSide with hEq | hTailRec
          · have hTerm := eq_of_eo_eq_true lhs r4 hEq
            subst r4
            exact native_includes_of_same_term_eval M lhs
              (native_re_concat rv1 rv2) rv4 hLhsEval hR4Eval
          · rcases eo_ite_true_result eqTail
                (__str_re_includes_rec lhs r4) hTailRec.2 with
              hEq | hRec
            · have hTerm := eq_of_eo_eq_true lhs r4 hEq
              subst r4
              exact native_includes_of_same_term_eval M lhs
                (native_re_concat rv1 rv2) rv4 hLhsEval hR4Eval
            · exact ihWild (native_re_concat rv1 rv2) rv4 hSupTy
                hSubArgs.2 hLhsEval hR4Eval hRec.2
        exact native_includes_concat_rhs_of_unbound M hM lhs
          (native_re_concat rv1 rv2) rv3 rv4 hSupTy hLhsEval hWild
          hTailIncl
      · rcases eo_ite_false_else_true
            (__eo_ite (__eo_eq r1 sigma)
              (__eo_ite (__eo_eq r2 rhs) (Term.Boolean true)
                (__str_re_includes_rec r2 rhs))
              (Term.Boolean false))
            (Term.Boolean true) hSigmaBranch.2 with
          ⟨hSigmaCond, _hTrue⟩
        rcases eo_ite_false_else_true (__eo_eq r1 sigma)
            (__eo_ite (__eo_eq r2 rhs) (Term.Boolean true)
              (__str_re_includes_rec r2 rhs))
            hSigmaCond with ⟨hEqSigma, hTailSide⟩
        have hSigmaTerm := eq_of_eo_eq_true r1 sigma hEqSigma
        have hR1All : rv1 = native_re_all := by
          rw [← hSigmaTerm] at hR1Eval
          dsimp [sigma] at hR1Eval
          rw [smtx_model_eval_sigma_star_concat_eps M] at hR1Eval
          cases hR1Eval
          rfl
        subst rv1
        have hTailIncl :
            NativeIncludes rv2 (native_re_concat rv3 rv4) := by
          rcases eo_ite_true_result (__eo_eq r2 rhs)
              (__str_re_includes_rec r2 rhs) hTailSide with
            hEq | hRec
          · have hTerm := eq_of_eo_eq_true r2 rhs hEq
            rw [hTerm] at hRhsEval
            exact native_includes_of_same_term_eval M r2 rv2
              (native_re_concat rv3 rv4) hR2Eval hRhsEval
          · exact ihSigma rv2 (native_re_concat rv3 rv4) hSupArgs.2
              hSubTy hR2Eval hRhsEval hRec.2
        exact native_includes_trans (native_includes_all_concat_tail rv2)
          hTailIncl
  · intro r1 r2 _hR2Ne
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_rec at hSide
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let sigma :=
      Term.Apply (Term.UOp UserOp.re_mult)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.UOp UserOp.re_allchar))
          eps)
    have hSupArgs := re_concat_arg_types_of_reglan r1 r2 hSupTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArgs.1 with
      ⟨rv1, hR1Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r2 hSupArgs.2 with
      ⟨rv2, hR2Eval⟩
    have hSupFull :=
      eval_re_concat_reglan M r1 r2 rv1 rv2 hR1Eval hR2Eval
    have hSubEps :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      dsimp [eps]
      exact smtx_model_eval_re_empty_string M
    rw [hSubEps] at hSubEval
    rw [hSupFull] at hSupEval
    cases hSubEval
    cases hSupEval
    rcases eo_and_eq_true (__eo_eq r1 sigma) (__eo_eq r2 eps) (by
        simpa [sigma, eps] using hSide) with ⟨hEqSigma, hEqEps⟩
    have hSigmaTerm := eq_of_eo_eq_true r1 sigma hEqSigma
    have hEpsTerm := eq_of_eo_eq_true r2 eps hEqEps
    have hR1All : rv1 = native_re_all := by
      rw [← hSigmaTerm] at hR1Eval
      dsimp [sigma, eps] at hR1Eval
      rw [smtx_model_eval_sigma_star_concat_eps M] at hR1Eval
      cases hR1Eval
      rfl
    have hR2Eps : rv2 = native_str_to_re [] := by
      rw [← hEpsTerm] at hR2Eval
      dsimp [eps] at hR2Eval
      rw [smtx_model_eval_re_empty_string M] at hR2Eval
      cases hR2Eval
      rfl
    subst rv1
    subst rv2
    simpa [native_re_concat_right_empty] using
      native_includes_re_all (native_str_to_re [])
  · intro r1 r3 _hR1Ne _hR3Ne _hNoBothEps _hNoLhsEps
      _hNoRhsEps _hNoConcat _hNoConcatEps
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_rec at hSide
    simp_all
  · intro x rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp [__str_re_includes_base_rec] at hSide
  · intro x _hNe rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp_all [__str_re_includes_base_rec]
  · intro r1 s1 _hR1Ne
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hReqSide :
        __eo_requires (__eo_is_str s1) (Term.Boolean true)
            (__str_eval_str_in_re_rec
              (__str_flatten
                (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
              r1) =
          Term.Boolean true := by
      simpa [__str_re_includes_base_rec] using hSide
    rcases eo_requires_true_parts (__eo_is_str s1) (Term.Boolean true)
        (__str_eval_str_in_re_rec
          (__str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
          r1)
        hReqSide with ⟨hIsStr, hEvalSide⟩
    rcases eo_is_str_eq_true_cases s1 hIsStr with ⟨pat, rfl⟩
    have hSTy := str_to_re_arg_type_of_reglan (Term.String pat) hSubTy
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String pat)) =
      SmtValue.RegLan rvSub at hSubEval
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      ] at hSubEval
    cases hSubEval
    exact native_includes_str_to_re_of_eval_side M hM r1 pat rvSup
      hSTy hSupTy hSupEval hEvalSide
  · intro s1 r1 _hR1Ne _hNotStr
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp_all [__str_re_includes_base_rec]
  · intro s1 s2 s3 s4
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_base_rec at hSide
    exact native_includes_range_of_side M hM s1 s2 s3 s4 rvSup rvSub
      hSupTy hSubTy hSupEval hSubEval hSide
  · intro r1 r3 _hR1Ne _hR3Ne _hR3NotStr _hR1NotStr _hNotRange
      ihUnion ihInter ihStar
    intro rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hBaseSide :
        __eo_ite (__eo_eq (__str_re_includes_lhs_union r1 r3)
            (Term.Boolean true))
          (Term.Boolean true)
          (__eo_ite
            (__eo_eq (__str_re_includes_rhs_inter r1 r3)
              (Term.Boolean true))
            (Term.Boolean true)
            (__eo_ite
              (__eo_eq (__str_re_includes_lhs_star r1 r3)
                (Term.Boolean true))
              (Term.Boolean true) (Term.Boolean false))) =
          Term.Boolean true := by
      simpa [__str_re_includes_base_rec] using hSide
    rcases eo_ite_true_result
            (__eo_eq (__str_re_includes_lhs_union r1 r3)
              (Term.Boolean true))
            (__eo_ite
              (__eo_eq (__str_re_includes_rhs_inter r1 r3)
                (Term.Boolean true))
              (Term.Boolean true)
              (__eo_ite
                (__eo_eq (__str_re_includes_lhs_star r1 r3)
                  (Term.Boolean true))
                (Term.Boolean true) (Term.Boolean false)))
            hBaseSide with hUnionEq | hRest
    · have hUnion :
          __str_re_includes_lhs_union r1 r3 = Term.Boolean true := by
        exact (eq_of_eo_eq_true
          (__str_re_includes_lhs_union r1 r3) (Term.Boolean true)
          hUnionEq).symm
      exact ihUnion rvSup rvSub hSupTy hSubTy hSupEval hSubEval hUnion
    · rcases eo_ite_true_result
              (__eo_eq (__str_re_includes_rhs_inter r1 r3)
                (Term.Boolean true))
              (__eo_ite
                (__eo_eq (__str_re_includes_lhs_star r1 r3)
                  (Term.Boolean true))
                (Term.Boolean true) (Term.Boolean false))
              hRest.2 with hInterEq | hStarRest
      · have hInter :
            __str_re_includes_rhs_inter r1 r3 = Term.Boolean true := by
          exact (eq_of_eo_eq_true
            (__str_re_includes_rhs_inter r1 r3) (Term.Boolean true)
            hInterEq).symm
        exact ihInter rvSup rvSub hSupTy hSubTy hSupEval hSubEval hInter
      · rcases eo_ite_false_else_true
                (__eo_eq (__str_re_includes_lhs_star r1 r3)
                  (Term.Boolean true))
                (Term.Boolean true) hStarRest.2 with ⟨hStarEq, _hTrue⟩
        have hStar :
            __str_re_includes_lhs_star r1 r3 = Term.Boolean true := by
          exact (eq_of_eo_eq_true
            (__str_re_includes_lhs_star r1 r3) (Term.Boolean true)
            hStarEq).symm
        exact ihStar rvSup rvSub hSupTy hSubTy hSupEval hSubEval hStar
  · intro x rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp [__str_re_includes_lhs_star] at hSide
  · intro x _hNe rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp_all [__str_re_includes_lhs_star]
  · intro r2 _hR2Ne rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    rw [smtx_model_eval_sigma_star_concat_eps M] at hSupEval
    cases hSupEval
    exact native_includes_re_all rvSub
  · intro r1 r2 _hR1NotSigma ihRec
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hStarSide :
        __eo_ite (__eo_eq r1 r2) (Term.Boolean true)
            (__str_re_includes_rec r1 r2) =
          Term.Boolean true := by
      simpa [__str_re_includes_lhs_star] using hSide
    have hSupArg := re_mult_arg_type_of_reglan r1 hSupTy
    have hSubArg := re_mult_arg_type_of_reglan r2 hSubTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArg with
      ⟨rv1, hR1Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r2 hSubArg with
      ⟨rv2, hR2Eval⟩
    have hSupFull := eval_re_mult_reglan M r1 rv1 hR1Eval
    have hSubFull := eval_re_mult_reglan M r2 rv2 hR2Eval
    rw [hSupFull] at hSupEval
    rw [hSubFull] at hSubEval
    cases hSupEval
    cases hSubEval
    have hBodyIncl :
        NativeIncludes rv1 rv2 := by
      rcases eo_ite_true_result (__eo_eq r1 r2)
          (__str_re_includes_rec r1 r2) hStarSide with hEq | hRec
      · have hTerm := eq_of_eo_eq_true r1 r2 hEq
        subst r2
        exact native_includes_of_same_term_eval M r1 rv1 rv2
          hR1Eval hR2Eval
      · exact ihRec rv1 rv2 hSupArg hSubArg hR1Eval hR2Eval hRec.2
    exact native_includes_star_mono hBodyIncl
  · intro r1 r2 _hR2Ne _hR1NotSigma _hR2NotMult ihRec
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hStarSide :
        __eo_ite (__eo_eq r1 r2) (Term.Boolean true)
            (__str_re_includes_rec r1 r2) =
          Term.Boolean true := by
      simpa [__str_re_includes_lhs_star] using hSide
    have hSupArg := re_mult_arg_type_of_reglan r1 hSupTy
    rcases smt_model_eval_reglan_of_type M hM r1 hSupArg with
      ⟨rv1, hR1Eval⟩
    have hSupFull := eval_re_mult_reglan M r1 rv1 hR1Eval
    rw [hSupFull] at hSupEval
    cases hSupEval
    have hBodyIncl :
        NativeIncludes rv1 rvSub := by
      rcases eo_ite_true_result (__eo_eq r1 r2)
          (__str_re_includes_rec r1 r2) hStarSide with hEq | hRec
      · have hTerm := eq_of_eo_eq_true r1 r2 hEq
        subst r2
        exact native_includes_of_same_term_eval M r1 rv1 rvSub
          hR1Eval hSubEval
      · exact ihRec rv1 rvSub hSupArg hSubTy hR1Eval hSubEval hRec.2
    exact native_includes_trans (native_includes_star_self rv1)
      hBodyIncl
  · intro r1 r2 _hR1Ne _hR2Ne _hNotSigma _hNotMultMult _hNotMult
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_lhs_star at hSide
    simp_all
  · intro x rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp [__str_re_includes_rhs_inter] at hSide
  · intro x _hNe rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    simp_all [__str_re_includes_rhs_inter]
  · intro r1 r3 r2 _hR1Ne ihRec ihInter
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    have hInterSide :
        __eo_ite
            (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
              (__str_re_includes_rec r1 r3))
            (Term.Boolean true)
            (__str_re_includes_rhs_inter r1 r2) =
          Term.Boolean true := by
      simpa [__str_re_includes_rhs_inter] using hSide
    have hSubArgs := re_inter_arg_types_of_reglan r3 r2 hSubTy
    rcases smt_model_eval_reglan_of_type M hM r3 hSubArgs.1 with
      ⟨rv3, hR3Eval⟩
    rcases smt_model_eval_reglan_of_type M hM r2 hSubArgs.2 with
      ⟨rv2, hR2Eval⟩
    have hInterEval :=
      eval_re_inter_reglan M r3 r2 rv3 rv2 hR3Eval hR2Eval
    rw [hInterEval] at hSubEval
    cases hSubEval
    rcases eo_ite_true_result
        (__eo_ite (__eo_eq r1 r3) (Term.Boolean true)
          (__str_re_includes_rec r1 r3))
        (__str_re_includes_rhs_inter r1 r2) hInterSide with
  hFirst | hTail
    · have hFirstIncl :
          NativeIncludes rvSup rv3 := by
        rcases eo_ite_true_result (__eo_eq r1 r3)
            (__str_re_includes_rec r1 r3) hFirst with hEq | hRec
        · have hTerm := eq_of_eo_eq_true r1 r3 hEq
          subst r3
          exact native_includes_of_same_term_eval M r1 rvSup rv3
            hSupEval hR3Eval
        · exact ihRec rvSup rv3 hSupTy hSubArgs.1 hSupEval
            hR3Eval hRec.2
      exact native_includes_trans hFirstIncl
        (native_includes_inter_left rv3 rv2)
    · have hTailIncl :
          NativeIncludes rvSup rv2 :=
        ihInter rvSup rv2 hSupTy hSubArgs.2 hSupEval hR2Eval
          hTail.2
      exact native_includes_trans hTailIncl
        (native_includes_inter_right rv3 rv2)
  · intro r1 r3 _hR1Ne _hR3Ne _hNotInter
      rvSup rvSub hSupTy hSubTy hSupEval hSubEval hSide
    unfold __str_re_includes_rhs_inter at hSide
    simp_all

private theorem str_re_includes_rec_sound
    (M : SmtModel) (hM : model_wf M) :
    (sup sub : Term) -> (rvSup rvSub : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt sup) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt sub) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt sup) = SmtValue.RegLan rvSup ->
      __smtx_model_eval M (__eo_to_smt sub) = SmtValue.RegLan rvSub ->
      __str_re_includes_rec sup sub = Term.Boolean true ->
        NativeIncludes rvSup rvSub
  | sup, sub, rvSup, rvSub, hSupTy, hSubTy, hSupEval, hSubEval, hSide =>
      (str_re_includes_sound_mutual M hM).2.1 sup sub rvSup rvSub hSupTy
        hSubTy hSupEval hSubEval hSide

private theorem smt_value_rel_re_concat_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat r s))
      (SmtValue.RegLan (native_re_concat r' s')) := by
  exact smt_value_rel_of_native_includes
    (native_includes_concat (native_includes_of_smt_value_rel hr)
      (native_includes_of_smt_value_rel hs))
    (native_includes_concat
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hr))
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hs)))

private theorem smt_value_rel_re_concat_assoc_local
    (r s t : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat (native_re_concat r s) t))
      (SmtValue.RegLan (native_re_concat r (native_re_concat s t))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  have hsimpa :=
    nativeListInRe_mk_concat_assoc str r s t
  try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
  exact hsimpa

private theorem smt_value_rel_re_mult_local
    {r r' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_mult r))
      (SmtValue.RegLan (native_re_mult r')) := by
  exact smt_value_rel_of_native_includes
    (native_includes_star_mono (native_includes_of_smt_value_rel hr))
    (native_includes_star_mono
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hr)))

private theorem smt_value_rel_re_union_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union r s))
      (SmtValue.RegLan (native_re_union r' s')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hrEq : native_str_in_re str r = native_str_in_re str r' := by
    rw [native_str_in_re_eq_model str r,
      native_str_in_re_eq_model str r']
    exact smt_value_rel_reglan_valid_eq hr hValid
  have hsEq : native_str_in_re str s = native_str_in_re str s' := by
    rw [native_str_in_re_eq_model str s,
      native_str_in_re_eq_model str s']
    exact smt_value_rel_reglan_valid_eq hs hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    hrEq, hsEq]

private theorem smt_value_rel_re_inter_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_inter r s))
      (SmtValue.RegLan (native_re_inter r' s')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hrEq : native_str_in_re str r = native_str_in_re str r' := by
    rw [native_str_in_re_eq_model str r,
      native_str_in_re_eq_model str r']
    exact smt_value_rel_reglan_valid_eq hr hValid
  have hsEq : native_str_in_re str s = native_str_in_re str s' := by
    rw [native_str_in_re_eq_model str s,
      native_str_in_re_eq_model str s']
    exact smt_value_rel_reglan_valid_eq hs hValid
  rw [← native_str_in_re_eq_model str _,
    ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    hrEq, hsEq]

private theorem smt_value_rel_str_to_re_of_seq_eq
    {sx sy : SmtSeq}
    (hEq : sx = sy) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_str_to_re (native_unpack_string sx)))
      (SmtValue.RegLan (native_str_to_re (native_unpack_string sy))) := by
  subst sy
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_str_to_re_of_seq_rel
    {sx sy : SmtSeq}
    (hRel : RuleProofs.smt_value_rel (SmtValue.Seq sx)
      (SmtValue.Seq sy)) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_str_to_re (native_unpack_string sx)))
      (SmtValue.RegLan (native_str_to_re (native_unpack_string sy))) := by
  have hSeq : RuleProofs.smt_seq_rel sx sy := by
    simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using hRel
  exact smt_value_rel_str_to_re_of_seq_eq
    ((RuleProofs.smt_seq_rel_iff_eq sx sy).1 hSeq)

private theorem eval_str_to_re_reglan
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) := by
  change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtValue.RegLan (native_str_to_re (native_unpack_string ss))
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hEval,
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTy]

private theorem smt_typeof_string_seq_char_of_valid
    (s : native_String) (hValid : native_string_valid s = true) :
    __smtx_typeof (__eo_to_smt (Term.String s)) =
      SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char
  rw [__smtx_typeof.eq_4]
  simp [hValid, native_ite]

private theorem string_seq_type_char
    (w : native_String) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String w)) =
      SmtType.Seq T) :
    T = SmtType.Char := by
  change __smtx_typeof (SmtTerm.String w) = SmtType.Seq T at hTy
  rw [__smtx_typeof.eq_4] at hTy
  cases hvalid : native_string_valid w
  · simp [hvalid, native_ite] at hTy
  · simp [hvalid, native_ite] at hTy
    exact hTy.symm

private theorem substrWord_full_is_list :
    ∀ w : native_String,
      __eo_is_list (Term.UOp UserOp.str_concat)
          (substrWord w 0 w.length) =
        Term.Boolean true
  | [] => by
      simp [substrWord, __eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        __eo_eq, native_teq, native_ite, SmtEval.native_not]
  | c :: cs => by
      rw [show (c :: cs).length = cs.length + 1 from rfl, substrWord,
        extractString_zero_cons,
        show (0 : native_Int) + 1 = 1 by simp, substrWord_cons_tail]
      exact eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) (Term.String [c])
        (substrWord cs 0 cs.length) (by decide)
        (substrWord_full_is_list cs)

private theorem substrWord_full_type
    (w : native_String) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String w)) =
      SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (substrWord w 0 w.length)) =
      SmtType.Seq T := by
  induction w with
  | nil =>
      simpa [substrWord] using hTy
  | cons c cs ih =>
      have hT : T = SmtType.Char := string_seq_type_char (c :: cs) T hTy
      have hValid : native_string_valid (c :: cs) = true := by
        rw [hT] at hTy
        exact native_string_valid_of_smtx_typeof_eo_string (c :: cs) hTy
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHeadTy :
          __smtx_typeof (__eo_to_smt (Term.String [c])) =
            SmtType.Seq T := by
        rw [hT]
        exact smt_typeof_string_seq_char_of_valid [c]
          (by simp [native_string_valid, hc])
      have hTailTy :
          __smtx_typeof (__eo_to_smt (substrWord cs 0 cs.length)) =
            SmtType.Seq T := by
        apply ih
        rw [hT]
        exact smt_typeof_string_seq_char_of_valid cs hcs
      rw [show (c :: cs).length = cs.length + 1 from rfl, substrWord,
        extractString_zero_cons,
        show (0 : native_Int) + 1 = 1 by simp, substrWord_cons_tail]
      exact smt_typeof_str_concat_of_seq (Term.String [c])
        (substrWord cs 0 cs.length) T hHeadTy hTailTy

private theorem eval_string_reglan_flatten_local
    (M : SmtModel) (w : native_String) :
    __smtx_model_eval M (__eo_to_smt (Term.String w)) =
      SmtValue.Seq (native_pack_string w) := by
  change __smtx_model_eval M (SmtTerm.String w) =
    SmtValue.Seq (native_pack_string w)
  simp [__smtx_model_eval]

private theorem substrWord_full_eval
    (M : SmtModel) :
    ∀ w : native_String,
      __smtx_model_eval M (__eo_to_smt (substrWord w 0 w.length)) =
        SmtValue.Seq (native_pack_string w)
  | [] => by
      simpa [substrWord] using eval_string_reglan_flatten_local M []
  | c :: cs => by
      rw [show (c :: cs).length = cs.length + 1 from rfl, substrWord,
        extractString_zero_cons,
        show (0 : native_Int) + 1 = 1 by simp, substrWord_cons_tail]
      rw [smtx_model_eval_str_concat_term_eq,
        eval_string_reglan_flatten_local M [c], substrWord_full_eval M cs]
      simp [__smtx_model_eval_str_concat, native_pack_string,
        native_seq_concat, Smtm.native_unpack_pack_seq, native_pack_seq,
        native_unpack_seq, __smtx_elem_typeof_seq_value]

private theorem smt_value_rel_substrWord_string
    (M : SmtModel) (w : native_String) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (substrWord w 0 w.length)))
      (__smtx_model_eval M (__eo_to_smt (Term.String w))) := by
  rw [substrWord_full_eval M w, eval_string_reglan_flatten_local M w]
  exact RuleProofs.smt_value_rel_refl _

private def reIncl_intRangeTerm : native_Int -> Nat -> Term
  | _start, 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | start, n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral start))
        (reIncl_intRangeTerm (start + 1) n)

private theorem reIncl_str_flatten_word_rec_range_eq_substrWord
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __str_flatten_word_rec (reIncl_intRangeTerm start n) (Term.String s) =
        substrWord s start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [reIncl_intRangeTerm, substrWord, __str_flatten_word_rec,
        __eo_extract, extractString]
      rw [reIncl_str_flatten_word_rec_range_eq_substrWord s n (start + 1)]
      simp [__eo_mk_apply, substrWord_ne_stuck]

private def reIncl_zeroIntListTerm : Nat -> Term
  | 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (reIncl_zeroIntListTerm n)

private theorem reIncl_zeroIntListTerm_ne_stuck :
    ∀ n, reIncl_zeroIntListTerm n ≠ Term.Stuck
  | 0 => by simp [reIncl_zeroIntListTerm]
  | _n + 1 => by simp [reIncl_zeroIntListTerm]

private theorem reIncl_eo_list_repeat_rec_zero_eq :
    ∀ n,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) n =
        reIncl_zeroIntListTerm n
  | 0 => by rfl
  | n + 1 => by
      simp [__eo_list_repeat_rec, reIncl_zeroIntListTerm,
        reIncl_eo_list_repeat_rec_zero_eq n, __eo_mk_apply,
        reIncl_zeroIntListTerm_ne_stuck]

private theorem reIncl_eo_list_repeat_zero_eq (n : Nat) :
    __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) (Term.Numeral (Int.ofNat n)) =
      reIncl_zeroIntListTerm n := by
  have hnot : native_zlt (↑n : native_Int) 0 = false := by
    simp [native_zlt]
  simp [__eo_list_repeat, native_ite, native_int_to_nat, hnot,
    reIncl_eo_list_repeat_rec_zero_eq]

private theorem reIncl_intRangeTerm_ne_stuck :
    ∀ n start, reIncl_intRangeTerm start n ≠ Term.Stuck
  | 0, _start => by simp [reIncl_intRangeTerm]
  | _n + 1, _start => by simp [reIncl_intRangeTerm]

private theorem reIncl_iota_zero_list_eq_range :
    ∀ (n : Nat) (start : native_Int),
      __iota_rec (reIncl_zeroIntListTerm n) (Term.Numeral start) =
        reIncl_intRangeTerm start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [reIncl_zeroIntListTerm, reIncl_intRangeTerm, __iota_rec,
        __eo_add, native_zplus]
      rw [reIncl_iota_zero_list_eq_range n (start + 1)]
      simp [__eo_mk_apply, reIncl_intRangeTerm_ne_stuck]

theorem str_flatten_concat_string_eq_local
    (s : native_String) (tail : Term) :
    __str_flatten (mkConcat (Term.String s) tail) =
      __eo_list_concat (Term.UOp UserOp.str_concat)
        (substrWord s 0 s.length) (__str_flatten tail) := by
  cases s with
  | nil =>
      change
        __eo_ite (__eo_is_str (Term.String []))
            (__eo_list_concat (Term.UOp UserOp.str_concat)
              (__str_flatten_word_rec
                (__eo_requires (__eo_is_neg (Term.Numeral 0))
                  (Term.Boolean false)
                  (__iota_rec
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0) (Term.Numeral 0))
                    (Term.Numeral 0)))
                (Term.String []))
              (__str_flatten tail))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String []))
              (__str_flatten tail)) =
          __eo_list_concat (Term.UOp UserOp.str_concat) (Term.String [])
            (__str_flatten tail)
      have hIsStr :
          __eo_is_str (Term.String []) = Term.Boolean true := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq, native_not,
          SmtEval.native_and]
      have hReqLen :
          __eo_requires (__eo_is_neg (Term.Numeral 0))
              (Term.Boolean false)
              (__iota_rec
                (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral 0) (Term.Numeral 0))
                (Term.Numeral 0)) =
            __iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0) (Term.Numeral 0))
              (Term.Numeral 0) := by
        rw [show __eo_is_neg (Term.Numeral 0) = Term.Boolean false by rfl]
        exact eo_requires_self_eq_of_ne_stuck (Term.Boolean false) _ (by simp)
      rw [hIsStr, eo_ite_true, hReqLen,
        show __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) (Term.Numeral 0) =
          reIncl_zeroIntListTerm 0 by
            simpa using reIncl_eo_list_repeat_zero_eq 0,
        reIncl_iota_zero_list_eq_range,
        reIncl_str_flatten_word_rec_range_eq_substrWord]
      simp [substrWord]
  | cons c cs =>
      change
        __eo_ite (__eo_is_str (Term.String (c :: cs)))
            (__eo_list_concat (Term.UOp UserOp.str_concat)
              (__str_flatten_word_rec
                (__eo_requires
                  (__eo_is_neg
                    (Term.Numeral (Int.ofNat (List.length cs + 1))))
                  (Term.Boolean false)
                  (__iota_rec
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0)
                      (Term.Numeral (Int.ofNat (List.length cs + 1))))
                    (Term.Numeral 0)))
                (Term.String (c :: cs)))
              (__str_flatten tail))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.String (c :: cs)))
              (__str_flatten tail)) =
          __eo_list_concat (Term.UOp UserOp.str_concat)
            (substrWord (c :: cs) 0 (List.length cs + 1))
            (__str_flatten tail)
      have hIsStr :
          __eo_is_str (Term.String (c :: cs)) = Term.Boolean true := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq, native_not,
          SmtEval.native_and]
      have hReqLen :
          __eo_requires
              (__eo_is_neg
                (Term.Numeral (Int.ofNat (List.length cs + 1))))
              (Term.Boolean false)
              (__iota_rec
                (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral 0)
                  (Term.Numeral (Int.ofNat (List.length cs + 1))))
                (Term.Numeral 0)) =
            __iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0)
                (Term.Numeral (Int.ofNat (List.length cs + 1))))
              (Term.Numeral 0) := by
        rw [show
            __eo_is_neg (Term.Numeral (Int.ofNat (List.length cs + 1))) =
              Term.Boolean false by
            change
              Term.Boolean (native_zlt (Int.ofNat (List.length cs + 1)) 0) =
                Term.Boolean false
            have hCountLen :
                native_zlt (Int.ofNat (List.length cs + 1)) 0 = false := by
              change decide ((Int.ofNat (List.length cs + 1) : Int) < 0) =
                false
              simp
              omega
            rw [hCountLen]]
        exact eo_requires_self_eq_of_ne_stuck (Term.Boolean false) _ (by simp)
      rw [hIsStr, eo_ite_true, hReqLen, reIncl_eo_list_repeat_zero_eq,
        reIncl_iota_zero_list_eq_range,
        reIncl_str_flatten_word_rec_range_eq_substrWord]

private theorem eo_is_str_false_of_not_string
    (t : Term) (ht : t ≠ Term.Stuck)
    (hNot : ¬ ∃ w : native_String, t = Term.String w) :
    __eo_is_str t = Term.Boolean false := by
  cases t <;>
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_not,
      SmtEval.native_and] at ht hNot ⊢

private theorem str_flatten_concat_nonstr_local
    (a rest : Term)
    (hNC : ∀ a1 a2 : Term, a = mkConcat a1 a2 → False)
    (ha : __eo_is_str a = Term.Boolean false)
    (hTail : __str_flatten rest ≠ Term.Stuck) :
    __str_flatten (mkConcat a rest) =
      mkConcat a (__str_flatten rest) := by
  rw [__str_flatten.eq_3 a rest hNC, ha, eo_ite_false]
  simp [__eo_mk_apply]

private theorem str_flatten_eq_default_of_not_str_concat_local
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_flatten x =
      __eo_requires x (__seq_empty (__eo_typeof x)) x := by
  cases x with
  | Stuck =>
      rfl
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · simp [__str_flatten, hop]
          | _ =>
              simp [__str_flatten]
      | _ =>
          simp [__str_flatten]
  | _ =>
      simp [__str_flatten]

private theorem str_flatten_default_eq_self_of_list_not_concat_seq
    (x : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hFlatNe : __str_flatten x ≠ Term.Stuck) :
    __str_flatten x = x := by
  rw [str_flatten_eq_default_of_not_str_concat_local x hNotConcat] at hFlatNe ⊢
  exact eo_requires_eq_result_of_ne_stuck x (__seq_empty (__eo_typeof x)) x
    hFlatNe

private theorem eo_requires_stuck_result_local (x y : Term) :
    __eo_requires x y Term.Stuck = Term.Stuck := by
  show (native_ite (native_teq x y)
      (native_ite (native_not (native_teq x Term.Stuck)) Term.Stuck
        Term.Stuck) Term.Stuck) = Term.Stuck
  cases native_teq x y with
  | false => rfl
  | true =>
      cases native_not (native_teq x Term.Stuck) with
      | false => rfl
      | true => rfl

private theorem eo_mk_apply_stuck_right_local (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  exact Classical.byContradiction
    (fun hNe => eo_mk_apply_arg_ne_stuck_of_ne_stuck f Term.Stuck hNe rfl)

private theorem eo_list_concat_str_stuck_right_local (a : Term) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a Term.Stuck =
      Term.Stuck := by
  show __eo_requires
      (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
      (__eo_requires
        (__eo_is_list (Term.UOp UserOp.str_concat) Term.Stuck)
        (Term.Boolean true)
        (__eo_list_concat_rec a Term.Stuck)) = Term.Stuck
  have hInner :
      __eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) Term.Stuck)
          (Term.Boolean true)
          (__eo_list_concat_rec a Term.Stuck) = Term.Stuck := rfl
  rw [hInner]
  exact eo_requires_stuck_result_local _ _

private theorem eo_ite_stuck_both_local (c : Term) :
    __eo_ite c Term.Stuck Term.Stuck = Term.Stuck := by
  show native_ite (native_teq c (Term.Boolean true)) Term.Stuck
      (native_ite (native_teq c (Term.Boolean false)) Term.Stuck
        Term.Stuck) = Term.Stuck
  cases native_teq c (Term.Boolean true) with
  | true => rfl
  | false =>
      cases native_teq c (Term.Boolean false) with
      | true => rfl
      | false => rfl

private theorem seq_empty_is_list_or_stuck_local (X : Term) :
    __seq_empty X = Term.Stuck ∨
      __eo_is_list (Term.UOp UserOp.str_concat) (__seq_empty X) =
        Term.Boolean true := by
  rw [__seq_empty.eq_def]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

private theorem str_flatten_ne_stuck_is_list_local :
    ∀ t : Term, __str_flatten t ≠ Term.Stuck ->
      __eo_is_list (Term.UOp UserOp.str_concat) t = Term.Boolean true := by
  intro t
  induction t using __str_flatten.induct with
  | case1 =>
      intro h
      simp [__str_flatten] at h
  | case2 a a2 b _ih1 ih2 =>
      intro h
      rw [__str_flatten.eq_2] at h
      have hNe0 :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a)
                    a2)))
              (Term.Boolean true)
              (__eo_requires
                (__eo_is_list (Term.UOp UserOp.str_concat)
                  (__str_flatten b))
                (Term.Boolean true)
                (__eo_list_concat_rec
                  (__str_flatten
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) a) a2))
                  (__str_flatten b))) ≠ Term.Stuck := h
      have hNe1 :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten b))
              (Term.Boolean true)
              (__eo_list_concat_rec
                (__str_flatten
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) a) a2))
                (__str_flatten b)) ≠ Term.Stuck := by
        rw [← eo_requires_eq_result_of_ne_stuck _ _ _ hNe0]
        exact hNe0
      have hFBList := eo_requires_eq_of_ne_stuck _ _ _ hNe1
      have hFBNe : __str_flatten b ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFBList
        simp [__eo_is_list] at hFBList
      exact eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) _ b (by decide) (ih2 hFBNe)
  | case3 t tail hNC ih =>
      intro h
      rw [__str_flatten.eq_3 t tail hNC] at h
      have hTailNe : __str_flatten tail ≠ Term.Stuck := by
        intro hBad
        apply h
        rw [hBad, eo_list_concat_str_stuck_right_local,
          eo_mk_apply_stuck_right_local]
        exact eo_ite_stuck_both_local _
      exact eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) t tail (by decide) (ih hTailNe)
  | case4 x hStuck hNS hNC =>
      intro h
      rw [__str_flatten.eq_4 x hStuck hNS hNC] at h
      have hEqT := eo_requires_eq_of_ne_stuck _ _ _ h
      rcases seq_empty_is_list_or_stuck_local (__eo_typeof x) with hS | hL
      · exact absurd (hEqT.trans hS) hStuck
      · rw [hEqT]
        exact hL

private theorem eo_list_concat_eq_rec_of_lists
    (a z : Term)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  have hzNe : z ≠ Term.Stuck := by
    intro hz
    subst z
    simp [__eo_is_list] at hListZ
  have hRecNe :
      __eo_list_concat_rec a z ≠ Term.Stuck :=
    eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
      a z hListA hzNe
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) =
    __eo_list_concat_rec a z
  rw [hListA, hListZ]
  simp [eo_requires_self_eq_of_ne_stuck]

private theorem smt_typeof_eo_list_concat_str_concat_of_seq
    (a z : Term) (T : SmtType)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
      SmtType.Seq T := by
  rw [eo_list_concat_eq_rec_of_lists a z hListA hListZ]
  exact smt_typeof_list_concat_rec_str_concat_of_seq a z T hListA haTy hzTy

private theorem eo_is_list_eo_list_concat_str_concat
    (a z : Term)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__eo_list_concat (Term.UOp UserOp.str_concat) a z) =
      Term.Boolean true := by
  rw [eo_list_concat_eq_rec_of_lists a z hListA hListZ]
  have hzNe : z ≠ Term.Stuck := by
    intro hz
    subst z
    simp [__eo_is_list] at hListZ
  exact eo_list_concat_rec_is_list_true_of_lists
    (Term.UOp UserOp.str_concat) a z hListA hListZ

private theorem smt_value_rel_eo_list_concat_str_concat
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (T : SmtType)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat a z))) := by
  rw [eo_list_concat_eq_rec_of_lists a z hListA hListZ]
  exact smt_value_rel_list_concat_rec_str_concat M hM a z T
    hListA haTy hzTy

private theorem str_flatten_list_eval_rel
    (M : SmtModel) (hM : model_wf M) :
    ∀ (parts : Term) (ss : SmtSeq) (T : SmtType),
      __eo_is_list (Term.UOp UserOp.str_concat) parts = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt parts) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt parts) = SmtValue.Seq ss ->
      __str_flatten parts ≠ Term.Stuck ->
      ∃ flatSs,
        __smtx_model_eval M (__eo_to_smt (__str_flatten parts)) =
          SmtValue.Seq flatSs ∧
        __smtx_typeof (__eo_to_smt (__str_flatten parts)) =
          SmtType.Seq T ∧
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_flatten parts) =
          Term.Boolean true ∧
        RuleProofs.smt_value_rel (SmtValue.Seq flatSs) (SmtValue.Seq ss) := by
  intro parts
  induction parts using __str_flatten.induct with
  | case1 =>
      intro ss T hList _hTy _hEval _hFlatNe
      simp [__eo_is_list] at hList
  | case2 a a2 b ih1 ih2 =>
      intro ss T hList hTy hEval hFlatNe
      have hFlatEq :
          __str_flatten
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) a) a2)) b) =
            __eo_list_concat (Term.UOp UserOp.str_concat)
              (__str_flatten
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) a) a2))
              (__str_flatten b) :=
        __str_flatten.eq_2 a a2 b
      rw [hFlatEq] at hFlatNe ⊢
      have hNe0 :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten (mkConcat a a2)))
              (Term.Boolean true)
              (__eo_requires
                (__eo_is_list (Term.UOp UserOp.str_concat)
                  (__str_flatten b))
                (Term.Boolean true)
                (__eo_list_concat_rec (__str_flatten (mkConcat a a2))
                  (__str_flatten b))) ≠ Term.Stuck := hFlatNe
      have hFAList := eo_requires_eq_of_ne_stuck _ _ _ hNe0
      have hNe1 :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten b))
              (Term.Boolean true)
              (__eo_list_concat_rec (__str_flatten (mkConcat a a2))
                (__str_flatten b)) ≠ Term.Stuck := by
        rw [← eo_requires_eq_result_of_ne_stuck _ _ _ hNe0]
        exact hNe0
      have hFBList := eo_requires_eq_of_ne_stuck _ _ _ hNe1
      have hFANe : __str_flatten (mkConcat a a2) ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFAList
        simp [__eo_is_list] at hFAList
      have hFBNe : __str_flatten b ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFBList
        simp [__eo_is_list] at hFBList
      have hHeadList := str_flatten_ne_stuck_is_list_local _ hFANe
      have hTailList := str_flatten_ne_stuck_is_list_local _ hFBNe
      have hArgs := str_concat_args_of_seq_type (mkConcat a a2) b T hTy
      have hHeadEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt (mkConcat a a2))) =
            SmtType.Seq T := by
        have hsimpa :=
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt (mkConcat a a2))
            (by
              unfold term_has_non_none_type
              rw [hArgs.1]
              simp)
        rw [hArgs.1] at hsimpa
        exact hsimpa
      have hTailEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt b)) =
            SmtType.Seq T := by
        simpa [hArgs.2] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt b)
            (by
              unfold term_has_non_none_type
              rw [hArgs.2]
              simp)
      rcases seq_value_canonical hHeadEvalTy with ⟨sHead, hHeadEval⟩
      rcases seq_value_canonical hTailEvalTy with ⟨sTail, hTailEval⟩
      have hPartsEvalCalc :
          __smtx_model_eval M
              (__eo_to_smt (mkConcat (mkConcat a a2) b)) =
            SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value sHead)
                (native_unpack_seq sHead ++ native_unpack_seq sTail)) := by
        rw [smtx_model_eval_str_concat_term_eq, hHeadEval, hTailEval]
        simp [__smtx_model_eval_str_concat, native_seq_concat]
      change __smtx_model_eval M
          (__eo_to_smt (mkConcat (mkConcat a a2) b)) =
        SmtValue.Seq ss at hEval
      rw [hPartsEvalCalc] at hEval
      cases hEval
      rcases ih1 sHead T hHeadList hArgs.1 hHeadEval hFANe with
        ⟨fA, hFAEval, hFATy, hFAListOut, hFARel⟩
      rcases ih2 sTail T hTailList hArgs.2 hTailEval hFBNe with
        ⟨fB, hFBEval, hFBTy, hFBListOut, hFBRel⟩
      have hFlatTy :=
        smt_typeof_eo_list_concat_str_concat_of_seq
          (__str_flatten (mkConcat a a2)) (__str_flatten b) T
          hFAList hFBList hFATy hFBTy
      have hFlatList :=
        eo_is_list_eo_list_concat_str_concat
          (__str_flatten (mkConcat a a2)) (__str_flatten b)
          hFAList hFBList
      have hFlatEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M
                (__eo_to_smt
                  (__eo_list_concat (Term.UOp UserOp.str_concat)
                    (__str_flatten (mkConcat a a2))
                    (__str_flatten b)))) =
            SmtType.Seq T := by
        simpa [hFlatTy] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt
              (__eo_list_concat (Term.UOp UserOp.str_concat)
                (__str_flatten (mkConcat a a2)) (__str_flatten b)))
            (by
              unfold term_has_non_none_type
              rw [hFlatTy]
              simp)
      rcases seq_value_canonical hFlatEvalTy with ⟨flatSs, hFlatEval⟩
      have hRel0 :=
        smt_value_rel_eo_list_concat_str_concat M hM
          (__str_flatten (mkConcat a a2)) (__str_flatten b) T
          hFAList hFBList hFATy hFBTy
      have hRelHead :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt (__str_flatten (mkConcat a a2))))
            (__smtx_model_eval M (__eo_to_smt (mkConcat a a2))) := by
        rw [hFAEval, hHeadEval]
        exact hFARel
      have hRelTail :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (__str_flatten b)))
            (__smtx_model_eval M (__eo_to_smt b)) := by
        simpa [hFBEval, hTailEval] using hFBRel
      have hRelL :=
        smt_value_rel_str_concat_left_congr M hM
          (__str_flatten (mkConcat a a2)) (mkConcat a a2)
          (__str_flatten b) T hFATy hArgs.1 hFBTy hRelHead
      have hRelR :=
        smt_value_rel_str_concat_right_congr M hM
          (mkConcat a a2) (__str_flatten b) b T
          hArgs.1 hFBTy hArgs.2 hRelTail
      refine ⟨flatSs, hFlatEval, hFlatTy, hFlatList, ?_⟩
      have hsimpa :=
        RuleProofs.smt_value_rel_trans _ _ _
          (RuleProofs.smt_value_rel_trans _ _ _ hRel0 hRelL) hRelR
      rw [hFlatEval, hPartsEvalCalc] at hsimpa
      exact hsimpa
  | case3 head tail hNC ih =>
      intro ss T hList hTy hEval hFlatNe
      have hArgs := str_concat_args_of_seq_type head tail T hTy
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          head tail hList
      have hHeadEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt head)) =
            SmtType.Seq T := by
        simpa [hArgs.1] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt head)
            (by
              unfold term_has_non_none_type
              rw [hArgs.1]
              simp)
      have hTailEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt tail)) =
            SmtType.Seq T := by
        simpa [hArgs.2] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt tail)
            (by
              unfold term_has_non_none_type
              rw [hArgs.2]
              simp)
      rcases seq_value_canonical hHeadEvalTy with ⟨sHead, hHeadEval⟩
      rcases seq_value_canonical hTailEvalTy with ⟨sTail, hTailEval⟩
      have hPartsEvalCalc :
          __smtx_model_eval M (__eo_to_smt (mkConcat head tail)) =
            SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value sHead)
                (native_unpack_seq sHead ++ native_unpack_seq sTail)) := by
        rw [smtx_model_eval_str_concat_term_eq, hHeadEval, hTailEval]
        simp [__smtx_model_eval_str_concat, native_seq_concat]
      change __smtx_model_eval M (__eo_to_smt (mkConcat head tail)) =
        SmtValue.Seq ss at hEval
      rw [hPartsEvalCalc] at hEval
      cases hEval
      have hHeadNe : head ≠ Term.Stuck := by
        intro hStuck
        have hHeadTy := hArgs.1
        rw [hStuck] at hHeadTy
        change __smtx_typeof SmtTerm.None = SmtType.Seq T at hHeadTy
        rw [TranslationProofs.smtx_typeof_none] at hHeadTy
        cases hHeadTy
      have hFlatTailNe : __str_flatten tail ≠ Term.Stuck := by
        by_cases hString : ∃ w : native_String, head = Term.String w
        · rcases hString with ⟨w, rfl⟩
          have hFlatEq :
              __str_flatten (mkConcat (Term.String w) tail) =
                __eo_list_concat (Term.UOp UserOp.str_concat)
                  (substrWord w 0 w.length) (__str_flatten tail) :=
            str_flatten_concat_string_eq_local w tail
          intro hTailStuck
          apply hFlatNe
          rw [hFlatEq, hTailStuck]
          simp [__eo_list_concat, __eo_is_list, __eo_requires, native_ite,
            native_teq, native_not]
        · have hStrFalse :
              __eo_is_str head = Term.Boolean false :=
            eo_is_str_false_of_not_string head hHeadNe hString
          have hFlatEq :
              __str_flatten (mkConcat head tail) =
                __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
                  (__str_flatten tail) := by
            rw [__str_flatten.eq_3 head tail hNC, hStrFalse, eo_ite_false]
          intro hTailStuck
          apply hFlatNe
          rw [hFlatEq, hTailStuck]
          simp [__eo_mk_apply]
      rcases ih sTail T hTailList hArgs.2 hTailEval hFlatTailNe with
        ⟨flatTail, hFlatTailEval, hFlatTailTy, hFlatTailList,
          hFlatTailRel⟩
      have hFlatTailRelEval :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (__str_flatten tail)))
            (__smtx_model_eval M (__eo_to_smt tail)) := by
        simpa [hFlatTailEval, hTailEval] using hFlatTailRel
      by_cases hString : ∃ w : native_String, head = Term.String w
      · rcases hString with ⟨w, rfl⟩
        let flatTerm :=
          __eo_list_concat (Term.UOp UserOp.str_concat)
            (substrWord w 0 w.length) (__str_flatten tail)
        have hFlatEq :
            __str_flatten (mkConcat (Term.String w) tail) = flatTerm := by
          simpa [flatTerm] using str_flatten_concat_string_eq_local w tail
        have hSubTy :
            __smtx_typeof (__eo_to_smt (substrWord w 0 w.length)) =
              SmtType.Seq T :=
          substrWord_full_type w T hArgs.1
        have hSubList :
            __eo_is_list (Term.UOp UserOp.str_concat)
                (substrWord w 0 w.length) =
              Term.Boolean true :=
          substrWord_full_is_list w
        have hFlatTy :
            __smtx_typeof (__eo_to_smt flatTerm) = SmtType.Seq T := by
          exact smt_typeof_eo_list_concat_str_concat_of_seq
            (substrWord w 0 w.length) (__str_flatten tail) T
            hSubList hFlatTailList hSubTy hFlatTailTy
        have hFlatList :
            __eo_is_list (Term.UOp UserOp.str_concat) flatTerm =
              Term.Boolean true := by
          exact eo_is_list_eo_list_concat_str_concat
            (substrWord w 0 w.length) (__str_flatten tail)
            hSubList hFlatTailList
        have hFlatEvalTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt flatTerm)) =
              SmtType.Seq T := by
          simpa [hFlatTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt flatTerm) (by
                unfold term_has_non_none_type
                rw [hFlatTy]
                simp)
        rcases seq_value_canonical hFlatEvalTy with
          ⟨flatSs, hFlatEval⟩
        have hListConcatRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt flatTerm))
              (__smtx_model_eval M
                (__eo_to_smt
                  (mkConcat (substrWord w 0 w.length)
                    (__str_flatten tail)))) := by
          exact smt_value_rel_eo_list_concat_str_concat M hM
            (substrWord w 0 w.length) (__str_flatten tail) T
            hSubList hFlatTailList hSubTy hFlatTailTy
        have hHeadRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt (substrWord w 0 w.length)))
              (__smtx_model_eval M (__eo_to_smt (Term.String w))) :=
          smt_value_rel_substrWord_string M w
        have hLeftRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (mkConcat (substrWord w 0 w.length)
                    (__str_flatten tail))))
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat (Term.String w)
                  (__str_flatten tail)))) :=
          smt_value_rel_str_concat_left_congr M hM
            (substrWord w 0 w.length) (Term.String w)
            (__str_flatten tail) T hSubTy hArgs.1 hFlatTailTy hHeadRel
        have hRightRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat (Term.String w)
                  (__str_flatten tail))))
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat (Term.String w) tail))) :=
          smt_value_rel_str_concat_right_congr M hM
            (Term.String w) (__str_flatten tail) tail T
            hArgs.1 hFlatTailTy hArgs.2 hFlatTailRelEval
        refine ⟨flatSs, ?_, ?_, ?_, ?_⟩
        · simpa [hFlatEq, flatTerm] using hFlatEval
        · simpa [hFlatEq, flatTerm] using hFlatTy
        · simpa [hFlatEq, flatTerm] using hFlatList
        · have hsimpa := RuleProofs.smt_value_rel_trans _ _ _ hListConcatRel (RuleProofs.smt_value_rel_trans _ _ _ hLeftRel hRightRel); rw [hFlatEval, hPartsEvalCalc] at hsimpa; exact hsimpa
      · have hStrFalse :
            __eo_is_str head = Term.Boolean false :=
          eo_is_str_false_of_not_string head hHeadNe hString
        have hFlatEq :
            __str_flatten (mkConcat head tail) =
              mkConcat head (__str_flatten tail) :=
          str_flatten_concat_nonstr_local head tail hNC hStrFalse hFlatTailNe
        have hFlatTy :
            __smtx_typeof
                (__eo_to_smt (mkConcat head (__str_flatten tail))) =
              SmtType.Seq T :=
          smt_typeof_str_concat_of_seq head (__str_flatten tail) T
            hArgs.1 hFlatTailTy
        have hFlatList :
            __eo_is_list (Term.UOp UserOp.str_concat)
                (mkConcat head (__str_flatten tail)) =
              Term.Boolean true :=
          eo_is_list_cons_self_true_of_tail_list
            (Term.UOp UserOp.str_concat) head (__str_flatten tail)
            (by decide) hFlatTailList
        have hFlatEvalTy :
            __smtx_typeof_value
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat head (__str_flatten tail)))) =
              SmtType.Seq T := by
          have hsimpa :=
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt (mkConcat head (__str_flatten tail))) (by
                unfold term_has_non_none_type
                rw [hFlatTy]
                simp)
          rw [hFlatTy] at hsimpa
          exact hsimpa
        rcases seq_value_canonical hFlatEvalTy with
          ⟨flatSs, hFlatEval⟩
        have hRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat head (__str_flatten tail))))
              (__smtx_model_eval M (__eo_to_smt (mkConcat head tail))) :=
          smt_value_rel_str_concat_right_congr M hM head
            (__str_flatten tail) tail T hArgs.1 hFlatTailTy hArgs.2
            hFlatTailRelEval
        refine ⟨flatSs, ?_, ?_, ?_, ?_⟩
        · simpa [hFlatEq] using hFlatEval
        · simpa [hFlatEq] using hFlatTy
        · simpa [hFlatEq] using hFlatList
        · have hsimpa := hRel; rw [hFlatEval, hPartsEvalCalc] at hsimpa; exact hsimpa
  | case4 x hStuck _hNSplice hNotConcat =>
      intro ss T hList hTy hEval hFlatNe
      have hNot : ¬ ∃ head tail : Term, x = mkConcat head tail := by
        rintro ⟨head, tail, hEq⟩
        exact hNotConcat head tail hEq
      have hFlatEq :
          __str_flatten x = x :=
        str_flatten_default_eq_self_of_list_not_concat_seq x T hList hNot hTy
          hFlatNe
      refine ⟨ss, ?_, ?_, ?_, ?_⟩
      · simpa [hFlatEq] using hEval
      · simpa [hFlatEq] using hTy
      · simpa [hFlatEq] using hList
      · exact RuleProofs.smt_value_rel_refl (SmtValue.Seq ss)

private theorem str_flatten_arg_ne_stuck_local (t : Term)
    (h : __str_flatten t ≠ Term.Stuck) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  simp [__str_flatten] at h

private theorem str_nary_intro_is_list_true_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
      Term.Boolean true := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil
      (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
  have hxNe : x ≠ Term.Stuck := term_ne_stuck_of_smt_type_seq x T hxTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hIntroEq :
        __str_nary_intro x =
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_not]
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck := by
      simpa [hIntroEq] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    rw [hIntroEq, hApplyEq]
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) x nil (by decide) hNilList
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    rw [hIntroEq]
    simpa using hListBool

theorem str_flatten_nary_intro_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (ss : SmtSeq)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hFlatNe : __str_flatten (__str_nary_intro s) ≠ Term.Stuck) :
    ∃ flatSs,
      __smtx_model_eval M
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtValue.Seq flatSs ∧
      __smtx_typeof
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss) := by
  have hIntroNe : __str_nary_intro s ≠ Term.Stuck :=
    str_flatten_arg_ne_stuck_local (__str_nary_intro s) hFlatNe
  have hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s SmtType.Char hTy
      type_inhabited_char (by native_decide) hIntroNe
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s SmtType.Char hTy
      hIntroNN hIntroNe
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    str_nary_intro_is_list_true_of_seq s SmtType.Char hTy hIntroNe
  have hIntroEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char := by
    simpa [hIntroTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (__str_nary_intro s)) (by
          unfold term_has_non_none_type
          rw [hIntroTy]
          simp)
  rcases seq_value_canonical hIntroEvalTy with ⟨introSs, hIntroEval⟩
  rcases str_flatten_list_eval_rel M hM (__str_nary_intro s) introSs
      SmtType.Char hIntroList hIntroTy hIntroEval hFlatNe with
    ⟨flatSs, hFlatEval, hFlatTy, hFlatList, hFlatRelIntro⟩
  have hIntroRel :
      RuleProofs.smt_value_rel (SmtValue.Seq introSs) (SmtValue.Seq ss) := by
    have hRel :=
      smt_value_rel_str_nary_intro M hM s SmtType.Char hTy hIntroNe
    simpa [hIntroEval, hEval] using hRel
  exact ⟨flatSs, hFlatEval, hFlatTy, hFlatList,
    RuleProofs.smt_value_rel_trans _ _ _ hFlatRelIntro hIntroRel⟩

private theorem re_split_str_to_re_eval_rel
    (M : SmtModel) (hM : model_wf M) :
    ∀ (parts tail : Term) (ss : SmtSeq) (rtail : SmtRegLan),
      __eo_is_list (Term.UOp UserOp.str_concat) parts = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt parts) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt parts) = SmtValue.Seq ss ->
      __smtx_typeof (__eo_to_smt tail) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.RegLan rtail ->
      ∃ r,
        __smtx_model_eval M
            (__eo_to_smt (__re_split_str_to_re parts tail)) =
          SmtValue.RegLan r ∧
        __smtx_typeof
            (__eo_to_smt (__re_split_str_to_re parts tail)) =
          SmtType.RegLan ∧
        RuleProofs.smt_value_rel (SmtValue.RegLan r)
          (SmtValue.RegLan
            (native_re_concat
              (native_str_to_re (native_unpack_string ss)) rtail)) := by
  intro parts tail
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      intro ss rtail hList _hPartsTy _hPartsEval _hTailTy _hTailEval
      simp [__eo_is_list] at hList
  | case2 parts hPartsNe =>
      intro ss rtail _hList _hPartsTy _hPartsEval hTailTy _hTailEval
      change __smtx_typeof SmtTerm.None = SmtType.RegLan at hTailTy
      rw [TranslationProofs.smtx_typeof_none] at hTailTy
      cases hTailTy
  | case3 c rest tail hTailNe ih =>
      intro ss rtail hList hPartsTy hPartsEval hTailTy hTailEval
      have hArgs := str_concat_args_of_seq_type c rest SmtType.Char hPartsTy
      have hRestList :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          c rest hList
      have hCEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c)) =
            SmtType.Seq SmtType.Char := by
        simpa [hArgs.1] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c) (by
            unfold term_has_non_none_type
            rw [hArgs.1]
            simp)
      have hRestEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt rest)) =
            SmtType.Seq SmtType.Char := by
        simpa [hArgs.2] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt rest) (by
              unfold term_has_non_none_type
              rw [hArgs.2]
              simp)
      rcases seq_value_canonical hCEvalTy with ⟨sc, hCEval⟩
      rcases seq_value_canonical hRestEvalTy with ⟨srest, hRestEval⟩
      have hScTy :
          __smtx_typeof_seq_value sc = SmtType.Seq SmtType.Char := by
        have hsimpa := hCEvalTy
        try simp [hCEval] at hsimpa ⊢
        exact hsimpa
      have hPartsEvalCalc :
          __smtx_model_eval M (__eo_to_smt (mkConcat c rest)) =
            SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value sc)
                (native_unpack_seq sc ++ native_unpack_seq srest)) := by
        rw [smtx_model_eval_str_concat_term_eq, hCEval, hRestEval]
        simp [__smtx_model_eval_str_concat, native_seq_concat]
      change __smtx_model_eval M (__eo_to_smt (mkConcat c rest)) =
        SmtValue.Seq ss at hPartsEval
      rw [hPartsEvalCalc] at hPartsEval
      cases hPartsEval
      rcases ih srest rtail hRestList hArgs.2 hRestEval hTailTy
          hTailEval with
        ⟨rRest, hSplitRestEval, hSplitRestTy, hSplitRestRel⟩
      let headRe := Term.Apply (Term.UOp UserOp.str_to_re) c
      let splitRest := __re_split_str_to_re rest tail
      have hHeadEval :
          __smtx_model_eval M (__eo_to_smt headRe) =
            SmtValue.RegLan (native_str_to_re (native_unpack_string sc)) := by
        dsimp [headRe]
        exact eval_str_to_re_reglan M c sc hCEval hScTy
      have hSplitRestTy' :
          __smtx_typeof (__eo_to_smt splitRest) = SmtType.RegLan := by
        simpa [splitRest] using hSplitRestTy
      have hSplitRestNe : splitRest ≠ Term.Stuck := by
        intro hStuck
        rw [hStuck] at hSplitRestTy'
        change __smtx_typeof SmtTerm.None = SmtType.RegLan at hSplitRestTy'
        rw [TranslationProofs.smtx_typeof_none] at hSplitRestTy'
        cases hSplitRestTy'
      have hMkApplyEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat) headRe) splitRest =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat) headRe) splitRest :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat) headRe) splitRest (by
            simp [__eo_mk_apply, headRe])
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) headRe)
                  splitRest)) =
            SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string sc)) rRest) :=
        eval_re_concat_reglan M headRe splitRest
          (native_str_to_re (native_unpack_string sc)) rRest hHeadEval
          (by simpa [splitRest] using hSplitRestEval)
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) headRe)
                  splitRest)) =
            SmtType.RegLan := by
        change __smtx_typeof
            (SmtTerm.re_concat (__eo_to_smt headRe)
              (__eo_to_smt splitRest)) =
          SmtType.RegLan
        rw [typeof_re_concat_eq]
        have hHeadTy :
            __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan := by
          change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt c)) =
            SmtType.RegLan
          rw [typeof_str_to_re_eq]
          simp [hArgs.1, native_ite, native_Teq]
        simp [hHeadTy, hSplitRestTy', native_ite, native_Teq]
      have hUnpack :
          native_unpack_string
              (native_pack_seq (__smtx_elem_typeof_seq_value sc)
                (native_unpack_seq sc ++ native_unpack_seq srest)) =
            native_unpack_string sc ++ native_unpack_string srest := by
        simp [native_unpack_string, Smtm.native_unpack_pack_seq,
          List.map_append]
      have hRelStep :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat (native_str_to_re (native_unpack_string sc))
                rRest))
            (SmtValue.RegLan
              (native_re_concat (native_str_to_re (native_unpack_string sc))
                (native_re_concat
                  (native_str_to_re (native_unpack_string srest)) rtail))) :=
        smt_value_rel_re_concat_local
          (RuleProofs.smt_value_rel_refl _)
          hSplitRestRel
      have hAssoc :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_re_concat
                  (native_str_to_re (native_unpack_string sc))
                  (native_str_to_re (native_unpack_string srest))) rtail))
            (SmtValue.RegLan
              (native_re_concat (native_str_to_re (native_unpack_string sc))
                (native_re_concat
                  (native_str_to_re (native_unpack_string srest)) rtail))) :=
        smt_value_rel_re_concat_assoc_local
          (native_str_to_re (native_unpack_string sc))
          (native_str_to_re (native_unpack_string srest)) rtail
      have hAppendRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_re_concat
                  (native_str_to_re (native_unpack_string sc))
                  (native_str_to_re (native_unpack_string srest))) rtail))
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re
                  (native_unpack_string sc ++ native_unpack_string srest))
                rtail)) :=
        smt_value_rel_re_concat_local
          (smt_value_rel_str_to_re_append (native_unpack_string sc)
            (native_unpack_string srest))
          (RuleProofs.smt_value_rel_refl _)
      refine ⟨native_re_concat (native_str_to_re (native_unpack_string sc))
          rRest, ?_, ?_, ?_⟩
      · simpa [__re_split_str_to_re, headRe, splitRest, hMkApplyEq]
          using hFullEval
      · simpa [__re_split_str_to_re, headRe, splitRest, hMkApplyEq]
          using hFullTy
      · rw [hUnpack]
        exact RuleProofs.smt_value_rel_trans _ _ _
          hRelStep
          (RuleProofs.smt_value_rel_trans _ _ _
            (RuleProofs.smt_value_rel_symm _ _ hAssoc) (by
              simpa [impl_native_string_to_values, List.map_append] using
                hAppendRel))
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      intro ss rtail hList hPartsTy hPartsEval hTailTy hTailEval
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) parts =
            Term.Boolean true :=
        eo_is_list_nil_str_concat_of_list_true_not_concat_local parts hList
          (by
            rintro ⟨head, rest, hEq⟩
            exact hNotConcat head rest (by simpa [mkConcat] using hEq))
      have hNilRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt parts))
            (SmtValue.Seq (SmtSeq.empty SmtType.Char)) :=
        smt_value_rel_str_concat_nil_empty M parts SmtType.Char hNil
          hPartsTy
      have hSeqRel :
          RuleProofs.smt_seq_rel ss (SmtSeq.empty SmtType.Char) := by
        simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel,
          hPartsEval] using hNilRel
      have hSsEq : ss = SmtSeq.empty SmtType.Char :=
        (RuleProofs.smt_seq_rel_iff_eq ss
          (SmtSeq.empty SmtType.Char)).1 hSeqRel
      refine ⟨rtail, ?_, ?_, ?_⟩
      · simpa [__re_split_str_to_re] using hTailEval
      · simpa [__re_split_str_to_re] using hTailTy
      · subst ss
        have hEmptyUnpack :
            native_unpack_string (SmtSeq.empty SmtType.Char) =
              ([] : native_String) := by
          simp [native_unpack_string, native_unpack_seq]
        simpa [hEmptyUnpack, native_re_concat_left_empty] using
          RuleProofs.smt_value_rel_refl (SmtValue.RegLan rtail)

private theorem re_split_str_to_re_parts_ne_stuck
    (parts tail : Term)
    (h : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    parts ≠ Term.Stuck := by
  intro hp
  subst parts
  simp [__re_split_str_to_re] at h

private theorem re_split_str_to_re_tail_ne_stuck
    (parts tail : Term)
    (h : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    tail ≠ Term.Stuck := by
  intro ht
  subst tail
  cases parts <;> simp [__re_split_str_to_re] at h

private theorem smt_typeof_re_union_of_reglan_local
    (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan
  rw [typeof_re_union_eq]
  simp [hA, hB, native_ite, native_Teq]

private theorem smt_typeof_re_inter_of_reglan_local
    (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hA, hB, native_ite, native_Teq]

/--
Evaluation, typing and value relation for `__eo_list_concat_rec` on
`re_concat` lists: splicing two evaluating regex lists concatenates
their values (up to extensional equivalence).
-/
private theorem eval_list_concat_rec_re_concat_rel_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ (x z : Term),
      __eo_is_list (Term.UOp UserOp.re_concat) x = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt z) = SmtType.RegLan ->
      ∀ (xv zv : SmtRegLan),
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan xv ->
        __smtx_model_eval M (__eo_to_smt z) = SmtValue.RegLan zv ->
        ∃ v,
          __smtx_model_eval M
              (__eo_to_smt (__eo_list_concat_rec x z)) =
            SmtValue.RegLan v ∧
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec x z)) =
            SmtType.RegLan ∧
          RuleProofs.smt_value_rel (SmtValue.RegLan v)
            (SmtValue.RegLan (native_re_concat xv zv)) := by
  intro x z
  induction x, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hList _hXTy _hZTy
      simp [__eo_is_list] at hList
  | case2 t ht =>
      intro _hList _hXTy hZTy
      exfalso
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl] at hZTy
      rw [TranslationProofs.smtx_typeof_none] at hZTy
      cases hZTy
  | case3 f x y z hz ih =>
      intro hList hXTy hZTy xv zv hXEval hZEval
      have hf := eo_is_list_cons_head_eq_of_true
        (Term.UOp UserOp.re_concat) f x y hList
      subst hf
      have hTailList := eo_is_list_tail_true_of_cons_self
        (Term.UOp UserOp.re_concat) x y hList
      have hArgs := re_concat_arg_types_of_reglan x y hXTy
      rcases smt_model_eval_reglan_of_type M hM x hArgs.1 with
        ⟨hv, hHEval⟩
      rcases smt_model_eval_reglan_of_type M hM y hArgs.2 with
        ⟨tv, hTEval⟩
      have hRecomp := eval_re_concat_reglan M x y hv tv hHEval hTEval
      have hXvEq : xv = native_re_concat hv tv := by
        injection hXEval.symm.trans hRecomp
      subst hXvEq
      rcases ih hTailList hArgs.2 hZTy tv zv hTEval hZEval with
        ⟨v', hV'Eval, hV'Ty, hV'Rel⟩
      have hRecNe : __eo_list_concat_rec y z ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hV'Eval
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl]
          at hV'Eval
        simp [__smtx_model_eval] at hV'Eval
      have hStep :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y)
              z =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat) x)
              (__eo_list_concat_rec y z) := by
        cases z
        case Stuck => exact absurd rfl hz
        all_goals rfl
      have hMkEq :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) x)
              (__eo_list_concat_rec y z) =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x)
              (__eo_list_concat_rec y z) := by
        cases hR : __eo_list_concat_rec y z
        case Stuck => exact absurd hR hRecNe
        all_goals rfl
      rw [hStep, hMkEq]
      refine ⟨native_re_concat hv v',
        eval_re_concat_reglan M x _ hv v' hHEval hV'Eval,
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan
          x _ hArgs.1 hV'Ty, ?_⟩
      exact RuleProofs.smt_value_rel_trans _ _ _
        (smt_value_rel_re_concat_local
          (RuleProofs.smt_value_rel_refl _) hV'Rel)
        (RuleProofs.smt_value_rel_symm _ _
          (smt_value_rel_re_concat_assoc_local hv tv zv))
  | case4 nil z hns hzs hncons =>
      intro hList _hXTy hZTy xv zv hXEval hZEval
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      have hIsListEq :
          __eo_is_list (Term.UOp UserOp.re_concat) nil =
            __eo_is_ok
              (__eo_get_nil_rec (Term.UOp UserOp.re_concat) nil) := by
        cases nil <;> first | exact absurd rfl hns | rfl
      rw [hIsListEq] at hList
      have hGnrNe :
          __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil ≠
            Term.Stuck := by
        intro hBad
        rw [hBad] at hList
        simp [__eo_is_ok, native_teq, SmtEval.native_not] at hList
      have hAtomEq :
          __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil =
            __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
              (Term.Boolean true) nil := by
        cases nil
        case Stuck => exact absurd rfl hns
        case Apply a b =>
          cases a
          case Apply g x => exact ((hncons _ _ _ rfl).elim)
          all_goals rfl
        all_goals rfl
      rw [hAtomEq] at hGnrNe
      have hNilTrue := eo_requires_eq_of_ne_stuck _ _ _ hGnrNe
      have hNilEval :=
        RuleProofs.ReUnfoldNegSupport.reConcat_nil_eval_empty_of_is_list_nil_true
          M nil hNilTrue
      have hXvEq : xv = native_str_to_re [] := by
        injection hXEval.symm.trans hNilEval
      subst hXvEq
      rw [hEq]
      refine ⟨zv, hZEval, hZTy, ?_⟩
      exact RuleProofs.smt_value_rel_symm _ _
        (smt_value_rel_reglan_of_eq (native_re_concat_left_empty zv))

/--
Evaluation, typing and value relation for `__eo_list_concat` on
`re_concat` lists (unwraps the two `requires` guards).
-/
private theorem eval_list_concat_re_concat_rel_local
    (M : SmtModel) (hM : model_wf M)
    (x z : Term) (xv zv : SmtRegLan)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.RegLan)
    (hXEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan xv)
    (hZEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.RegLan zv)
    (hNe :
      __eo_list_concat (Term.UOp UserOp.re_concat) x z ≠ Term.Stuck) :
    ∃ v,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_concat) x z)) =
        SmtValue.RegLan v ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_concat) x z)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan v)
        (SmtValue.RegLan (native_re_concat xv zv)) := by
  have hDef : __eo_list_concat (Term.UOp UserOp.re_concat) x z =
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) x)
        (Term.Boolean true)
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) z)
          (Term.Boolean true) (__eo_list_concat_rec x z)) := rfl
  have hNe0 : __eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) x)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec x z)) ≠ Term.Stuck := by
    rw [← hDef]
    exact hNe
  have hXList := eo_requires_eq_of_ne_stuck _ _ _ hNe0
  have hOuterEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe0
  have hNe1 : __eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec x z) ≠ Term.Stuck := by
    rw [← hOuterEq]
    exact hNe0
  have hInnerEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe1
  have hWhole : __eo_list_concat (Term.UOp UserOp.re_concat) x z =
      __eo_list_concat_rec x z := by
    rw [hDef, hOuterEq, hInnerEq]
  rw [hWhole]
  exact eval_list_concat_rec_re_concat_rel_local M hM x z hXList
    hXTy hZTy xv zv hXEval hZEval

theorem re_flatten_false_eval_rel
    (M : SmtModel) (hM : model_wf M) :
    ∀ (mode r : Term) (rv : SmtRegLan),
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __re_flatten mode r ≠ Term.Stuck ->
      ∃ flatRv,
        __smtx_model_eval M
            (__eo_to_smt (__re_flatten mode r)) =
          SmtValue.RegLan flatRv ∧
        __smtx_typeof
            (__eo_to_smt (__re_flatten mode r)) =
          SmtType.RegLan ∧
        RuleProofs.smt_value_rel (SmtValue.RegLan flatRv)
          (SmtValue.RegLan rv) := by
  intro mode r
  induction mode, r using __re_flatten.induct with
  | case1 x =>
      intro rv hTy _hEval _hFlatNe
      change __smtx_typeof SmtTerm.None = SmtType.RegLan at hTy
      rw [TranslationProofs.smtx_typeof_none] at hTy
      cases hTy
  | case2 =>
      intro rv _hTy hEval _hFlatNe
      have hEmptyEval := smtx_model_eval_re_empty_string M
      rw [hEmptyEval] at hEval
      cases hEval
      refine ⟨native_str_to_re [], ?_, ?_, ?_⟩
      · simpa [__re_flatten] using hEmptyEval
      · simpa [__re_flatten] using smtx_typeof_re_empty_string
      · exact RuleProofs.smt_value_rel_refl _
  | case3 s b ih =>
      intro rv hTy hEval hFlatNe
      let parts := __str_flatten (__str_nary_intro s)
      let flatB := __re_flatten (Term.Boolean true) b
      have hArgs :=
        re_concat_arg_types_of_reglan
          (Term.Apply (Term.UOp UserOp.str_to_re) s) b hTy
      have hSTy : __smtx_typeof (__eo_to_smt s) =
          SmtType.Seq SmtType.Char :=
        str_to_re_arg_type_of_reglan s hArgs.1
      have hSEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt s)) =
            SmtType.Seq SmtType.Char := by
        simpa [hSTy] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt s) (by
              unfold term_has_non_none_type
              rw [hSTy]
              simp)
      rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
      have hSsTy :
          __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
        have hsimpa := hSEvalTy
        try simp [hSEval] at hsimpa ⊢
        exact hsimpa
      rcases smt_model_eval_reglan_of_type M hM b hArgs.2 with
        ⟨rb, hBEval⟩
      have hHeadEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
            SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) :=
        eval_str_to_re_reglan M s ss hSEval hSsTy
      have hOrigEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat)
                    (Term.Apply (Term.UOp UserOp.str_to_re) s)) b)) =
            SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string ss)) rb) :=
        eval_re_concat_reglan M
          (Term.Apply (Term.UOp UserOp.str_to_re) s) b
          (native_str_to_re (native_unpack_string ss)) rb hHeadEval hBEval
      rw [hOrigEval] at hEval
      cases hEval
      have hSplitNe :
          __re_split_str_to_re parts flatB ≠ Term.Stuck := by
        simpa [__re_flatten, parts, flatB] using hFlatNe
      have hPartsNe : parts ≠ Term.Stuck :=
        re_split_str_to_re_parts_ne_stuck parts flatB hSplitNe
      have hFlatBNe : flatB ≠ Term.Stuck :=
        re_split_str_to_re_tail_ne_stuck parts flatB hSplitNe
      rcases str_flatten_nary_intro_eval_rel M hM s ss hSTy hSEval
          (by simpa [parts] using hPartsNe) with
        ⟨flatSs, hPartsEval, hPartsTy, hPartsList, hPartsRel⟩
      rcases ih rb hArgs.2 hBEval
          (by simpa [flatB] using hFlatBNe) with
        ⟨flatRb, hFlatBEval, hFlatBTy, hFlatBRel⟩
      rcases re_split_str_to_re_eval_rel M hM parts flatB flatSs flatRb
          hPartsList hPartsTy hPartsEval hFlatBTy hFlatBEval with
        ⟨rSplit, hSplitEval, hSplitTy, hSplitRel⟩
      have hHeadRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string flatSs)))
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string ss))) :=
        smt_value_rel_str_to_re_of_seq_rel hPartsRel
      have hConcatRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string flatSs))
                flatRb))
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string ss)) rb)) :=
        smt_value_rel_re_concat_local hHeadRel hFlatBRel
      refine ⟨rSplit, ?_, ?_, ?_⟩
      · simpa [__re_flatten, parts, flatB] using hSplitEval
      · simpa [__re_flatten, parts, flatB] using hSplitTy
      · exact RuleProofs.smt_value_rel_trans _ _ _
          hSplitRel hConcatRel
  | case4 a1 a2 b ih1 ih2 =>
      intro rv hTy hEval hFlatNe
      have hArgs := re_concat_arg_types_of_reglan
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1) a2) b hTy
      rcases smt_model_eval_reglan_of_type M hM
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1) a2)
          hArgs.1 with ⟨xv, hXEval⟩
      rcases smt_model_eval_reglan_of_type M hM b hArgs.2 with
        ⟨bv, hBEval⟩
      have hOrigEval := eval_re_concat_reglan M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1) a2) b
        xv bv hXEval hBEval
      rw [hOrigEval] at hEval
      cases hEval
      have hNe0 : __eo_list_concat (Term.UOp UserOp.re_concat)
          (__re_flatten (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1) a2))
          (__re_flatten (Term.Boolean true) b) ≠ Term.Stuck := by
        simpa [__re_flatten] using hFlatNe
      have hNe0' : __eo_requires
          (__eo_is_list (Term.UOp UserOp.re_concat)
            (__re_flatten (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1)
                a2)))
          (Term.Boolean true)
          (__eo_requires
            (__eo_is_list (Term.UOp UserOp.re_concat)
              (__re_flatten (Term.Boolean true) b))
            (Term.Boolean true)
            (__eo_list_concat_rec
              (__re_flatten (Term.Boolean true)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1)
                  a2))
              (__re_flatten (Term.Boolean true) b))) ≠ Term.Stuck :=
        hNe0
      have hXList := eo_requires_eq_of_ne_stuck _ _ _ hNe0'
      have hNe1 : __eo_requires
          (__eo_is_list (Term.UOp UserOp.re_concat)
            (__re_flatten (Term.Boolean true) b))
          (Term.Boolean true)
          (__eo_list_concat_rec
            (__re_flatten (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1)
                a2))
            (__re_flatten (Term.Boolean true) b)) ≠ Term.Stuck := by
        rw [← eo_requires_eq_result_of_ne_stuck _ _ _ hNe0']
        exact hNe0'
      have hBList := eo_requires_eq_of_ne_stuck _ _ _ hNe1
      have hFlatXNe : __re_flatten (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1) a2) ≠
            Term.Stuck := by
        intro hBad
        rw [hBad] at hXList
        simp [__eo_is_list] at hXList
      have hFlatBNe : __re_flatten (Term.Boolean true) b ≠
          Term.Stuck := by
        intro hBad
        rw [hBad] at hBList
        simp [__eo_is_list] at hBList
      rcases ih1 xv hArgs.1 hXEval hFlatXNe with
        ⟨fxv, hFxEval, hFxTy, hFxRel⟩
      rcases ih2 bv hArgs.2 hBEval hFlatBNe with
        ⟨fbv, hFbEval, hFbTy, hFbRel⟩
      rcases eval_list_concat_re_concat_rel_local M hM _ _ fxv fbv
          hFxTy hFbTy hFxEval hFbEval hNe0 with ⟨v, hVEval, hVTy, hVRel⟩
      refine ⟨v, ?_, ?_, ?_⟩
      · simpa [__re_flatten] using hVEval
      · simpa [__re_flatten] using hVTy
      · exact RuleProofs.smt_value_rel_trans _ _ _ hVRel
          (smt_value_rel_re_concat_local hFxRel hFbRel)
  | case5 a b hNotStr _hNotNested ihA ihB =>
      intro rv hTy hEval hFlatNe
      let flatA := __re_flatten (Term.Boolean false) a
      let flatB := __re_flatten (Term.Boolean true) b
      have hArgs := re_concat_arg_types_of_reglan a b hTy
      rcases smt_model_eval_reglan_of_type M hM a hArgs.1 with
        ⟨ra, hAEval⟩
      rcases smt_model_eval_reglan_of_type M hM b hArgs.2 with
        ⟨rb, hBEval⟩
      have hOrigEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
            SmtValue.RegLan (native_re_concat ra rb) :=
        eval_re_concat_reglan M a b ra rb hAEval hBEval
      rw [hOrigEval] at hEval
      cases hEval
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) flatA) flatB ≠
            Term.Stuck := by
        simpa [__re_flatten, flatA, flatB] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat) flatA ≠ Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatANe : flatA ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hFlatBNe : flatB ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      rcases ihA ra hArgs.1 hAEval
          (by simpa [flatA] using hFlatANe) with
        ⟨flatRa, hFlatAEval, hFlatATy, hFlatARel⟩
      rcases ihB rb hArgs.2 hBEval
          (by simpa [flatB] using hFlatBNe) with
        ⟨flatRb, hFlatBEval, hFlatBTy, hFlatBRel⟩
      have hInnerEq :
          __eo_mk_apply (Term.UOp UserOp.re_concat) flatA =
            Term.Apply (Term.UOp UserOp.re_concat) flatA :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.re_concat) flatA hInnerNe
      have hOutNe' :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat) flatA) flatB ≠
            Term.Stuck := by
        simpa [hInnerEq] using hOutNe
      have hOutEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat) flatA) flatB =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat) flatA) flatB :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat) flatA) flatB hOutNe'
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) flatA) flatB)) =
            SmtValue.RegLan (native_re_concat flatRa flatRb) :=
        eval_re_concat_reglan M flatA flatB flatRa flatRb
          hFlatAEval hFlatBEval
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) flatA) flatB)) =
            SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan
          flatA flatB hFlatATy hFlatBTy
      refine ⟨native_re_concat flatRa flatRb, ?_, ?_, ?_⟩
      · simpa [__re_flatten, flatA, flatB, hOutEq, hInnerEq] using
          hFullEval
      · simpa [__re_flatten, flatA, flatB, hOutEq, hInnerEq] using
          hFullTy
      · exact smt_value_rel_re_concat_local hFlatARel hFlatBRel
  | case6 s hNotEmpty =>
      intro rv hTy hEval hFlatNe
      let parts := __str_flatten (__str_nary_intro s)
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hSTy : __smtx_typeof (__eo_to_smt s) =
          SmtType.Seq SmtType.Char :=
        str_to_re_arg_type_of_reglan s hTy
      have hSEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt s)) =
            SmtType.Seq SmtType.Char := by
        simpa [hSTy] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt s) (by
              unfold term_has_non_none_type
              rw [hSTy]
              simp)
      rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
      have hSsTy :
          __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
        have hsimpa := hSEvalTy
        try simp [hSEval] at hsimpa ⊢
        exact hsimpa
      have hOrigEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
            SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) :=
        eval_str_to_re_reglan M s ss hSEval hSsTy
      rw [hOrigEval] at hEval
      cases hEval
      have hSplitNe :
          __re_split_str_to_re parts eps ≠ Term.Stuck := by
        simpa [__re_flatten, parts, eps] using hFlatNe
      have hPartsNe : parts ≠ Term.Stuck :=
        re_split_str_to_re_parts_ne_stuck parts eps hSplitNe
      rcases str_flatten_nary_intro_eval_rel M hM s ss hSTy hSEval
          (by simpa [parts] using hPartsNe) with
        ⟨flatSs, hPartsEval, hPartsTy, hPartsList, hPartsRel⟩
      rcases re_split_str_to_re_eval_rel M hM parts eps flatSs
          (native_str_to_re []) hPartsList hPartsTy hPartsEval
          (by simpa [eps] using smtx_typeof_re_empty_string)
          (by simpa [eps] using smtx_model_eval_re_empty_string M) with
        ⟨rSplit, hSplitEval, hSplitTy, hSplitRel⟩
      have hEmptyRight :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string flatSs))
                (native_str_to_re [])))
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string flatSs))) :=
        smt_value_rel_reglan_of_eq
          (native_re_concat_right_empty
            (native_str_to_re (native_unpack_string flatSs)))
      have hHeadRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string flatSs)))
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string ss))) :=
        smt_value_rel_str_to_re_of_seq_rel hPartsRel
      refine ⟨rSplit, ?_, ?_, ?_⟩
      · simpa [__re_flatten, parts, eps] using hSplitEval
      · simpa [__re_flatten, parts, eps] using hSplitTy
      · exact RuleProofs.smt_value_rel_trans _ _ _
          hSplitRel
          (RuleProofs.smt_value_rel_trans _ _ _ hEmptyRight hHeadRel)
  | case7 c hCNe hEmpty hConcatStr _hNested hConcat hStr ih =>
      intro rv hTy hEval hFlatNe
      let flatC := __re_flatten (Term.Boolean false) c
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) flatC) eps ≠
            Term.Stuck := by
        simpa [__re_flatten, flatC, eps] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat) flatC ≠ Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatCNe : flatC ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      rcases ih rv hTy hEval (by simpa [flatC] using hFlatCNe) with
        ⟨flatRv, hFlatEval, hFlatTy, hFlatRel⟩
      have hInnerEq :
          __eo_mk_apply (Term.UOp UserOp.re_concat) flatC =
            Term.Apply (Term.UOp UserOp.re_concat) flatC :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.re_concat) flatC hInnerNe
      have hOutEq :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) flatC) eps =
            Term.Apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) flatC) eps :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (__eo_mk_apply (Term.UOp UserOp.re_concat) flatC) eps hOutNe
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) flatC) eps)) =
            SmtValue.RegLan
              (native_re_concat flatRv (native_str_to_re [])) :=
        eval_re_concat_reglan M flatC eps flatRv (native_str_to_re [])
          hFlatEval (by simpa [eps] using smtx_model_eval_re_empty_string M)
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) flatC) eps)) =
            SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan
          flatC eps hFlatTy
          (by simpa [eps] using smtx_typeof_re_empty_string)
      have hConcatRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat flatRv (native_str_to_re [])))
            (SmtValue.RegLan
              (native_re_concat rv (native_str_to_re []))) :=
        smt_value_rel_re_concat_local hFlatRel
          (RuleProofs.smt_value_rel_refl _)
      have hRightEmpty :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat rv (native_str_to_re [])))
            (SmtValue.RegLan rv) :=
        smt_value_rel_reglan_of_eq (native_re_concat_right_empty rv)
      refine ⟨native_re_concat flatRv (native_str_to_re []), ?_, ?_, ?_⟩
      · have hsimpa := hFullEval; (try simp [__re_flatten, flatC, eps, hInnerEq] at hsimpa ⊢); exact hsimpa
      · have hsimpa := hFullTy; (try simp [__re_flatten, flatC, eps, hInnerEq] at hsimpa ⊢); exact hsimpa
      · exact RuleProofs.smt_value_rel_trans _ _ _
          hConcatRel hRightEmpty
  | case8 =>
      intro rv hTy hEval _hFlatNe
      refine ⟨rv, ?_, ?_, ?_⟩
      · simpa [__re_flatten] using hEval
      · simpa [__re_flatten] using hTy
      · exact RuleProofs.smt_value_rel_refl _
  | case9 =>
      intro rv hTy hEval _hFlatNe
      refine ⟨rv, ?_, ?_, ?_⟩
      · simpa [__re_flatten] using hEval
      · simpa [__re_flatten] using hTy
      · exact RuleProofs.smt_value_rel_refl _
  | case10 body ih =>
      intro rv hTy hEval hFlatNe
      let flatBody := __re_flatten (Term.Boolean true) body
      have hBodyTy := re_mult_arg_type_of_reglan body hTy
      rcases smt_model_eval_reglan_of_type M hM body hBodyTy with
        ⟨rBody, hBodyEval⟩
      have hOrigEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) body)) =
            SmtValue.RegLan (native_re_mult rBody) :=
        eval_re_mult_reglan M body rBody hBodyEval
      rw [hOrigEval] at hEval
      cases hEval
      have hOutNe :
          __eo_mk_apply (Term.UOp UserOp.re_mult) flatBody ≠
            Term.Stuck := by
        simpa [__re_flatten, flatBody] using hFlatNe
      have hFlatBodyNe : flatBody ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      rcases ih rBody hBodyTy hBodyEval
          (by simpa [flatBody] using hFlatBodyNe) with
        ⟨flatRBody, hFlatBodyEval, hFlatBodyTy, hFlatBodyRel⟩
      have hOutEq :
          __eo_mk_apply (Term.UOp UserOp.re_mult) flatBody =
            Term.Apply (Term.UOp UserOp.re_mult) flatBody :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.re_mult) flatBody hOutNe
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) flatBody)) =
            SmtValue.RegLan (native_re_mult flatRBody) :=
        eval_re_mult_reglan M flatBody flatRBody hFlatBodyEval
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) flatBody)) =
            SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_of_reglan
          flatBody hFlatBodyTy
      refine ⟨native_re_mult flatRBody, ?_, ?_, ?_⟩
      · simpa [__re_flatten, flatBody, hOutEq] using hFullEval
      · simpa [__re_flatten, flatBody, hOutEq] using hFullTy
      · exact smt_value_rel_re_mult_local hFlatBodyRel
  | case11 c1 c2 ih1 ih2 =>
      intro rv hTy hEval hFlatNe
      let flatC1 := __re_flatten (Term.Boolean true) c1
      let flatC2 := __re_flatten (Term.Boolean false) c2
      have hArgs := re_inter_arg_types_of_reglan c1 c2 hTy
      rcases smt_model_eval_reglan_of_type M hM c1 hArgs.1 with
        ⟨r1, hC1Eval⟩
      rcases smt_model_eval_reglan_of_type M hM c2 hArgs.2 with
        ⟨r2, hC2Eval⟩
      have hOrigEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)) =
            SmtValue.RegLan (native_re_inter r1 r2) :=
        eval_re_inter_reglan M c1 c2 r1 r2 hC1Eval hC2Eval
      rw [hOrigEval] at hEval
      cases hEval
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_inter) flatC1)
              flatC2 ≠
            Term.Stuck := by
        simpa [__re_flatten, flatC1, flatC2] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_inter) flatC1 ≠
            Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatC1Ne : flatC1 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hFlatC2Ne : flatC2 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      rcases ih1 r1 hArgs.1 hC1Eval
          (by simpa [flatC1] using hFlatC1Ne) with
        ⟨flatR1, hFlatC1Eval, hFlatC1Ty, hFlatC1Rel⟩
      rcases ih2 r2 hArgs.2 hC2Eval
          (by simpa [flatC2] using hFlatC2Ne) with
        ⟨flatR2, hFlatC2Eval, hFlatC2Ty, hFlatC2Rel⟩
      have hInnerEq :
          __eo_mk_apply (Term.UOp UserOp.re_inter) flatC1 =
            Term.Apply (Term.UOp UserOp.re_inter) flatC1 :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.re_inter) flatC1 hInnerNe
      have hOutNe' :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_inter) flatC1) flatC2 ≠
            Term.Stuck := by
        simpa [hInnerEq] using hOutNe
      have hOutEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_inter) flatC1) flatC2 =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) flatC1) flatC2 :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_inter) flatC1) flatC2 hOutNe'
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_inter) flatC1) flatC2)) =
            SmtValue.RegLan (native_re_inter flatR1 flatR2) :=
        eval_re_inter_reglan M flatC1 flatC2 flatR1 flatR2
          hFlatC1Eval hFlatC2Eval
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_inter) flatC1) flatC2)) =
            SmtType.RegLan :=
        smt_typeof_re_inter_of_reglan_local flatC1 flatC2
          hFlatC1Ty hFlatC2Ty
      refine ⟨native_re_inter flatR1 flatR2, ?_, ?_, ?_⟩
      · simpa [__re_flatten, flatC1, flatC2, hOutEq, hInnerEq] using
          hFullEval
      · simpa [__re_flatten, flatC1, flatC2, hOutEq, hInnerEq] using
          hFullTy
      · exact smt_value_rel_re_inter_local hFlatC1Rel hFlatC2Rel
  | case12 c1 c2 ih1 ih2 =>
      intro rv hTy hEval hFlatNe
      let flatC1 := __re_flatten (Term.Boolean true) c1
      let flatC2 := __re_flatten (Term.Boolean false) c2
      have hArgs := re_union_arg_types_of_reglan c1 c2 hTy
      rcases smt_model_eval_reglan_of_type M hM c1 hArgs.1 with
        ⟨r1, hC1Eval⟩
      rcases smt_model_eval_reglan_of_type M hM c2 hArgs.2 with
        ⟨r2, hC2Eval⟩
      have hOrigEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) =
            SmtValue.RegLan (native_re_union r1 r2) :=
        eval_re_union_reglan M c1 c2 r1 r2 hC1Eval hC2Eval
      rw [hOrigEval] at hEval
      cases hEval
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_union) flatC1)
              flatC2 ≠
            Term.Stuck := by
        simpa [__re_flatten, flatC1, flatC2] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_union) flatC1 ≠
            Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatC1Ne : flatC1 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hFlatC2Ne : flatC2 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      rcases ih1 r1 hArgs.1 hC1Eval
          (by simpa [flatC1] using hFlatC1Ne) with
        ⟨flatR1, hFlatC1Eval, hFlatC1Ty, hFlatC1Rel⟩
      rcases ih2 r2 hArgs.2 hC2Eval
          (by simpa [flatC2] using hFlatC2Ne) with
        ⟨flatR2, hFlatC2Eval, hFlatC2Ty, hFlatC2Rel⟩
      have hInnerEq :
          __eo_mk_apply (Term.UOp UserOp.re_union) flatC1 =
            Term.Apply (Term.UOp UserOp.re_union) flatC1 :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.re_union) flatC1 hInnerNe
      have hOutNe' :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_union) flatC1) flatC2 ≠
            Term.Stuck := by
        simpa [hInnerEq] using hOutNe
      have hOutEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_union) flatC1) flatC2 =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) flatC1) flatC2 :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_union) flatC1) flatC2 hOutNe'
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union) flatC1) flatC2)) =
            SmtValue.RegLan (native_re_union flatR1 flatR2) :=
        eval_re_union_reglan M flatC1 flatC2 flatR1 flatR2
          hFlatC1Eval hFlatC2Eval
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union) flatC1) flatC2)) =
            SmtType.RegLan :=
        smt_typeof_re_union_of_reglan_local flatC1 flatC2
          hFlatC1Ty hFlatC2Ty
      refine ⟨native_re_union flatR1 flatR2, ?_, ?_, ?_⟩
      · simpa [__re_flatten, flatC1, flatC2, hOutEq, hInnerEq] using
          hFullEval
      · simpa [__re_flatten, flatC1, flatC2, hOutEq, hInnerEq] using
          hFullTy
      · exact smt_value_rel_re_union_local hFlatC1Rel hFlatC2Rel
  | case13 c hCNe hAll hNone hMult hInter hUnion =>
      intro rv hTy hEval _hFlatNe
      refine ⟨rv, ?_, ?_, ?_⟩
      · simpa [__re_flatten] using hEval
      · simpa [__re_flatten] using hTy
      · exact RuleProofs.smt_value_rel_refl _
  | case14 x x_1 hTreeNe hEmpty hConcatStr _hNested hConcat
      hStr hTrue hAll hNone hMult hInter hUnion hFalse =>
      intro rv _hTy _hEval hFlatNe
      simp [__re_flatten] at hFlatNe

theorem re_inclusion_side_native_includes
    (M : SmtModel) (hM : model_wf M)
    (sup sub flatSup flatSub side : Term)
    (rvSup rvSub : SmtRegLan)
    (hSupTy : __smtx_typeof (__eo_to_smt sup) = SmtType.RegLan)
    (hSubTy : __smtx_typeof (__eo_to_smt sub) = SmtType.RegLan)
    (hSupEval : __smtx_model_eval M (__eo_to_smt sup) = SmtValue.RegLan rvSup)
    (hSubEval : __smtx_model_eval M (__eo_to_smt sub) = SmtValue.RegLan rvSub)
    (hFlatSup :
      flatSup = __re_flatten (Term.Boolean true) sup)
    (hFlatSub :
      flatSub = __re_flatten (Term.Boolean true) sub)
    (hSide :
      side =
        __eo_ite (__eo_eq flatSup flatSub) (Term.Boolean true)
          (__str_re_includes_rec flatSup flatSub))
    (hSideTrue : side = Term.Boolean true) :
    NativeIncludes rvSup rvSub := by
  subst flatSup
  subst flatSub
  rw [hSide] at hSideTrue
  let fs := __re_flatten (Term.Boolean true) sup
  let ft := __re_flatten (Term.Boolean true) sub
  change
    __eo_ite (__eo_eq fs ft) (Term.Boolean true)
      (__str_re_includes_rec fs ft) =
      Term.Boolean true at hSideTrue
  rcases eo_ite_true_result (__eo_eq fs ft)
      (__str_re_includes_rec fs ft) hSideTrue with hEq | hRec
  · have hFsNe : fs ≠ Term.Stuck := by
      intro hStuck
      have hBad := hEq
      rw [hStuck] at hBad
      simp [__eo_eq] at hBad
    have hFtNe : ft ≠ Term.Stuck := by
      intro hStuck
      have hBad := hEq
      rw [hStuck] at hBad
      simp [__eo_eq] at hBad
    rcases re_flatten_false_eval_rel M hM
        (Term.Boolean true) sup rvSup
        hSupTy hSupEval (by simpa [fs] using hFsNe) with
      ⟨flatRvSup, hFlatSupEval, hFlatSupTy, hFlatSupRel⟩
    rcases re_flatten_false_eval_rel M hM
        (Term.Boolean true) sub rvSub
        hSubTy hSubEval (by simpa [ft] using hFtNe) with
      ⟨flatRvSub, hFlatSubEval, hFlatSubTy, hFlatSubRel⟩
    have hTerm : fs = ft := (eq_of_eo_eq_true fs ft hEq).symm
    have hFlatIncl : NativeIncludes flatRvSup flatRvSub :=
      native_includes_of_same_term_eval M fs flatRvSup flatRvSub
        hFlatSupEval (by simpa [hTerm] using hFlatSubEval)
    exact native_includes_congr hFlatSupRel hFlatSubRel hFlatIncl
  · have hRecTrue : __str_re_includes_rec fs ft = Term.Boolean true :=
      hRec.2
    have hFsNe : fs ≠ Term.Stuck := by
      intro hStuck
      have hBad := hRecTrue
      rw [hStuck] at hBad
      simp [__str_re_includes_rec] at hBad
    have hFtNe : ft ≠ Term.Stuck := by
      intro hStuck
      have hBad := hRecTrue
      rw [hStuck] at hBad
      simp [__str_re_includes_rec] at hBad
    rcases re_flatten_false_eval_rel M hM
        (Term.Boolean true) sup rvSup
        hSupTy hSupEval (by simpa [fs] using hFsNe) with
      ⟨flatRvSup, hFlatSupEval, hFlatSupTy, hFlatSupRel⟩
    rcases re_flatten_false_eval_rel M hM
        (Term.Boolean true) sub rvSub
        hSubTy hSubEval (by simpa [ft] using hFtNe) with
      ⟨flatRvSub, hFlatSubEval, hFlatSubTy, hFlatSubRel⟩
    have hFlatIncl : NativeIncludes flatRvSup flatRvSub :=
      str_re_includes_rec_sound M hM fs ft flatRvSup flatRvSub
        hFlatSupTy hFlatSubTy hFlatSupEval hFlatSubEval hRecTrue
    exact native_includes_congr hFlatSupRel hFlatSubRel hFlatIncl

end RuleProofs
