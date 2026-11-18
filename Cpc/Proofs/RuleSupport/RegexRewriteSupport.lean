module

public import Cpc.Proofs.RuleSupport.ReConcatNullableSupport
import all Cpc.Proofs.RuleSupport.ReConcatNullableSupport
public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem smt_value_rel_re_concat_congr
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel
      (SmtValue.RegLan r) (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel
      (SmtValue.RegLan s) (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat r s))
      (SmtValue.RegLan (native_re_concat r' s')) := by
  have hrExt : ∀ xs : native_String,
      native_string_valid xs = true ->
      native_str_in_re xs r = native_str_in_re xs r' := fun xs hxs =>
    RuleProofs.reglan_str_in_re_eq_of_smt_value_rel hr xs hxs
  have hsExt : ∀ xs : native_String,
      native_string_valid xs = true ->
      native_str_in_re xs s = native_str_in_re xs s' := fun xs hxs =>
    RuleProofs.reglan_str_in_re_eq_of_smt_value_rel hs xs hxs
  apply RuleProofs.smt_value_rel_reglan_of_valid_eq
  intro xs hValid
  rw [RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid,
    RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs r s).1 (by have hsimpa := h; (try simp [native_re_concat] at hsimpa ⊢); exact hsimpa) with
      ⟨left, right, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (left ++ right) = true := by
      rw [hAppend]
      exact hValid
    have hLeftValid :=
      native_string_valid_append_left left right hAppendValid
    have hRightValid :=
      native_string_valid_append_right left right hAppendValid
    have hLeft' : nativeListInRe left r' = true := by
      have hEq := hrExt left hLeftValid
      rw [RuleProofs.native_str_in_re_eq_nativeListInRe left r hLeftValid,
        RuleProofs.native_str_in_re_eq_nativeListInRe left r' hLeftValid]
        at hEq
      rwa [← hEq]
    have hRight' : nativeListInRe right s' = true := by
      have hEq := hsExt right hRightValid
      rw [RuleProofs.native_str_in_re_eq_nativeListInRe right s hRightValid,
        RuleProofs.native_str_in_re_eq_nativeListInRe right s' hRightValid]
        at hEq
      rwa [← hEq]
    have hsimpa :=
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs r' s').2 ⟨left, right, hAppend, hLeft', hRight'⟩
    try simp [native_re_concat] at hsimpa ⊢
    exact hsimpa
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs r' s').1 (by have hsimpa := h; (try simp [native_re_concat] at hsimpa ⊢); exact hsimpa) with
      ⟨left, right, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (left ++ right) = true := by
      rw [hAppend]
      exact hValid
    have hLeftValid :=
      native_string_valid_append_left left right hAppendValid
    have hRightValid :=
      native_string_valid_append_right left right hAppendValid
    have hLeft' : nativeListInRe left r = true := by
      have hEq := hrExt left hLeftValid
      rw [RuleProofs.native_str_in_re_eq_nativeListInRe left r hLeftValid,
        RuleProofs.native_str_in_re_eq_nativeListInRe left r' hLeftValid]
        at hEq
      rwa [hEq]
    have hRight' : nativeListInRe right s = true := by
      have hEq := hsExt right hRightValid
      rw [RuleProofs.native_str_in_re_eq_nativeListInRe right s hRightValid,
        RuleProofs.native_str_in_re_eq_nativeListInRe right s' hRightValid]
        at hEq
      rwa [hEq]
    have hsimpa :=
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs r s).2 ⟨left, right, hAppend, hLeft', hRight'⟩
    try simp [native_re_concat] at hsimpa ⊢
    exact hsimpa

theorem smt_value_rel_re_concat_assoc
    (r s t : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat (native_re_concat r s) t))
      (SmtValue.RegLan
        (native_re_concat r (native_re_concat s t))) := by
  apply RuleProofs.smt_value_rel_reglan_of_valid_eq
  intro xs hValid
  rw [RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid,
    RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid]
  have hsimpa :=
    RuleProofs.nativeListInRe_mk_concat_assoc xs r s t
  try simp [native_re_concat] at hsimpa ⊢
  exact hsimpa

theorem nativeListInRe_raw_star_once
    (xs : List native_Char) (r : SmtRegLan)
    (hMem : nativeListInRe xs r = true) :
    nativeListInRe xs (SmtRegLan.star r) = true := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable]
  | cons c cs =>
      have hDer : nativeListInRe cs (native_re_deriv c r) = true := by
        simpa [nativeListInRe] using hMem
      have hNil : nativeListInRe [] (SmtRegLan.star r) = true := by
        simp [nativeListInRe, native_re_nullable]
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true :=
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          cs (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨cs, [], by simp, hDer, hNil⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat

theorem nativeListInRe_mk_star_once
    (xs : List native_Char) (r : SmtRegLan)
    (hMem : nativeListInRe xs r = true) :
    nativeListInRe xs (native_re_mk_star r) = true := by
  cases r with
  | empty =>
      have hFalse := RuleProofs.nativeListInRe_empty xs
      rw [hFalse] at hMem
      cases hMem
  | epsilon =>
      have hNil : xs = [] :=
        (RuleProofs.nativeListInRe_epsilon_iff xs).1 hMem
      subst xs
      simp [native_re_mk_star, native_re_mult, nativeListInRe, native_re_nullable]
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

theorem nativeListInRe_raw_star_cons_decomp
    {c : native_Char} {cs : List native_Char} {r : SmtRegLan}
    (h : nativeListInRe (c :: cs) (SmtRegLan.star r) = true) :
    ∃ firstTail rest,
      firstTail ++ rest = cs ∧
      nativeListInRe (c :: firstTail) r = true ∧
      nativeListInRe rest (SmtRegLan.star r) = true := by
  have hConcat :
      nativeListInRe cs
          (native_re_mk_concat (native_re_deriv c r)
            (SmtRegLan.star r)) = true := by
    simpa [nativeListInRe, native_re_deriv] using h
  rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        cs (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
    ⟨firstTail, rest, hAppend, hFirst, hRest⟩
  exact ⟨firstTail, rest, hAppend,
    by simpa [nativeListInRe] using hFirst, hRest⟩

theorem nativeListInRe_raw_star_snoc_decomp :
    (xs : List native_Char) -> (r : SmtRegLan) ->
      nativeListInRe xs (SmtRegLan.star r) = true ->
      xs = [] ∨
        ∃ pre last,
          xs = pre ++ last ∧
          nativeListInRe pre (SmtRegLan.star r) = true ∧
          nativeListInRe last r = true
  | [], r, _ => Or.inl rfl
  | c :: cs, r, hStar => by
      rcases nativeListInRe_raw_star_cons_decomp hStar with
        ⟨firstTail, rest, hAppend, hFirst, hRest⟩
      let first := c :: firstTail
      have hFirstStar :
          nativeListInRe first (SmtRegLan.star r) = true :=
        nativeListInRe_raw_star_once first r hFirst
      have hRestLen : rest.length < (c :: cs).length := by
        have hLen := congrArg List.length hAppend
        simp at hLen ⊢
        omega
      rcases nativeListInRe_raw_star_snoc_decomp rest r hRest with
        hRestNil | ⟨pre, last, hRestEq, hPre, hLast⟩
      · subst rest
        refine Or.inr ⟨[], first, ?_, ?_, hFirst⟩
        · simp only [List.nil_append, first]
          congr 1
          simpa using hAppend.symm
        · simp [nativeListInRe, native_re_nullable]
      · refine Or.inr ⟨first ++ pre, last, ?_, ?_, hLast⟩
        · calc
            c :: cs = first ++ rest := by simp [first, hAppend]
            _ = first ++ (pre ++ last) := by rw [hRestEq]
            _ = (first ++ pre) ++ last := by simp [List.append_assoc]
        · exact RuleProofs.nativeListInRe_raw_star_append
            first pre r hFirstStar hPre
termination_by xs _ _ => xs.length
decreasing_by
  all_goals omega

theorem nativeListInRe_raw_star_swap
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs
        (native_re_mk_concat (SmtRegLan.star r) r) =
      nativeListInRe xs
        (native_re_mk_concat r (SmtRegLan.star r)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs (SmtRegLan.star r) r).1 h with
      ⟨starPart, last, hAppend, hStar, hLast⟩
    cases starPart with
    | nil =>
        apply (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          xs r (SmtRegLan.star r)).2
        refine ⟨last, [], ?_, hLast, ?_⟩
        · simpa using hAppend
        · simp [nativeListInRe, native_re_nullable]
    | cons c cs =>
        rcases nativeListInRe_raw_star_cons_decomp hStar with
          ⟨firstTail, rest, hFirstAppend, hFirst, hRest⟩
        have hLastStar :
            nativeListInRe last (SmtRegLan.star r) = true :=
          nativeListInRe_raw_star_once last r hLast
        have hRestLast :
            nativeListInRe (rest ++ last) (SmtRegLan.star r) = true :=
          RuleProofs.nativeListInRe_raw_star_append
            rest last r hRest hLastStar
        apply (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          xs r (SmtRegLan.star r)).2
        refine ⟨c :: firstTail, rest ++ last, ?_, hFirst, hRestLast⟩
        calc
          (c :: firstTail) ++ (rest ++ last) =
              ((c :: firstTail) ++ rest) ++ last := by
                simp [List.append_assoc]
          _ = (c :: cs) ++ last := by
            simp only [List.cons_append]
            congr 1
            exact congrArg (fun q => q ++ last) hFirstAppend
          _ = xs := hAppend
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs r (SmtRegLan.star r)).1 h with
      ⟨first, starPart, hAppend, hFirst, hStar⟩
    rcases nativeListInRe_raw_star_snoc_decomp starPart r hStar with
      hStarNil | ⟨pre, last, hStarEq, hPre, hLast⟩
    · subst starPart
      apply (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs (SmtRegLan.star r) r).2
      refine ⟨[], first, ?_, ?_, hFirst⟩
      · simpa using hAppend
      · simp [nativeListInRe, native_re_nullable]
    · have hFirstStar :
          nativeListInRe first (SmtRegLan.star r) = true :=
        nativeListInRe_raw_star_once first r hFirst
      have hFirstPrefix :
          nativeListInRe (first ++ pre) (SmtRegLan.star r) = true :=
        RuleProofs.nativeListInRe_raw_star_append
          first pre r hFirstStar hPre
      apply (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs (SmtRegLan.star r) r).2
      refine ⟨first ++ pre, last, ?_, hFirstPrefix, hLast⟩
      calc
        (first ++ pre) ++ last = first ++ (pre ++ last) := by
          simp [List.append_assoc]
        _ = first ++ starPart := by rw [← hStarEq]
        _ = xs := hAppend

theorem nativeListInRe_mk_star_swap
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs
        (native_re_mk_concat (native_re_mk_star r) r) =
      nativeListInRe xs
        (native_re_mk_concat r (native_re_mk_star r)) := by
  cases r with
  | empty => simp [native_re_mk_star, native_re_mult, native_re_mk_concat,
      native_re_concat, RuleProofs.nativeListInRe_empty]
  | epsilon => simp [native_re_mk_star, native_re_mult, native_re_mk_concat]
  | star r => simp [native_re_mk_star, native_re_mult]
  | char c => have hsimpa := nativeListInRe_raw_star_swap xs (SmtRegLan.char c); (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa
  | range lo hi => have hsimpa := nativeListInRe_raw_star_swap xs (SmtRegLan.range lo hi); (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa
  | allchar => have hsimpa := nativeListInRe_raw_star_swap xs SmtRegLan.allchar; (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa
  | concat r s => have hsimpa := nativeListInRe_raw_star_swap xs (SmtRegLan.concat r s); (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa
  | union r s => have hsimpa := nativeListInRe_raw_star_swap xs (SmtRegLan.union r s); (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa
  | inter r s => have hsimpa := nativeListInRe_raw_star_swap xs (SmtRegLan.inter r s); (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa
  | comp r => have hsimpa := nativeListInRe_raw_star_swap xs (SmtRegLan.comp r); (try simp [native_re_mk_star] at hsimpa ⊢); exact hsimpa

theorem smt_value_rel_re_concat_star_swap_core
    (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat (native_re_mult r) r))
      (SmtValue.RegLan
        (native_re_concat r (native_re_mult r))) := by
  apply RuleProofs.smt_value_rel_reglan_of_valid_eq
  intro xs hValid
  rw [RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid,
    RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid]
  have hsimpa :=
    nativeListInRe_mk_star_swap xs r
  try simp [native_re_concat, native_re_mult] at hsimpa ⊢
  exact hsimpa

theorem smt_value_rel_re_concat_star_repeat_core
    (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat (native_re_mult r) (native_re_mult r)))
      (SmtValue.RegLan (native_re_mult r)) := by
  apply RuleProofs.smt_value_rel_reglan_of_valid_eq
  intro xs hValid
  rw [RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid,
    RuleProofs.native_str_in_re_eq_nativeListInRe xs _ hValid]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs (native_re_mk_star r) (native_re_mk_star r)).1
        (by have hsimpa := h; (try simp [native_re_concat, native_re_mult] at hsimpa ⊢); exact hsimpa) with
      ⟨left, right, hAppend, hLeft, hRight⟩
    have hsimpa :=
      RuleProofs.nativeListInRe_mk_star_append left right r hLeft hRight
    try simp [native_re_mult, ← hAppend] at hsimpa ⊢
    exact hsimpa
  · intro h
    have hNil : nativeListInRe [] (native_re_mk_star r) = true :=
      RuleProofs.nativeListInRe_nil_mk_star r
    have hsimpa :=
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
        xs (native_re_mk_star r) (native_re_mk_star r)).2
        ⟨[], xs, by simp, hNil, by have hsimpa := h; (try simp [native_re_mult] at hsimpa ⊢); exact hsimpa⟩
    try simp [native_re_concat, native_re_mult] at hsimpa ⊢
    exact hsimpa

theorem smt_value_rel_re_concat_star_repeat
    (pre r suffix : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat pre
          (native_re_concat (native_re_mult r)
            (native_re_concat (native_re_mult r) suffix))))
      (SmtValue.RegLan
        (native_re_concat pre
          (native_re_concat (native_re_mult r) suffix))) := by
  have hAssoc := RuleProofs.smt_value_rel_symm _ _
    (smt_value_rel_re_concat_assoc
      (native_re_mult r) (native_re_mult r) suffix)
  have hCollapse := smt_value_rel_re_concat_congr
    (smt_value_rel_re_concat_star_repeat_core r)
    (RuleProofs.smt_value_rel_refl (SmtValue.RegLan suffix))
  have hTail := RuleProofs.smt_value_rel_trans _ _ _ hAssoc hCollapse
  exact smt_value_rel_re_concat_congr
    (RuleProofs.smt_value_rel_refl (SmtValue.RegLan pre)) hTail

theorem smt_value_rel_re_concat_star_swap
    (pre r suffix : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat pre
          (native_re_concat (native_re_mult r)
            (native_re_concat r suffix))))
      (SmtValue.RegLan
        (native_re_concat pre
          (native_re_concat r
            (native_re_concat (native_re_mult r) suffix)))) := by
  have hAssocLeft := RuleProofs.smt_value_rel_symm _ _
    (smt_value_rel_re_concat_assoc (native_re_mult r) r suffix)
  have hSwap := smt_value_rel_re_concat_congr
    (smt_value_rel_re_concat_star_swap_core r)
    (RuleProofs.smt_value_rel_refl (SmtValue.RegLan suffix))
  have hAssocRight :=
    smt_value_rel_re_concat_assoc r (native_re_mult r) suffix
  have hTail := RuleProofs.smt_value_rel_trans _ _ _ hAssocLeft <|
    RuleProofs.smt_value_rel_trans _ _ _ hSwap hAssocRight
  exact smt_value_rel_re_concat_congr
    (RuleProofs.smt_value_rel_refl (SmtValue.RegLan pre)) hTail

theorem native_includes_union_of
    {sup r s : SmtRegLan}
    (hr : NativeIncludes sup r) (hs : NativeIncludes sup s) :
    NativeIncludes sup (native_re_union r s) := by
  intro str hValid hMem
  rw [native_str_in_re_re_union] at hMem
  simp only [Bool.or_eq_true] at hMem
  rcases hMem with hMem | hMem
  · exact hr str hValid hMem
  · exact hs str hValid hMem

theorem native_includes_star_epsilon (r : SmtRegLan) :
    NativeIncludes (native_re_mult r) (native_str_to_re []) := by
  intro str hValid hMem
  have hEq : str = [] :=
    native_str_in_re_str_to_re_eq hValid hMem
  subst str
  have hNil : nativeListInRe [] (native_re_mk_star r) = true :=
    nativeListInRe_nil_mk_star r
  have hsimpa := hNil
  try simp [native_str_in_re, native_string_valid, native_re_mult, nativeListInRe] at hsimpa ⊢
  exact hsimpa

theorem native_includes_star_closure
    {r s : SmtRegLan}
    (h : NativeIncludes (native_re_mult r) s) :
    NativeIncludes (native_re_mult r) (native_re_mult s) := by
  have hStar := native_includes_star_mono h
  cases r <;>
    simpa [native_re_mult, native_re_mk_star] using hStar

theorem smt_value_rel_re_mult_congr
    {r s : SmtRegLan}
    (h : RuleProofs.smt_value_rel
      (SmtValue.RegLan r) (SmtValue.RegLan s)) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_mult r))
      (SmtValue.RegLan (native_re_mult s)) := by
  exact smt_value_rel_of_native_includes
    (native_includes_star_mono (native_includes_of_smt_value_rel h))
    (native_includes_star_mono (native_includes_of_smt_value_rel
      (RuleProofs.smt_value_rel_symm _ _ h)))

theorem smt_value_rel_re_star_union_allchar
    (r s : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_mult
          (native_re_union r (native_re_union native_re_allchar s))))
      (SmtValue.RegLan native_re_all) := by
  have hAllchar :
      NativeIncludes
        (native_re_union r (native_re_union native_re_allchar s))
        native_re_allchar :=
    native_includes_trans
      (native_includes_union_right r
        (native_re_union native_re_allchar s))
      (native_includes_union_left native_re_allchar s)
  apply smt_value_rel_of_native_includes
  · simpa [native_re_all, native_re_mult, native_re_allchar] using
      native_includes_star_mono hAllchar
  · exact native_includes_re_all
      (native_re_mult
        (native_re_union r (native_re_union native_re_allchar s)))

theorem smt_value_rel_re_star_union_drop_epsilon
    (r s : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_mult
          (native_re_union r
            (native_re_union (native_str_to_re []) s))))
      (SmtValue.RegLan (native_re_mult (native_re_union r s))) := by
  let base := native_re_union r s
  let withEpsilon :=
    native_re_union r (native_re_union (native_str_to_re []) s)
  have hBaseToWith : NativeIncludes withEpsilon base :=
    native_includes_union_of
      (native_includes_union_left r
        (native_re_union (native_str_to_re []) s))
      (native_includes_trans
        (native_includes_union_right r
          (native_re_union (native_str_to_re []) s))
        (native_includes_union_right (native_str_to_re []) s))
  have hRToStarBase : NativeIncludes (native_re_mult base) r :=
    native_includes_trans (native_includes_star_self base)
      (native_includes_union_left r s)
  have hSToStarBase : NativeIncludes (native_re_mult base) s :=
    native_includes_trans (native_includes_star_self base)
      (native_includes_union_right r s)
  have hWithToStarBase : NativeIncludes (native_re_mult base) withEpsilon :=
    native_includes_union_of hRToStarBase
      (native_includes_union_of
        (native_includes_star_epsilon base) hSToStarBase)
  exact smt_value_rel_of_native_includes
    (native_includes_star_mono hBaseToWith)
    (native_includes_star_closure hWithToStarBase)

end RuleProofs

namespace RegexRewriteSupport

theorem list_concat_lists_of_ne_stuck (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have ha := RuleProofs.eo_requires_eq_of_ne_stuck
    (__eo_is_list f a) (Term.Boolean true)
    (__eo_requires (__eo_is_list f b) (Term.Boolean true)
      (__eo_list_concat_rec a b)) hReq
  have hReqEq := RuleProofs.eo_requires_result_eq_of_ne_stuck
    (__eo_is_list f a) (Term.Boolean true)
    (__eo_requires (__eo_is_list f b) (Term.Boolean true)
      (__eo_list_concat_rec a b)) hReq
  have hTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck := by
    rwa [hReqEq] at hReq
  have hb := RuleProofs.eo_requires_eq_of_ne_stuck
    (__eo_is_list f b) (Term.Boolean true)
    (__eo_list_concat_rec a b) hTail
  exact ⟨ha, hb⟩

theorem reConcat_list_smt_typeof_reglan_of_non_none (t : Term) :
    __eo_is_list (Term.UOp UserOp.re_concat) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro hList hNN
  cases t <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList ⊢
  next f y =>
    cases f <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList ⊢
    next op =>
      cases op <;> try { simp [__eo_is_list_nil] at hList }
      case str_to_re =>
        cases y <;> try { simp [__eo_is_list_nil, __smtx_typeof] at hList }
        case String cs =>
          cases cs with
          | nil =>
              change __smtx_typeof
                  (SmtTerm.str_to_re (SmtTerm.String [])) = SmtType.RegLan
              rw [typeof_str_to_re_eq]
              decide +kernel
          | cons c cs =>
              simp [__eo_is_list_nil] at hList
    next g x =>
      rw [← hList.1] at hNN ⊢
      have hArgs := reglan_binop_args_of_non_none
        (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt x) (__eo_to_smt y)) hNN
      change __smtx_typeof
          (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan
      rw [typeof_re_concat_eq]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]

theorem reUnion_list_smt_typeof_reglan_of_non_none (t : Term) :
    __eo_is_list (Term.UOp UserOp.re_union) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro hList hNN
  cases t <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList ⊢
  next op =>
    cases op <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, __smtx_typeof] at hList ⊢
  next f y =>
    cases f <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList ⊢
    next g x =>
      rw [← hList.1] at hNN ⊢
      have hArgs := reglan_binop_args_of_non_none
        (op := SmtTerm.re_union)
        (typeof_re_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN
      change __smtx_typeof
          (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan
      rw [typeof_re_union_eq]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]

end RegexRewriteSupport
