module

public import Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private abbrev mkStrInRe (s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r

private abbrev mkStrConcat (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) t

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, native_not, hxOk]

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  have hxNe : y ≠ Term.Stuck := by
    intro hy
    subst y
    simp at hxOk
  exact hxNe hx

private theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h hStuck
  have hResult := eo_requires_result_eq_of_ne_stuck x y z h
  exact h (by rw [hResult, hStuck])

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem str_in_re_args_smt_types_of_has_translation
    (s r : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hTrans
  have hNN :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) ≠
      SmtType.None
    exact hTrans
  exact seq_char_reglan_args_of_non_none
    (op := SmtTerm.str_in_re) (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNN

/- The shared regex support module now owns the generic membership algebra.

private def nativeListInRe : List native_Char -> SmtRegLan -> native_Bool
  | [], r => native_re_nullable r
  | c :: cs, r => nativeListInRe cs (native_re_deriv (SmtValue.Char c) r)

private theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

private theorem native_re_nullable_mk_union (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union, native_re_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_mk_union_self (r : SmtRegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union, native_re_union, native_re_union]

private theorem native_re_mk_union_eq_union_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union, native_re_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self]
            simp [nativeListInRe]
          · rw [native_re_mk_union_eq_union_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_mk_inter_self (r : SmtRegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter, native_re_inter, native_re_inter]

private theorem native_re_mk_inter_eq_inter_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter, native_re_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_nullable_mk_inter (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem nativeListInRe_mk_inter :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self]
            simp [nativeListInRe]
          · rw [native_re_mk_inter_eq_inter_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_nullable_mk_concat (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat, native_re_nullable]

private theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

private theorem nativeListInRe_mk_concat_epsilon_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.epsilon) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

private theorem native_re_mk_concat_eq_concat_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat, native_re_concat] at hrEmpty hsEmpty hrEps hsEps ⊢

private theorem nativeListInRe_deriv_mk_concat
    (xs : List native_Char) (c : native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_deriv c (native_re_mk_concat r s)) =
      nativeListInRe xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) := by
  by_cases hrEmpty : r = SmtRegLan.empty
  · subst r
    simp [native_re_mk_concat, native_re_concat, native_re_deriv, native_re_nullable,
      nativeListInRe_mk_union, nativeListInRe_empty]
  · by_cases hsEmpty : s = SmtRegLan.empty
    · subst s
      have hL :
          nativeListInRe xs
            (native_re_deriv c (native_re_mk_concat r SmtRegLan.empty)) =
            false := by
        simp [native_re_mk_concat, native_re_concat, native_re_deriv, nativeListInRe_empty]
      rw [hL]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat_empty_right]
      simp [native_re_deriv, nativeListInRe_empty]
    · by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_concat, native_re_deriv, native_re_nullable,
          nativeListInRe_mk_union, nativeListInRe_empty]
      · by_cases hsEps : s = SmtRegLan.epsilon
        · subst s
          have hMk : native_re_mk_concat r SmtRegLan.epsilon = r := by
            cases r <;> simp [native_re_mk_concat, native_re_concat, native_re_concat] at hrEmpty hrEps ⊢
          rw [hMk]
          rw [nativeListInRe_mk_union]
          rw [nativeListInRe_mk_concat_epsilon_right]
          simp [native_re_deriv, nativeListInRe_empty]
        · have hMk :=
            native_re_mk_concat_eq_concat_of_ne r s hrEmpty hsEmpty hrEps hsEps
          rw [hMk]
          simp [native_re_deriv, nativeListInRe_mk_union]

private def nativeListInReConcat :
    List native_Char -> SmtRegLan -> SmtRegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

private theorem nativeListInRe_mk_concat :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_concat r s) =
        nativeListInReConcat xs r s
  | [], r, s => by
      simp [nativeListInRe, nativeListInReConcat,
        native_re_nullable_mk_concat]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_deriv c (native_re_mk_concat r s)) =
          ((native_re_nullable r &&
              nativeListInRe cs (native_re_deriv c s)) ||
            nativeListInReConcat cs (native_re_deriv c r) s)
      rw [nativeListInRe_deriv_mk_concat cs c r s]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat cs (native_re_deriv c r) s]
      cases hNullable : native_re_nullable r <;>
        simp [nativeListInRe_empty, Bool.or_comm]

private theorem nativeListInReConcat_true_iff_exists_append :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInReConcat xs r s = true ↔
        ∃ xs₁ xs₂ : List native_Char,
          xs₁ ++ xs₂ = xs ∧
            nativeListInRe xs₁ r = true ∧
            nativeListInRe xs₂ s = true
  | [], r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.and_eq_true] at h
        exact ⟨[], [], by rfl, by simpa [nativeListInRe] using h.1,
          by simpa [nativeListInRe] using h.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [nativeListInReConcat, nativeListInRe] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with hHead | hTail
        · exact ⟨[], c :: cs, by rfl,
            by simpa [nativeListInRe] using hHead.1, hHead.2⟩
        · have hTailExists :=
            (nativeListInReConcat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by simpa [nativeListInRe] using hLeft, hRight⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp at hAppend
            | cons _ _ =>
                cases hAppend
                have hNullable : native_re_nullable r = true := by
                  simpa [nativeListInRe] using hLeft
                simp [nativeListInReConcat,
                  hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                nativeListInRe ds (native_re_deriv c r) = true := by
              simpa [nativeListInRe] using hLeft
            have hTail :
                nativeListInReConcat (ds ++ xs₂) (native_re_deriv c r) s =
                  true :=
              (nativeListInReConcat_true_iff_exists_append (ds ++ xs₂)
                (native_re_deriv c r) s).2
                ⟨ds, xs₂, by rfl, hLeftDeriv, hRight⟩
            simp [nativeListInReConcat, hTail]

private theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

-/

/- Length facts for regex atoms and string literals are shared by RegexSupport.

private theorem nativeListInRe_char_true_length
    (xs : List native_Char) (c : native_Char) :
    nativeListInRe xs (SmtRegLan.char c) = true ->
    xs.length = 1 := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable]
  | cons d ds =>
      cases ds with
      | nil =>
          intro _; rfl
      | cons e es =>
          intro h
          by_cases hMatch :
              (native_char_valid d = true ∧ native_char_valid c = true) ∧ d = c
          · simp [nativeListInRe, native_re_deriv, hMatch] at h
            have hEmpty := nativeListInRe_empty es
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at h
            simp at h
          · simp [nativeListInRe, native_re_deriv, hMatch] at h
            have hEmpty := nativeListInRe_empty es
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at h
            simp at h

private theorem nativeListInRe_allchar_true_length
    (xs : List native_Char) :
    nativeListInRe xs native_re_allchar = true ->
    xs.length = 1 := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_allchar, native_re_nullable]
  | cons c cs =>
      cases cs with
      | nil =>
          intro _; rfl
      | cons d ds =>
          intro h
          cases hValid : native_char_valid c
          · simp [nativeListInRe, native_re_allchar, native_re_deriv, hValid
              ] at h
            have hEmpty := nativeListInRe_empty ds
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at h
            simp at h
          · simp [nativeListInRe, native_re_allchar, native_re_deriv, hValid
              ] at h
            have hEmpty := nativeListInRe_empty ds
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at h
            simp at h

private theorem nativeListInRe_range_true_length
    (xs : List native_Char) (lo hi : native_Char) :
    nativeListInRe xs (SmtRegLan.range lo hi) = true ->
    xs.length = 1 := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable]
  | cons c cs =>
      cases cs with
      | nil =>
          intro _; rfl
      | cons d ds =>
          intro h
          simp [nativeListInRe, native_re_deriv] at h
          split at h
          · simp [native_re_deriv] at h
            have hEmpty := nativeListInRe_empty ds
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at h
            simp at h
          · simp [native_re_deriv] at h
            have hEmpty := nativeListInRe_empty ds
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at h
            simp at h

private theorem nativeListInRe_re_range_true_length
    (xs : List native_Char) (lo hi : native_String) :
    nativeListInRe xs (native_re_range lo hi) = true ->
    xs.length = 1 := by
  cases lo with
  | nil =>
      simp [native_re_range, nativeListInRe_empty]
  | cons c loTail =>
      cases loTail with
      | nil =>
          cases hi with
          | nil =>
              simp [native_re_range, nativeListInRe_empty]
          | cons d hiTail =>
              cases hiTail with
              | nil =>
                  exact nativeListInRe_range_true_length xs c d
              | cons _ _ =>
                  simp [native_re_range, nativeListInRe_empty]
      | cons _ _ =>
          simp [native_re_range, nativeListInRe_empty]

private theorem nativeListInRe_re_of_list_true_length :
    (pat xs : List native_Char) ->
      nativeListInRe xs (impl_native_re_of_list pat) = true ->
      xs.length = pat.length
  | [], xs, h => by
      cases xs with
      | nil =>
          rfl
      | cons c cs =>
          simp [impl_native_re_of_list, nativeListInRe,
            native_re_deriv] at h
          have hEmpty := nativeListInRe_empty cs
          unfold nativeListInRe at hEmpty
          rw [hEmpty] at h
          simp at h
  | c :: pat, xs, h => by
      rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
          (SmtRegLan.char c) (impl_native_re_of_list pat)).1
                  (by simpa [impl_native_re_of_list] using h) with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftLen : left.length = 1 :=
        nativeListInRe_char_true_length left c hLeft
      have hRightLen : right.length = pat.length :=
        nativeListInRe_re_of_list_true_length pat right hRight
      rw [← hAppend]
      simp [hLeftLen, hRightLen, Nat.add_comm]

private theorem nativeListInRe_str_to_re_true_length
    (pat xs : List native_Char) :
    nativeListInRe xs (native_str_to_re pat) = true ->
    xs.length = pat.length := by
  simpa [native_str_to_re] using nativeListInRe_re_of_list_true_length pat xs

-/

private theorem nativeListInRe_allchar_true_length
    (xs : List native_Char)
    (h : nativeListInRe xs native_re_allchar = true) :
    xs.length = 1 :=
  (nativeListInRe_allchar_true_iff xs).1 h |>.1

private theorem nativeListInRe_str_to_re_true_length
    (pat xs : List native_Char)
    (h : nativeListInRe xs
      (native_str_to_re (impl_native_string_to_values pat)) = true) :
    xs.length = pat.length :=
  nativeListInRe_str_to_re_string_true_length pat xs h

private theorem nativeListInRe_re_mult_empty :
    (xs : List native_Char) ->
      nativeListInRe xs (native_re_mult SmtRegLan.empty) = decide (xs = [])
  | [] => by
      simp [native_re_mult, nativeListInRe, native_re_nullable]
  | c :: cs => by
      simpa [native_re_mult, native_re_mk_star, native_re_mult, nativeListInRe, native_re_deriv,
        nativeListInRe_empty] using nativeListInRe_empty cs

private theorem nativeListInRe_re_mult_raw_eq_all_singletons
    (r : SmtRegLan)
    (hLen : ∀ xs : List native_Char, nativeListInRe xs r = true -> xs.length = 1)
    (hStar : native_re_mult r = SmtRegLan.star r) :
    (xs : List native_Char) ->
      nativeListInRe xs (native_re_mult r) =
        xs.all (fun c => nativeListInRe [c] r)
  | [] => by
      rw [hStar]
      simp [nativeListInRe, native_re_nullable]
  | c :: cs => by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h
        rw [hStar] at h
        change
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
            true at h
        rcases (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).1 h with
          ⟨left, right, hAppend, hLeft, hRight⟩
        have hPrefix : nativeListInRe (c :: left) r = true := by
          simpa [nativeListInRe] using hLeft
        have hLeftNil : left = [] := by
          have hLenPrefix := hLen (c :: left) hPrefix
          cases left with
          | nil => rfl
          | cons d ds =>
              simp at hLenPrefix
        subst left
        simp at hAppend
        subst right
        have hCsStar : nativeListInRe cs (native_re_mult r) = true := by
          rw [hStar]
          exact hRight
        have hAllCs : cs.all (fun c => nativeListInRe [c] r) = true := by
          rw [← nativeListInRe_re_mult_raw_eq_all_singletons r hLen hStar cs]
          exact hCsStar
        have hC : nativeListInRe [c] r = true := by
          simpa using hPrefix
        simp [hC, hAllCs]
      · intro h
        have hPair :
            nativeListInRe [c] r = true ∧
              cs.all (fun c => nativeListInRe [c] r) = true := by
          simpa [Bool.and_eq_true] using h
        have hC : nativeListInRe [c] r = true := hPair.1
        have hAllCs : cs.all (fun c => nativeListInRe [c] r) = true := hPair.2
        have hCsStar : nativeListInRe cs (SmtRegLan.star r) = true := by
          have hCs :
              nativeListInRe cs (native_re_mult r) = true := by
            rw [nativeListInRe_re_mult_raw_eq_all_singletons r hLen hStar cs]
            exact hAllCs
          rwa [hStar] at hCs
        rw [hStar]
        change
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
            true
        exact (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨[], cs, by simp, by simpa [nativeListInRe] using hC, hCsStar⟩

private theorem nativeListInRe_re_mult_eq_all_singletons
    (r : SmtRegLan)
    (hLen : ∀ xs : List native_Char, nativeListInRe xs r = true -> xs.length = 1)
    (xs : List native_Char) :
    nativeListInRe xs (native_re_mult r) =
      xs.all (fun c => nativeListInRe [c] r) := by
  cases r with
  | empty =>
      cases xs with
      | nil => simp [nativeListInRe_re_mult_empty]
      | cons c cs =>
          simp [nativeListInRe_re_mult_empty, nativeListInRe_empty]
  | epsilon =>
      have hBad := hLen [] (by simp [nativeListInRe, native_re_nullable])
      have : (0 : Nat) = 1 := by simpa using hBad
      omega
  | star r =>
      have hBad := hLen [] (by simp [nativeListInRe, native_re_nullable])
      have : (0 : Nat) = 1 := by simpa using hBad
      omega
  | char c =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons (SmtRegLan.char c)
        hLen rfl xs
  | range lo hi =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons (SmtRegLan.range lo hi)
        hLen rfl xs
  | allchar =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons SmtRegLan.allchar
        hLen rfl xs
  | concat r s =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons (SmtRegLan.concat r s)
        hLen rfl xs
  | union r s =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons (SmtRegLan.union r s)
        hLen rfl xs
  | inter r s =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons (SmtRegLan.inter r s)
        hLen rfl xs
  | comp r =>
      exact nativeListInRe_re_mult_raw_eq_all_singletons (SmtRegLan.comp r)
        hLen rfl xs

private theorem nativeListInRe_re_mult_append
    (r : SmtRegLan)
    (hLen : ∀ xs : List native_Char, nativeListInRe xs r = true -> xs.length = 1)
    (xs ys : List native_Char) :
    nativeListInRe (xs ++ ys) (native_re_mult r) =
      (nativeListInRe xs (native_re_mult r) &&
        nativeListInRe ys (native_re_mult r)) := by
  rw [nativeListInRe_re_mult_eq_all_singletons r hLen (xs ++ ys)]
  rw [nativeListInRe_re_mult_eq_all_singletons r hLen xs]
  rw [nativeListInRe_re_mult_eq_all_singletons r hLen ys]
  simp [List.all_append]

private theorem native_str_in_re_re_mult_append
    (r : SmtRegLan)
    (hLen : ∀ xs : List native_Char, nativeListInRe xs r = true -> xs.length = 1)
    (xs ys : native_String)
    (hxs : native_string_valid xs = true)
    (hys : native_string_valid ys = true) :
    native_str_in_re (xs ++ ys) (native_re_mult r) =
      (native_str_in_re xs (native_re_mult r) &&
        native_str_in_re ys (native_re_mult r)) := by
  have hAppend : native_string_valid (xs ++ ys) = true :=
    native_string_valid_append hxs hys
  simp [native_str_in_re, hxs, hys, hAppend]
  exact nativeListInRe_re_mult_append r hLen xs ys

private theorem native_unpack_seq_pack (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => by rfl
  | x :: xs => by simp [native_pack_seq, native_unpack_seq, native_unpack_seq_pack T xs]

private theorem native_unpack_string_pack_concat
    (T : SmtType) (ss1 ss2 : SmtSeq) :
    native_unpack_string
        (native_pack_seq T (native_seq_concat (native_unpack_seq ss1) (native_unpack_seq ss2))) =
      native_unpack_string ss1 ++ native_unpack_string ss2 := by
  simp [native_unpack_string, native_seq_concat, native_unpack_seq_pack, List.map_append]

private theorem eo_mk_apply_right_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem eo_add_eq_numeral_cases (x y : Term) (n : native_Int) :
    __eo_add x y = Term.Numeral n ->
    ∃ m k : native_Int,
      x = Term.Numeral m ∧ y = Term.Numeral k ∧ native_zplus m k = n := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_add, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at h
  case Numeral.Numeral m k =>
    exact ⟨m, k, rfl, rfl, h⟩
  case Binary.Binary =>
    split at h <;> simp at h

private theorem fixed_len_re_union_right_not_none
    (r₁ r₂ : Term) (n : native_Int)
    (hNone : r₂ ≠ Term.UOp UserOp.re_none) :
    __str_fixed_len_re
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r₁) r₂) =
      Term.Numeral n ->
    __eo_requires (__str_fixed_len_re r₂) (__str_fixed_len_re r₁)
        (__str_fixed_len_re r₁) =
      Term.Numeral n := by
  intro h
  cases r₂ <;>
    simp [__str_fixed_len_re, __eo_eq, native_ite, native_teq
      ] at h hNone ⊢
  all_goals try exact h
  case UOp op =>
    cases op <;>
      simp [__str_fixed_len_re
        ] at h hNone ⊢
    all_goals try exact h

private theorem fixed_len_re_inter_right_not_all
    (r₁ r₂ : Term) (n : native_Int)
    (hAll : r₂ ≠ Term.UOp UserOp.re_all) :
    __str_fixed_len_re
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r₁) r₂) =
      Term.Numeral n ->
    __eo_requires (__str_fixed_len_re r₂) (__str_fixed_len_re r₁)
        (__str_fixed_len_re r₁) =
      Term.Numeral n := by
  intro h
  cases r₂ <;>
    simp [__str_fixed_len_re, __eo_eq, native_ite, native_teq
      ] at h hAll ⊢
  all_goals try exact h
  case UOp op =>
    cases op <;>
      simp [__str_fixed_len_re
        ] at h hAll ⊢
    all_goals try exact h

private theorem fixed_len_re_sound
    (M : SmtModel) :
    (r : Term) -> (rv : SmtRegLan) -> (n : native_Int) ->
      __str_fixed_len_re r = Term.Numeral n ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      ∀ xs : List native_Char, nativeListInRe xs rv = true -> Int.ofNat xs.length = n
  | Term.UOp UserOp.re_allchar, rv, n, hFixed, hEval, xs, hIn => by
      simp [__str_fixed_len_re] at hFixed
      subst n
      change __smtx_model_eval M SmtTerm.re_allchar = SmtValue.RegLan rv at hEval
      rw [__smtx_model_eval.eq_104] at hEval
      simp at hEval
      subst rv
      have hLen := nativeListInRe_allchar_true_length xs hIn
      rw [hLen]
      rfl
  | Term.Apply (Term.UOp UserOp.str_to_re) (Term.String pat), rv, n, hFixed, hEval, xs, hIn => by
      simp [__str_fixed_len_re, __eo_len] at hFixed
      subst n
      change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String pat)) =
        SmtValue.RegLan rv at hEval
      rw [__smtx_model_eval.eq_107, __smtx_model_eval.eq_4] at hEval
      simp [__smtx_model_eval_str_to_re, native_pack_string,
        native_unpack_seq_pack] at hEval
      subst rv
      have hIn' : nativeListInRe xs (native_str_to_re pat) = true := by
        have hMap :
            List.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) pat = pat := by
          clear hIn
          induction pat with
          | nil => rfl
          | cons c cs ih =>
              simp [Function.comp, impl_native_ssm_char_of_value, ih]
        exact hIn
      have hLen := nativeListInRe_str_to_re_true_length pat xs hIn'
      simpa [native_str_len] using congrArg Int.ofNat hLen
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_range) lo) hi, rv, n, hFixed, hEval, xs, hIn => by
      simp [__str_fixed_len_re] at hFixed
      subst n
      change __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt lo) (__eo_to_smt hi)) =
        SmtValue.RegLan rv at hEval
      rw [__smtx_model_eval.eq_113] at hEval
      cases hlo : __smtx_model_eval M (__eo_to_smt lo) with
      | Seq slo =>
          cases hhi : __smtx_model_eval M (__eo_to_smt hi) with
          | Seq shi =>
              simp [__smtx_model_eval_re_range, hlo, hhi] at hEval
              subst rv
              have hLen := nativeListInRe_re_range_true_length xs
                (native_unpack_seq slo) (native_unpack_seq shi) hIn
              rw [hLen]
              rfl
          | _ =>
              simp [__smtx_model_eval_re_range, hlo, hhi] at hEval
      | _ =>
          cases hhi : __smtx_model_eval M (__eo_to_smt hi) <;>
            simp [__smtx_model_eval_re_range, hlo, hhi] at hEval
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r₁) r₂, rv, n, hFixed, hEval, xs, hIn => by
      change __eo_add (__str_fixed_len_re r₁) (__str_fixed_len_re r₂) =
        Term.Numeral n at hFixed
      rcases eo_add_eq_numeral_cases (__str_fixed_len_re r₁)
          (__str_fixed_len_re r₂) n hFixed with
        ⟨n₁, n₂, hFixed₁, hFixed₂, hAdd⟩
      change __smtx_model_eval M
          (SmtTerm.re_concat (__eo_to_smt r₁) (__eo_to_smt r₂)) =
        SmtValue.RegLan rv at hEval
      rw [__smtx_model_eval.eq_114] at hEval
      cases hEval₁ : __smtx_model_eval M (__eo_to_smt r₁) with
      | RegLan rv₁ =>
          cases hEval₂ : __smtx_model_eval M (__eo_to_smt r₂) with
          | RegLan rv₂ =>
              simp [__smtx_model_eval_re_concat, hEval₁, hEval₂] at hEval
              subst rv
              rcases (nativeListInRe_mk_concat_true_iff_exists_append xs rv₁ rv₂).1
                  (by exact hIn) with
                ⟨left, right, hAppend, hLeft, hRight⟩
              have hLeftLen :=
                fixed_len_re_sound M r₁ rv₁ n₁ hFixed₁ hEval₁ left hLeft
              have hRightLen :=
                fixed_len_re_sound M r₂ rv₂ n₂ hFixed₂ hEval₂ right hRight
              calc
                Int.ofNat xs.length = Int.ofNat (left ++ right).length := by
                  rw [hAppend]
                _ = Int.ofNat left.length + Int.ofNat right.length := by
                  simp
                _ = n₁ + n₂ := by
                  rw [hLeftLen, hRightLen]
                _ = n := by
                  simpa [native_zplus] using hAdd
          | _ =>
              simp [__smtx_model_eval_re_concat, hEval₁, hEval₂] at hEval
      | _ =>
          cases hEval₂ : __smtx_model_eval M (__eo_to_smt r₂) <;>
            simp [__smtx_model_eval_re_concat, hEval₁, hEval₂] at hEval
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r₁) r₂, rv, n, hFixed, hEval, xs, hIn => by
      by_cases hNone : r₂ = Term.UOp UserOp.re_none
      · subst r₂
        simp [__str_fixed_len_re, __eo_eq, native_ite, native_teq] at hFixed
        change __smtx_model_eval M
            (SmtTerm.re_union (__eo_to_smt r₁) SmtTerm.re_none) =
          SmtValue.RegLan rv at hEval
        rw [__smtx_model_eval.eq_116, __smtx_model_eval.eq_105] at hEval
        cases hEval₁ : __smtx_model_eval M (__eo_to_smt r₁) with
        | RegLan rv₁ =>
            simp [__smtx_model_eval_re_union, hEval₁] at hEval
            subst rv
            have hInLeft : nativeListInRe xs rv₁ = true := by
              have hMk : native_re_mk_union rv₁ SmtRegLan.empty = rv₁ := by
                cases rv₁ <;> simp [native_re_mk_union, native_re_union, native_re_union]
              change nativeListInRe xs
                (native_re_mk_union rv₁ SmtRegLan.empty) = true at hIn
              rwa [hMk] at hIn
            exact fixed_len_re_sound M r₁ rv₁ n hFixed hEval₁ xs
              hInLeft
        | _ =>
            simp [__smtx_model_eval_re_union, hEval₁] at hEval
      · have hFixed' :=
          fixed_len_re_union_right_not_none r₁ r₂ n hNone hFixed
        let len₁ := __str_fixed_len_re r₁
        let req := __eo_requires (__str_fixed_len_re r₂) len₁ len₁
        change req = Term.Numeral n at hFixed'
        have hReqNe : req ≠ Term.Stuck := by
          intro h
          rw [h] at hFixed'
          simp at hFixed'
        have hReqResult : req = len₁ :=
          eo_requires_result_eq_of_ne_stuck (__str_fixed_len_re r₂) len₁ len₁ hReqNe
        have hReqEq : __str_fixed_len_re r₂ = len₁ :=
          eo_requires_eq_of_ne_stuck (__str_fixed_len_re r₂) len₁ len₁ hReqNe
        have hFixed₁ : __str_fixed_len_re r₁ = Term.Numeral n := by
          simpa [len₁, req, hReqResult] using hFixed'
        have hFixed₂ : __str_fixed_len_re r₂ = Term.Numeral n := by
          rw [hReqEq]
          exact hFixed₁
        change __smtx_model_eval M
            (SmtTerm.re_union (__eo_to_smt r₁) (__eo_to_smt r₂)) =
          SmtValue.RegLan rv at hEval
        rw [__smtx_model_eval.eq_116] at hEval
        cases hEval₁ : __smtx_model_eval M (__eo_to_smt r₁) with
        | RegLan rv₁ =>
            cases hEval₂ : __smtx_model_eval M (__eo_to_smt r₂) with
            | RegLan rv₂ =>
                simp [__smtx_model_eval_re_union, hEval₁, hEval₂] at hEval
                subst rv
                have hUnion := nativeListInRe_mk_union xs rv₁ rv₂
                change nativeListInRe xs
                  (native_re_mk_union rv₁ rv₂) = true at hIn
                rw [hUnion] at hIn
                have hOr :
                    nativeListInRe xs rv₁ = true ∨
                      nativeListInRe xs rv₂ = true := by
                  simpa [Bool.or_eq_true] using hIn
                rcases hOr with hLeft | hRight
                · exact fixed_len_re_sound M r₁ rv₁ n hFixed₁ hEval₁ xs hLeft
                · exact fixed_len_re_sound M r₂ rv₂ n hFixed₂ hEval₂ xs hRight
            | _ =>
                simp [__smtx_model_eval_re_union, hEval₁, hEval₂] at hEval
        | _ =>
            cases hEval₂ : __smtx_model_eval M (__eo_to_smt r₂) <;>
              simp [__smtx_model_eval_re_union, hEval₁, hEval₂] at hEval
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r₁) r₂, rv, n, hFixed, hEval, xs, hIn => by
      by_cases hAll : r₂ = Term.UOp UserOp.re_all
      · subst r₂
        simp [__str_fixed_len_re, __eo_eq, native_ite, native_teq] at hFixed
        change __smtx_model_eval M
            (SmtTerm.re_inter (__eo_to_smt r₁) SmtTerm.re_all) =
          SmtValue.RegLan rv at hEval
        rw [__smtx_model_eval.eq_115, __smtx_model_eval.eq_106] at hEval
        cases hEval₁ : __smtx_model_eval M (__eo_to_smt r₁) with
        | RegLan rv₁ =>
            simp [__smtx_model_eval_re_inter, hEval₁] at hEval
            subst rv
            have hInter := nativeListInRe_mk_inter xs rv₁ native_re_all
            change nativeListInRe xs
              (native_re_mk_inter rv₁ native_re_all) = true at hIn
            rw [hInter] at hIn
            have hPair :
                nativeListInRe xs rv₁ = true ∧
                  nativeListInRe xs native_re_all = true := by
              simpa [Bool.and_eq_true] using hIn
            exact fixed_len_re_sound M r₁ rv₁ n hFixed hEval₁ xs
              hPair.1
        | _ =>
            simp [__smtx_model_eval_re_inter, hEval₁] at hEval
      · have hFixed' :=
          fixed_len_re_inter_right_not_all r₁ r₂ n hAll hFixed
        let len₁ := __str_fixed_len_re r₁
        let req := __eo_requires (__str_fixed_len_re r₂) len₁ len₁
        change req = Term.Numeral n at hFixed'
        have hReqNe : req ≠ Term.Stuck := by
          intro h
          rw [h] at hFixed'
          simp at hFixed'
        have hReqResult : req = len₁ :=
          eo_requires_result_eq_of_ne_stuck (__str_fixed_len_re r₂) len₁ len₁ hReqNe
        have hReqEq : __str_fixed_len_re r₂ = len₁ :=
          eo_requires_eq_of_ne_stuck (__str_fixed_len_re r₂) len₁ len₁ hReqNe
        have hFixed₁ : __str_fixed_len_re r₁ = Term.Numeral n := by
          simpa [len₁, req, hReqResult] using hFixed'
        have hFixed₂ : __str_fixed_len_re r₂ = Term.Numeral n := by
          rw [hReqEq]
          exact hFixed₁
        change __smtx_model_eval M
            (SmtTerm.re_inter (__eo_to_smt r₁) (__eo_to_smt r₂)) =
          SmtValue.RegLan rv at hEval
        rw [__smtx_model_eval.eq_115] at hEval
        cases hEval₁ : __smtx_model_eval M (__eo_to_smt r₁) with
        | RegLan rv₁ =>
            cases hEval₂ : __smtx_model_eval M (__eo_to_smt r₂) with
            | RegLan rv₂ =>
                simp [__smtx_model_eval_re_inter, hEval₁, hEval₂] at hEval
                subst rv
                have hInter := nativeListInRe_mk_inter xs rv₁ rv₂
                change nativeListInRe xs
                  (native_re_mk_inter rv₁ rv₂) = true at hIn
                rw [hInter] at hIn
                have hPair :
                    nativeListInRe xs rv₁ = true ∧
                      nativeListInRe xs rv₂ = true := by
                  simpa [Bool.and_eq_true] using hIn
                exact fixed_len_re_sound M r₁ rv₁ n hFixed₁ hEval₁ xs
                  hPair.1
            | _ =>
                simp [__smtx_model_eval_re_inter, hEval₁, hEval₂] at hEval
        | _ =>
            cases hEval₂ : __smtx_model_eval M (__eo_to_smt r₂) <;>
              simp [__smtx_model_eval_re_inter, hEval₁, hEval₂] at hEval
  | r, rv, n, hFixed, hEval, xs, hIn => by
      cases r with
      | UOp op =>
          cases op <;> simp [__str_fixed_len_re] at hFixed
          case re_allchar =>
            subst n
            change __smtx_model_eval M SmtTerm.re_allchar = SmtValue.RegLan rv at hEval
            rw [__smtx_model_eval.eq_104] at hEval
            simp at hEval
            subst rv
            have hLen := nativeListInRe_allchar_true_length xs hIn
            rw [hLen]
            rfl
      | Apply f x =>
          cases f with
          | UOp op =>
              cases op <;> simp [__str_fixed_len_re, __eo_len] at hFixed
              case str_to_re =>
                cases x <;> simp at hFixed
                case String pat =>
                  subst n
                  change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String pat)) =
                    SmtValue.RegLan rv at hEval
                  rw [__smtx_model_eval.eq_107, __smtx_model_eval.eq_4] at hEval
                  simp [__smtx_model_eval_str_to_re, native_pack_string,
                    native_unpack_seq_pack] at hEval
                  subst rv
                  have hIn' : nativeListInRe xs (native_str_to_re pat) = true := by
                    have hMap :
                        List.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) pat = pat := by
                      clear hIn
                      induction pat with
                      | nil => rfl
                      | cons c cs ih =>
                          simp [Function.comp, impl_native_ssm_char_of_value, ih]
                    exact hIn
                  have hLen := nativeListInRe_str_to_re_true_length pat xs hIn'
                  simpa [native_str_len] using congrArg Int.ofNat hLen
                case Binary w bits =>
                  subst n
                  change __smtx_model_eval M
                      (SmtTerm.str_to_re (SmtTerm.Binary w bits)) =
                    SmtValue.RegLan rv at hEval
                  rw [__smtx_model_eval.eq_107, __smtx_model_eval.eq_5] at hEval
                  simp [__smtx_model_eval_str_to_re] at hEval
          | Apply g y =>
              cases g with
              | UOp op =>
                  cases op <;> simp [__str_fixed_len_re] at hFixed
                  case re_range =>
                    subst n
                    change __smtx_model_eval M
                        (SmtTerm.re_range (__eo_to_smt y) (__eo_to_smt x)) =
                      SmtValue.RegLan rv at hEval
                    rw [__smtx_model_eval.eq_113] at hEval
                    cases hlo : __smtx_model_eval M (__eo_to_smt y) with
                    | Seq slo =>
                        cases hhi : __smtx_model_eval M (__eo_to_smt x) with
                        | Seq shi =>
                            simp [__smtx_model_eval_re_range, hlo, hhi] at hEval
                            subst rv
                            have hLen := nativeListInRe_re_range_true_length xs
                              (native_unpack_seq slo) (native_unpack_seq shi) hIn
                            rw [hLen]
                            rfl
                        | _ =>
                            simp [__smtx_model_eval_re_range, hlo, hhi] at hEval
                    | _ =>
                        cases hhi : __smtx_model_eval M (__eo_to_smt x) <;>
                          simp [__smtx_model_eval_re_range, hlo, hhi] at hEval
                  case re_concat =>
                    change __eo_add (__str_fixed_len_re y) (__str_fixed_len_re x) =
                      Term.Numeral n at hFixed
                    rcases eo_add_eq_numeral_cases (__str_fixed_len_re y)
                        (__str_fixed_len_re x) n hFixed with
                      ⟨n₁, n₂, hFixed₁, hFixed₂, hAdd⟩
                    change __smtx_model_eval M
                        (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x)) =
                      SmtValue.RegLan rv at hEval
                    rw [__smtx_model_eval.eq_114] at hEval
                    cases hEval₁ : __smtx_model_eval M (__eo_to_smt y) with
                    | RegLan rv₁ =>
                        cases hEval₂ : __smtx_model_eval M (__eo_to_smt x) with
                        | RegLan rv₂ =>
                            simp [__smtx_model_eval_re_concat, hEval₁, hEval₂] at hEval
                            subst rv
                            rcases (nativeListInRe_mk_concat_true_iff_exists_append xs rv₁ rv₂).1
                                (by exact hIn) with
                              ⟨left, right, hAppend, hLeft, hRight⟩
                            have hLeftLen :=
                              fixed_len_re_sound M y rv₁ n₁ hFixed₁ hEval₁ left hLeft
                            have hRightLen :=
                              fixed_len_re_sound M x rv₂ n₂ hFixed₂ hEval₂ right hRight
                            calc
                              Int.ofNat xs.length = Int.ofNat (left ++ right).length := by
                                rw [hAppend]
                              _ = Int.ofNat left.length + Int.ofNat right.length := by
                                simp
                              _ = n₁ + n₂ := by
                                rw [hLeftLen, hRightLen]
                              _ = n := by
                                simpa [native_zplus] using hAdd
                        | _ =>
                            simp [__smtx_model_eval_re_concat, hEval₁, hEval₂] at hEval
                    | _ =>
                        cases hEval₂ : __smtx_model_eval M (__eo_to_smt x) <;>
                          simp [__smtx_model_eval_re_concat, hEval₁, hEval₂] at hEval
                  case re_union =>
                    by_cases hNone : x = Term.UOp UserOp.re_none
                    · subst x
                      simp [__str_fixed_len_re, __eo_eq, native_ite, native_teq] at hFixed
                      change __smtx_model_eval M
                          (SmtTerm.re_union (__eo_to_smt y) SmtTerm.re_none) =
                        SmtValue.RegLan rv at hEval
                      rw [__smtx_model_eval.eq_116, __smtx_model_eval.eq_105] at hEval
                      cases hEval₁ : __smtx_model_eval M (__eo_to_smt y) with
                      | RegLan rv₁ =>
                          simp [__smtx_model_eval_re_union, hEval₁] at hEval
                          subst rv
                          have hInLeft : nativeListInRe xs rv₁ = true := by
                            have hMk : native_re_mk_union rv₁ SmtRegLan.empty = rv₁ := by
                              cases rv₁ <;> simp [native_re_mk_union, native_re_union, native_re_union]
                            change nativeListInRe xs
                              (native_re_mk_union rv₁ SmtRegLan.empty) = true at hIn
                            rwa [hMk] at hIn
                          exact fixed_len_re_sound M y rv₁ n hFixed hEval₁ xs hInLeft
                      | _ =>
                          simp [__smtx_model_eval_re_union, hEval₁] at hEval
                    · have hFixed' :=
                        fixed_len_re_union_right_not_none y x n hNone hFixed
                      let len₁ := __str_fixed_len_re y
                      let req := __eo_requires (__str_fixed_len_re x) len₁ len₁
                      change req = Term.Numeral n at hFixed'
                      have hReqNe : req ≠ Term.Stuck := by
                        intro h
                        rw [h] at hFixed'
                        simp at hFixed'
                      have hReqResult : req = len₁ :=
                        eo_requires_result_eq_of_ne_stuck (__str_fixed_len_re x) len₁ len₁ hReqNe
                      have hReqEq : __str_fixed_len_re x = len₁ :=
                        eo_requires_eq_of_ne_stuck (__str_fixed_len_re x) len₁ len₁ hReqNe
                      have hFixed₁ : __str_fixed_len_re y = Term.Numeral n := by
                        simpa [len₁, req, hReqResult] using hFixed'
                      have hFixed₂ : __str_fixed_len_re x = Term.Numeral n := by
                        rw [hReqEq]
                        exact hFixed₁
                      change __smtx_model_eval M
                          (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x)) =
                        SmtValue.RegLan rv at hEval
                      rw [__smtx_model_eval.eq_116] at hEval
                      cases hEval₁ : __smtx_model_eval M (__eo_to_smt y) with
                      | RegLan rv₁ =>
                          cases hEval₂ : __smtx_model_eval M (__eo_to_smt x) with
                          | RegLan rv₂ =>
                              simp [__smtx_model_eval_re_union, hEval₁, hEval₂] at hEval
                              subst rv
                              have hUnion := nativeListInRe_mk_union xs rv₁ rv₂
                              change nativeListInRe xs
                                (native_re_mk_union rv₁ rv₂) = true at hIn
                              rw [hUnion] at hIn
                              have hOr :
                                  nativeListInRe xs rv₁ = true ∨
                                    nativeListInRe xs rv₂ = true := by
                                simpa [Bool.or_eq_true] using hIn
                              rcases hOr with hLeft | hRight
                              · exact fixed_len_re_sound M y rv₁ n hFixed₁ hEval₁ xs hLeft
                              · exact fixed_len_re_sound M x rv₂ n hFixed₂ hEval₂ xs hRight
                          | _ =>
                              simp [__smtx_model_eval_re_union, hEval₁, hEval₂] at hEval
                      | _ =>
                          cases hEval₂ : __smtx_model_eval M (__eo_to_smt x) <;>
                            simp [__smtx_model_eval_re_union, hEval₁, hEval₂] at hEval
                  case re_inter =>
                    by_cases hAll : x = Term.UOp UserOp.re_all
                    · subst x
                      simp [__str_fixed_len_re, __eo_eq, native_ite, native_teq] at hFixed
                      change __smtx_model_eval M
                          (SmtTerm.re_inter (__eo_to_smt y) SmtTerm.re_all) =
                        SmtValue.RegLan rv at hEval
                      rw [__smtx_model_eval.eq_115, __smtx_model_eval.eq_106] at hEval
                      cases hEval₁ : __smtx_model_eval M (__eo_to_smt y) with
                      | RegLan rv₁ =>
                          simp [__smtx_model_eval_re_inter, hEval₁] at hEval
                          subst rv
                          have hInter := nativeListInRe_mk_inter xs rv₁ native_re_all
                          change nativeListInRe xs
                            (native_re_mk_inter rv₁ native_re_all) = true at hIn
                          rw [hInter] at hIn
                          have hPair :
                              nativeListInRe xs rv₁ = true ∧
                                nativeListInRe xs native_re_all = true := by
                            simpa [Bool.and_eq_true] using hIn
                          exact fixed_len_re_sound M y rv₁ n hFixed hEval₁ xs
                            hPair.1
                      | _ =>
                          simp [__smtx_model_eval_re_inter, hEval₁] at hEval
                    · have hFixed' :=
                        fixed_len_re_inter_right_not_all y x n hAll hFixed
                      let len₁ := __str_fixed_len_re y
                      let req := __eo_requires (__str_fixed_len_re x) len₁ len₁
                      change req = Term.Numeral n at hFixed'
                      have hReqNe : req ≠ Term.Stuck := by
                        intro h
                        rw [h] at hFixed'
                        simp at hFixed'
                      have hReqResult : req = len₁ :=
                        eo_requires_result_eq_of_ne_stuck (__str_fixed_len_re x) len₁ len₁ hReqNe
                      have hReqEq : __str_fixed_len_re x = len₁ :=
                        eo_requires_eq_of_ne_stuck (__str_fixed_len_re x) len₁ len₁ hReqNe
                      have hFixed₁ : __str_fixed_len_re y = Term.Numeral n := by
                        simpa [len₁, req, hReqResult] using hFixed'
                      have hFixed₂ : __str_fixed_len_re x = Term.Numeral n := by
                        rw [hReqEq]
                        exact hFixed₁
                      change __smtx_model_eval M
                          (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x)) =
                        SmtValue.RegLan rv at hEval
                      rw [__smtx_model_eval.eq_115] at hEval
                      cases hEval₁ : __smtx_model_eval M (__eo_to_smt y) with
                      | RegLan rv₁ =>
                          cases hEval₂ : __smtx_model_eval M (__eo_to_smt x) with
                          | RegLan rv₂ =>
                              simp [__smtx_model_eval_re_inter, hEval₁, hEval₂] at hEval
                              subst rv
                              have hInter := nativeListInRe_mk_inter xs rv₁ rv₂
                              change nativeListInRe xs
                                (native_re_mk_inter rv₁ rv₂) = true at hIn
                              rw [hInter] at hIn
                              have hPair :
                                  nativeListInRe xs rv₁ = true ∧
                                    nativeListInRe xs rv₂ = true := by
                                simpa [Bool.and_eq_true] using hIn
                              exact fixed_len_re_sound M y rv₁ n hFixed₁ hEval₁ xs
                                hPair.1
                          | _ =>
                              simp [__smtx_model_eval_re_inter, hEval₁, hEval₂] at hEval
                      | _ =>
                          cases hEval₂ : __smtx_model_eval M (__eo_to_smt x) <;>
                            simp [__smtx_model_eval_re_inter, hEval₁, hEval₂] at hEval
              | Apply h z =>
                  cases h <;> simp [__str_fixed_len_re] at hFixed
              | UOp1 op a =>
                  cases op <;> simp [__str_fixed_len_re] at hFixed
              | UOp2 op a b =>
                  cases op <;> simp [__str_fixed_len_re] at hFixed
              | UOp3 op a b c =>
                  cases op <;> simp [__str_fixed_len_re] at hFixed
              | _ =>
                  simp [__str_fixed_len_re] at hFixed
          | UOp1 op a =>
              cases op <;> simp [__str_fixed_len_re] at hFixed
          | UOp2 op a b =>
              cases op <;> simp [__str_fixed_len_re] at hFixed
          | UOp3 op a b c =>
              cases op <;> simp [__str_fixed_len_re] at hFixed
          | _ =>
              simp [__str_fixed_len_re] at hFixed
      | _ =>
          simp [__str_fixed_len_re] at hFixed
termination_by r => r

private theorem smtx_model_eval_str_in_re_concat_star_char_side
    (M : SmtModel) (hM : model_wf M) :
    (s r side : Term) -> (ss : SmtSeq) -> (rv : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      (∀ xs : List native_Char, nativeListInRe xs rv = true -> xs.length = 1) ->
      side =
        __str_mk_str_in_re_concat_star_char s
          (Term.Apply (Term.UOp UserOp.re_mult) r) ->
      side ≠ Term.Stuck ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) =
        __smtx_model_eval M (__eo_to_smt side)
  | Term.String str, r, side, _ss, rv, _hSTy, _hSEval, hREval, _hLen, hSide, hSideNe => by
      cases str with
      | nil =>
          subst side
          change __smtx_model_eval M
              (SmtTerm.str_in_re (SmtTerm.String [])
                (SmtTerm.re_mult (__eo_to_smt r))) =
            __smtx_model_eval M (SmtTerm.Boolean true)
          rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_4,
            __smtx_model_eval.eq_108, __smtx_model_eval.eq_1, hREval]
          simp [__smtx_model_eval_str_in_re, __smtx_model_eval_re_mult,
            Smtm.native_str_in_re, Smtm.native_re_str_valid,
            native_pack_string,
            native_pack_seq, native_unpack_seq
            ]
          cases rv <;> simp [native_re_mult, native_re_nullable]
      | cons _ _ =>
          subst side
          simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Apply f s2, r, side, ss, rv, hSTy, hSEval, hREval, hLen, hSide, hSideNe => by
      cases f with
      | Apply g s1 =>
          cases g with
          | UOp op =>
              cases op with
              | str_concat =>
                  subst side
                  let reStar := Term.Apply (Term.UOp UserOp.re_mult) r
                  let leftIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s1) reStar
                  let tail := __str_mk_str_in_re_concat_star_char s2 reStar
                  have hTailNe : tail ≠ Term.Stuck :=
                    eo_mk_apply_right_ne_stuck_of_ne_stuck
                      (Term.Apply (Term.UOp UserOp.and) leftIn) tail (by
                        simpa [__str_mk_str_in_re_concat_star_char, reStar, leftIn, tail]
                          using hSideNe)
                  have hConcatNN :
                      term_has_non_none_type
                        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) := by
                    unfold term_has_non_none_type
                    change __smtx_typeof
                        (__eo_to_smt
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) ≠
                      SmtType.None
                    rw [hSTy]
                    simp
                  rcases seq_binop_args_of_non_none
                      (op := SmtTerm.str_concat)
                      (t1 := __eo_to_smt s1) (t2 := __eo_to_smt s2)
                      (typeof_str_concat_eq (__eo_to_smt s1) (__eo_to_smt s2))
                      hConcatNN with
                    ⟨T, hS1TyRaw, hS2TyRaw⟩
                  have hT : T = SmtType.Char := by
                    change __smtx_typeof
                        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) =
                      SmtType.Seq SmtType.Char at hSTy
                    rw [typeof_str_concat_eq, hS1TyRaw, hS2TyRaw] at hSTy
                    simpa [__smtx_typeof_seq_op_2, native_ite, native_Teq] using hSTy
                  subst T
                  have hS1Ty : __smtx_typeof (__eo_to_smt s1) =
                      SmtType.Seq SmtType.Char := hS1TyRaw
                  have hS2Ty : __smtx_typeof (__eo_to_smt s2) =
                      SmtType.Seq SmtType.Char := hS2TyRaw
                  change __smtx_model_eval M
                      (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) =
                    SmtValue.Seq ss at hSEval
                  rw [__smtx_model_eval.eq_81] at hSEval
                  cases hS1Eval : __smtx_model_eval M (__eo_to_smt s1) with
                  | Seq ss1 =>
                      cases hS2Eval : __smtx_model_eval M (__eo_to_smt s2) with
                      | Seq ss2 =>
                          simp [__smtx_model_eval_str_concat, hS1Eval, hS2Eval] at hSEval
                          subst ss
                          have hS1EvalTy :
                              __smtx_typeof_value (SmtValue.Seq ss1) =
                                SmtType.Seq SmtType.Char := by
                            simpa [hS1Ty, hS1Eval] using
                              smt_model_eval_preserves_type_of_non_none M hM
                                (__eo_to_smt s1) (by
                                  unfold term_has_non_none_type
                                  rw [hS1Ty]
                                  simp)
                          have hS2EvalTy :
                              __smtx_typeof_value (SmtValue.Seq ss2) =
                                SmtType.Seq SmtType.Char := by
                            simpa [hS2Ty, hS2Eval] using
                              smt_model_eval_preserves_type_of_non_none M hM
                                (__eo_to_smt s2) (by
                                  unfold term_has_non_none_type
                                  rw [hS2Ty]
                                  simp)
                          have hS1Valid : native_string_valid (native_unpack_string ss1) = true :=
                            native_unpack_string_valid_of_typeof_seq_char hS1EvalTy
                          have hS2Valid : native_string_valid (native_unpack_string ss2) = true :=
                            native_unpack_string_valid_of_typeof_seq_char hS2EvalTy
                          have hS1Unpack :
                              native_unpack_seq ss1 =
                                impl_native_string_to_values (native_unpack_string ss1) :=
                            native_unpack_seq_eq_string_to_values_of_typeof_seq_char
                              hS1EvalTy
                          have hS2Unpack :
                              native_unpack_seq ss2 =
                                impl_native_string_to_values (native_unpack_string ss2) :=
                            native_unpack_seq_eq_string_to_values_of_typeof_seq_char
                              hS2EvalTy
                          have hLeftEval :
                              __smtx_model_eval M (__eo_to_smt leftIn) =
                                SmtValue.Boolean
                                  (native_str_in_re (native_unpack_string ss1)
                                    (native_re_mult rv)) := by
                            change __smtx_model_eval M
                                (SmtTerm.str_in_re (__eo_to_smt s1)
                                  (SmtTerm.re_mult (__eo_to_smt r))) =
                              SmtValue.Boolean
                                (native_str_in_re (native_unpack_string ss1)
                                  (native_re_mult rv))
                            rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_108,
                              hS1Eval, hREval]
                            simp only [__smtx_model_eval_str_in_re,
                              __smtx_model_eval_re_mult]
                            rw [hS1Unpack, ← native_str_in_re_eq_model]
                          have hTailEq :
                              __smtx_model_eval M
                                  (__eo_to_smt
                                    (Term.Apply
                                      (Term.Apply (Term.UOp UserOp.str_in_re) s2)
                                      (Term.Apply (Term.UOp UserOp.re_mult) r))) =
                                __smtx_model_eval M (__eo_to_smt tail) :=
                            smtx_model_eval_str_in_re_concat_star_char_side M hM
                              s2 r tail ss2 rv hS2Ty hS2Eval hREval hLen rfl hTailNe
                          have hTailEval :
                              __smtx_model_eval M (__eo_to_smt tail) =
                                SmtValue.Boolean
                                  (native_str_in_re (native_unpack_string ss2)
                                    (native_re_mult rv)) := by
                            rw [← hTailEq]
                            change __smtx_model_eval M
                                (SmtTerm.str_in_re (__eo_to_smt s2)
                                  (SmtTerm.re_mult (__eo_to_smt r))) =
                              SmtValue.Boolean
                                (native_str_in_re (native_unpack_string ss2)
                                  (native_re_mult rv))
                            rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_108,
                              hS2Eval, hREval]
                            simp only [__smtx_model_eval_str_in_re,
                              __smtx_model_eval_re_mult]
                            rw [hS2Unpack, ← native_str_in_re_eq_model]
                          have hSideEval :
                              __smtx_model_eval M
                                  (__eo_to_smt
                                    (__eo_mk_apply
                                      (Term.Apply (Term.UOp UserOp.and) leftIn) tail)) =
                                SmtValue.Boolean
                                  (native_str_in_re (native_unpack_string ss1)
                                      (native_re_mult rv) &&
                                    native_str_in_re (native_unpack_string ss2)
                                      (native_re_mult rv)) := by
                            have hMk :
                                __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) leftIn) tail =
                                  Term.Apply (Term.Apply (Term.UOp UserOp.and) leftIn) tail := by
                              simp [__eo_mk_apply]
                            rw [hMk]
                            change __smtx_model_eval M
                                (SmtTerm.and (__eo_to_smt leftIn) (__eo_to_smt tail)) =
                              SmtValue.Boolean
                                (native_str_in_re (native_unpack_string ss1)
                                    (native_re_mult rv) &&
                                  native_str_in_re (native_unpack_string ss2)
                                    (native_re_mult rv))
                            rw [__smtx_model_eval.eq_9, hLeftEval, hTailEval]
                            simp [__smtx_model_eval_and, native_and]
                          change __smtx_model_eval M
                              (SmtTerm.str_in_re
                                (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2))
                                (SmtTerm.re_mult (__eo_to_smt r))) =
                            __smtx_model_eval M
                              (__eo_to_smt
                                (__eo_mk_apply
                                  (Term.Apply (Term.UOp UserOp.and) leftIn) tail))
                          rw [hSideEval]
                          rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_81,
                            __smtx_model_eval.eq_108, hS1Eval, hS2Eval, hREval]
                          simp [__smtx_model_eval_str_concat, __smtx_model_eval_str_in_re,
                            __smtx_model_eval_re_mult, native_unpack_seq_pack,
                            hS1Unpack, hS2Unpack, impl_native_string_to_values]
                          rw [native_seq_concat, ← List.map_append]
                          change Smtm.native_str_in_re
                              (impl_native_string_to_values
                                (native_unpack_string ss1 ++ native_unpack_string ss2))
                              (native_re_mult rv) = _
                          rw [← native_str_in_re_eq_model]
                          exact native_str_in_re_re_mult_append rv hLen
                            (native_unpack_string ss1) (native_unpack_string ss2)
                            hS1Valid hS2Valid
                      | _ =>
                          simp [__smtx_model_eval_str_concat, hS1Eval, hS2Eval] at hSEval
                  | _ =>
                      cases hS2Eval : __smtx_model_eval M (__eo_to_smt s2) <;>
                        simp [__smtx_model_eval_str_concat, hS1Eval, hS2Eval] at hSEval
              | _ =>
                  subst side
                  simp [__str_mk_str_in_re_concat_star_char] at hSideNe
          | _ =>
              subst side
              simp [__str_mk_str_in_re_concat_star_char] at hSideNe
      | _ =>
          subst side
          simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.UOp _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.UOp1 _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.UOp2 _ _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.UOp3 _ _ _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.__eo_List, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.__eo_List_nil, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.__eo_List_cons, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Bool, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Boolean _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Numeral _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Rational _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Binary _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Type, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Stuck, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.FunType, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.Var _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.DatatypeType _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.DatatypeTypeRef _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.DtcAppType _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.DtCons _ _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.DtSel _ _ _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.USort _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
  | Term.UConst _ _, r, side, _ss, _rv, _hSTy, _hSEval, _hREval, _hLen, hSide, hSideNe => by
      subst side
      simp [__str_mk_str_in_re_concat_star_char] at hSideNe
termination_by s => s

private theorem str_in_re_concat_star_char_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b))
    (hProgNe :
      __eo_prog_str_in_re_concat_star_char
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_concat_star_char
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b)) := by
  let reStar := Term.Apply (Term.UOp UserOp.re_mult) r
  let strConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) strConcat) reStar
  let side := __str_mk_str_in_re_concat_star_char strConcat reStar
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  let inner := __eo_requires side b body
  change __eo_requires (__str_fixed_len_re r) (Term.Numeral 1) inner ≠
    Term.Stuck at hProgNe
  have hFixed : __str_fixed_len_re r = Term.Numeral 1 :=
    eo_requires_eq_of_ne_stuck (__str_fixed_len_re r) (Term.Numeral 1) inner hProgNe
  have hOuterResult :
      __eo_requires (__str_fixed_len_re r) (Term.Numeral 1) inner = inner :=
    eo_requires_result_eq_of_ne_stuck (__str_fixed_len_re r) (Term.Numeral 1) inner hProgNe
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__str_fixed_len_re r) (Term.Numeral 1)
      inner hProgNe
  have hSideEq : side = b := eo_requires_eq_of_ne_stuck side b body hInnerNe
  have hInnerResult : inner = body :=
    eo_requires_result_eq_of_ne_stuck side b body hInnerNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side b body hInnerNe
  subst b
  change StepRuleProperties M []
    (__eo_requires (__str_fixed_len_re r) (Term.Numeral 1)
      (__eo_requires side side body))
  rw [hOuterResult, hInnerResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    simpa [reStar, strConcat, strIn, side, body] using hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn side hEqTrans with
    ⟨hStrInTrans, _hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation strConcat reStar (by
      simpa [strIn] using hStrInTrans) with
    ⟨hSTy, hStarTy⟩
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan at hStarTy
    rw [typeof_re_mult_eq] at hStarTy
    by_cases hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan
    · exact hRTy
    · simp [hRTy, native_ite, native_Teq] at hStarTy
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt strConcat)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt strConcat) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hLen :
      ∀ xs : List native_Char, nativeListInRe xs rv = true -> xs.length = 1 := by
    intro xs hIn
    have hInt := fixed_len_re_sound M r rv (1 : native_Int) hFixed hREval xs hIn
    exact Int.ofNat.inj (by simpa using hInt)
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt strIn) =
        __smtx_model_eval M (__eo_to_smt side) := by
    exact smtx_model_eval_str_in_re_concat_star_char_side M hM
      strConcat r side ss rv hSTy hSEval hREval hLen rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt side))

end RuleProofs

public theorem cmd_step_str_in_re_concat_star_char_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_concat_star_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_concat_star_char args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_concat_star_char args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_concat_star_char args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp reStar =>
                                  cases inApp with
                                  | Apply inOp strConcat =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              cases strConcat with
                                              | Apply concatApp s2 =>
                                                  cases concatApp with
                                                  | Apply concatOp s1 =>
                                                      cases concatOp with
                                                      | UOp concatOpName =>
                                                          cases concatOpName with
                                                          | str_concat =>
                                                              cases reStar with
                                                              | Apply starOp r =>
                                                                  cases starOp with
                                                                  | UOp starOpName =>
                                                                      cases starOpName with
                                                                      | re_mult =>
                                                                          have hProps :=
                                                                            RuleProofs.str_in_re_concat_star_char_valid_properties
                                                                              M hM s1 s2 r b (by
                                                                                simpa using hA1Trans) (by
                                                                                change
                                                                                  __eo_prog_str_in_re_concat_star_char
                                                                                    (Term.Apply
                                                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                                                        (Term.Apply
                                                                                          (Term.Apply
                                                                                            (Term.UOp UserOp.str_in_re)
                                                                                            (Term.Apply
                                                                                              (Term.Apply
                                                                                                (Term.UOp UserOp.str_concat) s1) s2))
                                                                                          (Term.Apply
                                                                                            (Term.UOp UserOp.re_mult) r))) b) ≠
                                                                                    Term.Stuck at hProg
                                                                                exact hProg)
                                                                          change StepRuleProperties M []
                                                                            (__eo_prog_str_in_re_concat_star_char
                                                                              (Term.Apply
                                                                                (Term.Apply (Term.UOp UserOp.eq)
                                                                                  (Term.Apply
                                                                                    (Term.Apply
                                                                                      (Term.UOp UserOp.str_in_re)
                                                                                      (Term.Apply
                                                                                        (Term.Apply
                                                                                          (Term.UOp UserOp.str_concat) s1) s2))
                                                                                    (Term.Apply
                                                                                      (Term.UOp UserOp.re_mult) r))) b))
                                                                          simpa [premiseTermList] using hProps
                                                                      | _ =>
                                                                          change Term.Stuck ≠ Term.Stuck at hProg
                                                                          exact False.elim (hProg rfl)
                                                                  | _ =>
                                                                      change Term.Stuck ≠ Term.Stuck at hProg
                                                                      exact False.elim (hProg rfl)
                                                              | _ =>
                                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                                  exact False.elim (hProg rfl)
                                                          | _ =>
                                                              change Term.Stuck ≠ Term.Stuck at hProg
                                                              exact False.elim (hProg rfl)
                                                      | _ =>
                                                          change Term.Stuck ≠ Term.Stuck at hProg
                                                          exact False.elim (hProg rfl)
                                                  | _ =>
                                                      change Term.Stuck ≠ Term.Stuck at hProg
                                                      exact False.elim (hProg rfl)
                                              | _ =>
                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                  exact False.elim (hProg rfl)
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
