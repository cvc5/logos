module

public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrContainsReplCharSupport

theorem eqs_of_requires4_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term)
    (hProg :
      __eo_requires
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h123 := StrEqReplSupport.eo_and_eq_true_left hGuard
  have h4 := StrEqReplSupport.eo_and_eq_true_right hGuard
  have h12 := StrEqReplSupport.eo_and_eq_true_left h123
  have h3 := StrEqReplSupport.eo_and_eq_true_right h123
  have h1 := StrEqReplSupport.eo_and_eq_true_left h12
  have h2 := StrEqReplSupport.eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4⟩

theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem native_seq_prefix_eq_append
    (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

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
          rw [ite_eq_left (native_seq_prefix_eq_append pat after)]
          simp
  | cons b bs ih =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          have hbs : bs.length < f := by
            simp only [List.length_cons] at hFuel
            omega
          unfold native_seq_indexof_rec
          by_cases hPre :
              native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [ite_eq_left hPre]
            simp
          · rw [ite_eq_right hPre]
            have hxs :
                (b :: bs) ++ pat ++ after = b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

theorem native_seq_contains_of_decomp
    (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  have hLen : pat.length ≤ (before ++ pat ++ after).length := by
    simp [List.length_append]
    omega
  have hNe :
      native_seq_indexof (before ++ pat ++ after) pat 0 ≠ -1 := by
    rw [native_seq_indexof_eq_rec]
    simp only [Int.reduceLT, ite_false, Int.toNat_zero, Nat.zero_add]
    rw [dite_eq_left hLen]
    have hFuel :
        before.length <
          (before ++ pat ++ after).length - pat.length + 1 := by
      simp [List.length_append]
      omega
    simpa using
      native_seq_indexof_rec_append_ne_neg pat after before 0
        ((before ++ pat ++ after).length - pat.length + 1) hFuel
  have hGe : 0 ≤ native_seq_indexof (before ++ pat ++ after) pat 0 := by
    rcases native_seq_indexof_eq_neg_one_or_ge
        (before ++ pat ++ after) pat 0 with h | h
    · exact absurd h hNe
    · exact h
  unfold native_seq_contains
  exact decide_eq_true hGe

theorem native_seq_contains_iff_decomp
    (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔
      ∃ before after, xs = before ++ pat ++ after := by
  constructor
  · intro h
    have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
      unfold native_seq_contains at h
      exact of_decide_eq_true h
    exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩
  · rintro ⟨before, after, rfl⟩
    exact native_seq_contains_of_decomp before pat after

theorem native_seq_contains_trans
    (xs mid pat : List SmtValue)
    (hXMid : native_seq_contains xs mid = true)
    (hMidPat : native_seq_contains mid pat = true) :
    native_seq_contains xs pat = true := by
  rcases (native_seq_contains_iff_decomp xs mid).1 hXMid with
    ⟨before, after, hXs⟩
  rcases (native_seq_contains_iff_decomp mid pat).1 hMidPat with
    ⟨midBefore, midAfter, hMid⟩
  apply (native_seq_contains_iff_decomp xs pat).2
  refine ⟨before ++ midBefore, midAfter ++ after, ?_⟩
  rw [hXs, hMid]
  simp [List.append_assoc]

theorem native_seq_contains_replacement_of_pattern_present
    (source pattern replacement : List SmtValue)
    (hContains : native_seq_contains source pattern = true) :
    native_seq_contains
        (native_seq_replace source pattern replacement) replacement = true := by
  cases pattern with
  | nil =>
      simpa [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero] using
        native_seq_contains_of_decomp [] replacement source
  | cons p ps =>
      have hNonneg : 0 ≤ native_seq_indexof source (p :: ps) 0 := by
        unfold native_seq_contains at hContains
        exact of_decide_eq_true hContains
      have hNotNeg : ¬ native_seq_indexof source (p :: ps) 0 < 0 :=
        Int.not_lt_of_ge hNonneg
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      rw [ite_eq_right hNotNeg]
      exact native_seq_contains_of_decomp
        (source.take (Int.toNat (native_seq_indexof source (p :: ps) 0)))
        replacement
        (source.drop
          (Int.toNat (native_seq_indexof source (p :: ps) 0) +
            (p :: ps).length))

theorem native_seq_contains_pattern_replacement_of_replaced_source
    (source pattern replacement : List SmtValue)
    (hPattern : native_seq_contains source pattern = true)
    (hReplaced :
      native_seq_contains source
          (native_seq_replace source pattern replacement) = true) :
    native_seq_contains pattern replacement = true := by
  cases pattern with
  | nil =>
      rcases (native_seq_contains_iff_decomp source
          (native_seq_replace source [] replacement)).1 hReplaced with
        ⟨outerPrefix, outerSuffix, hSource⟩
      have hLen := congrArg List.length hSource
      have hReplacementLen : replacement.length = 0 := by
        simp [StrEqReplSupport.native_seq_replace_eq_indexof,
          StrEqReplSupport.native_seq_indexof_nil_zero,
          List.length_append] at hLen
        omega
      have hReplacementNil : replacement = [] :=
        List.eq_nil_of_length_eq_zero hReplacementLen
      subst replacement
      exact native_seq_contains_of_decomp [] [] []
  | cons p ps =>
      have hIndexNonneg :
          0 ≤ native_seq_indexof source (p :: ps) 0 := by
        unfold native_seq_contains at hPattern
        exact of_decide_eq_true hPattern
      have hIndexNotNeg :
          ¬ native_seq_indexof source (p :: ps) 0 < 0 :=
        Int.not_lt_of_ge hIndexNonneg
      let k := Int.toNat (native_seq_indexof source (p :: ps) 0)
      let before := source.take k
      let after := source.drop (k + (p :: ps).length)
      have hSourceFirst : before ++ (p :: ps) ++ after = source := by
        simpa [before, after, k] using
          StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
            source (p :: ps) hIndexNonneg
      have hReplaceEq :
          native_seq_replace source (p :: ps) replacement =
            before ++ replacement ++ after := by
        simp [StrEqReplSupport.native_seq_replace_eq_indexof,
          hIndexNotNeg, before, after, k]
      rcases (native_seq_contains_iff_decomp source
          (native_seq_replace source (p :: ps) replacement)).1
          hReplaced with
        ⟨outerBefore, outerAfter, hSourceReplaced⟩
      rw [hReplaceEq] at hSourceReplaced
      have hWords :
          before ++ (p :: ps) ++ after =
            outerBefore ++ (before ++ replacement ++ after) ++ outerAfter :=
        by exact hSourceFirst.trans hSourceReplaced
      have hLen := congrArg List.length hWords
      simp only [List.length_append] at hLen
      have hReplacementBound :
          outerBefore.length + replacement.length + outerAfter.length =
            (p :: ps).length := by
        omega
      let innerPrefix := (outerBefore ++ before).drop before.length
      have hBeforeLe :
          before.length ≤ (outerBefore ++ before).length := by
        simp
      have hInnerPrefixLen :
          innerPrefix.length = outerBefore.length := by
        simp [innerPrefix, List.length_drop]
      have hWordsAssoc :
          before ++ ((p :: ps) ++ after) =
            (outerBefore ++ before) ++
              (replacement ++ after ++ outerAfter) := by
        simpa [List.append_assoc] using hWords
      have hDropped :
          (p :: ps) ++ after =
            (innerPrefix ++ replacement) ++ (after ++ outerAfter) := by
        calc
          (p :: ps) ++ after =
              (before ++ ((p :: ps) ++ after)).drop before.length := by
                simp
          _ = ((outerBefore ++ before) ++
                (replacement ++ after ++ outerAfter)).drop before.length := by
                rw [hWordsAssoc]
          _ = (outerBefore ++ before).drop before.length ++
                (replacement ++ after ++ outerAfter) := by
                rw [List.drop_append_of_le_length hBeforeLe]
          _ = (innerPrefix ++ replacement) ++ (after ++ outerAfter) := by
                simp [innerPrefix, List.append_assoc]
      have hPrefixReplacementLe :
          (innerPrefix ++ replacement).length ≤ (p :: ps).length := by
        simp only [List.length_append, hInnerPrefixLen]
        omega
      have hTaken := congrArg (List.take (p :: ps).length) hDropped
      have hPatternDecomp :
          p :: ps = innerPrefix ++ replacement ++
            (after ++ outerAfter).take
              ((p :: ps).length - (innerPrefix ++ replacement).length) := by
        calc
          p :: ps = ((p :: ps) ++ after).take (p :: ps).length := by
            simp
          _ = ((innerPrefix ++ replacement) ++ (after ++ outerAfter)).take
                (p :: ps).length := hTaken
          _ = innerPrefix ++ replacement ++
                (after ++ outerAfter).take
                  ((p :: ps).length -
                    (innerPrefix ++ replacement).length) := by
            rw [List.take_append,
              List.take_of_length_le hPrefixReplacementLe]
      exact (native_seq_contains_iff_decomp (p :: ps) replacement).2
        ⟨innerPrefix,
          (after ++ outerAfter).take
            ((p :: ps).length - (innerPrefix ++ replacement).length),
          hPatternDecomp⟩

theorem native_seq_replace_dual_ite2_of_contains_true
    (source pattern replacement outerReplacement : List SmtValue)
    (hPatternReplacementAbsent :
      native_seq_contains pattern replacement = false)
    (hPatternPresent : native_seq_contains source pattern = true) :
    native_seq_replace source
        (native_seq_replace source pattern replacement) outerReplacement =
      source := by
  have hInnerAbsent :
      native_seq_contains source
          (native_seq_replace source pattern replacement) = false := by
    cases hInner : native_seq_contains source
        (native_seq_replace source pattern replacement)
    · rfl
    · have hPatternReplacement :=
        native_seq_contains_pattern_replacement_of_replaced_source
          source pattern replacement hPatternPresent hInner
      rw [hPatternReplacement] at hPatternReplacementAbsent
      contradiction
  exact StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
    source (native_seq_replace source pattern replacement) outerReplacement
    hInnerAbsent

theorem native_seq_length_le_of_contains
    (source pattern : List SmtValue)
    (hContains : native_seq_contains source pattern = true) :
    pattern.length ≤ source.length := by
  rcases (native_seq_contains_iff_decomp source pattern).1 hContains with
    ⟨before, after, rfl⟩
  simp [List.length_append]
  omega

theorem native_seq_replace_src_inv_no_contains1
    (xs source blocked : List SmtValue)
    (hAbsent : native_seq_contains source blocked = false) :
    native_seq_replace xs (native_seq_replace source xs blocked) source =
      native_seq_replace xs source source := by
  by_cases hSourceXs : native_seq_contains source xs = true
  · have hInnerBlocked :
        native_seq_contains (native_seq_replace source xs blocked) blocked =
          true :=
      native_seq_contains_replacement_of_pattern_present
        source xs blocked hSourceXs
    have hOuterAbsent :
        native_seq_contains xs (native_seq_replace source xs blocked) =
          false := by
      cases h :
          native_seq_contains xs (native_seq_replace source xs blocked)
      · rfl
      · have hXsBlocked := native_seq_contains_trans xs
            (native_seq_replace source xs blocked) blocked h hInnerBlocked
        have hSourceBlocked := native_seq_contains_trans source xs blocked
          hSourceXs hXsBlocked
        rw [hSourceBlocked] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs (native_seq_replace source xs blocked) source hOuterAbsent]
    exact (StrEqReplSupport.native_seq_replace_id xs source).symm
  · have hSourceXsFalse : native_seq_contains source xs = false := by
      cases h : native_seq_contains source xs
      · rfl
      · exact False.elim (hSourceXs h)
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      source xs blocked hSourceXsFalse]

theorem native_seq_replace_src_inv_no_contains2
    (xs source blocked : List SmtValue)
    (hAbsent : native_seq_contains source blocked = false) :
    native_seq_replace xs (native_seq_replace source xs blocked) xs =
      native_seq_replace xs source xs := by
  by_cases hSourceXs : native_seq_contains source xs = true
  · have hInnerBlocked :
        native_seq_contains (native_seq_replace source xs blocked) blocked =
          true :=
      native_seq_contains_replacement_of_pattern_present
        source xs blocked hSourceXs
    have hOuterAbsent :
        native_seq_contains xs (native_seq_replace source xs blocked) =
          false := by
      cases h :
          native_seq_contains xs (native_seq_replace source xs blocked)
      · rfl
      · have hXsBlocked := native_seq_contains_trans xs
            (native_seq_replace source xs blocked) blocked h hInnerBlocked
        have hSourceBlocked := native_seq_contains_trans source xs blocked
          hSourceXs hXsBlocked
        rw [hSourceBlocked] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs (native_seq_replace source xs blocked) xs hOuterAbsent]
    exact (StrEqReplSupport.native_seq_replace_source_of_pat_len_ge
      xs source (native_seq_length_le_of_contains source xs hSourceXs)).symm
  · have hSourceXsFalse : native_seq_contains source xs = false := by
      cases h : native_seq_contains source xs
      · rfl
      · exact False.elim (hSourceXs h)
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      source xs blocked hSourceXsFalse]

theorem native_seq_replace_src_inv_no_contains3
    (xs source pattern replacement outerReplacement : List SmtValue)
    (hPatternAbsent : native_seq_contains xs pattern = false)
    (hReplacementAbsent : native_seq_contains xs replacement = false) :
    native_seq_replace xs
        (native_seq_replace source pattern replacement) outerReplacement =
      native_seq_replace xs source outerReplacement := by
  by_cases hXsSource : native_seq_contains xs source = true
  · have hSourcePatternFalse :
        native_seq_contains source pattern = false := by
      cases h : native_seq_contains source pattern
      · rfl
      · have hXsPattern := native_seq_contains_trans xs source pattern
            hXsSource h
        rw [hXsPattern] at hPatternAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      source pattern replacement hSourcePatternFalse]
  · have hXsSourceFalse : native_seq_contains xs source = false := by
      cases h : native_seq_contains xs source
      · rfl
      · exact False.elim (hXsSource h)
    have hOuterPatternFalse :
        native_seq_contains xs
            (native_seq_replace source pattern replacement) = false := by
      by_cases hSourcePattern : native_seq_contains source pattern = true
      · have hInnerReplacement :
            native_seq_contains
                (native_seq_replace source pattern replacement) replacement =
              true :=
          native_seq_contains_replacement_of_pattern_present
            source pattern replacement hSourcePattern
        cases h :
            native_seq_contains xs
              (native_seq_replace source pattern replacement)
        · rfl
        · have hXsReplacement := native_seq_contains_trans xs
              (native_seq_replace source pattern replacement) replacement
              h hInnerReplacement
          rw [hXsReplacement] at hReplacementAbsent
          contradiction
      · have hSourcePatternFalse :
            native_seq_contains source pattern = false := by
          cases h : native_seq_contains source pattern
          · rfl
          · exact False.elim (hSourcePattern h)
        rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
          source pattern replacement hSourcePatternFalse]
        exact hXsSourceFalse
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs (native_seq_replace source pattern replacement) outerReplacement
      hOuterPatternFalse]
    exact (StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs source outerReplacement hXsSourceFalse).symm

theorem native_seq_replace_dual_ite1_of_contains_true
    (xs pattern replacement outerReplacement : List SmtValue)
    (hReplacementAbsent : native_seq_contains xs replacement = false)
    (hPatternPresent : native_seq_contains xs pattern = true) :
    native_seq_replace xs
        (native_seq_replace xs pattern replacement) outerReplacement = xs := by
  have hInnerReplacement :
      native_seq_contains
          (native_seq_replace xs pattern replacement) replacement = true :=
    native_seq_contains_replacement_of_pattern_present
      xs pattern replacement hPatternPresent
  have hInnerAbsent :
      native_seq_contains xs (native_seq_replace xs pattern replacement) =
        false := by
    cases h :
        native_seq_contains xs (native_seq_replace xs pattern replacement)
    · rfl
    · have hContradiction := native_seq_contains_trans xs
          (native_seq_replace xs pattern replacement) replacement
          h hInnerReplacement
      rw [hContradiction] at hReplacementAbsent
      contradiction
  exact StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
    xs (native_seq_replace xs pattern replacement) outerReplacement
    hInnerAbsent

theorem native_seq_replace_dual_ite1_of_contains_false
    (xs pattern replacement outerReplacement : List SmtValue)
    (hPatternAbsent : native_seq_contains xs pattern = false) :
    native_seq_replace xs
        (native_seq_replace xs pattern replacement) outerReplacement =
      outerReplacement := by
  rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
    xs pattern replacement hPatternAbsent]
  exact StrEqReplSupport.native_seq_replace_self xs outerReplacement

theorem native_seq_replace_tgt_no_contains
    (xs pat blocked repl : List SmtValue)
    (hAbsent : native_seq_contains xs blocked = false) :
    native_seq_replace xs pat (native_seq_replace pat blocked repl) = xs := by
  by_cases hContains : native_seq_contains xs pat = true
  · have hInnerAbsent : native_seq_contains pat blocked = false := by
      cases h : native_seq_contains pat blocked
      · rfl
      · have hContradiction := native_seq_contains_trans xs pat blocked
            hContains h
        rw [hContradiction] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      pat blocked repl hInnerAbsent]
    exact StrEqReplSupport.native_seq_replace_id xs pat
  · have hContainsFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hContains h)
    exact StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat (native_seq_replace pat blocked repl) hContainsFalse

theorem native_seq_replace_src_tgt_no_contains
    (xs pat replacement innerRepl : List SmtValue)
    (hAbsent : native_seq_contains replacement pat = false) :
    native_seq_replace xs pat
        (native_seq_replace replacement xs innerRepl) =
      native_seq_replace xs pat replacement := by
  by_cases hContains : native_seq_contains xs pat = true
  · have hInnerAbsent :
        native_seq_contains replacement xs = false := by
      cases h : native_seq_contains replacement xs
      · rfl
      · have hContradiction := native_seq_contains_trans
            replacement xs pat h hContains
        rw [hContradiction] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      replacement xs innerRepl hInnerAbsent]
  · have hContainsFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hContains h)
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat (native_seq_replace replacement xs innerRepl)
      hContainsFalse]
    exact (StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat replacement hContainsFalse).symm

theorem native_seq_contains_singleton_iff_mem
    (xs : List SmtValue) (w : SmtValue) :
    native_seq_contains xs [w] = true ↔ w ∈ xs := by
  constructor
  · intro h
    rcases (native_seq_contains_iff_decomp xs [w]).1 h with
      ⟨before, after, hXs⟩
    rw [hXs]
    simp
  · intro h
    rcases List.mem_iff_append.mp h with ⟨before, after, hXs⟩
    rw [hXs]
    simpa [List.append_assoc] using
      native_seq_contains_of_decomp before [w] after

theorem native_seq_contains_append_of_pattern_length_one
    (xs ys pat : List SmtValue) (hLen : pat.length = 1) :
    native_seq_contains (xs ++ ys) pat =
      SmtEval.native_or
        (native_seq_contains xs pat) (native_seq_contains ys pat) := by
  cases pat with
  | nil =>
      simp at hLen
  | cons p ps =>
      cases ps with
      | nil =>
          apply Bool.eq_iff_iff.mpr
          rw [native_seq_contains_singleton_iff_mem]
          simp only [SmtEval.native_or, Bool.or_eq_true]
          rw [native_seq_contains_singleton_iff_mem,
            native_seq_contains_singleton_iff_mem]
          exact List.mem_append
      | cons q qs =>
          simp at hLen

theorem native_seq_contains_nil (xs : List SmtValue) :
    native_seq_contains xs [] = true := by
  simpa using native_seq_contains_of_decomp [] [] xs

/-! ### One-character replacement commutes with taking a prefix -/

theorem native_seq_replace_take_of_length_one
    (xs pat repl : List SmtValue) (n : Nat)
    (hPatLen : pat.length = 1) (hReplLen : repl.length = 1) :
    (native_seq_replace xs pat repl).take n =
      native_seq_replace (xs.take n) pat repl := by
  by_cases hContains : native_seq_contains xs pat = true
  · have hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
      simpa [native_seq_contains] using hContains
    let idx := native_seq_indexof xs pat 0
    let k := Int.toNat idx
    have hBounds : k + pat.length ≤ xs.length := by
      exact StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
        xs pat hIdxNonneg
    have hkLe : k ≤ xs.length := by omega
    by_cases hnLe : n ≤ k
    · have hPrefixContainsFalse :
          native_seq_contains (xs.take n) pat = false := by
        cases hPrefixContains : native_seq_contains (xs.take n) pat
        · rfl
        · have hPrefixIdxNonneg :
              0 ≤ native_seq_indexof (xs.take n) pat 0 := by
            simpa [native_seq_contains] using hPrefixContains
          have hIndexAppend := native_seq_indexof_append_of_nonneg
            (xs.take n) pat (xs.drop n) 0 hPrefixIdxNonneg
          rw [List.take_append_drop] at hIndexAppend
          have hPrefixBounds :=
            StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
              (xs.take n) pat hPrefixIdxNonneg
          have hTakeLen : (xs.take n).length ≤ n := List.length_take_le _ _
          have hIndexEq :
              Int.toNat (native_seq_indexof (xs.take n) pat 0) = k := by
            rw [← hIndexAppend]
          rw [hIndexEq, hPatLen] at hPrefixBounds
          omega
      rw [StrEqReplSupport.native_seq_replace_of_indexof_nonneg
        xs pat repl hIdxNonneg]
      rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
        (xs.take n) pat repl hPrefixContainsFalse]
      rw [show Int.toNat (native_seq_indexof xs pat 0) = k from rfl]
      simp [List.take_append, List.length_take, Nat.min_eq_left hkLe,
        Nat.min_eq_left hnLe, hnLe]
      rw [List.take_take, Nat.min_eq_left hnLe]
    · have hkLt : k < n := Nat.lt_of_not_ge hnLe
      have hPrefixContains : native_seq_contains (xs.take n) pat = true := by
        have hDecomp :=
          StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
            xs pat hIdxNonneg
        change xs.take k ++ pat ++ xs.drop (k + pat.length) = xs at hDecomp
        apply (native_seq_contains_iff_decomp (xs.take n) pat).2
        refine ⟨xs.take k,
          (xs.drop (k + pat.length)).take (n - (k + pat.length)), ?_⟩
        have hTaken := congrArg (List.take n) hDecomp
        rw [List.take_append] at hTaken
        have hTakeKPat : (xs.take k ++ pat).take n = xs.take k ++ pat := by
          apply List.take_of_length_le
          simp [List.length_take, Nat.min_eq_left hkLe, hPatLen]
          omega
        rw [hTakeKPat] at hTaken
        have hTakeKPatLen : (xs.take k ++ pat).length = k + pat.length := by
          simp [List.length_take, Nat.min_eq_left hkLe]
        rw [hTakeKPatLen] at hTaken
        exact hTaken.symm
      have hPrefixIdxNonneg :
          0 ≤ native_seq_indexof (xs.take n) pat 0 := by
        simpa [native_seq_contains] using hPrefixContains
      have hIndexAppend := native_seq_indexof_append_of_nonneg
        (xs.take n) pat (xs.drop n) 0 hPrefixIdxNonneg
      rw [List.take_append_drop] at hIndexAppend
      have hIndexEq :
          native_seq_indexof (xs.take n) pat 0 = idx := by
        exact hIndexAppend.symm
      rw [StrEqReplSupport.native_seq_replace_of_indexof_nonneg
        xs pat repl hIdxNonneg]
      rw [StrEqReplSupport.native_seq_replace_of_indexof_nonneg
        (xs.take n) pat repl hPrefixIdxNonneg]
      rw [hIndexEq]
      change
        (xs.take k ++ repl ++ xs.drop (k + pat.length)).take n =
          (xs.take n).take k ++ repl ++ (xs.take n).drop (k + pat.length)
      rw [List.take_append]
      have hTakeKRepl :
          (xs.take k ++ repl).take n = xs.take k ++ repl := by
        apply List.take_of_length_le
        simp [List.length_take, Nat.min_eq_left hkLe, hReplLen]
        omega
      rw [hTakeKRepl]
      have hTakeKReplLen :
          (xs.take k ++ repl).length = k + repl.length := by
        simp [List.length_take, Nat.min_eq_left hkLe]
      rw [hTakeKReplLen]
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkLt)]
      rw [List.drop_take]
      simp [List.append_assoc, hPatLen, hReplLen]
  · have hContainsFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hContains h)
    have hPrefixContainsFalse :
        native_seq_contains (xs.take n) pat = false := by
      cases hPrefix : native_seq_contains (xs.take n) pat
      · rfl
      · rcases (native_seq_contains_iff_decomp (xs.take n) pat).1 hPrefix with
          ⟨before, after, hTake⟩
        have hXs : xs = before ++ pat ++ (after ++ xs.drop n) := by
          calc
            xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
            _ = before ++ pat ++ (after ++ xs.drop n) := by
              rw [hTake]
              simp [List.append_assoc]
        have hWhole : native_seq_contains xs pat = true := by
          rw [hXs]
          exact native_seq_contains_of_decomp before pat (after ++ xs.drop n)
        rw [hWhole] at hContainsFalse
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat repl hContainsFalse]
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      (xs.take n) pat repl hPrefixContainsFalse]

theorem native_seq_extract_replace_of_length_one
    (xs pat repl : List SmtValue) (n : native_Int)
    (hPatLen : pat.length = 1) (hReplLen : repl.length = 1) :
    native_seq_extract (native_seq_replace xs pat repl) 0 n =
      native_seq_replace (native_seq_extract xs 0 n) pat repl := by
  by_cases hn : 0 ≤ n
  · rw [native_seq_extract_zero_eq_take _ n hn,
      native_seq_extract_zero_eq_take _ n hn]
    exact native_seq_replace_take_of_length_one xs pat repl (Int.toNat n)
      hPatLen hReplLen
  · have hNeg : n < 0 := Int.lt_of_not_ge hn
    have hPatNe : pat ≠ [] := by
      intro hPatNil
      rw [hPatNil] at hPatLen
      simp at hPatLen
    rw [native_seq_extract_empty_of_len_nonpos _ 0 n (Int.le_of_lt hNeg),
      native_seq_extract_empty_of_len_nonpos _ 0 n (Int.le_of_lt hNeg),
      StrEqReplSupport.native_seq_replace_empty_src]
    simp [hPatNe]

theorem native_seq_replace_eq_self_of_contains_false
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = false) :
    native_seq_replace xs pat repl = xs := by
  have hNot : ¬ 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at hContains
    simpa using hContains
  have hNeg := Int.lt_of_not_ge hNot
  cases pat with
  | nil =>
      have hNil := native_seq_contains_nil xs
      rw [hNil] at hContains
      contradiction
  | cons p ps =>
      simp [StrEqReplSupport.native_seq_replace_eq_indexof, hNeg]

theorem mem_native_seq_replace_iff_of_not_mem_pattern
    (w : SmtValue) (xs pat repl : List SmtValue)
    (hNotMem : w ∉ pat) :
    w ∈ native_seq_replace xs pat repl ↔
      w ∈ xs ∨ (native_seq_contains xs pat = true ∧ w ∈ repl) := by
  cases pat with
  | nil =>
      rw [native_seq_contains_nil]
      rw [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero]
      simp only [Int.reduceLT, ite_false, Int.toNat_zero, List.take_zero,
        List.nil_append, Nat.zero_add, List.drop_zero, List.mem_append,
        true_and]
      exact or_comm
  | cons p ps =>
      by_cases hContains : native_seq_contains xs (p :: ps) = true
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 := by
          unfold native_seq_contains at hContains
          exact of_decide_eq_true hContains
        have hNotNeg : ¬ native_seq_indexof xs (p :: ps) 0 < 0 :=
          Int.not_lt_of_ge hNonneg
        let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hDecomp :
            xs.take n ++ (p :: ps) ++
                xs.drop (n + (p :: ps).length) = xs := by
          simpa [n] using
            StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
              xs (p :: ps) hNonneg
        have hMemX :
            w ∈ xs ↔
              w ∈ xs.take n ∨
                w ∈ xs.drop (n + (p :: ps).length) := by
          constructor
          · intro hMem
            rw [← hDecomp] at hMem
            simp only [List.mem_append] at hMem
            rcases hMem with hTakeOrPat | hDrop
            · rcases hTakeOrPat with hTake | hPat
              · exact Or.inl hTake
              · exact False.elim (hNotMem hPat)
            · exact Or.inr hDrop
          · intro hMem
            rw [← hDecomp]
            simp only [List.mem_append]
            rcases hMem with hTake | hDrop
            · exact Or.inl (Or.inl hTake)
            · exact Or.inr hDrop
        rw [StrEqReplSupport.native_seq_replace_eq_indexof]
        rw [ite_eq_right hNotNeg]
        change
          w ∈ xs.take n ++ repl ++
              xs.drop (n + (p :: ps).length) ↔
            w ∈ xs ∨
              (native_seq_contains xs (p :: ps) = true ∧ w ∈ repl)
        rw [hContains]
        simp only [true_and, List.mem_append]
        rw [hMemX]
        constructor
        · rintro ((hTake | hRepl) | hDrop)
          · exact Or.inl (Or.inl hTake)
          · exact Or.inr hRepl
          · exact Or.inl (Or.inr hDrop)
        · rintro ((hTake | hDrop) | hRepl)
          · exact Or.inl (Or.inl hTake)
          · exact Or.inr hDrop
          · exact Or.inl (Or.inr hRepl)
      · have hContainsFalse :
            native_seq_contains xs (p :: ps) = false := by
          cases h : native_seq_contains xs (p :: ps)
          · rfl
          · exact False.elim (hContains h)
        rw [native_seq_replace_eq_self_of_contains_false
          xs (p :: ps) repl hContainsFalse, hContainsFalse]
        simp

theorem native_seq_contains_replace_char
    (xs pat repl target : List SmtValue)
    (hLen : target.length = 1)
    (hPatTarget : native_seq_contains pat target = false) :
    native_seq_contains (native_seq_replace xs pat repl) target =
      SmtEval.native_or (native_seq_contains xs target)
        (SmtEval.native_and (native_seq_contains xs pat)
          (native_seq_contains repl target)) := by
  cases target with
  | nil => simp at hLen
  | cons w ws =>
      cases ws with
      | nil =>
          have hNotMem : w ∉ pat := by
            intro hMem
            have hTrue : native_seq_contains pat [w] = true :=
              (native_seq_contains_singleton_iff_mem pat w).2 hMem
            rw [hTrue] at hPatTarget
            contradiction
          apply Bool.eq_iff_iff.mpr
          rw [native_seq_contains_singleton_iff_mem]
          rw [mem_native_seq_replace_iff_of_not_mem_pattern
            w xs pat repl hNotMem]
          simp [SmtEval.native_or, SmtEval.native_and,
            native_seq_contains_singleton_iff_mem]
      | cons v vs => simp at hLen

theorem mem_native_seq_replace_self_iff
    (w : SmtValue) (xs pat : List SmtValue) :
    w ∈ native_seq_replace xs pat xs ↔ w ∈ xs := by
  cases pat with
  | nil =>
      simp [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [StrEqReplSupport.native_seq_replace_eq_indexof, hNeg]
      · rw [StrEqReplSupport.native_seq_replace_eq_indexof]
        rw [ite_eq_right hNeg]
        simp only [List.mem_append]
        constructor
        · intro h
          rcases h with hTakeOrXs | hDrop
          · rcases hTakeOrXs with hTake | hXs
            · exact List.mem_of_mem_take hTake
            · exact hXs
          · exact List.mem_of_mem_drop hDrop
        · intro hXs
          exact Or.inl (Or.inr hXs)

theorem native_seq_contains_replace_self_of_target_len_one
    (xs pat target : List SmtValue) (hLen : target.length = 1) :
    native_seq_contains (native_seq_replace xs pat xs) target =
      native_seq_contains xs target := by
  cases target with
  | nil => simp at hLen
  | cons w ws =>
      cases ws with
      | nil =>
          apply Bool.eq_iff_iff.mpr
          rw [native_seq_contains_singleton_iff_mem,
            native_seq_contains_singleton_iff_mem]
          exact mem_native_seq_replace_self_iff w xs pat
      | cons v vs => simp at hLen

end StrContainsReplCharSupport
