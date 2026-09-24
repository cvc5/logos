module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrEqReplSupport

theorem eo_typeof_eq_nonstuck_bool (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals assumption

theorem eo_and_eq_true_left {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp [__eo_and, native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    unfold __eo_requires at h
    cases hEq : native_teq (Term.Numeral w1) (Term.Numeral w2) <;>
      simp [native_ite, hEq] at h
    cases hOk : native_not (native_teq (Term.Numeral w1) Term.Stuck) <;>
      simp [native_ite, hOk] at h

theorem eo_and_eq_true_right {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    y = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp [__eo_and, native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    unfold __eo_requires at h
    cases hEq : native_teq (Term.Numeral w1) (Term.Numeral w2) <;>
      simp [native_ite, hEq] at h
    cases hOk : native_not (native_teq (Term.Numeral w1) Term.Stuck) <;>
      simp [native_ite, hOk] at h

theorem eqs_of_requires3_and_eq_true_not_stuck
    {x1 y1 x2 y2 x3 y3 body : Term}
    (h :
      __eo_requires
        (__eo_and (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3))
        (Term.Boolean true) body ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 := by
  have hGuard :
      __eo_and (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck h
  have h12 := eo_and_eq_true_left hGuard
  have h3 := eo_and_eq_true_right hGuard
  have h1 := eo_and_eq_true_left h12
  have h2 := eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3⟩

theorem eo_typeof_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_replace] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_replace] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_replace] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_replace] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_replace] at h ⊢
            case Seq =>
              cases C <;> simp [__eo_typeof_str_replace] at h ⊢
              case Apply k z =>
                cases k <;> simp [__eo_typeof_str_replace] at h ⊢
                case UOp opk =>
                  cases opk <;> simp [__eo_typeof_str_replace] at h ⊢
                  case Seq =>
                    have hEq :=
                      RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                        x x y z (Term.Apply Term.Seq x) h
                    rcases hEq with ⟨hy, hz⟩
                    subst y
                    subst z
                    simp

theorem eo_typeof_str_replace_result_of_seq_args
    (T : Term)
    (h : __eo_typeof_str_replace
      (Term.Apply Term.Seq T) (Term.Apply Term.Seq T)
      (Term.Apply Term.Seq T) ≠ Term.Stuck) :
    __eo_typeof_str_replace
        (Term.Apply Term.Seq T) (Term.Apply Term.Seq T)
        (Term.Apply Term.Seq T) =
      Term.Apply Term.Seq T := by
  cases T <;>
    simp [__eo_typeof_str_replace, __eo_requires, __eo_eq, native_ite,
      native_teq, SmtEval.native_not, __eo_and, native_and] at h ⊢

theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

theorem smtx_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_str_prefixof_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_prefixof x y) =
      __smtx_model_eval_str_prefixof
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

theorem smtx_eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

theorem native_seq_indexof_rec_nil
    (xs : List SmtValue) (i fuel : Nat) (hFuel : fuel ≠ 0) :
    native_seq_indexof_rec xs [] i fuel = Int.ofNat i := by
  cases fuel with
  | zero => exact False.elim (hFuel rfl)
  | succ fuel =>
      rw [Smtm.native_seq_indexof_rec.eq_def]
      simp [native_seq_prefix_eq]

@[simp] theorem native_seq_indexof_nil_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  rw [native_seq_indexof_eq_rec]
  simp [native_seq_indexof_rec_nil]

theorem native_re_find_idx_aux_re_of_list_length :
    ∀ (pat xs : List SmtValue) (i idx len : Nat),
      impl_native_re_find_idx_aux (impl_native_re_of_list pat) xs i =
          some (idx, len) →
        len = pat.length
  | pat, [], i, idx, len, hFind => by
      rw [impl_native_re_find_idx_aux.eq_def,
        native_re_prefix_match_re_of_list] at hFind
      by_cases hPrefix : native_seq_prefix_eq pat [] = true
      · simp [hPrefix] at hFind
        omega
      · simp [hPrefix] at hFind
  | pat, x :: xs, i, idx, len, hFind => by
      rw [impl_native_re_find_idx_aux.eq_def,
        native_re_prefix_match_re_of_list] at hFind
      by_cases hPrefix : native_seq_prefix_eq pat (x :: xs) = true
      · simp [hPrefix] at hFind
        omega
      · simp [hPrefix] at hFind
        exact native_re_find_idx_aux_re_of_list_length
          pat xs (i + 1) idx len hFind

theorem native_seq_replace_eq_indexof
    (xs pat repl : List SmtValue) :
    native_seq_replace xs pat repl =
      if native_seq_indexof xs pat 0 < 0 then
        xs
      else
        xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ repl ++
          xs.drop
            (Int.toNat (native_seq_indexof xs pat 0) + pat.length) := by
  unfold native_seq_replace native_seq_indexof native_str_replace_re
    native_str_indexof_re
  simp only [Int.reduceLT, if_false, Int.toNat_zero, Nat.zero_le, if_true]
  cases hFind : native_re_find_idx_from (native_str_to_re pat) xs 0 with
  | none => simp [hFind]
  | some result =>
      rcases result with ⟨idx, len⟩
      have hLen : len = pat.length := by
        apply native_re_find_idx_aux_re_of_list_length
          pat xs 0 idx len
        simpa [native_re_find_idx_from, native_str_to_re] using hFind
      have hIdxNonneg : ¬ (Int.ofNat idx : native_Int) < 0 := by simp
      simp only [hFind]
      rw [if_neg hIdxNonneg, hLen]
      simp

/-- Compatibility form for proofs that expose the regex-backed implementation
of `native_seq_replace`. -/
@[simp] theorem native_str_replace_re_to_re_eq_indexof
    (xs pat repl : List SmtValue) :
    native_str_replace_re xs (native_str_to_re pat) repl =
      if native_seq_indexof xs pat 0 < 0 then
        xs
      else
        xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ repl ++
          xs.drop
            (Int.toNat (native_seq_indexof xs pat 0) + pat.length) := by
  simpa only [native_seq_replace] using
    native_seq_replace_eq_indexof xs pat repl

theorem native_seq_replace_empty_src (pat repl : List SmtValue) :
    native_seq_replace [] pat repl = if pat = [] then repl else [] := by
  cases pat with
  | nil => simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      simp [native_seq_replace_eq_indexof, native_seq_indexof_eq_rec,
        native_seq_prefix_eq]

theorem native_seq_replace_empty_src_eq_iff
    (pat repl target : List SmtValue) (hTarget : target ≠ []) :
    native_seq_replace [] pat repl = target ↔
      pat = [] ∧ repl = target := by
  rw [native_seq_replace_empty_src]
  by_cases hPat : pat = []
  · simp [hPat]
  · simp [hPat, hTarget]

theorem native_seq_replace_of_indexof_nonneg
    (xs pat repl : List SmtValue)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_replace xs pat repl =
      xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ repl ++
        xs.drop
          (Int.toNat (native_seq_indexof xs pat 0) + pat.length) := by
  cases pat with
  | nil =>
      have hIdx : native_seq_indexof xs [] 0 = 0 :=
        native_seq_indexof_nil_zero xs
      rw [hIdx]
      simp [native_seq_replace_eq_indexof, hIdx]
  | cons p ps =>
      rw [native_seq_replace_eq_indexof]
      rw [if_neg (Int.not_lt_of_ge hNonneg)]

theorem native_seq_indexof_zero_bounds_of_nonneg
    (xs pat : List SmtValue)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤ xs.length := by
  rw [native_seq_indexof_eq_rec] at hNonneg ⊢
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hNonneg ⊢
    cases hResult :
        native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) with
    | ofNat j =>
        rcases native_seq_indexof_rec_decomp xs pat 0
            (xs.length - pat.length + 1) j hResult with
          ⟨_hZeroLe, before, after, hXs, hBeforeLen⟩
        have hLengths := congrArg List.length hXs
        simp only [List.length_append] at hLengths
        simp at hBeforeLen
        simp
        omega
    | negSucc j =>
        rw [hResult] at hNonneg
        simp at hNonneg
  · simp [hBounds] at hNonneg

theorem native_seq_replace_append_of_indexof_nonneg
    (xs pat repl suffix : List SmtValue)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_replace (xs ++ suffix) pat repl =
      native_seq_replace xs pat repl ++ suffix := by
  have hIndex := native_seq_indexof_append_of_nonneg xs pat suffix 0 hNonneg
  have hBounds := native_seq_indexof_zero_bounds_of_nonneg xs pat hNonneg
  have hIdxLe : Int.toNat (native_seq_indexof xs pat 0) ≤ xs.length := by
    omega
  have hNonnegAppend :
      0 ≤ native_seq_indexof (xs ++ suffix) pat 0 := by
    rw [hIndex]
    exact hNonneg
  rw [native_seq_replace_of_indexof_nonneg _ _ _ hNonnegAppend,
    native_seq_replace_of_indexof_nonneg _ _ _ hNonneg, hIndex]
  rw [List.take_append_of_le_length hIdxLe]
  rw [list_drop_append_of_le_length xs suffix
    (Int.toNat (native_seq_indexof xs pat 0) + pat.length) hBounds]
  simp only [List.append_assoc]

theorem native_seq_replace_eq_nil_iff_of_repl_ne_nil
    (xs pat repl : List SmtValue) (hRepl : repl ≠ []) :
    native_seq_replace xs pat repl = [] ↔ xs = [] ∧ pat ≠ [] := by
  constructor
  · intro hReplace
    cases pat with
    | nil =>
        have hExpanded : repl ++ xs = [] := by
          simpa [native_seq_replace_eq_indexof,
            native_seq_indexof_nil_zero] using hReplace
        exact False.elim (hRepl (List.append_eq_nil_iff.mp hExpanded).1)
    | cons p ps =>
        by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
        · have hXs : xs = [] := by
            simpa [native_seq_replace_eq_indexof, hNeg] using hReplace
          exact ⟨hXs, by simp⟩
        · have hExpanded :
              xs.take (Int.toNat (native_seq_indexof xs (p :: ps) 0)) ++
                  repl ++
                  xs.drop
                    (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
                      (p :: ps).length) =
                [] := by
              simpa [native_seq_replace_eq_indexof, hNeg] using hReplace
          have hReplNil : repl = [] := by
            have hLen := congrArg List.length hExpanded
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_append, List.length_nil] at hLen
            omega
          exact False.elim (hRepl hReplNil)
  · rintro ⟨rfl, hPat⟩
    rw [native_seq_replace_empty_src]
    simp [hPat]

theorem native_seq_indexof_zero_decomp_take_drop
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ pat ++
        xs.drop (Int.toNat (native_seq_indexof xs pat 0) + pat.length) =
      xs := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  rw [native_seq_indexof_eq_rec] at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx

    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    change xs.take j ++ pat ++ xs.drop (j + pat.length) = xs
    rw [hXs, ← hBeforeLen']
    simp
  · simp [hBounds] at hIdx

theorem native_seq_replace_length_eq_of_same_len
    (xs pat repl : List SmtValue)
    (hLen : pat.length = repl.length) :
    (native_seq_replace xs pat repl).length = xs.length := by
  cases pat with
  | nil =>
      have hReplNil : repl = [] := by
        cases repl with
        | nil => rfl
        | cons _ _ => simp at hLen
      subst repl
      simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace_eq_indexof, hNeg]
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
          int_nonneg_of_not_neg hNeg
        have hDecomp :=
          native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
        have hLenDecomp := congrArg List.length hDecomp
        simp [List.length_append] at hLenDecomp
        simp [native_seq_replace_eq_indexof, hNeg, List.length_append, ← hLen]
        omega

theorem native_seq_replace_self (xs repl : List SmtValue) :
    native_seq_replace xs xs repl = repl := by
  cases xs with
  | nil => simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons x xs =>
      simp [native_seq_replace_eq_indexof, native_seq_indexof_self_zero]

theorem native_seq_replace_source_of_pat_len_ge
    (xs pat : List SmtValue) (hLen : xs.length ≤ pat.length) :
    native_seq_replace xs pat xs = xs := by
  cases pat with
  | nil =>
      have hXsLen : xs.length = 0 := Nat.eq_zero_of_le_zero hLen
      have hXsNil : xs = [] := List.eq_nil_of_length_eq_zero hXsLen
      subst xs
      simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace_eq_indexof, hNeg]
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
          int_nonneg_of_not_neg hNeg
        let idx := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hDecomp :
            xs.take idx ++ (p :: ps) ++
                xs.drop (idx + (p :: ps).length) =
              xs := by
          simpa [idx] using
            native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
        have hLenDecomp := congrArg List.length hDecomp
        have hLen' : xs.length ≤ ps.length + 1 := by
          simpa using hLen
        have hTakeNil : xs.take idx = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_append, List.length_cons] at hLenDecomp
          omega
        have hDropNil : xs.drop (idx + (p :: ps).length) = [] := by
          apply List.eq_nil_of_length_eq_zero
          change (xs.drop (idx + (ps.length + 1))).length = 0
          simp only [List.length_append, List.length_cons] at hLenDecomp
          omega
        rw [native_seq_replace_eq_indexof]
        rw [if_neg hNeg]
        change xs.take idx ++ xs ++ xs.drop (idx + (p :: ps).length) = xs
        rw [hTakeNil, hDropNil]
        simp

theorem native_seq_replace_self_replacement_len_ge
    (xs pat : List SmtValue) :
    xs.length ≤ (native_seq_replace xs pat xs).length := by
  cases pat with
  | nil =>
      simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace_eq_indexof, hNeg]
      · simp [native_seq_replace_eq_indexof, hNeg]
        omega

theorem native_seq_replace_dual_self
    (xs pat : List SmtValue) :
    native_seq_replace xs (native_seq_replace xs pat xs) xs = xs := by
  apply native_seq_replace_source_of_pat_len_ge
  exact native_seq_replace_self_replacement_len_ge xs pat

theorem native_seq_replace_id
    (xs pat : List SmtValue) :
    native_seq_replace xs pat pat = xs := by
  cases pat with
  | nil =>
      simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace_eq_indexof, hNeg]
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
          int_nonneg_of_not_neg hNeg
        rw [native_seq_replace_eq_indexof]
        rw [if_neg hNeg]
        exact native_seq_indexof_zero_decomp_take_drop
          xs (p :: ps) hNonneg

theorem native_seq_replace_tgt_self
    (xs pat : List SmtValue) :
    native_seq_replace xs pat (native_seq_replace pat xs pat) = xs := by
  cases pat with
  | nil =>
      cases xs <;> simp [native_seq_replace_eq_indexof,
        native_seq_indexof_eq_rec, native_seq_prefix_eq]
  | cons p ps =>
      by_cases hContains : native_seq_contains xs (p :: ps) = true
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 := by
          unfold native_seq_contains at hContains
          exact of_decide_eq_true hContains
        let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hDecomp :
            xs.take n ++ (p :: ps) ++
                xs.drop (n + (p :: ps).length) = xs := by
          simpa [n] using
            native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
        have hLenEq := congrArg List.length hDecomp
        have hLen : (p :: ps).length ≤ xs.length := by
          simp only [List.length_append] at hLenEq
          omega
        have hInner : native_seq_replace (p :: ps) xs (p :: ps) = p :: ps :=
          native_seq_replace_source_of_pat_len_ge (p :: ps) xs hLen
        rw [hInner]
        exact native_seq_replace_id xs (p :: ps)
      · have hContainsFalse :
            native_seq_contains xs (p :: ps) = false := by
          cases h : native_seq_contains xs (p :: ps)
          · rfl
          · exact False.elim (hContains h)
        have hNot : ¬ 0 ≤ native_seq_indexof xs (p :: ps) 0 := by
          unfold native_seq_contains at hContainsFalse
          simpa using hContainsFalse
        have hNeg := Int.lt_of_not_ge hNot
        simp [native_seq_replace_eq_indexof, hNeg]

theorem native_seq_contains_nil (xs : List SmtValue) :
    native_seq_contains xs [] = true := by
  unfold native_seq_contains
  rw [native_seq_indexof_nil_zero]
  simp

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
      have hTrue := native_seq_contains_nil xs
      rw [hTrue] at hContains
      contradiction
  | cons p ps =>
      simp [native_seq_replace_eq_indexof, hNeg]

theorem native_seq_replace_eq_self_iff_contains_false
    (xs pat repl : List SmtValue) (hPatRepl : pat ≠ repl) :
    native_seq_replace xs pat repl = xs ↔
      native_seq_contains xs pat = false := by
  constructor
  · intro hReplace
    cases hContains : native_seq_contains xs pat with
    | false => rfl
    | true =>
        exfalso
        have hNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
          unfold native_seq_contains at hContains
          exact of_decide_eq_true hContains
        cases pat with
        | nil =>
            have hExpanded : repl ++ xs = xs := by
              simpa [native_seq_replace_eq_indexof,
                native_seq_indexof_nil_zero] using hReplace
            have hLen := congrArg List.length hExpanded
            have hReplNil : repl = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [List.length_append] at hLen
              omega
            exact hPatRepl hReplNil.symm
        | cons p ps =>
            let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
            have hNotNeg : ¬ native_seq_indexof xs (p :: ps) 0 < 0 :=
              Int.not_lt_of_ge hNonneg
            have hExpanded :
                xs.take n ++ repl ++
                    xs.drop (n + (p :: ps).length) = xs := by
              simpa [native_seq_replace_eq_indexof, hNotNeg, n] using hReplace
            have hDecomp :
                xs.take n ++ (p :: ps) ++
                    xs.drop (n + (p :: ps).length) = xs := by
              simpa [n] using
                native_seq_indexof_zero_decomp_take_drop xs (p :: ps)
                  hNonneg
            have hBoth := hExpanded.trans hDecomp.symm
            have hBoth' :
                xs.take n ++
                    (repl ++ xs.drop (n + (p :: ps).length)) =
                  xs.take n ++
                    ((p :: ps) ++ xs.drop (n + (p :: ps).length)) := by
              simpa [List.append_assoc] using hBoth
            have hTail :
                repl ++ xs.drop (n + (p :: ps).length) =
                  (p :: ps) ++ xs.drop (n + (p :: ps).length) :=
              List.append_cancel_left hBoth'
            have hEq : repl = p :: ps := List.append_cancel_right hTail
            exact hPatRepl hEq.symm
  · exact native_seq_replace_eq_self_of_contains_false xs pat repl

theorem native_seq_replace_length_le_of_repl_length_le
    (xs pat repl : List SmtValue) (hReplLe : repl.length ≤ pat.length) :
    (native_seq_replace xs pat repl).length ≤ xs.length := by
  cases pat with
  | nil =>
      have hReplNil : repl = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hReplLe)
      subst repl
      simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace_eq_indexof, hNeg]
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
          int_nonneg_of_not_neg hNeg
        have hReplLe' : repl.length ≤ ps.length + 1 := by
          simpa using hReplLe
        have hBound := native_seq_indexof_zero_bounds_of_nonneg
          xs (p :: ps) hNonneg
        have hIndexLe :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) ≤ xs.length := by
          omega
        simp [native_seq_replace_eq_indexof, hNeg, List.length_append,
          List.length_take, List.length_drop, Nat.min_eq_left hIndexLe]
        omega

theorem native_seq_contains_false_of_source_len_lt_pattern
    (xs pat : List SmtValue) (hLen : xs.length < pat.length) :
    native_seq_contains xs pat = false := by
  unfold native_seq_contains
  rw [native_seq_indexof_eq_rec]
  have hBounds : ¬ pat.length ≤ xs.length := Nat.not_le_of_gt hLen
  simp [hBounds]

theorem eq_of_native_seq_contains_of_same_len
    (xs pat : List SmtValue)
    (hContains : native_seq_contains xs pat = true)
    (hLen : xs.length = pat.length) :
    xs = pat := by
  have hNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at hContains
    exact of_decide_eq_true hContains
  let n := Int.toNat (native_seq_indexof xs pat 0)
  have hDecomp :
      xs.take n ++ pat ++ xs.drop (n + pat.length) = xs := by
    simpa [n] using native_seq_indexof_zero_decomp_take_drop xs pat hNonneg
  have hLenDecomp := congrArg List.length hDecomp
  have hTakeNil : xs.take n = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append] at hLenDecomp
    omega
  have hDropNil : xs.drop (n + pat.length) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append] at hLenDecomp
    omega
  simpa [hTakeNil, hDropNil] using hDecomp.symm

theorem native_seq_replace_src_self
    (xs pat repl : List SmtValue) :
    native_seq_replace xs (native_seq_replace pat xs pat) repl =
      native_seq_replace xs pat repl := by
  by_cases hContains : native_seq_contains xs pat = true
  · have hNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
      unfold native_seq_contains at hContains
      exact of_decide_eq_true hContains
    let n := Int.toNat (native_seq_indexof xs pat 0)
    have hDecomp :
        xs.take n ++ pat ++ xs.drop (n + pat.length) = xs := by
      simpa [n] using
        native_seq_indexof_zero_decomp_take_drop xs pat hNonneg
    have hLenEq := congrArg List.length hDecomp
    have hLen : pat.length ≤ xs.length := by
      simp only [List.length_append] at hLenEq
      omega
    have hInner : native_seq_replace pat xs pat = pat :=
      native_seq_replace_source_of_pat_len_ge pat xs hLen
    rw [hInner]
  · have hContainsFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hContains h)
    rw [native_seq_replace_eq_self_of_contains_false
      xs pat repl hContainsFalse]
    by_cases hReverse : native_seq_contains pat xs = true
    · have hReverseNonneg : 0 ≤ native_seq_indexof pat xs 0 := by
        unfold native_seq_contains at hReverse
        exact of_decide_eq_true hReverse
      let n := Int.toNat (native_seq_indexof pat xs 0)
      have hReverseDecomp :
          pat.take n ++ xs ++ pat.drop (n + xs.length) = pat := by
        simpa [n] using
          native_seq_indexof_zero_decomp_take_drop pat xs hReverseNonneg
      have hReverseLenEq := congrArg List.length hReverseDecomp
      have hLe : xs.length ≤ pat.length := by
        simp only [List.length_append] at hReverseLenEq
        omega
      have hLenNe : xs.length ≠ pat.length := by
        intro hSameLen
        have hEq : pat = xs :=
          eq_of_native_seq_contains_of_same_len pat xs hReverse hSameLen.symm
        subst pat
        rw [native_seq_contains_self] at hContainsFalse
        contradiction
      have hLt : xs.length < pat.length := by omega
      have hInnerLen :
          pat.length ≤ (native_seq_replace pat xs pat).length :=
        native_seq_replace_self_replacement_len_ge pat xs
      have hTooLong :
          xs.length < (native_seq_replace pat xs pat).length := by omega
      have hInnerAbsent :=
        native_seq_contains_false_of_source_len_lt_pattern
          xs (native_seq_replace pat xs pat) hTooLong
      exact native_seq_replace_eq_self_of_contains_false
        xs (native_seq_replace pat xs pat) repl hInnerAbsent
    · have hReverseFalse : native_seq_contains pat xs = false := by
        cases h : native_seq_contains pat xs
        · rfl
        · exact False.elim (hReverse h)
      have hInner := native_seq_replace_eq_self_of_contains_false
        pat xs pat hReverseFalse
      rw [hInner]
      exact native_seq_replace_eq_self_of_contains_false
        xs pat repl hContainsFalse

theorem native_seq_replace_eq_repl_iff_of_same_len
    (xs pat repl : List SmtValue)
    (hLen : pat.length = repl.length) :
    native_seq_replace xs pat repl = repl ↔ xs = pat ∨ xs = repl := by
  cases pat with
  | nil =>
      have hReplLen : repl.length = 0 := hLen.symm
      have hReplNil : repl = [] := List.eq_nil_of_length_eq_zero hReplLen
      subst repl
      simp [native_seq_replace_eq_indexof, native_seq_indexof_nil_zero]
  | cons p ps =>
      constructor
      · intro hReplace
        by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
        · right
          simpa [native_seq_replace_eq_indexof, hNeg] using hReplace
        · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
            int_nonneg_of_not_neg hNeg
          let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
          have hExpanded :
              xs.take n ++ repl ++ xs.drop (n + (p :: ps).length) =
                repl := by
            simpa [native_seq_replace_eq_indexof, hNeg, n] using hReplace
          have hLenExpanded := congrArg List.length hExpanded
          have hTakeNil : xs.take n = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_append] at hLenExpanded
            omega
          have hDropNil : xs.drop (n + (p :: ps).length) = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_append] at hLenExpanded
            omega
          have hDropNil' : xs.drop (n + (ps.length + 1)) = [] := by
            simpa using hDropNil
          have hDecomp :
              xs.take n ++ (p :: ps) ++
                  xs.drop (n + (p :: ps).length) =
                xs := by
            simpa [n] using
              native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
          left
          simpa [hTakeNil, hDropNil'] using hDecomp.symm
      · rintro (rfl | rfl)
        · exact native_seq_replace_self (p :: ps) _
        · apply native_seq_replace_source_of_pat_len_ge
          omega

theorem native_seq_replace_empty_repl_eq_nil_iff_of_pat_ne_nil
    (xs pat : List SmtValue) (hPat : pat ≠ []) :
    native_seq_replace xs pat [] = [] ↔ xs = [] ∨ xs = pat := by
  constructor
  · intro hReplace
    cases pat with
    | nil => exact False.elim (hPat rfl)
    | cons p ps =>
        by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
        · left
          simpa [native_seq_replace_eq_indexof, hNeg] using hReplace
        · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
            int_nonneg_of_not_neg hNeg
          let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
          have hExpanded :
              xs.take n ++ xs.drop (n + (p :: ps).length) = [] := by
            simpa [native_seq_replace_eq_indexof, hNeg, n] using hReplace
          have hParts := List.append_eq_nil_iff.mp hExpanded
          have hDecomp :
              xs.take n ++ (p :: ps) ++
                  xs.drop (n + (p :: ps).length) = xs := by
            simpa [n] using
              native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
          right
          have hTakeNil : xs.take n = [] := hParts.1
          have hDropNil : xs.drop (n + (p :: ps).length) = [] := hParts.2
          rw [hTakeNil, hDropNil] at hDecomp
          simpa using hDecomp.symm
  · intro hCases
    rcases hCases with hXsNil | hXsPat
    · subst xs
      rw [native_seq_replace_empty_src]
      simp [hPat]
    · subst xs
      exact native_seq_replace_self pat []

theorem native_seq_extract_zero_nat_any
    (xs : List SmtValue) (n : Nat) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  by_cases hle : n ≤ xs.length
  · exact native_seq_extract_zero_nat xs n hle
  · cases xs with
    | nil =>
        simp [native_seq_extract]
    | cons x xs =>
        unfold native_seq_extract
        have hn : n ≠ 0 := by
          intro hn
          subst n
          simp at hle
        have hLenLt : (x :: xs).length < n := Nat.lt_of_not_ge hle
        have hLenLe : (x :: xs).length ≤ n := Nat.le_of_lt hLenLt
        have hmin :
            min (Int.ofNat n) (Int.ofNat (x :: xs).length) =
              Int.ofNat (x :: xs).length :=
          Int.min_eq_right (Int.ofNat_le.mpr hLenLe)
        have hminToNat :
            (min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat =
              (x :: xs).length := by
          rw [hmin]
          simp
        simp [hn]
        change
          (x :: xs).take
              ((min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat) =
            (x :: xs).take n
        rw [hminToNat,
          List.take_of_length_le (Nat.le_refl (x :: xs).length),
          List.take_of_length_le hLenLe]

theorem smtx_eval_str_prefixof_len_one_eq
    (sx sy : SmtSeq) (T : SmtType)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T)
    (hLen : (native_unpack_seq sy).length = 1) :
    __smtx_model_eval_str_prefixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      SmtValue.Boolean
        (decide (native_unpack_seq sx = [] ∨ sx = sy)) := by
  let xs := native_unpack_seq sx
  let ys := native_unpack_seq sy
  have hSxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  have hSxPack : native_pack_seq T xs = sx := by
    simpa [xs, hSxElem] using native_pack_unpack_seq sx
  have hSyPack : native_pack_seq T ys = sy := by
    simpa [ys, hSyElem] using native_pack_unpack_seq sy
  have hExtract :
      native_seq_extract ys 0 (Int.ofNat xs.length) = ys.take xs.length := by
    exact native_seq_extract_zero_nat_any ys xs.length
  have hYsLen : ys.length = 1 := by
    simpa [ys] using hLen
  have hSeqIff :
      sx = native_pack_seq T (ys.take xs.length) ↔
        xs = [] ∨ sx = sy := by
    by_cases hXsNil : xs = []
    · have hSxPackNil : native_pack_seq T [] = sx := by
        calc
          native_pack_seq T [] = native_pack_seq T xs := by rw [hXsNil]
          _ = sx := hSxPack
      rw [hXsNil]
      simp only [List.length_nil, List.take_zero, true_or, iff_true]
      exact hSxPackNil.symm
    · have hXsLenNe : xs.length ≠ 0 := by
        intro hZero
        exact hXsNil (List.eq_nil_of_length_eq_zero hZero)
      have hXsPos : 1 ≤ xs.length := by omega
      have hTake : ys.take xs.length = ys := by
        apply List.take_of_length_le
        omega
      rw [hTake, hSyPack]
      simp [hXsNil]
  have hExtractRaw :
      native_seq_extract (native_unpack_seq sy) 0
          (Int.ofNat (native_unpack_seq sx).length) =
        (native_unpack_seq sy).take (native_unpack_seq sx).length := by
    simpa [xs, ys] using hExtract
  calc
    __smtx_model_eval_str_prefixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
        SmtValue.Boolean
          (native_veq (SmtValue.Seq sx)
            (SmtValue.Seq (native_pack_seq T (ys.take xs.length)))) := by
      simp only [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
        __smtx_model_eval_str_substr, __smtx_model_eval_eq, native_seq_len]
      rw [hSyElem, hExtractRaw]
    _ = SmtValue.Boolean
          (decide (native_unpack_seq sx = [] ∨ sx = sy)) := by
      simp [native_veq, xs, hSeqIff]

theorem list_eq_nil_of_native_seq_len_zero (xs : List SmtValue)
    (h : native_seq_len xs = 0) :
    xs = [] := by
  have hLenInt : (xs.length : Int) = 0 := by
    simpa [native_seq_len] using h
  have hLenNat : xs.length = 0 := by
    omega
  exact List.eq_nil_of_length_eq_zero hLenNat

theorem seq_eq_of_unpack_eq_of_elem_eq
    (s t : SmtSeq)
    (hElem : __smtx_elem_typeof_seq_value s = __smtx_elem_typeof_seq_value t)
    (hUnpack : native_unpack_seq s = native_unpack_seq t) :
    s = t := by
  calc
    s = native_pack_seq (__smtx_elem_typeof_seq_value s)
        (native_unpack_seq s) := (native_pack_unpack_seq s).symm
    _ = native_pack_seq (__smtx_elem_typeof_seq_value t)
        (native_unpack_seq t) := by rw [hElem, hUnpack]
    _ = t := native_pack_unpack_seq t

end StrEqReplSupport
