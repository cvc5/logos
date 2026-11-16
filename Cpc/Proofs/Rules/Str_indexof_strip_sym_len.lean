module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev stripSymShiftPremise (m n s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq m)
    (Term.Apply (Term.Apply Term.neg n) (Term.Apply Term.str_len s))

private abbrev stripSymNonnegPremise (m : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq m) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev stripSymLePremise (s m : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s)) m))
    (Term.Boolean true)

private abbrev stripSymContainsPremise (s m t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.str_contains
          (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) m)
            (Term.Apply Term.str_len s)))
        t))
    (Term.Boolean true)

private abbrev stripSymGenTail (s₁ s₂ : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.str_concat s₂)
    (__eo_nil Term.str_concat (__eo_typeof s₁))

private abbrev stripSymIdx (s₂ t m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof s₂) t) m

private abbrev stripSymRhs (s₁ s₂ t m : Term) : Term :=
  Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len s₁))
    (Term.Apply (Term.Apply Term.plus (stripSymIdx s₂ t m))
      (Term.Numeral 0))

private abbrev stripSymGenConclusion (s₁ s₂ t n m : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply Term.eq
      (__eo_mk_apply
        (__eo_mk_apply
          (__eo_mk_apply Term.str_indexof
            (__eo_mk_apply (Term.Apply Term.str_concat s₁)
              (stripSymGenTail s₁ s₂))) t) n))
    (stripSymRhs s₁ s₂ t m)

private abbrev stripSymLhs (s₁ s₂ t n : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.str_indexof
        (Term.Apply (Term.Apply Term.str_concat s₁)
          (Term.Apply (Term.Apply Term.str_concat s₂)
            (__seq_empty (__eo_typeof s₁))))) t) n

private abbrev stripSymConclusion (s₁ s₂ t n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (stripSymLhs s₁ s₂ t n))
    (stripSymRhs s₁ s₂ t m)

private theorem eo_and_eq_true_parts
    (A B : Term)
    (h : __eo_and A B = Term.Boolean true) :
    A = Term.Boolean true ∧ B = Term.Boolean true := by
  cases A <;> cases B <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean => exact h
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hw : w₁ = w₂ <;>
      simp [__eo_requires, hw, native_teq, native_ite,
        SmtEval.native_not] at h

private theorem mk_apply_info (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x ∧ f ≠ Term.Stuck ∧
      x ≠ Term.Stuck := by
  by_cases hf : f = Term.Stuck
  · subst hf
    simp [__eo_mk_apply] at h
  · by_cases hx : x = Term.Stuck
    · subst hx
      cases f <;> simp [__eo_mk_apply] at h
    · refine ⟨?_, hf, hx⟩
      cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_typeof_str_indexof_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_indexof A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Apply Term.Seq T ∧
      C = Term.Int := by
  cases A <;> simp [__eo_typeof_str_indexof] at h ⊢
  case Apply fA aA =>
    cases fA <;> simp at h ⊢
    case UOp opA =>
      cases opA <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case Apply fB aB =>
          cases fB <;> simp at h ⊢
          case UOp opB =>
            cases opB <;> simp at h ⊢
            case Seq =>
              cases C <;> simp at h ⊢
              case UOp opC =>
                cases opC <;> simp at h ⊢
                case Int =>
                  have hCond : __eo_eq aA aB = Term.Boolean true :=
                    support_eo_requires_cond_eq_of_non_stuck h
                  have hBA : aB = aA :=
                    support_eq_of_eo_eq_true aA aB hCond
                  subst aB
                  simp

private theorem stripSym_smtx_typeof_of_eo_seq
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

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

private theorem smtx_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

private theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op =>
    cases op <;> simp [__seq_empty, Term.Seq]

private theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_indexof_nonneg_of_drop_contains
    (xs pat : List SmtValue) (i : native_Int)
    (hINonneg : 0 ≤ i) (hILe : Int.toNat i ≤ xs.length)
    (hContains : native_seq_contains (xs.drop (Int.toNat i)) pat = true) :
    0 ≤ native_seq_indexof xs pat i := by
  rcases (native_seq_contains_iff_decomp
      (xs.drop (Int.toNat i)) pat).1 hContains with
    ⟨before, after, hDrop⟩
  have hLengths := congrArg List.length hDrop
  have hBounds : Int.toNat i + pat.length ≤ xs.length := by
    rw [List.length_drop] at hLengths
    simp only [List.length_append] at hLengths
    omega
  have hFuel :
      before.length < xs.length - (Int.toNat i + pat.length) + 1 := by
    rw [List.length_drop] at hLengths
    simp only [List.length_append] at hLengths
    omega
  have hRecNe :
      native_seq_indexof_rec (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) ≠ -1 := by
    rw [hDrop]
    exact native_seq_indexof_rec_append_ne_neg pat after before
      (Int.toNat i) (xs.length - (Int.toNat i + pat.length) + 1) hFuel
  rw [native_seq_indexof_eq_rec]
  rw [ite_eq_right (Int.not_lt_of_ge hINonneg)]
  rw [dite_eq_left hBounds]
  rcases native_seq_indexof_rec_eq_neg_one_or_ge
      (xs.drop (Int.toNat i)) pat (Int.toNat i)
      (xs.length - (Int.toNat i + pat.length) + 1) with hNeg | hGe
  · exact False.elim (hRecNe hNeg)
  · exact Int.le_trans (Int.natCast_nonneg _) hGe

private theorem native_seq_indexof_rec_offset_local
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
        rw [ite_eq_left hPrefix, ite_eq_left hPrefix]
        have hne : (Int.ofNat i : Int) ≠ -1 := by
          intro h
          have hNonneg : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
          omega
        rw [ite_eq_right hne]
        simp
      · unfold native_seq_indexof_rec
        rw [ite_eq_right hPrefix, ite_eq_right hPrefix]
        cases xs with
        | nil =>
            simp
        | cons _ xs =>
            rw [show i + off + 1 = (i + 1) + off by omega]
            exact native_seq_indexof_rec_offset_local xs pat (i + 1) off fuel

private theorem native_seq_indexof_rec_shift
    (xs pat : List SmtValue) (i off fuel : Nat) :
    native_seq_indexof_rec xs pat (off + i) fuel =
      (let r := native_seq_indexof_rec xs pat i fuel
       if r = (-1 : Int) then (-1 : Int) else r + Int.ofNat off) := by
  rw [Nat.add_comm]
  exact native_seq_indexof_rec_offset_local xs pat i off fuel

/-- Core list lemma: searching past a prefix shifts the index by its length. -/
private theorem native_seq_indexof_append_prefix_shift
    (xs ys pat : List SmtValue) (m : Int)
    (hM : 0 ≤ m) (hMLe : Int.toNat m ≤ ys.length)
    (hContains : native_seq_contains (ys.drop (Int.toNat m)) pat = true) :
    native_seq_indexof (xs ++ ys) pat ((xs.length : Int) + m) =
      (xs.length : Int) + native_seq_indexof ys pat m := by
  have hNonneg :=
    native_seq_indexof_nonneg_of_drop_contains ys pat m hM hMLe hContains
  rcases (native_seq_contains_iff_decomp
      (ys.drop (Int.toNat m)) pat).1 hContains with
    ⟨before, after, hDrop⟩
  have hLengths := congrArg List.length hDrop
  rw [List.length_drop] at hLengths
  simp only [List.length_append] at hLengths
  have hBounds : Int.toNat m + pat.length ≤ ys.length := by omega
  have hToNat :
      Int.toNat ((xs.length : Int) + m) = xs.length + Int.toNat m := by
    omega
  have hNotNeg : ¬ ((xs.length : Int) + m) < 0 := by omega
  have hBoundsApp :
      Int.toNat ((xs.length : Int) + m) + pat.length ≤ (xs ++ ys).length := by
    rw [hToNat, List.length_append]
    omega
  have hDropApp :
      (xs ++ ys).drop (xs.length + Int.toNat m) = ys.drop (Int.toNat m) := by
    simp [List.drop_append]
  have hFuelApp :
      (xs ++ ys).length - (xs.length + Int.toNat m + pat.length) + 1 =
        ys.length - (Int.toNat m + pat.length) + 1 := by
    rw [List.length_append]
    omega
  have hYs :
      native_seq_indexof ys pat m =
        native_seq_indexof_rec (ys.drop (Int.toNat m)) pat (Int.toNat m)
          (ys.length - (Int.toNat m + pat.length) + 1) := by
    rw [native_seq_indexof_eq_rec, ite_eq_right (Int.not_lt_of_ge hM),
      dite_eq_left hBounds]
  rw [native_seq_indexof_eq_rec, ite_eq_right hNotNeg,
    dite_eq_left hBoundsApp, hToNat, hDropApp, hFuelApp,
    native_seq_indexof_rec_shift, ← hYs]
  have hNe : native_seq_indexof ys pat m ≠ -1 := by
    intro h
    rw [h] at hNonneg
    exact absurd hNonneg (by decide)
  simp only [hNe, ite_false]
  exact Int.add_comm _ _

private theorem eqs10_of_requires_nested_and_eq_true_not_stuck
    (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ x₆ y₆ x₇ y₇ x₈ y₈ x₉ y₉ x₁₀ y₁₀
      B : Term)
    (h :
      __eo_requires
        (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and
          (__eo_and (__eo_and (__eo_and (__eo_eq x₁ y₁) (__eo_eq x₂ y₂))
            (__eo_eq x₃ y₃)) (__eo_eq x₄ y₄)) (__eo_eq x₅ y₅))
            (__eo_eq x₆ y₆)) (__eo_eq x₇ y₇)) (__eo_eq x₈ y₈))
            (__eo_eq x₉ y₉)) (__eo_eq x₁₀ y₁₀))
        (Term.Boolean true) B ≠ Term.Stuck) :
    y₁ = x₁ ∧ y₂ = x₂ ∧ y₃ = x₃ ∧ y₄ = x₄ ∧ y₅ = x₅ ∧ y₆ = x₆ ∧
      y₇ = x₇ ∧ y₈ = x₈ ∧ y₉ = x₉ ∧ y₁₀ = x₁₀ := by
  have hGuard := support_eo_requires_cond_eq_of_non_stuck h
  have h₁₀ := eo_and_eq_true_parts _ _ hGuard
  have h₉ := eo_and_eq_true_parts _ _ h₁₀.1
  have h₈ := eo_and_eq_true_parts _ _ h₉.1
  have h₇ := eo_and_eq_true_parts _ _ h₈.1
  have h₆ := eo_and_eq_true_parts _ _ h₇.1
  have h₅ := eo_and_eq_true_parts _ _ h₆.1
  have h₄ := eo_and_eq_true_parts _ _ h₅.1
  have h₃ := eo_and_eq_true_parts _ _ h₄.1
  have h₂ := eo_and_eq_true_parts _ _ h₃.1
  exact ⟨RuleProofs.eq_of_eo_eq_true _ _ h₂.1,
    RuleProofs.eq_of_eo_eq_true _ _ h₂.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₃.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₄.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₅.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₆.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₇.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₈.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₉.2,
    RuleProofs.eq_of_eo_eq_true _ _ h₁₀.2⟩

private theorem prog_str_indexof_strip_sym_len_info
    (s₁ s₂ t n m P₁ P₂ P₃ P₄ : Term)
    (hProg :
      __eo_prog_str_indexof_strip_sym_len s₁ s₂ t n m
          (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) (Proof.pf P₄) ≠
        Term.Stuck) :
    P₁ = stripSymShiftPremise m n s₁ ∧
      P₂ = stripSymNonnegPremise m ∧
      P₃ = stripSymLePremise s₂ m ∧
      P₄ = stripSymContainsPremise s₂ m t ∧
      __eo_prog_str_indexof_strip_sym_len s₁ s₂ t n m
          (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) (Proof.pf P₄) =
        stripSymGenConclusion s₁ s₂ t n m := by
  unfold __eo_prog_str_indexof_strip_sym_len at hProg
  split at hProg <;> try contradiction
  next heq₁ heq₂ heq₃ heq₄ =>
    cases heq₁
    cases heq₂
    cases heq₃
    cases heq₄
    rcases eqs10_of_requires_nested_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hProg with
      ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
    subst_vars
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_strip_sym_len, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, stripSymGenConclusion, stripSymGenTail,
      stripSymRhs, stripSymIdx]

private theorem eo_typeof_plus_right_ne_stuck (A B : Term)
    (h : __eo_typeof_plus A B ≠ Term.Stuck) : B ≠ Term.Stuck := by
  intro hB
  subst hB
  cases A <;> simp [__eo_typeof_plus] at h

/-- From a well-typed generated conclusion, recover the argument types and the
reduced conclusion shape. -/
private theorem gen_conclusion_info
    (s₁ s₂ t n m : Term)
    (hTy : __eo_typeof (stripSymGenConclusion s₁ s₂ t n m) = Term.Bool) :
    ∃ T, __eo_typeof s₁ = Term.Apply Term.Seq T ∧
      __eo_typeof s₂ = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧
      __eo_typeof m = Term.Int ∧
      stripSymGenConclusion s₁ s₂ t n m =
        stripSymConclusion s₁ s₂ t n m := by
  have hNS := term_ne_stuck_of_typeof_bool hTy
  rcases mk_apply_info _ _ hNS with ⟨hE₁, hEqL, _⟩
  rcases mk_apply_info _ _ hEqL with ⟨hE₂, _, hL⟩
  rcases mk_apply_info _ _ hL with ⟨hE₃, hL₂, _⟩
  rcases mk_apply_info _ _ hL₂ with ⟨hE₄, hL₃, _⟩
  rcases mk_apply_info _ _ hL₃ with ⟨hE₅, _, hC⟩
  rcases mk_apply_info _ _ hC with ⟨hE₆, _, hZ⟩
  have hGen :
      stripSymGenConclusion s₁ s₂ t n m =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.str_indexof
                  (Term.Apply (Term.Apply Term.str_concat s₁)
                    (stripSymGenTail s₁ s₂))) t) n))
          (stripSymRhs s₁ s₂ t m) := by
    simp only [stripSymGenConclusion] at hE₁ hE₂ hE₃ hE₄ hE₅ hE₆ ⊢
    rw [hE₁, hE₂, hE₃, hE₄, hE₅, hE₆]
  rw [hGen] at hTy
  have hOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hLeftNN := hOps.1
  have hRightNN := hOps.2
  change __eo_typeof_str_indexof
      (__eo_typeof
        (Term.Apply (Term.Apply Term.str_concat s₁)
          (stripSymGenTail s₁ s₂)))
      (__eo_typeof t) (__eo_typeof n) ≠ Term.Stuck at hLeftNN
  rcases eo_typeof_str_indexof_args_of_ne_stuck _ _ _ hLeftNN with
    ⟨T, hConcatTy, hTTy, hNTy⟩
  change __eo_typeof_plus (__eo_typeof (Term.Apply Term.str_len s₁))
      (__eo_typeof_plus (__eo_typeof (stripSymIdx s₂ t m))
        (__eo_typeof (Term.Numeral 0))) ≠ Term.Stuck at hRightNN
  have hIdxNN :=
    eo_typeof_plus_right_ne_stuck _ _ hRightNN
  have hIdxNN' : __eo_typeof (stripSymIdx s₂ t m) ≠ Term.Stuck := by
    intro h
    rw [h] at hIdxNN
    exact hIdxNN rfl
  change __eo_typeof_str_indexof (__eo_typeof s₂) (__eo_typeof t)
      (__eo_typeof m) ≠ Term.Stuck at hIdxNN'
  rcases eo_typeof_str_indexof_args_of_ne_stuck _ _ _ hIdxNN' with
    ⟨U, _, _, hMTy⟩
  have hArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      s₁ (stripSymGenTail s₁ s₂) T hConcatTy
  have hNil :
      __eo_nil Term.str_concat (__eo_typeof s₁) =
        __seq_empty (__eo_typeof s₁) := by
    rw [hArgs.1]
    rfl
  have hTail :
      stripSymGenTail s₁ s₂ =
        Term.Apply (Term.Apply Term.str_concat s₂)
          (__seq_empty (__eo_typeof s₁)) := by
    simp only [stripSymGenTail]
    rw [hNil]
    exact (mk_apply_info _ _ (by
      rw [← hNil]
      exact hZ)).1
  have hTailTy := hArgs.2
  rw [hTail] at hTailTy
  have hArgs₂ :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      s₂ (__seq_empty (__eo_typeof s₁)) T hTailTy
  refine ⟨T, hArgs.1, hArgs₂.1, hTTy, hNTy, hMTy, ?_⟩
  rw [hGen, hTail]

private theorem smtx_typeof_conclusion_sides
    (s₁ s₂ t n m T : Term)
    (hS₁Trans : RuleProofs.eo_has_smt_translation s₁)
    (hS₂Trans : RuleProofs.eo_has_smt_translation s₂)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hS₁Ty : __eo_typeof s₁ = Term.Apply Term.Seq T)
    (hS₂Ty : __eo_typeof s₂ = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int) :
    RuleProofs.eo_has_bool_type (stripSymConclusion s₁ s₂ t n m) := by
  have hS₁SmtTy := stripSym_smtx_typeof_of_eo_seq s₁ T hS₁Trans hS₁Ty
  have hS₂SmtTy := stripSym_smtx_typeof_of_eo_seq s₂ T hS₂Trans hS₂Ty
  have hTSmtTy := stripSym_smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hEmptyTy :=
    smtx_typeof_seq_empty_typeof_of_smt_type_seq s₁ (__eo_to_smt_type T)
      hS₁SmtTy
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt s₂)
            (__eo_to_smt (__seq_empty (__eo_typeof s₁)))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hS₂SmtTy, hEmptyTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hConcatTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt s₁)
            (SmtTerm.str_concat (__eo_to_smt s₂)
              (__eo_to_smt (__seq_empty (__eo_typeof s₁))))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hS₁SmtTy, hInnerTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (stripSymLhs s₁ s₂ t n)) =
        SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof
          (SmtTerm.str_concat (__eo_to_smt s₁)
            (SmtTerm.str_concat (__eo_to_smt s₂)
              (__eo_to_smt (__seq_empty (__eo_typeof s₁)))))
          (__eo_to_smt t) (__eo_to_smt n)) = SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hConcatTy, hTSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hIdxTy :
      __smtx_typeof
          (SmtTerm.str_indexof (__eo_to_smt s₂) (__eo_to_smt t)
            (__eo_to_smt m)) = SmtType.Int := by
    rw [typeof_str_indexof_eq]
    simp [hS₂SmtTy, hTSmtTy, hMSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hRightTy :
      __smtx_typeof (__eo_to_smt (stripSymRhs s₁ s₂ t m)) =
        SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt s₁))
          (SmtTerm.plus
            (SmtTerm.str_indexof (__eo_to_smt s₂) (__eo_to_smt t)
              (__eo_to_smt m))
            (SmtTerm.Numeral 0))) = SmtType.Int
    rw [typeof_plus_eq, typeof_plus_eq, typeof_str_len_eq, hIdxTy]
    simp [hS₁SmtTy, __smtx_typeof_seq_op_1_ret,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq,
      __smtx_typeof.eq_def]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLeftTy, hRightTy]) (by rw [hLeftTy]; simp)

private theorem smtx_eval_neg_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem facts_strip_sym_len
    (M : SmtModel) (hM : model_wf M)
    (s₁ s₂ t n m T : Term)
    (hS₁Trans : RuleProofs.eo_has_smt_translation s₁)
    (hS₂Trans : RuleProofs.eo_has_smt_translation s₂)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hS₁Ty : __eo_typeof s₁ = Term.Apply Term.Seq T)
    (hS₂Ty : __eo_typeof s₂ = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hPremShift : eo_interprets M (stripSymShiftPremise m n s₁) true)
    (hPremNonneg : eo_interprets M (stripSymNonnegPremise m) true)
    (hPremLe : eo_interprets M (stripSymLePremise s₂ m) true)
    (hPremContains :
      eo_interprets M (stripSymContainsPremise s₂ m t) true) :
    eo_interprets M (stripSymConclusion s₁ s₂ t n m) true := by
  have hBool :=
    smtx_typeof_conclusion_sides s₁ s₂ t n m T hS₁Trans hS₂Trans hTTrans
      hNTrans hMTrans hS₁Ty hS₂Ty hTTy hNTy hMTy
  have hS₁SmtTy := stripSym_smtx_typeof_of_eo_seq s₁ T hS₁Trans hS₁Ty
  have hS₂SmtTy := stripSym_smtx_typeof_of_eo_seq s₂ T hS₂Trans hS₂Ty
  have hTSmtTy := stripSym_smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hEvalTy : ∀ (x : Term) (U : SmtType),
      __smtx_typeof (__eo_to_smt x) = U → U ≠ SmtType.None →
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) = U := by
    intro x U hx hU
    have := smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
      (by unfold term_has_non_none_type; rw [hx]; exact hU)
    rw [hx] at this
    exact this
  rcases seq_value_canonical
      (hEvalTy s₁ _ hS₁SmtTy (by simp)) with ⟨ss₁, hS₁Eval⟩
  rcases seq_value_canonical
      (hEvalTy s₂ _ hS₂SmtTy (by simp)) with ⟨ss₂, hS₂Eval⟩
  rcases seq_value_canonical
      (hEvalTy t _ hTSmtTy (by simp)) with ⟨st, hTEval⟩
  rcases int_value_canonical
      (hEvalTy n _ hNSmtTy (by simp)) with ⟨ni, hNEval⟩
  rcases int_value_canonical
      (hEvalTy m _ hMSmtTy (by simp)) with ⟨mi, hMEval⟩
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof s₁))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) :=
    eval_seq_empty_typeof M s₁ (__eo_to_smt_type T) hS₁SmtTy
  have hShift : ni = ((native_unpack_seq ss₁).length : Int) + mi := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremShift
    cases hPremShift with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt m)
              (SmtTerm.neg (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt s₁)))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_neg_term_eq,
          smtx_eval_str_len_term_eq, hS₁Eval, hNEval, hMEval] at hEval
        have h : mi = ni + -((native_unpack_seq ss₁).length : Int) := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval__,
            __smtx_model_eval_eq, native_veq, native_seq_len, native_zplus,
            native_zneg] using hEval
        have h' : @Eq Int mi (ni + -((native_unpack_seq ss₁).length : Int)) :=
          h
        show @Eq Int ni (((native_unpack_seq ss₁).length : Int) + mi)
        omega
  have hMNonneg : 0 ≤ mi := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremNonneg
    cases hPremNonneg with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.geq (__eo_to_smt m) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrSubstrContainsSupport.smtx_eval_geq_term_eq, hMEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
          __smtx_model_eval_eq, native_veq, native_zleq] using hEval
  have hMLe : mi ≤ native_seq_len (native_unpack_seq ss₂) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremLe
    cases hPremLe with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt s₂))
                (__eo_to_smt m))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrSubstrContainsSupport.smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, hS₂Eval, hMEval,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
          __smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq,
          native_zleq] using hEval
  have hContainsExtract :
      native_seq_contains
          (native_seq_extract (native_unpack_seq ss₂) mi
            (native_seq_len (native_unpack_seq ss₂)))
          (native_unpack_seq st) = true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremContains
    cases hPremContains with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains
                (SmtTerm.str_substr (__eo_to_smt s₂) (__eo_to_smt m)
                  (SmtTerm.str_len (__eo_to_smt s₂)))
                (__eo_to_smt t))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          hS₂Eval, hMEval, smtx_eval_str_len_term_eq, hS₂Eval,
          hTEval, StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_substr, __smtx_model_eval_str_len,
          __smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq, Smtm.native_unpack_pack_seq] using hEval
  have hContainsDrop :
      native_seq_contains
          ((native_unpack_seq ss₂).drop (Int.toNat mi))
          (native_unpack_seq st) = true := by
    rw [← native_seq_extract_len_tail_of_bounds
      (native_unpack_seq ss₂) mi hMNonneg hMLe]
    exact hContainsExtract
  have hMLeNat : Int.toNat mi ≤ (native_unpack_seq ss₂).length := by
    have h₁ : (mi : Int) ≤ ((native_unpack_seq ss₂).length : Int) := by
      simpa [native_seq_len] using hMLe
    exact Int.toNat_le.mpr h₁
  have hCore :=
    native_seq_indexof_append_prefix_shift (native_unpack_seq ss₁)
      (native_unpack_seq ss₂) (native_unpack_seq st) mi hMNonneg hMLeNat
      hContainsDrop
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (stripSymLhs s₁ s₂ t n)) =
        __smtx_model_eval M (__eo_to_smt (stripSymRhs s₁ s₂ t m)) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof
          (SmtTerm.str_concat (__eo_to_smt s₁)
            (SmtTerm.str_concat (__eo_to_smt s₂)
              (__eo_to_smt (__seq_empty (__eo_typeof s₁)))))
          (__eo_to_smt t) (__eo_to_smt n)) =
      __smtx_model_eval M
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt s₁))
          (SmtTerm.plus
            (SmtTerm.str_indexof (__eo_to_smt s₂) (__eo_to_smt t)
              (__eo_to_smt m))
            (SmtTerm.Numeral 0)))
    rw [smtx_eval_str_indexof_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
      smtx_eval_str_indexof_term_eq, smtx_eval_str_len_term_eq,
      StrEqReplSupport.smtx_eval_numeral_term_eq,
      hS₁Eval, hS₂Eval, hTEval, hNEval, hMEval, hEmptyEval]
    simp only [__smtx_model_eval_str_indexof, __smtx_model_eval_str_concat,
      __smtx_model_eval_plus, __smtx_model_eval_str_len, native_seq_concat,
      Smtm.native_unpack_pack_seq, native_seq_len, native_zplus]
    simp only [native_unpack_seq, List.append_nil, hShift]
    simpa using congrArg SmtValue.Numeral hCore
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_str_indexof_strip_sym_len_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_strip_sym_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_strip_sym_len args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_strip_sym_len args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_indexof_strip_sym_len args
          premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons s₁ args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons s₂ args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons t args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons n args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons m args =>
  cases args with
  | cons _ _ => exact absurd rfl hProg
  | nil =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₁ premises =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₂ premises =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₃ premises =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₄ premises =>
  cases premises with
  | cons _ _ => exact absurd rfl hProg
  | nil =>
  let P₁ := __eo_state_proven_nth s i₁
  let P₂ := __eo_state_proven_nth s i₂
  let P₃ := __eo_state_proven_nth s i₃
  let P₄ := __eo_state_proven_nth s i₄
  have hS₁Trans : RuleProofs.eo_has_smt_translation s₁ := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
  have hS₂Trans : RuleProofs.eo_has_smt_translation s₂ := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
  have hNTrans : RuleProofs.eo_has_smt_translation n := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.2.1
  have hMTrans : RuleProofs.eo_has_smt_translation m := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using
      hCmdTrans.2.2.2.2.1
  change __eo_typeof
      (__eo_prog_str_indexof_strip_sym_len s₁ s₂ t n m (Proof.pf P₁)
        (Proof.pf P₂) (Proof.pf P₃) (Proof.pf P₄)) = Term.Bool at hResultTy
  have hRuleProg :
      __eo_prog_str_indexof_strip_sym_len s₁ s₂ t n m (Proof.pf P₁)
          (Proof.pf P₂) (Proof.pf P₃) (Proof.pf P₄) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases prog_str_indexof_strip_sym_len_info s₁ s₂ t n m P₁ P₂ P₃ P₄
      hRuleProg with ⟨hP₁, hP₂, hP₃, hP₄, hProgGen⟩
  rw [hProgGen] at hResultTy
  rcases gen_conclusion_info s₁ s₂ t n m hResultTy with
    ⟨T, hS₁Ty, hS₂Ty, hTTy, hNTy, hMTy, hGenEq⟩
  have hProgEq :
      __eo_prog_str_indexof_strip_sym_len s₁ s₂ t n m (Proof.pf P₁)
          (Proof.pf P₂) (Proof.pf P₃) (Proof.pf P₄) =
        stripSymConclusion s₁ s₂ t n m := by
    rw [hProgGen, hGenEq]
  have hBool :=
    smtx_typeof_conclusion_sides s₁ s₂ t n m T hS₁Trans hS₂Trans hTTrans
      hNTrans hMTrans hS₁Ty hS₂Ty hTTy hNTy hMTy
  change StepRuleProperties M (premiseTermList s _)
    (__eo_prog_str_indexof_strip_sym_len s₁ s₂ t n m (Proof.pf P₁)
      (Proof.pf P₂) (Proof.pf P₃) (Proof.pf P₄))
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hPrem₁ : eo_interprets M (stripSymShiftPremise m n s₁) true := by
      simpa [hP₁] using hTrue P₁ (by simp [P₁, premiseTermList])
    have hPrem₂ : eo_interprets M (stripSymNonnegPremise m) true := by
      simpa [hP₂] using hTrue P₂ (by simp [P₂, premiseTermList])
    have hPrem₃ : eo_interprets M (stripSymLePremise s₂ m) true := by
      simpa [hP₃] using hTrue P₃ (by simp [P₃, premiseTermList])
    have hPrem₄ :
        eo_interprets M (stripSymContainsPremise s₂ m t) true := by
      simpa [hP₄] using hTrue P₄ (by simp [P₄, premiseTermList])
    rw [hProgEq]
    exact facts_strip_sym_len M hM s₁ s₂ t n m T hS₁Trans hS₂Trans
      hTTrans hNTrans hMTrans hS₁Ty hS₂Ty hTTy hNTy hMTy hPrem₁ hPrem₂
      hPrem₃ hPrem₄
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool
