module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

public section

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-! Shared helpers for the `str_indexof_strip_*_len` rule proofs. -/

namespace StrIndexofStripSupport

theorem eo_and_eq_true_parts
    (A B : Term)
    (h : __eo_and A B = Term.Boolean true) :
    A = Term.Boolean true ∧ B = Term.Boolean true := by
  cases A <;> cases B <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean => exact h
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hw : w₁ = w₂ <;>
      simp [__eo_requires, hw, native_teq, native_ite,
        SmtEval.native_not] at h

theorem mk_apply_info (f x : Term)
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

theorem eo_typeof_str_indexof_args_of_ne_stuck
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

theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

theorem smtx_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op =>
    cases op <;> simp [__seq_empty, Term.Seq]

theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem native_seq_indexof_nonneg_of_drop_contains
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
theorem native_seq_indexof_rec_shift
    (xs pat : List SmtValue) (i off fuel : Nat) :
    native_seq_indexof_rec xs pat (off + i) fuel =
      (let r := native_seq_indexof_rec xs pat i fuel
       if r = (-1 : Int) then (-1 : Int) else r + Int.ofNat off) := by
  rw [Nat.add_comm]
  exact RuleProofs.native_seq_indexof_rec_offset xs pat i off fuel

/-- Core list lemma: searching past a prefix shifts the index by its length. -/
theorem native_seq_indexof_append_prefix_shift
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

end StrIndexofStripSupport
