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

private abbrev indexofContainsPreLenPremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len s))
        (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev indexofContainsPreContainsPremiseRaw
    (tSub n tLen s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.str_contains
          (Term.Apply
            (Term.Apply (Term.Apply Term.str_substr tSub) n)
            (Term.Apply Term.str_len tLen)))
        s))
    (Term.Boolean true)

private abbrev indexofContainsPreContainsPremise
    (t s n : Term) : Term :=
  indexofContainsPreContainsPremiseRaw t n t s

private abbrev indexofContainsPreLeft
    (t₁ t₂ s n : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.str_indexof
        (Term.Apply (Term.Apply Term.str_concat t₁) t₂)) s) n

private abbrev indexofContainsPreRight
    (t s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) s) n

private abbrev indexofContainsPreConclusion
    (t₁ t₂ s n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (indexofContainsPreLeft t₁ t₂ s n))
    (indexofContainsPreRight t₁ s n)

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

private theorem eqs5_of_requires_nested_and_eq_true_not_stuck
    (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ B : Term)
    (h :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x₁ y₁) (__eo_eq x₂ y₂))
              (__eo_eq x₃ y₃))
            (__eo_eq x₄ y₄))
          (__eo_eq x₅ y₅))
        (Term.Boolean true) B ≠ Term.Stuck) :
    y₁ = x₁ ∧ y₂ = x₂ ∧ y₃ = x₃ ∧ y₄ = x₄ ∧ y₅ = x₅ := by
  have hGuard := support_eo_requires_cond_eq_of_non_stuck h
  have h₄₅ := eo_and_eq_true_parts _ _ hGuard
  have h₃₄ := eo_and_eq_true_parts _ _ h₄₅.1
  have h₁₂₃ := eo_and_eq_true_parts _ _ h₃₄.1
  have h₁₂ := eo_and_eq_true_parts _ _ h₁₂₃.1
  exact ⟨RuleProofs.eq_of_eo_eq_true x₁ y₁ h₁₂.1,
    RuleProofs.eq_of_eo_eq_true x₂ y₂ h₁₂.2,
    RuleProofs.eq_of_eo_eq_true x₃ y₃ h₁₂₃.2,
    RuleProofs.eq_of_eo_eq_true x₄ y₄ h₃₄.2,
    RuleProofs.eq_of_eo_eq_true x₅ y₅ h₄₅.2⟩

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

private theorem smtx_typeof_indexof_contains_pre_of_eo_seq
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

private theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_indexof_nonneg_of_drop_contains
    (xs pat : List SmtValue) (i : native_Int)
    (hINonneg : 0 ≤ i) (hPat : pat ≠ [])
    (hContains : native_seq_contains (xs.drop (Int.toNat i)) pat = true) :
    0 ≤ native_seq_indexof xs pat i := by
  rcases (native_seq_contains_iff_decomp
      (xs.drop (Int.toNat i)) pat).1 hContains with
    ⟨before, after, hDrop⟩
  have hLengths := congrArg List.length hDrop
  have hPatPos : 0 < pat.length := by
    cases pat with
    | nil => exact False.elim (hPat rfl)
    | cons _ _ => simp
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
  rw [if_neg (Int.not_lt_of_ge hINonneg)]
  rw [dif_pos hBounds]
  rcases native_seq_indexof_rec_eq_neg_one_or_ge
      (xs.drop (Int.toNat i)) pat (Int.toNat i)
      (xs.length - (Int.toNat i + pat.length) + 1) with hNeg | hGe
  · exact False.elim (hRecNe hNeg)
  · exact Int.le_trans (Int.natCast_nonneg _) hGe

private theorem prog_str_indexof_contains_pre_info
    (t₁ t₂ s n P₁ P₂ : Term)
    (hProg :
      __eo_prog_str_indexof_contains_pre t₁ t₂ s n
          (Proof.pf P₁) (Proof.pf P₂) ≠ Term.Stuck) :
    ∃ sLen tSub nSub tLen sSub,
      P₁ = indexofContainsPreLenPremise sLen ∧
      P₂ = indexofContainsPreContainsPremiseRaw
        tSub nSub tLen sSub ∧
      sLen = s ∧ tSub = t₁ ∧ nSub = n ∧ tLen = t₁ ∧ sSub = s ∧
      __eo_prog_str_indexof_contains_pre t₁ t₂ s n
          (Proof.pf P₁) (Proof.pf P₂) =
        indexofContainsPreConclusion t₁ t₂ s n := by
  unfold __eo_prog_str_indexof_contains_pre at hProg
  split at hProg <;> try contradiction
  next heq₁ heq₂ =>
    cases heq₁
    cases heq₂
    rcases eqs5_of_requires_nested_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ _ _ hProg with
      ⟨hS₁, hT₁, hN, hT₂, hS₂⟩
    subst_vars
    refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_contains_pre, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, indexofContainsPreConclusion,
      indexofContainsPreLeft, indexofContainsPreRight]

private theorem typed___eo_prog_str_indexof_contains_pre_impl
    (t₁ t₂ s n P₁ P₂ T : Term)
    (hT₁Trans : RuleProofs.eo_has_smt_translation t₁)
    (hT₂Trans : RuleProofs.eo_has_smt_translation t₂)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hT₁Ty : __eo_typeof t₁ = Term.Apply Term.Seq T)
    (hT₂Ty : __eo_typeof t₂ = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hProgEq :
      __eo_prog_str_indexof_contains_pre t₁ t₂ s n
          (Proof.pf P₁) (Proof.pf P₂) =
        indexofContainsPreConclusion t₁ t₂ s n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_indexof_contains_pre t₁ t₂ s n
        (Proof.pf P₁) (Proof.pf P₂)) := by
  let left := indexofContainsPreLeft t₁ t₂ s n
  let right := indexofContainsPreRight t₁ s n
  have hT₁SmtTy :=
    smtx_typeof_indexof_contains_pre_of_eo_seq t₁ T hT₁Trans hT₁Ty
  have hT₂SmtTy :=
    smtx_typeof_indexof_contains_pre_of_eo_seq t₂ T hT₂Trans hT₂Ty
  have hSSmtTy :=
    smtx_typeof_indexof_contains_pre_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hConcatTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt t₁) (__eo_to_smt t₂)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hT₁SmtTy, hT₂SmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hLeftTy : __smtx_typeof (__eo_to_smt left) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof
          (SmtTerm.str_concat (__eo_to_smt t₁) (__eo_to_smt t₂))
          (__eo_to_smt s) (__eo_to_smt n)) = SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hConcatTy, hSSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hRightTy : __smtx_typeof (__eo_to_smt right) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt t₁) (__eo_to_smt s)
          (__eo_to_smt n)) = SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hT₁SmtTy, hSSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (indexofContainsPreConclusion t₁ t₂ s n) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type left right
      (by rw [hLeftTy, hRightTy]) (by rw [hLeftTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_indexof_contains_pre_impl
    (M : SmtModel) (hM : model_wf M)
    (t₁ t₂ s n P₁ P₂ T : Term)
    (hT₁Trans : RuleProofs.eo_has_smt_translation t₁)
    (hT₂Trans : RuleProofs.eo_has_smt_translation t₂)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hT₁Ty : __eo_typeof t₁ = Term.Apply Term.Seq T)
    (hT₂Ty : __eo_typeof t₂ = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPremLen : eo_interprets M (indexofContainsPreLenPremise s) true)
    (hPremContains :
      eo_interprets M (indexofContainsPreContainsPremise t₁ s n) true)
    (hProgEq :
      __eo_prog_str_indexof_contains_pre t₁ t₂ s n
          (Proof.pf P₁) (Proof.pf P₂) =
        indexofContainsPreConclusion t₁ t₂ s n) :
    eo_interprets M
      (__eo_prog_str_indexof_contains_pre t₁ t₂ s n
        (Proof.pf P₁) (Proof.pf P₂)) true := by
  let left := indexofContainsPreLeft t₁ t₂ s n
  let right := indexofContainsPreRight t₁ s n
  have hBool : RuleProofs.eo_has_bool_type
      (indexofContainsPreConclusion t₁ t₂ s n) := by
    simpa [hProgEq] using
      typed___eo_prog_str_indexof_contains_pre_impl
        t₁ t₂ s n P₁ P₂ T hT₁Trans hT₂Trans hSTrans hNTrans
        hT₁Ty hT₂Ty hSTy hNTy hProgEq
  have hT₁SmtTy :=
    smtx_typeof_indexof_contains_pre_of_eo_seq t₁ T hT₁Trans hT₁Ty
  have hT₂SmtTy :=
    smtx_typeof_indexof_contains_pre_of_eo_seq t₂ T hT₂Trans hT₂Ty
  have hSSmtTy :=
    smtx_typeof_indexof_contains_pre_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hT₁EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t₁)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hT₁SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t₁) (by
        unfold term_has_non_none_type
        rw [hT₁SmtTy]
        simp)
  have hT₂EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t₂)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hT₂SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t₂) (by
        unfold term_has_non_none_type
        rw [hT₂SmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases seq_value_canonical hT₁EvalTy with ⟨st₁, hT₁Eval⟩
  rcases seq_value_canonical hT₂EvalTy with ⟨st₂, hT₂Eval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hPatPos : 0 < (native_unpack_seq ss).length := by
    have hLenPos : 0 < native_seq_len (native_unpack_seq ss) := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremLen
      cases hPremLen with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq
                (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt s))
                  (SmtTerm.Numeral 0))
                (SmtTerm.Boolean true)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq,
            smtx_eval_str_len_term_eq, hSEval,
            StrEqReplSupport.smtx_eval_numeral_term_eq,
            StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
          simpa [__smtx_model_eval_gt, __smtx_model_eval_lt,
            __smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_zlt] using hEval
    simpa [native_seq_len] using hLenPos
  have hPatNe : native_unpack_seq ss ≠ [] := by
    intro hNil
    rw [hNil] at hPatPos
    simp at hPatPos
  have hContainsExtract :
      native_seq_contains
          (native_seq_extract (native_unpack_seq st₁) ni
            (native_seq_len (native_unpack_seq st₁)))
          (native_unpack_seq ss) = true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremContains
    cases hPremContains with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains
                (SmtTerm.str_substr (__eo_to_smt t₁) (__eo_to_smt n)
                  (SmtTerm.str_len (__eo_to_smt t₁)))
                (__eo_to_smt s))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          hT₁Eval, hNEval, smtx_eval_str_len_term_eq, hT₁Eval,
          hSEval, StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_substr, __smtx_model_eval_str_len,
          __smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq, Smtm.native_unpack_pack_seq] using hEval
  have hNNonneg : 0 ≤ ni := by
    by_cases hNeg : ni < 0
    · have hExtractEmpty :
          native_seq_extract (native_unpack_seq st₁) ni
              (native_seq_len (native_unpack_seq st₁)) = [] := by
        simp [native_seq_extract, hNeg]
      have hFalse :=
        StrEqReplSupport.native_seq_contains_false_of_source_len_lt_pattern
          ([] : List SmtValue) (native_unpack_seq ss) (by
            simpa using hPatPos)
      rw [hExtractEmpty, hFalse] at hContainsExtract
      contradiction
    · exact int_nonneg_of_not_neg hNeg
  have hNLeLen : ni ≤ native_seq_len (native_unpack_seq st₁) := by
    by_cases hLe : ni ≤ native_seq_len (native_unpack_seq st₁)
    · exact hLe
    · have hGt : native_seq_len (native_unpack_seq st₁) < ni :=
        Int.lt_of_not_ge hLe
      have hLenLe :
          (Int.ofNat (native_unpack_seq st₁).length : Int) ≤ ni := by
        simpa [native_seq_len] using Int.le_of_lt hGt
      have hExtractEmpty :
          native_seq_extract (native_unpack_seq st₁) ni
              (native_seq_len (native_unpack_seq st₁)) = [] := by
        unfold native_seq_extract
        rw [if_pos (by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr hLenLe)]
      have hFalse :=
        StrEqReplSupport.native_seq_contains_false_of_source_len_lt_pattern
          ([] : List SmtValue) (native_unpack_seq ss) (by
            simpa using hPatPos)
      rw [hExtractEmpty, hFalse] at hContainsExtract
      contradiction
  have hContainsDrop :
      native_seq_contains
          ((native_unpack_seq st₁).drop (Int.toNat ni))
          (native_unpack_seq ss) = true := by
    rw [← native_seq_extract_len_tail_of_bounds
      (native_unpack_seq st₁) ni hNNonneg hNLeLen]
    exact hContainsExtract
  have hIndexNonneg :
      0 ≤ native_seq_indexof (native_unpack_seq st₁)
        (native_unpack_seq ss) ni :=
    native_seq_indexof_nonneg_of_drop_contains
      (native_unpack_seq st₁) (native_unpack_seq ss) ni
      hNNonneg hPatNe hContainsDrop
  have hIndexEq :
      native_seq_indexof
          (native_unpack_seq st₁ ++ native_unpack_seq st₂)
          (native_unpack_seq ss) ni =
        native_seq_indexof (native_unpack_seq st₁)
          (native_unpack_seq ss) ni :=
    native_seq_indexof_append_of_nonneg
      (native_unpack_seq st₁) (native_unpack_seq ss)
      (native_unpack_seq st₂) ni hIndexNonneg
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt left) =
        __smtx_model_eval M (__eo_to_smt right) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof
          (SmtTerm.str_concat (__eo_to_smt t₁) (__eo_to_smt t₂))
          (__eo_to_smt s) (__eo_to_smt n)) =
      __smtx_model_eval M
        (SmtTerm.str_indexof (__eo_to_smt t₁) (__eo_to_smt s)
          (__eo_to_smt n))
    rw [smtx_eval_str_indexof_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hT₁Eval, hT₂Eval, hSEval, hNEval,
      smtx_eval_str_indexof_term_eq, hT₁Eval, hSEval, hNEval]
    simpa [__smtx_model_eval_str_concat, native_seq_concat,
      __smtx_model_eval_str_indexof, Smtm.native_unpack_pack_seq]
      using congrArg SmtValue.Numeral hIndexEq
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M left right hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt right))

public theorem cmd_step_str_indexof_contains_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_contains_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_contains_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_contains_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_indexof_contains_pre args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons t₁ args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons t₂ args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons needle args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons n args =>
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
                              | cons _ _ => exact absurd rfl hProg
                              | nil =>
                                  let P₁ := __eo_state_proven_nth s i₁
                                  let P₂ := __eo_state_proven_nth s i₂
                                  have hT₁Trans :
                                      RuleProofs.eo_has_smt_translation t₁ := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.1
                                  have hT₂Trans :
                                      RuleProofs.eo_has_smt_translation t₂ := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.2.1
                                  have hNeedleTrans :
                                      RuleProofs.eo_has_smt_translation needle := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.2.1
                                  have hNTrans :
                                      RuleProofs.eo_has_smt_translation n := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.2.2.1
                                  change __eo_typeof
                                      (__eo_prog_str_indexof_contains_pre
                                        t₁ t₂ needle n (Proof.pf P₁)
                                        (Proof.pf P₂)) = Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_indexof_contains_pre
                                          t₁ t₂ needle n (Proof.pf P₁)
                                          (Proof.pf P₂) ≠ Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_indexof_contains_pre_info
                                      t₁ t₂ needle n P₁ P₂ hRuleProg with
                                    ⟨sLen, tSub, nSub, tLen, sSub,
                                      hP₁, hP₂, hsLen, htSub, hnSub,
                                      htLen, hsSub, hProgEq⟩
                                  subst sLen
                                  subst tSub
                                  subst nSub
                                  subst tLen
                                  subst sSub
                                  rw [hProgEq] at hResultTy
                                  have hOps :=
                                    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof
                                        (indexofContainsPreLeft
                                          t₁ t₂ needle n))
                                      (__eo_typeof
                                        (indexofContainsPreRight
                                          t₁ needle n)) hResultTy
                                  have hLeftNN := hOps.1
                                  have hRightNN := hOps.2
                                  change __eo_typeof_str_indexof
                                      (__eo_typeof
                                        (Term.Apply
                                          (Term.Apply Term.str_concat t₁) t₂))
                                      (__eo_typeof needle) (__eo_typeof n) ≠
                                    Term.Stuck at hLeftNN
                                  rcases eo_typeof_str_indexof_args_of_ne_stuck
                                      (__eo_typeof
                                        (Term.Apply
                                          (Term.Apply Term.str_concat t₁) t₂))
                                      (__eo_typeof needle) (__eo_typeof n)
                                      hLeftNN with
                                    ⟨T, hConcatTy, hNeedleTy, hNTy⟩
                                  change __eo_typeof_str_indexof
                                      (__eo_typeof t₁) (__eo_typeof needle)
                                      (__eo_typeof n) ≠ Term.Stuck at hRightNN
                                  rcases eo_typeof_str_indexof_args_of_ne_stuck
                                      (__eo_typeof t₁) (__eo_typeof needle)
                                      (__eo_typeof n) hRightNN with
                                    ⟨U, hT₁TyU, hNeedleTyU, _hNTyU⟩
                                  have hUT : U = T := by
                                    rw [hNeedleTy] at hNeedleTyU
                                    exact ((Term.Apply.inj hNeedleTyU).2).symm
                                  subst U
                                  have hConcatArgs :=
                                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                      t₁ t₂ T hConcatTy
                                  have hT₁Ty :
                                      __eo_typeof t₁ = Term.Apply Term.Seq T := by
                                    exact hConcatArgs.1
                                  have hT₂Ty :
                                      __eo_typeof t₂ = Term.Apply Term.Seq T :=
                                    hConcatArgs.2
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem₁Raw : eo_interprets M P₁ true :=
                                      hTrue P₁ (by simp [P₁, premiseTermList])
                                    have hPrem₂Raw : eo_interprets M P₂ true :=
                                      hTrue P₂ (by simp [P₂, premiseTermList])
                                    have hPrem₁ : eo_interprets M
                                        (indexofContainsPreLenPremise needle)
                                        true := by
                                      simpa [hP₁] using hPrem₁Raw
                                    have hPrem₂ : eo_interprets M
                                        (indexofContainsPreContainsPremise
                                          t₁ needle n) true := by
                                      simpa [hP₂] using hPrem₂Raw
                                    exact
                                      facts___eo_prog_str_indexof_contains_pre_impl
                                        M hM t₁ t₂ needle n P₁ P₂ T
                                        hT₁Trans hT₂Trans hNeedleTrans hNTrans
                                        hT₁Ty hT₂Ty hNeedleTy hNTy hPrem₁
                                        hPrem₂ hProgEq
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (typed___eo_prog_str_indexof_contains_pre_impl
                                          t₁ t₂ needle n P₁ P₂ T
                                          hT₁Trans hT₂Trans hNeedleTrans
                                          hNTrans hT₁Ty hT₂Ty hNeedleTy hNTy
                                          hProgEq)
