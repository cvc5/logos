module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev indexofNoContainsPremiseRaw
    (tSub s n tLen : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.str_contains
          (Term.Apply
            (Term.Apply (Term.Apply Term.str_substr tSub) n)
            (Term.Apply Term.str_len tLen)))
        s))
    (Term.Boolean false)

private abbrev indexofNoContainsPremise (t s n : Term) : Term :=
  indexofNoContainsPremiseRaw t s n t

private abbrev indexofNoContainsLhs (t s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) s) n

private abbrev indexofNoContainsConclusion (t s n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (indexofNoContainsLhs t s n))
    (Term.Numeral (-1 : native_Int))

private theorem eo_and_eq_true_parts
    (A B : Term)
    (h : __eo_and A B = Term.Boolean true) :
    A = Term.Boolean true ∧ B = Term.Boolean true := by
  cases A <;> cases B <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean =>
    exact h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;>
      simp [__eo_requires, hw, native_teq, native_ite,
        SmtEval.native_not] at h

private theorem eqs4_of_requires_nested_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term)
    (h :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4))
        (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  have hProg := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg
  have hTop := eo_and_eq_true_parts _ _ hProg.1
  have hMid := eo_and_eq_true_parts _ _ hTop.1
  have hBot := eo_and_eq_true_parts _ _ hMid.1
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 hBot.1,
    RuleProofs.eq_of_eo_eq_true x2 y2 hBot.2,
    RuleProofs.eq_of_eo_eq_true x3 y3 hMid.2,
    RuleProofs.eq_of_eo_eq_true x4 y4 hTop.2⟩

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

private theorem smtx_typeof_of_eo_seq
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

private theorem smtx_eval_str_len_indexof_no_contains_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_len x) =
      __smtx_model_eval_str_len (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_substr_indexof_no_contains_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_contains_indexof_no_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_prefix_eq_append
    (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

private theorem native_seq_indexof_rec_append_ne_neg
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
            simp only [List.length_cons] at hFuel
            omega
          unfold native_seq_indexof_rec
          by_cases hPre :
              native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [if_pos hPre]
            simp
          · rw [if_neg hPre]
            have hxs : (b :: bs) ++ pat ++ after =
                b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

private theorem native_seq_contains_of_decomp
    (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  have hLen : pat.length ≤ (before ++ pat ++ after).length := by
    simp [List.length_append]
    omega
  have hNe :
      native_seq_indexof (before ++ pat ++ after) pat 0 ≠ -1 := by
    rw [native_seq_indexof_eq_rec]
    simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
    rw [dif_pos hLen]
    have hFuel :
        before.length <
          (before ++ pat ++ after).length - pat.length + 1 := by
      simp [List.length_append]
      omega
    simpa using
      native_seq_indexof_rec_append_ne_neg pat after before 0
        ((before ++ pat ++ after).length - pat.length + 1) hFuel
  have hGe :
      0 ≤ native_seq_indexof (before ++ pat ++ after) pat 0 := by
    rcases native_seq_indexof_eq_neg_one_or_ge
        (before ++ pat ++ after) pat 0 with h | h
    · exact absurd h hNe
    · exact h
  unfold native_seq_contains
  exact decide_eq_true hGe

private theorem native_seq_contains_of_indexof_rec_ne_neg
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

private theorem native_seq_indexof_oob
    (xs pat : List SmtValue) (i : native_Int)
    (hLenLt : native_seq_len xs < i) :
    native_seq_indexof xs pat i = -1 := by
  unfold native_seq_indexof
  have hNotNeg : ¬ i < 0 := by
    intro hi
    have hLenNonneg : (0 : Int) ≤ native_seq_len xs := by
      simp [native_seq_len]
    exact (Int.not_lt_of_ge hLenNonneg) (Int.lt_trans hLenLt hi)
  have hiNonneg : 0 ≤ i := int_nonneg_of_not_neg hNotNeg
  have hLenLtInt : (xs.length : Int) < i := by
    simpa [native_seq_len] using hLenLt
  have hStartGtInt : (xs.length : Int) < (Int.toNat i : Int) := by
    simpa [Int.toNat_of_nonneg hiNonneg] using hLenLtInt
  have hStartGtNat : xs.length < Int.toNat i :=
    Int.ofNat_lt.mp hStartGtInt
  have hBoundsFalse : ¬ Int.toNat i + pat.length ≤ xs.length := by
    omega
  simp [hNotNeg, hBoundsFalse]

private theorem native_seq_indexof_eq_neg_one_of_drop_contains_false
    (xs pat : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ i)
    (hContains :
      native_seq_contains (xs.drop (Int.toNat i)) pat = false) :
    native_seq_indexof xs pat i = -1 := by
  unfold native_seq_indexof
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
  simp [hNotNeg]
  by_cases hBounds : Int.toNat i + pat.length ≤ xs.length
  · simp [hBounds]
    by_cases hRec :
        native_seq_indexof_rec (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) =
        -1
    · exact hRec
    · have hContainsTrue :=
        native_seq_contains_of_indexof_rec_ne_neg
          (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) hRec
      rw [hContains] at hContainsTrue
      contradiction
  · simp [hBounds]

private theorem prog_str_indexof_no_contains_info
    (t s n P : Term)
    (hProg : __eo_prog_str_indexof_no_contains t s n (Proof.pf P) ≠
      Term.Stuck) :
    ∃ tSub n0 tLen s0,
      P = indexofNoContainsPremiseRaw tSub s0 n0 tLen ∧
      tSub = t ∧
      n0 = n ∧
      tLen = t ∧
      s0 = s ∧
      __eo_prog_str_indexof_no_contains t s n (Proof.pf P) =
        indexofNoContainsConclusion t s n := by
  unfold __eo_prog_str_indexof_no_contains at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases eqs4_of_requires_nested_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ hProg with
      ⟨htSub, hn0, htLen, hs0⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_no_contains, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, indexofNoContainsConclusion,
      indexofNoContainsLhs]

private theorem typed___eo_prog_str_indexof_no_contains_impl
    (t s n P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int)
    (hProgEq :
      __eo_prog_str_indexof_no_contains t s n (Proof.pf P) =
        indexofNoContainsConclusion t s n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_indexof_no_contains t s n (Proof.pf P)) := by
  rcases hTy with ⟨T, hTTy, hSTy, hNTy⟩
  let lhs := indexofNoContainsLhs t s n
  let rhs := Term.Numeral (-1 : native_Int)
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt n)) =
      SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hTSmtTy, hSSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int
    rw [__smtx_typeof.eq_def]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [indexofNoContainsConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_indexof_no_contains_impl
    (M : SmtModel) (hM : model_wf M) (t s n P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int)
    (hPrem : eo_interprets M (indexofNoContainsPremise t s n) true)
    (hProgEq :
      __eo_prog_str_indexof_no_contains t s n (Proof.pf P) =
        indexofNoContainsConclusion t s n) :
    eo_interprets M
      (__eo_prog_str_indexof_no_contains t s n (Proof.pf P)) true := by
  rcases hTy with ⟨T, hTTy, hSTy, hNTy⟩
  let lhs := indexofNoContainsLhs t s n
  let rhs := Term.Numeral (-1 : native_Int)
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, indexofNoContainsConclusion, lhs, rhs] using
      typed___eo_prog_str_indexof_no_contains_impl t s n P
        hTTrans hSTrans hNTrans ⟨T, hTTy, hSTy, hNTy⟩ hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
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
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hContainsFalse :
      native_seq_contains
          (native_seq_extract (native_unpack_seq ts) ni
            (native_seq_len (native_unpack_seq ts)))
          (native_unpack_seq ss) =
        false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains
                (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
                  (SmtTerm.str_len (__eo_to_smt t)))
                (__eo_to_smt s))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          smtx_eval_str_contains_indexof_no_contains_term_eq,
          smtx_eval_str_substr_indexof_no_contains_term_eq,
          hTEval, hNEval, smtx_eval_str_len_indexof_no_contains_term_eq,
          hTEval, hSEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_substr,
          __smtx_model_eval_str_len, __smtx_model_eval_str_contains,
          __smtx_model_eval_eq, native_veq, Smtm.native_unpack_pack_seq]
          using hEval
  have hIndexof :
      native_seq_indexof (native_unpack_seq ts) (native_unpack_seq ss) ni =
        -1 := by
    by_cases hNeg : ni < 0
    · unfold native_seq_indexof
      simp [hNeg]
    · have hNonneg : 0 ≤ ni := int_nonneg_of_not_neg hNeg
      by_cases hAfter : native_seq_len (native_unpack_seq ts) < ni
      · exact native_seq_indexof_oob (native_unpack_seq ts) (native_unpack_seq ss)
          ni hAfter
      · have hLeLen : ni ≤ native_seq_len (native_unpack_seq ts) := by
          exact Int.le_of_not_gt hAfter
        have hExtractTail :
            native_seq_extract (native_unpack_seq ts) ni
                (native_seq_len (native_unpack_seq ts)) =
              (native_unpack_seq ts).drop (Int.toNat ni) :=
          native_seq_extract_len_tail_of_bounds (native_unpack_seq ts) ni
            hNonneg hLeLen
        have hDropContainsFalse :
            native_seq_contains
                ((native_unpack_seq ts).drop (Int.toNat ni))
                (native_unpack_seq ss) =
              false := by
          simpa [hExtractTail] using hContainsFalse
        exact native_seq_indexof_eq_neg_one_of_drop_contains_false
          (native_unpack_seq ts) (native_unpack_seq ss) ni hNonneg
          hDropContainsFalse
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt n)) =
      __smtx_model_eval M (SmtTerm.Numeral (-1 : native_Int))
    rw [smtx_eval_str_indexof_term_eq, hTEval, hSEval, hNEval,
      smtx_eval_numeral_term_eq]
    simp [__smtx_model_eval_str_indexof, hIndexof]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_indexof_no_contains_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_no_contains args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_no_contains args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_no_contains args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_no_contains args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons pIdx premises =>
                      cases premises with
                      | nil =>
                          let P := __eo_state_proven_nth s pIdx
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.2.2.1
                          change __eo_typeof
                              (__eo_prog_str_indexof_no_contains a1 a2 a3
                                (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_indexof_no_contains a1 a2 a3
                                  (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_indexof_no_contains_info
                              a1 a2 a3 P hProgRule with
                            ⟨tSub, n0, tLen, s0, hPremShape, htSub, hn0,
                              htLen, hs0, hProgEq⟩
                          subst tSub
                          subst n0
                          subst tLen
                          subst s0
                          let lhs := indexofNoContainsLhs a1 a2 a3
                          let rhs := Term.Numeral (-1 : native_Int)
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Int := by
                            change __eo_typeof_str_indexof (__eo_typeof a1)
                                (__eo_typeof a2) (__eo_typeof a3) ≠
                              Term.Stuck at hLhsNotStuck
                            exact eo_typeof_str_indexof_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a3) hLhsNotStuck
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (indexofNoContainsPremise a1 a2 a3) true := by
                              simpa [hPremShape, indexofNoContainsPremise] using
                                hPremRaw
                            exact facts___eo_prog_str_indexof_no_contains_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hArgTypes hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_indexof_no_contains_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hArgTypes hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
