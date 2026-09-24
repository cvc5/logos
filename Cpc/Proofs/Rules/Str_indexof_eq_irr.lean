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

private abbrev indexofEqIrrPremiseLeft (n t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.leq n) (Term.Apply Term.str_len t)))
    (Term.Boolean true)

private abbrev indexofEqIrrPremiseRight (n r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.leq n) (Term.Apply Term.str_len r)))
    (Term.Boolean true)

private abbrev indexofEqIrrPremiseSubstrRaw
    (t nT tLen r nR rLen : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) nT)
        (Term.Apply Term.str_len tLen)))
    (Term.Apply (Term.Apply (Term.Apply Term.str_substr r) nR)
      (Term.Apply Term.str_len rLen))

private abbrev indexofEqIrrPremiseSubstr (t r n : Term) : Term :=
  indexofEqIrrPremiseSubstrRaw t n t r n r

private abbrev indexofEqIrrLeft (t s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) s) n

private abbrev indexofEqIrrRight (r s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof r) s) n

private abbrev indexofEqIrrInner (t s r n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (indexofEqIrrLeft t s n))
    (indexofEqIrrRight r s n)

private abbrev indexofEqIrrConclusion (t s r n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (indexofEqIrrInner t s r n))
    (Term.Boolean true)

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

private theorem eqs10_of_requires_nested_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 x8 y8
      x9 y9 x10 y10 B : Term)
    (h :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and
                      (__eo_and
                        (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
                        (__eo_eq x3 y3))
                      (__eo_eq x4 y4))
                    (__eo_eq x5 y5))
                  (__eo_eq x6 y6))
                (__eo_eq x7 y7))
              (__eo_eq x8 y8))
            (__eo_eq x9 y9))
          (__eo_eq x10 y10))
        (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 ∧ y5 = x5 ∧
      y6 = x6 ∧ y7 = x7 ∧ y8 = x8 ∧ y9 = x9 ∧ y10 = x10 := by
  have hProg := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg
  have h10 := eo_and_eq_true_parts _ _ hProg.1
  have h9 := eo_and_eq_true_parts _ _ h10.1
  have h8 := eo_and_eq_true_parts _ _ h9.1
  have h7 := eo_and_eq_true_parts _ _ h8.1
  have h6 := eo_and_eq_true_parts _ _ h7.1
  have h5 := eo_and_eq_true_parts _ _ h6.1
  have h4 := eo_and_eq_true_parts _ _ h5.1
  have h3 := eo_and_eq_true_parts _ _ h4.1
  have h2 := eo_and_eq_true_parts _ _ h3.1
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h2.1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2.2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3.2,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4.2,
    RuleProofs.eq_of_eo_eq_true x5 y5 h5.2,
    RuleProofs.eq_of_eo_eq_true x6 y6 h6.2,
    RuleProofs.eq_of_eo_eq_true x7 y7 h7.2,
    RuleProofs.eq_of_eo_eq_true x8 y8 h8.2,
    RuleProofs.eq_of_eo_eq_true x9 y9 h9.2,
    RuleProofs.eq_of_eo_eq_true x10 y10 h10.2⟩

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

private theorem smtx_eval_str_len_eq_irr_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_len x) =
      __smtx_model_eval_str_len (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_substr_eq_irr_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_indexof_eq_of_drop_eq
    (xs ys pat : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ i)
    (hXLe : i ≤ native_seq_len xs)
    (hYLe : i ≤ native_seq_len ys)
    (hDrop : xs.drop (Int.toNat i) = ys.drop (Int.toNat i)) :
    native_seq_indexof xs pat i = native_seq_indexof ys pat i := by
  unfold native_seq_indexof
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
  have hToNat : (Int.toNat i : Int) = i :=
    Int.toNat_of_nonneg hNonneg
  have hXStartLeInt : (Int.toNat i : Int) ≤ (xs.length : Int) := by
    simpa [hToNat, native_seq_len] using hXLe
  have hYStartLeInt : (Int.toNat i : Int) ≤ (ys.length : Int) := by
    simpa [hToNat, native_seq_len] using hYLe
  have hXStartLeNat : Int.toNat i ≤ xs.length :=
    Int.ofNat_le.mp hXStartLeInt
  have hYStartLeNat : Int.toNat i ≤ ys.length :=
    Int.ofNat_le.mp hYStartLeInt
  have hLenEq : xs.length = ys.length := by
    have hDropLen := congrArg List.length hDrop
    rw [List.length_drop, List.length_drop] at hDropLen
    omega
  simp [hNotNeg, hDrop, hLenEq]

private theorem prog_str_indexof_eq_irr_info
    (t s r n P1 P2 P3 : Term)
    (hProg :
      __eo_prog_str_indexof_eq_irr t s r n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠
        Term.Stuck) :
    ∃ nT tLen nR rLen tSub nSubT tSubLen rSub nSubR rSubLen,
      P1 = indexofEqIrrPremiseLeft nT tLen ∧
      P2 = indexofEqIrrPremiseRight nR rLen ∧
      P3 = indexofEqIrrPremiseSubstrRaw
        tSub nSubT tSubLen rSub nSubR rSubLen ∧
      nT = n ∧
      tLen = t ∧
      nR = n ∧
      rLen = r ∧
      tSub = t ∧
      nSubT = n ∧
      tSubLen = t ∧
      rSub = r ∧
      nSubR = n ∧
      rSubLen = r ∧
      __eo_prog_str_indexof_eq_irr t s r n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        indexofEqIrrConclusion t s r n := by
  unfold __eo_prog_str_indexof_eq_irr at hProg
  split at hProg <;> try contradiction
  next hP1 hP2 hP3 =>
    cases hP1
    cases hP2
    cases hP3
    rcases eqs10_of_requires_nested_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hProg with
      ⟨hnT, htLen, hnR, hrLen, htSub, hnSubT, htSubLen,
        hrSub, hnSubR, hrSubLen⟩
    subst_vars
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_eq_irr, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, indexofEqIrrConclusion, indexofEqIrrInner,
      indexofEqIrrLeft, indexofEqIrrRight]

private theorem typed___eo_prog_str_indexof_eq_irr_impl
    (t s r n P1 P2 P3 : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : (∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
        __eo_typeof s = Term.Apply Term.Seq T ∧
        __eo_typeof n = Term.Int) ∧
      (∃ U, __eo_typeof r = Term.Apply Term.Seq U ∧
        __eo_typeof s = Term.Apply Term.Seq U ∧
        __eo_typeof n = Term.Int))
    (hProgEq :
      __eo_prog_str_indexof_eq_irr t s r n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        indexofEqIrrConclusion t s r n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_indexof_eq_irr t s r n
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) := by
  rcases hTy with ⟨⟨T, hTTy, hSTy, hNTy⟩,
    ⟨U, hRTy, hSUty, _hNUty⟩⟩
  let left := indexofEqIrrLeft t s n
  let right := indexofEqIrrRight r s n
  let inner := indexofEqIrrInner t s r n
  let rhs := Term.Boolean true
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r U hRTrans hRTy
  have hSSmtUTy := smtx_typeof_of_eo_seq s U hSTrans hSUty
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hLeftTy : __smtx_typeof (__eo_to_smt left) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt n)) =
      SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hTSmtTy, hSSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hRightTy : __smtx_typeof (__eo_to_smt right) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt r) (__eo_to_smt s)
          (__eo_to_smt n)) =
      SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hRSmtTy, hSSmtUTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hInnerTy : __smtx_typeof (__eo_to_smt inner) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.eq (__eo_to_smt left) (__eo_to_smt right)) =
      SmtType.Bool
    rw [typeof_eq_eq]
    simp [hLeftTy, hRightTy, __smtx_typeof_eq, __smtx_typeof_guard,
      native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq inner) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type inner rhs
      (by rw [hInnerTy, hRhsTy]) (by rw [hInnerTy]; simp)
  rw [hProgEq]
  simpa [indexofEqIrrConclusion, inner, rhs] using hBoolEq

private theorem facts___eo_prog_str_indexof_eq_irr_impl
    (M : SmtModel) (hM : model_wf M)
    (t s r n P1 P2 P3 : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : (∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
        __eo_typeof s = Term.Apply Term.Seq T ∧
        __eo_typeof n = Term.Int) ∧
      (∃ U, __eo_typeof r = Term.Apply Term.Seq U ∧
        __eo_typeof s = Term.Apply Term.Seq U ∧
        __eo_typeof n = Term.Int))
    (hPremLeft : eo_interprets M (indexofEqIrrPremiseLeft n t) true)
    (hPremRight : eo_interprets M (indexofEqIrrPremiseRight n r) true)
    (hPremSubstr : eo_interprets M (indexofEqIrrPremiseSubstr t r n) true)
    (hProgEq :
      __eo_prog_str_indexof_eq_irr t s r n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        indexofEqIrrConclusion t s r n) :
    eo_interprets M
      (__eo_prog_str_indexof_eq_irr t s r n
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) true := by
  rcases hTy with ⟨⟨T, hTTy, hSTy, hNTy⟩,
    ⟨U, hRTy, hSUty, _hNUty⟩⟩
  let left := indexofEqIrrLeft t s n
  let right := indexofEqIrrRight r s n
  let inner := indexofEqIrrInner t s r n
  let rhs := Term.Boolean true
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq inner) rhs) := by
    simpa [hProgEq, indexofEqIrrConclusion, inner, rhs] using
      typed___eo_prog_str_indexof_eq_irr_impl t s r n P1 P2 P3
        hTTrans hSTrans hRTrans hNTrans
        ⟨⟨T, hTTy, hSTy, hNTy⟩, ⟨U, hRTy, hSUty, hNTy⟩⟩ hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r U hRTrans hRTy
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
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type U) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
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
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hNLeT :
      ni ≤ native_seq_len (native_unpack_seq ts) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremLeft
    cases hPremLeft with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.leq (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt t)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_leq_term_eq,
          hNEval, smtx_eval_str_len_eq_irr_term_eq, hTEval,
          smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_leq, __smtx_model_eval_str_len,
          __smtx_model_eval_eq, native_veq, native_zleq] using hEval
  have hNLeR :
      ni ≤ native_seq_len (native_unpack_seq rs) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremRight
    cases hPremRight with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.leq (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt r)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_leq_term_eq,
          hNEval, smtx_eval_str_len_eq_irr_term_eq, hREval,
          smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_leq, __smtx_model_eval_str_len,
          __smtx_model_eval_eq, native_veq, native_zleq] using hEval
  have hExtractEq :
      native_seq_extract (native_unpack_seq ts) ni
          (native_seq_len (native_unpack_seq ts)) =
        native_seq_extract (native_unpack_seq rs) ni
          (native_seq_len (native_unpack_seq rs)) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremSubstr
    cases hPremSubstr with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt t)))
              (SmtTerm.str_substr (__eo_to_smt r) (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt r)))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          smtx_eval_str_substr_eq_irr_term_eq,
          hTEval, hNEval, smtx_eval_str_len_eq_irr_term_eq, hTEval,
          smtx_eval_str_substr_eq_irr_term_eq,
          hREval, hNEval, smtx_eval_str_len_eq_irr_term_eq, hREval] at hEval
        have hBool :
            decide
              (SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value ts)
                    (native_seq_extract (native_unpack_seq ts) ni
                      (native_seq_len (native_unpack_seq ts)))) =
                SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value rs)
                    (native_seq_extract (native_unpack_seq rs) ni
                      (native_seq_len (native_unpack_seq rs))))) = true := by
          simpa [__smtx_model_eval_str_substr, __smtx_model_eval_str_len,
            __smtx_model_eval_eq, native_veq] using hEval
        have hSeqValueEq :
            SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value ts)
                  (native_seq_extract (native_unpack_seq ts) ni
                    (native_seq_len (native_unpack_seq ts)))) =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value rs)
                  (native_seq_extract (native_unpack_seq rs) ni
                    (native_seq_len (native_unpack_seq rs)))) :=
          of_decide_eq_true hBool
        let unpackValue : SmtValue -> List SmtValue
          | SmtValue.Seq s => native_unpack_seq s
          | _ => []
        have hUnpack := congrArg unpackValue hSeqValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hIndexofEq :
      native_seq_indexof (native_unpack_seq ts) (native_unpack_seq ss) ni =
        native_seq_indexof (native_unpack_seq rs) (native_unpack_seq ss) ni := by
    by_cases hNeg : ni < 0
    · unfold native_seq_indexof
      simp [hNeg]
    · have hNonneg : 0 ≤ ni := int_nonneg_of_not_neg hNeg
      have hDropT :
          native_seq_extract (native_unpack_seq ts) ni
              (native_seq_len (native_unpack_seq ts)) =
            (native_unpack_seq ts).drop (Int.toNat ni) :=
        native_seq_extract_len_tail_of_bounds (native_unpack_seq ts) ni
          hNonneg hNLeT
      have hDropR :
          native_seq_extract (native_unpack_seq rs) ni
              (native_seq_len (native_unpack_seq rs)) =
            (native_unpack_seq rs).drop (Int.toNat ni) :=
        native_seq_extract_len_tail_of_bounds (native_unpack_seq rs) ni
          hNonneg hNLeR
      have hDropEq :
          (native_unpack_seq ts).drop (Int.toNat ni) =
            (native_unpack_seq rs).drop (Int.toNat ni) := by
        simpa [hDropT, hDropR] using hExtractEq
      exact native_seq_indexof_eq_of_drop_eq
        (native_unpack_seq ts) (native_unpack_seq rs) (native_unpack_seq ss)
        ni hNonneg hNLeT hNLeR hDropEq
  have hInnerEvalTrue :
      __smtx_model_eval M (__eo_to_smt inner) = SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt n))
          (SmtTerm.str_indexof (__eo_to_smt r) (__eo_to_smt s)
            (__eo_to_smt n))) =
      SmtValue.Boolean true
    rw [smtx_eval_eq_term_eq,
      smtx_eval_str_indexof_term_eq, hTEval, hSEval, hNEval,
      smtx_eval_str_indexof_term_eq, hREval, hSEval, hNEval]
    simp [__smtx_model_eval_str_indexof, hIndexofEq,
      __smtx_model_eval_eq, native_veq]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt inner) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    rw [hInnerEvalTrue]
    change SmtValue.Boolean true = __smtx_model_eval M (SmtTerm.Boolean true)
    rw [smtx_eval_boolean_term_eq]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M inner rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_indexof_eq_irr_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_eq_irr args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_eq_irr args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_eq_irr args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_eq_irr args premises ≠
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons i1 premises =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons i2 premises =>
                              cases premises with
                              | nil =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | cons i3 premises =>
                                  cases premises with
                                  | nil =>
                                      let P1 := __eo_state_proven_nth s i1
                                      let P2 := __eo_state_proven_nth s i2
                                      let P3 := __eo_state_proven_nth s i3
                                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                                          hCmdTrans.1
                                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                                          hCmdTrans.2.1
                                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                                          hCmdTrans.2.2.1
                                      have hA4Trans : RuleProofs.eo_has_smt_translation a4 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                                          hCmdTrans.2.2.2.1
                                      change __eo_typeof
                                          (__eo_prog_str_indexof_eq_irr a1 a2 a3 a4
                                            (Proof.pf P1) (Proof.pf P2)
                                            (Proof.pf P3)) =
                                        Term.Bool at hResultTy
                                      have hProgRule :
                                          __eo_prog_str_indexof_eq_irr a1 a2 a3 a4
                                              (Proof.pf P1) (Proof.pf P2)
                                              (Proof.pf P3) ≠
                                            Term.Stuck :=
                                        term_ne_stuck_of_typeof_bool hResultTy
                                      rcases prog_str_indexof_eq_irr_info
                                          a1 a2 a3 a4 P1 P2 P3 hProgRule with
                                        ⟨nT, tLen, nR, rLen, tSub, nSubT,
                                          tSubLen, rSub, nSubR, rSubLen,
                                          hP1Shape, hP2Shape, hP3Shape,
                                          hnT, htLen, hnR, hrLen, htSub,
                                          hnSubT, htSubLen, hrSub, hnSubR,
                                          hrSubLen, hProgEq⟩
                                      subst nT
                                      subst tLen
                                      subst nR
                                      subst rLen
                                      subst tSub
                                      subst nSubT
                                      subst tSubLen
                                      subst rSub
                                      subst nSubR
                                      subst rSubLen
                                      let left := indexofEqIrrLeft a1 a2 a4
                                      let right := indexofEqIrrRight a3 a2 a4
                                      let inner := indexofEqIrrInner a1 a2 a3 a4
                                      let rhs := Term.Boolean true
                                      rw [hProgEq] at hResultTy
                                      change __eo_typeof_eq (__eo_typeof inner)
                                          (__eo_typeof rhs) =
                                        Term.Bool at hResultTy
                                      have hInnerType :
                                          __eo_typeof inner = Term.Bool := by
                                        have hEq :=
                                          RuleProofs.eo_typeof_eq_bool_operands_eq
                                            (__eo_typeof inner) (__eo_typeof rhs)
                                            hResultTy
                                        simpa [rhs] using hEq
                                      change __eo_typeof_eq (__eo_typeof left)
                                          (__eo_typeof right) =
                                        Term.Bool at hInnerType
                                      have hLeftNotStuck :
                                          __eo_typeof left ≠ Term.Stuck :=
                                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                          (__eo_typeof left) (__eo_typeof right)
                                          hInnerType).1
                                      have hRightNotStuck :
                                          __eo_typeof right ≠ Term.Stuck :=
                                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                          (__eo_typeof left) (__eo_typeof right)
                                          hInnerType).2
                                      have hLeftTypes :
                                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                            __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                            __eo_typeof a4 = Term.Int := by
                                        change __eo_typeof_str_indexof (__eo_typeof a1)
                                            (__eo_typeof a2) (__eo_typeof a4) ≠
                                          Term.Stuck at hLeftNotStuck
                                        exact eo_typeof_str_indexof_args_of_ne_stuck
                                          (__eo_typeof a1) (__eo_typeof a2)
                                          (__eo_typeof a4) hLeftNotStuck
                                      have hRightTypes :
                                          ∃ U, __eo_typeof a3 = Term.Apply Term.Seq U ∧
                                            __eo_typeof a2 = Term.Apply Term.Seq U ∧
                                            __eo_typeof a4 = Term.Int := by
                                        change __eo_typeof_str_indexof (__eo_typeof a3)
                                            (__eo_typeof a2) (__eo_typeof a4) ≠
                                          Term.Stuck at hRightNotStuck
                                        exact eo_typeof_str_indexof_args_of_ne_stuck
                                          (__eo_typeof a3) (__eo_typeof a2)
                                          (__eo_typeof a4) hRightNotStuck
                                      have hArgTypes := And.intro hLeftTypes hRightTypes
                                      refine ⟨?_, ?_⟩
                                      · intro hTrue
                                        have hPrem1Raw : eo_interprets M P1 true :=
                                          hTrue P1 (by simp [P1, premiseTermList])
                                        have hPrem2Raw : eo_interprets M P2 true :=
                                          hTrue P2 (by simp [P2, premiseTermList])
                                        have hPrem3Raw : eo_interprets M P3 true :=
                                          hTrue P3 (by simp [P3, premiseTermList])
                                        have hPrem1 :
                                            eo_interprets M
                                              (indexofEqIrrPremiseLeft a4 a1) true := by
                                          simpa [hP1Shape] using hPrem1Raw
                                        have hPrem2 :
                                            eo_interprets M
                                              (indexofEqIrrPremiseRight a4 a3) true := by
                                          simpa [hP2Shape] using hPrem2Raw
                                        have hPrem3 :
                                            eo_interprets M
                                              (indexofEqIrrPremiseSubstr a1 a3 a4)
                                              true := by
                                          simpa [hP3Shape, indexofEqIrrPremiseSubstr]
                                            using hPrem3Raw
                                        exact facts___eo_prog_str_indexof_eq_irr_impl
                                          M hM a1 a2 a3 a4 P1 P2 P3
                                          hA1Trans hA2Trans hA3Trans hA4Trans
                                          hArgTypes hPrem1 hPrem2 hPrem3 hProgEq
                                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                          (typed___eo_prog_str_indexof_eq_irr_impl
                                            a1 a2 a3 a4 P1 P2 P3
                                            hA1Trans hA2Trans hA3Trans hA4Trans
                                            hArgTypes hProgEq)
                                  | cons _ _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
