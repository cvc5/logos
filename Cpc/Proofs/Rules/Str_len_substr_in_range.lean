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

private abbrev substrRangeStartPremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev substrRangeLenPremise (m : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq m) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev substrRangeInBoundsPremise (s n m : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.geq (Term.Apply Term.str_len s))
        (Term.Apply
          (Term.Apply Term.plus n)
          (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))))
    (Term.Boolean true)

private abbrev substrRangeLhs (s n m : Term) : Term :=
  Term.Apply Term.str_len
    (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m)

private abbrev substrRangeConclusion (s n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrRangeLhs s n m)) m

private theorem eo_typeof_str_substr_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_substr A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Int ∧ C = Term.Int := by
  cases A <;> simp [__eo_typeof_str_substr] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case UOp opb =>
          cases opb <;> simp at h ⊢
          case Int =>
            cases C <;> simp at h ⊢
            case UOp opc =>
              cases opc <;> simp at h ⊢

private theorem eo_typeof_str_len_str_substr_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_len (__eo_typeof_str_substr A B C) ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Int ∧ C = Term.Int := by
  have hSubstr : __eo_typeof_str_substr A B C ≠ Term.Stuck := by
    intro hStuck
    apply h
    rw [hStuck]
    simp [__eo_typeof_str_len]
  exact eo_typeof_str_substr_args_of_ne_stuck A B C hSubstr

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

private theorem smtx_eval_str_substr_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_plus_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_extract_len_le_arg_of_nonneg
    (xs : List SmtValue) (i n : native_Int) :
    0 <= n -> Int.ofNat (native_seq_extract xs i n).length <= n := by
  intro hn
  simp only [native_seq_extract]
  split
  · simp [hn]
  · rename_i h
    have hProp : ¬ ((i < 0 ∨ n <= 0) ∨ Int.ofNat xs.length <= i) := by
      simpa [Bool.or_eq_true, decide_eq_true_eq] using h
    have hiNonneg : 0 <= i := by
      have hiNot : ¬ i < 0 := by
        intro hi
        exact hProp (Or.inl (Or.inl hi))
      exact Int.le_of_not_gt hiNot
    have hTake :
        ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.toNat (min n (Int.ofNat xs.length - i)) :=
      List.length_take_le _ _
    have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by omega
    have hMinNonneg : 0 <= min n (Int.ofNat xs.length - i) :=
      (Int.le_min).2 ⟨hn, hDiffNonneg⟩
    have hCast :
        Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) =
          min n (Int.ofNat xs.length - i) :=
      Int.toNat_of_nonneg hMinNonneg
    have hLenLe :
        Int.ofNat
            ((xs.drop (Int.toNat i)).take
              (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) :=
      Int.ofNat_le.mpr hTake
    have hMinLe : min n (Int.ofNat xs.length - i) <= n :=
      Int.min_le_left _ _
    omega

private theorem native_seq_extract_len_ge_arg_of_in_range
    (xs : List SmtValue) (i n : native_Int) :
    0 <= i -> 0 <= n -> i + n <= Int.ofNat xs.length ->
    n <= Int.ofNat (native_seq_extract xs i n).length := by
  intro hi hn hle
  simp only [native_seq_extract]
  by_cases hnZero : n = 0
  · subst n
    simp
  · have hnPos : 0 < n := by grind
    have hiLt : i < Int.ofNat xs.length := by grind
    have hCondFalse :
        ¬ (decide (i < 0) || decide (n <= 0) ||
              decide (i >= Int.ofNat xs.length)) = true := by
      simp [Bool.or_eq_true, decide_eq_true_eq]
      grind
    split
    · rename_i h
      exact False.elim (hCondFalse h)
    · have hMin : min n (Int.ofNat xs.length - i) = n := by
        apply Int.min_eq_left
        grind
      have hTakeNat :
          Int.toNat (min n (Int.ofNat xs.length - i)) = Int.toNat n := by
        rw [hMin]
      have hiCast : Int.ofNat (Int.toNat i) = i :=
        Int.toNat_of_nonneg hi
      have hnCast : Int.ofNat (Int.toNat n) = n :=
        Int.toNat_of_nonneg hn
      have hDropLen :
          (xs.drop (Int.toNat i)).length = xs.length - Int.toNat i :=
        List.length_drop
      have hNLeDrop : Int.toNat n <= (xs.drop (Int.toNat i)).length := by
        rw [hDropLen]
        have hNat : Int.toNat n + Int.toNat i <= xs.length := by
          rw [← Int.ofNat_le]
          rw [Int.natCast_add]
          change
            Int.ofNat (Int.toNat n) + Int.ofNat (Int.toNat i) <=
              Int.ofNat xs.length
          rw [hnCast, hiCast]
          grind
        omega
      rw [hTakeNat, List.length_take, Nat.min_eq_left hNLeDrop]
      rw [hnCast]
      exact Int.le_refl _

private theorem native_seq_extract_length_eq_of_in_range
    (xs : List SmtValue) (i n : native_Int)
    (hi : 0 <= i) (hn : 0 <= n)
    (hrange : i + n <= Int.ofNat xs.length) :
    Int.ofNat (native_seq_extract xs i n).length = n := by
  apply Int.le_antisymm
  · exact native_seq_extract_len_le_arg_of_nonneg xs i n hn
  · exact native_seq_extract_len_ge_arg_of_in_range xs i n hi hn hrange

private theorem eo_and_eq_true_left {x y : Term}
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

private theorem eo_and_eq_true_right {x y : Term}
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

private theorem eqs_of_requires5_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 B : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (__eo_eq x5 y5))
        (Term.Boolean true) B ≠ Term.Stuck ->
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 ∧ y5 = x5 := by
  intro hProg
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (__eo_eq x5 y5) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h1234 : __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) = Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have h5 : __eo_eq x5 y5 = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have h123 : __eo_and
          (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3) = Term.Boolean true :=
    eo_and_eq_true_left h1234
  have h4 : __eo_eq x4 y4 = Term.Boolean true :=
    eo_and_eq_true_right h1234
  have h12 : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) =
      Term.Boolean true :=
    eo_and_eq_true_left h123
  have h3 : __eo_eq x3 y3 = Term.Boolean true :=
    eo_and_eq_true_right h123
  have h1 : __eo_eq x1 y1 = Term.Boolean true :=
    eo_and_eq_true_left h12
  have h2 : __eo_eq x2 y2 = Term.Boolean true :=
    eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4,
    RuleProofs.eq_of_eo_eq_true x5 y5 h5⟩

private theorem prog_str_len_substr_in_range_info
    (s n m Pn Pm Pr : Term)
    (hProg :
      __eo_prog_str_len_substr_in_range s n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pr) ≠ Term.Stuck) :
    ∃ n0 m0 s0 n1 m1,
      Pn = substrRangeStartPremise n0 ∧
      Pm = substrRangeLenPremise m0 ∧
      Pr = substrRangeInBoundsPremise s0 n1 m1 ∧
      n0 = n ∧ m0 = m ∧ s0 = s ∧ n1 = n ∧ m1 = m ∧
      __eo_prog_str_len_substr_in_range s n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pr) =
        substrRangeConclusion s n m := by
  unfold __eo_prog_str_len_substr_in_range at hProg
  split at hProg <;> try contradiction
  next heqN heqM heqR =>
    cases heqN
    cases heqM
    cases heqR
    rcases eqs_of_requires5_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ _ _ hProg with
      ⟨hn0, hm0, hs0, hn1, hm1⟩
    subst_vars
    refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_len_substr_in_range, __eo_requires, __eo_and,
      __eo_eq, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, substrRangeConclusion, substrRangeLhs]

private theorem typed___eo_prog_str_len_substr_in_range_impl
    (s n m Pn Pm Pr : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧ __eo_typeof m = Term.Int)
    (hProgEq :
      __eo_prog_str_len_substr_in_range s n m
          (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pr) =
        substrRangeConclusion s n m) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_len_substr_in_range s n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pr)) := by
  rcases hTy with ⟨T, hSTy, hNTy, hMTy⟩
  let substr := Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m
  let lhs := Term.Apply Term.str_len substr
  let rhs := m
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hSubstrTy :
      __smtx_typeof (__eo_to_smt substr) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt m)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr,
      __smtx_typeof.eq_def]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_len
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt m))) =
      SmtType.Int
    rw [typeof_str_len_eq]
    rw [show
        __smtx_typeof
            (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
              (__eo_to_smt m)) =
          SmtType.Seq (__eo_to_smt_type T) by
      change __smtx_typeof (__eo_to_smt substr) =
        SmtType.Seq (__eo_to_smt_type T)
      exact hSubstrTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hMSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [substrRangeConclusion, substrRangeLhs, lhs, rhs, substr] using hBoolEq

private theorem facts___eo_prog_str_len_substr_in_range_impl
    (M : SmtModel) (hM : model_wf M) (s n m Pn Pm Pr : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧ __eo_typeof m = Term.Int)
    (hPremN : eo_interprets M (substrRangeStartPremise n) true)
    (hPremM : eo_interprets M (substrRangeLenPremise m) true)
    (hPremRange : eo_interprets M (substrRangeInBoundsPremise s n m) true)
    (hProgEq :
      __eo_prog_str_len_substr_in_range s n m
          (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pr) =
        substrRangeConclusion s n m) :
    eo_interprets M
      (__eo_prog_str_len_substr_in_range s n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pr)) true := by
  rcases hTy with ⟨T, hSTy, hNTy, hMTy⟩
  let substr := Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m
  let lhs := Term.Apply Term.str_len substr
  let rhs := m
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, substrRangeConclusion, substrRangeLhs, lhs, rhs,
      substr] using
      typed___eo_prog_str_len_substr_in_range_impl s n m Pn Pm Pr
        hSTrans hNTrans hMTrans ⟨T, hSTy, hNTy, hMTy⟩ hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
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
  have hMEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
        SmtType.Int := by
    simpa [hMSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m) (by
        unfold term_has_non_none_type
        rw [hMSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hNNonneg : 0 <= ni := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremN
    cases hPremN with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq, hNEval,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0 ni = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_eq, native_veq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hMNonneg : 0 <= mi := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremM
    cases hPremM with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt m) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq, hMEval,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0 mi = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_eq, native_veq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hRange : ni + mi <= Int.ofNat (native_unpack_seq ss).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremRange
    cases hPremRange with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_len (__eo_to_smt s))
                (SmtTerm.plus (__eo_to_smt n)
                  (SmtTerm.plus (__eo_to_smt m) (SmtTerm.Numeral 0))))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, hSEval, smtx_eval_plus_term_eq,
          hNEval, smtx_eval_plus_term_eq, hMEval,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq
              (native_zplus ni (native_zplus mi 0))
              (Int.ofNat (native_unpack_seq ss).length) = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_plus, __smtx_model_eval_str_len,
            __smtx_model_eval_eq, native_veq, native_seq_len] using hEval
        have hLe :
            native_zplus ni (native_zplus mi 0) <=
              Int.ofNat (native_unpack_seq ss).length := by
          simpa [SmtEval.native_zleq] using hLeBool
        simpa [native_zplus, SmtEval.native_zplus] using hLe
  have hExtractLen :
      Int.ofNat
          (native_seq_extract (native_unpack_seq ss) ni mi).length =
        mi :=
    native_seq_extract_length_eq_of_in_range
      (native_unpack_seq ss) ni mi hNNonneg hMNonneg hRange
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_len
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt m))) =
      __smtx_model_eval M (__eo_to_smt m)
    rw [smtx_eval_str_len_term_eq, smtx_eval_str_substr_term_eq, hSEval,
      hNEval, hMEval]
    simpa [__smtx_model_eval_str_substr, __smtx_model_eval_str_len,
      native_seq_len, Smtm.native_unpack_pack_seq] using hExtractLen
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_len_substr_in_range_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_substr_in_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_len_substr_in_range args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_substr_in_range args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_len_substr_in_range args premises ≠
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
                  | cons p1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p2 premises =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons p3 premises =>
                              cases premises with
                              | nil =>
                                  let P1 := __eo_state_proven_nth s p1
                                  let P2 := __eo_state_proven_nth s p2
                                  let P3 := __eo_state_proven_nth s p3
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
                                      (__eo_prog_str_len_substr_in_range a1 a2 a3
                                        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) =
                                    Term.Bool at hResultTy
                                  have hProgRule :
                                      __eo_prog_str_len_substr_in_range a1 a2 a3
                                          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_len_substr_in_range_info
                                      a1 a2 a3 P1 P2 P3 hProgRule with
                                    ⟨n0, m0, s0, n1, m1, hP1Shape, hP2Shape,
                                      hP3Shape, hn0, hm0, hs0, hn1, hm1,
                                      hProgEq⟩
                                  subst n0
                                  subst m0
                                  subst s0
                                  subst n1
                                  subst m1
                                  let lhs := substrRangeLhs a1 a2 a3
                                  rw [hProgEq] at hResultTy
                                  change __eo_typeof_eq (__eo_typeof lhs)
                                      (__eo_typeof a3) =
                                    Term.Bool at hResultTy
                                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof lhs) (__eo_typeof a3)
                                      hResultTy).1
                                  have hArgTypes :
                                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                        __eo_typeof a2 = Term.Int ∧
                                        __eo_typeof a3 = Term.Int := by
                                    change __eo_typeof_str_len
                                        (__eo_typeof_str_substr (__eo_typeof a1)
                                          (__eo_typeof a2) (__eo_typeof a3)) ≠
                                      Term.Stuck at hLhsNotStuck
                                    exact eo_typeof_str_len_str_substr_args_of_ne_stuck
                                      (__eo_typeof a1) (__eo_typeof a2)
                                      (__eo_typeof a3) hLhsNotStuck
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem1Raw : eo_interprets M P1 true :=
                                      hTrue P1 (by
                                        simp [P1, P2, P3, premiseTermList])
                                    have hPrem2Raw : eo_interprets M P2 true :=
                                      hTrue P2 (by
                                        simp [P1, P2, P3, premiseTermList])
                                    have hPrem3Raw : eo_interprets M P3 true :=
                                      hTrue P3 (by
                                        simp [P1, P2, P3, premiseTermList])
                                    have hPrem1 :
                                        eo_interprets M
                                          (substrRangeStartPremise a2) true := by
                                      simpa [hP1Shape] using hPrem1Raw
                                    have hPrem2 :
                                        eo_interprets M
                                          (substrRangeLenPremise a3) true := by
                                      simpa [hP2Shape] using hPrem2Raw
                                    have hPrem3 :
                                        eo_interprets M
                                          (substrRangeInBoundsPremise a1 a2 a3)
                                          true := by
                                      simpa [hP3Shape] using hPrem3Raw
                                    exact facts___eo_prog_str_len_substr_in_range_impl
                                      M hM a1 a2 a3 P1 P2 P3 hA1Trans hA2Trans
                                      hA3Trans hArgTypes hPrem1 hPrem2 hPrem3
                                      hProgEq
                                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (typed___eo_prog_str_len_substr_in_range_impl
                                        a1 a2 a3 P1 P2 P3 hA1Trans hA2Trans
                                        hA3Trans hArgTypes hProgEq)
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
