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

private abbrev substrEmptyLeqStartPremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev substrEmptyLeqLenPremise (m : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt m) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev substrEmptyLeqEmptyPremise (emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len emp))
    (Term.Numeral 0)

private abbrev substrEmptyLeqExtract (s n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m

private abbrev substrEmptyLeqLhs (s emp n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrEmptyLeqExtract s n m)) emp

private abbrev substrEmptyLeqRhs (s n : Term) : Term :=
  Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_len s)) n

private abbrev substrEmptyLeqConclusion (s emp n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrEmptyLeqLhs s emp n m))
    (substrEmptyLeqRhs s n)

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

private theorem eo_typeof_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not] at h ⊢
      exact h

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

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq
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

private theorem native_seq_extract_empty_of_start_ge_len
    (xs : List SmtValue) (i n : native_Int)
    (h : native_seq_len xs <= i) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  have hLen : (↑xs.length : native_Int) <= i := by
    simpa [native_seq_len] using h
  simp [hLen]

private theorem native_seq_extract_ne_nil_of_start_lt_len_pos
    (xs : List SmtValue) (i n : native_Int)
    (hi : 0 <= i) (hlt : i < Int.ofNat xs.length) (hn : 0 < n) :
    native_seq_extract xs i n ≠ [] := by
  simp only [native_seq_extract]
  have hCondFalse :
      ¬ (decide (i < 0) || decide (n <= 0) ||
            decide (i >= Int.ofNat xs.length)) = true := by
    simp [Bool.or_eq_true, decide_eq_true_eq]
    grind
  split
  · rename_i h
    exact False.elim (hCondFalse h)
  · have hStartLtNat : Int.toNat i < xs.length := by
      exact (Int.toNat_lt hi).mpr hlt
    have hDropPos : 0 < (xs.drop (Int.toNat i)).length := by
      rw [List.length_drop]
      exact Nat.sub_pos_of_lt hStartLtNat
    have hDiffPos : 0 < Int.ofNat xs.length - i := Int.sub_pos.mpr hlt
    have hMinPos : 0 < min n (Int.ofNat xs.length - i) := by
      exact (Int.lt_min).2 ⟨hn, hDiffPos⟩
    have hMinNonneg : 0 <= min n (Int.ofNat xs.length - i) :=
      Int.le_of_lt hMinPos
    have hTakePos :
        0 < Int.toNat (min n (Int.ofNat xs.length - i)) := by
      have hMinCast :
          Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) =
            min n (Int.ofNat xs.length - i) :=
        Int.toNat_of_nonneg hMinNonneg
      have hLtCast :
          (0 : Int) <
            Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) := by
        rw [hMinCast]
        exact hMinPos
      have hNatLt :
          Int.toNat (0 : Int) <
            Int.toNat (min n (Int.ofNat xs.length - i)) :=
        (Int.toNat_lt (by omega : (0 : Int) <= 0)).mpr hLtCast
      simpa using hNatLt
    have hTakeLenPos :
        0 <
          ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length := by
      rw [List.length_take]
      exact (Nat.lt_min).2 ⟨hTakePos, hDropPos⟩
    exact List.length_pos_iff.mp hTakeLenPos

private theorem native_veq_substr_empty_eq_start_ge_len
    (T : SmtType) (xs : List SmtValue) (rseq : SmtSeq) (i n : native_Int)
    (hrseq : native_pack_seq T [] = rseq)
    (hi : 0 <= i) (hn : 0 < n) :
    native_veq
        (SmtValue.Seq (native_pack_seq T (native_seq_extract xs i n)))
        (SmtValue.Seq rseq) =
      native_zleq (Int.ofNat xs.length) i := by
  by_cases hStartGe : Int.ofNat xs.length <= i
  · have hExtract : native_seq_extract xs i n = [] :=
      native_seq_extract_empty_of_start_ge_len xs i n (by
        simpa [native_seq_len] using hStartGe)
    simpa [native_veq, native_zleq, SmtEval.native_zleq, hExtract,
      hrseq] using hStartGe
  · have hStartLt : i < Int.ofNat xs.length := Int.lt_of_not_ge hStartGe
    have hExtractNe : native_seq_extract xs i n ≠ [] :=
      native_seq_extract_ne_nil_of_start_lt_len_pos xs i n hi hStartLt hn
    have hLeftNe :
        SmtValue.Seq (native_pack_seq T (native_seq_extract xs i n)) ≠
          SmtValue.Seq rseq := by
      intro hEq
      injection hEq with hPackEq
      rw [← hrseq] at hPackEq
      cases hExtract : native_seq_extract xs i n with
      | nil =>
          exact hExtractNe hExtract
      | cons v vs =>
          rw [hExtract] at hPackEq
          simp [native_pack_seq] at hPackEq
    have hZleqFalse : native_zleq (Int.ofNat xs.length) i = false := by
      simpa [native_zleq, SmtEval.native_zleq] using hStartGe
    simpa [native_veq, hLeftNe] using hZleqFalse.symm

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

private theorem eqs_of_requires3_and_eq_true_not_stuck
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
  have h12 : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) =
      Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have h3 : __eo_eq x3 y3 = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have h1 : __eo_eq x1 y1 = Term.Boolean true :=
    eo_and_eq_true_left h12
  have h2 : __eo_eq x2 y2 = Term.Boolean true :=
    eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3⟩

private theorem prog_str_substr_eq_empty_leq_len_info
    (s emp n m Pn Pm Pemp : Term)
    (hProg :
      __eo_prog_str_substr_eq_empty_leq_len s emp n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pemp) ≠ Term.Stuck) :
    ∃ n0 m0 emp0,
      Pn = substrEmptyLeqStartPremise n0 ∧
      Pm = substrEmptyLeqLenPremise m0 ∧
      Pemp = substrEmptyLeqEmptyPremise emp0 ∧
      n0 = n ∧ m0 = m ∧ emp0 = emp ∧
      __eo_prog_str_substr_eq_empty_leq_len s emp n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pemp) =
        substrEmptyLeqConclusion s emp n m := by
  unfold __eo_prog_str_substr_eq_empty_leq_len at hProg
  split at hProg <;> try contradiction
  next heqN heqM heqEmp =>
    cases heqN
    cases heqM
    cases heqEmp
    rcases eqs_of_requires3_and_eq_true_not_stuck hProg with
      ⟨hn0, hm0, hemp0⟩
    subst_vars
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_eq_empty_leq_len, __eo_requires, __eo_and,
      __eo_eq, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, substrEmptyLeqConclusion, substrEmptyLeqLhs,
      substrEmptyLeqRhs, substrEmptyLeqExtract, substrEmptyLeqStartPremise,
      substrEmptyLeqLenPremise, substrEmptyLeqEmptyPremise]

private theorem facts___eo_prog_str_substr_eq_empty_leq_len_impl
    (M : SmtModel) (hM : model_wf M) (s emp n m Pn Pm Pemp T : Term)
    (hBoolEq : RuleProofs.eo_has_bool_type (substrEmptyLeqConclusion s emp n m))
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hPremN : eo_interprets M (substrEmptyLeqStartPremise n) true)
    (hPremM : eo_interprets M (substrEmptyLeqLenPremise m) true)
    (hPremEmp : eo_interprets M (substrEmptyLeqEmptyPremise emp) true)
    (hProgEq :
      __eo_prog_str_substr_eq_empty_leq_len s emp n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pemp) =
        substrEmptyLeqConclusion s emp n m) :
    eo_interprets M
      (__eo_prog_str_substr_eq_empty_leq_len s emp n m
        (Proof.pf Pn) (Proof.pf Pm) (Proof.pf Pemp)) true := by
  let lhs := substrEmptyLeqLhs s emp n m
  let rhs := substrEmptyLeqRhs s n
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
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
  have hEmpEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt emp)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hEmpSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt emp) (by
        unfold term_has_non_none_type
        rw [hEmpSmtTy]
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
  rcases seq_value_canonical hEmpEvalTy with ⟨empSeq, hEmpEval⟩
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
          simpa [__smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, native_veq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hMPos : 0 < mi := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremM
    cases hPremM with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.gt (__eo_to_smt m) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq, hMEval,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        have hGtBool : native_zlt 0 mi = true := by
          simpa [__smtx_model_eval_eq, __smtx_model_eval_gt,
            __smtx_model_eval_lt, native_veq] using hEval
        simpa [SmtEval.native_zlt] using hGtBool
  have hEmpLenZero : native_seq_len (native_unpack_seq empSeq) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremEmp
    cases hPremEmp with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt emp))
              (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hEmpEval,
          smtx_eval_numeral_term_eq] at hEval
        simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len,
          native_veq, SmtEval.native_zeq] using hEval
  have hEmpNil : native_unpack_seq empSeq = [] := by
    have hLenNat : (native_unpack_seq empSeq).length = 0 := by
      have hLenInt : Int.ofNat (native_unpack_seq empSeq).length = 0 := by
        simpa [native_seq_len] using hEmpLenZero
      exact Int.ofNat_eq_zero.mp hLenInt
    exact List.eq_nil_of_length_eq_zero hLenNat
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hSEvalTy
  have hEmpSeqTy :
      __smtx_typeof_seq_value empSeq = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hEmpEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hEmpEvalTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hEmpElem : __smtx_elem_typeof_seq_value empSeq = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hEmpSeqTy
  have hEmpPack : native_pack_seq (__eo_to_smt_type T) [] = empSeq := by
    have hPack := native_pack_unpack_seq empSeq
    rw [← hEmpElem]
    simpa [hEmpNil] using hPack
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt m))
          (__eo_to_smt emp)) =
      __smtx_model_eval M
        (SmtTerm.leq (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_substr_term_eq, hSEval,
      hNEval, hMEval, hEmpEval]
    rw [smtx_eval_leq_term_eq, smtx_eval_str_len_term_eq, hSEval, hNEval]
    simp [__smtx_model_eval_eq, __smtx_model_eval_str_substr,
      __smtx_model_eval_leq, __smtx_model_eval_str_len, native_seq_len,
      hSElem,
      native_veq_substr_empty_eq_start_ge_len (__eo_to_smt_type T)
        (native_unpack_seq ss) empSeq ni mi hEmpPack hNNonneg hMPos]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs
    (by simpa [substrEmptyLeqConclusion, lhs, rhs] using hBoolEq) <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_eq_empty_leq_len_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_eq_empty_leq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_eq_empty_leq_len args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_eq_empty_leq_len args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_eq_empty_leq_len args premises ≠
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
                                      let Pn := __eo_state_proven_nth s p1
                                      let Pm := __eo_state_proven_nth s p2
                                      let Pemp := __eo_state_proven_nth s p3
                                      have hA1Trans :
                                          RuleProofs.eo_has_smt_translation a1 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk]
                                          using hCmdTrans.1
                                      have hA2Trans :
                                          RuleProofs.eo_has_smt_translation a2 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk]
                                          using hCmdTrans.2.1
                                      have hA3Trans :
                                          RuleProofs.eo_has_smt_translation a3 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk]
                                          using hCmdTrans.2.2.1
                                      have hA4Trans :
                                          RuleProofs.eo_has_smt_translation a4 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk]
                                          using hCmdTrans.2.2.2.1
                                      change __eo_typeof
                                          (__eo_prog_str_substr_eq_empty_leq_len a1 a2 a3 a4
                                            (Proof.pf Pn) (Proof.pf Pm)
                                            (Proof.pf Pemp)) =
                                        Term.Bool at hResultTy
                                      have hProgRule :
                                          __eo_prog_str_substr_eq_empty_leq_len a1 a2 a3 a4
                                              (Proof.pf Pn) (Proof.pf Pm)
                                              (Proof.pf Pemp) ≠
                                            Term.Stuck :=
                                        term_ne_stuck_of_typeof_bool hResultTy
                                      rcases prog_str_substr_eq_empty_leq_len_info a1 a2 a3 a4
                                          Pn Pm Pemp hProgRule with
                                        ⟨n0, m0, emp0, hPremNShape,
                                          hPremMShape, hPremEmpShape, hn0, hm0,
                                          hemp0, hProgEq⟩
                                      subst n0
                                      subst m0
                                      subst emp0
                                      let lhs := substrEmptyLeqLhs a1 a2 a3 a4
                                      let rhs := substrEmptyLeqRhs a1 a3
                                      let extract := substrEmptyLeqExtract a1 a3 a4
                                      rw [hProgEq] at hResultTy
                                      change __eo_typeof
                                          (Term.Apply (Term.Apply Term.eq lhs) rhs) =
                                        Term.Bool at hResultTy
                                      change __eo_typeof_eq (__eo_typeof lhs)
                                          (__eo_typeof rhs) =
                                        Term.Bool at hResultTy
                                      have hOuterOperands :=
                                        RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                          (__eo_typeof lhs) (__eo_typeof rhs) hResultTy
                                      have hLhsTy : __eo_typeof lhs = Term.Bool := by
                                        change __eo_typeof_eq (__eo_typeof extract)
                                            (__eo_typeof a2) = Term.Bool
                                        exact eo_typeof_eq_bool_of_ne_stuck
                                          (__eo_typeof extract) (__eo_typeof a2)
                                          hOuterOperands.1
                                      have hInnerOperands :=
                                        RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                          (__eo_typeof extract) (__eo_typeof a2) hLhsTy
                                      have hSubstrNotStuck := hInnerOperands.1
                                      change __eo_typeof_str_substr (__eo_typeof a1)
                                          (__eo_typeof a3) (__eo_typeof a4) ≠
                                        Term.Stuck at hSubstrNotStuck
                                      rcases eo_typeof_str_substr_args_of_ne_stuck
                                          (__eo_typeof a1) (__eo_typeof a3)
                                          (__eo_typeof a4) hSubstrNotStuck with
                                        ⟨T, hA1TyT, hA3Ty, hA4Ty⟩
                                      have hExtractTy :
                                          __eo_typeof extract = Term.Apply Term.Seq T := by
                                        change __eo_typeof_str_substr (__eo_typeof a1)
                                          (__eo_typeof a3) (__eo_typeof a4) =
                                          Term.Apply Term.Seq T
                                        simp [hA1TyT, hA3Ty, hA4Ty,
                                          __eo_typeof_str_substr]
                                      have hA2Ty :
                                          __eo_typeof a2 = Term.Apply Term.Seq T := by
                                        have hInnerEq :=
                                          RuleProofs.eo_typeof_eq_bool_operands_eq
                                            (__eo_typeof extract) (__eo_typeof a2)
                                            hLhsTy
                                        rw [← hInnerEq, hExtractTy]
                                      have hA1SmtTy :=
                                        smtx_typeof_of_eo_seq a1 T hA1Trans hA1TyT
                                      have hA2SmtTy :=
                                        smtx_typeof_of_eo_seq a2 T hA2Trans hA2Ty
                                      have hA3SmtTy :=
                                        smtx_typeof_of_eo_int a3 hA3Trans hA3Ty
                                      have hA4SmtTy :=
                                        smtx_typeof_of_eo_int a4 hA4Trans hA4Ty
                                      have hExtractSmtTy :
                                          __smtx_typeof (__eo_to_smt extract) =
                                            SmtType.Seq (__eo_to_smt_type T) := by
                                        change __smtx_typeof
                                            (SmtTerm.str_substr (__eo_to_smt a1)
                                              (__eo_to_smt a3) (__eo_to_smt a4)) =
                                          SmtType.Seq (__eo_to_smt_type T)
                                        rw [typeof_str_substr_eq]
                                        simp [hA1SmtTy, hA3SmtTy, hA4SmtTy,
                                          __smtx_typeof_str_substr]
                                      have hLhsSmtTy :
                                          __smtx_typeof (__eo_to_smt lhs) =
                                            SmtType.Bool := by
                                        have hEqBool :
                                            RuleProofs.eo_has_bool_type
                                              (Term.Apply
                                                (Term.Apply Term.eq extract) a2) :=
                                          RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                            extract a2
                                            (by rw [hExtractSmtTy, hA2SmtTy])
                                            (by rw [hExtractSmtTy]; simp)
                                        simpa [lhs, substrEmptyLeqLhs, __eo_to_smt, __smtx_typeof, extract,
                                          substrEmptyLeqExtract,
                                          RuleProofs.eo_has_bool_type] using hEqBool
                                      have hRhsSmtTy :
                                          __smtx_typeof (__eo_to_smt rhs) =
                                            SmtType.Bool := by
                                        change __smtx_typeof
                                            (SmtTerm.leq
                                              (SmtTerm.str_len (__eo_to_smt a1))
                                              (__eo_to_smt a3)) =
                                          SmtType.Bool
                                        have hLenSmtTy :
                                            __smtx_typeof
                                                (SmtTerm.str_len (__eo_to_smt a1)) =
                                              SmtType.Int := by
                                          rw [typeof_str_len_eq]
                                          simp [hA1SmtTy,
                                            __smtx_typeof_seq_op_1_ret]
                                        rw [typeof_leq_eq]
                                        simp [hLenSmtTy, hA3SmtTy,
                                          __smtx_typeof_arith_overload_op_2_ret,
                                          __smtx_typeof_seq_op_1_ret,
                                          native_ite, native_Teq]
                                      have hBoolEq :
                                          RuleProofs.eo_has_bool_type
                                            (substrEmptyLeqConclusion a1 a2 a3 a4) := by
                                        have hEqBool :
                                            RuleProofs.eo_has_bool_type
                                              (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
                                          RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                            lhs rhs
                                            (by rw [hLhsSmtTy, hRhsSmtTy])
                                            (by rw [hLhsSmtTy]; simp)
                                        simpa [substrEmptyLeqConclusion, lhs, rhs] using hEqBool
                                      refine ⟨?_, ?_⟩
                                      · intro hTrue
                                        have hPremNRaw : eo_interprets M Pn true :=
                                          hTrue Pn (by simp [Pn, Pm, Pemp, premiseTermList])
                                        have hPremMRaw : eo_interprets M Pm true :=
                                          hTrue Pm (by simp [Pn, Pm, Pemp, premiseTermList])
                                        have hPremEmpRaw : eo_interprets M Pemp true :=
                                          hTrue Pemp (by simp [Pn, Pm, Pemp, premiseTermList])
                                        have hPremN :
                                            eo_interprets M (substrEmptyLeqStartPremise a3)
                                              true := by
                                          simpa [hPremNShape] using hPremNRaw
                                        have hPremM :
                                            eo_interprets M (substrEmptyLeqLenPremise a4)
                                              true := by
                                          simpa [hPremMShape] using hPremMRaw
                                        have hPremEmp :
                                            eo_interprets M (substrEmptyLeqEmptyPremise a2)
                                              true := by
                                          simpa [hPremEmpShape] using hPremEmpRaw
                                        change eo_interprets M
                                          (__eo_prog_str_substr_eq_empty_leq_len a1 a2 a3 a4
                                            (Proof.pf Pn) (Proof.pf Pm)
                                            (Proof.pf Pemp)) true
                                        exact facts___eo_prog_str_substr_eq_empty_leq_len_impl
                                          M hM a1 a2 a3 a4 Pn Pm Pemp T hBoolEq
                                          hA1Trans hA2Trans hA3Trans hA4Trans
                                          hA1TyT hA2Ty hA3Ty hA4Ty hPremN hPremM
                                          hPremEmp hProgEq
                                      · change RuleProofs.eo_has_smt_translation
                                          (__eo_prog_str_substr_eq_empty_leq_len a1 a2 a3 a4
                                            (Proof.pf Pn) (Proof.pf Pm)
                                            (Proof.pf Pemp))
                                        rw [hProgEq]
                                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                          hBoolEq
                                  | cons _ _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
