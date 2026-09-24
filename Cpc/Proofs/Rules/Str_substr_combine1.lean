module

public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrSubstrContainsSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem native_seq_extract_empty_of_len_nonpos_local
    (xs : List SmtValue) (i n : native_Int) (h : n ≤ 0) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  simp [h]

private theorem native_seq_extract_empty_of_start_ge_len_local
    (xs : List SmtValue) (i n : native_Int)
    (h : native_seq_len xs ≤ i) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  have hLen : (Int.ofNat xs.length : native_Int) ≤ i := by
    simpa [native_seq_len] using h
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hLen)]

private theorem take_drop_nested_of_cover
    (xs : List SmtValue) (i m j n : Nat)
    (hCover : m ≤ j + n) :
    (((xs.drop i).take m).drop j).take n =
      (xs.drop (i + j)).take (m - j) := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  have hMin : min n (m - j) = m - j := by omega
  rw [hMin]

private theorem native_seq_extract_nested_of_declared_cover
    (xs : List SmtValue) (i m j n : native_Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hCover : m - j ≤ n) :
    native_seq_extract (native_seq_extract xs i m) j n =
      native_seq_extract xs (i + j) (m - j) := by
  by_cases hkLe : m - j ≤ 0
  · have hMLeJ : m ≤ j := Int.le_of_sub_nonpos hkLe
    have hRight : native_seq_extract xs (i + j) (m - j) = [] :=
      native_seq_extract_empty_of_len_nonpos_local _ _ _ hkLe
    rw [hRight]
    by_cases hmLe : m ≤ 0
    · rw [native_seq_extract_empty_of_len_nonpos_local xs i m hmLe]
      simp [native_seq_extract]
    · have hm : 0 < m := Int.lt_of_not_ge hmLe
      have hInnerEq := native_seq_extract_eq_drop_take xs i m hi hm
      have hInnerLen :
          Int.ofNat (native_seq_extract xs i m).length ≤ m := by
        rw [hInnerEq]
        have hLen : ((xs.drop (Int.toNat i)).take (Int.toNat m)).length ≤
            Int.toNat m := List.length_take_le _ _
        apply Int.le_trans (Int.ofNat_le.mpr hLen)
        rw [Int.toNat_of_nonneg (Int.le_of_lt hm)]
        exact Int.le_refl m
      have hStart : native_seq_len (native_seq_extract xs i m) ≤ j := by
        simpa [native_seq_len] using Int.le_trans hInnerLen hMLeJ
      exact native_seq_extract_empty_of_start_ge_len_local
        (native_seq_extract xs i m) j n hStart
  · have hk : 0 < m - j := Int.lt_of_not_ge hkLe
    have hm : 0 < m := Int.lt_of_lt_of_le hk (Int.sub_le_self m hj)
    have hn : 0 < n := Int.lt_of_lt_of_le hk hCover
    rw [native_seq_extract_eq_drop_take xs i m hi hm]
    rw [native_seq_extract_eq_drop_take _ j n hj hn]
    rw [native_seq_extract_eq_drop_take xs (i + j) (m - j)
      (Int.add_nonneg hi hj) hk]
    rw [Int.toNat_add hi hj]
    have hSubNat : Int.toNat (m - j) = Int.toNat m - Int.toNat j := by
      rw [← Int.toNat_of_nonneg (Int.le_of_lt hm),
        ← Int.toNat_of_nonneg hj]
      exact Int.toNat_sub (Int.toNat m) (Int.toNat j)
    rw [hSubNat]
    apply take_drop_nested_of_cover
    have hCover' : m ≤ j + n := by
      have hSub : m + (-j) ≤ n := by
        simpa [Int.sub_eq_add_neg] using hCover
      have hLe : m ≤ n - (-j) := Int.add_le_iff_le_sub.mp hSub
      simpa [Int.sub_eq_add_neg, Int.add_comm, Int.add_left_comm,
        Int.add_assoc] using hLe
    apply Int.ofNat_le.mp
    rw [← Int.ofNat_add_ofNat, Int.toNat_of_nonneg hj,
      Int.toNat_of_nonneg (Int.le_of_lt hn),
      Int.toNat_of_nonneg (Int.le_of_lt hm)]
    exact hCover'

private theorem smtx_eval_neg_term_eq_local
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private abbrev combine1NonnegPremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev combine1Inner (s n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m

private abbrev combine1BoundPremise
    (s n1 m1 n2 m2 : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq
        (Term.Apply (Term.Apply Term.neg m2)
          (Term.Apply (Term.Apply Term.neg m1) n2)))
        (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev combine1Lhs
    (s n1 m1 n2 m2 : Term) : Term :=
  combine1Inner (combine1Inner s n1 m1) n2 m2

private abbrev combine1Start (n1 n2 : Term) : Term :=
  Term.Apply (Term.Apply Term.plus n1)
    (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0))

private abbrev combine1Rhs
    (s n1 m1 n2 : Term) : Term :=
  combine1Inner s (combine1Start n1 n2)
    (Term.Apply (Term.Apply Term.neg m1) n2)

private abbrev combine1Conclusion
    (s n1 m1 n2 m2 : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (combine1Lhs s n1 m1 n2 m2))
    (combine1Rhs s n1 m1 n2)

private theorem prog_str_substr_combine1_info
    (s n1 m1 n2 m2 P1 P2 P3 : Term)
    (hProg :
      __eo_prog_str_substr_combine1 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠ Term.Stuck) :
    P1 = combine1NonnegPremise n1 ∧
      P2 = combine1NonnegPremise n2 ∧
      P3 = combine1BoundPremise s n1 m1 n2 m2 ∧
      __eo_prog_str_substr_combine1 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        combine1Conclusion s n1 m1 n2 m2 := by
  unfold __eo_prog_str_substr_combine1 at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 heq3 =>
    cases heq1
    cases heq2
    cases heq3
    have hGuard := support_eo_requires_cond_eq_of_non_stuck hProg
    have h1234 := StrEqReplSupport.eo_and_eq_true_left hGuard
    have h5 := StrEqReplSupport.eo_and_eq_true_right hGuard
    have h123 := StrEqReplSupport.eo_and_eq_true_left h1234
    have h4 := StrEqReplSupport.eo_and_eq_true_right h1234
    have h12 := StrEqReplSupport.eo_and_eq_true_left h123
    have h3 := StrEqReplSupport.eo_and_eq_true_right h123
    have h1 := StrEqReplSupport.eo_and_eq_true_left h12
    have h2 := StrEqReplSupport.eo_and_eq_true_right h12
    have e1 := RuleProofs.eq_of_eo_eq_true _ _ h1
    have e2 := RuleProofs.eq_of_eo_eq_true _ _ h2
    have e3 := RuleProofs.eq_of_eo_eq_true _ _ h3
    have e4 := RuleProofs.eq_of_eo_eq_true _ _ h4
    have e5 := RuleProofs.eq_of_eo_eq_true _ _ h5
    subst_vars
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_combine1, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, combine1Conclusion, combine1Lhs,
      combine1Rhs, combine1Inner, combine1Start]

private theorem typed___eo_prog_str_substr_combine1_impl
    (s n1 m1 n2 m2 P1 P2 P3 : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hN1Trans : RuleProofs.eo_has_smt_translation n1)
    (hM1Trans : RuleProofs.eo_has_smt_translation m1)
    (hN2Trans : RuleProofs.eo_has_smt_translation n2)
    (hM2Trans : RuleProofs.eo_has_smt_translation m2)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hN1Ty : __eo_typeof n1 = Term.Int)
    (hM1Ty : __eo_typeof m1 = Term.Int)
    (hN2Ty : __eo_typeof n2 = Term.Int)
    (hM2Ty : __eo_typeof m2 = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_combine1 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        combine1Conclusion s n1 m1 n2 m2) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_combine1 s n1 m1 n2 m2
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) := by
  let inner := combine1Inner s n1 m1
  let lhs := combine1Lhs s n1 m1 n2 m2
  let rhs := combine1Rhs s n1 m1 n2
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hN1SmtTy := smtx_typeof_of_eo_int n1 hN1Trans hN1Ty
  have hM1SmtTy := smtx_typeof_of_eo_int m1 hM1Trans hM1Ty
  have hN2SmtTy := smtx_typeof_of_eo_int n2 hN2Trans hN2Ty
  have hM2SmtTy := smtx_typeof_of_eo_int m2 hM2Trans hM2Ty
  have hInnerTy : __smtx_typeof (__eo_to_smt inner) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1)
          (__eo_to_smt m1)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hN1SmtTy, hM1SmtTy, __smtx_typeof_str_substr]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt inner) (__eo_to_smt n2)
          (__eo_to_smt m2)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hInnerTy, hN2SmtTy, hM2SmtTy, __smtx_typeof_str_substr]
  have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_def]
  have hTailPlusTy : __smtx_typeof
      (SmtTerm.plus (__eo_to_smt n2) (SmtTerm.Numeral 0)) =
        SmtType.Int := by
    rw [typeof_plus_eq]
    simp [hN2SmtTy, hZeroTy, __smtx_typeof_arith_overload_op_2]
  have hStartTy : __smtx_typeof (__eo_to_smt (combine1Start n1 n2)) =
      SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.plus (__eo_to_smt n1)
          (SmtTerm.plus (__eo_to_smt n2) (SmtTerm.Numeral 0))) =
      SmtType.Int
    rw [typeof_plus_eq]
    simp [hN1SmtTy, hTailPlusTy, __smtx_typeof_arith_overload_op_2]
  have hRemainingTy : __smtx_typeof
      (SmtTerm.neg (__eo_to_smt m1) (__eo_to_smt n2)) = SmtType.Int := by
    rw [typeof_neg_eq]
    simp [hM1SmtTy, hN2SmtTy, __smtx_typeof_arith_overload_op_2]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s)
          (__eo_to_smt (combine1Start n1 n2))
          (SmtTerm.neg (__eo_to_smt m1) (__eo_to_smt n2))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hStartTy, hRemainingTy, __smtx_typeof_str_substr]
  have hBool : RuleProofs.eo_has_bool_type
      (combine1Conclusion s n1 m1 n2 m2) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_substr_combine1_impl
    (M : SmtModel) (hM : model_wf M)
    (s n1 m1 n2 m2 P1 P2 P3 : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hN1Trans : RuleProofs.eo_has_smt_translation n1)
    (hM1Trans : RuleProofs.eo_has_smt_translation m1)
    (hN2Trans : RuleProofs.eo_has_smt_translation n2)
    (hM2Trans : RuleProofs.eo_has_smt_translation m2)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hN1Ty : __eo_typeof n1 = Term.Int)
    (hM1Ty : __eo_typeof m1 = Term.Int)
    (hN2Ty : __eo_typeof n2 = Term.Int)
    (hM2Ty : __eo_typeof m2 = Term.Int)
    (hPrem1 : eo_interprets M (combine1NonnegPremise n1) true)
    (hPrem2 : eo_interprets M (combine1NonnegPremise n2) true)
    (hPrem3 : eo_interprets M
      (combine1BoundPremise s n1 m1 n2 m2) true)
    (hProgEq :
      __eo_prog_str_substr_combine1 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        combine1Conclusion s n1 m1 n2 m2) :
    eo_interprets M
      (__eo_prog_str_substr_combine1 s n1 m1 n2 m2
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) true := by
  let inner := combine1Inner s n1 m1
  let lhs := combine1Lhs s n1 m1 n2 m2
  let rhs := combine1Rhs s n1 m1 n2
  have hBool : RuleProofs.eo_has_bool_type
      (combine1Conclusion s n1 m1 n2 m2) := by
    simpa [hProgEq] using typed___eo_prog_str_substr_combine1_impl
      s n1 m1 n2 m2 P1 P2 P3 hSTrans hN1Trans hM1Trans hN2Trans
      hM2Trans hSTy hN1Ty hM1Ty hN2Ty hM2Ty hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hN1SmtTy := smtx_typeof_of_eo_int n1 hN1Trans hN1Ty
  have hM1SmtTy := smtx_typeof_of_eo_int m1 hM1Trans hM1Ty
  have hN2SmtTy := smtx_typeof_of_eo_int n2 hN2Trans hN2Ty
  have hM2SmtTy := smtx_typeof_of_eo_int m2 hM2Trans hM2Ty
  have hSEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hN1EvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt n1)) = SmtType.Int := by
    simpa [hN1SmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt n1) (by
        unfold term_has_non_none_type
        rw [hN1SmtTy]
        simp)
  have hM1EvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt m1)) = SmtType.Int := by
    simpa [hM1SmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt m1) (by
        unfold term_has_non_none_type
        rw [hM1SmtTy]
        simp)
  have hN2EvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt n2)) = SmtType.Int := by
    simpa [hN2SmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt n2) (by
        unfold term_has_non_none_type
        rw [hN2SmtTy]
        simp)
  have hM2EvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt m2)) = SmtType.Int := by
    simpa [hM2SmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt m2) (by
        unfold term_has_non_none_type
        rw [hM2SmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hN1EvalTy with ⟨n1i, hN1Eval⟩
  rcases int_value_canonical hM1EvalTy with ⟨m1i, hM1Eval⟩
  rcases int_value_canonical hN2EvalTy with ⟨n2i, hN2Eval⟩
  rcases int_value_canonical hM2EvalTy with ⟨m2i, hM2Eval⟩
  have hNonnegOfPrem (t : Term) (ti : native_Int)
      (hEvalT : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral ti)
      (hPrem : eo_interprets M (combine1NonnegPremise t) true) :
      0 ≤ ti := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.geq (__eo_to_smt t) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq, hEvalT,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0 ti = true := by
          simpa [__smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, native_veq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hN1Nonneg := hNonnegOfPrem n1 n1i hN1Eval hPrem1
  have hN2Nonneg := hNonnegOfPrem n2 n2i hN2Eval hPrem2
  have hBound : m1i - n2i ≤ m2i := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem3
    cases hPrem3 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.neg (__eo_to_smt m2)
                  (SmtTerm.neg (__eo_to_smt m1) (__eo_to_smt n2)))
                (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_neg_term_eq_local, smtx_eval_neg_term_eq_local,
          hM1Eval, hN2Eval, hM2Eval, smtx_eval_numeral_term_eq,
          smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0
            (native_zplus m2i
              (native_zneg (native_zplus m1i (native_zneg n2i)))) = true := by
          simpa [__smtx_model_eval__, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq]
            using hEval
        have hLeAdd : 0 ≤ m2i + (-(m1i + (-n2i))) := by
          simp only [SmtEval.native_zleq, native_zplus, SmtEval.native_zplus, native_zneg] at hLeBool
          exact of_decide_eq_true hLeBool
        have hLe : 0 ≤ m2i - (m1i - n2i) := by
          simpa [Int.sub_eq_add_neg] using hLeAdd
        exact Int.sub_nonneg.mp hLe
  have hSeqTy : __smtx_typeof_seq_value ss =
      SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hSEvalTy
  have hElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSeqTy
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1)
            (__eo_to_smt m1)) (__eo_to_smt n2) (__eo_to_smt m2)) =
      __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt s)
          (SmtTerm.plus (__eo_to_smt n1)
            (SmtTerm.plus (__eo_to_smt n2) (SmtTerm.Numeral 0)))
          (SmtTerm.neg (__eo_to_smt m1) (__eo_to_smt n2)))
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_substr_term_eq,
      smtx_eval_str_substr_term_eq, smtx_eval_plus_term_eq,
      smtx_eval_plus_term_eq, smtx_eval_neg_term_eq_local,
      hSEval, hN1Eval, hM1Eval, hN2Eval, hM2Eval,
      smtx_eval_numeral_term_eq]
    simp [__smtx_model_eval_str_substr, __smtx_model_eval_plus,
      __smtx_model_eval__, native_zplus, SmtEval.native_zplus, native_zneg,
      Int.sub_eq_add_neg, hElem, elem_typeof_pack_seq,
      Smtm.native_unpack_pack_seq,
      native_seq_extract_nested_of_declared_cover _ _ _ _ _ hN1Nonneg
        hN2Nonneg hBound]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_combine1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_combine1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_combine1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_combine1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_combine1 args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons a3 args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons a4 args =>
                  cases args with
                  | nil => exact absurd rfl hProg
                  | cons a5 args =>
                      cases args with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          cases premises with
                          | nil => exact absurd rfl hProg
                          | cons p1 premises =>
                              cases premises with
                              | nil => exact absurd rfl hProg
                              | cons p2 premises =>
                                  cases premises with
                                  | nil => exact absurd rfl hProg
                                  | cons p3 premises =>
                                      cases premises with
                                      | cons _ _ => exact absurd rfl hProg
                                      | nil =>
                                          let P1 := __eo_state_proven_nth s p1
                                          let P2 := __eo_state_proven_nth s p2
                                          let P3 := __eo_state_proven_nth s p3
                                          have hA1Trans :
                                              RuleProofs.eo_has_smt_translation a1 := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using
                                                hCmdTrans.1
                                          have hA2Trans :
                                              RuleProofs.eo_has_smt_translation a2 := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using
                                                hCmdTrans.2.1
                                          have hA3Trans :
                                              RuleProofs.eo_has_smt_translation a3 := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using
                                                hCmdTrans.2.2.1
                                          have hA4Trans :
                                              RuleProofs.eo_has_smt_translation a4 := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using
                                                hCmdTrans.2.2.2.1
                                          have hA5Trans :
                                              RuleProofs.eo_has_smt_translation a5 := by
                                            simpa [cmdTranslationOk,
                                              cArgListTranslationOk] using
                                                hCmdTrans.2.2.2.2.1
                                          change __eo_typeof
                                              (__eo_prog_str_substr_combine1
                                                a1 a2 a3 a4 a5
                                                (Proof.pf P1) (Proof.pf P2)
                                                (Proof.pf P3)) =
                                            Term.Bool at hResultTy
                                          have hRuleProg :
                                              __eo_prog_str_substr_combine1
                                                  a1 a2 a3 a4 a5
                                                  (Proof.pf P1) (Proof.pf P2)
                                                  (Proof.pf P3) ≠
                                                Term.Stuck :=
                                            term_ne_stuck_of_typeof_bool hResultTy
                                          rcases prog_str_substr_combine1_info
                                              a1 a2 a3 a4 a5 P1 P2 P3
                                              hRuleProg with
                                            ⟨hP1, hP2, hP3, hProgEq⟩
                                          rw [hProgEq] at hResultTy
                                          have hOpsNN :
                                              __eo_typeof
                                                  (combine1Lhs
                                                    a1 a2 a3 a4 a5) ≠
                                                  Term.Stuck ∧
                                                __eo_typeof
                                                  (combine1Rhs
                                                    a1 a2 a3 a4) ≠
                                                  Term.Stuck := by
                                            change __eo_typeof_eq
                                                (__eo_typeof
                                                  (combine1Lhs
                                                    a1 a2 a3 a4 a5))
                                                (__eo_typeof
                                                  (combine1Rhs
                                                    a1 a2 a3 a4)) =
                                              Term.Bool at hResultTy
                                            exact
                                              RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                                _ _ hResultTy
                                          have hLhsNN := hOpsNN.1
                                          change __eo_typeof_str_substr
                                              (__eo_typeof
                                                (combine1Inner a1 a2 a3))
                                              (__eo_typeof a4)
                                              (__eo_typeof a5) ≠
                                            Term.Stuck at hLhsNN
                                          rcases
                                              eo_typeof_str_substr_args_of_ne_stuck
                                                (__eo_typeof
                                                  (combine1Inner a1 a2 a3))
                                                (__eo_typeof a4)
                                                (__eo_typeof a5) hLhsNN with
                                            ⟨T, hInnerTy, hA4Ty, hA5Ty⟩
                                          have hInnerNN :
                                              __eo_typeof
                                                  (combine1Inner a1 a2 a3) ≠
                                                Term.Stuck := by
                                            rw [hInnerTy]
                                            simp
                                          change __eo_typeof_str_substr
                                              (__eo_typeof a1)
                                              (__eo_typeof a2)
                                              (__eo_typeof a3) ≠
                                            Term.Stuck at hInnerNN
                                          rcases
                                              eo_typeof_str_substr_args_of_ne_stuck
                                                (__eo_typeof a1)
                                                (__eo_typeof a2)
                                                (__eo_typeof a3) hInnerNN with
                                            ⟨U, hA1Ty, hA2Ty, hA3Ty⟩
                                          have hInnerCalc :
                                              __eo_typeof
                                                  (combine1Inner a1 a2 a3) =
                                                Term.Apply Term.Seq U := by
                                            change __eo_typeof_str_substr
                                                (__eo_typeof a1)
                                                (__eo_typeof a2)
                                                (__eo_typeof a3) =
                                              Term.Apply Term.Seq U
                                            rw [hA1Ty, hA2Ty, hA3Ty]
                                            exact
                                              eo_typeof_str_substr_result_of_seq_args
                                                U (by
                                                  simpa [hA1Ty, hA2Ty, hA3Ty]
                                                    using hInnerNN)
                                          rw [hInnerTy] at hInnerCalc
                                          cases hInnerCalc
                                          refine ⟨?_, ?_⟩
                                          · intro hTrue
                                            have hPrem1Raw :
                                                eo_interprets M P1 true :=
                                              hTrue P1 (by
                                                simp [P1, premiseTermList])
                                            have hPrem2Raw :
                                                eo_interprets M P2 true :=
                                              hTrue P2 (by
                                                simp [P2, premiseTermList])
                                            have hPrem3Raw :
                                                eo_interprets M P3 true :=
                                              hTrue P3 (by
                                                simp [P3, premiseTermList])
                                            have hPrem1 : eo_interprets M
                                                (combine1NonnegPremise a2)
                                                true := by
                                              simpa [hP1] using hPrem1Raw
                                            have hPrem2 : eo_interprets M
                                                (combine1NonnegPremise a4)
                                                true := by
                                              simpa [hP2] using hPrem2Raw
                                            have hPrem3 : eo_interprets M
                                                (combine1BoundPremise
                                                  a1 a2 a3 a4 a5) true := by
                                              simpa [hP3] using hPrem3Raw
                                            exact
                                              facts___eo_prog_str_substr_combine1_impl
                                                M hM a1 a2 a3 a4 a5
                                                P1 P2 P3 hA1Trans hA2Trans
                                                hA3Trans hA4Trans hA5Trans
                                                hA1Ty hA2Ty hA3Ty hA4Ty hA5Ty
                                                hPrem1 hPrem2 hPrem3 hProgEq
                                          · exact
                                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                _
                                                (typed___eo_prog_str_substr_combine1_impl
                                                  a1 a2 a3 a4 a5 P1 P2 P3
                                                  hA1Trans hA2Trans hA3Trans
                                                  hA4Trans hA5Trans hA1Ty
                                                  hA2Ty hA3Ty hA4Ty hA5Ty
                                                  hProgEq)
