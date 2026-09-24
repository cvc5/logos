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

private theorem take_drop_nested_of_bound
    (xs : List SmtValue) (i m j n : Nat)
    (hBound : j + n ≤ m) :
    (((xs.drop i).take m).drop j).take n =
      (xs.drop (i + j)).take n := by
  rw [List.drop_take, List.take_take, List.drop_drop]
  have hMin : min n (m - j) = n := by omega
  rw [hMin]

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

private theorem native_seq_extract_nested_of_bound
    (xs : List SmtValue) (i m j n : native_Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j)
    (hBound : j + n ≤ Int.ofNat (native_seq_extract xs i m).length) :
    native_seq_extract (native_seq_extract xs i m) j n =
      native_seq_extract xs (i + j) n := by
  by_cases hn : n ≤ 0
  · have hij : 0 ≤ i + j := Int.add_nonneg hi hj
    simp [native_seq_extract, hn, Int.not_lt.mpr hij]
  · have hnPos : 0 < n := Int.lt_of_not_ge hn
    have hInnerNonempty : native_seq_extract xs i m ≠ [] := by
      intro hEmpty
      rw [hEmpty] at hBound
      simp at hBound
      exact (Int.not_lt_of_ge hBound
        (Int.add_pos_of_nonneg_of_pos hj hnPos))
    have hmPos : 0 < m := by
      by_cases hmLe : m ≤ 0
      · exact False.elim (hInnerNonempty
          (native_seq_extract_empty_of_len_nonpos_local xs i m hmLe))
      · exact Int.lt_of_not_ge hmLe
    have hiLt : i < Int.ofNat xs.length := by
      by_cases hLenLe : Int.ofNat xs.length ≤ i
      · exact False.elim (hInnerNonempty
          (native_seq_extract_empty_of_start_ge_len_local xs i m (by
            simpa [native_seq_len] using hLenLe)))
      · exact Int.lt_of_not_ge hLenLe
    let inner := native_seq_extract xs i m
    let I := Int.toNat i
    let J := Int.toNat j
    let N := Int.toNat n
    let K := Int.toNat (min m (Int.ofNat xs.length - i))
    have hiCast : (I : native_Int) = i := Int.toNat_of_nonneg hi
    have hjCast : (J : native_Int) = j := Int.toNat_of_nonneg hj
    have hnCast : (N : native_Int) = n :=
      Int.toNat_of_nonneg (Int.le_of_lt hnPos)
    have hInnerEq : inner = (xs.drop I).take K := by
      unfold inner native_seq_extract I K
      rw [if_neg (by
        intro hGuard
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hGuard
        rcases hGuard with (hneg | hmLe) | hLenLe
        · exact (Int.not_lt_of_ge hi hneg)
        · exact (Int.not_le_of_gt hmPos hmLe)
        · exact (Int.not_le_of_gt hiLt hLenLe))]
    have hBoundNat : J + N ≤ inner.length := by
      apply Int.ofNat_le.mp
      rw [← Int.ofNat_add_ofNat, hjCast, hnCast]
      exact hBound
    have hInnerLenLe : inner.length ≤ xs.length - I := by
      rw [hInnerEq, List.length_take, List.length_drop]
      exact Nat.min_le_right _ _
    have hIWithin : I < xs.length := by
      apply Int.ofNat_lt.mp
      rw [hiCast]
      exact hiLt
    have hJNLe : J + N ≤ xs.length - I :=
      Nat.le_trans hBoundNat hInnerLenLe
    have hTotalNat : I + J + N ≤ xs.length := by
      have h := Nat.add_le_of_le_sub (Nat.le_of_lt hIWithin) hJNLe
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hNPos : 0 < N := by
      apply Int.natCast_pos.mp
      rw [hnCast]
      exact hnPos
    have hJWithin : J < inner.length := by omega
    have hIJWithin : I + J < xs.length := by omega
    have hOuterEq : native_seq_extract inner j n =
        (inner.drop J).take N := by
      have hJCast : (Int.toNat j : native_Int) = j := hjCast
      have hNCast : (Int.toNat n : native_Int) = n := hnCast
      have hJInt : j < Int.ofNat inner.length := by
        rw [← hjCast]
        exact Int.ofNat_lt.mpr hJWithin
      have hNLe : n ≤ Int.ofNat inner.length - j := by
        calc
          n = (N : native_Int) := hnCast.symm
          _ ≤ Int.ofNat (inner.length - J) :=
            Int.ofNat_le.mpr (by omega)
          _ = Int.ofNat inner.length - (J : native_Int) :=
            Int.ofNat_sub (Nat.le_of_lt hJWithin)
          _ = Int.ofNat inner.length - j := by rw [hjCast]
      unfold native_seq_extract
      rw [if_neg (by
        intro hGuard
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hGuard
        rcases hGuard with (hneg | hnLe) | hLenLe
        · exact (Int.not_lt_of_ge hj hneg)
        · exact (Int.not_le_of_gt hnPos hnLe)
        · exact (Int.not_le_of_gt hJInt hLenLe))]
      rw [Int.min_eq_left hNLe]
    have hRightEq : native_seq_extract xs (i + j) n =
        (xs.drop (I + J)).take N := by
      have hij : 0 ≤ i + j := Int.add_nonneg hi hj
      have hIJCast : ((I + J : Nat) : native_Int) = i + j := by
        calc
          ((I + J : Nat) : native_Int) =
              (I : native_Int) + (J : native_Int) :=
            (Int.ofNat_add_ofNat I J).symm
          _ = i + j := by rw [hiCast, hjCast]
      have hIJInt : i + j < Int.ofNat xs.length := by
        rw [← hIJCast]
        exact Int.ofNat_lt.mpr hIJWithin
      have hNLe : n ≤ Int.ofNat xs.length - (i + j) := by
        calc
          n = (N : native_Int) := hnCast.symm
          _ ≤ Int.ofNat (xs.length - (I + J)) :=
            Int.ofNat_le.mpr (by omega)
          _ = Int.ofNat xs.length - ((I + J : Nat) : native_Int) :=
            Int.ofNat_sub (Nat.le_of_lt hIJWithin)
          _ = Int.ofNat xs.length - (i + j) := by rw [hIJCast]
      unfold native_seq_extract
      rw [if_neg (by
        intro hGuard
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hGuard
        rcases hGuard with (hneg | hnLe) | hLenLe
        · exact (Int.not_lt_of_ge hij hneg)
        · exact (Int.not_le_of_gt hnPos hnLe)
        · exact (Int.not_le_of_gt hIJInt hLenLe))]
      rw [Int.min_eq_left hNLe]
      simp [I, J, N, Int.toNat_add hi hj]
    rw [hOuterEq, hRightEq, hInnerEq]
    have hInnerLenK : inner.length ≤ K := by
      rw [hInnerEq, List.length_take]
      exact Nat.min_le_left _ _
    exact take_drop_nested_of_bound xs I K J N
      (Nat.le_trans hBoundNat hInnerLenK)

private abbrev combine3NonnegPremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev combine3Inner (s n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m

private abbrev combine3BoundPremise
    (s n1 m1 n2 m2 : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.geq (Term.Apply Term.str_len
          (combine3Inner s n1 m1)))
        (Term.Apply (Term.Apply Term.plus n2)
          (Term.Apply (Term.Apply Term.plus m2) (Term.Numeral 0)))))
    (Term.Boolean true)

private abbrev combine3Lhs
    (s n1 m1 n2 m2 : Term) : Term :=
  combine3Inner (combine3Inner s n1 m1) n2 m2

private abbrev combine3Start (n1 n2 : Term) : Term :=
  Term.Apply (Term.Apply Term.plus n1)
    (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0))

private abbrev combine3Rhs
    (s n1 n2 m2 : Term) : Term :=
  combine3Inner s (combine3Start n1 n2) m2

private abbrev combine3Conclusion
    (s n1 m1 n2 m2 : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (combine3Lhs s n1 m1 n2 m2))
    (combine3Rhs s n1 n2 m2)

private theorem prog_str_substr_combine3_info
    (s n1 m1 n2 m2 P1 P2 P3 : Term)
    (hProg :
      __eo_prog_str_substr_combine3 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠ Term.Stuck) :
    P1 = combine3NonnegPremise n1 ∧
      P2 = combine3NonnegPremise n2 ∧
      P3 = combine3BoundPremise s n1 m1 n2 m2 ∧
      __eo_prog_str_substr_combine3 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        combine3Conclusion s n1 m1 n2 m2 := by
  unfold __eo_prog_str_substr_combine3 at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 heq3 =>
    cases heq1
    cases heq2
    cases heq3
    have hGuard := support_eo_requires_cond_eq_of_non_stuck hProg
    have h123456 := StrEqReplSupport.eo_and_eq_true_left hGuard
    have h7 := StrEqReplSupport.eo_and_eq_true_right hGuard
    have h12345 := StrEqReplSupport.eo_and_eq_true_left h123456
    have h6 := StrEqReplSupport.eo_and_eq_true_right h123456
    have h1234 := StrEqReplSupport.eo_and_eq_true_left h12345
    have h5 := StrEqReplSupport.eo_and_eq_true_right h12345
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
    have e6 := RuleProofs.eq_of_eo_eq_true _ _ h6
    have e7 := RuleProofs.eq_of_eo_eq_true _ _ h7
    subst_vars
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_combine3, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, combine3Conclusion, combine3Lhs,
      combine3Rhs, combine3Inner, combine3Start]

private theorem typed___eo_prog_str_substr_combine3_impl
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
      __eo_prog_str_substr_combine3 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        combine3Conclusion s n1 m1 n2 m2) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_combine3 s n1 m1 n2 m2
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) := by
  let inner := combine3Inner s n1 m1
  let lhs := combine3Lhs s n1 m1 n2 m2
  let rhs := combine3Rhs s n1 n2 m2
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
  have hStartTy : __smtx_typeof (__eo_to_smt (combine3Start n1 n2)) =
      SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.plus (__eo_to_smt n1)
          (SmtTerm.plus (__eo_to_smt n2) (SmtTerm.Numeral 0))) =
      SmtType.Int
    rw [typeof_plus_eq]
    simp [hN1SmtTy, hTailPlusTy, __smtx_typeof_arith_overload_op_2]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s)
          (__eo_to_smt (combine3Start n1 n2)) (__eo_to_smt m2)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hStartTy, hM2SmtTy, __smtx_typeof_str_substr]
  have hBool : RuleProofs.eo_has_bool_type
      (combine3Conclusion s n1 m1 n2 m2) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_substr_combine3_impl
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
    (hPrem1 : eo_interprets M (combine3NonnegPremise n1) true)
    (hPrem2 : eo_interprets M (combine3NonnegPremise n2) true)
    (hPrem3 : eo_interprets M
      (combine3BoundPremise s n1 m1 n2 m2) true)
    (hProgEq :
      __eo_prog_str_substr_combine3 s n1 m1 n2 m2
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        combine3Conclusion s n1 m1 n2 m2) :
    eo_interprets M
      (__eo_prog_str_substr_combine3 s n1 m1 n2 m2
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) true := by
  let inner := combine3Inner s n1 m1
  let lhs := combine3Lhs s n1 m1 n2 m2
  let rhs := combine3Rhs s n1 n2 m2
  have hBool : RuleProofs.eo_has_bool_type
      (combine3Conclusion s n1 m1 n2 m2) := by
    simpa [hProgEq] using typed___eo_prog_str_substr_combine3_impl
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
      (hPrem : eo_interprets M (combine3NonnegPremise t) true) :
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
  have hBound : n2i + m2i ≤
      Int.ofNat (native_seq_extract (native_unpack_seq ss) n1i m1i).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem3
    cases hPrem3 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_len
                  (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1)
                    (__eo_to_smt m1)))
                (SmtTerm.plus (__eo_to_smt n2)
                  (SmtTerm.plus (__eo_to_smt m2) (SmtTerm.Numeral 0))))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, smtx_eval_str_substr_term_eq,
          hSEval, hN1Eval, hM1Eval, smtx_eval_plus_term_eq, hN2Eval,
          smtx_eval_plus_term_eq, hM2Eval, smtx_eval_numeral_term_eq,
          smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq (native_zplus n2i
            (native_zplus m2i 0))
            (Int.ofNat
              (native_seq_extract (native_unpack_seq ss) n1i m1i).length) =
            true := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_str_substr,
            __smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_plus, __smtx_model_eval_eq, native_veq,
            native_seq_len, Smtm.native_unpack_pack_seq] using hEval
        simpa [SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus] using hLeBool
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
          (__eo_to_smt m2))
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_substr_term_eq,
      smtx_eval_str_substr_term_eq, smtx_eval_plus_term_eq,
      smtx_eval_plus_term_eq, hSEval, hN1Eval, hM1Eval, hN2Eval,
      hM2Eval, smtx_eval_numeral_term_eq]
    simp [__smtx_model_eval_str_substr, __smtx_model_eval_plus,
      native_zplus, SmtEval.native_zplus, hElem, elem_typeof_pack_seq,
      Smtm.native_unpack_pack_seq,
      native_seq_extract_nested_of_bound _ _ _ _ _ hN1Nonneg
        hN2Nonneg hBound]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_combine3_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_combine3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_combine3 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_combine3 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_combine3 args premises ≠
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
                                              (__eo_prog_str_substr_combine3
                                                a1 a2 a3 a4 a5
                                                (Proof.pf P1) (Proof.pf P2)
                                                (Proof.pf P3)) =
                                            Term.Bool at hResultTy
                                          have hRuleProg :
                                              __eo_prog_str_substr_combine3
                                                  a1 a2 a3 a4 a5
                                                  (Proof.pf P1) (Proof.pf P2)
                                                  (Proof.pf P3) ≠
                                                Term.Stuck :=
                                            term_ne_stuck_of_typeof_bool hResultTy
                                          rcases prog_str_substr_combine3_info
                                              a1 a2 a3 a4 a5 P1 P2 P3
                                              hRuleProg with
                                            ⟨hP1, hP2, hP3, hProgEq⟩
                                          rw [hProgEq] at hResultTy
                                          have hOpsNN :
                                              __eo_typeof
                                                  (combine3Lhs
                                                    a1 a2 a3 a4 a5) ≠
                                                  Term.Stuck ∧
                                                __eo_typeof
                                                  (combine3Rhs
                                                    a1 a2 a4 a5) ≠
                                                  Term.Stuck := by
                                            change __eo_typeof_eq
                                                (__eo_typeof
                                                  (combine3Lhs
                                                    a1 a2 a3 a4 a5))
                                                (__eo_typeof
                                                  (combine3Rhs
                                                    a1 a2 a4 a5)) =
                                              Term.Bool at hResultTy
                                            exact
                                              RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                                _ _ hResultTy
                                          have hLhsNN := hOpsNN.1
                                          change __eo_typeof_str_substr
                                              (__eo_typeof
                                                (combine3Inner a1 a2 a3))
                                              (__eo_typeof a4)
                                              (__eo_typeof a5) ≠
                                            Term.Stuck at hLhsNN
                                          rcases
                                              eo_typeof_str_substr_args_of_ne_stuck
                                                (__eo_typeof
                                                  (combine3Inner a1 a2 a3))
                                                (__eo_typeof a4)
                                                (__eo_typeof a5) hLhsNN with
                                            ⟨T, hInnerTy, hA4Ty, hA5Ty⟩
                                          have hInnerNN :
                                              __eo_typeof
                                                  (combine3Inner a1 a2 a3) ≠
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
                                                  (combine3Inner a1 a2 a3) =
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
                                                (combine3NonnegPremise a2)
                                                true := by
                                              simpa [hP1] using hPrem1Raw
                                            have hPrem2 : eo_interprets M
                                                (combine3NonnegPremise a4)
                                                true := by
                                              simpa [hP2] using hPrem2Raw
                                            have hPrem3 : eo_interprets M
                                                (combine3BoundPremise
                                                  a1 a2 a3 a4 a5) true := by
                                              simpa [hP3] using hPrem3Raw
                                            exact
                                              facts___eo_prog_str_substr_combine3_impl
                                                M hM a1 a2 a3 a4 a5
                                                P1 P2 P3 hA1Trans hA2Trans
                                                hA3Trans hA4Trans hA5Trans
                                                hA1Ty hA2Ty hA3Ty hA4Ty hA5Ty
                                                hPrem1 hPrem2 hPrem3 hProgEq
                                          · exact
                                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                _
                                                (typed___eo_prog_str_substr_combine3_impl
                                                  a1 a2 a3 a4 a5 P1 P2 P3
                                                  hA1Trans hA2Trans hA3Trans
                                                  hA4Trans hA5Trans hA1Ty
                                                  hA2Ty hA3Ty hA4Ty hA5Ty
                                                  hProgEq)
