module

public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrSubstrContainsSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem native_seq_extract_eq_drop_take_local
    (xs : List SmtValue) (i n : native_Int)
    (hi : 0 ≤ i) (hn : 0 < n) :
    native_seq_extract xs i n =
      (xs.drop (Int.toNat i)).take (Int.toNat n) := by
  unfold native_seq_extract
  by_cases hOob : Int.ofNat xs.length ≤ i
  · rw [if_pos (by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr hOob)]
    have hDrop : xs.drop (Int.toNat i) = [] := by
      apply List.drop_eq_nil_of_le
      apply Int.ofNat_le.mp
      rw [Int.toNat_of_nonneg hi]
      exact hOob
    rw [hDrop]
    simp
  · have hiLt : i < Int.ofNat xs.length := Int.lt_of_not_ge hOob
    rw [if_neg (by
      intro hGuard
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hGuard
      rcases hGuard with (hneg | hnLe) | hLenLe
      · exact (Int.not_lt_of_ge hi hneg)
      · exact (Int.not_le_of_gt hn hnLe)
      · exact (Int.not_le_of_gt hiLt hLenLe))]
    by_cases hnLe : n ≤ Int.ofNat xs.length - i
    · rw [Int.min_eq_left hnLe]
    · have hRemLt : Int.ofNat xs.length - i < n :=
        Int.lt_of_not_ge hnLe
      rw [Int.min_eq_right (Int.le_of_lt hRemLt)]
      apply List.take_eq_take_iff.mpr
      have hiNat : Int.toNat i ≤ xs.length := by
        apply Int.ofNat_le.mp
        rw [Int.toNat_of_nonneg hi]
        exact Int.le_of_lt hiLt
      have hDropLen : (xs.drop (Int.toNat i)).length =
          xs.length - Int.toNat i := List.length_drop
      have hRemCast :
          Int.toNat (Int.ofNat xs.length - i) =
            xs.length - Int.toNat i := by
        rw [← Int.toNat_of_nonneg hi]
        exact Int.toNat_sub xs.length (Int.toNat i)
      rw [hDropLen, hRemCast]
      have hRemNatLe : xs.length - Int.toNat i ≤ Int.toNat n := by
        apply Int.ofNat_le.mp
        rw [← hRemCast, Int.toNat_of_nonneg
          (Int.sub_nonneg.mpr (Int.le_of_lt hiLt)),
          Int.toNat_of_nonneg (Int.le_of_lt hn)]
        exact Int.le_of_lt hRemLt
      simp [hRemNatLe]

private theorem native_seq_extract_zero_eq_take_local
    (xs : List SmtValue) (n : native_Int) (hn : 0 ≤ n) :
    native_seq_extract xs 0 n = xs.take (Int.toNat n) := by
  by_cases hZero : n = 0
  · subst n
    simp [native_seq_extract]
  · have hPos : 0 < n := Int.lt_of_not_ge (by
      intro hLe
      exact hZero (Int.le_antisymm hLe hn))
    simpa using
      native_seq_extract_eq_drop_take_local xs 0 n (by decide) hPos

private theorem native_seq_extract_append_prefix
    (xs ys : List SmtValue) (n : native_Int)
    (hBound : Int.ofNat xs.length ≤ n) :
    native_seq_extract (xs ++ ys) 0 n =
      xs ++ native_seq_extract ys 0 (n - Int.ofNat xs.length) := by
  have hn : 0 ≤ n :=
    Int.le_trans (Int.natCast_nonneg xs.length) hBound
  have hRemaining : 0 ≤ n - Int.ofNat xs.length :=
    Int.sub_nonneg.mpr hBound
  rw [native_seq_extract_zero_eq_take_local (xs ++ ys) n hn]
  rw [native_seq_extract_zero_eq_take_local ys
    (n - Int.ofNat xs.length) hRemaining]
  have hBoundNat : xs.length ≤ Int.toNat n := by
    apply Int.ofNat_le.mp
    rw [Int.toNat_of_nonneg hn]
    exact hBound
  have hSubNat :
      Int.toNat (n - Int.ofNat xs.length) =
        Int.toNat n - xs.length := by
    rw [← Int.toNat_of_nonneg hn]
    exact Int.toNat_sub (Int.toNat n) xs.length
  rw [List.take_append, hSubNat,
    List.take_of_length_le hBoundNat]

private abbrev substrLenIncludePreBoundPremise (n s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq n) (Term.Apply Term.str_len s)))
    (Term.Boolean true)

private abbrev substrLenIncludePreConcat (s tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s) tail

private abbrev substrLenIncludePreTail (s2 s3 : Term) : Term :=
  substrLenIncludePreConcat s2 s3

private abbrev substrLenIncludePreNil (s1 : Term) : Term :=
  __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof s1)

private abbrev substrLenIncludePreOffset (n s1 : Term) : Term :=
  Term.Apply (Term.Apply Term.neg n) (Term.Apply Term.str_len s1)

private abbrev substrLenIncludePreSuffix
    (s1 s2 s3 n : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.str_substr
        (__str_nary_elim (substrLenIncludePreTail s2 s3)))
      (Term.Numeral 0))
    (substrLenIncludePreOffset n s1)

private abbrev substrLenIncludePreSuffixList
    (s1 s2 s3 n : Term) : Term :=
  substrLenIncludePreConcat
    (substrLenIncludePreSuffix s1 s2 s3 n)
    (substrLenIncludePreNil s1)

private abbrev substrLenIncludePreLhs
    (s1 s2 s3 n : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.str_substr
        (substrLenIncludePreConcat s1 (substrLenIncludePreTail s2 s3)))
      (Term.Numeral 0)) n

private abbrev substrLenIncludePreRhs
    (s1 s2 s3 n : Term) : Term :=
  substrLenIncludePreConcat s1
    (substrLenIncludePreSuffixList s1 s2 s3 n)

private abbrev substrLenIncludePreConclusion
    (s1 s2 s3 n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrLenIncludePreLhs s1 s2 s3 n))
    (substrLenIncludePreRhs s1 s2 s3 n)

private theorem prog_str_substr_len_include_pre_info
    (s1 s2 s3 n P : Term)
    (hProg :
      __eo_prog_str_substr_len_include_pre s1 s2 s3 n (Proof.pf P) ≠
        Term.Stuck) :
    ∃ n0 s0,
      P = substrLenIncludePreBoundPremise n0 s0 ∧
      n0 = n ∧ s0 = s1 ∧
      __str_nary_elim (substrLenIncludePreTail s2 s3) ≠ Term.Stuck ∧
      substrLenIncludePreNil s1 ≠ Term.Stuck ∧
      __eo_prog_str_substr_len_include_pre s1 s2 s3 n (Proof.pf P) =
        substrLenIncludePreConclusion s1 s2 s3 n := by
  unfold __eo_prog_str_substr_len_include_pre at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hN, hS⟩
    subst_vars
    have hBodyNe := eo_requires_result_ne_stuck_of_ne_stuck
      _ _ _ hProg
    have hRhsNe := CnfSupport.mk_apply_ne_stuck_right hBodyNe
    have hSuffixListNe := CnfSupport.mk_apply_ne_stuck_right hRhsNe
    have hSuffixListFnNe :=
      CnfSupport.mk_apply_ne_stuck_left hSuffixListNe
    have hSuffixNe :=
      CnfSupport.mk_apply_ne_stuck_right hSuffixListFnNe
    have hNilNe := CnfSupport.mk_apply_ne_stuck_right hSuffixListNe
    have hSuffixFn2Ne := CnfSupport.mk_apply_ne_stuck_left hSuffixNe
    have hSuffixFn1Ne := CnfSupport.mk_apply_ne_stuck_left hSuffixFn2Ne
    have hElimNe := CnfSupport.mk_apply_ne_stuck_right hSuffixFn1Ne
    refine ⟨_, _, rfl, rfl, rfl, hElimNe, hNilNe, ?_⟩
    simp_all [__eo_prog_str_substr_len_include_pre, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, substrLenIncludePreConclusion,
      substrLenIncludePreLhs, substrLenIncludePreRhs,
      substrLenIncludePreConcat, substrLenIncludePreTail,
      substrLenIncludePreOffset, substrLenIncludePreSuffix,
      substrLenIncludePreSuffixList, substrLenIncludePreNil,
      __eo_mk_apply, __eo_list_singleton_elim]

private theorem smtx_eval_neg_term_eq_local
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem typed___eo_prog_str_substr_len_include_pre_impl
    (s1 s2 s3 n P : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq T)
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq T)
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hElim :
      __str_nary_elim (substrLenIncludePreTail s2 s3) ≠ Term.Stuck)
    (hNil : substrLenIncludePreNil s1 ≠ Term.Stuck)
    (hProgEq :
      __eo_prog_str_substr_len_include_pre s1 s2 s3 n (Proof.pf P) =
        substrLenIncludePreConclusion s1 s2 s3 n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_len_include_pre s1 s2 s3 n (Proof.pf P)) := by
  let tail := substrLenIncludePreTail s2 s3
  let source := substrLenIncludePreConcat s1 tail
  let suffix := substrLenIncludePreSuffix s1 s2 s3 n
  let suffixList := substrLenIncludePreSuffixList s1 s2 s3 n
  let lhs := substrLenIncludePreLhs s1 s2 s3 n
  let rhs := substrLenIncludePreRhs s1 s2 s3 n
  have hS1SmtTy := smtx_typeof_of_eo_seq s1 T hS1Trans hS1Ty
  have hS2SmtTy := smtx_typeof_of_eo_seq s2 T hS2Trans hS2Ty
  have hS3SmtTy := smtx_typeof_of_eo_seq s3 T hS3Trans hS3Ty
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS2SmtTy, hS3SmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hSourceTy :
      __smtx_typeof (__eo_to_smt source) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS1SmtTy, hTailTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim tail)) =
        SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck tail
      (__eo_to_smt_type T) hTailTy hElim
  have hLenTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt s1)) =
        SmtType.Int := by
    rw [typeof_str_len_eq]
    simp [hS1SmtTy, __smtx_typeof_seq_op_1_ret]
  have hOffsetTy :
      __smtx_typeof
          (SmtTerm.neg (__eo_to_smt n)
            (SmtTerm.str_len (__eo_to_smt s1))) = SmtType.Int := by
    rw [typeof_neg_eq]
    simp [hNSmtTy, hLenTy, __smtx_typeof_arith_overload_op_2]
  have hZeroTy :
      __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_def]
  have hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr
          (__eo_to_smt (__str_nary_elim tail))
          (SmtTerm.Numeral 0)
          (SmtTerm.neg (__eo_to_smt n)
            (SmtTerm.str_len (__eo_to_smt s1)))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hElimTy, hZeroTy, hOffsetTy, __smtx_typeof_str_substr]
  have hNilTy :
      __smtx_typeof (__eo_to_smt (substrLenIncludePreNil s1)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    have hS1NN :
        __smtx_typeof (__eo_to_smt s1) ≠ SmtType.None := by
      rw [hS1SmtTy]
      exact seq_ne_none (__eo_to_smt_type T)
    have hTypeMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation s1 hS1NN
    have hType :
        __eo_to_smt_type (__eo_typeof s1) =
          SmtType.Seq (__eo_to_smt_type T) := by
      rw [← hTypeMatch, hS1SmtTy]
    rw [substrLenIncludePreNil,
      strConcat_nil_eq_seq_empty_of_type hType]
    exact smt_typeof_seq_empty_typeof s1 (__eo_to_smt_type T) hS1SmtTy
      (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
        s1 (__eo_to_smt_type T) hS1SmtTy
        (smt_seq_component_wf_of_non_none_type
          (__eo_to_smt s1) (__eo_to_smt_type T) hS1SmtTy).1
        (smt_seq_component_wf_of_non_none_type
          (__eo_to_smt s1) (__eo_to_smt_type T) hS1SmtTy).2)
  have hSuffixListTy :
      __smtx_typeof (__eo_to_smt suffixList) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt suffix)
          (__eo_to_smt (substrLenIncludePreNil s1))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hSuffixTy, hNilTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt source)
          (SmtTerm.Numeral 0) (__eo_to_smt n)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSourceTy, hZeroTy, hNSmtTy, __smtx_typeof_str_substr]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s1)
          (__eo_to_smt suffixList)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS1SmtTy, hSuffixListTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (substrLenIncludePreConclusion s1 s2 s3 n) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_substr_len_include_pre_impl
    (M : SmtModel) (hModel : model_wf M)
    (s1 s2 s3 n P : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq T)
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq T)
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPrem : eo_interprets M (substrLenIncludePreBoundPremise n s1) true)
    (hElim :
      __str_nary_elim (substrLenIncludePreTail s2 s3) ≠ Term.Stuck)
    (hNil : substrLenIncludePreNil s1 ≠ Term.Stuck)
    (hProgEq :
      __eo_prog_str_substr_len_include_pre s1 s2 s3 n (Proof.pf P) =
        substrLenIncludePreConclusion s1 s2 s3 n) :
    eo_interprets M
      (__eo_prog_str_substr_len_include_pre s1 s2 s3 n (Proof.pf P)) true := by
  let tail := substrLenIncludePreTail s2 s3
  let lhs := substrLenIncludePreLhs s1 s2 s3 n
  let rhs := substrLenIncludePreRhs s1 s2 s3 n
  have hBool : RuleProofs.eo_has_bool_type
      (substrLenIncludePreConclusion s1 s2 s3 n) := by
    simpa [hProgEq] using
      typed___eo_prog_str_substr_len_include_pre_impl
        s1 s2 s3 n P hS1Trans hS2Trans hS3Trans hNTrans
        hS1Ty hS2Ty hS3Ty hNTy hElim hNil hProgEq
  have hS1SmtTy := smtx_typeof_of_eo_seq s1 T hS1Trans hS1Ty
  have hS2SmtTy := smtx_typeof_of_eo_seq s2 T hS2Trans hS2Ty
  have hS3SmtTy := smtx_typeof_of_eo_seq s3 T hS3Trans hS3Ty
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS2SmtTy, hS3SmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hS1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel
        (__eo_to_smt s1) (by
          unfold term_has_non_none_type
          rw [hS1SmtTy]
          simp)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel
        (__eo_to_smt s2) (by
          unfold term_has_non_none_type
          rw [hS2SmtTy]
          simp)
  have hS3EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s3)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS3SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel
        (__eo_to_smt s3) (by
          unfold term_has_non_none_type
          rw [hS3SmtTy]
          simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel
        (__eo_to_smt n) (by
          unfold term_has_non_none_type
          rw [hNSmtTy]
          simp)
  rcases seq_value_canonical hS1EvalTy with ⟨ss1, hS1Eval⟩
  rcases seq_value_canonical hS2EvalTy with ⟨ss2, hS2Eval⟩
  rcases seq_value_canonical hS3EvalTy with ⟨ss3, hS3Eval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hS1SeqTy : __smtx_typeof_seq_value ss1 =
      SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS1Eval, __smtx_typeof_seq_value, __smtx_typeof_value] using hS1EvalTy
  have hS2SeqTy : __smtx_typeof_seq_value ss2 =
      SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS2Eval, __smtx_typeof_seq_value, __smtx_typeof_value] using hS2EvalTy
  have hS1Elem :
      __smtx_elem_typeof_seq_value ss1 = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hS1SeqTy
  have hS2Elem :
      __smtx_elem_typeof_seq_value ss2 = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hS2SeqTy
  let tailSeq := native_pack_seq (__smtx_elem_typeof_seq_value ss2)
    (native_unpack_seq ss2 ++ native_unpack_seq ss3)
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.Seq tailSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
      SmtValue.Seq tailSeq
    rw [smtx_eval_str_concat_term_eq, hS2Eval, hS3Eval]
    simp [tailSeq, __smtx_model_eval_str_concat, native_seq_concat]
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim tail)) =
        SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck tail
      (__eo_to_smt_type T) hTailTy hElim
  have hElimEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tail))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hElimTy] using
      smt_model_eval_preserves_type_of_non_none M hModel
        (__eo_to_smt (__str_nary_elim tail)) (by
          unfold term_has_non_none_type
          rw [hElimTy]
          simp)
  rcases seq_value_canonical hElimEvalTy with ⟨elimSeq, hElimEval⟩
  have hElimRel := smt_value_rel_str_nary_elim M hModel tail
    (__eo_to_smt_type T) hTailTy hElim
  have hElimSeqEq : elimSeq = tailSeq := by
    rw [hElimEval, hTailEval] at hElimRel
    have hValEq : SmtValue.Seq elimSeq = SmtValue.Seq tailSeq :=
      (RuleProofs.smt_value_rel_iff_eq (SmtValue.Seq elimSeq)
        (SmtValue.Seq tailSeq) (by
          rintro ⟨r1, r2, hBad, _⟩
          cases hBad)).1 hElimRel
    cases hValEq
    rfl
  have hNilEq :
      substrLenIncludePreNil s1 =
        __seq_empty (__eo_typeof s1) :=
    strConcat_nil_eq_seq_empty_of_ne_stuck (__eo_typeof s1) hNil
  have hNilEval :
      __smtx_model_eval M
          (__eo_to_smt (substrLenIncludePreNil s1)) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) := by
    rw [hNilEq]
    exact eval_seq_empty_typeof M s1 (__eo_to_smt_type T) hS1SmtTy
  have hBound : Int.ofNat (native_unpack_seq ss1).length ≤ ni := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt s1)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq, hNEval,
          smtx_eval_str_len_term_eq, hS1Eval,
          smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq (Int.ofNat (native_unpack_seq ss1).length) ni =
              true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr
          (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail))
          (SmtTerm.Numeral 0) (__eo_to_smt n)) =
      __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s1)
          (SmtTerm.str_concat
            (SmtTerm.str_substr
              (__eo_to_smt (__str_nary_elim tail))
              (SmtTerm.Numeral 0)
              (SmtTerm.neg (__eo_to_smt n)
                (SmtTerm.str_len (__eo_to_smt s1))))
            (__eo_to_smt (substrLenIncludePreNil s1))))
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_concat_term_eq,
      smtx_eval_str_concat_term_eq, smtx_eval_str_concat_term_eq,
      smtx_eval_str_substr_term_eq, smtx_eval_neg_term_eq_local,
      smtx_eval_str_len_term_eq, hS1Eval, hTailEval, hElimEval,
      hNilEval, hNEval, smtx_eval_numeral_term_eq]
    rw [hElimSeqEq]
    simp [__smtx_model_eval_str_substr, __smtx_model_eval_str_concat,
      __smtx_model_eval_str_len, __smtx_model_eval__,
      native_seq_concat, native_seq_len, native_zplus, native_zneg,
      SmtEval.native_zplus, Int.sub_eq_add_neg,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
      native_unpack_seq, hS1Elem, hS2Elem, tailSeq,
      native_seq_extract_append_prefix _ _ _ hBound]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_len_include_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_len_include_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_len_include_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_len_include_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_len_include_pre args premises ≠
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
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | nil => exact absurd rfl hProg
                      | cons p premises =>
                          cases premises with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
                              let P := __eo_state_proven_nth s p
                              have hA1Trans :
                                  RuleProofs.eo_has_smt_translation a1 := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.1
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
                              change __eo_typeof
                                  (__eo_prog_str_substr_len_include_pre
                                    a1 a2 a3 a4 (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_substr_len_include_pre
                                      a1 a2 a3 a4 (Proof.pf P) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_substr_len_include_pre_info
                                  a1 a2 a3 a4 P hRuleProg with
                                ⟨n0, s0, hP, hN, hS, hElim, hNil, hProgEq⟩
                              subst n0
                              subst s0
                              rw [hProgEq] at hResultTy
                              have hOpsNN :
                                  __eo_typeof
                                      (substrLenIncludePreLhs
                                        a1 a2 a3 a4) ≠ Term.Stuck ∧
                                    __eo_typeof
                                      (substrLenIncludePreRhs
                                        a1 a2 a3 a4) ≠ Term.Stuck := by
                                change __eo_typeof_eq
                                    (__eo_typeof
                                      (substrLenIncludePreLhs
                                        a1 a2 a3 a4))
                                    (__eo_typeof
                                      (substrLenIncludePreRhs
                                        a1 a2 a3 a4)) =
                                  Term.Bool at hResultTy
                                exact
                                  RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                    _ _ hResultTy
                              have hLhsNN := hOpsNN.1
                              change __eo_typeof_str_substr
                                  (__eo_typeof
                                    (substrLenIncludePreConcat a1
                                      (substrLenIncludePreTail a2 a3)))
                                  Term.Int (__eo_typeof a4) ≠
                                Term.Stuck at hLhsNN
                              rcases eo_typeof_str_substr_args_of_ne_stuck
                                  (__eo_typeof
                                    (substrLenIncludePreConcat a1
                                      (substrLenIncludePreTail a2 a3)))
                                  Term.Int (__eo_typeof a4) hLhsNN with
                                ⟨T, hSourceTy, _hZeroTy, hA4Ty⟩
                              have hSourceNN :
                                  __eo_typeof
                                      (substrLenIncludePreConcat a1
                                        (substrLenIncludePreTail a2 a3)) ≠
                                    Term.Stuck := by
                                rw [hSourceTy]
                                simp
                              change __eo_typeof_str_concat
                                  (__eo_typeof a1)
                                  (__eo_typeof
                                    (substrLenIncludePreTail a2 a3)) ≠
                                Term.Stuck at hSourceNN
                              rcases eo_typeof_str_concat_args_of_ne_stuck
                                  (__eo_typeof a1)
                                  (__eo_typeof
                                    (substrLenIncludePreTail a2 a3))
                                  hSourceNN with
                                ⟨U, hA1Ty, hTailTy⟩
                              have hSourceCalc :
                                  __eo_typeof
                                      (substrLenIncludePreConcat a1
                                        (substrLenIncludePreTail a2 a3)) =
                                    Term.Apply Term.Seq U := by
                                change __eo_typeof_str_concat
                                    (__eo_typeof a1)
                                    (__eo_typeof
                                      (substrLenIncludePreTail a2 a3)) =
                                  Term.Apply Term.Seq U
                                rw [hA1Ty, hTailTy]
                                exact
                                  eo_typeof_str_concat_result_of_seq_args
                                    U (by
                                      simpa [hA1Ty, hTailTy] using hSourceNN)
                              rw [hSourceTy] at hSourceCalc
                              cases hSourceCalc
                              have hTailNN :
                                  __eo_typeof
                                      (substrLenIncludePreTail a2 a3) ≠
                                    Term.Stuck := by
                                rw [hTailTy]
                                simp
                              change __eo_typeof_str_concat
                                  (__eo_typeof a2) (__eo_typeof a3) ≠
                                Term.Stuck at hTailNN
                              rcases eo_typeof_str_concat_args_of_ne_stuck
                                  (__eo_typeof a2) (__eo_typeof a3)
                                  hTailNN with
                                ⟨V, hA2Ty, hA3Ty⟩
                              have hTailCalc :
                                  __eo_typeof
                                      (substrLenIncludePreTail a2 a3) =
                                    Term.Apply Term.Seq V := by
                                change __eo_typeof_str_concat
                                    (__eo_typeof a2) (__eo_typeof a3) =
                                  Term.Apply Term.Seq V
                                rw [hA2Ty, hA3Ty]
                                exact
                                  eo_typeof_str_concat_result_of_seq_args
                                    V (by
                                      simpa [hA2Ty, hA3Ty] using hTailNN)
                              rw [hTailTy] at hTailCalc
                              cases hTailCalc
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem : eo_interprets M
                                    (substrLenIncludePreBoundPremise a4 a1)
                                    true := by
                                  simpa [hP] using hPremRaw
                                exact
                                  facts___eo_prog_str_substr_len_include_pre_impl
                                    M hM a1 a2 a3 a4 P
                                    hA1Trans hA2Trans hA3Trans hA4Trans
                                    hA1Ty hA2Ty hA3Ty hA4Ty hPrem
                                    hElim hNil hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_substr_len_include_pre_impl
                                      a1 a2 a3 a4 P
                                      hA1Trans hA2Trans hA3Trans hA4Trans
                                      hA1Ty hA2Ty hA3Ty hA4Ty
                                      hElim hNil hProgEq)
