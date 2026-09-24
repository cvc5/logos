module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev sdLen (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) s

private abbrev sdSubstr (s i n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) i) n

private abbrev sdMinus (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y

private abbrev sdPurify (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_purify) x

private abbrev sdConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y

private abbrev sdEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev sdAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

private abbrev stringDecomposePrefix (s n : Term) : Term :=
  sdPurify (sdSubstr s (Term.Numeral 0) n)

private abbrev stringDecomposeRemainderLen (s n : Term) : Term :=
  sdMinus (sdLen s) n

private abbrev stringDecomposeSuffix (s n : Term) : Term :=
  sdPurify (sdSubstr s n (stringDecomposeRemainderLen s n))

private abbrev stringDecomposeShortPrefix (s n : Term) : Term :=
  sdPurify (sdSubstr s (Term.Numeral 0) (stringDecomposeRemainderLen s n))

private abbrev stringDecomposeLast (s n : Term) : Term :=
  sdPurify (sdSubstr s (stringDecomposeRemainderLen s n) n)

private abbrev stringDecomposeFalseBody (s n : Term) : Term :=
  let pre := stringDecomposePrefix s n
  let suf := stringDecomposeSuffix s n
  sdAnd
    (sdEq s
      (sdConcat pre
        (sdConcat suf (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)))))
    (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true))

private abbrev stringDecomposeTrueBody (s n : Term) : Term :=
  let pre := stringDecomposeShortPrefix s n
  let last := stringDecomposeLast s n
  sdAnd
    (sdEq s
      (sdConcat pre
        (sdConcat last (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)))))
    (sdAnd (sdEq (sdLen last) n) (Term.Boolean true))

private abbrev stringDecomposeFalseGeneratedBody (s n : Term) : Term :=
  let pre := stringDecomposePrefix s n
  let suf := stringDecomposeSuffix s n
  let eqHead := Term.Apply (Term.UOp UserOp.eq) s
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and)
      (__eo_mk_apply eqHead
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) pre)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suf)
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))))))
    (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true))

private abbrev stringDecomposeTrueGeneratedBody (s n : Term) : Term :=
  let pre := stringDecomposeShortPrefix s n
  let last := stringDecomposeLast s n
  let eqHead := Term.Apply (Term.UOp UserOp.eq) s
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and)
      (__eo_mk_apply eqHead
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) pre)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) last)
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))))))
    (sdAnd (sdEq (sdLen last) n) (Term.Boolean true))

private theorem smtx_typeof_str_len_seq
    (s : SmtTerm) (T : SmtType)
    (hs : __smtx_typeof s = SmtType.Seq T) :
    __smtx_typeof (SmtTerm.str_len s) = SmtType.Int := by
  rw [typeof_str_len_eq]
  simp [hs, __smtx_typeof_seq_op_1_ret]

private theorem smtx_typeof_str_substr_seq
    (s i n : SmtTerm) (T : SmtType)
    (hs : __smtx_typeof s = SmtType.Seq T)
    (hi : __smtx_typeof i = SmtType.Int)
    (hn : __smtx_typeof n = SmtType.Int) :
    __smtx_typeof (SmtTerm.str_substr s i n) = SmtType.Seq T := by
  rw [typeof_str_substr_eq]
  simp [__smtx_typeof_str_substr, hs, hi, hn]

private theorem smtx_typeof_str_concat_seq
    (x y : SmtTerm) (T : SmtType)
    (hx : __smtx_typeof x = SmtType.Seq T)
    (hy : __smtx_typeof y = SmtType.Seq T) :
    __smtx_typeof (SmtTerm.str_concat x y) = SmtType.Seq T := by
  rw [typeof_str_concat_eq]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hx, hy]

private theorem smtx_typeof_neg_int
    (x y : SmtTerm)
    (hx : __smtx_typeof x = SmtType.Int)
    (hy : __smtx_typeof y = SmtType.Int) :
    __smtx_typeof (SmtTerm.neg x y) = SmtType.Int := by
  rw [typeof_neg_eq]
  simp [__smtx_typeof_arith_overload_op_2, hx, hy]

private theorem smt_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
    have hGood :=
      smt_term_result_seq_components_wf_of_non_none (__eo_to_smt x) hTrans
    simp only [hxTy] at hGood
    exact hGood
  by_cases hSpecial :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · rw [hSpecial]
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) = SmtType.Seq T
    rw [__smtx_typeof.eq_4]
    rw [hSpecial] at hA
    simp [TranslationProofs.eo_to_smt_type_seq,
      TranslationProofs.eo_to_smt_type_char] at hA
    exact hA
  · by_cases hStuck : __eo_typeof x = Term.Stuck
    · rw [hStuck] at hA
      simp [__eo_to_smt_type] at hA
    · have hDefault :
          __seq_empty (__eo_typeof x) = Term.UOp1 UserOp1.seq_empty (__eo_typeof x) := by
        cases hTy : __eo_typeof x <;>
          simp [__seq_empty, hTy] at hStuck hSpecial ⊢
        case Apply f a =>
          cases f <;> simp at hSpecial ⊢
          case UOp op =>
            cases op <;> simp at hSpecial ⊢
            case Seq =>
              cases a <;> simp at hSpecial ⊢
              case UOp op' =>
                cases op' <;> simp at hSpecial ⊢
      rw [hDefault]
      change
        __smtx_typeof (__eo_to_smt_seq_empty
          (__eo_to_smt_type (__eo_typeof x))) = SmtType.Seq T
      rw [hA]
      change __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T
      simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hSeqWF]

private theorem smt_typeof_nil_str_concat_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact smt_typeof_seq_empty_typeof_of_smt_type_seq x T hxTy

private theorem nil_str_concat_typeof_ne_stuck_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x) ≠ Term.Stuck := by
  intro h
  have hNilTy :=
    smt_typeof_nil_str_concat_typeof_of_smt_type_seq x T hxTy
  rw [h] at hNilTy
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hNilTy
  rw [TranslationProofs.smtx_typeof_none] at hNilTy
  cases hNilTy

private theorem native_seq_extract_zero_nat
    (xs : List SmtValue) (n : Nat) (hle : n <= xs.length) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  unfold native_seq_extract
  by_cases hn : n = 0
  · subst n
    simp
  · have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : Int) < Int.ofNat n := Int.ofNat_lt.mpr hnPosNat
    have hxsPosNat : 0 < xs.length := Nat.lt_of_lt_of_le hnPosNat hle
    have hxsNe : xs ≠ [] := by
      intro h
      subst xs
      simp at hxsPosNat
    have hmin : min (Int.ofNat n) (Int.ofNat xs.length) = Int.ofNat n :=
      Int.min_eq_left (Int.ofNat_le.mpr hle)
    have hminToNat :
        (min (Int.ofNat n) (Int.ofNat xs.length)).toNat = n := by
      rw [hmin]
      simp
    have hminNat : min n xs.length = n := Nat.min_eq_left hle
    simp [hn, hxsNe]
    change
      min ((min (Int.ofNat n) (Int.ofNat xs.length)).toNat) xs.length =
        min n xs.length
    rw [hminToNat, hminNat]

private theorem native_seq_extract_to_end_nat
    (xs : List SmtValue) (i : Nat) (hle : i <= xs.length) :
    native_seq_extract xs (Int.ofNat i) (Int.ofNat (xs.length - i)) =
      xs.drop i := by
  unfold native_seq_extract
  by_cases hend : xs.length - i = 0
  · have hLenLe : xs.length <= i := by omega
    have hcast : (Int.ofNat i >= Int.ofNat xs.length) = true := by
      simp [hLenLe]
    simp [hend,List.drop_eq_nil_of_le hLenLe]
  · have htailPosNat : 0 < xs.length - i := Nat.pos_of_ne_zero hend
    have hiltNat : i < xs.length := by omega
    have htailPos : (0 : Int) < Int.ofNat (xs.length - i) :=
      Int.ofNat_lt.mpr htailPosNat
    have hilt : Int.ofNat i < Int.ofNat xs.length :=
      Int.ofNat_lt.mpr hiltNat
    have hcastSub : Int.ofNat (xs.length - i) = Int.ofNat xs.length - Int.ofNat i :=
      Int.ofNat_sub hle
    have hmin :
        min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i) =
          Int.ofNat (xs.length - i) := by
      rw [← hcastSub]
      exact Int.min_eq_left (Int.le_refl _)
    have htake :
        (xs.drop i).take (xs.length - i) = xs.drop i := by
      apply List.take_of_length_le
      rw [List.length_drop]
      exact Nat.le_refl _
    have hLenNotLe : ¬ xs.length <= i := Nat.not_le_of_gt hiltNat
    have hiNonneg : ¬ ((i : native_Int) < (0 : native_Int)) := by
      exact Int.not_lt_of_ge (Int.natCast_nonneg i)
    have hminToNat :
        (min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i)).toNat =
          xs.length - i := by
      rw [hmin]
      simp
    simp [hend, hLenNotLe]
    rw [if_neg hiNonneg]
    change
      List.take
          ((min (Int.ofNat (xs.length - i))
              (Int.ofNat xs.length - Int.ofNat i)).toNat)
          (List.drop i xs) =
        List.drop i xs
    rw [hminToNat]
    exact htake

private theorem native_seq_extract_split_front
    (xs : List SmtValue) (n : native_Int)
    (h0 : 0 <= n) (hle : n <= Int.ofNat xs.length) :
    native_seq_extract xs 0 n ++
        native_seq_extract xs n (Int.ofNat xs.length - n) =
      xs := by
  let N := n.toNat
  have hNle : N <= xs.length := by
    dsimp [N]
    rw [Int.toNat_le]
    exact hle
  have hnCast : Int.ofNat N = n := by
    dsimp [N]
    exact Int.toNat_of_nonneg h0
  have hlenSub :
      Int.ofNat xs.length - Int.ofNat N = Int.ofNat (xs.length - N) :=
    (Int.ofNat_sub hNle).symm
  rw [← hnCast, hlenSub]
  rw [native_seq_extract_zero_nat xs N hNle]
  rw [native_seq_extract_to_end_nat xs N hNle]
  exact List.take_append_drop N xs

private theorem native_seq_extract_prefix_length
    (xs : List SmtValue) (n : native_Int)
    (h0 : 0 <= n) (hle : n <= Int.ofNat xs.length) :
    Int.ofNat (native_seq_extract xs 0 n).length = n := by
  let N := n.toNat
  have hNle : N <= xs.length := by
    dsimp [N]
    rw [Int.toNat_le]
    exact hle
  have hnCast : Int.ofNat N = n := by
    dsimp [N]
    exact Int.toNat_of_nonneg h0
  rw [← hnCast]
  rw [native_seq_extract_zero_nat xs N hNle]
  rw [List.length_take, Nat.min_eq_left hNle]

private theorem native_seq_extract_split_back
    (xs : List SmtValue) (n : native_Int)
    (h0 : 0 <= n) (hle : n <= Int.ofNat xs.length) :
    native_seq_extract xs 0 (Int.ofNat xs.length - n) ++
        native_seq_extract xs (Int.ofNat xs.length - n) n =
      xs := by
  let N := n.toNat
  have hNle : N <= xs.length := by
    dsimp [N]
    rw [Int.toNat_le]
    exact hle
  have hnCast : Int.ofNat N = n := by
    dsimp [N]
    exact Int.toNat_of_nonneg h0
  have hremCast :
      Int.ofNat (xs.length - N) = Int.ofNat xs.length - n := by
    rw [← hnCast]
    exact Int.ofNat_sub hNle
  rw [← hremCast, ← hnCast]
  have hRemLe : xs.length - N <= xs.length := Nat.sub_le _ _
  rw [native_seq_extract_zero_nat xs (xs.length - N) hRemLe]
  have hTailLen : xs.length - (xs.length - N) = N := Nat.sub_sub_self hNle
  have hTailCast :
      Int.ofNat N = Int.ofNat (xs.length - (xs.length - N)) := by
    rw [hTailLen]
  rw [hTailCast]
  rw [native_seq_extract_to_end_nat xs (xs.length - N) hRemLe]
  exact List.take_append_drop (xs.length - N) xs

private theorem native_seq_extract_last_length
    (xs : List SmtValue) (n : native_Int)
    (h0 : 0 <= n) (hle : n <= Int.ofNat xs.length) :
    Int.ofNat
        (native_seq_extract xs (Int.ofNat xs.length - n) n).length =
      n := by
  let N := n.toNat
  have hNle : N <= xs.length := by
    dsimp [N]
    rw [Int.toNat_le]
    exact hle
  have hnCast : Int.ofNat N = n := by
    dsimp [N]
    exact Int.toNat_of_nonneg h0
  have hremCast :
      Int.ofNat (xs.length - N) = Int.ofNat xs.length - n := by
    rw [← hnCast]
    exact Int.ofNat_sub hNle
  rw [← hremCast, ← hnCast]
  have hRemLe : xs.length - N <= xs.length := Nat.sub_le _ _
  have hTailLen : xs.length - (xs.length - N) = N := Nat.sub_sub_self hNle
  have hTailCast :
      Int.ofNat N = Int.ofNat (xs.length - (xs.length - N)) := by
    rw [hTailLen]
  rw [hTailCast]
  rw [native_seq_extract_to_end_nat xs (xs.length - N) hRemLe]
  rw [List.length_drop]

private theorem eval_nil_str_concat_typeof_of_smt_type_seq
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact eval_seq_empty_typeof M x T hxTy

private theorem smt_typeof_int_of_geq_zero_bool (n : Term)
    (h :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  unfold RuleProofs.eo_has_bool_type at h
  change
    __smtx_typeof
        (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0)) =
      SmtType.Bool at h
  have hNN :
      term_has_non_none_type
        (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0)) := by
    unfold term_has_non_none_type
    rw [h]
    simp
  rcases arith_binop_ret_bool_args_of_non_none
      (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (SmtTerm.Numeral 0)) hNN with
    hArgs | hArgs
  · exact hArgs.1
  · have hNum : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
      simp [__smtx_typeof]
    rw [hNum] at hArgs
    cases hArgs.2

private theorem smt_typeof_seq_of_geq_str_len_bool (s n : Term)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (h :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (sdLen s)) n)) :
    ∃ T, __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
  unfold RuleProofs.eo_has_bool_type at h
  change
    __smtx_typeof
        (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)) =
      SmtType.Bool at h
  have hNN :
      term_has_non_none_type
        (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    rw [h]
    simp
  rcases arith_binop_ret_bool_args_of_non_none
      (op := SmtTerm.geq)
      (typeof_geq_eq (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)) hNN with
    hArgs | hArgs
  · have hLenNN : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt s)) := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt s)) hLenNN
  · rw [hN] at hArgs
    cases hArgs.2

private theorem eval_geq_zero_true_of_premise
    (M : SmtModel) (n : Term) (ni : native_Int)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral ni)
    (hPrem :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))
        true) :
    0 <= ni := by
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))
        true).mp hPrem with
    | intro_true _ hEval => exact hEval
  change
    __smtx_model_eval M
        (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0)) =
      SmtValue.Boolean true at hEval
  simp [__smtx_model_eval, hnEval, __smtx_model_eval_geq,
    __smtx_model_eval_leq, native_zleq] at hEval
  exact hEval

private theorem eval_len_geq_true_of_premise
    (M : SmtModel) (s n : Term) (ss : SmtSeq) (ni : native_Int)
    (hsEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral ni)
    (hPrem :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (sdLen s)) n)
        true) :
    ni <= Int.ofNat (native_unpack_seq ss).length := by
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (sdLen s)) n)) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (sdLen s)) n)
        true).mp hPrem with
    | intro_true _ hEval => exact hEval
  change
    __smtx_model_eval M
        (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)) =
      SmtValue.Boolean true at hEval
  simp [__smtx_model_eval, hsEval, hnEval, __smtx_model_eval_str_len,
    __smtx_model_eval_geq, __smtx_model_eval_leq, native_seq_len,
    native_zleq] at hEval
  exact hEval

private theorem smt_typeof_string_decompose_prefix
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (stringDecomposePrefix s n)) = SmtType.Seq T := by
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0) (__eo_to_smt n))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt s) (SmtTerm.Numeral 0)
      (__eo_to_smt n) T hS (by simp [__smtx_typeof]) hN

private theorem smt_typeof_string_decompose_remainder_len
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (stringDecomposeRemainderLen s n)) =
      SmtType.Int := by
  change
    __smtx_typeof
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)) =
      SmtType.Int
  exact smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)
    (smtx_typeof_str_len_seq (__eo_to_smt s) T hS) hN

private theorem smt_typeof_string_decompose_suffix
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (stringDecomposeSuffix s n)) = SmtType.Seq T := by
  have hRem := smt_typeof_string_decompose_remainder_len s n T hS hN
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt (stringDecomposeRemainderLen s n)))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt s) (__eo_to_smt n)
      (__eo_to_smt (stringDecomposeRemainderLen s n)) T hS hN hRem

private theorem smt_typeof_string_decompose_short_prefix
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (stringDecomposeShortPrefix s n)) =
      SmtType.Seq T := by
  have hRem := smt_typeof_string_decompose_remainder_len s n T hS hN
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
            (__eo_to_smt (stringDecomposeRemainderLen s n)))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt s) (SmtTerm.Numeral 0)
      (__eo_to_smt (stringDecomposeRemainderLen s n)) T hS
      (by simp [__smtx_typeof]) hRem

private theorem smt_typeof_string_decompose_last
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (stringDecomposeLast s n)) =
      SmtType.Seq T := by
  have hRem := smt_typeof_string_decompose_remainder_len s n T hS hN
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt s)
            (__eo_to_smt (stringDecomposeRemainderLen s n)) (__eo_to_smt n))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt s)
      (__eo_to_smt (stringDecomposeRemainderLen s n)) (__eo_to_smt n)
      T hS hRem hN

private theorem typed_string_decompose_false_body
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (stringDecomposeFalseBody s n) := by
  let pre := stringDecomposePrefix s n
  let suf := stringDecomposeSuffix s n
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
  have hPre : __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
    simpa [pre] using smt_typeof_string_decompose_prefix s n T hS hN
  have hSuf : __smtx_typeof (__eo_to_smt suf) = SmtType.Seq T := by
    simpa [suf] using smt_typeof_string_decompose_suffix s n T hS hN
  have hNil : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPre
  have hSufNil :
      __smtx_typeof (__eo_to_smt (sdConcat suf nil)) = SmtType.Seq T := by
    change
      __smtx_typeof (SmtTerm.str_concat (__eo_to_smt suf) (__eo_to_smt nil)) =
        SmtType.Seq T
    exact smtx_typeof_str_concat_seq (__eo_to_smt suf) (__eo_to_smt nil) T hSuf hNil
  have hRhs :
      __smtx_typeof (__eo_to_smt (sdConcat pre (sdConcat suf nil))) =
        SmtType.Seq T := by
    change
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt pre)
            (__eo_to_smt (sdConcat suf nil))) =
        SmtType.Seq T
    exact smtx_typeof_str_concat_seq (__eo_to_smt pre)
      (__eo_to_smt (sdConcat suf nil)) T hPre hSufNil
  have hEqMain :
      RuleProofs.eo_has_bool_type (sdEq s (sdConcat pre (sdConcat suf nil))) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type s
      (sdConcat pre (sdConcat suf nil))
      (by rw [hS, hRhs]) (by rw [hS]; simp)
  have hLenPre :
      __smtx_typeof (__eo_to_smt (sdLen pre)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt pre)) = SmtType.Int
    exact smtx_typeof_str_len_seq (__eo_to_smt pre) T hPre
  have hEqLen : RuleProofs.eo_has_bool_type (sdEq (sdLen pre) n) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (sdLen pre) n
      (by rw [hLenPre, hN]) (by rw [hLenPre]; simp)
  have hTail :
      RuleProofs.eo_has_bool_type (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hEqLen RuleProofs.eo_has_bool_type_true
  simpa [stringDecomposeFalseBody, pre, suf, nil, sdAnd, sdEq, sdConcat]
    using RuleProofs.eo_has_bool_type_and_of_bool_args
      (sdEq s (sdConcat pre (sdConcat suf nil)))
      (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true))
      hEqMain hTail

private theorem typed_string_decompose_true_body
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (stringDecomposeTrueBody s n) := by
  let pre := stringDecomposeShortPrefix s n
  let last := stringDecomposeLast s n
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
  have hPre : __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
    simpa [pre] using smt_typeof_string_decompose_short_prefix s n T hS hN
  have hLast : __smtx_typeof (__eo_to_smt last) = SmtType.Seq T := by
    simpa [last] using smt_typeof_string_decompose_last s n T hS hN
  have hNil : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPre
  have hLastNil :
      __smtx_typeof (__eo_to_smt (sdConcat last nil)) = SmtType.Seq T := by
    change
      __smtx_typeof (SmtTerm.str_concat (__eo_to_smt last) (__eo_to_smt nil)) =
        SmtType.Seq T
    exact smtx_typeof_str_concat_seq (__eo_to_smt last) (__eo_to_smt nil) T hLast hNil
  have hRhs :
      __smtx_typeof (__eo_to_smt (sdConcat pre (sdConcat last nil))) =
        SmtType.Seq T := by
    change
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt pre)
            (__eo_to_smt (sdConcat last nil))) =
        SmtType.Seq T
    exact smtx_typeof_str_concat_seq (__eo_to_smt pre)
      (__eo_to_smt (sdConcat last nil)) T hPre hLastNil
  have hEqMain :
      RuleProofs.eo_has_bool_type (sdEq s (sdConcat pre (sdConcat last nil))) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type s
      (sdConcat pre (sdConcat last nil))
      (by rw [hS, hRhs]) (by rw [hS]; simp)
  have hLenLast :
      __smtx_typeof (__eo_to_smt (sdLen last)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt last)) = SmtType.Int
    exact smtx_typeof_str_len_seq (__eo_to_smt last) T hLast
  have hEqLen : RuleProofs.eo_has_bool_type (sdEq (sdLen last) n) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (sdLen last) n
      (by rw [hLenLast, hN]) (by rw [hLenLast]; simp)
  have hTail :
      RuleProofs.eo_has_bool_type (sdAnd (sdEq (sdLen last) n) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hEqLen RuleProofs.eo_has_bool_type_true
  simpa [stringDecomposeTrueBody, pre, last, nil, sdAnd, sdEq, sdConcat]
    using RuleProofs.eo_has_bool_type_and_of_bool_args
      (sdEq s (sdConcat pre (sdConcat last nil)))
      (sdAnd (sdEq (sdLen last) n) (Term.Boolean true))
      hEqMain hTail

private theorem eo_requires_true_eq (x body : Term)
    (h : x = Term.Boolean true) :
    __eo_requires x (Term.Boolean true) body = body := by
  subst x
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

private theorem string_decompose_requires_eq
    (n lv body : Term)
    (hReq :
      __eo_requires (__eo_eq n lv) (Term.Boolean true) body ≠ Term.Stuck) :
    __eo_requires (__eo_eq n lv) (Term.Boolean true) body = body ∧
      lv = n := by
  have hReq' := hReq
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hReq'
  rcases hReq' with ⟨hCond, _hBody⟩
  exact ⟨eo_requires_true_eq _ body hCond,
    eq_of_eo_eq_true_local n lv hCond⟩

private theorem string_decompose_false_generated_eq_body
    (s n : Term) (T : SmtType)
    (hPre : __smtx_typeof (__eo_to_smt (stringDecomposePrefix s n)) =
      SmtType.Seq T) :
    stringDecomposeFalseGeneratedBody s n =
      stringDecomposeFalseBody s n := by
  let pre := stringDecomposePrefix s n
  let suf := stringDecomposeSuffix s n
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
  have hNilNe : nil ≠ Term.Stuck := by
    simpa [nil, pre] using
      nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T (by simpa [pre] using hPre)
  simp [stringDecomposeFalseGeneratedBody, stringDecomposeFalseBody,
    pre,nil, sdAnd, sdEq, sdConcat, __eo_mk_apply]

private theorem string_decompose_true_generated_eq_body
    (s n : Term) (T : SmtType)
    (hPre : __smtx_typeof (__eo_to_smt (stringDecomposeShortPrefix s n)) =
      SmtType.Seq T) :
    stringDecomposeTrueGeneratedBody s n =
      stringDecomposeTrueBody s n := by
  let pre := stringDecomposeShortPrefix s n
  let last := stringDecomposeLast s n
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
  have hNilNe : nil ≠ Term.Stuck := by
    simpa [nil, pre] using
      nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T (by simpa [pre] using hPre)
  simp [stringDecomposeTrueGeneratedBody, stringDecomposeTrueBody,
    pre,nil, sdAnd, sdEq, sdConcat, __eo_mk_apply]

private theorem facts_string_decompose_false_body
    (M : SmtModel) (hM : model_wf M)
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hTyped : RuleProofs.eo_has_bool_type (stringDecomposeFalseBody s n))
    (hPremGe :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))
        true)
    (hPremLen :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (sdLen s)) n)
        true) :
    eo_interprets M (stringDecomposeFalseBody s n) true := by
  let pre := stringDecomposePrefix s n
  let suf := stringDecomposeSuffix s n
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
  let rhs := sdConcat pre (sdConcat suf nil)
  have hEqBool :
      RuleProofs.eo_has_bool_type (sdEq s rhs) := by
    simpa [stringDecomposeFalseBody, pre, suf, nil, rhs, sdAnd, sdEq, sdConcat]
      using RuleProofs.eo_has_bool_type_and_left
        (sdEq s rhs)
        (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true)) hTyped
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true)) := by
    simpa [stringDecomposeFalseBody, pre, suf, nil, rhs, sdAnd, sdEq, sdConcat]
      using RuleProofs.eo_has_bool_type_and_right
        (sdEq s rhs)
        (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true)) hTyped
  have hLenBool : RuleProofs.eo_has_bool_type (sdEq (sdLen pre) n) :=
    RuleProofs.eo_has_bool_type_and_left
      (sdEq (sdLen pre) n) (Term.Boolean true) hTailBool
  have hSEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt s) (SmtType.Seq T)
      hS (seq_ne_none T) (type_inhabited_seq T)
  have hNEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt n) SmtType.Int
      hN (by simp) type_inhabited_int
  rcases seq_value_canonical hSEvalTy with ⟨ss, hsEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hnEval⟩
  let xs := native_unpack_seq ss
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hsEval, __smtx_typeof_value] using hSEvalTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have h0 : 0 <= ni :=
    eval_geq_zero_true_of_premise M n ni hnEval hPremGe
  have hle : ni <= Int.ofNat xs.length := by
    simpa [xs] using
      eval_len_geq_true_of_premise M s n ss ni hsEval hnEval hPremLen
  have hPreTy : __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
    simpa [pre] using smt_typeof_string_decompose_prefix s n T hS hN
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
  have hSplit :
      native_seq_extract xs 0 ni ++
          native_seq_extract xs ni (Int.ofNat xs.length - ni) =
        xs :=
    native_seq_extract_split_front xs ni h0 hle
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T xs) := by
    change
      __smtx_model_eval M
          (SmtTerm.str_concat
            (SmtTerm._at_purify
              (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0) (__eo_to_smt n)))
            (SmtTerm.str_concat
              (SmtTerm._at_purify
                (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
                  (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n))))
              (__eo_to_smt nil))) =
        SmtValue.Seq (native_pack_seq T xs)
    simpa [rhs, pre, suf, nil, xs, stringDecomposePrefix, stringDecomposeSuffix,
      stringDecomposeRemainderLen, sdConcat, sdPurify, sdSubstr, sdMinus, sdLen,
      __smtx_model_eval, hsEval, hnEval, hNilEval, __smtx_model_eval_str_substr,
      __smtx_model_eval_str_concat, __smtx_model_eval_str_len,
      __smtx_model_eval__at_purify, __smtx_model_eval__, native_seq_len,
      native_seq_concat, native_zplus, native_zneg,
      _root_.native_unpack_pack_seq,
      elem_typeof_pack_seq, native_unpack_seq, hElem, Int.sub_eq_add_neg,
      List.append_assoc] using
      congrArg (fun ys => SmtValue.Seq (native_pack_seq T ys)) hSplit
  have hEqRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    unfold RuleProofs.smt_value_rel
    rw [hsEval, hRhsEval]
    exact smt_seq_rel_pack_unpack T ss hElem
  have hEqTrue : eo_interprets M (sdEq s rhs) true :=
    RuleProofs.eo_interprets_eq_of_rel M s rhs hEqBool hEqRel
  have hPreLenEval :
      __smtx_model_eval M (__eo_to_smt (sdLen pre)) =
        SmtValue.Numeral ni := by
    change
      __smtx_model_eval M
          (SmtTerm.str_len
            (SmtTerm._at_purify
              (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0) (__eo_to_smt n)))) =
        SmtValue.Numeral ni
    simpa [pre, xs, stringDecomposePrefix, sdLen, sdPurify, sdSubstr,
      __smtx_model_eval, hsEval, hnEval, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval__at_purify,
      native_seq_len, _root_.native_unpack_pack_seq] using
      congrArg SmtValue.Numeral (native_seq_extract_prefix_length xs ni h0 hle)
  have hLenRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (sdLen pre)))
        (__smtx_model_eval M (__eo_to_smt n)) := by
    rw [hPreLenEval, hnEval]
    exact RuleProofs.smt_value_rel_refl _
  have hLenTrue : eo_interprets M (sdEq (sdLen pre) n) true :=
    RuleProofs.eo_interprets_eq_of_rel M (sdLen pre) n hLenBool hLenRel
  have hTailTrue :
      eo_interprets M (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true)) true :=
    RuleProofs.eo_interprets_and_intro M _ _
      hLenTrue (RuleProofs.eo_interprets_true M)
  simpa [stringDecomposeFalseBody, pre, suf, nil, rhs, sdAnd, sdEq, sdConcat]
    using RuleProofs.eo_interprets_and_intro M (sdEq s rhs)
      (sdAnd (sdEq (sdLen pre) n) (Term.Boolean true))
      hEqTrue hTailTrue

private theorem facts_string_decompose_true_body
    (M : SmtModel) (hM : model_wf M)
    (s n : Term) (T : SmtType)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hN : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hTyped : RuleProofs.eo_has_bool_type (stringDecomposeTrueBody s n))
    (hPremGe :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))
        true)
    (hPremLen :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (sdLen s)) n)
        true) :
    eo_interprets M (stringDecomposeTrueBody s n) true := by
  let pre := stringDecomposeShortPrefix s n
  let last := stringDecomposeLast s n
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
  let rhs := sdConcat pre (sdConcat last nil)
  have hEqBool :
      RuleProofs.eo_has_bool_type (sdEq s rhs) := by
    simpa [stringDecomposeTrueBody, pre, last, nil, rhs, sdAnd, sdEq, sdConcat]
      using RuleProofs.eo_has_bool_type_and_left
        (sdEq s rhs)
        (sdAnd (sdEq (sdLen last) n) (Term.Boolean true)) hTyped
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (sdAnd (sdEq (sdLen last) n) (Term.Boolean true)) := by
    simpa [stringDecomposeTrueBody, pre, last, nil, rhs, sdAnd, sdEq, sdConcat]
      using RuleProofs.eo_has_bool_type_and_right
        (sdEq s rhs)
        (sdAnd (sdEq (sdLen last) n) (Term.Boolean true)) hTyped
  have hLenBool : RuleProofs.eo_has_bool_type (sdEq (sdLen last) n) :=
    RuleProofs.eo_has_bool_type_and_left
      (sdEq (sdLen last) n) (Term.Boolean true) hTailBool
  have hSEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt s) (SmtType.Seq T)
      hS (seq_ne_none T) (type_inhabited_seq T)
  have hNEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt n) SmtType.Int
      hN (by simp) type_inhabited_int
  rcases seq_value_canonical hSEvalTy with ⟨ss, hsEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hnEval⟩
  let xs := native_unpack_seq ss
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hsEval, __smtx_typeof_value] using hSEvalTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have h0 : 0 <= ni :=
    eval_geq_zero_true_of_premise M n ni hnEval hPremGe
  have hle : ni <= Int.ofNat xs.length := by
    simpa [xs] using
      eval_len_geq_true_of_premise M s n ss ni hsEval hnEval hPremLen
  have hPreTy : __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
    simpa [pre] using smt_typeof_string_decompose_short_prefix s n T hS hN
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
  have hSplit :
      native_seq_extract xs 0 (Int.ofNat xs.length - ni) ++
          native_seq_extract xs (Int.ofNat xs.length - ni) ni =
        xs :=
    native_seq_extract_split_back xs ni h0 hle
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T xs) := by
    change
      __smtx_model_eval M
          (SmtTerm.str_concat
            (SmtTerm._at_purify
              (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
                (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n))))
            (SmtTerm.str_concat
              (SmtTerm._at_purify
                (SmtTerm.str_substr (__eo_to_smt s)
                  (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n))
                  (__eo_to_smt n)))
              (__eo_to_smt nil))) =
        SmtValue.Seq (native_pack_seq T xs)
    simpa [rhs, pre, last, nil, xs, stringDecomposeShortPrefix,
      stringDecomposeLast, stringDecomposeRemainderLen, sdConcat, sdPurify,
      sdSubstr, sdMinus, sdLen, __smtx_model_eval, hsEval, hnEval, hNilEval,
      __smtx_model_eval_str_substr, __smtx_model_eval_str_concat,
      __smtx_model_eval_str_len, __smtx_model_eval__at_purify,
      __smtx_model_eval__, native_seq_len, native_seq_concat, native_zplus,
      native_zneg, _root_.native_unpack_pack_seq, elem_typeof_pack_seq,
      native_unpack_seq, hElem, Int.sub_eq_add_neg, List.append_assoc] using
      congrArg (fun ys => SmtValue.Seq (native_pack_seq T ys)) hSplit
  have hEqRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    unfold RuleProofs.smt_value_rel
    rw [hsEval, hRhsEval]
    exact smt_seq_rel_pack_unpack T ss hElem
  have hEqTrue : eo_interprets M (sdEq s rhs) true :=
    RuleProofs.eo_interprets_eq_of_rel M s rhs hEqBool hEqRel
  have hLastLenEval :
      __smtx_model_eval M (__eo_to_smt (sdLen last)) =
        SmtValue.Numeral ni := by
    change
      __smtx_model_eval M
          (SmtTerm.str_len
            (SmtTerm._at_purify
              (SmtTerm.str_substr (__eo_to_smt s)
                (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n))
                (__eo_to_smt n)))) =
        SmtValue.Numeral ni
    simpa [last, xs, stringDecomposeLast, stringDecomposeRemainderLen,
      sdLen, sdPurify, sdSubstr, sdMinus, __smtx_model_eval, hsEval, hnEval,
      __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
      __smtx_model_eval__at_purify, __smtx_model_eval__, native_seq_len,
      native_zplus, native_zneg, _root_.native_unpack_pack_seq,
      Int.sub_eq_add_neg] using
      congrArg SmtValue.Numeral (native_seq_extract_last_length xs ni h0 hle)
  have hLenRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (sdLen last)))
        (__smtx_model_eval M (__eo_to_smt n)) := by
    rw [hLastLenEval, hnEval]
    exact RuleProofs.smt_value_rel_refl _
  have hLenTrue : eo_interprets M (sdEq (sdLen last) n) true :=
    RuleProofs.eo_interprets_eq_of_rel M (sdLen last) n hLenBool hLenRel
  have hTailTrue :
      eo_interprets M (sdAnd (sdEq (sdLen last) n) (Term.Boolean true)) true :=
    RuleProofs.eo_interprets_and_intro M _ _
      hLenTrue (RuleProofs.eo_interprets_true M)
  simpa [stringDecomposeTrueBody, pre, last, nil, rhs, sdAnd, sdEq, sdConcat]
    using RuleProofs.eo_interprets_and_intro M (sdEq s rhs)
      (sdAnd (sdEq (sdLen last) n) (Term.Boolean true))
      hEqTrue hTailTrue

public theorem cmd_step_string_decompose_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_decompose args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_decompose args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_decompose args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hCmdNe : __eo_cmd_step_proven s CRule.string_decompose args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hCmdNe
      exact False.elim (hCmdNe rfl)
  | cons b args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hCmdNe
          exact False.elim (hCmdNe rfl)
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hCmdNe
              exact False.elim (hCmdNe rfl)
          | cons i₁ premises =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hCmdNe
                  exact False.elim (hCmdNe rfl)
              | cons i₂ premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hCmdNe
                      exact False.elim (hCmdNe rfl)
                  | nil =>
                      let P₁ := __eo_state_proven_nth s i₁
                      let P₂ := __eo_state_proven_nth s i₂
                      have hBTrans : RuleProofs.eo_has_smt_translation b := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                      let bArg := b
                      have hBTransArg : RuleProofs.eo_has_smt_translation bArg := by
                        simpa [bArg] using hBTrans
                      change
                        __eo_typeof
                            (__eo_prog_string_decompose bArg (Proof.pf P₁) (Proof.pf P₂)) =
                          Term.Bool at hResultTy
                      change
                        StepRuleProperties M [P₁, P₂]
                          (__eo_prog_string_decompose bArg (Proof.pf P₁) (Proof.pf P₂))
                      change
                        __eo_prog_string_decompose bArg (Proof.pf P₁) (Proof.pf P₂) ≠
                          Term.Stuck at hCmdNe
                      unfold __eo_prog_string_decompose at hResultTy hCmdNe ⊢
                      repeat' (split at * <;> try (subst_vars; simp at hResultTy hCmdNe))
                      all_goals
                        try
                          exact False.elim (by
                            change Term.Stuck = Term.Bool at hResultTy
                            cases hResultTy)
                      rename_i
                        _mTy _p₁Ty _p₂Ty nArg sArg lvN hP₁Eq hP₂Eq _hbNeTy
                        _mNe _p₁Ne _p₂Ne _nArgNe _sArgNe _lvNNe _hP₁EqNe _hP₂EqNe
                        _hbNe
                      change
                        __eo_typeof
                            (__eo_requires (__eo_eq nArg lvN) (Term.Boolean true)
                              (__eo_ite bArg
                                (stringDecomposeTrueGeneratedBody sArg nArg)
                                (stringDecomposeFalseGeneratedBody sArg nArg))) =
                          Term.Bool at hResultTy
                      change
                        StepRuleProperties M [P₁, P₂]
                          (__eo_requires (__eo_eq nArg lvN) (Term.Boolean true)
                            (__eo_ite bArg
                              (stringDecomposeTrueGeneratedBody sArg nArg)
                              (stringDecomposeFalseGeneratedBody sArg nArg)))
                      have hReqNe :
                          __eo_requires (__eo_eq nArg lvN) (Term.Boolean true)
                              (__eo_ite bArg
                                (stringDecomposeTrueGeneratedBody sArg nArg)
                                (stringDecomposeFalseGeneratedBody sArg nArg)) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases string_decompose_requires_eq nArg lvN
                          (__eo_ite bArg
                            (stringDecomposeTrueGeneratedBody sArg nArg)
                            (stringDecomposeFalseGeneratedBody sArg nArg)) hReqNe with
                        ⟨hReqEq, hLv⟩
                      have hP₁TermEq :
                          P₁ =
                            Term.Apply
                              (Term.Apply (Term.UOp UserOp.geq) nArg)
                              (Term.Numeral 0) := by
                        injection hP₁Eq
                      have hP₂TermEq :
                          P₂ =
                            Term.Apply
                              (Term.Apply (Term.UOp UserOp.geq) (sdLen sArg))
                              lvN := by
                        injection hP₂Eq
                      rw [hReqEq] at hResultTy ⊢
                      have hP₁Bool :
                          RuleProofs.eo_has_bool_type
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.geq) nArg)
                              (Term.Numeral 0)) := by
                        simpa [hP₁TermEq] using
                          hPremisesBool P₁ (by simp [P₁, premiseTermList])
                      have hNTy :
                          __smtx_typeof (__eo_to_smt nArg) = SmtType.Int :=
                        smt_typeof_int_of_geq_zero_bool nArg hP₁Bool
                      have hP₂Bool :
                          RuleProofs.eo_has_bool_type
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.geq) (sdLen sArg))
                              nArg) := by
                        simpa [hP₂TermEq, hLv] using
                          hPremisesBool P₂ (by simp [P₂, premiseTermList])
                      rcases smt_typeof_seq_of_geq_str_len_bool sArg nArg hNTy hP₂Bool with
                        ⟨T, hSTy⟩
                      cases hB : bArg <;>
                        simp [hB, __eo_ite, native_ite, native_teq] at hResultTy ⊢
                      all_goals
                        try
                          exact False.elim (by
                            change Term.Stuck = Term.Bool at hResultTy
                            cases hResultTy)
                      case Boolean bv =>
                        cases bv <;>
                          simp at hResultTy ⊢
                        · have hTyped :
                              RuleProofs.eo_has_bool_type
                                (stringDecomposeFalseBody sArg nArg) :=
                            typed_string_decompose_false_body sArg nArg T hSTy hNTy
                          have hPreTy :
                              __smtx_typeof
                                  (__eo_to_smt (stringDecomposePrefix sArg nArg)) =
                                SmtType.Seq T := by
                            exact smt_typeof_string_decompose_prefix sArg nArg T hSTy hNTy
                          have hGenEq :
                              stringDecomposeFalseGeneratedBody sArg nArg =
                                stringDecomposeFalseBody sArg nArg :=
                            string_decompose_false_generated_eq_body sArg nArg T hPreTy
                          rw [hGenEq] at hResultTy ⊢
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type
                            (stringDecomposeFalseBody sArg nArg) hTyped⟩
                          intro hTrue
                          have hPremGe :
                              eo_interprets M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.geq) nArg)
                                  (Term.Numeral 0))
                                true := by
                            simpa [hP₁TermEq] using hTrue P₁ (by simp [P₁])
                          have hPremLen :
                              eo_interprets M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.geq) (sdLen sArg))
                                  nArg)
                                true := by
                            simpa [hP₂TermEq, hLv] using hTrue P₂ (by simp [P₂])
                          exact facts_string_decompose_false_body M hM sArg nArg T
                            hSTy hNTy hTyped hPremGe hPremLen
                        · have hTyped :
                              RuleProofs.eo_has_bool_type
                                (stringDecomposeTrueBody sArg nArg) :=
                            typed_string_decompose_true_body sArg nArg T hSTy hNTy
                          have hPreTy :
                              __smtx_typeof
                                  (__eo_to_smt (stringDecomposeShortPrefix sArg nArg)) =
                                SmtType.Seq T := by
                            exact smt_typeof_string_decompose_short_prefix sArg nArg T
                              hSTy hNTy
                          have hGenEq :
                              stringDecomposeTrueGeneratedBody sArg nArg =
                                stringDecomposeTrueBody sArg nArg :=
                            string_decompose_true_generated_eq_body sArg nArg T hPreTy
                          rw [hGenEq] at hResultTy ⊢
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type
                            (stringDecomposeTrueBody sArg nArg) hTyped⟩
                          intro hTrue
                          have hPremGe :
                              eo_interprets M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.geq) nArg)
                                  (Term.Numeral 0))
                                true := by
                            simpa [hP₁TermEq] using hTrue P₁ (by simp [P₁])
                          have hPremLen :
                              eo_interprets M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.geq) (sdLen sArg))
                                  nArg)
                                true := by
                            simpa [hP₂TermEq, hLv] using hTrue P₂ (by simp [P₂])
                          exact facts_string_decompose_true_body M hM sArg nArg T
                            hSTy hNTy hTyped hPremGe hPremLen
