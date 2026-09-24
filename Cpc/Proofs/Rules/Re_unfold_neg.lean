module

public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private abbrev idxName : native_String :=
  native_string_lit "@var.str_index"

private abbrev idxVar : Term :=
  Term.Var (Term.String idxName) (Term.UOp UserOp.Int)

private abbrev idxList : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons idxVar) Term.__eo_List_nil

abbrev mkNot (x : Term) : Term :=
  Term.Apply Term.not x

abbrev mkAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.and x) y

abbrev mkOr (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.or x) y

abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) y

abbrev mkLt (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y

abbrev mkLeq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y

abbrev mkNeg (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y

abbrev mkStrLen (x : Term) : Term :=
  Term.Apply Term.str_len x

abbrev mkSubstr (s i n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) i) n

abbrev mkStrInRe (s r : Term) : Term :=
  Term.Apply (Term.Apply Term.str_in_re s) r

abbrev mkReMult (r : Term) : Term :=
  Term.Apply Term.re_mult r

abbrev mkReConcat (r s : Term) : Term :=
  Term.Apply (Term.Apply Term.re_concat r) s

abbrev qforallIdx (body : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) idxList) body

abbrev reUnfoldNegStarBody (t r1 : Term) : Term :=
  mkOr (mkLeq idxVar (Term.Numeral 0))
    (mkOr (mkLt (mkStrLen t) idxVar)
      (mkOr (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))
            (mkReMult r1)))
          (Term.Boolean false))))

abbrev reUnfoldNegStarFormula (t r1 : Term) : Term :=
  mkAnd (mkNot (mkEq t (Term.String [])))
    (mkAnd (qforallIdx (reUnfoldNegStarBody t r1)) (Term.Boolean true))

abbrev reUnfoldNegConcatBody (t r1 tail : Term) : Term :=
  mkOr (mkLt idxVar (Term.Numeral 0))
    (mkOr (mkLt (mkStrLen t) idxVar)
      (mkOr (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail))
          (Term.Boolean false))))

abbrev reUnfoldNegConcatFormula (t r1 r2 : Term) : Term :=
  qforallIdx
    (reUnfoldNegConcatBody t r1
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))

theorem str_in_re_args_of_bool_type (s r : Term) :
    RuleProofs.eo_has_bool_type (mkStrInRe s r) ->
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hBool
  have hNN :
      term_has_non_none_type
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_bool_type at hBool
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtType.Bool at hBool
    rw [hBool]
    simp
  exact seq_char_reglan_args_of_non_none
    (op := SmtTerm.str_in_re)
    (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNN

theorem smtx_typeof_idxVar :
    __smtx_typeof (__eo_to_smt idxVar) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Var idxName SmtType.Int) = SmtType.Int
  have hWF : __smtx_type_wf SmtType.Int = true := by
    simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and]
  simp [__smtx_typeof, __smtx_typeof_guard_wf, hWF, native_ite]

theorem smtx_typeof_zero :
    __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
  simp [__smtx_typeof]

theorem smtx_typeof_empty_string :
    __smtx_typeof (__eo_to_smt (Term.String [])) =
      SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.String []) = SmtType.Seq SmtType.Char
  simp [__smtx_typeof, native_string_valid, native_ite]

theorem smtx_typeof_re_mult_of_reglan (r : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (mkReMult r)) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan
  rw [typeof_re_mult_eq]
  simp [hr, native_ite, native_Teq]

theorem smtx_typeof_re_mult_arg_of_reglan (r : Term) :
    __smtx_typeof (__eo_to_smt (mkReMult r)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hTy
  change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan at hTy
  rw [typeof_re_mult_eq] at hTy
  cases h : __smtx_typeof (__eo_to_smt r) <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

theorem smtx_typeof_re_concat_of_reglan (r s : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (mkReConcat r s)) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_re_concat_eq]
  simp [hr, hs, native_ite, native_Teq]

theorem smtx_typeof_re_concat_args_of_reglan (r s : Term) :
    __smtx_typeof (__eo_to_smt (mkReConcat r s)) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt s) = SmtType.RegLan := by
  intro hTy
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt s)) =
    SmtType.RegLan at hTy
  rw [typeof_re_concat_eq] at hTy
  cases hr : __smtx_typeof (__eo_to_smt r) <;>
    cases hs : __smtx_typeof (__eo_to_smt s) <;>
    simp [hr, hs, native_ite, native_Teq] at hTy ⊢

theorem smtx_typeof_str_in_re_of_seq_reglan (s r : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type (mkStrInRe s r) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtType.Bool
  rw [typeof_str_in_re_eq]
  simp [hs, hr, native_ite, native_Teq]

theorem smtx_typeof_str_len_of_seq_char (s : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (mkStrLen s)) = SmtType.Int := by
  simpa [mkStrLen, __eo_to_smt, __smtx_typeof] using
    smtx_typeof_str_len_seq (__eo_to_smt s) SmtType.Char hs

theorem smtx_typeof_substr_of_seq_char (s i n : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hi : __smtx_typeof (__eo_to_smt i) = SmtType.Int)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (mkSubstr s i n)) =
      SmtType.Seq SmtType.Char := by
  simpa [mkSubstr, __eo_to_smt, __smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt s) (__eo_to_smt i)
      (__eo_to_smt n) SmtType.Char hs hi hn

theorem smtx_typeof_neg_of_int (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (mkNeg x y)) = SmtType.Int := by
  simpa [mkNeg, __eo_to_smt, __smtx_typeof] using smtx_typeof_neg_int (__eo_to_smt x) (__eo_to_smt y) hx hy

private theorem smtx_typeof_lt_of_int (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (mkLt x y) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Bool
  rw [typeof_lt_eq]
  simp [hx, hy, __smtx_typeof_arith_overload_op_2_ret]

private theorem smtx_typeof_leq_of_int (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (mkLeq x y) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Bool
  rw [typeof_leq_eq]
  simp [hx, hy, __smtx_typeof_arith_overload_op_2_ret]

private theorem typeof_exists_eq_local (s : native_String) (T : SmtType)
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := by
  rw [smtx_typeof_exists_term_eq]

private theorem smtx_typeof_not_bool_of_arg_bool (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_exists_int_bool_of_body_bool (body : SmtTerm) :
    __smtx_typeof body = SmtType.Bool ->
    __smtx_typeof (SmtTerm.exists idxName SmtType.Int body) = SmtType.Bool := by
  intro hBody
  have hGuard :
      __smtx_typeof_guard_wf SmtType.Int SmtType.Bool = SmtType.Bool := by
    simp [__smtx_typeof_guard_wf, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and,
      native_ite]
  rw [typeof_exists_eq_local]
  simp [hBody, hGuard, native_ite, native_Teq]

private theorem qforall_idx_has_bool_type (body : Term) :
    RuleProofs.eo_has_bool_type body ->
    RuleProofs.eo_has_bool_type (qforallIdx body) := by
  intro hBody
  unfold RuleProofs.eo_has_bool_type at hBody ⊢
  change __smtx_typeof
      (SmtTerm.not
        (SmtTerm.exists idxName SmtType.Int
          (SmtTerm.not (__eo_to_smt body)))) = SmtType.Bool
  exact smtx_typeof_not_bool_of_arg_bool _
    (smtx_typeof_exists_int_bool_of_body_bool _
      (smtx_typeof_not_bool_of_arg_bool _ hBody))

private theorem re_unfold_neg_star_body_has_bool_type (t r1 : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type (reUnfoldNegStarBody t r1) := by
  have hLen := smtx_typeof_str_len_of_seq_char t ht
  have hNeg := smtx_typeof_neg_of_int (mkStrLen t) idxVar hLen smtx_typeof_idxVar
  have hLeftSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t (Term.Numeral 0) idxVar)) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t (Term.Numeral 0) idxVar
      ht smtx_typeof_zero smtx_typeof_idxVar
  have hRightSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t idxVar (mkNeg (mkStrLen t) idxVar)
      ht smtx_typeof_idxVar hNeg
  have hLe0 := smtx_typeof_leq_of_int idxVar (Term.Numeral 0)
    smtx_typeof_idxVar smtx_typeof_zero
  have hLtLen := smtx_typeof_lt_of_int (mkStrLen t) idxVar
    hLen smtx_typeof_idxVar
  have hLeftIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t (Term.Numeral 0) idxVar) r1 hLeftSub hr1
  have hRightIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) (mkReMult r1)
      hRightSub (smtx_typeof_re_mult_of_reglan r1 hr1)
  exact RuleProofs.eo_has_bool_type_or_of_bool_args
    (mkLeq idxVar (Term.Numeral 0))
    (mkOr (mkLt (mkStrLen t) idxVar)
      (mkOr (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))
            (mkReMult r1)))
          (Term.Boolean false))))
    hLe0
    (RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkLt (mkStrLen t) idxVar)
      (mkOr (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))
            (mkReMult r1)))
          (Term.Boolean false)))
      hLtLen
      (RuleProofs.eo_has_bool_type_or_of_bool_args
        (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))
            (mkReMult r1)))
          (Term.Boolean false))
        (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hLeftIn)
        (RuleProofs.eo_has_bool_type_or_of_bool_args
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))
            (mkReMult r1)))
          (Term.Boolean false)
          (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hRightIn)
          RuleProofs.eo_has_bool_type_false)))

theorem re_unfold_neg_concat_body_has_bool_type (t r1 tail : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTail : __smtx_typeof (__eo_to_smt tail) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type (reUnfoldNegConcatBody t r1 tail) := by
  have hLen := smtx_typeof_str_len_of_seq_char t ht
  have hNeg := smtx_typeof_neg_of_int (mkStrLen t) idxVar hLen smtx_typeof_idxVar
  have hLeftSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t (Term.Numeral 0) idxVar)) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t (Term.Numeral 0) idxVar
      ht smtx_typeof_zero smtx_typeof_idxVar
  have hRightSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t idxVar (mkNeg (mkStrLen t) idxVar)
      ht smtx_typeof_idxVar hNeg
  have hLt0 := smtx_typeof_lt_of_int idxVar (Term.Numeral 0)
    smtx_typeof_idxVar smtx_typeof_zero
  have hLtLen := smtx_typeof_lt_of_int (mkStrLen t) idxVar
    hLen smtx_typeof_idxVar
  have hLeftIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t (Term.Numeral 0) idxVar) r1 hLeftSub hr1
  have hRightIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail
      hRightSub hTail
  exact RuleProofs.eo_has_bool_type_or_of_bool_args
    (mkLt idxVar (Term.Numeral 0))
    (mkOr (mkLt (mkStrLen t) idxVar)
      (mkOr (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail))
          (Term.Boolean false))))
    hLt0
    (RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkLt (mkStrLen t) idxVar)
      (mkOr (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail))
          (Term.Boolean false)))
      hLtLen
      (RuleProofs.eo_has_bool_type_or_of_bool_args
        (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1))
        (mkOr
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail))
          (Term.Boolean false))
        (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hLeftIn)
        (RuleProofs.eo_has_bool_type_or_of_bool_args
          (mkNot (mkStrInRe
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail))
          (Term.Boolean false)
          (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hRightIn)
          RuleProofs.eo_has_bool_type_false)))

private theorem re_unfold_neg_star_formula_has_bool_type (t r1 : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type (reUnfoldNegStarFormula t r1) := by
  have hEqEmpty : RuleProofs.eo_has_bool_type (mkEq t (Term.String [])) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t (Term.String [])
      (by rw [ht, smtx_typeof_empty_string])
      (by rw [ht]; simp)
  have hForall :=
    qforall_idx_has_bool_type (reUnfoldNegStarBody t r1)
      (re_unfold_neg_star_body_has_bool_type t r1 ht hr1)
  exact RuleProofs.eo_has_bool_type_and_of_bool_args
    (mkNot (mkEq t (Term.String [])))
    (mkAnd (qforallIdx (reUnfoldNegStarBody t r1)) (Term.Boolean true))
    (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqEmpty)
    (RuleProofs.eo_has_bool_type_and_of_bool_args
      (qforallIdx (reUnfoldNegStarBody t r1)) (Term.Boolean true)
      hForall RuleProofs.eo_has_bool_type_true)

theorem re_unfold_neg_concat_formula_has_bool_type
    (t r1 tail : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTail : __smtx_typeof (__eo_to_smt tail) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type
      (qforallIdx (reUnfoldNegConcatBody t r1 tail)) := by
  exact qforall_idx_has_bool_type (reUnfoldNegConcatBody t r1 tail)
    (re_unfold_neg_concat_body_has_bool_type t r1 tail ht hr1 hTail)

theorem native_unpack_string_substr_split
    (ss : SmtSeq) (i : native_Int)
    (hi0 : 0 <= i)
    (hile : i <= native_seq_len (native_unpack_seq ss)) :
    native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) 0 i)) ++
      native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) i
            (native_seq_len (native_unpack_seq ss) - i))) =
      native_unpack_string ss := by
  let xs := native_unpack_seq ss
  let n := Int.toNat i
  have hiCast : (Int.ofNat n : Int) = i := by
    simpa [n] using Int.toNat_of_nonneg hi0
  have hNLe : n <= xs.length := by
    have hInt : (Int.ofNat n : Int) <= Int.ofNat xs.length := by
      rw [hiCast]
      simpa [xs, native_seq_len] using hile
    exact Int.ofNat_le.mp hInt
  have hLeft :
      native_seq_extract xs 0 i = xs.take n := by
    rw [← hiCast]
    exact native_seq_extract_zero_nat xs n hNLe
  have hLenSub :
      native_seq_len xs - Int.ofNat n = Int.ofNat (xs.length - n) := by
    rw [native_seq_len]
    exact (Int.ofNat_sub hNLe).symm
  have hRight :
      native_seq_extract xs i (native_seq_len xs - i) = xs.drop n := by
    rw [← hiCast, hLenSub]
    exact native_seq_extract_to_end_nat xs n hNLe
  unfold native_unpack_string
  rw [hLeft, hRight]
  simp [xs, native_unpack_seq_pack_seq, List.take_append_drop]

private theorem nativeListInRe_star_append_intro (r : SmtRegLan) :
    (xs ys : List native_Char) ->
      nativeListInRe xs r = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, hLeft, hRight => by
      change
        nativeListInRe (cs ++ ys)
            (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
          true
      exact (nativeListInRe_mk_concat_true_iff_exists_append (cs ++ ys)
          (native_re_deriv c r) (SmtRegLan.star r)).2
        ⟨cs, ys, rfl, by simpa [nativeListInRe] using hLeft, hRight⟩

private theorem nativeListInRe_star_append_closed :
    (xs ys : List native_Char) -> (r : SmtRegLan) ->
      nativeListInRe xs (SmtRegLan.star r) = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, r, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, r, hLeft, hRight => by
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true := by
        simpa [nativeListInRe, native_re_deriv] using hLeft
      rcases (nativeListInRe_mk_concat_true_iff_exists_append cs
          (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
        ⟨left, right, hAppend, hLeftPart, hRightPart⟩
      have hLen : right.length < (c :: cs).length := by
        have hLenEq := congrArg List.length hAppend
        simp at hLenEq ⊢
        omega
      have hTail :
          nativeListInRe (right ++ ys) (SmtRegLan.star r) = true :=
        nativeListInRe_star_append_closed right ys r hRightPart hRight
      have hAppend' : left ++ (right ++ ys) = cs ++ ys := by
        rw [← List.append_assoc, hAppend]
      have hConcat' :
          nativeListInRe (cs ++ ys)
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true :=
        (nativeListInRe_mk_concat_true_iff_exists_append (cs ++ ys)
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨left, right ++ ys, hAppend', hLeftPart, hTail⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat'
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    omega

private theorem native_str_in_re_re_mult_append_intro
    (s1 s2 : native_String) (r : SmtRegLan) :
    native_str_in_re s1 r = true ->
    native_str_in_re s2 (native_re_mult r) = true ->
    native_str_in_re (s1 ++ s2) (native_re_mult r) = true := by
  intro h1 h2
  have h1Parts :
      native_string_valid s1 = true ∧ nativeListInRe s1 r = true := by
    simpa [native_str_in_re, nativeListInRe] using h1
  have h2Parts :
      native_string_valid s2 = true ∧
        nativeListInRe s2 (native_re_mult r) = true := by
    simpa [native_str_in_re, nativeListInRe] using h2
  have hValidAppend : native_string_valid (s1 ++ s2) = true := by
    have hAll1 : s1.all native_char_valid = true := by
      simpa [native_string_valid] using h1Parts.1
    have hAll2 : s2.all native_char_valid = true := by
      simpa [native_string_valid] using h2Parts.1
    change (s1 ++ s2).all native_char_valid = true
    simp [hAll1, hAll2]
  have hList :
      nativeListInRe (s1 ++ s2) (native_re_mult r) = true := by
    cases r with
    | empty =>
        have hBad : False := by
          have hEmpty := nativeListInRe_empty s1
          have hEq : false = true := by
            simpa [hEmpty] using h1Parts.2
          cases hEq
        exact False.elim hBad
    | epsilon =>
        cases s1 with
        | nil =>
            simpa [native_re_mult, native_re_mk_star] using h2Parts.2
        | cons c cs =>
            have hBad : False := by
              have hCsEmpty : nativeListInRe cs SmtRegLan.empty = true := by
                simpa [nativeListInRe, native_re_deriv] using h1Parts.2
              have hEq : false = true := by
                simpa [nativeListInRe_empty cs] using hCsEmpty
              cases hEq
            exact False.elim hBad
    | star r0 =>
        have h2Star :
            nativeListInRe s2 (SmtRegLan.star r0) = true := by
          simpa [native_re_mult, native_re_mk_star] using h2Parts.2
        simpa [native_re_mult, native_re_mk_star] using
          nativeListInRe_star_append_closed s1 s2 r0 h1Parts.2 h2Star
    | char c =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.char c) s1 s2
          h1Parts.2 h2Parts.2
    | range lo hi =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.range lo hi) s1 s2
          h1Parts.2 h2Parts.2
    | allchar =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro SmtRegLan.allchar s1 s2
          h1Parts.2 h2Parts.2
    | concat r0 r1 =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.concat r0 r1) s1 s2
          h1Parts.2 h2Parts.2
    | union r0 r1 =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.union r0 r1) s1 s2
          h1Parts.2 h2Parts.2
    | inter r0 r1 =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.inter r0 r1) s1 s2
          h1Parts.2 h2Parts.2
    | comp r0 =>
        simp [native_re_mult] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.comp r0) s1 s2
          h1Parts.2 h2Parts.2
  simpa [native_str_in_re, hValidAppend, nativeListInRe] using hList

private theorem native_str_in_re_re_mult_empty (r : SmtRegLan) :
    native_str_in_re [] (native_re_mult r) = true := by
  cases r <;> simp [native_str_in_re, native_string_valid, native_re_mult,
    nativeListInRe, native_re_nullable]

abbrev RegLanEval (M : SmtModel) (t : Term) : Prop :=
  ∃ r, __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r

theorem native_string_valid_of_str_in_re_true
    {str : native_String} {r : SmtRegLan}
    (h : native_str_in_re str r = true) :
    native_string_valid str = true := by
  cases hValid : native_string_valid str <;>
    simp [native_str_in_re, hValid] at h ⊢

theorem native_str_in_re_of_reglan_rel
    (str : native_String) (r s : SmtRegLan) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s) ->
    native_str_in_re str r = true ->
    native_str_in_re str s = true := by
  classical
  intro hRel hMem
  have hValid := native_string_valid_of_str_in_re_true hMem
  simpa [← reglan_str_in_re_eq_of_smt_value_rel hRel str hValid] using hMem

theorem reConcat_nil_eval_empty_of_is_list_nil_true
    (M : SmtModel) (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.RegLan (native_str_to_re ([] : native_String)) := by
  cases nil <;> try simp [__eo_is_list_nil] at hNil
  case Apply f x =>
    cases f <;> try simp at hNil
    case UOp op =>
      cases op <;> try simp at hNil
      case str_to_re =>
        cases x <;> try simp at hNil
        case String s =>
          cases s with
          | nil =>
              change __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.String [])) =
                SmtValue.RegLan (native_str_to_re ([] : native_String))
              simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                native_str_to_re, impl_native_re_of_list, native_pack_string,
                impl_native_string_to_values, native_pack_seq, native_unpack_seq]
          | cons c cs =>
              simp at hNil

private theorem reConcat_smt_value_rel_right_empty_eval
    (M : SmtModel) (x id : Term) (r : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan r ->
    __smtx_model_eval M (__eo_to_smt id) =
      SmtValue.RegLan (native_str_to_re ([] : native_String)) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkReConcat x id)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxEval hIdEval
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt id)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_re_concat, hxEval, hIdEval]
  cases r <;>
    simp [__smtx_model_eval_eq, native_re_concat,
      native_str_to_re, impl_native_re_of_list, impl_native_string_to_values]

private theorem reConcat_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.re_concat) t = Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
    exact False.elim (hNe rfl)
  case Apply f x =>
    cases f
    case UOp op =>
      cases op
      case str_to_re =>
        cases x
        case String s =>
          cases s with
          | nil =>
              exact ⟨true, by simp [__eo_is_list_nil]⟩
          | cons c cs =>
              exact ⟨false, by simp [__eo_is_list_nil]⟩
        all_goals
          exact ⟨false, by simp [__eo_is_list_nil]⟩
      all_goals
        exact ⟨false, by simp [__eo_is_list_nil]⟩
    all_goals
      exact ⟨false, by simp [__eo_is_list_nil]⟩
  all_goals
    exact ⟨false, by simp [__eo_is_list_nil]⟩

theorem reConcat_singleton_elim_rel_eval
    (M : SmtModel) (c : Term) :
    __eo_is_list (Term.UOp UserOp.re_concat) c = Term.Boolean true ->
    RegLanEval M c ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hCan
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.re_concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_concat) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.re_concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases reConcat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M (__eo_to_smt (mkReConcat head tail)))
          · rcases hCan with ⟨rConcat, hConcatEval⟩
            have hConcatEval' :
                __smtx_model_eval_re_concat
                    (__smtx_model_eval M (__eo_to_smt head))
                    (__smtx_model_eval M (__eo_to_smt tail)) =
                  SmtValue.RegLan rConcat := by
              change __smtx_model_eval M
                  (SmtTerm.re_concat (__eo_to_smt head) (__eo_to_smt tail)) =
                SmtValue.RegLan rConcat at hConcatEval
              simpa [__smtx_model_eval] using hConcatEval
            cases hHeadEval : __smtx_model_eval M (__eo_to_smt head) with
            | RegLan rHead =>
                exact RuleProofs.smt_value_rel_symm _ _
                  (reConcat_smt_value_rel_right_empty_eval M
                    head tail rHead hHeadEval
                    (reConcat_nil_eval_empty_of_is_list_nil_true M tail hNil))
            | NotValue =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Boolean b =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Numeral n =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Rational q =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Binary i n =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Fun s T U =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Char c =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Seq s =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Map m =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Set m =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | UValue i e =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | DtCons s d i =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Apply f x =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

theorem reConcat_singleton_elim_list_of_ne_stuck (c : Term) :
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat) c ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.re_concat) c = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c) ≠
        Term.Stuck := by
    simpa [__eo_list_singleton_elim] using h
  exact eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.re_concat) c)
    (Term.Boolean true) (__eo_list_singleton_elim_2 c) hReq

theorem reConcat_singleton_elim_has_reglan_type (c : Term) :
    __eo_is_list (Term.UOp UserOp.re_concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.RegLan ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) c)) =
      SmtType.RegLan := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.RegLan
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.re_concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_concat) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.re_concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases reConcat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          have hArgs := smtx_typeof_re_concat_args_of_reglan head tail hTy
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact hTy
          · exact hArgs.1
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hTy

theorem smt_eval_seq_char_of_smt_type_seq_char
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.Seq SmtType.Char ->
    ∃ s, __smtx_model_eval M t = SmtValue.Seq s := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) =
        SmtType.Seq SmtType.Char := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical hValTy

theorem smt_eval_reglan_of_smt_type_reglan
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

theorem smt_eval_int_of_smt_type_int
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.Int ->
    ∃ n, __smtx_model_eval M t = SmtValue.Numeral n := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Int := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact int_value_canonical hValTy

theorem eval_re_mult_of_reglan (M : SmtModel) (r : Term)
    (rv : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __smtx_model_eval M (__eo_to_smt (mkReMult r)) =
      SmtValue.RegLan (native_re_mult rv) := by
  intro hEval
  change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r)) =
    SmtValue.RegLan (native_re_mult rv)
  simp [__smtx_model_eval, __smtx_model_eval_re_mult, hEval]

theorem eval_re_concat_of_reglan (M : SmtModel) (r s : Term)
    (rv sv : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.RegLan sv ->
    __smtx_model_eval M (__eo_to_smt (mkReConcat r s)) =
      SmtValue.RegLan (native_re_concat rv sv) := by
  intro hr hs
  change __smtx_model_eval M
      (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt s)) =
    SmtValue.RegLan (native_re_concat rv sv)
  simp [__smtx_model_eval, __smtx_model_eval_re_concat, hr, hs]

theorem eval_str_in_re_of_seq_reglan (M : SmtModel)
    (s r : Term) (ss : SmtSeq) (rv : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __smtx_model_eval M (__eo_to_smt (mkStrInRe s r)) =
      SmtValue.Boolean (Smtm.native_str_in_re (native_unpack_seq ss) rv) := by
  intro hs hr
  change __smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtValue.Boolean (Smtm.native_str_in_re (native_unpack_seq ss) rv)
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hs, hr]

theorem negated_str_in_re_native_false
    (M : SmtModel) (hM : model_wf M) (s r : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hrTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    eo_interprets M (mkNot (mkStrInRe s r)) true ->
      ∃ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
        native_str_in_re (native_unpack_string ss) rv = false := by
  intro hPrem
  rcases smt_eval_seq_char_of_smt_type_seq_char M hM (__eo_to_smt s) hsTy with
    ⟨ss, hsEval⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r) hrTy with
    ⟨rv, hrEval⟩
  have hFalse :=
    RuleProofs.eo_interprets_not_true_implies_false M (mkStrInRe s r) hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hFalse
  cases hFalse with
  | intro_false _hTy hEval =>
      have hNative :
          native_str_in_re (native_unpack_string ss) rv = false := by
        have hValTy :=
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
            unfold term_has_non_none_type
            rw [hsTy]
            simp)
        have hSSTy :
            __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
          simpa [hsEval, hsTy, __smtx_typeof_value] using hValTy
        have hUnpack :=
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSSTy
        change __smtx_model_eval M
            (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
          SmtValue.Boolean false at hEval
        simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
          hsEval, hrEval] at hEval
        rw [hUnpack] at hEval
        simpa only [← RuleProofs.native_str_in_re_eq_model] using hEval
      exact ⟨ss, rv, hsEval, hrEval, hNative⟩

theorem negated_str_in_re_re_mult_native_false
    (M : SmtModel) (hM : model_wf M) (s r : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hrTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    eo_interprets M (mkNot (mkStrInRe s (mkReMult r))) true ->
      ∃ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
        native_str_in_re (native_unpack_string ss) (native_re_mult rv) = false := by
  intro hPrem
  rcases negated_str_in_re_native_false M hM s (mkReMult r) hsTy
      (smtx_typeof_re_mult_of_reglan r hrTy) hPrem with
    ⟨ss, rvStar, hsEval, hStarEval, hNo⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r) hrTy with
    ⟨rv, hrEval⟩
  have hStarEval' := eval_re_mult_of_reglan M r rv hrEval
  rw [hStarEval'] at hStarEval
  cases hStarEval
  exact ⟨ss, rv, hsEval, hrEval, hNo⟩

theorem negated_str_in_re_re_concat_native_false
    (M : SmtModel) (hM : model_wf M) (s r1 r2 : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hr1Ty : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan) :
    eo_interprets M (mkNot (mkStrInRe s (mkReConcat r1 r2))) true ->
      ∃ ss rv1 rv2,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan rv1 ∧
        __smtx_model_eval M (__eo_to_smt r2) = SmtValue.RegLan rv2 ∧
        native_str_in_re (native_unpack_string ss)
          (native_re_concat rv1 rv2) = false := by
  intro hPrem
  rcases negated_str_in_re_native_false M hM s (mkReConcat r1 r2) hsTy
      (smtx_typeof_re_concat_of_reglan r1 r2 hr1Ty hr2Ty) hPrem with
    ⟨ss, rvConcat, hsEval, hConcatEval, hNo⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r1) hr1Ty with
    ⟨rv1, hr1Eval⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r2) hr2Ty with
    ⟨rv2, hr2Eval⟩
  have hConcatEval' := eval_re_concat_of_reglan M r1 r2 rv1 rv2 hr1Eval hr2Eval
  rw [hConcatEval'] at hConcatEval
  cases hConcatEval
  exact ⟨ss, rv1, rv2, hsEval, hr1Eval, hr2Eval, hNo⟩

theorem eval_substr_of_seq_ints (M : SmtModel)
    (s i n : Term) (ss : SmtSeq) (zi zn : native_Int) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt i) = SmtValue.Numeral zi ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt (mkSubstr s i n)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) zi zn)) := by
  intro hs hi hn
  change __smtx_model_eval M
      (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt i) (__eo_to_smt n)) =
    SmtValue.Seq
      (native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_seq_extract (native_unpack_seq ss) zi zn))
  simp [__smtx_model_eval, __smtx_model_eval_str_substr, hs, hi, hn]

theorem eval_strlen_of_seq (M : SmtModel) (s : Term) (ss : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt (mkStrLen s)) =
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
  intro hs
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (native_seq_len (native_unpack_seq ss))
  simp [__smtx_model_eval, __smtx_model_eval_str_len, hs]

theorem eval_neg_of_ints (M : SmtModel)
    (x y : Term) (zx zy : native_Int) :
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral zx ->
    __smtx_model_eval M (__eo_to_smt y) = SmtValue.Numeral zy ->
    __smtx_model_eval M (__eo_to_smt (mkNeg x y)) =
      SmtValue.Numeral (zx - zy) := by
  intro hx hy
  change __smtx_model_eval M
      (SmtTerm.neg (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.Numeral (zx - zy)
  simp [__smtx_model_eval, __smtx_model_eval__, hx, hy,
    SmtEval.native_zplus, SmtEval.native_zneg, Int.sub_eq_add_neg]

theorem nonneg_of_not_zlt_zero (i : native_Int) :
    (¬ native_zlt i 0 = true) -> 0 <= i := by
  intro hNot
  by_cases hGe : 0 <= i
  · exact hGe
  · have hLt : i < 0 := Int.lt_of_not_ge hGe
    have hBool : native_zlt i 0 = true := by
      simpa [native_zlt, SmtEval.native_zlt] using hLt
    exact False.elim (hNot hBool)

theorem nonneg_of_not_zleq_zero (i : native_Int) :
    (¬ native_zleq i 0 = true) -> 0 <= i := by
  intro hNot
  have hPos : 0 < i := by
    by_cases hPos : 0 < i
    · exact hPos
    · have hLe : i <= 0 := Int.not_lt.mp hPos
      have hBool : native_zleq i 0 = true := by
        simpa [native_zleq, SmtEval.native_zleq] using hLe
      exact False.elim (hNot hBool)
  exact Int.le_of_lt hPos

theorem le_of_not_zlt_true (a b : native_Int) :
    (¬ native_zlt a b = true) -> b <= a := by
  intro hNot
  by_cases hLe : b <= a
  · exact hLe
  · have hLt : a < b := Int.lt_of_not_ge hLe
    have hBool : native_zlt a b = true := by
      simpa [native_zlt, SmtEval.native_zlt] using hLt
    exact False.elim (hNot hBool)

theorem bool_eq_false_of_not_true {b : Bool} :
    (¬ b = true) -> b = false := by
  intro h
  cases b <;> simp at h ⊢

private theorem qforall_idx_eval_true_of_forall_values
    (M : SmtModel) (body : Term)
    (hAll :
      ∀ v : SmtValue,
        __smtx_typeof_value v = SmtType.Int ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push M idxName SmtType.Int v)
          (__eo_to_smt body) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (qforallIdx body)) =
      SmtValue.Boolean true := by
  classical
  change __smtx_model_eval M
      (SmtTerm.not
        (SmtTerm.exists idxName SmtType.Int
          (SmtTerm.not (__eo_to_smt body)))) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval]
  by_cases hEx :
      ∃ v : SmtValue,
        __smtx_typeof_value v = SmtType.Int ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval_not
              (__smtx_model_eval
                (native_model_push M idxName SmtType.Int v)
                (__eo_to_smt body)) =
            SmtValue.Boolean true
  · rcases hEx with ⟨v, hvTy, hvCan, hEvalNot⟩
    have hEval := hAll v hvTy hvCan
    simp [__smtx_model_eval_not, hEval, SmtEval.native_not] at hEvalNot
  · -- `rw` would have to match the goal's `Decidable` instance syntactically;
    -- routing through `congrArg` lets `refine` unify it up to defeq instead
    refine Eq.trans (congrArg __smtx_model_eval_not (dif_neg hEx)) ?_
    simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem re_unfold_neg_star_body_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 : Term) (i : native_Int)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hIdx :
      __smtx_model_eval M (__eo_to_smt idxVar) = SmtValue.Numeral i) :
    eo_interprets M (mkNot (mkStrInRe t (mkReMult r1))) true ->
    __smtx_model_eval M (__eo_to_smt (reUnfoldNegStarBody t r1)) =
      SmtValue.Boolean true := by
  intro hPrem
  rcases negated_str_in_re_re_mult_native_false M hM t r1 ht hr1 hPrem with
    ⟨ss, rv, htEval, hrEval, hNo⟩
  let len : native_Int := native_seq_len (native_unpack_seq ss)
  let leftSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) 0 i)
  let rightSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) i (len - i))
  let leftStr : native_String := native_unpack_string leftSeq
  let rightStr : native_String := native_unpack_string rightSeq
  have hLenEval :
      __smtx_model_eval M (__eo_to_smt (mkStrLen t)) =
        SmtValue.Numeral len := by
    simpa [len] using eval_strlen_of_seq M t ss htEval
  have hNegEval :
      __smtx_model_eval M
          (__eo_to_smt (mkNeg (mkStrLen t) idxVar)) =
        SmtValue.Numeral (len - i) :=
    eval_neg_of_ints M (mkStrLen t) idxVar len i hLenEval hIdx
  have hLeftSubEval :
      __smtx_model_eval M
          (__eo_to_smt (mkSubstr t (Term.Numeral 0) idxVar)) =
        SmtValue.Seq leftSeq := by
    simpa [leftSeq] using
      eval_substr_of_seq_ints M t (Term.Numeral 0) idxVar ss 0 i
        htEval (by
          change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
          simp [__smtx_model_eval]) hIdx
  have hRightSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))) =
        SmtValue.Seq rightSeq := by
    simpa [rightSeq] using
      eval_substr_of_seq_ints M t idxVar
        (mkNeg (mkStrLen t) idxVar) ss i (len - i)
        htEval hIdx hNegEval
  have hSsValid : native_re_str_valid (native_unpack_seq ss) = true := by
    apply native_re_str_valid_unpack_seq_of_typeof_seq_char
    have hValTy :=
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [ht]
        simp)
    simpa [htEval, ht, __smtx_typeof_value] using hValTy
  have hLeftUnpack :
      native_unpack_seq leftSeq =
        impl_native_string_to_values (native_unpack_string leftSeq) := by
    apply native_unpack_seq_eq_values_of_valid
    simpa [leftSeq, native_unpack_seq_pack_seq] using
      native_re_str_valid_extract hSsValid 0 i
  have hRightUnpack :
      native_unpack_seq rightSeq =
        impl_native_string_to_values (native_unpack_string rightSeq) := by
    apply native_unpack_seq_eq_values_of_valid
    simpa [rightSeq, native_unpack_seq_pack_seq] using
      native_re_str_valid_extract hSsValid i (len - i)
  have hLeftInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv) := by
    simpa [leftStr, hLeftUnpack, ← native_str_in_re_eq_model] using
      eval_str_in_re_of_seq_reglan M
        (mkSubstr t (Term.Numeral 0) idxVar) r1 leftSeq rv
        hLeftSubEval hrEval
  have hRightInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe
              (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))
              (mkReMult r1))) =
        SmtValue.Boolean (native_str_in_re rightStr (native_re_mult rv)) := by
    simpa [rightStr, hRightUnpack, ← native_str_in_re_eq_model] using
      eval_str_in_re_of_seq_reglan M
        (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) (mkReMult r1)
        rightSeq (native_re_mult rv) hRightSubEval
        (eval_re_mult_of_reglan M r1 rv hrEval)
  have hIdxEval' :
      native_model_var_lookup M idxName SmtType.Int = SmtValue.Numeral i := by
    change __smtx_model_eval M (SmtTerm.Var idxName SmtType.Int) =
      SmtValue.Numeral i at hIdx
    simpa [__smtx_model_eval] using hIdx
  have hLenEval' :
      __smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.Numeral len := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)) =
      SmtValue.Numeral len at hLenEval
    simpa [__smtx_model_eval] using hLenEval
  have hNegEval' :
      __smtx_model_eval__
          (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
          (native_model_var_lookup M idxName SmtType.Int) =
        SmtValue.Numeral (len - i) := by
    change __smtx_model_eval M
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
          (SmtTerm.Var idxName SmtType.Int)) =
      SmtValue.Numeral (len - i) at hNegEval
    simpa [__smtx_model_eval] using hNegEval
  have hLeftSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0) (native_model_var_lookup M idxName SmtType.Int) =
        SmtValue.Seq leftSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
          (SmtTerm.Var idxName SmtType.Int)) =
      SmtValue.Seq leftSeq at hLeftSubEval
    simpa [__smtx_model_eval] using hLeftSubEval
  have hRightSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (native_model_var_lookup M idxName SmtType.Int)
          (__smtx_model_eval__
            (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
            (native_model_var_lookup M idxName SmtType.Int)) =
        SmtValue.Seq rightSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t)
          (SmtTerm.Var idxName SmtType.Int)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
            (SmtTerm.Var idxName SmtType.Int))) =
      SmtValue.Seq rightSeq at hRightSubEval
    simpa [__smtx_model_eval] using hRightSubEval
  have hLeftInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral 0) (native_model_var_lookup M idxName SmtType.Int))
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
            (SmtTerm.Var idxName SmtType.Int))
          (__eo_to_smt r1)) =
      SmtValue.Boolean (native_str_in_re leftStr rv) at hLeftInEval
    simpa [__smtx_model_eval] using hLeftInEval
  have hRightInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (native_model_var_lookup M idxName SmtType.Int)
            (__smtx_model_eval__
              (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
              (native_model_var_lookup M idxName SmtType.Int)))
          (__smtx_model_eval_re_mult
            (__smtx_model_eval M (__eo_to_smt r1))) =
        SmtValue.Boolean (native_str_in_re rightStr (native_re_mult rv)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t)
            (SmtTerm.Var idxName SmtType.Int)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.Var idxName SmtType.Int)))
          (SmtTerm.re_mult (__eo_to_smt r1))) =
      SmtValue.Boolean (native_str_in_re rightStr (native_re_mult rv)) at hRightInEval
    simpa [__smtx_model_eval] using hRightInEval
  have hNegEval'' :
      __smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral i) =
        SmtValue.Numeral (len - i) := by
    simpa [hLenEval', hIdxEval'] using hNegEval'
  have hLeftSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0) (SmtValue.Numeral i) =
        SmtValue.Seq leftSeq := by
    simpa [hIdxEval'] using hLeftSubEval'
  have hRightSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral i) (SmtValue.Numeral (len - i)) =
        SmtValue.Seq rightSeq := by
    simpa [hIdxEval', hLenEval', hNegEval''] using hRightSubEval'
  have hLeftInEval'' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral 0) (SmtValue.Numeral i))
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv) := by
    simpa [hIdxEval'] using hLeftInEval'
  have hRightInEval'' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral i) (SmtValue.Numeral (len - i)))
          (__smtx_model_eval_re_mult
            (__smtx_model_eval M (__eo_to_smt r1))) =
        SmtValue.Boolean (native_str_in_re rightStr (native_re_mult rv)) := by
    simpa [hIdxEval', hLenEval', hNegEval''] using hRightInEval'
  have hLeftInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq leftSeq)
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv) := by
    simpa [hLeftSubEval''] using hLeftInEval''
  have hRightInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq rightSeq)
          (__smtx_model_eval_re_mult
            (__smtx_model_eval M (__eo_to_smt r1))) =
        SmtValue.Boolean (native_str_in_re rightStr (native_re_mult rv)) := by
    simpa [hRightSubEval''] using hRightInEval''
  change __smtx_model_eval M
      (SmtTerm.or
        (SmtTerm.leq (__eo_to_smt idxVar) (SmtTerm.Numeral 0))
        (SmtTerm.or
          (SmtTerm.lt (SmtTerm.str_len (__eo_to_smt t)) (__eo_to_smt idxVar))
          (SmtTerm.or
            (SmtTerm.not
              (SmtTerm.str_in_re
                (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
                  (__eo_to_smt idxVar))
                (__eo_to_smt r1)))
            (SmtTerm.or
              (SmtTerm.not
                (SmtTerm.str_in_re
                  (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt idxVar)
                    (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
                      (__eo_to_smt idxVar)))
                  (SmtTerm.re_mult (__eo_to_smt r1))))
              (SmtTerm.Boolean false))))) = SmtValue.Boolean true
  by_cases hLe0 : native_zleq i 0 = true
  · simp [__smtx_model_eval,
      __smtx_model_eval_or, __smtx_model_eval_not, __smtx_model_eval_leq,
      __smtx_model_eval_lt, hIdxEval', hLenEval',
      hNegEval'', hLeftSubEval'', hRightSubEval'', hLeftInEvalSeq, hRightInEvalSeq, hLe0,
      SmtEval.native_or, SmtEval.native_not]
  · by_cases hPast : native_zlt len i = true
    · simp [__smtx_model_eval,
        __smtx_model_eval_or, __smtx_model_eval_not, __smtx_model_eval_leq,
        __smtx_model_eval_lt, hIdxEval', hLenEval',
        hNegEval'', hLeftSubEval'', hRightSubEval'', hLeftInEvalSeq, hRightInEvalSeq,
        bool_eq_false_of_not_true hLe0, hPast, SmtEval.native_or,
        SmtEval.native_not]
    · by_cases hLeft : native_str_in_re leftStr rv = true
      · by_cases hRight : native_str_in_re rightStr (native_re_mult rv) = true
        · have hi0 : 0 <= i := nonneg_of_not_zleq_zero i hLe0
          have hile : i <= len := le_of_not_zlt_true len i hPast
          have hSplit :
              leftStr ++ rightStr = native_unpack_string ss := by
            simpa [leftStr, rightStr, leftSeq, rightSeq, len] using
              native_unpack_string_substr_split ss i hi0 hile
          have hWhole :
              native_str_in_re (native_unpack_string ss)
                (native_re_mult rv) = true := by
            rw [← hSplit]
            exact native_str_in_re_re_mult_append_intro leftStr rightStr rv
              hLeft hRight
          rw [hNo] at hWhole
          cases hWhole
        · simp [__smtx_model_eval,
            __smtx_model_eval_or, __smtx_model_eval_not,
            __smtx_model_eval_leq, __smtx_model_eval_lt, hIdxEval',
            hLenEval', hNegEval'', hLeftSubEval'',
            hRightSubEval'',
            hLeftInEvalSeq, hRightInEvalSeq,
            bool_eq_false_of_not_true hLe0,
            bool_eq_false_of_not_true hPast, hLeft,
            bool_eq_false_of_not_true hRight, SmtEval.native_or,
            SmtEval.native_not]
      · simp [__smtx_model_eval,
          __smtx_model_eval_or, __smtx_model_eval_not,
          __smtx_model_eval_leq, __smtx_model_eval_lt, hIdxEval',
          hLenEval', hNegEval'', hLeftSubEval'',
          hRightSubEval'',
          hLeftInEvalSeq, hRightInEvalSeq,
          bool_eq_false_of_not_true hLe0,
          bool_eq_false_of_not_true hPast, bool_eq_false_of_not_true hLeft,
          SmtEval.native_or, SmtEval.native_not]

theorem re_unfold_neg_concat_body_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 r2 tail : Term) (i : native_Int)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2 : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan)
    (hTail : __smtx_typeof (__eo_to_smt tail) = SmtType.RegLan)
    (hTailRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tail))
        (__smtx_model_eval M (__eo_to_smt r2)))
    (hIdx :
      __smtx_model_eval M (__eo_to_smt idxVar) = SmtValue.Numeral i) :
    eo_interprets M (mkNot (mkStrInRe t (mkReConcat r1 r2))) true ->
    __smtx_model_eval M (__eo_to_smt (reUnfoldNegConcatBody t r1 tail)) =
      SmtValue.Boolean true := by
  intro hPrem
  rcases negated_str_in_re_re_concat_native_false M hM t r1 r2 ht hr1 hr2 hPrem with
    ⟨ss, rv1, rv2, htEval, hr1Eval, hr2Eval, hNo⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt tail) hTail with
    ⟨rvTail, hTailEval⟩
  have hTailRelReg :
      RuleProofs.smt_value_rel (SmtValue.RegLan rvTail)
        (SmtValue.RegLan rv2) := by
    simpa [hTailEval, hr2Eval] using hTailRel
  let len : native_Int := native_seq_len (native_unpack_seq ss)
  let leftSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) 0 i)
  let rightSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) i (len - i))
  let leftStr : native_String := native_unpack_string leftSeq
  let rightStr : native_String := native_unpack_string rightSeq
  have hLenEval :
      __smtx_model_eval M (__eo_to_smt (mkStrLen t)) =
        SmtValue.Numeral len := by
    simpa [len] using eval_strlen_of_seq M t ss htEval
  have hNegEval :
      __smtx_model_eval M
          (__eo_to_smt (mkNeg (mkStrLen t) idxVar)) =
        SmtValue.Numeral (len - i) :=
    eval_neg_of_ints M (mkStrLen t) idxVar len i hLenEval hIdx
  have hLeftSubEval :
      __smtx_model_eval M
          (__eo_to_smt (mkSubstr t (Term.Numeral 0) idxVar)) =
        SmtValue.Seq leftSeq := by
    simpa [leftSeq] using
      eval_substr_of_seq_ints M t (Term.Numeral 0) idxVar ss 0 i
        htEval (by
          change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
          simp [__smtx_model_eval]) hIdx
  have hRightSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar))) =
        SmtValue.Seq rightSeq := by
    simpa [rightSeq] using
      eval_substr_of_seq_ints M t idxVar
        (mkNeg (mkStrLen t) idxVar) ss i (len - i)
        htEval hIdx hNegEval
  have hSsValid : native_re_str_valid (native_unpack_seq ss) = true := by
    apply native_re_str_valid_unpack_seq_of_typeof_seq_char
    have hValTy :=
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [ht]
        simp)
    simpa [htEval, ht, __smtx_typeof_value] using hValTy
  have hLeftUnpack :
      native_unpack_seq leftSeq =
        impl_native_string_to_values (native_unpack_string leftSeq) := by
    apply native_unpack_seq_eq_values_of_valid
    simpa [leftSeq, native_unpack_seq_pack_seq] using
      native_re_str_valid_extract hSsValid 0 i
  have hRightUnpack :
      native_unpack_seq rightSeq =
        impl_native_string_to_values (native_unpack_string rightSeq) := by
    apply native_unpack_seq_eq_values_of_valid
    simpa [rightSeq, native_unpack_seq_pack_seq] using
      native_re_str_valid_extract hSsValid i (len - i)
  have hLeftInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe (mkSubstr t (Term.Numeral 0) idxVar) r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    simpa [leftStr, hLeftUnpack, ← native_str_in_re_eq_model] using
      eval_str_in_re_of_seq_reglan M
        (mkSubstr t (Term.Numeral 0) idxVar) r1 leftSeq rv1
        hLeftSubEval hr1Eval
  have hRightInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe
              (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail)) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    simpa [rightStr, hRightUnpack, ← native_str_in_re_eq_model] using
      eval_str_in_re_of_seq_reglan M
        (mkSubstr t idxVar (mkNeg (mkStrLen t) idxVar)) tail
        rightSeq rvTail hRightSubEval hTailEval
  have hIdxEval' :
      native_model_var_lookup M idxName SmtType.Int = SmtValue.Numeral i := by
    change __smtx_model_eval M (SmtTerm.Var idxName SmtType.Int) =
      SmtValue.Numeral i at hIdx
    simpa [__smtx_model_eval] using hIdx
  have hLenEval' :
      __smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.Numeral len := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)) =
      SmtValue.Numeral len at hLenEval
    simpa [__smtx_model_eval] using hLenEval
  have hNegEval' :
      __smtx_model_eval__
          (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
          (native_model_var_lookup M idxName SmtType.Int) =
        SmtValue.Numeral (len - i) := by
    change __smtx_model_eval M
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
          (SmtTerm.Var idxName SmtType.Int)) =
      SmtValue.Numeral (len - i) at hNegEval
    simpa [__smtx_model_eval] using hNegEval
  have hLeftSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0) (native_model_var_lookup M idxName SmtType.Int) =
        SmtValue.Seq leftSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
          (SmtTerm.Var idxName SmtType.Int)) =
      SmtValue.Seq leftSeq at hLeftSubEval
    simpa [__smtx_model_eval] using hLeftSubEval
  have hRightSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (native_model_var_lookup M idxName SmtType.Int)
          (__smtx_model_eval__
            (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
            (native_model_var_lookup M idxName SmtType.Int)) =
        SmtValue.Seq rightSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t)
          (SmtTerm.Var idxName SmtType.Int)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
            (SmtTerm.Var idxName SmtType.Int))) =
      SmtValue.Seq rightSeq at hRightSubEval
    simpa [__smtx_model_eval] using hRightSubEval
  have hLeftInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral 0) (native_model_var_lookup M idxName SmtType.Int))
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
            (SmtTerm.Var idxName SmtType.Int))
          (__eo_to_smt r1)) =
      SmtValue.Boolean (native_str_in_re leftStr rv1) at hLeftInEval
    simpa [__smtx_model_eval] using hLeftInEval
  have hRightInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (native_model_var_lookup M idxName SmtType.Int)
            (__smtx_model_eval__
              (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
              (native_model_var_lookup M idxName SmtType.Int)))
          (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t)
            (SmtTerm.Var idxName SmtType.Int)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.Var idxName SmtType.Int)))
          (__eo_to_smt tail)) =
      SmtValue.Boolean (native_str_in_re rightStr rvTail) at hRightInEval
    simpa [__smtx_model_eval] using hRightInEval
  have hNegEval'' :
      __smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral i) =
        SmtValue.Numeral (len - i) := by
    simpa [hLenEval', hIdxEval'] using hNegEval'
  have hLeftSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0) (SmtValue.Numeral i) =
        SmtValue.Seq leftSeq := by
    simpa [hIdxEval'] using hLeftSubEval'
  have hRightSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral i) (SmtValue.Numeral (len - i)) =
        SmtValue.Seq rightSeq := by
    simpa [hIdxEval', hLenEval', hNegEval''] using hRightSubEval'
  have hLeftInEval'' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral 0) (SmtValue.Numeral i))
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    simpa [hIdxEval'] using hLeftInEval'
  have hRightInEval'' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral i) (SmtValue.Numeral (len - i)))
          (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    simpa [hIdxEval', hLenEval', hNegEval''] using hRightInEval'
  have hLeftInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq leftSeq)
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    simpa [hLeftSubEval''] using hLeftInEval''
  have hRightInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq rightSeq)
          (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    simpa [hRightSubEval''] using hRightInEval''
  change __smtx_model_eval M
      (SmtTerm.or
        (SmtTerm.lt (__eo_to_smt idxVar) (SmtTerm.Numeral 0))
        (SmtTerm.or
          (SmtTerm.lt (SmtTerm.str_len (__eo_to_smt t)) (__eo_to_smt idxVar))
          (SmtTerm.or
            (SmtTerm.not
              (SmtTerm.str_in_re
                (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
                  (__eo_to_smt idxVar))
                (__eo_to_smt r1)))
            (SmtTerm.or
              (SmtTerm.not
                (SmtTerm.str_in_re
                  (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt idxVar)
                    (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
                      (__eo_to_smt idxVar)))
                  (__eo_to_smt tail)))
              (SmtTerm.Boolean false))))) = SmtValue.Boolean true
  by_cases hLt0 : native_zlt i 0 = true
  · simp [__smtx_model_eval,
      __smtx_model_eval_or, __smtx_model_eval_not, __smtx_model_eval_lt,
      hIdxEval', hLenEval', hNegEval'', hLeftSubEval'', hRightSubEval'', hLeftInEvalSeq, hRightInEvalSeq,
      hLt0, SmtEval.native_or, SmtEval.native_not]
  · by_cases hPast : native_zlt len i = true
    · simp [__smtx_model_eval,
        __smtx_model_eval_or, __smtx_model_eval_not, __smtx_model_eval_lt,
        hIdxEval', hLenEval', hNegEval'', hLeftSubEval'', hRightSubEval'', hLeftInEvalSeq, hRightInEvalSeq,
        bool_eq_false_of_not_true hLt0, hPast, SmtEval.native_or,
        SmtEval.native_not]
    · by_cases hLeft : native_str_in_re leftStr rv1 = true
      · by_cases hRight : native_str_in_re rightStr rvTail = true
        · have hi0 : 0 <= i := nonneg_of_not_zlt_zero i hLt0
          have hile : i <= len := le_of_not_zlt_true len i hPast
          have hSplit :
              leftStr ++ rightStr = native_unpack_string ss := by
            simpa [leftStr, rightStr, leftSeq, rightSeq, len] using
              native_unpack_string_substr_split ss i hi0 hile
          have hRightR2 :
              native_str_in_re rightStr rv2 = true :=
            native_str_in_re_of_reglan_rel rightStr rvTail rv2
              hTailRelReg hRight
          have hWhole :
              native_str_in_re (native_unpack_string ss)
                (native_re_concat rv1 rv2) = true := by
            rw [← hSplit]
            exact native_str_in_re_re_concat_intro leftStr rightStr rv1 rv2
              hLeft hRightR2
          rw [hNo] at hWhole
          cases hWhole
        · simp [__smtx_model_eval,
            __smtx_model_eval_or, __smtx_model_eval_not,
            __smtx_model_eval_lt, hIdxEval', hLenEval', hNegEval'',
            hLeftSubEval'', hRightSubEval'', hLeftInEvalSeq, hRightInEvalSeq,
            bool_eq_false_of_not_true hLt0,
            bool_eq_false_of_not_true hPast, hLeft,
            bool_eq_false_of_not_true hRight, SmtEval.native_or,
            SmtEval.native_not]
      · simp [__smtx_model_eval,
          __smtx_model_eval_or, __smtx_model_eval_not,
          __smtx_model_eval_lt, hIdxEval', hLenEval', hNegEval'',
          hLeftSubEval'', hRightSubEval'', hLeftInEvalSeq, hRightInEvalSeq,
          bool_eq_false_of_not_true hLt0,
          bool_eq_false_of_not_true hPast, bool_eq_false_of_not_true hLeft,
          SmtEval.native_or, SmtEval.native_not]

private theorem re_unfold_neg_star_nonempty_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan) :
    eo_interprets M (mkNot (mkStrInRe t (mkReMult r1))) true ->
    __smtx_model_eval M (__eo_to_smt (mkNot (mkEq t (Term.String [])))) =
      SmtValue.Boolean true := by
  intro hPrem
  rcases negated_str_in_re_re_mult_native_false M hM t r1 ht hr1 hPrem with
    ⟨ss, rv, htEval, _hrEval, hNo⟩
  have hNotEmpty : native_unpack_string ss ≠ [] := by
    intro hEmpty
    have hMem :
        native_str_in_re (native_unpack_string ss) (native_re_mult rv) = true := by
      rw [hEmpty]
      exact native_str_in_re_re_mult_empty rv
    rw [hNo] at hMem
    cases hMem
  have hSeqNe : ss ≠ native_pack_string ([] : native_String) := by
    intro hSeq
    apply hNotEmpty
    rw [hSeq]
    simp [native_pack_string, native_unpack_string, native_pack_seq,
      native_unpack_seq]
  have hEqFalse :
      __smtx_model_eval M (__eo_to_smt (mkEq t (Term.String []))) =
        SmtValue.Boolean false := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt t) (SmtTerm.String [])) =
      SmtValue.Boolean false
    simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq, htEval,
      hSeqNe]
  change __smtx_model_eval M
      (SmtTerm.not (SmtTerm.eq (__eo_to_smt t) (SmtTerm.String []))) =
    SmtValue.Boolean true
  simp [__smtx_model_eval, __smtx_model_eval_not, __smtx_model_eval_eq,
    native_veq, htEval, hSeqNe, SmtEval.native_not]

private theorem re_unfold_neg_star_qforall_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hPremVar :
      ∀ N, model_wf N ->
        model_agrees_on_globals M N ->
        eo_interprets N (mkNot (mkStrInRe t (mkReMult r1))) true) :
    __smtx_model_eval M (__eo_to_smt (qforallIdx (reUnfoldNegStarBody t r1))) =
      SmtValue.Boolean true := by
  apply qforall_idx_eval_true_of_forall_values
  intro v hvTy hvCan
  rcases int_value_canonical hvTy with ⟨i, rfl⟩
  let N := native_model_push M idxName SmtType.Int (SmtValue.Numeral i)
  have hWF : __smtx_type_wf SmtType.Int = true := by
    simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and]
  have hN : model_wf N := by
    exact model_total_typed_push hM idxName SmtType.Int
      (SmtValue.Numeral i) hWF rfl (by
        simp [value_canonical, __smtx_value_canonical])
  have hAgree : model_agrees_on_globals M N := by
    exact model_agrees_on_globals_push M idxName SmtType.Int (SmtValue.Numeral i)
  have hIdxEval :
      __smtx_model_eval N (__eo_to_smt idxVar) = SmtValue.Numeral i := by
    change __smtx_model_eval N (SmtTerm.Var idxName SmtType.Int) =
      SmtValue.Numeral i
    simp [__smtx_model_eval, N, native_model_var_lookup, native_model_push]
  exact re_unfold_neg_star_body_eval_true N hN t r1 i ht hr1 hIdxEval
    (hPremVar N hN hAgree)

private theorem re_unfold_neg_star_formula_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hPrem : eo_interprets M (mkNot (mkStrInRe t (mkReMult r1))) true)
    (hPremVar :
      ∀ N, model_wf N ->
        model_agrees_on_globals M N ->
        eo_interprets N (mkNot (mkStrInRe t (mkReMult r1))) true) :
    __smtx_model_eval M (__eo_to_smt (reUnfoldNegStarFormula t r1)) =
      SmtValue.Boolean true := by
  have hNonempty :=
    re_unfold_neg_star_nonempty_eval_true M hM t r1 ht hr1 hPrem
  have hForall :=
    re_unfold_neg_star_qforall_eval_true M hM t r1 ht hr1 hPremVar
  have hNonempty' :
      __smtx_model_eval_not
          (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Seq (native_pack_string ([] : native_String)))) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.not (SmtTerm.eq (__eo_to_smt t) (SmtTerm.String []))) =
      SmtValue.Boolean true at hNonempty
    simpa [__smtx_model_eval] using hNonempty
  have hRight' :
      __smtx_model_eval_and
          (__smtx_model_eval M
            (__eo_to_smt (qforallIdx (reUnfoldNegStarBody t r1))))
          (SmtValue.Boolean true) =
        SmtValue.Boolean true := by
    rw [hForall]
    simp [__smtx_model_eval_and, SmtEval.native_and]
  change __smtx_model_eval M
      (SmtTerm.and
        (SmtTerm.not (SmtTerm.eq (__eo_to_smt t) (SmtTerm.String [])))
        (SmtTerm.and
          (__eo_to_smt (qforallIdx (reUnfoldNegStarBody t r1)))
          (SmtTerm.Boolean true))) =
    SmtValue.Boolean true
  simp [__smtx_model_eval, __smtx_model_eval_and, hNonempty', hForall,
    SmtEval.native_and]

theorem re_unfold_neg_concat_formula_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 r2 : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2 : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan)
    (hList : __eo_is_list (Term.UOp UserOp.re_concat) r2 = Term.Boolean true)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)) =
        SmtType.RegLan)
    (hPremVar :
      ∀ N, model_wf N ->
        model_agrees_on_globals M N ->
        eo_interprets N (mkNot (mkStrInRe t (mkReConcat r1 r2))) true) :
    __smtx_model_eval M (__eo_to_smt (reUnfoldNegConcatFormula t r1 r2)) =
      SmtValue.Boolean true := by
  change __smtx_model_eval M
      (__eo_to_smt
        (qforallIdx
          (reUnfoldNegConcatBody t r1
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)))) =
    SmtValue.Boolean true
  apply qforall_idx_eval_true_of_forall_values
  intro v hvTy hvCan
  rcases int_value_canonical hvTy with ⟨i, rfl⟩
  let N := native_model_push M idxName SmtType.Int (SmtValue.Numeral i)
  have hWF : __smtx_type_wf SmtType.Int = true := by
    simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and]
  have hN : model_wf N := by
    exact model_total_typed_push hM idxName SmtType.Int
      (SmtValue.Numeral i) hWF rfl (by
        simp [value_canonical, __smtx_value_canonical])
  have hAgree : model_agrees_on_globals M N := by
    exact model_agrees_on_globals_push M idxName SmtType.Int (SmtValue.Numeral i)
  have hIdxEval :
      __smtx_model_eval N (__eo_to_smt idxVar) = SmtValue.Numeral i := by
    change __smtx_model_eval N (SmtTerm.Var idxName SmtType.Int) =
      SmtValue.Numeral i
    simp [__smtx_model_eval, N, native_model_var_lookup, native_model_push]
  have hTailRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval N
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)))
        (__smtx_model_eval N (__eo_to_smt r2)) := by
    rcases smt_eval_reglan_of_smt_type_reglan N hN (__eo_to_smt r2) hr2 with
      ⟨rv2, hr2Eval⟩
    exact reConcat_singleton_elim_rel_eval N r2 hList ⟨rv2, hr2Eval⟩
  exact re_unfold_neg_concat_body_eval_true N hN t r1 r2
    (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2) i
    ht hr1 hr2 hTail hTailRel hIdxEval (hPremVar N hN hAgree)

theorem re_unfold_neg_concat_singleton_ne_of_ne_stuck
    (t r1 r2 : Term) :
    __mk_re_unfold_neg t (mkReConcat r1 r2) ≠ Term.Stuck ->
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2 ≠ Term.Stuck := by
  intro h
  change __mk_re_unfold_neg t
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2) ≠
    Term.Stuck at h
  cases t <;> simp [__mk_re_unfold_neg] at h
  all_goals
    have hBody₁ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
    have hBody₂ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hBody₁
    have hBody₃ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hBody₂
    have hBody₄ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hBody₃
    have hOrFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hBody₄
    have hNotRight := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOrFun
    have hRightIn := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNotRight
    exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRightIn

private theorem re_unfold_neg_star_eq_formula_of_ne_stuck (t r1 : Term) :
    __mk_re_unfold_neg t (mkReMult r1) ≠ Term.Stuck ->
    __mk_re_unfold_neg t (mkReMult r1) =
      reUnfoldNegStarFormula t r1 := by
  intro h
  change __mk_re_unfold_neg t
      (Term.Apply (Term.UOp UserOp.re_mult) r1) =
    reUnfoldNegStarFormula t r1
  cases t <;>
    simp [__mk_re_unfold_neg, reUnfoldNegStarFormula,
      reUnfoldNegStarBody, qforallIdx, mkNot, mkAnd, mkOr, mkEq, mkLeq,
      mkLt, mkStrLen, mkSubstr, mkStrInRe, mkNeg, mkReMult] at h ⊢

theorem re_unfold_neg_concat_eq_formula_of_ne_stuck
    (t r1 r2 : Term) :
    __mk_re_unfold_neg t (mkReConcat r1 r2) ≠ Term.Stuck ->
    __mk_re_unfold_neg t (mkReConcat r1 r2) =
      reUnfoldNegConcatFormula t r1 r2 := by
  intro h
  change __mk_re_unfold_neg t
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2) =
    reUnfoldNegConcatFormula t r1 r2
  cases t <;> try (simp [__mk_re_unfold_neg] at h)
  all_goals
    simp [__mk_re_unfold_neg] at h ⊢
    have hBody₁ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
    have hBody₂ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hBody₁
    have hBody₃ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hBody₂
    have hBody₄ := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hBody₃
    have hOrFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hBody₄
    have hNotRight := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOrFun
    have hRightIn := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNotRight
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hBody₁]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hBody₂]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hBody₃]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hBody₄]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hOrFun]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hNotRight]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRightIn]
    try simp [reUnfoldNegConcatFormula, reUnfoldNegConcatBody, qforallIdx,
      mkNot, mkOr, mkLt, mkStrLen, mkSubstr, mkStrInRe, mkNeg, mkReConcat]

private theorem re_unfold_neg_nonstuck_shape (p : Term) :
    __eo_prog_re_unfold_neg (Proof.pf p) ≠ Term.Stuck ->
    ∃ t r,
      p = mkNot (mkStrInRe t r) ∧
      __eo_prog_re_unfold_neg (Proof.pf p) = __mk_re_unfold_neg t r := by
  intro h
  cases p with
  | Apply f inner =>
      cases f with
      | UOp op =>
          cases op <;> try (simp [__eo_prog_re_unfold_neg] at h)
          case not =>
            cases inner with
            | Apply f2 r =>
                cases f2 with
                | Apply op2 t =>
                    cases op2 with
                    | UOp op3 =>
                        cases op3 <;>
                          try (simp at h)
                        case str_in_re =>
                          exact ⟨t, r, rfl, rfl⟩
                    | _ => simp at h
                | _ => simp at h
            | _ => simp at h
      | _ => simp [__eo_prog_re_unfold_neg] at h
  | _ => simp [__eo_prog_re_unfold_neg] at h

end RuleProofs

public theorem cmd_step_re_unfold_neg_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_unfold_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_unfold_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_unfold_neg args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_unfold_neg args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n premises =>
          cases premises with
          | nil =>
              let p := __eo_state_proven_nth s n
              change StepRuleProperties M [p]
                (__eo_prog_re_unfold_neg (Proof.pf p))
              have hProgLocal :
                  __eo_prog_re_unfold_neg (Proof.pf p) ≠ Term.Stuck := by
                change __eo_prog_re_unfold_neg
                    (Proof.pf (__eo_state_proven_nth s n)) ≠
                  Term.Stuck at hProg
                simpa [p] using hProg
              rcases RuleProofs.re_unfold_neg_nonstuck_shape p hProgLocal with
                ⟨t, r, hp, hProgEq⟩
              have hpBool :
                  RuleProofs.eo_has_bool_type
                    (RuleProofs.mkNot (RuleProofs.mkStrInRe t r)) := by
                have h := hPremisesBool p (by simp [p, premiseTermList])
                simpa [hp] using h
              have hInnerBool :
                  RuleProofs.eo_has_bool_type
                    (RuleProofs.mkStrInRe t r) :=
                RuleProofs.eo_has_bool_type_not_arg
                  (RuleProofs.mkStrInRe t r) hpBool
              have hArgs :=
                RuleProofs.str_in_re_args_of_bool_type t r hInnerBool
              have hMkNe : __mk_re_unfold_neg t r ≠ Term.Stuck := by
                intro hStuck
                apply hProgLocal
                rw [hProgEq, hStuck]
              cases r with
              | Apply f rArg =>
                  cases f with
                  | UOp op =>
                      by_cases hop : op = UserOp.re_mult
                      · subst op
                        let r1 := rArg
                        have hr1 :
                            __smtx_typeof (__eo_to_smt r1) =
                              SmtType.RegLan :=
                          RuleProofs.smtx_typeof_re_mult_arg_of_reglan r1
                            hArgs.2
                        have hResultBool :
                            RuleProofs.eo_has_bool_type
                              (RuleProofs.reUnfoldNegStarFormula t r1) :=
                          RuleProofs.re_unfold_neg_star_formula_has_bool_type
                            t r1 hArgs.1 hr1
                        have hFormulaEq :
                            __mk_re_unfold_neg t (RuleProofs.mkReMult r1) =
                              RuleProofs.reUnfoldNegStarFormula t r1 :=
                          RuleProofs.re_unfold_neg_star_eq_formula_of_ne_stuck
                            t r1 hMkNe
                        refine ⟨?_, ?_⟩
                        · intro hTrue
                          have hPremM :
                              eo_interprets M
                                (RuleProofs.mkNot
                                  (RuleProofs.mkStrInRe t
                                    (RuleProofs.mkReMult r1))) true := by
                            have h := hTrue.true_here p (by simp [p])
                            simpa [hp, r1, RuleProofs.mkReMult] using h
                          have hPremVar :
                              ∀ N, model_wf N ->
                                model_agrees_on_globals M N ->
                                eo_interprets N
                                  (RuleProofs.mkNot
                                    (RuleProofs.mkStrInRe t
                                      (RuleProofs.mkReMult r1))) true := by
                            intro N hN hAgree
                            have hAll :=
                              hTrue.true_in_var_model N hN hAgree
                            have h := hAll p (by simp [p])
                            simpa [hp, r1, RuleProofs.mkReMult] using h
                          have hEval :=
                            RuleProofs.re_unfold_neg_star_formula_eval_true
                              M hM t r1 hArgs.1 hr1 hPremM hPremVar
                          have hInterp :
                              eo_interprets M
                                (RuleProofs.reUnfoldNegStarFormula t r1)
                                true := by
                            apply RuleProofs.eo_interprets_of_bool_eval
                              M _ true hResultBool
                            exact hEval
                          simpa [hProgEq, hFormulaEq, r1] using hInterp
                        · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (by simpa [hProgEq, hFormulaEq, r1] using hResultBool)
                      · cases t <;> cases op <;>
                          first
                          | exact False.elim (hop rfl)
                          | simp [__mk_re_unfold_neg] at hMkNe
                  | Apply fHead r1 =>
                      cases fHead with
                      | UOp op =>
                          by_cases hop : op = UserOp.re_concat
                          · subst op
                            let r2 := rArg
                            have hRArgs :
                                __smtx_typeof (__eo_to_smt r1) =
                                    SmtType.RegLan ∧
                                  __smtx_typeof (__eo_to_smt r2) =
                                    SmtType.RegLan :=
                              RuleProofs.smtx_typeof_re_concat_args_of_reglan
                                r1 r2 hArgs.2
                            have hSingletonNe :
                                __eo_list_singleton_elim
                                    (Term.UOp UserOp.re_concat) r2 ≠
                                  Term.Stuck :=
                              RuleProofs.re_unfold_neg_concat_singleton_ne_of_ne_stuck
                                t r1 r2 hMkNe
                            have hList :
                                __eo_is_list (Term.UOp UserOp.re_concat) r2 =
                                  Term.Boolean true :=
                              RuleProofs.reConcat_singleton_elim_list_of_ne_stuck
                                r2 hSingletonNe
                            have hTailTy :
                                __smtx_typeof
                                    (__eo_to_smt
                                      (__eo_list_singleton_elim
                                        (Term.UOp UserOp.re_concat) r2)) =
                                  SmtType.RegLan :=
                              RuleProofs.reConcat_singleton_elim_has_reglan_type
                                r2 hList hRArgs.2
                            have hResultBool :
                                RuleProofs.eo_has_bool_type
                                  (RuleProofs.reUnfoldNegConcatFormula
                                    t r1 r2) := by
                              simpa [RuleProofs.reUnfoldNegConcatFormula] using
                                RuleProofs.re_unfold_neg_concat_formula_has_bool_type
                                  t r1
                                  (__eo_list_singleton_elim
                                    (Term.UOp UserOp.re_concat) r2)
                                  hArgs.1 hRArgs.1 hTailTy
                            have hFormulaEq :
                                __mk_re_unfold_neg t
                                    (RuleProofs.mkReConcat r1 r2) =
                                  RuleProofs.reUnfoldNegConcatFormula
                                    t r1 r2 :=
                              RuleProofs.re_unfold_neg_concat_eq_formula_of_ne_stuck
                                t r1 r2 hMkNe
                            refine ⟨?_, ?_⟩
                            · intro hTrue
                              have hPremVar :
                                  ∀ N, model_wf N ->
                                    model_agrees_on_globals M N ->
                                    eo_interprets N
                                      (RuleProofs.mkNot
                                        (RuleProofs.mkStrInRe t
                                          (RuleProofs.mkReConcat r1 r2)))
                                      true := by
                                intro N hN hAgree
                                have hAll :=
                                  hTrue.true_in_var_model N hN hAgree
                                have h := hAll p (by simp [p])
                                simpa [hp, r2, RuleProofs.mkReConcat] using h
                              have hEval :=
                                RuleProofs.re_unfold_neg_concat_formula_eval_true
                                  M hM t r1 r2 hArgs.1 hRArgs.1 hRArgs.2
                                  hList hTailTy hPremVar
                              have hInterp :
                                  eo_interprets M
                                    (RuleProofs.reUnfoldNegConcatFormula
                                      t r1 r2) true := by
                                apply RuleProofs.eo_interprets_of_bool_eval
                                  M _ true hResultBool
                                exact hEval
                              simpa [hProgEq, hFormulaEq, r2] using hInterp
                            · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (by simpa [hProgEq, hFormulaEq, r2] using hResultBool)
                          · cases t <;> cases op <;>
                              first
                              | exact False.elim (hop rfl)
                              | simp [__mk_re_unfold_neg] at hMkNe
                      | _ => cases t <;> simp [__mk_re_unfold_neg] at hMkNe
                  | _ => cases t <;> simp [__mk_re_unfold_neg] at hMkNe
              | _ =>
                  cases t <;> simp [__mk_re_unfold_neg] at hMkNe
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
