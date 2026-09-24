module

public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs
namespace ReUnfoldNegSupport

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
  by_cases hArg : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan
  · exact hArg
  · simp [hArg, native_ite, native_Teq] at hTy

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
  by_cases hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan <;>
    by_cases hs : __smtx_typeof (__eo_to_smt s) = SmtType.RegLan
  · exact ⟨hr, hs⟩
  · simp [hr, hs, native_ite, native_Teq] at hTy
  · simp [hr, native_ite, native_Teq] at hTy
  · simp [hr, native_ite, native_Teq] at hTy

theorem smtx_typeof_str_in_re_of_seq_reglan (s r : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type (mkStrInRe s r) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtType.Bool
  rw [typeof_str_in_re_eq]
  simp [hs, hr, native_ite, native_Teq]

theorem smtx_typeof_str_len_of_seq_char (s : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (mkStrLen s)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int
  rw [typeof_str_len_eq]
  simp [hs, __smtx_typeof_seq_op_1_ret]

theorem smtx_typeof_substr_of_seq_char (s i n : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hi : __smtx_typeof (__eo_to_smt i) = SmtType.Int)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (mkSubstr s i n)) =
      SmtType.Seq SmtType.Char := by
  change __smtx_typeof
      (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt i) (__eo_to_smt n)) =
    SmtType.Seq SmtType.Char
  rw [typeof_str_substr_eq]
  simp [__smtx_typeof_str_substr, hs, hi, hn]

theorem smtx_typeof_neg_of_int (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (mkNeg x y)) = SmtType.Int := by
  simpa [mkNeg, __eo_to_smt, __smtx_typeof] using smtx_typeof_neg_int (__eo_to_smt x) (__eo_to_smt y) hx hy

private theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq,
        native_unpack_seq_pack_seq T xs]

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
  have hModelExt : ∀ str : native_String,
      native_string_valid str = true ->
        Smtm.native_str_in_re (impl_native_string_to_values str) r =
          Smtm.native_str_in_re (impl_native_string_to_values str) s := by
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
    simpa [__smtx_model_eval_eq] using hRel
  have hExt : native_str_in_re str r = native_str_in_re str s := by
    simpa only [← RuleProofs.native_str_in_re_eq_model] using
      hModelExt str hValid
  simpa [hExt] using hMem

theorem reConcat_nil_eval_empty_of_is_list_nil_true
    (M : SmtModel) (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.RegLan (native_str_to_re ([] : native_String)) := by
  cases nil <;> try (simp only [__eo_is_list_nil] at hNil; cases hNil)
  case Apply f x =>
    cases f <;> try (simp only [__eo_is_list_nil] at hNil; cases hNil)
    case UOp op =>
      cases op <;> try (simp only [__eo_is_list_nil] at hNil; cases hNil)
      case str_to_re =>
        cases x <;> try (simp only [__eo_is_list_nil] at hNil; cases hNil)
        case String s =>
          cases s with
          | nil =>
              change __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.String [])) =
                SmtValue.RegLan (native_str_to_re ([] : native_String))
              simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                native_str_to_re, impl_native_re_of_list, native_pack_string,
                native_pack_seq, native_unpack_seq,
                impl_native_string_to_values]
          | cons _ _ =>
              simp only [__eo_is_list_nil] at hNil
              cases hNil

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
          | cons _ _ =>
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
            | Boolean _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Numeral _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Rational _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Binary _ _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Fun _ _ _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Char _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Seq _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Map _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Set _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | UValue _ _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | DtCons _ _ _ =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_concat, hHeadEval, hTailEval] at hConcatEval'
            | Apply _ _ =>
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

theorem bool_eq_false_of_not_true {b : Bool} :
    (¬ b = true) -> b = false := by
  intro h
  cases b <;> simp at h ⊢

end ReUnfoldNegSupport
end RuleProofs
