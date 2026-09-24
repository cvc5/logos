module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrConcatClashSupport

/-!
Equal sequence concatenations with equally long prefixes have equal prefixes.
These are local support lemmas for the CPC string-clash rewrites.
-/

theorem smt_seq_rel_pack_prefix_of_eq_length (T : SmtType) :
    ∀ xs ys xs' ys' : List SmtValue,
      xs.length = ys.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ xs'))
        (native_pack_seq T (ys ++ ys')) ->
      RuleProofs.smt_seq_rel (native_pack_seq T xs)
        (native_pack_seq T ys)
  | [], [], xs', ys', _hLen, _hRel => by
      exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 rfl
  | [], _ :: _, xs', ys', hLen, _hRel => by
      cases hLen
  | _ :: _, [], xs', ys', hLen, _hRel => by
      cases hLen
  | x :: xs, y :: ys, xs', ys', hLen, hRel => by
      have hTailLen : xs.length = ys.length := by
        simpa using Nat.succ.inj hLen
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq] at hRel ⊢
      have hTailRel :=
        smt_seq_rel_pack_prefix_of_eq_length T xs ys xs' ys' hTailLen
          ((RuleProofs.smt_seq_rel_iff_eq _ _).2 hRel.2)
      exact ⟨hRel.1, (RuleProofs.smt_seq_rel_iff_eq _ _).1 hTailRel⟩

theorem smt_value_rel_str_concat_heads_of_eq_length
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq,
    smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hxsEval, hyEval, hysEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sxs)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sys))) =
      SmtValue.Boolean true at hRel
  rw [hsxElem, hsyElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sxs))
    (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys)) at hRel
  have hHeadPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_prefix_of_eq_length T (native_unpack_seq sx)
      (native_unpack_seq sy) (native_unpack_seq sxs)
      (native_unpack_seq sys) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hHeadPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

theorem smt_value_rel_str_concat_head_of_eq_length
    (M : SmtModel) (hM : model_wf M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel
  rw [smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hysEval] at hRel
  change RuleProofs.smt_seq_rel sx
    (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sys)) at hRel
  rw [hsyElem] at hRel
  have hPackedRel : RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx ++ []))
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys)) := by
    simpa using RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx)) sx
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys))
      (RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq T (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack T sx hsxElem)) hRel
  have hHeadPack : RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_prefix_of_eq_length T (native_unpack_seq sx)
      (native_unpack_seq sy) [] (native_unpack_seq sys) hLenXY hPackedRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hHeadPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

abbrev mkStrLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

abbrev concatClashNePremise (x y : Term) : Term :=
  mkEq (mkEq x y) (Term.Boolean false)

abbrev concatClashLenPremise (x y : Term) : Term :=
  mkEq (mkStrLen x) (mkStrLen y)

abbrev concatClashConclusion (x xs y ys : Term) : Term :=
  mkEq (mkEq (mkConcat x xs) (mkConcat y ys)) (Term.Boolean false)

abbrev concatClash2Conclusion (x y ys : Term) : Term :=
  mkEq (mkEq x (mkConcat y ys)) (Term.Boolean false)

theorem eo_typeof_str_concat_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_concat A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_concat] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_concat] at h ⊢
            case Seq =>
              have hEq := RuleProofs.eq_of_requires_eq_true_not_stuck
                x y (Term.Apply Term.Seq x) h
              subst y
              simp

theorem smtx_typeof_seq_of_eo_typeof
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

theorem concat_clash_eo_and_true_split (a b : Term)
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    simp_all [__eo_and, native_and, SmtEval.native_and]
  all_goals
    simp [__eo_requires, native_ite, native_teq, native_not] at h
  all_goals
    split at h <;> exact Term.noConfusion h

theorem concat_clash_requires_guard_eq (x y z : Term)
    (h : __eo_requires x y z ≠ Term.Stuck) : x = y := by
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

theorem concat_clash_smt_seq_types_of_eo_type
    (x xs y ys : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hxsTrans : RuleProofs.eo_has_smt_translation xs)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hysTrans : RuleProofs.eo_has_smt_translation ys)
    (hTy : __eo_typeof (concatClashConclusion x xs y ys) = Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T := by
  change __eo_typeof_eq
      (__eo_typeof (mkEq (mkConcat x xs) (mkConcat y ys))) Term.Bool =
    Term.Bool at hTy
  have hInnerTy :
      __eo_typeof (mkEq (mkConcat x xs) (mkConcat y ys)) = Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  change __eo_typeof_eq (__eo_typeof (mkConcat x xs))
    (__eo_typeof (mkConcat y ys)) = Term.Bool at hInnerTy
  have hConcatSame :
      __eo_typeof (mkConcat x xs) = __eo_typeof (mkConcat y ys) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hInnerTy
  have hConcatNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hInnerTy
  have hLeftNe := hConcatNe.1
  have hRightNe := hConcatNe.2
  change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof xs) ≠
    Term.Stuck at hLeftNe
  change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) ≠
    Term.Stuck at hRightNe
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hLeftNe with
    ⟨U, hxEo, hxsEo⟩
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hRightNe with
    ⟨V, hyEo, hysEo⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hxEo, hxsEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hLeftNe
  have hVNe : V ≠ Term.Stuck := by
    intro hV
    subst V
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hRightNe
  have hLeftEo : __eo_typeof (mkConcat x xs) = Term.Apply Term.Seq U := by
    change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof xs) = _
    simp [hxEo, hxsEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not, hUNe]
  have hRightEo : __eo_typeof (mkConcat y ys) = Term.Apply Term.Seq V := by
    change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) = _
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not, hVNe]
  have hUV : U = V := by
    rw [hLeftEo, hRightEo] at hConcatSame
    injection hConcatSame
  subst V
  refine ⟨__eo_to_smt_type U,
    smtx_typeof_seq_of_eo_typeof x U hxTrans hxEo,
    smtx_typeof_seq_of_eo_typeof xs U hxsTrans hxsEo,
    smtx_typeof_seq_of_eo_typeof y U hyTrans hyEo,
    smtx_typeof_seq_of_eo_typeof ys U hysTrans hysEo⟩

theorem concat_clash2_smt_seq_types_of_eo_type
    (x y ys : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hysTrans : RuleProofs.eo_has_smt_translation ys)
    (hTy : __eo_typeof (concatClash2Conclusion x y ys) = Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T := by
  change __eo_typeof_eq (__eo_typeof (mkEq x (mkConcat y ys))) Term.Bool =
    Term.Bool at hTy
  have hInnerTy : __eo_typeof (mkEq x (mkConcat y ys)) = Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof (mkConcat y ys)) =
    Term.Bool at hInnerTy
  have hSame : __eo_typeof x = __eo_typeof (mkConcat y ys) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hInnerTy
  have hRightNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hInnerTy).2
  change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) ≠
    Term.Stuck at hRightNe
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hRightNe with
    ⟨U, hyEo, hysEo⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hRightNe
  have hRightEo : __eo_typeof (mkConcat y ys) = Term.Apply Term.Seq U := by
    change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) = _
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not, hUNe]
  have hxEo : __eo_typeof x = Term.Apply Term.Seq U := by
    rw [hSame, hRightEo]
  refine ⟨__eo_to_smt_type U,
    smtx_typeof_seq_of_eo_typeof x U hxTrans hxEo,
    smtx_typeof_seq_of_eo_typeof y U hyTrans hyEo,
    smtx_typeof_seq_of_eo_typeof ys U hysTrans hysEo⟩

theorem smtx_model_eval_eq_false_of_not_rel (v w : SmtValue)
    (h : ¬ RuleProofs.smt_value_rel v w) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v w) with
    ⟨b, hb⟩
  cases b with
  | false => exact hb
  | true =>
      exfalso
      apply h
      exact hb

theorem str_len_eq_unpack_length_eq
    (M : SmtModel) (x y : Term)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    ∀ sx sy : SmtSeq,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
      (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
  intro sx sy hxEval hyEval
  have hLenRel := RuleProofs.eo_interprets_eq_rel M
    (mkStrLen x) (mkStrLen y) hLen
  change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt x)))
      (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt y))) at hLenRel
  rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
    hxEval, hyEval] at hLenRel
  unfold RuleProofs.smt_value_rel at hLenRel
  have hLenInt :
      ((native_unpack_seq sx).length : Int) =
        ((native_unpack_seq sy).length : Int) := by
    simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
      native_seq_len, native_veq] using hLenRel
  exact_mod_cast hLenInt

theorem eo_has_bool_type_concat_clash
    (x xs y ys : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatClashConclusion x xs y ys) := by
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x xs)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x xs T hxTy hxsTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat y ys)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y ys T hyTy hysTy
  have hInnerBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x xs) (mkConcat y ys)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hLeftTy, hRightTy]) (by rw [hLeftTy]; exact seq_ne_none T)
  have hFalseBool :
      RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hInnerBool.trans hFalseBool.symm)
    (by rw [hInnerBool]; decide)

theorem eo_has_bool_type_concat_clash2
    (x y ys : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatClash2Conclusion x y ys) := by
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat y ys)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y ys T hyTy hysTy
  have hInnerBool : RuleProofs.eo_has_bool_type
      (mkEq x (mkConcat y ys)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hxTy, hRightTy]) (by rw [hxTy]; exact seq_ne_none T)
  have hFalseBool :
      RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hInnerBool.trans hFalseBool.symm)
    (by rw [hInnerBool]; decide)

theorem concat_clash_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) =
        SmtValue.Boolean false := by
  have hHeadFalse :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M x y hNe
  have hNotRel : ¬ RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) := by
    intro hConcatRel
    have hHeadRel := smt_value_rel_str_concat_heads_of_eq_length
      M hM x xs y ys T hxTy hxsTy hyTy hysTy
      (str_len_eq_unpack_length_eq M x y hLen) hConcatRel
    unfold RuleProofs.smt_value_rel at hHeadRel
    rw [hHeadFalse] at hHeadRel
    cases hHeadRel
  exact smtx_model_eval_eq_false_of_not_rel _ _ hNotRel

theorem concat_clash2_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) =
        SmtValue.Boolean false := by
  have hHeadFalse :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M x y hNe
  have hNotRel : ¬ RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) := by
    intro hConcatRel
    have hHeadRel := smt_value_rel_str_concat_head_of_eq_length
      M hM x y ys T hxTy hyTy hysTy
      (str_len_eq_unpack_length_eq M x y hLen) hConcatRel
    unfold RuleProofs.smt_value_rel at hHeadRel
    rw [hHeadFalse] at hHeadRel
    cases hHeadRel
  exact smtx_model_eval_eq_false_of_not_rel _ _ hNotRel

theorem eo_interprets_concat_clash
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    eo_interprets M (concatClashConclusion x xs y ys) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact eo_has_bool_type_concat_clash x xs y ys T hxTy hxsTy hyTy hysTy
  · have hInnerEval :
        __smtx_model_eval M
            (__eo_to_smt (mkEq (mkConcat x xs) (mkConcat y ys))) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt (mkConcat x xs))
            (__eo_to_smt (mkConcat y ys))) = SmtValue.Boolean false
      rw [smtx_eval_eq_term_eq]
      exact concat_clash_model_eval_eq_false M hM x xs y ys T
        hxTy hxsTy hyTy hysTy hNe hLen
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_def]
    rw [hInnerEval, hFalseEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

theorem eo_interprets_concat_clash2
    (M : SmtModel) (hM : model_wf M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    eo_interprets M (concatClash2Conclusion x y ys) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact eo_has_bool_type_concat_clash2 x y ys T hxTy hyTy hysTy
  · have hInnerEval :
        __smtx_model_eval M (__eo_to_smt (mkEq x (mkConcat y ys))) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (mkConcat y ys))) =
        SmtValue.Boolean false
      rw [smtx_eval_eq_term_eq]
      exact concat_clash2_model_eval_eq_false M hM x y ys T
        hxTy hyTy hysTy hNe hLen
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_def]
    rw [hInnerEval, hFalseEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

/-!
The reverse clash rules use CPC's n-ary list encoding for the expression
`tail ++ head`.  The following helpers reduce that encoding to ordinary
sequence concatenation without exposing those details in the rule proofs.
-/

abbrev concatClashRevTail (head tail : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.str_concat) tail
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
      (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tail)))

abbrev concatClashRevConclusion
    (head tail otherHead otherTail : Term) : Term :=
  mkEq
    (mkEq (concatClashRevTail head tail)
      (concatClashRevTail otherHead otherTail))
    (Term.Boolean false)

abbrev concatClash2RevConclusion (x head tail : Term) : Term :=
  mkEq (mkEq x (concatClashRevTail head tail)) (Term.Boolean false)

theorem concat_clash_rev_list_concat_facts (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hA := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInner := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hZ := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInner
  exact ⟨hA, hZ⟩

theorem concat_clash_rev_list_concat_eq_rec (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hOuter := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInner := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  exact hOuter.trans hInner

theorem concat_clash_rev_smt_typeof_list_of_non_none (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hNN : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
  by_cases hConcat : ∃ head tail : Term, a = mkConcat head tail
  · rcases hConcat with ⟨head, tail, rfl⟩
    exact smt_typeof_str_concat_seq_of_non_none head tail hNN
  · have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) a =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_of_list_true_not_concat_local a hList hConcat
    exact smt_typeof_seq_of_str_concat_list_nil_non_none a hNil hNN

theorem concat_clash_rev_smt_typeof_nil (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtType.Seq T := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hTy]
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

theorem concat_clash_rev_list_concat_rec_right_type_ne_stuck
    (a z : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true) :
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
      __eo_typeof z ≠ Term.Stuck := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hTy
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro hTy
      have hRec : __eo_list_concat_rec a Term.Stuck = Term.Stuck := by
        cases a <;> rfl
      rw [hRec] at hTy
      exact False.elim (hTy (by native_decide))
  | case3 g x y z hZ ih =>
      intro hTy
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
          g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) x y hList
      have hWholeNe :
          __eo_list_concat_rec (mkConcat x y) z ≠ Term.Stuck := by
        intro h
        rw [h] at hTy
        exact hTy rfl
      have hTailNe : __eo_list_concat_rec y z ≠ Term.Stuck := by
        intro h
        apply hWholeNe
        simp [__eo_list_concat_rec, hZ, h, __eo_mk_apply, mkConcat]
      have hRecEq :
          __eo_list_concat_rec (mkConcat x y) z =
            mkConcat x (__eo_list_concat_rec y z) :=
        eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x y z hTailNe
      have hTailTy : __eo_typeof (__eo_list_concat_rec y z) ≠
          Term.Stuck := by
        rw [hRecEq] at hTy
        change __eo_typeof_str_concat (__eo_typeof x)
            (__eo_typeof (__eo_list_concat_rec y z)) ≠ Term.Stuck at hTy
        rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hTy with
          ⟨U, _hxTy, hRecTy⟩
        rw [hRecTy]
        intro h
        cases h
      exact ih hTailList hTailTy
  | case4 nil z hNil hZ hNot =>
      intro hTy
      simpa [__eo_list_concat_rec] using hTy

theorem concat_clash_rev_tail_smt_types
    (head tail : Term)
    (hHeadTrans : RuleProofs.eo_has_smt_translation head)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hTailEoTy : __eo_typeof (concatClashRevTail head tail) ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt head) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (concatClashRevTail head tail)) =
        SmtType.Seq T := by
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tail)
  let z := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head) nil
  have hRevNe : concatClashRevTail head tail ≠ Term.Stuck := by
    intro h
    rw [h] at hTailEoTy
    exact hTailEoTy rfl
  have hLists := concat_clash_rev_list_concat_facts tail z
    (by simpa [concatClashRevTail, z, nil] using hRevNe)
  have hListTail := hLists.1
  have hListZ := hLists.2
  rcases concat_clash_rev_smt_typeof_list_of_non_none tail hListTail
      hTailTrans with ⟨T, hTailTy⟩
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using concat_clash_rev_smt_typeof_nil tail T hTailTy
  have hRevEq : concatClashRevTail head tail =
      __eo_list_concat_rec tail z := by
    simpa [concatClashRevTail, z, nil] using
      concat_clash_rev_list_concat_eq_rec tail z
        (by simpa [concatClashRevTail, z, nil] using hRevNe)
  have hRecEoTy : __eo_typeof (__eo_list_concat_rec tail z) ≠
      Term.Stuck := by
    simpa [hRevEq] using hTailEoTy
  have hZEoTy : __eo_typeof z ≠ Term.Stuck :=
    concat_clash_rev_list_concat_rec_right_type_ne_stuck tail z
      hListTail hRecEoTy
  have hZNe : z ≠ Term.Stuck := by
    intro h
    apply hZEoTy
    rw [h]
    rfl
  have hZEQ : z = mkConcat head nil := by
    simpa [z] using eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) head) nil hZNe
  have hConcatEoTy :
      __eo_typeof_str_concat (__eo_typeof head) (__eo_typeof nil) ≠
        Term.Stuck := by
    simpa [hZEQ, __eo_typeof, __eo_typeof_str_concat, mkConcat] using hZEoTy
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hConcatEoTy with
    ⟨U, hHeadEoTy, hNilEoTy⟩
  have hNilTrans : RuleProofs.eo_has_smt_translation nil := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hNilTy]
    exact seq_ne_none T
  have hHeadTyU := smtx_typeof_seq_of_eo_typeof head U
    hHeadTrans hHeadEoTy
  have hNilTyU := smtx_typeof_seq_of_eo_typeof nil U hNilTrans hNilEoTy
  have hTU : T = __eo_to_smt_type U := by
    have hSeq : SmtType.Seq T = SmtType.Seq (__eo_to_smt_type U) := by
      rw [← hNilTy, hNilTyU]
    injection hSeq
  have hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T := by
    simpa [hTU] using hHeadTyU
  have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    rw [hZEQ]
    exact smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hRevTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail head tail)) =
        SmtType.Seq T := by
    rw [hRevEq]
    exact smt_typeof_list_concat_rec_str_concat_of_seq tail z T
      hListTail hTailTy hZTy
  exact ⟨T, hHeadTy, hTailTy, hRevTy⟩

theorem concat_clash_ne_operands_same_smt_type (x y : Term)
    (hBool : RuleProofs.eo_has_bool_type (concatClashNePremise x y)) :
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  have hOuter :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkEq x y) (Term.Boolean false) hBool
  have hInnerBool : RuleProofs.eo_has_bool_type (mkEq x y) := by
    unfold RuleProofs.eo_has_bool_type
    rw [hOuter.1]
    rfl
  exact RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    x y hInnerBool

theorem concat_clash_rev_tail_eo_types_not_stuck
    (x xs y ys : Term)
    (hTy : __eo_typeof (concatClashRevConclusion x xs y ys) = Term.Bool) :
    __eo_typeof (concatClashRevTail x xs) ≠ Term.Stuck ∧
      __eo_typeof (concatClashRevTail y ys) ≠ Term.Stuck := by
  change __eo_typeof_eq
      (__eo_typeof
        (mkEq (concatClashRevTail x xs) (concatClashRevTail y ys)))
      Term.Bool = Term.Bool at hTy
  have hInner :
      __eo_typeof
          (mkEq (concatClashRevTail x xs) (concatClashRevTail y ys)) =
        Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  change __eo_typeof_eq (__eo_typeof (concatClashRevTail x xs))
      (__eo_typeof (concatClashRevTail y ys)) = Term.Bool at hInner
  exact RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hInner

theorem concat_clash2_rev_tail_eo_type_not_stuck
    (x y ys : Term)
    (hTy : __eo_typeof (concatClash2RevConclusion x y ys) = Term.Bool) :
    __eo_typeof (concatClashRevTail y ys) ≠ Term.Stuck := by
  change __eo_typeof_eq
      (__eo_typeof (mkEq x (concatClashRevTail y ys))) Term.Bool =
    Term.Bool at hTy
  have hInner :
      __eo_typeof (mkEq x (concatClashRevTail y ys)) = Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  change __eo_typeof_eq (__eo_typeof x)
      (__eo_typeof (concatClashRevTail y ys)) = Term.Bool at hInner
  exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hInner).2

theorem smt_value_rel_concat_clash_rev_tail
    (M : SmtModel) (hM : model_wf M) (head tail : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hTailEoTy : __eo_typeof (concatClashRevTail head tail) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail head tail)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat tail head))) := by
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tail)
  let z := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head) nil
  have hRevNe : concatClashRevTail head tail ≠ Term.Stuck := by
    intro h
    rw [h] at hTailEoTy
    exact hTailEoTy rfl
  have hLists := concat_clash_rev_list_concat_facts tail z
    (by simpa [concatClashRevTail, z, nil] using hRevNe)
  have hListTail := hLists.1
  have hListZ := hLists.2
  have hRevEq : concatClashRevTail head tail =
      __eo_list_concat_rec tail z := by
    simpa [concatClashRevTail, z, nil] using
      concat_clash_rev_list_concat_eq_rec tail z
        (by simpa [concatClashRevTail, z, nil] using hRevNe)
  have hZNe : z ≠ Term.Stuck := by
    intro h
    rw [h] at hListZ
    simp [__eo_is_list] at hListZ
  have hZEQ : z = mkConcat head nil := by
    simpa [z] using eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) head) nil hZNe
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using concat_clash_rev_smt_typeof_nil tail T hTailTy
  have hTailNN : __smtx_typeof (__eo_to_smt tail) ≠ SmtType.None := by
    rw [hTailTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation tail hTailNN
  have hEoType : __eo_to_smt_type (__eo_typeof tail) = SmtType.Seq T := by
    rw [← hTypeMatch, hTailTy]
  have hNilIsNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true := by
    simpa [nil] using strConcat_nil_is_list_nil_of_type hEoType
  have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    rw [hZEQ]
    exact smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hRecRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec tail z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat tail z))) :=
    smt_value_rel_list_concat_rec_str_concat M hM tail z T
      hListTail hTailTy hZTy
  have hZRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt z))
      (__smtx_model_eval M (__eo_to_smt head)) := by
    rw [hZEQ]
    exact smt_value_rel_str_concat_list_nil_right_empty M hM head nil T
      hHeadTy hNilIsNil hNilTy
  have hCongr : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat tail z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat tail head))) :=
    smt_value_rel_str_concat_right_congr M hM tail z head T
      hTailTy hZTy hHeadTy hZRel
  rw [hRevEq]
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec tail z)))
    (__smtx_model_eval M (__eo_to_smt (mkConcat tail z)))
    (__smtx_model_eval M (__eo_to_smt (mkConcat tail head)))
    hRecRel hCongr

theorem smt_seq_rel_pack_suffix_of_eq_length (T : SmtType) :
    ∀ xs ys sx sy : List SmtValue,
      sx.length = sy.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ sx))
        (native_pack_seq T (ys ++ sy)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T sx)
        (native_pack_seq T sy)
  | [], [], sx, sy, _hLen, hRel => by
      simpa using hRel
  | [], y :: ys, sx, sy, hLen, hRel => by
      have hTotal := smt_seq_rel_pack_length_eq T T sx ((y :: ys) ++ sy) hRel
      simp at hTotal
      omega
  | x :: xs, [], sx, sy, hLen, hRel => by
      have hTotal := smt_seq_rel_pack_length_eq T T ((x :: xs) ++ sx) sy hRel
      simp at hTotal
      omega
  | x :: xs, y :: ys, sx, sy, hLen, hRel => by
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq] at hRel
      exact smt_seq_rel_pack_suffix_of_eq_length T xs ys sx sy hLen
        ((RuleProofs.smt_seq_rel_iff_eq _ _).2 hRel.2)

theorem smt_value_rel_str_concat_tails_of_eq_length
    (M : SmtModel) (hM : model_wf M) (xs x ys y : Term)
    (T : SmtType)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat xs x)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat ys y))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  have hsxsTy : __smtx_typeof_seq_value sxs = SmtType.Seq T := by
    simpa [hxsEval, __smtx_typeof_value] using hxsValTy
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsysTy : __smtx_typeof_seq_value sys = SmtType.Seq T := by
    simpa [hysEval, __smtx_typeof_value] using hysValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxsElem : __smtx_elem_typeof_seq_value sxs = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxsTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsysElem : __smtx_elem_typeof_seq_value sys = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsysTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY := hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq,
    smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxsEval, hxEval, hysEval, hyEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sxs)
      (native_unpack_seq sxs ++ native_unpack_seq sx)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sys)
      (native_unpack_seq sys ++ native_unpack_seq sy))) =
      SmtValue.Boolean true at hRel
  rw [hsxsElem, hsysElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sxs ++ native_unpack_seq sx))
    (native_pack_seq T (native_unpack_seq sys ++ native_unpack_seq sy)) at hRel
  have hTailPack := smt_seq_rel_pack_suffix_of_eq_length T
    (native_unpack_seq sxs) (native_unpack_seq sys)
    (native_unpack_seq sx) (native_unpack_seq sy) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hTailPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

theorem smt_value_rel_str_concat_tail_of_eq_length
    (M : SmtModel) (hM : model_wf M) (x ys y : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat ys y))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY := hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel
  rw [smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hysEval, hyEval] at hRel
  change RuleProofs.smt_seq_rel sx
    (native_pack_seq (__smtx_elem_typeof_seq_value sys)
      (native_unpack_seq sys ++ native_unpack_seq sy)) at hRel
  have hsysValTy : __smtx_typeof_seq_value sys = SmtType.Seq T := by
    simpa [hysEval, __smtx_typeof_value] using hysValTy
  have hsysElem : __smtx_elem_typeof_seq_value sys = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsysValTy
  rw [hsysElem] at hRel
  have hPackedRel : RuleProofs.smt_seq_rel
      (native_pack_seq T ([] ++ native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sys ++ native_unpack_seq sy)) := by
    simpa using RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx)) sx
      (native_pack_seq T (native_unpack_seq sys ++ native_unpack_seq sy))
      (RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq T (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack T sx hsxElem)) hRel
  have hTailPack := smt_seq_rel_pack_suffix_of_eq_length T []
    (native_unpack_seq sys) (native_unpack_seq sx)
    (native_unpack_seq sy) hLenXY hPackedRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hTailPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

theorem eo_has_bool_type_concat_clash_rev
    (x xs y ys : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail x xs)) =
        SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail y ys)) =
        SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatClashRevConclusion x xs y ys) := by
  have hInnerBool : RuleProofs.eo_has_bool_type
      (mkEq (concatClashRevTail x xs) (concatClashRevTail y ys)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hLeftTy, hRightTy]) (by rw [hLeftTy]; exact seq_ne_none T)
  have hFalseBool : RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hInnerBool.trans hFalseBool.symm)
    (by rw [hInnerBool]; decide)

theorem eo_has_bool_type_concat_clash2_rev
    (x y ys : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail y ys)) =
        SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatClash2RevConclusion x y ys) := by
  have hInnerBool : RuleProofs.eo_has_bool_type
      (mkEq x (concatClashRevTail y ys)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hxTy, hRightTy]) (by rw [hxTy]; exact seq_ne_none T)
  have hFalseBool : RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hInnerBool.trans hFalseBool.symm)
    (by rw [hInnerBool]; decide)

theorem concat_clash_rev_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLeftEoTy : __eo_typeof (concatClashRevTail x xs) ≠ Term.Stuck)
    (hRightEoTy : __eo_typeof (concatClashRevTail y ys) ≠ Term.Stuck)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail x xs)))
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail y ys))) =
        SmtValue.Boolean false := by
  have hHeadFalse :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M x y hNe
  have hLeftNorm := smt_value_rel_concat_clash_rev_tail M hM x xs T
    hxTy hxsTy hLeftEoTy
  have hRightNorm := smt_value_rel_concat_clash_rev_tail M hM y ys T
    hyTy hysTy hRightEoTy
  have hNotRel : ¬ RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail x xs)))
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail y ys))) := by
    intro hRevRel
    have hConcatRel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat xs x)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat ys y))) :=
      RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt (mkConcat xs x)))
        (__smtx_model_eval M (__eo_to_smt (concatClashRevTail x xs)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat ys y)))
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (concatClashRevTail x xs)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat xs x))) hLeftNorm)
        (RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt (concatClashRevTail x xs)))
          (__smtx_model_eval M (__eo_to_smt (concatClashRevTail y ys)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat ys y)))
          hRevRel hRightNorm)
    have hTailRel := smt_value_rel_str_concat_tails_of_eq_length
      M hM xs x ys y T hxsTy hxTy hysTy hyTy
      (str_len_eq_unpack_length_eq M x y hLen) hConcatRel
    unfold RuleProofs.smt_value_rel at hTailRel
    rw [hHeadFalse] at hTailRel
    cases hTailRel
  exact smtx_model_eval_eq_false_of_not_rel _ _ hNotRel

theorem concat_clash2_rev_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hRightEoTy : __eo_typeof (concatClashRevTail y ys) ≠ Term.Stuck)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail y ys))) =
        SmtValue.Boolean false := by
  have hHeadFalse :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M x y hNe
  have hRightNorm := smt_value_rel_concat_clash_rev_tail M hM y ys T
    hyTy hysTy hRightEoTy
  have hNotRel : ¬ RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (concatClashRevTail y ys))) := by
    intro hRevRel
    have hConcatRel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt (mkConcat ys y))) :=
      RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt (concatClashRevTail y ys)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat ys y)))
        hRevRel hRightNorm
    have hTailRel := smt_value_rel_str_concat_tail_of_eq_length
      M hM x ys y T hxTy hysTy hyTy
      (str_len_eq_unpack_length_eq M x y hLen) hConcatRel
    unfold RuleProofs.smt_value_rel at hTailRel
    rw [hHeadFalse] at hTailRel
    cases hTailRel
  exact smtx_model_eval_eq_false_of_not_rel _ _ hNotRel

theorem eo_interprets_concat_clash_rev
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail x xs)) =
        SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail y ys)) =
        SmtType.Seq T)
    (hLeftEoTy : __eo_typeof (concatClashRevTail x xs) ≠ Term.Stuck)
    (hRightEoTy : __eo_typeof (concatClashRevTail y ys) ≠ Term.Stuck)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    eo_interprets M (concatClashRevConclusion x xs y ys) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact eo_has_bool_type_concat_clash_rev x xs y ys T hxTy hxsTy
      hyTy hysTy hLeftTy hRightTy
  · have hInnerEval :
        __smtx_model_eval M
            (__eo_to_smt
              (mkEq (concatClashRevTail x xs)
                (concatClashRevTail y ys))) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt (concatClashRevTail x xs))
            (__eo_to_smt (concatClashRevTail y ys))) =
        SmtValue.Boolean false
      rw [smtx_eval_eq_term_eq]
      exact concat_clash_rev_model_eval_eq_false M hM x xs y ys T
        hxTy hxsTy hyTy hysTy hLeftEoTy hRightEoTy hNe hLen
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_def]
    rw [hInnerEval, hFalseEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

theorem eo_interprets_concat_clash2_rev
    (M : SmtModel) (hM : model_wf M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (concatClashRevTail y ys)) =
        SmtType.Seq T)
    (hRightEoTy : __eo_typeof (concatClashRevTail y ys) ≠ Term.Stuck)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    eo_interprets M (concatClash2RevConclusion x y ys) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact eo_has_bool_type_concat_clash2_rev x y ys T hxTy hyTy hysTy
      hRightTy
  · have hInnerEval :
        __smtx_model_eval M
            (__eo_to_smt (mkEq x (concatClashRevTail y ys))) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt x)
            (__eo_to_smt (concatClashRevTail y ys))) =
        SmtValue.Boolean false
      rw [smtx_eval_eq_term_eq]
      exact concat_clash2_rev_model_eval_eq_false M hM x y ys T
        hxTy hyTy hysTy hRightEoTy hNe hLen
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_def]
    rw [hInnerEval, hFalseEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

end StrConcatClashSupport
