module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrContainsConcatSupport

abbrev containsTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) y

abbrev concatTail (middle suffix : Term) : Term :=
  mkConcat middle suffix

abbrev concatMiddle (pfx middle suffix : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.str_concat) pfx
    (concatTail middle suffix)

theorem str_contains_eval_eq
    (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hX : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hY : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    __smtx_model_eval M (__eo_to_smt (containsTerm x y)) =
      SmtValue.Boolean
        (native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy)) := by
  change __smtx_model_eval M
      (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [StrContainsReplCharSupport.smtx_eval_str_contains_term_eq, hX, hY]
  rfl

theorem str_concat_unpack_eval
    (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hX : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hY : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    ∃ sxy,
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
          SmtValue.Seq sxy ∧
        native_unpack_seq sxy =
          native_unpack_seq sx ++ native_unpack_seq sy := by
  rw [smtx_model_eval_str_concat_term_eq, hX, hY]
  refine ⟨_, rfl, ?_⟩
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    Smtm.native_unpack_pack_seq]

theorem native_seq_contains_append_right
    (xs rest pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    native_seq_contains (xs ++ rest) pat = true := by
  rcases
      (StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat).1 h with
    ⟨before, after, rfl⟩
  simpa [List.append_assoc] using
    StrContainsReplCharSupport.native_seq_contains_of_decomp
      before pat (after ++ rest)

theorem native_seq_contains_append_left
    (pre xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    native_seq_contains (pre ++ xs) pat = true := by
  rcases
      (StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat).1 h with
    ⟨before, after, rfl⟩
  simpa [List.append_assoc] using
    StrContainsReplCharSupport.native_seq_contains_of_decomp
      (pre ++ before) pat after

/-! ### The generated n-ary concatenation shape -/

theorem concat_middle_structure
    (pfx middle suffix U : Term)
    (hTy :
      __eo_typeof (concatMiddle pfx middle suffix) =
        Term.Apply Term.Seq U) :
    __eo_is_list (Term.UOp UserOp.str_concat) pfx =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (concatTail middle suffix) = Term.Boolean true ∧
      concatMiddle pfx middle suffix =
        __eo_list_concat_rec pfx (concatTail middle suffix) ∧
      __eo_typeof
          (__eo_list_concat_rec pfx (concatTail middle suffix)) =
        Term.Apply Term.Seq U ∧
      __eo_typeof middle = Term.Apply Term.Seq U ∧
      __eo_typeof suffix = Term.Apply Term.Seq U := by
  have hNe : concatMiddle pfx middle suffix ≠ Term.Stuck := by
    intro h
    rw [h] at hTy
    cases hTy
  have hFacts :=
    StrConcatClashSupport.concat_clash_rev_list_concat_facts
      pfx (concatTail middle suffix) hNe
  have hEqRec :=
    StrConcatClashSupport.concat_clash_rev_list_concat_eq_rec
      pfx (concatTail middle suffix) hNe
  have hRecTy :
      __eo_typeof
          (__eo_list_concat_rec pfx (concatTail middle suffix)) =
        Term.Apply Term.Seq U := by
    rw [← hEqRec]
    exact hTy
  have hTailTy :
      __eo_typeof (concatTail middle suffix) =
        Term.Apply Term.Seq U :=
    StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
      pfx (concatTail middle suffix) U hFacts.1 hRecTy
  have hArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      middle suffix U hTailTy
  exact ⟨hFacts.1, hFacts.2, hEqRec, hRecTy, hArgs.1, hArgs.2⟩

theorem eo_typeof_str_concat_seq_of_ne_stuck
    (x y : Term)
    (h : __eo_typeof (mkConcat x y) ≠ Term.Stuck) :
    ∃ U,
      __eo_typeof x = Term.Apply Term.Seq U ∧
      __eo_typeof y = Term.Apply Term.Seq U ∧
      __eo_typeof (mkConcat x y) = Term.Apply Term.Seq U := by
  change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof y) ≠
    Term.Stuck at h
  rcases StrConcatClashSupport.eo_typeof_str_concat_args_of_ne_stuck
      (__eo_typeof x) (__eo_typeof y) h with ⟨U, hXTy, hYTy⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [__eo_typeof_str_concat, hXTy, hYTy, __eo_requires,
      __eo_eq, native_ite, native_teq, SmtEval.native_not] at h
  exact ⟨U, hXTy, hYTy,
    StrConcatUnifySupport.eo_typeof_str_concat_result_of_args
      x y U hXTy hYTy hUNe⟩

theorem eo_typeof_list_concat_rec_of_right_seq
    (pfx tail U : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) pfx = Term.Boolean true)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq U)
    (hRecNe : __eo_typeof (__eo_list_concat_rec pfx tail) ≠ Term.Stuck) :
    __eo_typeof (__eo_list_concat_rec pfx tail) =
      Term.Apply Term.Seq U := by
  induction pfx, tail using __eo_list_concat_rec.induct with
  | case1 tail =>
      simp [__eo_is_list] at hList
  | case2 pfx hPfx =>
      have hRec : __eo_list_concat_rec pfx Term.Stuck = Term.Stuck := by
        cases pfx <;> rfl
      rw [hRec] at hRecNe
      exact False.elim (hRecNe rfl)
  | case3 f head rest tail hTailNe ih =>
      have hf : f = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.str_concat) f head rest hList
      subst f
      have hRestList :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) head rest hList
      have hRestTermNe : __eo_list_concat_rec rest tail ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) rest tail hRestList hTailNe
      have hRestRecNe :
          __eo_typeof (__eo_list_concat_rec rest tail) ≠ Term.Stuck := by
        intro hRest
        apply hRecNe
        rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          head rest tail hRestTermNe]
        change __eo_typeof_str_concat (__eo_typeof head)
          (__eo_typeof (__eo_list_concat_rec rest tail)) = Term.Stuck
        rw [hRest]
        cases __eo_typeof head <;> simp [__eo_typeof_str_concat]
      have hRestTy := ih hRestList hTailTy hRestRecNe
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head rest tail hRestTermNe] at hRecNe ⊢
      rcases eo_typeof_str_concat_seq_of_ne_stuck
          head (__eo_list_concat_rec rest tail) hRecNe with
        ⟨V, hHeadTy, hRestTyV, hConcatTy⟩
      have hVU : V = U := by
        rw [hRestTy] at hRestTyV
        exact ((Term.Apply.inj hRestTyV).2).symm
      simpa [hVU] using hConcatTy
  | case4 nil tail hNil hTailNe hNotConcat =>
      simpa [__eo_list_concat_rec] using hTailTy

theorem concat_middle_smt_types
    (pfx middle suffix U : Term)
    (hPrefixTrans : RuleProofs.eo_has_smt_translation pfx)
    (hMiddleTrans : RuleProofs.eo_has_smt_translation middle)
    (hSuffixTrans : RuleProofs.eo_has_smt_translation suffix)
    (hTy :
      __eo_typeof (concatMiddle pfx middle suffix) =
        Term.Apply Term.Seq U) :
    let T := __eo_to_smt_type U
    __smtx_typeof (__eo_to_smt (concatMiddle pfx middle suffix)) =
        SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T := by
  let T := __eo_to_smt_type U
  rcases concat_middle_structure pfx middle suffix U hTy with
    ⟨hPrefixList, _hTailList, hEqRec, hRecEoTy,
      hMiddleEoTy, hSuffixEoTy⟩
  have hMiddleTy :
      __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T := by
    simpa [T] using
      StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof
        middle U hMiddleTrans hMiddleEoTy
  have hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T := by
    simpa [T] using
      StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof
        suffix U hSuffixTrans hSuffixEoTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt (concatTail middle suffix)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq middle suffix T hMiddleTy hSuffixTy
  have hTailTrans :
      RuleProofs.eo_has_smt_translation (concatTail middle suffix) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailTy]
    exact seq_ne_none T
  have hRecTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat_rec pfx (concatTail middle suffix))) =
        SmtType.Seq T := by
    simpa [T] using
      StrLeqConcatNarySupport.smtx_typeof_list_concat_rec_of_eo_type
        pfx (concatTail middle suffix) U hPrefixList hPrefixTrans
        hTailTrans hRecEoTy
  refine ⟨?_, hMiddleTy, hSuffixTy⟩
  rw [hEqRec]
  exact hRecTy

/-! ### Semantic containment through an n-ary prefix -/

theorem eval_contains_concat_left
    (M : SmtModel) (hM : model_wf M)
    (left right needle : Term) (T : SmtType)
    (hLeftTy : __smtx_typeof (__eo_to_smt left) = SmtType.Seq T)
    (hRightTy : __smtx_typeof (__eo_to_smt right) = SmtType.Seq T)
    (hNeedleTy : __smtx_typeof (__eo_to_smt needle) = SmtType.Seq T)
    (hContains :
      __smtx_model_eval M (__eo_to_smt (containsTerm left needle)) =
        SmtValue.Boolean true) :
    __smtx_model_eval M
        (__eo_to_smt (containsTerm (mkConcat left right) needle)) =
      SmtValue.Boolean true := by
  have hLeftEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt left)
      (SmtType.Seq T) hLeftTy (seq_ne_none T) (type_inhabited_seq T)
  have hRightEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt right)
      (SmtType.Seq T) hRightTy (seq_ne_none T) (type_inhabited_seq T)
  have hNeedleEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt needle)
      (SmtType.Seq T) hNeedleTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hLeftEvalTy with ⟨sLeft, hLeftEval⟩
  rcases seq_value_canonical hRightEvalTy with ⟨sRight, hRightEval⟩
  rcases seq_value_canonical hNeedleEvalTy with ⟨sNeedle, hNeedleEval⟩
  have hNative :
      native_seq_contains (native_unpack_seq sLeft)
          (native_unpack_seq sNeedle) = true := by
    rw [str_contains_eval_eq M left needle sLeft sNeedle
      hLeftEval hNeedleEval] at hContains
    exact SmtValue.Boolean.inj hContains
  rcases str_concat_unpack_eval M left right sLeft sRight
      hLeftEval hRightEval with ⟨sConcat, hConcatEval, hConcatUnpack⟩
  rw [str_contains_eval_eq M (mkConcat left right) needle
    sConcat sNeedle hConcatEval hNeedleEval]
  rw [hConcatUnpack,
    native_seq_contains_append_right _ _ _ hNative]

theorem eval_contains_concat_right
    (M : SmtModel) (hM : model_wf M)
    (left right needle : Term) (T : SmtType)
    (hLeftTy : __smtx_typeof (__eo_to_smt left) = SmtType.Seq T)
    (hRightTy : __smtx_typeof (__eo_to_smt right) = SmtType.Seq T)
    (hNeedleTy : __smtx_typeof (__eo_to_smt needle) = SmtType.Seq T)
    (hContains :
      __smtx_model_eval M (__eo_to_smt (containsTerm right needle)) =
        SmtValue.Boolean true) :
    __smtx_model_eval M
        (__eo_to_smt (containsTerm (mkConcat left right) needle)) =
      SmtValue.Boolean true := by
  have hLeftEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt left)
      (SmtType.Seq T) hLeftTy (seq_ne_none T) (type_inhabited_seq T)
  have hRightEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt right)
      (SmtType.Seq T) hRightTy (seq_ne_none T) (type_inhabited_seq T)
  have hNeedleEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt needle)
      (SmtType.Seq T) hNeedleTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hLeftEvalTy with ⟨sLeft, hLeftEval⟩
  rcases seq_value_canonical hRightEvalTy with ⟨sRight, hRightEval⟩
  rcases seq_value_canonical hNeedleEvalTy with ⟨sNeedle, hNeedleEval⟩
  have hNative :
      native_seq_contains (native_unpack_seq sRight)
          (native_unpack_seq sNeedle) = true := by
    rw [str_contains_eval_eq M right needle sRight sNeedle
      hRightEval hNeedleEval] at hContains
    exact SmtValue.Boolean.inj hContains
  rcases str_concat_unpack_eval M left right sLeft sRight
      hLeftEval hRightEval with ⟨sConcat, hConcatEval, hConcatUnpack⟩
  rw [str_contains_eval_eq M (mkConcat left right) needle
    sConcat sNeedle hConcatEval hNeedleEval]
  rw [hConcatUnpack,
    native_seq_contains_append_left _ _ _ hNative]

theorem eval_contains_list_concat_rec
    (M : SmtModel) (hM : model_wf M) :
    ∀ (pfx tail needle : Term) (T : SmtType),
      __eo_is_list (Term.UOp UserOp.str_concat) pfx =
          Term.Boolean true ->
      __smtx_typeof
          (__eo_to_smt (__eo_list_concat_rec pfx tail)) =
        SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt needle) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt (containsTerm tail needle)) =
        SmtValue.Boolean true ->
      __smtx_model_eval M
          (__eo_to_smt
            (containsTerm (__eo_list_concat_rec pfx tail) needle)) =
        SmtValue.Boolean true
  | pfx, tail, needle, T, hList, hRecTy, hNeedleTy, hContains => by
      induction pfx, tail using __eo_list_concat_rec.induct with
      | case1 tail =>
          simp [__eo_is_list] at hList
      | case2 pfx hPrefix =>
          have hRec : __eo_list_concat_rec pfx Term.Stuck = Term.Stuck := by
            cases pfx <;> rfl
          rw [hRec] at hRecTy
          change __smtx_typeof SmtTerm.None = SmtType.Seq T at hRecTy
          rw [TranslationProofs.smtx_typeof_none] at hRecTy
          cases hRecTy
      | case3 f head rest tail hTailNe ih =>
          have hf : f = Term.UOp UserOp.str_concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.str_concat) f head rest hList
          subst f
          have hRestList :
              __eo_is_list (Term.UOp UserOp.str_concat) rest =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.str_concat) head rest hList
          have hRestRecNe :
              __eo_list_concat_rec rest tail ≠ Term.Stuck := by
            have hRecNN :
                __eo_list_concat_rec (mkConcat head rest) tail ≠
                  Term.Stuck :=
              term_ne_stuck_of_smt_type_seq
                (__eo_list_concat_rec (mkConcat head rest) tail) T hRecTy
            intro h
            apply hRecNN
            simp [__eo_list_concat_rec, hTailNe, h, __eo_mk_apply,
              mkConcat]
          have hRecEq :
              __eo_list_concat_rec (mkConcat head rest) tail =
                mkConcat head (__eo_list_concat_rec rest tail) :=
            eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
              head rest tail hRestRecNe
          have hConcatTy :
              __smtx_typeof
                  (__eo_to_smt
                    (mkConcat head (__eo_list_concat_rec rest tail))) =
                SmtType.Seq T := by
            rw [← hRecEq]
            exact hRecTy
          have hArgs :=
            str_concat_args_of_seq_type head
              (__eo_list_concat_rec rest tail) T hConcatTy
          have hRestContains :
              __smtx_model_eval M
                  (__eo_to_smt
                    (containsTerm (__eo_list_concat_rec rest tail) needle)) =
                SmtValue.Boolean true :=
            ih hRestList hArgs.2 hContains
          rw [hRecEq]
          exact eval_contains_concat_right M hM head
            (__eo_list_concat_rec rest tail) needle T hArgs.1 hArgs.2
            hNeedleTy hRestContains
      | case4 nil tail hNil hTailNe hNotConcat =>
          simpa [__eo_list_concat_rec] using hContains

theorem eval_contains_concat_middle
    (M : SmtModel) (hM : model_wf M)
    (pfx middle suffix needle : Term) (T : SmtType)
    (hPrefixList :
      __eo_is_list (Term.UOp UserOp.str_concat) pfx =
        Term.Boolean true)
    (hEqRec :
      concatMiddle pfx middle suffix =
        __eo_list_concat_rec pfx (concatTail middle suffix))
    (hWholeTy :
      __smtx_typeof (__eo_to_smt (concatMiddle pfx middle suffix)) =
        SmtType.Seq T)
    (hMiddleTy :
      __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T)
    (hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T)
    (hNeedleTy :
      __smtx_typeof (__eo_to_smt needle) = SmtType.Seq T)
    (hContains :
      __smtx_model_eval M (__eo_to_smt (containsTerm middle needle)) =
        SmtValue.Boolean true) :
    __smtx_model_eval M
        (__eo_to_smt
          (containsTerm (concatMiddle pfx middle suffix) needle)) =
      SmtValue.Boolean true := by
  have hTailTy :
      __smtx_typeof (__eo_to_smt (concatTail middle suffix)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq middle suffix T hMiddleTy hSuffixTy
  have hTailContains :=
    eval_contains_concat_left M hM middle suffix needle T
      hMiddleTy hSuffixTy hNeedleTy hContains
  have hRecTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat_rec pfx (concatTail middle suffix))) =
        SmtType.Seq T := by
    rw [← hEqRec]
    exact hWholeTy
  have hRecContains :=
    eval_contains_list_concat_rec M hM pfx
      (concatTail middle suffix) needle T hPrefixList hRecTy
      hNeedleTy hTailContains
  rw [hEqRec]
  exact hRecContains

theorem eval_contains_self
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (containsTerm x x)) =
      SmtValue.Boolean true := by
  have hEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x)
      (SmtType.Seq T) hTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hEvalTy with ⟨sx, hEval⟩
  rw [str_contains_eval_eq M x x sx sx hEval hEval,
    native_seq_contains_self]

theorem eval_contains_of_interprets_eq_bool
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (b : native_Bool) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (h : eo_interprets M
      (mkEq (containsTerm x y) (Term.Boolean b)) true) :
    __smtx_model_eval M (__eo_to_smt (containsTerm x y)) =
      SmtValue.Boolean b := by
  have hXEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x)
      (SmtType.Seq T) hXTy (seq_ne_none T) (type_inhabited_seq T)
  have hYEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt y)
      (SmtType.Seq T) hYTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq
            (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.Boolean b)) = SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq,
        StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
        hXEval, hYEval,
        show __smtx_model_eval M (SmtTerm.Boolean b) =
            SmtValue.Boolean b by rw [__smtx_model_eval.eq_def]] at hEval
      have hNative :
          native_seq_contains (native_unpack_seq sx)
              (native_unpack_seq sy) = b := by
        cases b <;>
          simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
            native_veq] using hEval
      rw [str_contains_eval_eq M x y sx sy hXEval hYEval, hNative]

theorem eval_contains_false_of_contained_witness
    (M : SmtModel) (hM : model_wf M)
    (outer candidate witness : Term) (T : SmtType)
    (hOuterTy : __smtx_typeof (__eo_to_smt outer) = SmtType.Seq T)
    (hCandidateTy :
      __smtx_typeof (__eo_to_smt candidate) = SmtType.Seq T)
    (hWitnessTy : __smtx_typeof (__eo_to_smt witness) = SmtType.Seq T)
    (hOuterWitness :
      __smtx_model_eval M (__eo_to_smt (containsTerm outer witness)) =
        SmtValue.Boolean false)
    (hCandidateWitness :
      __smtx_model_eval M
          (__eo_to_smt (containsTerm candidate witness)) =
        SmtValue.Boolean true) :
    __smtx_model_eval M
        (__eo_to_smt (containsTerm outer candidate)) =
      SmtValue.Boolean false := by
  have hOuterEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt outer)
      (SmtType.Seq T) hOuterTy (seq_ne_none T) (type_inhabited_seq T)
  have hCandidateEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt candidate)
      (SmtType.Seq T) hCandidateTy (seq_ne_none T) (type_inhabited_seq T)
  have hWitnessEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt witness)
      (SmtType.Seq T) hWitnessTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hOuterEvalTy with ⟨sOuter, hOuterEval⟩
  rcases seq_value_canonical hCandidateEvalTy with
    ⟨sCandidate, hCandidateEval⟩
  rcases seq_value_canonical hWitnessEvalTy with ⟨sWitness, hWitnessEval⟩
  have hOuterNative :
      native_seq_contains (native_unpack_seq sOuter)
          (native_unpack_seq sWitness) = false := by
    rw [str_contains_eval_eq M outer witness sOuter sWitness
      hOuterEval hWitnessEval] at hOuterWitness
    exact SmtValue.Boolean.inj hOuterWitness
  have hCandidateNative :
      native_seq_contains (native_unpack_seq sCandidate)
          (native_unpack_seq sWitness) = true := by
    rw [str_contains_eval_eq M candidate witness sCandidate sWitness
      hCandidateEval hWitnessEval] at hCandidateWitness
    exact SmtValue.Boolean.inj hCandidateWitness
  have hOuterCandidate :
      native_seq_contains (native_unpack_seq sOuter)
          (native_unpack_seq sCandidate) = false := by
    cases h : native_seq_contains (native_unpack_seq sOuter)
        (native_unpack_seq sCandidate)
    · rfl
    · have hTrans :=
        StrContainsReplCharSupport.native_seq_contains_trans
          (native_unpack_seq sOuter) (native_unpack_seq sCandidate)
          (native_unpack_seq sWitness) h hCandidateNative
      rw [hOuterNative] at hTrans
      contradiction
  rw [str_contains_eval_eq M outer candidate sOuter sCandidate
    hOuterEval hCandidateEval, hOuterCandidate]

theorem eval_eq_false_of_contains_witness
    (M : SmtModel) (hM : model_wf M)
    (x y witness : Term) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hWitnessTy : __smtx_typeof (__eo_to_smt witness) = SmtType.Seq T)
    (hXWitness :
      __smtx_model_eval M (__eo_to_smt (containsTerm x witness)) =
        SmtValue.Boolean true)
    (hYWitness :
      __smtx_model_eval M (__eo_to_smt (containsTerm y witness)) =
        SmtValue.Boolean false) :
    __smtx_model_eval M (__eo_to_smt (mkEq x y)) =
      SmtValue.Boolean false := by
  have hXEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x)
      (SmtType.Seq T) hXTy (seq_ne_none T) (type_inhabited_seq T)
  have hYEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt y)
      (SmtType.Seq T) hYTy (seq_ne_none T) (type_inhabited_seq T)
  have hWitnessEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt witness)
      (SmtType.Seq T) hWitnessTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hWitnessEvalTy with ⟨sw, hWitnessEval⟩
  have hXNative :
      native_seq_contains (native_unpack_seq sx)
          (native_unpack_seq sw) = true := by
    rw [str_contains_eval_eq M x witness sx sw hXEval hWitnessEval] at hXWitness
    exact SmtValue.Boolean.inj hXWitness
  have hYNative :
      native_seq_contains (native_unpack_seq sy)
          (native_unpack_seq sw) = false := by
    rw [str_contains_eval_eq M y witness sy sw hYEval hWitnessEval] at hYWitness
    exact SmtValue.Boolean.inj hYWitness
  have hSeqNe : sx ≠ sy := by
    intro hEq
    subst sy
    rw [hXNative] at hYNative
    contradiction
  change __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.Boolean false
  rw [smtx_eval_eq_term_eq, hXEval, hYEval]
  simp [__smtx_model_eval_eq, native_veq, hSeqNe]

/-! ### Standard typing and interpretation helpers -/

theorem eo_has_bool_type_contains_eq_bool
    (x y : Term) (b : native_Bool) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type
      (mkEq (containsTerm x y) (Term.Boolean b)) := by
  have hContainsTy :
      __smtx_typeof (__eo_to_smt (containsTerm x y)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXTy, hYTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hBoolTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean b)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (containsTerm x y) (Term.Boolean b)
    (by rw [hContainsTy, hBoolTy]) (by rw [hContainsTy]; decide)

theorem eo_interprets_contains_eq_bool_of_eval
    (M : SmtModel) (x y : Term) (b : native_Bool)
    (hBool :
      RuleProofs.eo_has_bool_type
        (mkEq (containsTerm x y) (Term.Boolean b)))
    (hEval :
      __smtx_model_eval M (__eo_to_smt (containsTerm x y)) =
        SmtValue.Boolean b) :
    eo_interprets M (mkEq (containsTerm x y) (Term.Boolean b)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (containsTerm x y) (Term.Boolean b) hBool <| by
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (containsTerm x y)))
        (__smtx_model_eval M (SmtTerm.Boolean b))
      rw [hEval, show __smtx_model_eval M (SmtTerm.Boolean b) =
          SmtValue.Boolean b by rw [__smtx_model_eval.eq_def]]
      exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean b)

end StrContainsConcatSupport
