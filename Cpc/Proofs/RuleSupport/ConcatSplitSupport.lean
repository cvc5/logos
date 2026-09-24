module

public import Cpc.Proofs.RuleSupport.StrConcatSupport
import all Cpc.Proofs.RuleSupport.StrConcatSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev concatSplitNormalize (rev x : Term) : Term :=
  __eo_ite rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))
    (__str_nary_intro x)

abbrev concatSplitHead (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatSplitNormalize rev x)
    (Term.Numeral 0)

abbrev mkStrLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

abbrev mkNot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) x

abbrev mkOr (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y

abbrev mkAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

abbrev mkGt (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y

abbrev mkGeq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y

abbrev mkNeg (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y

abbrev mkSubstr (s i n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) i) n

abbrev mkIte (c t e : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e

abbrev concatSplitRaw (tHead sHead rev : Term) : Term :=
  __str_unify_split tHead sHead rev

abbrev concatSplitTerm (tHead sHead rev : Term) : Term :=
  __eo_mk_apply (Term.UOp UserOp._at_purify) (concatSplitRaw tHead sHead rev)

abbrev concatSplitRawFalseBody (tHead sHead : Term) : Term :=
  let lt := mkStrLen tHead
  let ls := mkStrLen sHead
  mkIte (mkGeq lt ls)
    (mkSubstr tHead ls (mkNeg lt ls))
    (mkSubstr sHead lt (mkNeg ls lt))

abbrev concatSplitRawTrueBody (tHead sHead : Term) : Term :=
  let lt := mkStrLen tHead
  let ls := mkStrLen sHead
  mkIte (mkGeq lt ls)
    (mkSubstr tHead (Term.Numeral 0) (mkNeg lt ls))
    (mkSubstr sHead (Term.Numeral 0) (mkNeg ls lt))

abbrev concatSplitFormula (rev tHead sHead : Term) : Term :=
  let split := concatSplitTerm tHead sHead rev
  let splitTy := __eo_typeof split
  let splitCons := __eo_mk_apply (Term.UOp UserOp.str_concat) split
  let tCons := __eo_mk_apply (Term.UOp UserOp.str_concat) tHead
  let nilSplit := __eo_nil (Term.UOp UserOp.str_concat) splitTy
  let sCons := __eo_mk_apply (Term.UOp UserOp.str_concat) sHead
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.or)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.eq) tHead)
            (__eo_ite rev
              (__eo_mk_apply splitCons (__eo_mk_apply sCons nilSplit))
              (__eo_mk_apply sCons
                (__eo_mk_apply splitCons
                  (__eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof sHead)))))))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.eq) sHead)
              (__eo_ite rev
                (__eo_mk_apply splitCons (__eo_mk_apply tCons nilSplit))
                (__eo_mk_apply tCons
                  (__eo_mk_apply splitCons
                    (__eo_nil (Term.UOp UserOp.str_concat)
                      (__eo_typeof tHead)))))))
          (Term.Boolean false))))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.UOp UserOp.not)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.eq) split)
            (__seq_empty splitTy))))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.gt)
            (__eo_mk_apply (Term.UOp UserOp.str_len) split))
          (Term.Numeral 0)))
        (Term.Boolean true)))

abbrev concatSplitFalseFormula (tHead sHead : Term) : Term :=
  let split := concatSplitTerm tHead sHead (Term.Boolean false)
  mkAnd
    (mkOr
      (mkEq tHead
        (mkConcat sHead
          (mkConcat split
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead)))))
      (mkOr
        (mkEq sHead
          (mkConcat tHead
            (mkConcat split
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tHead)))))
        (Term.Boolean false)))
    (mkAnd
      (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))

abbrev concatSplitTrueFormula (tHead sHead : Term) : Term :=
  let split := concatSplitTerm tHead sHead (Term.Boolean true)
  mkAnd
    (mkOr
      (mkEq tHead
        (mkConcat split
          (mkConcat sHead
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split)))))
      (mkOr
        (mkEq sHead
          (mkConcat split
            (mkConcat tHead
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split)))))
        (Term.Boolean false)))
    (mkAnd
      (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))

abbrev concatSplitBody (rev t s tc sc : Term) : Term :=
  let sHead := concatSplitHead rev s
  let tHead := concatSplitHead rev t
  __eo_requires tHead tc <|
    __eo_requires sHead sc <|
      concatSplitFormula rev tHead sHead

theorem eo_prog_concat_split_eq_of_ne_stuck
    (rev t s tc sc : Term)
    (hProg :
      __eo_prog_concat_split rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
        Term.Stuck) :
    __eo_prog_concat_split rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) =
      concatSplitFormula rev tc sc ∧
      concatSplitHead rev t = tc ∧ concatSplitHead rev s = sc := by
  have hProgBody :
      __eo_prog_concat_split rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) =
        concatSplitBody rev t s tc sc := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals
      simp [__eo_prog_concat_split, concatSplitBody, concatSplitFormula,
        concatSplitHead, concatSplitNormalize, concatSplitTerm, concatSplitRaw]
  have hBodyNe : concatSplitBody rev t s tc sc ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadT :
      concatSplitHead rev t = tc :=
    eo_requires_eq_of_ne_stuck (concatSplitHead rev t) tc
      (__eo_requires (concatSplitHead rev s) sc
        (concatSplitFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s))) hBodyNe
  have hInnerNe :
      __eo_requires (concatSplitHead rev s) sc
        (concatSplitFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s)) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (concatSplitHead rev t) tc
      _ hBodyNe
  have hHeadS :
      concatSplitHead rev s = sc :=
    eo_requires_eq_of_ne_stuck (concatSplitHead rev s) sc _ hInnerNe
  have hOuterEq :
      concatSplitBody rev t s tc sc =
        __eo_requires (concatSplitHead rev s) sc
          (concatSplitFormula rev (concatSplitHead rev t)
            (concatSplitHead rev s)) :=
    eo_requires_eq_result_of_ne_stuck (concatSplitHead rev t) tc
      (__eo_requires (concatSplitHead rev s) sc
        (concatSplitFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s))) hBodyNe
  have hInnerEq :
      __eo_requires (concatSplitHead rev s) sc
          (concatSplitFormula rev (concatSplitHead rev t)
            (concatSplitHead rev s)) =
        concatSplitFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s) :=
    eo_requires_eq_result_of_ne_stuck (concatSplitHead rev s) sc
      (concatSplitFormula rev (concatSplitHead rev t)
        (concatSplitHead rev s)) hInnerNe
  have hFormula :
      __eo_prog_concat_split rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) =
        concatSplitFormula rev tc sc := by
    rw [hProgBody, hOuterEq, hInnerEq, hHeadT, hHeadS]
  exact ⟨hFormula, hHeadT, hHeadS⟩

theorem list_nth_zero_eq_cons_of_ne_stuck (f a x : Term)
    (hNthEq : __eo_list_nth f a (Term.Numeral 0) = x)
    (hNthNe : __eo_list_nth f a (Term.Numeral 0) ≠ Term.Stuck) :
    ∃ tail,
      a = Term.Apply (Term.Apply f x) tail ∧
        __eo_is_list f tail = Term.Boolean true := by
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral 0)) ≠ Term.Stuck := by
    simpa [__eo_list_nth] using hNthNe
  have hList : __eo_is_list f a = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hRecNe : __eo_list_nth_rec a (Term.Numeral 0) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hReqEq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral 0)) =
        __eo_list_nth_rec a (Term.Numeral 0) :=
    eo_requires_eq_result_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hRecEq : __eo_list_nth_rec a (Term.Numeral 0) = x := by
    rw [__eo_list_nth] at hNthEq
    rw [hReqEq] at hNthEq
    exact hNthEq
  cases a with
  | Stuck =>
      simp [__eo_list_nth_rec] at hRecNe
  | Apply g tail =>
      cases g with
      | Apply f' head =>
          have hHead : head = x := by
            simpa [__eo_list_nth_rec] using hRecEq
          have hFEq : f' = f :=
            eo_is_list_cons_head_eq_of_true f f' head tail hList
          subst head
          subst f'
          exact ⟨tail, rfl,
            eo_is_list_tail_true_of_cons_self f x tail hList⟩
      | _ =>
          simp [__eo_list_nth_rec] at hRecNe
  | _ =>
      simp [__eo_list_nth_rec] at hRecNe

theorem len_eq_seq_types_of_bool (x y : Term)
    (hLenBool : RuleProofs.eo_has_bool_type (mkEq (mkStrLen x) (mkStrLen y))) :
    ∃ T U,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq U := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrLen x) (mkStrLen y) hLenBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkStrLen y)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hLeftTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof] using hLeftNN
  have hRightTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof] using hRightNN
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt x)) hLeftTerm with
    ⟨T, hxTy⟩
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt y)) hRightTerm with
    ⟨U, hyTyU⟩
  exact ⟨T, U, hxTy, hyTyU⟩

theorem str_nary_intro_cons_seq_types_of_head_seq
    (x head tail : Term) (T : SmtType)
    (hIntroEq : __str_nary_intro x = mkConcat head tail)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
  have hIntroNe : __str_nary_intro x ≠ Term.Stuck := by
    rw [hIntroEq]
    simp [mkConcat]
  by_cases hConcat : ∃ h tl : Term, x = mkConcat h tl
  · rcases hConcat with ⟨h, tl, rfl⟩
    rcases str_concat_args_of_non_none h tl hxNN with ⟨U, hhTy, htlTy⟩
    have hxTyU :
        __smtx_typeof (__eo_to_smt (mkConcat h tl)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq h tl U hhTy htlTy
    have hIntroNN :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) ≠
          SmtType.None :=
      str_nary_intro_concat_has_smt_translation h tl hxNN
    have hIntroTyU :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) =
          SmtType.Seq U :=
      smt_typeof_str_nary_intro_of_seq (mkConcat h tl) U hxTyU hIntroNN
    have hResultTyU :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) =
          SmtType.Seq U := by
      simpa [hIntroEq] using hIntroTyU
    rcases str_concat_args_of_seq_type head tail U hResultTyU with
      ⟨hHeadTyU, hTailTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hHeadTyU, hHeadTy]
      injection hSeq
    exact ⟨by simpa [hUT] using hxTyU, by simpa [hUT] using hTailTyU⟩
  · rcases str_nary_intro_not_str_concat_cases_typeof_empty x hConcat hIntroNe with
      hIntroSelf | ⟨hIntroCons, _hEmptyNil⟩
    · rw [hIntroSelf] at hIntroEq
      exact False.elim (hConcat ⟨head, tail, hIntroEq⟩)
    · rw [hIntroCons] at hIntroEq
      injection hIntroEq with hFun hTailEq
      injection hFun with _ hHeadEq
      subst head
      subst tail
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := hHeadTy
      rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T
          hxTy with
        ⟨hTInh, hTWf⟩
      have hEmptyNN :
          __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
            SmtType.None :=
        seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
          hTInh hTWf
      exact ⟨hxTy,
        by
          simpa using smt_typeof_seq_empty_typeof x T hxTy hEmptyNN⟩

theorem eo_is_list_nil_str_concat_of_list_true_not_concat
    (x : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
      Term.Boolean true := by
  cases x with
  | Stuck =>
      simp [__eo_is_list] at hList
  | Apply f a =>
      cases f with
      | Apply g b =>
          by_cases hg : g = Term.UOp UserOp.str_concat
          · subst g
            exact False.elim (hNotConcat ⟨b, a, rfl⟩)
          · simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
              __eo_requires, native_ite, SmtEval.native_not, native_teq] at hList
            exact False.elim (hg hList.1.symm)
      | _ =>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
            __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
            native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList
  | String s =>
      simpa [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        native_ite, SmtEval.native_not, native_teq, __eo_eq] using hList
  | UOp1 op A =>
      cases op <;>
        simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
          __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
          native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList ⊢
  | _ =>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList ⊢

theorem str_nary_intro_rev_cons_seq_types_of_head_seq
    (x head tail : Term) (T : SmtType)
    (hRevIntroEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        mkConcat head tail)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
  have hRevIntroNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck := by
    rw [hRevIntroEq]
    simp [mkConcat]
  have hIntroNe : __str_nary_intro x ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRevIntroNe
  by_cases hConcat : ∃ h tl : Term, x = mkConcat h tl
  · rcases hConcat with ⟨h, tl, rfl⟩
    rcases str_concat_args_of_non_none h tl hxNN with ⟨U, hhTy, htlTy⟩
    have hxTyU :
        __smtx_typeof (__eo_to_smt (mkConcat h tl)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq h tl U hhTy htlTy
    have hIntroNN :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) ≠
          SmtType.None :=
      str_nary_intro_concat_has_smt_translation h tl hxNN
    have hIntroTyU :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) =
          SmtType.Seq U :=
      smt_typeof_str_nary_intro_of_seq (mkConcat h tl) U hxTyU hIntroNN
    have hIntroList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_nary_intro (mkConcat h tl)) =
          Term.Boolean true :=
      eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__str_nary_intro (mkConcat h tl)) hRevIntroNe
    have hRevIntroTyU :
        __smtx_typeof
            (__eo_to_smt
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat h tl)))) =
          SmtType.Seq U :=
      smt_typeof_list_rev_str_concat_of_seq
        (__str_nary_intro (mkConcat h tl)) U hIntroList hIntroTyU
        hRevIntroNe
    have hResultTyU :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) =
          SmtType.Seq U := by
      simpa [hRevIntroEq] using hRevIntroTyU
    rcases str_concat_args_of_seq_type head tail U hResultTyU with
      ⟨hHeadTyU, hTailTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hHeadTyU, hHeadTy]
      injection hSeq
    exact ⟨by simpa [hUT] using hxTyU, by simpa [hUT] using hTailTyU⟩
  · rcases str_nary_intro_not_str_concat_cases_typeof_empty x hConcat hIntroNe with
      hIntroSelf | ⟨hIntroCons, _hEmptyNil⟩
    · have hRevEq :
          __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
            __str_nary_intro x :=
        eo_list_rev_str_nary_intro_eq_of_not_str_concat x hConcat
          hIntroNe hRevIntroNe
      rw [hRevEq, hIntroSelf] at hRevIntroEq
      exact False.elim (hConcat ⟨head, tail, hRevIntroEq⟩)
    · have hRevEq :
          __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
            __str_nary_intro x :=
        eo_list_rev_str_nary_intro_eq_of_not_str_concat x hConcat
          hIntroNe hRevIntroNe
      rw [hRevEq, hIntroCons] at hRevIntroEq
      injection hRevIntroEq with hFun hTailEq
      injection hFun with _ hHeadEq
      subst head
      subst tail
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := hHeadTy
      rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T
          hxTy with
        ⟨hTInh, hTWf⟩
      have hEmptyNN :
          __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
            SmtType.None :=
        seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
          hTInh hTWf
      exact ⟨hxTy,
        by
          simpa using smt_typeof_seq_empty_typeof x T hxTy hEmptyNN⟩

theorem eo_list_nth_arg_ne_stuck_of_ne_stuck
    (f a i : Term)
    (hNth : __eo_list_nth f a i ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a i) ≠ Term.Stuck := by
    simpa [__eo_list_nth] using hNth
  have hIsNe : __eo_is_list f a ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a i) hReq
  intro hA
  subst a
  cases f <;> simp [__eo_is_list] at hIsNe

theorem concatSplitNormalize_ne_stuck_of_head_ne_stuck
    (rev x : Term)
    (hHead : concatSplitHead rev x ≠ Term.Stuck) :
    concatSplitNormalize rev x ≠ Term.Stuck := by
  exact eo_list_nth_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.str_concat) (concatSplitNormalize rev x)
    (Term.Numeral 0) hHead

theorem concatSplit_rev_cases_of_prog_ne_stuck
    (rev t s tc sc : Term)
    (hProg :
      __eo_prog_concat_split rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
        Term.Stuck)
    (htcNe : tc ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_split_eq_of_ne_stuck rev t s tc sc hProg with
    ⟨_, hHeadT, _⟩
  have hHeadNe : concatSplitHead rev t ≠ Term.Stuck := by
    rw [hHeadT]
    exact htcNe
  have hNormNe : concatSplitNormalize rev t ≠ Term.Stuck :=
    concatSplitNormalize_ne_stuck_of_head_ne_stuck rev t hHeadNe
  have hIteNe :
      __eo_ite rev
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (__str_nary_intro t) ≠ Term.Stuck := by
    simpa [concatSplitNormalize] using hNormNe
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
    (__str_nary_intro t) hIteNe

theorem smtx_typeof_str_len_seq
    (s : SmtTerm) (T : SmtType)
    (hs : __smtx_typeof s = SmtType.Seq T) :
    __smtx_typeof (SmtTerm.str_len s) = SmtType.Int := by
  rw [typeof_str_len_eq]
  simp [hs, __smtx_typeof_seq_op_1_ret]

theorem smtx_typeof_str_substr_seq
    (s i n : SmtTerm) (T : SmtType)
    (hs : __smtx_typeof s = SmtType.Seq T)
    (hi : __smtx_typeof i = SmtType.Int)
    (hn : __smtx_typeof n = SmtType.Int) :
    __smtx_typeof (SmtTerm.str_substr s i n) = SmtType.Seq T := by
  rw [typeof_str_substr_eq]
  simp [__smtx_typeof_str_substr, hs, hi, hn]

theorem smtx_typeof_str_concat_seq
    (x y : SmtTerm) (T : SmtType)
    (hx : __smtx_typeof x = SmtType.Seq T)
    (hy : __smtx_typeof y = SmtType.Seq T) :
    __smtx_typeof (SmtTerm.str_concat x y) = SmtType.Seq T := by
  rw [typeof_str_concat_eq]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hx, hy]

theorem smtx_typeof_neg_int
    (x y : SmtTerm)
    (hx : __smtx_typeof x = SmtType.Int)
    (hy : __smtx_typeof y = SmtType.Int) :
    __smtx_typeof (SmtTerm.neg x y) = SmtType.Int := by
  rw [typeof_neg_eq]
  simp [__smtx_typeof_arith_overload_op_2, hx, hy]

theorem smtx_typeof_geq_int
    (x y : SmtTerm)
    (hx : __smtx_typeof x = SmtType.Int)
    (hy : __smtx_typeof y = SmtType.Int) :
    __smtx_typeof (SmtTerm.geq x y) = SmtType.Bool := by
  rw [typeof_geq_eq]
  simp [hx, hy, __smtx_typeof_arith_overload_op_2_ret]

theorem smtx_typeof_gt_int
    (x y : SmtTerm)
    (hx : __smtx_typeof x = SmtType.Int)
    (hy : __smtx_typeof y = SmtType.Int) :
    __smtx_typeof (SmtTerm.gt x y) = SmtType.Bool := by
  rw [typeof_gt_eq]
  simp [hx, hy, __smtx_typeof_arith_overload_op_2_ret]

private theorem smtx_eval_purify_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_purify x) =
      __smtx_model_eval__at_purify (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem concatSplitRaw_false_eq_of_ne_stuck
    (tHead sHead : Term)
    (htNe : tHead ≠ Term.Stuck) (hsNe : sHead ≠ Term.Stuck) :
    concatSplitRaw tHead sHead (Term.Boolean false) =
      concatSplitRawFalseBody tHead sHead := by
  cases tHead <;> cases sHead <;>
    simp [concatSplitRaw, concatSplitRawFalseBody, __str_unify_split,
      mkIte, mkGeq, mkNeg, mkSubstr, mkStrLen] at htNe hsNe ⊢

theorem concatSplitRaw_true_eq_of_ne_stuck
    (tHead sHead : Term)
    (htNe : tHead ≠ Term.Stuck) (hsNe : sHead ≠ Term.Stuck) :
    concatSplitRaw tHead sHead (Term.Boolean true) =
      concatSplitRawTrueBody tHead sHead := by
  cases tHead <;> cases sHead <;>
    simp [concatSplitRaw, concatSplitRawTrueBody, __str_unify_split,
      mkIte, mkGeq, mkNeg, mkSubstr, mkStrLen] at htNe hsNe ⊢

theorem smt_typeof_concatSplitTerm_false
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (concatSplitTerm tHead sHead (Term.Boolean false))) =
      SmtType.Seq T := by
  let lt := SmtTerm.str_len (__eo_to_smt tHead)
  let ls := SmtTerm.str_len (__eo_to_smt sHead)
  have hlt : __smtx_typeof lt = SmtType.Int := by
    simpa [lt] using smtx_typeof_str_len_seq (__eo_to_smt tHead) T htTy
  have hls : __smtx_typeof ls = SmtType.Int := by
    simpa [ls] using smtx_typeof_str_len_seq (__eo_to_smt sHead) T hsTy
  have hcond : __smtx_typeof (SmtTerm.geq lt ls) = SmtType.Bool :=
    smtx_typeof_geq_int lt ls hlt hls
  have hdiffTS : __smtx_typeof (SmtTerm.neg lt ls) = SmtType.Int :=
    smtx_typeof_neg_int lt ls hlt hls
  have hdiffST : __smtx_typeof (SmtTerm.neg ls lt) = SmtType.Int :=
    smtx_typeof_neg_int ls lt hls hlt
  have hThen :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt tHead) ls
            (SmtTerm.neg lt ls)) = SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt tHead) ls
      (SmtTerm.neg lt ls) T htTy hls hdiffTS
  have hElse :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt sHead) lt
            (SmtTerm.neg ls lt)) = SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt sHead) lt
      (SmtTerm.neg ls lt) T hsTy hlt hdiffST
  have htNe : tHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tHead
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htTy]
        exact seq_ne_none T)
  have hsNe : sHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sHead
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [hsTy]
        exact seq_ne_none T)
  rw [concatSplitTerm,
    concatSplitRaw_false_eq_of_ne_stuck tHead sHead htNe hsNe]
  simp only [concatSplitRawFalseBody, mkIte, mkGeq, mkNeg, mkSubstr, mkStrLen]
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.ite (SmtTerm.geq lt ls)
            (SmtTerm.str_substr (__eo_to_smt tHead) ls
              (SmtTerm.neg lt ls))
            (SmtTerm.str_substr (__eo_to_smt sHead) lt
              (SmtTerm.neg ls lt)))) =
      SmtType.Seq T
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.geq lt ls)
        (SmtTerm.str_substr (__eo_to_smt tHead) ls (SmtTerm.neg lt ls))
        (SmtTerm.str_substr (__eo_to_smt sHead) lt (SmtTerm.neg ls lt))) =
    SmtType.Seq T
  rw [typeof_ite_eq, hcond, hThen, hElse]
  simp [__smtx_typeof_ite, native_ite, native_Teq]

theorem smt_typeof_concatSplitTerm_true
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (concatSplitTerm tHead sHead (Term.Boolean true))) =
      SmtType.Seq T := by
  let lt := SmtTerm.str_len (__eo_to_smt tHead)
  let ls := SmtTerm.str_len (__eo_to_smt sHead)
  have hlt : __smtx_typeof lt = SmtType.Int := by
    simpa [lt] using smtx_typeof_str_len_seq (__eo_to_smt tHead) T htTy
  have hls : __smtx_typeof ls = SmtType.Int := by
    simpa [ls] using smtx_typeof_str_len_seq (__eo_to_smt sHead) T hsTy
  have hcond : __smtx_typeof (SmtTerm.geq lt ls) = SmtType.Bool :=
    smtx_typeof_geq_int lt ls hlt hls
  have hdiffTS : __smtx_typeof (SmtTerm.neg lt ls) = SmtType.Int :=
    smtx_typeof_neg_int lt ls hlt hls
  have hdiffST : __smtx_typeof (SmtTerm.neg ls lt) = SmtType.Int :=
    smtx_typeof_neg_int ls lt hls hlt
  have hThen :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt tHead) (SmtTerm.Numeral 0)
            (SmtTerm.neg lt ls)) = SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt tHead) (SmtTerm.Numeral 0)
      (SmtTerm.neg lt ls) T htTy (by simp [__smtx_typeof]) hdiffTS
  have hElse :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt sHead) (SmtTerm.Numeral 0)
            (SmtTerm.neg ls lt)) = SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt sHead) (SmtTerm.Numeral 0)
      (SmtTerm.neg ls lt) T hsTy (by simp [__smtx_typeof]) hdiffST
  have htNe : tHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tHead
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htTy]
        exact seq_ne_none T)
  have hsNe : sHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sHead
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [hsTy]
        exact seq_ne_none T)
  rw [concatSplitTerm,
    concatSplitRaw_true_eq_of_ne_stuck tHead sHead htNe hsNe]
  simp only [concatSplitRawTrueBody, mkIte, mkGeq, mkNeg, mkSubstr, mkStrLen]
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.ite (SmtTerm.geq lt ls)
            (SmtTerm.str_substr (__eo_to_smt tHead) (SmtTerm.Numeral 0)
              (SmtTerm.neg lt ls))
            (SmtTerm.str_substr (__eo_to_smt sHead) (SmtTerm.Numeral 0)
              (SmtTerm.neg ls lt)))) =
      SmtType.Seq T
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.geq lt ls)
        (SmtTerm.str_substr (__eo_to_smt tHead) (SmtTerm.Numeral 0)
          (SmtTerm.neg lt ls))
        (SmtTerm.str_substr (__eo_to_smt sHead) (SmtTerm.Numeral 0)
          (SmtTerm.neg ls lt))) = SmtType.Seq T
  rw [typeof_ite_eq, hcond, hThen, hElse]
  simp [__smtx_typeof_ite, native_ite, native_Teq]

theorem smt_typeof_nil_str_concat_typeof_of_smt_type_seq
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
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

theorem nil_str_concat_typeof_ne_stuck_of_smt_type_seq
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

theorem eval_nil_str_concat_typeof_of_smt_type_seq
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

theorem smt_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

@[simp] private theorem term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

@[simp] private theorem term_uop_ne_stuck (op : UserOp) :
    Term.UOp op ≠ Term.Stuck := by
  intro h
  cases h

@[simp] private theorem term_boolean_ne_stuck (b : Bool) :
    Term.Boolean b ≠ Term.Stuck := by
  intro h
  cases h

@[simp] private theorem term_numeral_ne_stuck (n : native_Int) :
    Term.Numeral n ≠ Term.Stuck := by
  intro h
  cases h

theorem eo_has_bool_type_eq_of_seq_type
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkEq x y) := by
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hxTy, hyTy]
  · rw [hxTy]
    exact seq_ne_none T

theorem smt_typeof_mkConcat_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  simpa [mkConcat] using
    smtx_typeof_str_concat_seq (__eo_to_smt x) (__eo_to_smt y) T hxTy hyTy

theorem eo_has_bool_type_gt_strlen_pos
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkGt (mkStrLen x) (Term.Numeral 0)) := by
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt x)) (SmtTerm.Numeral 0)) =
      SmtType.Bool
  exact smtx_typeof_gt_int (SmtTerm.str_len (__eo_to_smt x))
    (SmtTerm.Numeral 0)
    (smtx_typeof_str_len_seq (__eo_to_smt x) T hxTy)
    (by simp [__smtx_typeof])

theorem concatSplitFalseFormula_has_bool_type
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatSplitFalseFormula tHead sHead) := by
  let split := concatSplitTerm tHead sHead (Term.Boolean false)
  let nilS := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead)
  let nilT := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tHead)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_false tHead sHead T htTy hsTy
  have hNilSTy :
      __smtx_typeof (__eo_to_smt nilS) = SmtType.Seq T := by
    simpa [nilS] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq sHead T hsTy
  have hNilTTy :
      __smtx_typeof (__eo_to_smt nilT) = SmtType.Seq T := by
    simpa [nilT] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq tHead T htTy
  let rhsT := mkConcat sHead (mkConcat split nilS)
  let rhsS := mkConcat tHead (mkConcat split nilT)
  have hSplitNilS :
      __smtx_typeof (__eo_to_smt (mkConcat split nilS)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq split nilS T hSplitTy hNilSTy
  have hSplitNilT :
      __smtx_typeof (__eo_to_smt (mkConcat split nilT)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq split nilT T hSplitTy hNilTTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq sHead
      (mkConcat split nilS) T hsTy hSplitNilS
  have hRhsSTy : __smtx_typeof (__eo_to_smt rhsS) = SmtType.Seq T := by
    simpa [rhsS] using smt_typeof_mkConcat_seq tHead
      (mkConcat split nilT) T htTy hSplitNilT
  have hEqT : RuleProofs.eo_has_bool_type (mkEq tHead rhsT) :=
    eo_has_bool_type_eq_of_seq_type tHead rhsT T htTy hRhsTTy
  have hEqS : RuleProofs.eo_has_bool_type (mkEq sHead rhsS) :=
    eo_has_bool_type_eq_of_seq_type sHead rhsS T hsTy hRhsSTy
  have hOrRight :
      RuleProofs.eo_has_bool_type (mkOr (mkEq sHead rhsS) (Term.Boolean false)) := by
    simpa [mkOr] using RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkEq sHead rhsS) (Term.Boolean false) hEqS
      RuleProofs.eo_has_bool_type_false
  have hOr :
      RuleProofs.eo_has_bool_type
        (mkOr (mkEq tHead rhsT)
          (mkOr (mkEq sHead rhsS) (Term.Boolean false))) := by
    simpa [mkOr] using RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkEq tHead rhsT) (mkOr (mkEq sHead rhsS) (Term.Boolean false))
      hEqT hOrRight
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof split))) =
        SmtType.Seq T :=
    smt_typeof_seq_empty_typeof_of_smt_type_seq split T hSplitTy
  have hNonemptyEq :
      RuleProofs.eo_has_bool_type
        (mkEq split (__seq_empty (__eo_typeof split))) :=
    eo_has_bool_type_eq_of_seq_type split (__seq_empty (__eo_typeof split))
      T hSplitTy hEmptyTy
  have hNonempty :
      RuleProofs.eo_has_bool_type
        (mkNot (mkEq split (__seq_empty (__eo_typeof split)))) := by
    simpa [mkNot] using
      RuleProofs.eo_has_bool_type_not_of_bool_arg
        (mkEq split (__seq_empty (__eo_typeof split))) hNonemptyEq
  have hGt : RuleProofs.eo_has_bool_type
      (mkGt (mkStrLen split) (Term.Numeral 0)) :=
    eo_has_bool_type_gt_strlen_pos split T hSplitTy
  have hLenTail :
      RuleProofs.eo_has_bool_type
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)) := by
    simpa [mkAnd] using RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)
      hGt RuleProofs.eo_has_bool_type_true
  have hRight :
      RuleProofs.eo_has_bool_type
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true))) := by
    simpa [mkAnd] using RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true))
      hNonempty hLenTail
  simpa [concatSplitFalseFormula, split, nilS, nilT, rhsT, rhsS, mkAnd,
    mkOr] using RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkOr (mkEq tHead rhsT)
        (mkOr (mkEq sHead rhsS) (Term.Boolean false)))
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      hOr hRight

theorem concatSplitTrueFormula_has_bool_type
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatSplitTrueFormula tHead sHead) := by
  let split := concatSplitTerm tHead sHead (Term.Boolean true)
  let nilSplit := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_true tHead sHead T htTy hsTy
  have hNilSplitTy :
      __smtx_typeof (__eo_to_smt nilSplit) = SmtType.Seq T := by
    simpa [nilSplit] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq split T hSplitTy
  let rhsT := mkConcat split (mkConcat sHead nilSplit)
  let rhsS := mkConcat split (mkConcat tHead nilSplit)
  have hSNil :
      __smtx_typeof (__eo_to_smt (mkConcat sHead nilSplit)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq sHead nilSplit T hsTy hNilSplitTy
  have hTNil :
      __smtx_typeof (__eo_to_smt (mkConcat tHead nilSplit)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq tHead nilSplit T htTy hNilSplitTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq split
      (mkConcat sHead nilSplit) T hSplitTy hSNil
  have hRhsSTy : __smtx_typeof (__eo_to_smt rhsS) = SmtType.Seq T := by
    simpa [rhsS] using smt_typeof_mkConcat_seq split
      (mkConcat tHead nilSplit) T hSplitTy hTNil
  have hEqT : RuleProofs.eo_has_bool_type (mkEq tHead rhsT) :=
    eo_has_bool_type_eq_of_seq_type tHead rhsT T htTy hRhsTTy
  have hEqS : RuleProofs.eo_has_bool_type (mkEq sHead rhsS) :=
    eo_has_bool_type_eq_of_seq_type sHead rhsS T hsTy hRhsSTy
  have hOrRight :
      RuleProofs.eo_has_bool_type (mkOr (mkEq sHead rhsS) (Term.Boolean false)) := by
    simpa [mkOr] using RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkEq sHead rhsS) (Term.Boolean false) hEqS
      RuleProofs.eo_has_bool_type_false
  have hOr :
      RuleProofs.eo_has_bool_type
        (mkOr (mkEq tHead rhsT)
          (mkOr (mkEq sHead rhsS) (Term.Boolean false))) := by
    simpa [mkOr] using RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkEq tHead rhsT) (mkOr (mkEq sHead rhsS) (Term.Boolean false))
      hEqT hOrRight
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof split))) =
        SmtType.Seq T :=
    smt_typeof_seq_empty_typeof_of_smt_type_seq split T hSplitTy
  have hNonemptyEq :
      RuleProofs.eo_has_bool_type
        (mkEq split (__seq_empty (__eo_typeof split))) :=
    eo_has_bool_type_eq_of_seq_type split (__seq_empty (__eo_typeof split))
      T hSplitTy hEmptyTy
  have hNonempty :
      RuleProofs.eo_has_bool_type
        (mkNot (mkEq split (__seq_empty (__eo_typeof split)))) := by
    simpa [mkNot] using
      RuleProofs.eo_has_bool_type_not_of_bool_arg
        (mkEq split (__seq_empty (__eo_typeof split))) hNonemptyEq
  have hGt : RuleProofs.eo_has_bool_type
      (mkGt (mkStrLen split) (Term.Numeral 0)) :=
    eo_has_bool_type_gt_strlen_pos split T hSplitTy
  have hLenTail :
      RuleProofs.eo_has_bool_type
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)) := by
    simpa [mkAnd] using RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)
      hGt RuleProofs.eo_has_bool_type_true
  have hRight :
      RuleProofs.eo_has_bool_type
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true))) := by
    simpa [mkAnd] using RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true))
      hNonempty hLenTail
  simpa [concatSplitTrueFormula, split, nilSplit, rhsT, rhsS, mkAnd, mkOr]
    using RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkOr (mkEq tHead rhsT)
        (mkOr (mkEq sHead rhsS) (Term.Boolean false)))
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      hOr hRight

theorem concatSplitFormula_false_eq_plain
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    concatSplitFormula (Term.Boolean false) tHead sHead =
      concatSplitFalseFormula tHead sHead := by
  let split := concatSplitTerm tHead sHead (Term.Boolean false)
  have htNe : tHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tHead
      (by unfold RuleProofs.eo_has_smt_translation; rw [htTy]; exact seq_ne_none T)
  have hsNe : sHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sHead
      (by unfold RuleProofs.eo_has_smt_translation; rw [hsTy]; exact seq_ne_none T)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_false tHead sHead T htTy hsTy
  have hSplitNe : split ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation split
      (by unfold RuleProofs.eo_has_smt_translation; rw [hSplitTy]; exact seq_ne_none T)
  have hNilTNe :
      __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tHead) ≠ Term.Stuck :=
    nil_str_concat_typeof_ne_stuck_of_smt_type_seq tHead T htTy
  have hNilSNe :
      __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead) ≠ Term.Stuck :=
    nil_str_concat_typeof_ne_stuck_of_smt_type_seq sHead T hsTy
  have hEmptySplitNe : __seq_empty (__eo_typeof split) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq split T hSplitTy
  have hSplitNe' :
      concatSplitTerm tHead sHead (Term.Boolean false) ≠ Term.Stuck := by
    simpa [split] using hSplitNe
  have hEmptySplitNe' :
      __seq_empty
          (__eo_typeof (concatSplitTerm tHead sHead (Term.Boolean false))) ≠
        Term.Stuck := by
    simpa [split] using hEmptySplitNe
  have hLeftNe :
      mkOr
          (mkEq tHead
            (mkConcat sHead
              (mkConcat (concatSplitTerm tHead sHead (Term.Boolean false))
                (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead)))))
          (mkOr
            (mkEq sHead
              (mkConcat tHead
                (mkConcat (concatSplitTerm tHead sHead (Term.Boolean false))
                  (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tHead)))))
            (Term.Boolean false)) ≠ Term.Stuck := by
    simp [mkOr, mkEq, mkConcat]
  have hRightNe :
      mkAnd
        (mkNot
          (mkEq (concatSplitTerm tHead sHead (Term.Boolean false))
            (__seq_empty
              (__eo_typeof
                (concatSplitTerm tHead sHead (Term.Boolean false))))))
        (mkAnd
          (mkGt
            (mkStrLen (concatSplitTerm tHead sHead (Term.Boolean false)))
            (Term.Numeral 0))
          (Term.Boolean true)) ≠ Term.Stuck := by
    simp [mkAnd, mkNot, mkEq, mkGt, mkStrLen]
  simp [concatSplitFormula, concatSplitFalseFormula,
    mkEq, mkAnd, mkOr, mkNot, mkGt, mkStrLen, mkConcat, __eo_mk_apply,
    eo_ite_false]

theorem concatSplitFormula_true_eq_plain
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    concatSplitFormula (Term.Boolean true) tHead sHead =
      concatSplitTrueFormula tHead sHead := by
  let split := concatSplitTerm tHead sHead (Term.Boolean true)
  have htNe : tHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tHead
      (by unfold RuleProofs.eo_has_smt_translation; rw [htTy]; exact seq_ne_none T)
  have hsNe : sHead ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sHead
      (by unfold RuleProofs.eo_has_smt_translation; rw [hsTy]; exact seq_ne_none T)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_true tHead sHead T htTy hsTy
  have hSplitNe : split ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation split
      (by unfold RuleProofs.eo_has_smt_translation; rw [hSplitTy]; exact seq_ne_none T)
  have hNilSplitNe :
      __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split) ≠ Term.Stuck :=
    nil_str_concat_typeof_ne_stuck_of_smt_type_seq split T hSplitTy
  have hEmptySplitNe : __seq_empty (__eo_typeof split) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq split T hSplitTy
  have hSplitNe' :
      concatSplitTerm tHead sHead (Term.Boolean true) ≠ Term.Stuck := by
    simpa [split] using hSplitNe
  have hEmptySplitNe' :
      __seq_empty
          (__eo_typeof (concatSplitTerm tHead sHead (Term.Boolean true))) ≠
        Term.Stuck := by
    simpa [split] using hEmptySplitNe
  have hNilSplitNe' :
      __eo_nil (Term.UOp UserOp.str_concat)
          (__eo_typeof (concatSplitTerm tHead sHead (Term.Boolean true))) ≠
        Term.Stuck := by
    simpa [split] using hNilSplitNe
  have hLeftNe :
      mkOr
          (mkEq tHead
            (mkConcat (concatSplitTerm tHead sHead (Term.Boolean true))
              (mkConcat sHead
                (__eo_nil (Term.UOp UserOp.str_concat)
                  (__eo_typeof
                    (concatSplitTerm tHead sHead (Term.Boolean true)))))))
          (mkOr
            (mkEq sHead
              (mkConcat (concatSplitTerm tHead sHead (Term.Boolean true))
                (mkConcat tHead
                  (__eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (concatSplitTerm tHead sHead (Term.Boolean true)))))))
            (Term.Boolean false)) ≠ Term.Stuck := by
    simp [mkOr, mkEq, mkConcat]
  have hRightNe :
      mkAnd
        (mkNot
          (mkEq (concatSplitTerm tHead sHead (Term.Boolean true))
            (__seq_empty
              (__eo_typeof
                (concatSplitTerm tHead sHead (Term.Boolean true))))))
        (mkAnd
          (mkGt
            (mkStrLen (concatSplitTerm tHead sHead (Term.Boolean true)))
            (Term.Numeral 0))
          (Term.Boolean true)) ≠ Term.Stuck := by
    simp [mkAnd, mkNot, mkEq, mkGt, mkStrLen]
  simp [concatSplitFormula, concatSplitTrueFormula,
    mkEq, mkAnd, mkOr, mkNot, mkGt, mkStrLen, mkConcat, __eo_mk_apply,
    eo_ite_true]

theorem concat_split_head_types_same_of_prog
    (rev t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenNeBool :
      RuleProofs.eo_has_bool_type
        (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))))
    (hProg :
      __eo_prog_concat_split rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T := by
  have hLenBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen tc) (mkStrLen sc)) :=
    RuleProofs.eo_has_bool_type_not_arg
      (mkEq (mkStrLen tc) (mkStrLen sc)) hLenNeBool
  rcases len_eq_seq_types_of_bool tc sc hLenBool with
    ⟨T, U, htcTy, hscTyU⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htcTy]
        exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [hscTyU]
        exact seq_ne_none U)
  rcases eo_prog_concat_split_eq_of_ne_stuck rev t s tc sc hProg with
    ⟨_, hHeadT, hHeadS⟩
  rcases concatSplit_rev_cases_of_prog_ne_stuck rev t s tc sc hProg htcNe
    with hRev | hRev
  · subst rev
    have hNthTEq :
        __eo_list_nth (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
            (Term.Numeral 0) = tc := by
      simpa [concatSplitHead, concatSplitNormalize, eo_ite_true] using hHeadT
    have hNthSEq :
        __eo_list_nth (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
            (Term.Numeral 0) = sc := by
      simpa [concatSplitHead, concatSplitNormalize, eo_ite_true] using hHeadS
    have hNthTNe :
        __eo_list_nth (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
            (Term.Numeral 0) ≠ Term.Stuck := by
      rw [hNthTEq]
      exact htcNe
    have hNthSNe :
        __eo_list_nth (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
            (Term.Numeral 0) ≠ Term.Stuck := by
      rw [hNthSEq]
      exact hscNe
    rcases list_nth_zero_eq_cons_of_ne_stuck
        (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
        tc hNthTEq hNthTNe with
      ⟨tTail, hRevIntroT, _⟩
    rcases list_nth_zero_eq_cons_of_ne_stuck
        (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        sc hNthSEq hNthSNe with
      ⟨sTail, hRevIntroS, _⟩
    rcases str_nary_intro_rev_cons_seq_types_of_head_seq t tc tTail T
        hRevIntroT htcTy hTNN with
      ⟨htTy, _⟩
    rcases str_nary_intro_rev_cons_seq_types_of_head_seq s sc sTail U
        hRevIntroS hscTyU hSNN with
      ⟨hsTyU, _⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq T = SmtType.Seq U := by
        rw [← htTy, hTSSameTy, hsTyU]
      injection hSeq.symm
    exact ⟨T, htcTy, by simpa [hUT] using hscTyU⟩
  · subst rev
    have hNthTEq :
        __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
            (Term.Numeral 0) = tc := by
      simpa [concatSplitHead, concatSplitNormalize, eo_ite_false] using hHeadT
    have hNthSEq :
        __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
            (Term.Numeral 0) = sc := by
      simpa [concatSplitHead, concatSplitNormalize, eo_ite_false] using hHeadS
    have hNthTNe :
        __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
            (Term.Numeral 0) ≠ Term.Stuck := by
      rw [hNthTEq]
      exact htcNe
    have hNthSNe :
        __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
            (Term.Numeral 0) ≠ Term.Stuck := by
      rw [hNthSEq]
      exact hscNe
    rcases list_nth_zero_eq_cons_of_ne_stuck
        (Term.UOp UserOp.str_concat) (__str_nary_intro t) tc
        hNthTEq hNthTNe with
      ⟨tTail, hIntroT, _⟩
    rcases list_nth_zero_eq_cons_of_ne_stuck
        (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
        hNthSEq hNthSNe with
      ⟨sTail, hIntroS, _⟩
    rcases str_nary_intro_cons_seq_types_of_head_seq t tc tTail T
        hIntroT htcTy hTNN with
      ⟨htTy, _⟩
    rcases str_nary_intro_cons_seq_types_of_head_seq s sc sTail U
        hIntroS hscTyU hSNN with
      ⟨hsTyU, _⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq T = SmtType.Seq U := by
        rw [← htTy, hTSSameTy, hsTyU]
      injection hSeq.symm
    exact ⟨T, htcTy, by simpa [hUT] using hscTyU⟩

theorem concat_split_false_context
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenNeBool :
      RuleProofs.eo_has_bool_type
        (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))))
    (hProg :
      __eo_prog_concat_split (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T tTail sTail,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
  rcases eo_prog_concat_split_eq_of_ne_stuck
      (Term.Boolean false) t s tc sc hProg with
    ⟨_, hHeadT, hHeadS⟩
  rcases concat_split_head_types_same_of_prog (Term.Boolean false) t s tc sc
      hPremBool hLenNeBool hProg with
    ⟨T, htcTy, hscTy⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = tc := by
    simpa [concatSplitHead, concatSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simpa [concatSplitHead, concatSplitNormalize, eo_ite_false] using hHeadS
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) tc
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_cons_seq_types_of_head_seq t tc tTail T
      hIntroT htcTy hTNN with
    ⟨htTy, htTailTy⟩
  rcases str_nary_intro_cons_seq_types_of_head_seq s sc sTail T
      hIntroS hscTy hSNN with
    ⟨hsTy, hsTailTy⟩
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck := by
    rw [hIntroT]
    simp
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroS]
    simp
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T := by
    rw [hIntroT]
    exact smt_typeof_mkConcat_seq tc tTail T htcTy htTailTy
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T := by
    rw [hIntroS]
    exact smt_typeof_mkConcat_seq sc sTail T hscTy hsTailTy
  have hIntroBool :
      RuleProofs.eo_has_bool_type
        (mkEq (__str_nary_intro t) (__str_nary_intro s)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroTTy, hIntroSTy]
    · rw [hIntroTTy]
      exact seq_ne_none T
  have hIntroEq :
      eo_interprets M (mkEq (__str_nary_intro t) (__str_nary_intro s)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM t s T htTy hsTy
      hIntroTNe hIntroSNe hST hIntroBool
  have hConcatEq :
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
    simpa [hIntroT, hIntroS] using hIntroEq
  exact ⟨T, tTail, sTail, htcTy, hscTy, htTailTy, hsTailTy, hConcatEq⟩

theorem eo_interprets_rev_cons_snoc_of_list_nil_raw
    (M : SmtModel) (hM : model_wf M) (head nil : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))
        (mkConcat nil head)) true := by
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil hRevCons
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq head nil T hHeadTy hNilTy
  have hElimCons :
      __str_nary_elim (mkConcat head nil) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head nil T hHeadTy
      hNilTy (eo_is_list_str_concat_nil_true_of_nil_true nil hNil)
  let lhs :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil))
  let rhs := mkConcat nil head
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq T := by
    subst lhs
    rw [hRevConsEq]
    exact smt_typeof_str_nary_elim_of_seq_ne_stuck
      (mkConcat head nil) T hConsTy hElimCons
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    subst rhs
    exact smt_typeof_mkConcat_seq nil head T hNilTy hHeadTy
  have hBool : RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLhsTy, hRhsTy]
    · rw [hLhsTy]
      exact seq_ne_none T
  have hLhsToCons :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt (mkConcat head nil))) := by
    subst lhs
    rw [hRevConsEq]
    exact smt_value_rel_str_nary_elim M hM (mkConcat head nil) T
      hConsTy hElimCons
  have hConsToHead :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
        (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM head nil T hHeadTy
      hNil hNilTy
  have hRhsToHead :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt rhs))
        (__smtx_model_eval M (__eo_to_smt head)) := by
    subst rhs
    exact smt_value_rel_str_concat_list_nil_left_empty M hM nil head T
      hNil hNilTy hHeadTy
  have hLhsToHead :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt head)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) hLhsToCons hConsToHead
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt rhs)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M (__eo_to_smt rhs)) hLhsToHead
      (RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt rhs))
        (__smtx_model_eval M (__eo_to_smt head)) hRhsToHead)
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool hRel

theorem eo_interprets_rev_cons_snoc_prefix_of_seq
    (M : SmtModel) (hM : model_wf M) (head tail : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)) ≠
        Term.Stuck) :
    ∃ pref,
      __smtx_typeof (__eo_to_smt pref) = SmtType.Seq T ∧
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head tail)))
            (mkConcat pref head)) true := by
  by_cases hTailConcat : ∃ a aTail : Term, tail = mkConcat a aTail
  · rcases hTailConcat with ⟨a, aTail, rfl⟩
    have hRevTail :
        __eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat a aTail) ≠ Term.Stuck :=
      eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
        (mkConcat a aTail) hTailList
    have hElimTail :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat a aTail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq a aTail T
        hTailTy hRevTail
    let pref :=
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat a aTail))
    have hPrefixTy :
        __smtx_typeof (__eo_to_smt pref) = SmtType.Seq T := by
      subst pref
      exact smt_typeof_str_nary_elim_list_rev_of_seq (mkConcat a aTail)
        T hTailList hTailTy hRevTail hElimTail
    have hSnoc :
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head (mkConcat a aTail))))
            (mkConcat pref head)) true := by
      subst pref
      exact eo_interprets_rev_cons_snoc_of_seq M hM head (mkConcat a aTail)
        T hHeadTy hTailList hTailTy hRevCons hRevTail hElimCons
        hElimTail
    exact ⟨pref, hPrefixTy, hSnoc⟩
  · have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) tail =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_of_list_true_not_concat tail hTailList
        hTailConcat
    exact ⟨tail, hTailTy,
      eo_interprets_rev_cons_snoc_of_list_nil_raw M hM head tail T
        hHeadTy hNil hTailTy hRevCons⟩

theorem concat_split_true_context
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenNeBool :
      RuleProofs.eo_has_bool_type
        (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))))
    (hProg :
      __eo_prog_concat_split (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T tPrefix sPrefix,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true := by
  rcases eo_prog_concat_split_eq_of_ne_stuck
      (Term.Boolean true) t s tc sc hProg with
    ⟨_, hHeadT, hHeadS⟩
  rcases concat_split_head_types_same_of_prog (Term.Boolean true) t s tc sc
      hPremBool hLenNeBool hProg with
    ⟨T, htcTy, hscTy⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = tc := by
    simpa [concatSplitHead, concatSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simpa [concatSplitHead, concatSplitNormalize, eo_ite_true] using hHeadS
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      tc hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      sc hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t tc tTail T
      hRevIntroT htcTy hTNN with
    ⟨htTy, htTailTy⟩
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq s sc sTail T
      hRevIntroS hscTy hSNN with
    ⟨hsTy, hsTailTy⟩
  have hRevIntroTNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck := by
    rw [hRevIntroT]
    simp
  have hRevIntroSNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck := by
    rw [hRevIntroS]
    simp
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntroTNe
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt t) T
      htTy with
    ⟨hTInh, hTWf⟩
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf t T htTy hTInh hTWf
      hIntroTNe
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq t T htTy hIntroTNN
      hIntroTNe
  have hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq s T hsTy hIntroSNN
      hIntroSNe
  have hDoubleT :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M t T htTy
      hIntroTNN hIntroTNe hRevIntroTNe
  have hDoubleS :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M s T hsTy
      hIntroSNN hIntroSNe hRevIntroSNe
  have hDoubleEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))) true :=
    eo_interprets_double_rev_intros_of_elim_intros M hM t s T htTy hsTy
      hIntroTNN hIntroSNN hIntroTNe hIntroSNe hElimIntroT
      hElimIntroS hDoubleT hDoubleS hST
  have hRevConcatEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat tc tTail)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true := by
    simpa [hRevIntroT, hRevIntroS] using hDoubleEq
  have hConsTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat tc tTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      tc tTail (by decide) hTTailList
  have hConsSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat sc sTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      sc sTail (by decide) hSTailList
  have hConsTTy :
      __smtx_typeof (__eo_to_smt (mkConcat tc tTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq tc tTail T htcTy htTailTy
  have hConsSTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc sTail T hscTy hsTailTy
  have hRevConsT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat tc tTail) hConsTList
  have hRevConsS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat sc sTail) hConsSList
  have hElimConsT :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat tc tTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq tc tTail T
      hConsTTy hRevConsT
  have hElimConsS :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat sc sTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq sc sTail T
      hConsSTy hRevConsS
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM tc tTail T
      htcTy hTTailList htTailTy hRevConsT hElimConsT with
    ⟨tPrefix, htPrefixTy, hSnocT⟩
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM sc sTail T
      hscTy hSTailList hsTailTy hRevConsS hElimConsS with
    ⟨sPrefix, hsPrefixTy, hSnocS⟩
  have hSnocTSymm :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat tc tTail)))) true :=
    eo_interprets_eq_symm_local M
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail)))
      (mkConcat tPrefix tc) hSnocT
  have hLeftToRight :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix tc)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail)))
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      hSnocTSymm hRevConcatEq
  have hSnocEq :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix tc)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      (mkConcat sPrefix sc) hLeftToRight hSnocS
  exact ⟨T, tPrefix, sPrefix, htcTy, hscTy, htPrefixTy, hsPrefixTy,
    hSnocEq⟩

theorem native_seq_extract_zero_nat
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

theorem native_seq_extract_to_end_nat
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

theorem concat_split_take_eq_of_append_eq_of_le
    {α : Type} (xs ys xtail ytail : List α)
    (h : xs ++ xtail = ys ++ ytail) (hle : ys.length <= xs.length) :
    xs.take ys.length = ys := by
  have hTake := congrArg (List.take ys.length) h
  rw [List.take_append_of_le_length hle, List.take_left] at hTake
  exact hTake

theorem concat_split_left_eq_append_drop_of_append_eq_of_le
    {α : Type} (xs ys xtail ytail : List α)
    (h : xs ++ xtail = ys ++ ytail) (hle : ys.length <= xs.length) :
    xs = ys ++ xs.drop ys.length := by
  have hTake := concat_split_take_eq_of_append_eq_of_le xs ys xtail ytail h hle
  calc
    xs = xs.take ys.length ++ xs.drop ys.length :=
      (List.take_append_drop ys.length xs).symm
    _ = ys ++ xs.drop ys.length := by
      rw [hTake]

theorem concat_split_suffix_eq_take_append_of_append_eq_of_le
    {α : Type} (px xs py ys : List α)
    (h : px ++ xs = py ++ ys) (hle : ys.length <= xs.length) :
    xs = xs.take (xs.length - ys.length) ++ ys := by
  have hRev :
      xs.reverse ++ px.reverse = ys.reverse ++ py.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse h
  have hRevLeft :
      xs.reverse = ys.reverse ++ xs.reverse.drop ys.length := by
    simpa using
      concat_split_left_eq_append_drop_of_append_eq_of_le
        xs.reverse ys.reverse px.reverse py.reverse hRev (by simpa using hle)
  have hBack := congrArg List.reverse hRevLeft
  simpa [List.reverse_append, List.drop_reverse] using hBack

theorem concat_split_append_eq_of_concat_eq
    (M : SmtModel) (hM : model_wf M)
    (x xtail y ytail : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxtailTy : __smtx_typeof (__eo_to_smt xtail) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hytailTy : __smtx_typeof (__eo_to_smt ytail) = SmtType.Seq T)
    (hEq : eo_interprets M (mkEq (mkConcat x xtail) (mkConcat y ytail)) true) :
    ∃ sx sxtail sy sytail : SmtSeq,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
      __smtx_model_eval M (__eo_to_smt xtail) = SmtValue.Seq sxtail ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
      __smtx_model_eval M (__eo_to_smt ytail) = SmtValue.Seq sytail ∧
      native_unpack_seq sx ++ native_unpack_seq sxtail =
        native_unpack_seq sy ++ native_unpack_seq sytail := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hxtailValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xtail)
    (SmtType.Seq T) hxtailTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hytailValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ytail)
    (SmtType.Seq T) hytailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hxtailValTy with ⟨sxtail, hxtailEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hytailValTy with ⟨sytail, hytailEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hRel := RuleProofs.eo_interprets_eq_rel M
    (mkConcat x xtail) (mkConcat y ytail) hEq
  unfold RuleProofs.smt_value_rel at hRel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
    at hRel
  rw [hxEval, hxtailEval, hyEval, hytailEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sxtail)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sytail))) =
      SmtValue.Boolean true at hRel
  rw [hsxElem, hsyElem] at hRel
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sxtail))
    (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sytail)) at hRel
  have hPackEq :=
    (RuleProofs.smt_seq_rel_iff_eq _ _).1 hRel
  have hListEq := congrArg native_unpack_seq hPackEq
  exact
    ⟨sx, sxtail, sy, sytail, hxEval, hxtailEval, hyEval, hytailEval,
      by simpa [Smtm.native_unpack_pack_seq] using hListEq⟩

theorem native_pack_seq_ne_empty_of_length_pos
    (T : SmtType) {xs : List SmtValue} (hPos : 0 < xs.length) :
    native_pack_seq T xs ≠ SmtSeq.empty T := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenZero : xs.length = 0 := by
    have hLen := congrArg List.length hUnpack
    simpa [Smtm.native_unpack_pack_seq, native_unpack_seq] using hLen
  omega

theorem eval_concatSplitTerm_false_left
    (M : SmtModel) (hM : model_wf M)
    (tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (st ss : SmtSeq)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hle : (native_unpack_seq ss).length <= (native_unpack_seq st).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatSplitTerm tc sc (Term.Boolean false))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).drop (native_unpack_seq ss).length)) := by
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have htNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hsNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hSub :
      native_seq_extract xs (Int.ofNat ys.length)
          (Int.ofNat (xs.length - ys.length)) =
        xs.drop ys.length :=
    native_seq_extract_to_end_nat xs ys.length (by simpa [xs, ys] using hle)
  have hDiff :
      Int.ofNat (xs.length - ys.length) =
        Int.ofNat xs.length - Int.ofNat ys.length :=
    Int.ofNat_sub (by simpa [xs, ys] using hle)
  have hCondTrue :
      native_zleq (Int.ofNat (native_unpack_seq ss).length)
          (Int.ofNat (native_unpack_seq st).length) = true := by
    simp [native_zleq, SmtEval.native_zleq]
    exact hle
  have hEvalCond :
      __smtx_model_eval M
          (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt sc))) =
        SmtValue.Boolean true := by
    simp [__smtx_model_eval, htcEval, hscEval, __smtx_model_eval_str_len,
      __smtx_model_eval_geq, __smtx_model_eval_leq, native_seq_len]
    exact hCondTrue
  have hSubEval :
      native_seq_extract (native_unpack_seq st)
          (Int.ofNat (native_unpack_seq ss).length)
          (Int.ofNat (native_unpack_seq st).length +
            -Int.ofNat (native_unpack_seq ss).length) =
        (native_unpack_seq st).drop (native_unpack_seq ss).length := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [xs, ys, Int.sub_eq_add_neg] using hSub'
  rw [concatSplitTerm, concatSplitRaw_false_eq_of_ne_stuck tc sc htNe hsNe]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.ite
            (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt sc)))
            (SmtTerm.str_substr (__eo_to_smt tc)
              (SmtTerm.str_len (__eo_to_smt sc))
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
                (SmtTerm.str_len (__eo_to_smt sc))))
            (SmtTerm.str_substr (__eo_to_smt sc)
              (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc))
                (SmtTerm.str_len (__eo_to_smt tc)))))) =
      SmtValue.Seq (native_pack_seq T (xs.drop ys.length))
  rw [smtx_eval_purify_term_eq, smtx_eval_ite_term_eq, hEvalCond]
  simp [xs, ys, htcEval, hscEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval__, __smtx_model_eval_ite,
    __smtx_model_eval_str_substr, __smtx_model_eval__at_purify,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

theorem eval_concatSplitTerm_false_right
    (M : SmtModel) (hM : model_wf M)
    (tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (st ss : SmtSeq)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hlt : (native_unpack_seq st).length < (native_unpack_seq ss).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatSplitTerm tc sc (Term.Boolean false))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq ss).drop (native_unpack_seq st).length)) := by
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have htNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hsNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hlt' : xs.length < ys.length := by
    simpa [xs, ys] using hlt
  have hle : xs.length <= ys.length := Nat.le_of_lt hlt'
  have hCondFalse :
      native_zleq (Int.ofNat (native_unpack_seq ss).length)
          (Int.ofNat (native_unpack_seq st).length) = false := by
    simp [native_zleq, SmtEval.native_zleq]
    exact hlt
  have hEvalCond :
      __smtx_model_eval M
          (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt sc))) =
        SmtValue.Boolean false := by
    simp [__smtx_model_eval, htcEval, hscEval, __smtx_model_eval_str_len,
      __smtx_model_eval_geq, __smtx_model_eval_leq, native_seq_len]
    exact hCondFalse
  have hSub :
      native_seq_extract ys (Int.ofNat xs.length)
          (Int.ofNat (ys.length - xs.length)) =
        ys.drop xs.length :=
    native_seq_extract_to_end_nat ys xs.length hle
  have hDiff :
      Int.ofNat (ys.length - xs.length) =
        Int.ofNat ys.length - Int.ofNat xs.length :=
    Int.ofNat_sub hle
  have hSubEval :
      native_seq_extract (native_unpack_seq ss)
          (Int.ofNat (native_unpack_seq st).length)
          (Int.ofNat (native_unpack_seq ss).length +
            -Int.ofNat (native_unpack_seq st).length) =
        (native_unpack_seq ss).drop (native_unpack_seq st).length := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [xs, ys, Int.sub_eq_add_neg] using hSub'
  rw [concatSplitTerm, concatSplitRaw_false_eq_of_ne_stuck tc sc htNe hsNe]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.ite
            (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt sc)))
            (SmtTerm.str_substr (__eo_to_smt tc)
              (SmtTerm.str_len (__eo_to_smt sc))
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
                (SmtTerm.str_len (__eo_to_smt sc))))
            (SmtTerm.str_substr (__eo_to_smt sc)
              (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc))
                (SmtTerm.str_len (__eo_to_smt tc)))))) =
      SmtValue.Seq (native_pack_seq T (ys.drop xs.length))
  rw [smtx_eval_purify_term_eq, smtx_eval_ite_term_eq, hEvalCond]
  simp [xs, ys, htcEval, hscEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval__, __smtx_model_eval_ite,
    __smtx_model_eval_str_substr, __smtx_model_eval__at_purify,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

theorem eval_concatSplitTerm_true_left
    (M : SmtModel) (hM : model_wf M)
    (tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (st ss : SmtSeq)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hle : (native_unpack_seq ss).length <= (native_unpack_seq st).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatSplitTerm tc sc (Term.Boolean true))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - (native_unpack_seq ss).length))) := by
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have htNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hsNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hTakeLen : xs.length - ys.length <= xs.length := Nat.sub_le _ _
  have hSub :
      native_seq_extract xs 0 (Int.ofNat (xs.length - ys.length)) =
        xs.take (xs.length - ys.length) :=
    native_seq_extract_zero_nat xs (xs.length - ys.length) hTakeLen
  have hDiff :
      Int.ofNat (xs.length - ys.length) =
        Int.ofNat xs.length - Int.ofNat ys.length :=
    Int.ofNat_sub (by simpa [xs, ys] using hle)
  have hCondTrue :
      native_zleq (Int.ofNat (native_unpack_seq ss).length)
          (Int.ofNat (native_unpack_seq st).length) = true := by
    simp [native_zleq, SmtEval.native_zleq]
    exact hle
  have hEvalCond :
      __smtx_model_eval M
          (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt sc))) =
        SmtValue.Boolean true := by
    simp [__smtx_model_eval, htcEval, hscEval, __smtx_model_eval_str_len,
      __smtx_model_eval_geq, __smtx_model_eval_leq, native_seq_len]
    exact hCondTrue
  have hSubEval :
      native_seq_extract (native_unpack_seq st) 0
          (Int.ofNat (native_unpack_seq st).length +
            -Int.ofNat (native_unpack_seq ss).length) =
        (native_unpack_seq st).take
          ((native_unpack_seq st).length - (native_unpack_seq ss).length) := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [xs, ys, Int.sub_eq_add_neg] using hSub'
  rw [concatSplitTerm, concatSplitRaw_true_eq_of_ne_stuck tc sc htNe hsNe]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.ite
            (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt sc)))
            (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
                (SmtTerm.str_len (__eo_to_smt sc))))
            (SmtTerm.str_substr (__eo_to_smt sc) (SmtTerm.Numeral 0)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc))
                (SmtTerm.str_len (__eo_to_smt tc)))))) =
      SmtValue.Seq (native_pack_seq T (xs.take (xs.length - ys.length)))
  rw [smtx_eval_purify_term_eq, smtx_eval_ite_term_eq, hEvalCond]
  simp [xs, ys, htcEval, hscEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval__, __smtx_model_eval_ite,
    __smtx_model_eval_str_substr, __smtx_model_eval__at_purify,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

theorem eval_concatSplitTerm_true_right
    (M : SmtModel) (hM : model_wf M)
    (tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (st ss : SmtSeq)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hlt : (native_unpack_seq st).length < (native_unpack_seq ss).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatSplitTerm tc sc (Term.Boolean true))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq ss).take
            ((native_unpack_seq ss).length - (native_unpack_seq st).length))) := by
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have htNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hsNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hlt' : xs.length < ys.length := by
    simpa [xs, ys] using hlt
  have hle : xs.length <= ys.length := Nat.le_of_lt hlt'
  have hCondFalse :
      native_zleq (Int.ofNat (native_unpack_seq ss).length)
          (Int.ofNat (native_unpack_seq st).length) = false := by
    simp [native_zleq, SmtEval.native_zleq]
    exact hlt
  have hEvalCond :
      __smtx_model_eval M
          (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt sc))) =
        SmtValue.Boolean false := by
    simp [__smtx_model_eval, htcEval, hscEval, __smtx_model_eval_str_len,
      __smtx_model_eval_geq, __smtx_model_eval_leq, native_seq_len]
    exact hCondFalse
  have hTakeLen : ys.length - xs.length <= ys.length := Nat.sub_le _ _
  have hSub :
      native_seq_extract ys 0 (Int.ofNat (ys.length - xs.length)) =
        ys.take (ys.length - xs.length) :=
    native_seq_extract_zero_nat ys (ys.length - xs.length) hTakeLen
  have hDiff :
      Int.ofNat (ys.length - xs.length) =
        Int.ofNat ys.length - Int.ofNat xs.length :=
    Int.ofNat_sub hle
  have hSubEval :
      native_seq_extract (native_unpack_seq ss) 0
          (Int.ofNat (native_unpack_seq ss).length +
            -Int.ofNat (native_unpack_seq st).length) =
        (native_unpack_seq ss).take
          ((native_unpack_seq ss).length - (native_unpack_seq st).length) := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [xs, ys, Int.sub_eq_add_neg] using hSub'
  rw [concatSplitTerm, concatSplitRaw_true_eq_of_ne_stuck tc sc htNe hsNe]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.ite
            (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt sc)))
            (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
                (SmtTerm.str_len (__eo_to_smt sc))))
            (SmtTerm.str_substr (__eo_to_smt sc) (SmtTerm.Numeral 0)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc))
                (SmtTerm.str_len (__eo_to_smt tc)))))) =
      SmtValue.Seq (native_pack_seq T (ys.take (ys.length - xs.length)))
  rw [smtx_eval_purify_term_eq, smtx_eval_ite_term_eq, hEvalCond]
  simp [xs, ys, htcEval, hscEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval__, __smtx_model_eval_ite,
    __smtx_model_eval_str_substr, __smtx_model_eval__at_purify,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

theorem concat_split_nonempty_tail
    (M : SmtModel) (split : Term) (T : SmtType) (zs : List SmtValue)
    (hSplitTy : __smtx_typeof (__eo_to_smt split) = SmtType.Seq T)
    (hSplitEval :
      __smtx_model_eval M (__eo_to_smt split) =
        SmtValue.Seq (native_pack_seq T zs))
    (hPos : 0 < zs.length) :
    eo_interprets M
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      true := by
  let empty := __seq_empty (__eo_typeof split)
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T := by
    simpa [empty] using
      smt_typeof_seq_empty_typeof_of_smt_type_seq split T hSplitTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt empty) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [empty] using eval_seq_empty_typeof M split T hSplitTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (mkEq split empty) :=
    eo_has_bool_type_eq_of_seq_type split empty T hSplitTy hEmptyTy
  have hPackNe : native_pack_seq T zs ≠ SmtSeq.empty T :=
    native_pack_seq_ne_empty_of_length_pos T hPos
  have hValNe :
      SmtValue.Seq (native_pack_seq T zs) ≠
        SmtValue.Seq (SmtSeq.empty T) := by
    intro h
    injection h with hSeq
    exact hPackNe hSeq
  have hEqEval :
      __smtx_model_eval M (__eo_to_smt (mkEq split empty)) =
        SmtValue.Boolean false := by
    change
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt split) (__eo_to_smt empty)) =
        SmtValue.Boolean false
    rw [smtx_eval_eq_term_eq]
    rw [hSplitEval, hEmptyEval]
    simp [__smtx_model_eval_eq, native_veq, hValNe]
  have hEqFalse : eo_interprets M (mkEq split empty) false :=
    RuleProofs.eo_interprets_of_bool_eval M (mkEq split empty) false
      hEqBool hEqEval
  have hNotTrue : eo_interprets M (mkNot (mkEq split empty)) true :=
    RuleProofs.eo_interprets_not_of_false M (mkEq split empty) hEqFalse
  have hGtBool :
      RuleProofs.eo_has_bool_type (mkGt (mkStrLen split) (Term.Numeral 0)) :=
    eo_has_bool_type_gt_strlen_pos split T hSplitTy
  have hGtEval :
      __smtx_model_eval M
          (__eo_to_smt (mkGt (mkStrLen split) (Term.Numeral 0))) =
        SmtValue.Boolean true := by
    change
      __smtx_model_eval M
          (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt split))
            (SmtTerm.Numeral 0)) =
        SmtValue.Boolean true
    simp [__smtx_model_eval, hSplitEval, __smtx_model_eval_str_len,
      __smtx_model_eval_gt, __smtx_model_eval_lt, native_seq_len,
      native_zlt, SmtEval.native_zlt, Smtm.native_unpack_pack_seq]
    exact_mod_cast hPos
  have hGtTrue :
      eo_interprets M (mkGt (mkStrLen split) (Term.Numeral 0)) true :=
    RuleProofs.eo_interprets_of_bool_eval M
      (mkGt (mkStrLen split) (Term.Numeral 0)) true hGtBool hGtEval
  have hGtTail :
      eo_interprets M
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true))
        true :=
    RuleProofs.eo_interprets_and_intro M
      (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)
      hGtTrue (RuleProofs.eo_interprets_true M)
  simpa [empty, mkAnd, mkNot] using
    RuleProofs.eo_interprets_and_intro M (mkNot (mkEq split empty))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true))
      hNotTrue hGtTail

theorem eval_mkConcat_right_nested
    (M : SmtModel) (a b c : Term) (T : SmtType)
    (sa sb sc : SmtSeq)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa)
    (hbEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sb)
    (hcEval : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq sc)
    (haElem : __smtx_elem_typeof_seq_value sa = T) :
    __smtx_model_eval M (__eo_to_smt (mkConcat a (mkConcat b c))) =
      SmtValue.Seq
        (native_pack_seq T
          (native_unpack_seq sa ++ native_unpack_seq sb ++ native_unpack_seq sc)) := by
  rw [smtx_model_eval_str_concat_term_eq M a (mkConcat b c)]
  rw [smtx_model_eval_str_concat_term_eq M b c]
  rw [haEval, hbEval, hcEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    Smtm.native_unpack_pack_seq, haElem, List.append_assoc]
