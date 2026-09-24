module

public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatLPropFormula (rev tHead sHead : Term) : Term :=
  let split := concatSplitTerm tHead sHead rev
  let splitTy := __eo_typeof split
  let splitCons := __eo_mk_apply (Term.UOp UserOp.str_concat) split
  let sCons := __eo_mk_apply (Term.UOp UserOp.str_concat) sHead
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq) tHead)
        (__eo_ite rev
          (__eo_mk_apply splitCons
            (__eo_mk_apply sCons
              (__eo_nil (Term.UOp UserOp.str_concat) splitTy)))
          (__eo_mk_apply sCons
            (__eo_mk_apply splitCons
              (__eo_nil (Term.UOp UserOp.str_concat)
                (__eo_typeof sHead)))))))
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

private abbrev concatLPropFalseFormula (tHead sHead : Term) : Term :=
  let split := concatSplitTerm tHead sHead (Term.Boolean false)
  mkAnd
    (mkEq tHead
      (mkConcat sHead
        (mkConcat split
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead)))))
    (mkAnd
      (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))

private abbrev concatLPropTrueFormula (tHead sHead : Term) : Term :=
  let split := concatSplitTerm tHead sHead (Term.Boolean true)
  mkAnd
    (mkEq tHead
      (mkConcat split
        (mkConcat sHead
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split)))))
    (mkAnd
      (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
      (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))

private theorem eo_prog_concat_lprop_eq_of_ne_stuck
    (rev t s tc sc : Term)
    (hProg :
      __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck) :
    __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) =
      concatLPropFormula rev tc sc ∧
      concatSplitHead rev t = tc ∧ concatSplitHead rev s = sc := by
  have hProgBody :
      __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) =
        (__eo_requires (concatSplitHead rev t) tc
          (__eo_requires (concatSplitHead rev s) sc
            (concatLPropFormula rev (concatSplitHead rev t)
              (concatSplitHead rev s)))) := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals
      simp [__eo_prog_concat_lprop, concatLPropFormula, concatSplitHead,
        concatSplitNormalize, concatSplitTerm, concatSplitRaw]
  have hBodyNe :
      __eo_requires (concatSplitHead rev t) tc
          (__eo_requires (concatSplitHead rev s) sc
            (concatLPropFormula rev (concatSplitHead rev t)
              (concatSplitHead rev s))) ≠ Term.Stuck := by
    rw [← hProgBody]
    exact hProg
  have hHeadT :
      concatSplitHead rev t = tc :=
    eo_requires_eq_of_ne_stuck (concatSplitHead rev t) tc
      (__eo_requires (concatSplitHead rev s) sc
        (concatLPropFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s))) hBodyNe
  have hInnerNe :
      __eo_requires (concatSplitHead rev s) sc
        (concatLPropFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s)) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (concatSplitHead rev t) tc
      _ hBodyNe
  have hHeadS :
      concatSplitHead rev s = sc :=
    eo_requires_eq_of_ne_stuck (concatSplitHead rev s) sc _ hInnerNe
  have hOuterEq :
      __eo_requires (concatSplitHead rev t) tc
          (__eo_requires (concatSplitHead rev s) sc
            (concatLPropFormula rev (concatSplitHead rev t)
              (concatSplitHead rev s))) =
        __eo_requires (concatSplitHead rev s) sc
          (concatLPropFormula rev (concatSplitHead rev t)
            (concatSplitHead rev s)) :=
    eo_requires_eq_result_of_ne_stuck (concatSplitHead rev t) tc
      (__eo_requires (concatSplitHead rev s) sc
        (concatLPropFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s))) hBodyNe
  have hInnerEq :
      __eo_requires (concatSplitHead rev s) sc
          (concatLPropFormula rev (concatSplitHead rev t)
            (concatSplitHead rev s)) =
        concatLPropFormula rev (concatSplitHead rev t)
          (concatSplitHead rev s) :=
    eo_requires_eq_result_of_ne_stuck (concatSplitHead rev s) sc
      (concatLPropFormula rev (concatSplitHead rev t)
        (concatSplitHead rev s)) hInnerNe
  have hFormula :
      __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) =
        concatLPropFormula rev tc sc := by
    rw [hProgBody, hOuterEq, hInnerEq, hHeadT, hHeadS]
  exact ⟨hFormula, hHeadT, hHeadS⟩

private theorem len_gt_seq_types_of_bool (x y : Term)
    (hLenGtBool : RuleProofs.eo_has_bool_type (mkGt (mkStrLen x) (mkStrLen y))) :
    ∃ T U,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq U := by
  have hGtTerm :
      term_has_non_none_type
        (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt x))
          (SmtTerm.str_len (__eo_to_smt y))) := by
    apply _root_.term_has_non_none_of_type_eq
    · simpa [RuleProofs.eo_has_bool_type, mkGt, mkStrLen, __eo_to_smt, __smtx_typeof] using hLenGtBool
    · decide
  have hArgs :=
    arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt)
      (typeof_gt_eq (SmtTerm.str_len (__eo_to_smt x))
        (SmtTerm.str_len (__eo_to_smt y))) hGtTerm
  have hLeftTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) := by
    rcases hArgs with hInt | hReal
    · unfold term_has_non_none_type
      rw [hInt.1]
      simp
    · unfold term_has_non_none_type
      rw [hReal.1]
      simp
  have hRightTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt y)) := by
    rcases hArgs with hInt | hReal
    · unfold term_has_non_none_type
      rw [hInt.2]
      simp
    · unfold term_has_non_none_type
      rw [hReal.2]
      simp
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt x)) hLeftTerm with
    ⟨T, hxTy⟩
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt y)) hRightTerm with
    ⟨U, hyTy⟩
  exact ⟨T, U, hxTy, hyTy⟩

private theorem concatLProp_rev_cases_of_prog_ne_stuck
    (rev t s tc sc : Term)
    (hProg :
      __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck)
    (htcNe : tc ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_lprop_eq_of_ne_stuck rev t s tc sc hProg with
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

private theorem concat_lprop_head_types_same_of_prog
    (rev t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenGtBool : RuleProofs.eo_has_bool_type (mkGt (mkStrLen tc) (mkStrLen sc)))
    (hProg :
      __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T := by
  rcases len_gt_seq_types_of_bool tc sc hLenGtBool with
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
  rcases eo_prog_concat_lprop_eq_of_ne_stuck rev t s tc sc hProg with
    ⟨_, hHeadT, hHeadS⟩
  rcases concatLProp_rev_cases_of_prog_ne_stuck rev t s tc sc hProg htcNe
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

private theorem concat_lprop_len_ne_bool_of_seq_types
    (tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type
      (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) := by
  have hLenTc :
      __smtx_typeof (__eo_to_smt (mkStrLen tc)) = SmtType.Int := by
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof, htcTy] using smtx_typeof_str_len_seq (__eo_to_smt tc) T htcTy
  have hLenSc :
      __smtx_typeof (__eo_to_smt (mkStrLen sc)) = SmtType.Int := by
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof, hscTy] using smtx_typeof_str_len_seq (__eo_to_smt sc) T hscTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen tc) (mkStrLen sc)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLenTc, hLenSc]
    · rw [hLenTc]
      decide
  simpa [mkNot] using
    RuleProofs.eo_has_bool_type_not_of_bool_arg
      (mkEq (mkStrLen tc) (mkStrLen sc)) hEqBool

private theorem concat_lprop_to_split_ne_stuck_false
    (t s tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_lprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck) :
    __eo_prog_concat_split (Term.Boolean false) (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
      Term.Stuck := by
  rcases eo_prog_concat_lprop_eq_of_ne_stuck (Term.Boolean false) t s tc sc
      hProg with
    ⟨_, hHeadT, hHeadS⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hSplitNe : concatSplitFormula (Term.Boolean false) tc sc ≠ Term.Stuck := by
    rw [concatSplitFormula_false_eq_plain tc sc T htcTy hscTy]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation
      (concatSplitFalseFormula tc sc)
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concatSplitFalseFormula_has_bool_type tc sc T htcTy hscTy))
  have hEq :
      __eo_prog_concat_split (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) =
        concatSplitFormula (Term.Boolean false) tc sc := by
    change
      __eo_requires (concatSplitHead (Term.Boolean false) t) tc
          (__eo_requires (concatSplitHead (Term.Boolean false) s) sc
            (concatSplitFormula (Term.Boolean false)
              (concatSplitHead (Term.Boolean false) t)
              (concatSplitHead (Term.Boolean false) s))) =
        concatSplitFormula (Term.Boolean false) tc sc
    rw [hHeadT, hHeadS]
    simp [__eo_requires, htcNe, hscNe, native_ite, native_teq,
      SmtEval.native_not]
  rw [hEq]
  exact hSplitNe

private theorem concat_lprop_to_split_ne_stuck_true
    (t s tc sc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_lprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck) :
    __eo_prog_concat_split (Term.Boolean true) (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
      Term.Stuck := by
  rcases eo_prog_concat_lprop_eq_of_ne_stuck (Term.Boolean true) t s tc sc
      hProg with
    ⟨_, hHeadT, hHeadS⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hSplitNe : concatSplitFormula (Term.Boolean true) tc sc ≠ Term.Stuck := by
    rw [concatSplitFormula_true_eq_plain tc sc T htcTy hscTy]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation
      (concatSplitTrueFormula tc sc)
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concatSplitTrueFormula_has_bool_type tc sc T htcTy hscTy))
  have hEq :
      __eo_prog_concat_split (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) =
        concatSplitFormula (Term.Boolean true) tc sc := by
    change
      __eo_requires (concatSplitHead (Term.Boolean true) t) tc
          (__eo_requires (concatSplitHead (Term.Boolean true) s) sc
            (concatSplitFormula (Term.Boolean true)
              (concatSplitHead (Term.Boolean true) t)
              (concatSplitHead (Term.Boolean true) s))) =
        concatSplitFormula (Term.Boolean true) tc sc
    rw [hHeadT, hHeadS]
    simp [__eo_requires, htcNe, hscNe, native_ite, native_teq,
      SmtEval.native_not]
  rw [hEq]
  exact hSplitNe

private theorem concat_lprop_false_context
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenGtBool : RuleProofs.eo_has_bool_type (mkGt (mkStrLen tc) (mkStrLen sc)))
    (hProg :
      __eo_prog_concat_lprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T tTail sTail,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
  rcases concat_lprop_head_types_same_of_prog (Term.Boolean false) t s tc sc
      hPremBool hLenGtBool hProg with
    ⟨T, htcTy, hscTy⟩
  have hLenNeBool :=
    concat_lprop_len_ne_bool_of_seq_types tc sc T htcTy hscTy
  have hSplitProg :=
    concat_lprop_to_split_ne_stuck_false t s tc sc T htcTy hscTy hProg
  exact concat_split_false_context M hM t s tc sc hPremBool hLenNeBool
    hSplitProg hST

private theorem concat_lprop_true_context
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenGtBool : RuleProofs.eo_has_bool_type (mkGt (mkStrLen tc) (mkStrLen sc)))
    (hProg :
      __eo_prog_concat_lprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T tPrefix sPrefix,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true := by
  rcases concat_lprop_head_types_same_of_prog (Term.Boolean true) t s tc sc
      hPremBool hLenGtBool hProg with
    ⟨T, htcTy, hscTy⟩
  have hLenNeBool :=
    concat_lprop_len_ne_bool_of_seq_types tc sc T htcTy hscTy
  have hSplitProg :=
    concat_lprop_to_split_ne_stuck_true t s tc sc T htcTy hscTy hProg
  exact concat_split_true_context M hM t s tc sc hPremBool hLenNeBool
    hSplitProg hST

private theorem concat_lprop_lengths_gt_of_gt_eval
    (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hGt : eo_interprets M (mkGt (mkStrLen x) (mkStrLen y)) true) :
    (native_unpack_seq sy).length < (native_unpack_seq sx).length := by
  have hEval :
      __smtx_model_eval M (__eo_to_smt (mkGt (mkStrLen x) (mkStrLen y))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (mkGt (mkStrLen x) (mkStrLen y)) true).mp hGt with
    | intro_true _ hEval => exact hEval
  change
    __smtx_model_eval M
        (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt x))
          (SmtTerm.str_len (__eo_to_smt y))) =
      SmtValue.Boolean true at hEval
  simp [__smtx_model_eval, hxEval, hyEval, __smtx_model_eval_str_len,
    __smtx_model_eval_gt, __smtx_model_eval_lt, native_seq_len, native_zlt,
    SmtEval.native_zlt] at hEval
  exact_mod_cast hEval

private theorem concatLPropFalseFormula_has_bool_type
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatLPropFalseFormula tHead sHead) := by
  let split := concatSplitTerm tHead sHead (Term.Boolean false)
  let nilS := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_false tHead sHead T htTy hsTy
  have hNilSTy :
      __smtx_typeof (__eo_to_smt nilS) = SmtType.Seq T := by
    simpa [nilS] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq sHead T hsTy
  let rhsT := mkConcat sHead (mkConcat split nilS)
  have hSplitNilS :
      __smtx_typeof (__eo_to_smt (mkConcat split nilS)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq split nilS T hSplitTy hNilSTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq sHead
      (mkConcat split nilS) T hsTy hSplitNilS
  have hEqT : RuleProofs.eo_has_bool_type (mkEq tHead rhsT) :=
    eo_has_bool_type_eq_of_seq_type tHead rhsT T htTy hRhsTTy
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
  simpa [concatLPropFalseFormula, split, nilS, rhsT, mkAnd] using
    RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkEq tHead rhsT)
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      hEqT hRight

private theorem concatLPropTrueFormula_has_bool_type
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatLPropTrueFormula tHead sHead) := by
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
  have hSNil :
      __smtx_typeof (__eo_to_smt (mkConcat sHead nilSplit)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq sHead nilSplit T hsTy hNilSplitTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq split
      (mkConcat sHead nilSplit) T hSplitTy hSNil
  have hEqT : RuleProofs.eo_has_bool_type (mkEq tHead rhsT) :=
    eo_has_bool_type_eq_of_seq_type tHead rhsT T htTy hRhsTTy
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
  simpa [concatLPropTrueFormula, split, nilSplit, rhsT, mkAnd] using
    RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkEq tHead rhsT)
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      hEqT hRight

private theorem concatLPropFormula_false_eq_plain
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    concatLPropFormula (Term.Boolean false) tHead sHead =
      concatLPropFalseFormula tHead sHead := by
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
      mkEq tHead
        (mkConcat sHead
          (mkConcat (concatSplitTerm tHead sHead (Term.Boolean false))
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sHead)))) ≠
        Term.Stuck := by
    simp [mkEq, mkConcat]
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
  simp [concatLPropFormula, concatLPropFalseFormula,
    mkEq, mkAnd, mkNot, mkGt, mkStrLen, mkConcat, __eo_mk_apply,
    eo_ite_false]

private theorem concatLPropFormula_true_eq_plain
    (tHead sHead : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T) :
    concatLPropFormula (Term.Boolean true) tHead sHead =
      concatLPropTrueFormula tHead sHead := by
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
      mkEq tHead
        (mkConcat (concatSplitTerm tHead sHead (Term.Boolean true))
          (mkConcat sHead
            (__eo_nil (Term.UOp UserOp.str_concat)
              (__eo_typeof
                (concatSplitTerm tHead sHead (Term.Boolean true)))))) ≠
        Term.Stuck := by
    simp [mkEq, mkConcat]
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
  simp [concatLPropFormula, concatLPropTrueFormula,
    mkEq, mkAnd, mkNot, mkGt, mkStrLen, mkConcat, __eo_mk_apply,
    eo_ite_true]

private theorem facts_concat_lprop_false_formula
    (M : SmtModel) (hM : model_wf M)
    (tc sc tTail sTail : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true)
    (hGt : eo_interprets M (mkGt (mkStrLen tc) (mkStrLen sc)) true) :
    eo_interprets M (concatLPropFalseFormula tc sc) true := by
  let split := concatSplitTerm tc sc (Term.Boolean false)
  let nilS := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sc)
  let rhsT := mkConcat sc (mkConcat split nilS)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_false tc sc T htcTy hscTy
  have hNilSTy :
      __smtx_typeof (__eo_to_smt nilS) = SmtType.Seq T := by
    simpa [nilS] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq sc T hscTy
  have hSplitNilS :
      __smtx_typeof (__eo_to_smt (mkConcat split nilS)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq split nilS T hSplitTy hNilSTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq sc (mkConcat split nilS)
      T hscTy hSplitNilS
  have hEqTBool : RuleProofs.eo_has_bool_type (mkEq tc rhsT) :=
    eo_has_bool_type_eq_of_seq_type tc rhsT T htcTy hRhsTTy
  rcases concat_split_append_eq_of_concat_eq M hM tc tTail sc sTail T
      htcTy htTailTy hscTy hsTailTy hConcatEq with
    ⟨st, stTail, ss, ssTail, htcEval, _htTailEval, hscEval, _hsTailEval,
      hAppend⟩
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have hltOrig :
      (native_unpack_seq ss).length < (native_unpack_seq st).length :=
    concat_lprop_lengths_gt_of_gt_eval M tc sc st ss htcEval hscEval hGt
  have hleOrig :
      (native_unpack_seq ss).length <= (native_unpack_seq st).length :=
    Nat.le_of_lt hltOrig
  have hle : ys.length <= xs.length := by
    simpa [xs, ys] using hleOrig
  have hAppendXY :
      xs ++ native_unpack_seq stTail =
        ys ++ native_unpack_seq ssTail := by
    simpa [xs, ys] using hAppend
  have hList : xs = ys ++ xs.drop ys.length :=
    concat_split_left_eq_append_drop_of_append_eq_of_le xs ys
      (native_unpack_seq stTail) (native_unpack_seq ssTail) hAppendXY hle
  have hSplitEval :
      __smtx_model_eval M (__eo_to_smt split) =
        SmtValue.Seq (native_pack_seq T (xs.drop ys.length)) := by
    simpa [split, xs, ys] using
      eval_concatSplitTerm_false_left M hM tc sc T htcTy hscTy st ss
        htcEval hscEval hleOrig
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hstElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hssElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have hNilSEval :
      __smtx_model_eval M (__eo_to_smt nilS) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nilS] using eval_nil_str_concat_typeof_of_smt_type_seq M sc T hscTy
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhsT) =
        SmtValue.Seq (native_pack_seq T xs) := by
    have hNested := eval_mkConcat_right_nested M sc split nilS T ss
      (native_pack_seq T (xs.drop ys.length)) (SmtSeq.empty T) hscEval
      hSplitEval hNilSEval hssElem
    calc
      __smtx_model_eval M (__eo_to_smt rhsT) =
          SmtValue.Seq
            (native_pack_seq T
              (native_unpack_seq ss ++
                native_unpack_seq (native_pack_seq T (xs.drop ys.length)) ++
                native_unpack_seq (SmtSeq.empty T))) := by
        simpa only [rhsT] using hNested
      _ = SmtValue.Seq (native_pack_seq T xs) := by
        rw [_root_.native_unpack_pack_seq]
        change
          SmtValue.Seq
            (native_pack_seq T (ys ++ xs.drop ys.length ++ [])) =
          SmtValue.Seq (native_pack_seq T xs)
        rw [List.append_nil, ← hList]
  have hEqRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tc))
        (__smtx_model_eval M (__eo_to_smt rhsT)) := by
    unfold RuleProofs.smt_value_rel
    rw [htcEval, hRhsEval]
    exact smt_seq_rel_pack_unpack T st hstElem
  have hEqTrue : eo_interprets M (mkEq tc rhsT) true :=
    RuleProofs.eo_interprets_eq_of_rel M tc rhsT hEqTBool hEqRel
  have hSplitPos : 0 < (xs.drop ys.length).length := by
    rw [List.length_drop]
    have hlt : ys.length < xs.length := by
      simpa [xs, ys] using hltOrig
    exact Nat.sub_pos_of_lt hlt
  have hTailTrue :
      eo_interprets M
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
        true :=
    concat_split_nonempty_tail M split T (xs.drop ys.length) hSplitTy
      hSplitEval hSplitPos
  simpa [concatLPropFalseFormula, split, nilS, rhsT, mkAnd] using
    RuleProofs.eo_interprets_and_intro M (mkEq tc rhsT)
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      hEqTrue hTailTrue

private theorem facts_concat_lprop_true_formula
    (M : SmtModel) (hM : model_wf M)
    (tc sc tPrefix sPrefix : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true)
    (hGt : eo_interprets M (mkGt (mkStrLen tc) (mkStrLen sc)) true) :
    eo_interprets M (concatLPropTrueFormula tc sc) true := by
  let split := concatSplitTerm tc sc (Term.Boolean true)
  let nilSplit := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split)
  let rhsT := mkConcat split (mkConcat sc nilSplit)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_true tc sc T htcTy hscTy
  have hNilSplitTy :
      __smtx_typeof (__eo_to_smt nilSplit) = SmtType.Seq T := by
    simpa [nilSplit] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq split T hSplitTy
  have hSNil :
      __smtx_typeof (__eo_to_smt (mkConcat sc nilSplit)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc nilSplit T hscTy hNilSplitTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq split (mkConcat sc nilSplit)
      T hSplitTy hSNil
  have hEqTBool : RuleProofs.eo_has_bool_type (mkEq tc rhsT) :=
    eo_has_bool_type_eq_of_seq_type tc rhsT T htcTy hRhsTTy
  rcases concat_split_append_eq_of_concat_eq M hM tPrefix tc sPrefix sc T
      htPrefixTy htcTy hsPrefixTy hscTy hConcatEq with
    ⟨stPrefix, st, ssPrefix, ss, _htPrefixEval, htcEval, _hsPrefixEval,
      hscEval, hAppend⟩
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have hltOrig :
      (native_unpack_seq ss).length < (native_unpack_seq st).length :=
    concat_lprop_lengths_gt_of_gt_eval M tc sc st ss htcEval hscEval hGt
  have hleOrig :
      (native_unpack_seq ss).length <= (native_unpack_seq st).length :=
    Nat.le_of_lt hltOrig
  have hle : ys.length <= xs.length := by
    simpa [xs, ys] using hleOrig
  have hAppendXY :
      native_unpack_seq stPrefix ++ xs =
        native_unpack_seq ssPrefix ++ ys := by
    simpa [xs, ys] using hAppend
  have hList : xs = xs.take (xs.length - ys.length) ++ ys :=
    concat_split_suffix_eq_take_append_of_append_eq_of_le
      (native_unpack_seq stPrefix) xs (native_unpack_seq ssPrefix) ys
      hAppendXY hle
  have hSplitEval :
      __smtx_model_eval M (__eo_to_smt split) =
        SmtValue.Seq (native_pack_seq T (xs.take (xs.length - ys.length))) := by
    simpa [split, xs, ys] using
      eval_concatSplitTerm_true_left M hM tc sc T htcTy hscTy st ss
        htcEval hscEval hleOrig
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hstElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hNilSplitEval :
      __smtx_model_eval M (__eo_to_smt nilSplit) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nilSplit] using
      eval_nil_str_concat_typeof_of_smt_type_seq M split T hSplitTy
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhsT) =
        SmtValue.Seq (native_pack_seq T xs) := by
    have hNested := eval_mkConcat_right_nested M split sc nilSplit T
      (native_pack_seq T (xs.take (xs.length - ys.length))) ss
      (SmtSeq.empty T) hSplitEval hscEval hNilSplitEval
      (elem_typeof_pack_seq T (xs.take (xs.length - ys.length)))
    calc
      __smtx_model_eval M (__eo_to_smt rhsT) =
          SmtValue.Seq
            (native_pack_seq T
              (native_unpack_seq
                  (native_pack_seq T (xs.take (xs.length - ys.length))) ++
                native_unpack_seq ss ++ native_unpack_seq (SmtSeq.empty T))) := by
        simpa only [rhsT] using hNested
      _ = SmtValue.Seq (native_pack_seq T xs) := by
        rw [_root_.native_unpack_pack_seq]
        change
          SmtValue.Seq
            (native_pack_seq T
              (xs.take (xs.length - ys.length) ++ ys ++ [])) =
          SmtValue.Seq (native_pack_seq T xs)
        rw [List.append_nil, ← hList]
  have hEqRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tc))
        (__smtx_model_eval M (__eo_to_smt rhsT)) := by
    unfold RuleProofs.smt_value_rel
    rw [htcEval, hRhsEval]
    exact smt_seq_rel_pack_unpack T st hstElem
  have hEqTrue : eo_interprets M (mkEq tc rhsT) true :=
    RuleProofs.eo_interprets_eq_of_rel M tc rhsT hEqTBool hEqRel
  have hDiffPos : 0 < xs.length - ys.length := by
    have hlt : ys.length < xs.length := by
      simpa [xs, ys] using hltOrig
    exact Nat.sub_pos_of_lt hlt
  have hSplitPos : 0 < (xs.take (xs.length - ys.length)).length := by
    rw [List.length_take]
    rw [Nat.min_eq_left (Nat.sub_le _ _)]
    exact hDiffPos
  have hTailTrue :
      eo_interprets M
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
        true :=
    concat_split_nonempty_tail M split T (xs.take (xs.length - ys.length))
      hSplitTy hSplitEval hSplitPos
  simpa [concatLPropTrueFormula, split, nilSplit, rhsT, mkAnd] using
    RuleProofs.eo_interprets_and_intro M (mkEq tc rhsT)
      (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
        (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
      hEqTrue hTailTrue

private theorem eo_prog_concat_lprop_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_lprop rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ t s tc sc,
      x1 = mkEq t s ∧
        x2 = mkGt (mkStrLen tc) (mkStrLen sc) := by
  cases x1 with
  | Apply lhs1 rhs1 =>
      cases lhs1 with
      | Apply op1 t =>
          cases op1 with
          | UOp u1 =>
              cases u1 with
              | eq =>
                  cases x2 with
                  | Apply lhs2 rhs2 =>
                      cases lhs2 with
                      | Apply op2 lhsLen =>
                          cases op2 with
                          | UOp u2 =>
                              cases u2 with
                              | gt =>
                                  cases lhsLen with
                                  | Apply lenOp tc =>
                                      cases lenOp with
                                      | UOp lenU1 =>
                                          cases lenU1 with
                                          | str_len =>
                                              cases rhs2 with
                                              | Apply lenOp2 sc =>
                                                  cases lenOp2 with
                                                  | UOp lenU2 =>
                                                      cases lenU2 with
                                                      | str_len =>
                                                          exact
                                                            ⟨t, rhs1, tc, sc,
                                                              rfl, rfl⟩
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_lprop]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_lprop]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_lprop]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_lprop]
                                                  at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_lprop]
                                              at hProg
                                  | _ =>
                                      cases rev <;>
                                        simp [__eo_prog_concat_lprop] at hProg
                              | _ =>
                                  cases rev <;>
                                    simp [__eo_prog_concat_lprop] at hProg
                          | _ =>
                              cases rev <;> simp [__eo_prog_concat_lprop] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_lprop] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_lprop] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_lprop] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_lprop] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_lprop] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_lprop] at hProg

private theorem step_concat_lprop_core
    (M : SmtModel) (hM : model_wf M)
    (rev t s tc sc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenGtBool : RuleProofs.eo_has_bool_type (mkGt (mkStrLen tc) (mkStrLen sc)))
    (hProg :
      __eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
            (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc)))) =
        Term.Bool) :
    StepRuleProperties M [mkEq t s, mkGt (mkStrLen tc) (mkStrLen sc)]
      (__eo_prog_concat_lprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkGt (mkStrLen tc) (mkStrLen sc)))) := by
  rcases eo_prog_concat_lprop_eq_of_ne_stuck rev t s tc sc hProg with
    ⟨hProgEq, _, _⟩
  rcases concat_lprop_head_types_same_of_prog rev t s tc sc hPremBool
      hLenGtBool hProg with
    ⟨T, htcTy, hscTy⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htcTy]
        exact seq_ne_none T)
  rcases concatLProp_rev_cases_of_prog_ne_stuck rev t s tc sc hProg htcNe
    with hRev | hRev
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hGt :
          eo_interprets M (mkGt (mkStrLen tc) (mkStrLen sc)) true :=
        hPremisesTrue (mkGt (mkStrLen tc) (mkStrLen sc)) (by simp)
      rcases concat_lprop_true_context M hM t s tc sc hPremBool
          hLenGtBool hProg hST with
        ⟨T', tPrefix, sPrefix, htcTy', hscTy', htPrefixTy,
          hsPrefixTy, hConcatEq⟩
      rw [hProgEq]
      rw [concatLPropFormula_true_eq_plain tc sc T' htcTy' hscTy']
      exact facts_concat_lprop_true_formula M hM tc sc tPrefix sPrefix T'
        htcTy' hscTy' htPrefixTy hsPrefixTy hConcatEq hGt
    · rw [hProgEq]
      rw [concatLPropFormula_true_eq_plain tc sc T htcTy hscTy]
      exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concatLPropTrueFormula_has_bool_type tc sc T htcTy hscTy)
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hGt :
          eo_interprets M (mkGt (mkStrLen tc) (mkStrLen sc)) true :=
        hPremisesTrue (mkGt (mkStrLen tc) (mkStrLen sc)) (by simp)
      rcases concat_lprop_false_context M hM t s tc sc hPremBool
          hLenGtBool hProg hST with
        ⟨T', tTail, sTail, htcTy', hscTy', htTailTy, hsTailTy,
          hConcatEq⟩
      rw [hProgEq]
      rw [concatLPropFormula_false_eq_plain tc sc T' htcTy' hscTy']
      exact facts_concat_lprop_false_formula M hM tc sc tTail sTail T'
        htcTy' hscTy' htTailTy hsTailTy hConcatEq hGt
    · rw [hProgEq]
      rw [concatLPropFormula_false_eq_plain tc sc T htcTy hscTy]
      exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concatLPropFalseFormula_has_bool_type tc sc T htcTy hscTy)

private theorem cmd_step_concat_lprop_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_lprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_lprop args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_lprop args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_lprop args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n2 premises =>
                  cases premises with
                  | nil =>
                      let X1 := __eo_state_proven_nth s n1
                      let X2 := __eo_state_proven_nth s n2
                      have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                        hPremisesBool X1 (by simp [X1, premiseTermList])
                      have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
                        hPremisesBool X2 (by simp [X2, premiseTermList])
                      have hProgConcat :
                          __eo_prog_concat_lprop a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_lprop a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_lprop_premise_shapes_of_ne_stuck
                            a1 X1 X2 hProgConcat with
                        ⟨lhs, rhs, lhs1, rhs1, hX1Eq, hX2Eq⟩
                      have hState1Eq :
                          __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                        simpa [X1] using hX1Eq
                      have hState2Eq :
                          __eo_state_proven_nth s n2 =
                            mkGt (mkStrLen lhs1) (mkStrLen rhs1) := by
                        simpa [X2] using hX2Eq
                      have hPremEqBool :
                          RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                        simpa [X1, hState1Eq] using hX1Bool
                      have hLenGtBool :
                          RuleProofs.eo_has_bool_type
                            (mkGt (mkStrLen lhs1) (mkStrLen rhs1)) := by
                        simpa [X2, hState2Eq] using hX2Bool
                      have hProgRule :
                          __eo_prog_concat_lprop a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf (mkGt (mkStrLen lhs1)
                                (mkStrLen rhs1))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_lprop a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf (mkGt (mkStrLen lhs1)
                                  (mkStrLen rhs1)))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_lprop a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_lprop a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_lprop_core M hM a1 lhs rhs lhs1 rhs1
                        hPremEqBool hLenGtBool hProgRule hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)

public theorem cmd_step_concat_lprop_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_lprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_lprop args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_lprop args premises) :=
by
  exact cmd_step_concat_lprop_properties_aux M hM s args premises
