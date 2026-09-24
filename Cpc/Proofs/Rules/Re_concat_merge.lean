module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatSupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReConcatMergeProof

private abbrev mkReConcat (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r) s

private abbrev strRe (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) s

private abbrev empty : Term := Term.String []

private abbrev mkStrConcat (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) t

private abbrev mergedString (s t : Term) : Term :=
  mkStrConcat s (mkStrConcat t empty)

private abbrev leftInner (t ys : Term) : Term :=
  mkReConcat (strRe t) ys

private abbrev leftTail (s t ys : Term) : Term :=
  mkReConcat (strRe s) (leftInner t ys)

private abbrev rightTail (s t ys : Term) : Term :=
  mkReConcat (strRe (mergedString s t)) ys

private abbrev lhs (xs s t ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_concat) xs (leftTail s t ys)

private abbrev joined (xs s t ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_concat) xs (rightTail s t ys)

private abbrev rhs (xs s t ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
    (joined xs s t ys)

private abbrev concl (xs s t ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs s t ys))
    (rhs xs s t ys)

private abbrev mkConcl (xs s t ys : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs xs s t ys))
    (rhs xs s t ys)

private theorem prog_mk_form (xs s t ys : Term)
    (hxs : xs ≠ Term.Stuck) (hs : s ≠ Term.Stuck)
    (ht : t ≠ Term.Stuck) (hys : ys ≠ Term.Stuck) :
    __eo_prog_re_concat_merge xs s t ys = mkConcl xs s t ys := by
  exact __eo_prog_re_concat_merge.eq_5 xs s t ys hxs hs ht hys

private theorem eo_typeof_str_to_re_arg_seq_char_of_ne_stuck (T : Term)
    (h : __eo_typeof_str_to_re T ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_to_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_to_re] at h ⊢
            | _ => simp [__eo_typeof_str_to_re] at h
      | _ => simp [__eo_typeof_str_to_re] at h
  | _ => simp [__eo_typeof_str_to_re] at h

private theorem smtx_typeof_str_to_re_of_seq_char (s : Term)
    (hs : __smtx_typeof (__eo_to_smt s) =
      SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (strRe s)) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hs, native_ite, native_Teq]

private theorem smtx_typeof_re_concat_of_reglan (r q : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hq : __smtx_typeof (__eo_to_smt q) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (mkReConcat r q)) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt q)) =
    SmtType.RegLan
  rw [typeof_re_concat_eq]
  simp [hr, hq, native_ite, native_Teq]

private theorem eval_str_re
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hs : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    __smtx_model_eval M (__eo_to_smt (strRe s)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) := by
  change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s)) = _
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hs,
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTy]

private theorem eval_merged_string
    (M : SmtModel) (s t : Term) (ss ts : SmtSeq)
    (hs : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (ht : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ts)
    (hssTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char)
    (htsTy : __smtx_typeof_value (SmtValue.Seq ts) =
      SmtType.Seq SmtType.Char) :
    __smtx_model_eval M (__eo_to_smt (mergedString s t)) =
      SmtValue.Seq
        (native_pack_string
          (native_unpack_string ss ++ native_unpack_string ts)) := by
  have hssSeqTy : __smtx_typeof_seq_value ss =
      SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using hssTy
  have htsSeqTy : __smtx_typeof_seq_value ts =
      SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using htsTy
  have htsElem : __smtx_elem_typeof_seq_value ts = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value htsSeqTy
  have hInner :
      __smtx_model_eval M (__eo_to_smt (mkStrConcat t empty)) =
        SmtValue.Seq ts := by
    rw [smtx_model_eval_str_concat_term_eq, ht]
    change __smtx_model_eval_str_concat (SmtValue.Seq ts)
        (SmtValue.Seq (SmtSeq.empty SmtType.Char)) = SmtValue.Seq ts
    change SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ts)
          (native_unpack_seq ts ++ [])) = SmtValue.Seq ts
    rw [List.append_nil]
    exact congrArg SmtValue.Seq (native_pack_unpack_seq ts)
  rw [smtx_model_eval_str_concat_term_eq, hs, hInner]
  change SmtValue.Seq
      (native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_unpack_seq ss ++ native_unpack_seq ts)) = _
  exact congrArg SmtValue.Seq
    (StrLeqConcatSupport.native_pack_seq_concat_eq_pack_string_append
      ss ts hssSeqTy htsSeqTy)

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (xs s t ys : Term)
    (hXsList :
      __eo_is_list (Term.UOp UserOp.re_concat) xs = Term.Boolean true)
    (hYsList :
      __eo_is_list (Term.UOp UserOp.re_concat) ys = Term.Boolean true)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hYsTrans : RuleProofs.eo_has_smt_translation ys)
    (hSEoTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (hTEoTy : __eo_typeof t = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (concl xs s t ys) ∧
      eo_interprets M (concl xs s t ys) true := by
  have hXsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.RegLan :=
    RegexRewriteSupport.reConcat_list_smt_typeof_reglan_of_non_none xs
      hXsList (by
        simpa [RuleProofs.eo_has_smt_translation] using hXsTrans)
  have hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan :=
    RegexRewriteSupport.reConcat_list_smt_typeof_reglan_of_non_none ys
      hYsList (by
        simpa [RuleProofs.eo_has_smt_translation] using hYsTrans)
  have hSTyRaw :=
    TranslationProofs.eo_to_smt_typeof_matches_translation s hSTrans
  have hSTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char := by
    rw [hSEoTy, TranslationProofs.eo_to_smt_type_seq,
      TranslationProofs.eo_to_smt_type_char] at hSTyRaw
    exact hSTyRaw
  have hTTyRaw :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTTrans
  have hTTy :
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char := by
    rw [hTEoTy, TranslationProofs.eo_to_smt_type_seq,
      TranslationProofs.eo_to_smt_type_char] at hTTyRaw
    exact hTTyRaw
  have hStrSTy := smtx_typeof_str_to_re_of_seq_char s hSTy
  have hStrTTy := smtx_typeof_str_to_re_of_seq_char t hTTy
  have hLeftInnerList :
      __eo_is_list (Term.UOp UserOp.re_concat) (leftInner t ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_concat) (strRe t) ys (by simp) hYsList
  have hLeftTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) (leftTail s t ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_concat) (strRe s) (leftInner t ys)
      (by simp) hLeftInnerList
  have hLeftInnerTy :=
    smtx_typeof_re_concat_of_reglan (strRe t) ys hStrTTy hYsTy
  have hLeftTailTy :=
    smtx_typeof_re_concat_of_reglan (strRe s) (leftInner t ys)
      hStrSTy hLeftInnerTy
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt empty) = SmtType.Seq SmtType.Char := by
    rfl
  have hTEmptyTy :
      __smtx_typeof (__eo_to_smt (mkStrConcat t empty)) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq t empty SmtType.Char hTTy hEmptyTy
  have hMergedTy :
      __smtx_typeof (__eo_to_smt (mergedString s t)) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq s (mkStrConcat t empty)
      SmtType.Char hSTy hTEmptyTy
  have hMergedReTy :=
    smtx_typeof_str_to_re_of_seq_char (mergedString s t) hMergedTy
  have hRightTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) (rightTail s t ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_concat) (strRe (mergedString s t)) ys
      (by simp) hYsList
  have hRightTailTy :=
    smtx_typeof_re_concat_of_reglan (strRe (mergedString s t)) ys
      hMergedReTy hYsTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rxs, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  rcases RuleProofs.ReUnfoldNegSupport.smt_eval_seq_char_of_smt_type_seq_char
      M hM (__eo_to_smt s) hSTy with ⟨ss, hSEval⟩
  rcases RuleProofs.ReUnfoldNegSupport.smt_eval_seq_char_of_smt_type_seq_char
      M hM (__eo_to_smt t) hTTy with ⟨ts, hTEval⟩
  have hSValTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char := by
    simpa [hSEval, hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by unfold term_has_non_none_type; rw [hSTy]; simp)
  have hTValTy : __smtx_typeof_value (SmtValue.Seq ts) =
      SmtType.Seq SmtType.Char := by
    simpa [hTEval, hTTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by unfold term_has_non_none_type; rw [hTTy]; simp)
  have hSSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using hSValTy
  have hTSeqTy : __smtx_typeof_seq_value ts = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value] using hTValTy
  have hStrSEval := eval_str_re M s ss hSEval hSSeqTy
  have hStrTEval := eval_str_re M t ts hTEval hTSeqTy
  have hLeftInnerEval :
      __smtx_model_eval M (__eo_to_smt (leftInner t ys)) =
        SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string ts)) rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt (strRe t)) (__eo_to_smt ys)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      hStrTEval, hYsEval]
  have hLeftTailEval :
      __smtx_model_eval M (__eo_to_smt (leftTail s t ys)) =
        SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string ss))
            (native_re_concat
              (native_str_to_re (native_unpack_string ts)) rys)) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt (strRe s))
          (__eo_to_smt (leftInner t ys))) = _
    -- rewrite the component evaluations before `simp` unfolds
    -- `__eo_to_smt (leftInner ..)` past `hLeftInnerEval`'s left-hand side
    simp only [__smtx_model_eval]
    rw [hStrSEval, hLeftInnerEval]
    simp [__smtx_model_eval_re_concat]
  have hMergedEval :=
    eval_merged_string M s t ss ts hSEval hTEval hSValTy hTValTy
  have hMergedValid :
      native_string_valid
          (native_unpack_string ss ++ native_unpack_string ts) = true := by
    have hSValid := native_unpack_string_valid_of_typeof_seq_char hSSeqTy
    have hTValid := native_unpack_string_valid_of_typeof_seq_char hTSeqTy
    simpa [native_string_valid, List.all_append, hSValid, hTValid] using
      And.intro hSValid hTValid
  have hMergedReEval := eval_str_re M (mergedString s t)
    (native_pack_string
      (native_unpack_string ss ++ native_unpack_string ts)) hMergedEval
    (typeof_pack_string _ hMergedValid)
  have hRightTailEval :
      __smtx_model_eval M (__eo_to_smt (rightTail s t ys)) =
        SmtValue.RegLan
          (native_re_concat
            (native_str_to_re
              (native_unpack_string ss ++ native_unpack_string ts)) rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (__eo_to_smt (strRe (mergedString s t))) (__eo_to_smt ys)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      hMergedReEval, hYsEval, impl_native_string_to_values,
      RuleProofs.native_unpack_string_pack_string]
  rcases RuleProofs.reConcat_list_concat_eval_rel M xs (leftTail s t ys)
      rxs _ hXsList hLeftTailList hXsTy hLeftTailTy
      hXsEval hLeftTailEval with
    ⟨rlhs, hLhsEval, hLhsTy, hLhsRel⟩
  rcases RuleProofs.reConcat_list_concat_eval_rel M xs (rightTail s t ys)
      rxs _ hXsList hRightTailList hXsTy hRightTailTy
      hXsEval hRightTailEval with
    ⟨rjoined, hJoinedEval, hJoinedTy, hJoinedRel⟩
  have hJoinedList :
      __eo_is_list (Term.UOp UserOp.re_concat) (joined xs s t ys) =
        Term.Boolean true := by
    have hReduce : joined xs s t ys =
        __eo_list_concat_rec xs (rightTail s t ys) := by
      simp [joined, __eo_list_concat, hXsList, hRightTailList,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not]
    rw [hReduce]
    exact eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.re_concat) xs (rightTail s t ys)
      hXsList hRightTailList
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs xs s t ys)) = SmtType.RegLan :=
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
      (joined xs s t ys) hJoinedList hJoinedTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM
      (rhs xs s t ys) hRhsTy with ⟨rrhs, hRhsEval⟩
  have hRhsRel : RuleProofs.smt_value_rel (SmtValue.RegLan rrhs)
      (SmtValue.RegLan rjoined) := by
    simpa [hRhsEval, hJoinedEval] using
      RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_rel_eval
        M (joined xs s t ys) hJoinedList ⟨rjoined, hJoinedEval⟩
  have hTailMerge : RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat
          (native_str_to_re (native_unpack_string ss))
          (native_re_concat
            (native_str_to_re (native_unpack_string ts)) rys)))
      (SmtValue.RegLan
        (native_re_concat
          (native_str_to_re
            (native_unpack_string ss ++ native_unpack_string ts)) rys)) := by
    exact RuleProofs.smt_value_rel_trans _ _ _
      (RuleProofs.smt_value_rel_symm _ _
        (RuleProofs.smt_value_rel_re_concat_assoc
          (native_str_to_re (native_unpack_string ss))
          (native_str_to_re (native_unpack_string ts)) rys))
      (RuleProofs.smt_value_rel_re_concat_congr
        (RuleProofs.smt_value_rel_str_to_re_append
          (native_unpack_string ss) (native_unpack_string ts))
        (RuleProofs.smt_value_rel_refl (SmtValue.RegLan rys)))
  have hCore := RuleProofs.smt_value_rel_re_concat_congr
    (RuleProofs.smt_value_rel_refl (SmtValue.RegLan rxs)) hTailMerge
  have hBool : RuleProofs.eo_has_bool_type (concl xs s t ys) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs s t ys) (rhs xs s t ys)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M
      (lhs xs s t ys) (rhs xs s t ys) hBool <| by
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_trans _ _ _ hLhsRel <|
      RuleProofs.smt_value_rel_trans _ _ _ hCore <|
      RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_symm _ _ hJoinedRel)
        (RuleProofs.smt_value_rel_symm _ _ hRhsRel)

end ReConcatMergeProof

public theorem cmd_step_re_concat_merge_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_merge args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_concat_merge args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_merge args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_concat_merge args premises ≠
      Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a1 args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons a2 args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons a3 args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons a4 args =>
          cases args with
          | cons _ _ => exact False.elim (hProg rfl)
          | nil =>
            cases premises with
            | cons _ _ => exact False.elim (hProg rfl)
            | nil =>
              have hTrans : cArgListTranslationOk
                  (CArgList.cons a1 (CArgList.cons a2
                    (CArgList.cons a3 (CArgList.cons a4 CArgList.nil)))) :=
                hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hTrans.1
              have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hTrans.2.1
              have hA3Trans : RuleProofs.eo_has_smt_translation a3 := hTrans.2.2.1
              have hA4Trans : RuleProofs.eo_has_smt_translation a4 := hTrans.2.2.2.1
              have hProgLocal :
                  __eo_prog_re_concat_merge a1 a2 a3 a4 ≠ Term.Stuck := hProg
              have hA1Ne : a1 ≠ Term.Stuck := by
                intro h; subst a1
                exact hProgLocal (__eo_prog_re_concat_merge.eq_1 a2 a3 a4)
              have hA2Ne : a2 ≠ Term.Stuck := by
                intro h; subst a2
                exact hProgLocal (__eo_prog_re_concat_merge.eq_2 a1 a3 a4 hA1Ne)
              have hA3Ne : a3 ≠ Term.Stuck := by
                intro h; subst a3
                exact hProgLocal
                  (__eo_prog_re_concat_merge.eq_3 a1 a2 a4 hA1Ne hA2Ne)
              have hA4Ne : a4 ≠ Term.Stuck := by
                intro h; subst a4
                exact hProgLocal
                  (__eo_prog_re_concat_merge.eq_4 a1 a2 a3 hA1Ne hA2Ne hA3Ne)
              have hProgMk :
                  __eo_cmd_step_proven s CRule.re_concat_merge
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3 (CArgList.cons a4 CArgList.nil))))
                      CIndexList.nil =
                    ReConcatMergeProof.mkConcl a1 a2 a3 a4 :=
                ReConcatMergeProof.prog_mk_form a1 a2 a3 a4
                  hA1Ne hA2Ne hA3Ne hA4Ne
              have hMkNe : ReConcatMergeProof.mkConcl a1 a2 a3 a4 ≠
                  Term.Stuck := by simpa [hProgMk] using hProg
              have hEqFunNe :
                  __eo_mk_apply (Term.UOp UserOp.eq)
                      (ReConcatMergeProof.lhs a1 a2 a3 a4) ≠ Term.Stuck :=
                eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
              have hLhsNe : ReConcatMergeProof.lhs a1 a2 a3 a4 ≠
                  Term.Stuck :=
                eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
              have hLists := RegexRewriteSupport.list_concat_lists_of_ne_stuck
                (Term.UOp UserOp.re_concat) a1
                (ReConcatMergeProof.leftTail a2 a3 a4) hLhsNe
              have hInnerList :
                  __eo_is_list (Term.UOp UserOp.re_concat)
                      (ReConcatMergeProof.leftInner a3 a4) = Term.Boolean true :=
                eo_is_list_tail_true_of_cons_self
                  (Term.UOp UserOp.re_concat) (ReConcatMergeProof.strRe a2)
                  (ReConcatMergeProof.leftInner a3 a4) hLists.2
              have hYsList :
                  __eo_is_list (Term.UOp UserOp.re_concat) a4 =
                    Term.Boolean true :=
                eo_is_list_tail_true_of_cons_self
                  (Term.UOp UserOp.re_concat) (ReConcatMergeProof.strRe a3)
                  a4 hInnerList
              have hProgApply :
                  __eo_cmd_step_proven s CRule.re_concat_merge
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3 (CArgList.cons a4 CArgList.nil))))
                      CIndexList.nil =
                    ReConcatMergeProof.concl a1 a2 a3 a4 := by
                rw [hProgMk]
                unfold ReConcatMergeProof.mkConcl ReConcatMergeProof.concl
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
              have hConclTy :
                  __eo_typeof (ReConcatMergeProof.concl a1 a2 a3 a4) =
                    Term.Bool := by rwa [← hProgApply]
              have hLhsTyNe :
                  __eo_typeof (ReConcatMergeProof.lhs a1 a2 a3 a4) ≠
                    Term.Stuck := by
                change __eo_typeof_eq
                    (__eo_typeof (ReConcatMergeProof.lhs a1 a2 a3 a4))
                    (__eo_typeof (ReConcatMergeProof.rhs a1 a2 a3 a4)) =
                  Term.Bool at hConclTy
                exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
                  hConclTy).1
              have hLhsTyNe' := hLhsTyNe
              change __eo_typeof
                  (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                    (ReConcatMergeProof.leftTail a2 a3 a4)) ≠
                Term.Stuck at hLhsTyNe'
              rw [RuleProofs.list_concat_reduce (Term.UOp UserOp.re_concat)
                a1 (ReConcatMergeProof.leftTail a2 a3 a4)
                hLists.1 hLists.2] at hLhsTyNe'
              have hTailTyNe := RuleProofs.list_concat_rec_tail_typeof_ne_stuck
                a1 (ReConcatMergeProof.leftTail a2 a3 a4)
                hLists.1 hLhsTyNe'
              have hOuterInv := RuleProofs.eo_typeof_re_concat_term_args
                (ReConcatMergeProof.strRe a2)
                (ReConcatMergeProof.leftInner a3 a4) hTailTyNe
              have hInnerTyNe :
                  __eo_typeof (ReConcatMergeProof.leftInner a3 a4) ≠
                    Term.Stuck := by rw [hOuterInv.2]; decide
              have hInnerInv := RuleProofs.eo_typeof_re_concat_term_args
                (ReConcatMergeProof.strRe a3) a4 hInnerTyNe
              have hStrSNe :
                  __eo_typeof (ReConcatMergeProof.strRe a2) ≠ Term.Stuck := by
                rw [hOuterInv.1]; decide
              have hStrTNe :
                  __eo_typeof (ReConcatMergeProof.strRe a3) ≠ Term.Stuck := by
                rw [hInnerInv.1]; decide
              change __eo_typeof_str_to_re (__eo_typeof a2) ≠ Term.Stuck
                at hStrSNe
              change __eo_typeof_str_to_re (__eo_typeof a3) ≠ Term.Stuck
                at hStrTNe
              have hA2EoTy :=
                ReConcatMergeProof.eo_typeof_str_to_re_arg_seq_char_of_ne_stuck
                  (__eo_typeof a2) hStrSNe
              have hA3EoTy :=
                ReConcatMergeProof.eo_typeof_str_to_re_arg_seq_char_of_ne_stuck
                  (__eo_typeof a3) hStrTNe
              have hFacts := ReConcatMergeProof.type_and_facts M hM
                a1 a2 a3 a4 hLists.1 hYsList
                hA1Trans hA2Trans hA3Trans hA4Trans hA2EoTy hA3EoTy
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                (by simpa [hProgApply] using hFacts.1)⟩
              intro _hTrue
              rw [hProgApply]
              exact hFacts.2
