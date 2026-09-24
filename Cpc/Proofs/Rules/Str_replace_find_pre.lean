module

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrReplaceFindPreProof

private abbrev op : Term := Term.UOp UserOp.str_concat

private abbrev concat (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private abbrev replace (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) pat) repl

private abbrev leftTail (pat suffix : Term) : Term := concat pat suffix

private abbrev leftSource (pfx pat suffix : Term) : Term :=
  __eo_list_concat op pfx (leftTail pat suffix)

private abbrev lhs (pat repl pfx suffix : Term) : Term :=
  replace (leftSource pfx pat suffix) pat repl

private abbrev lhsGenerated (pat repl pfx suffix : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_replace)
        (leftSource pfx pat suffix)) pat) repl

private abbrev coreTailGenerated (pat pfx : Term) : Term :=
  __eo_mk_apply (Term.Apply op pat)
    (StringRewriteSupport.prefixPatternNil pfx)

private abbrev coreJoinedGenerated (pfx pat : Term) : Term :=
  __eo_list_concat op pfx (coreTailGenerated pat pfx)

private abbrev coreSourceGenerated (pfx pat : Term) : Term :=
  __eo_list_singleton_elim op (coreJoinedGenerated pfx pat)

private abbrev coreReplaceGenerated
    (pfx pat repl : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_replace)
        (coreSourceGenerated pfx pat)) pat) repl

private abbrev coreReplace (pfx pat repl : Term) : Term :=
  replace (StringRewriteSupport.prefixPatternSource pfx pat) pat repl

private abbrev rightJoinedGenerated
    (pfx pat repl suffix : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply op (coreReplaceGenerated pfx pat repl)) suffix

private abbrev rightJoined (pfx pat repl suffix : Term) : Term :=
  concat (coreReplace pfx pat repl) suffix

private abbrev rhsGenerated
    (pfx pat repl suffix : Term) : Term :=
  __eo_list_singleton_elim op
    (rightJoinedGenerated pfx pat repl suffix)

private abbrev rhs (pfx pat repl suffix : Term) : Term :=
  __eo_list_singleton_elim op (rightJoined pfx pat repl suffix)

private abbrev mkConcl (pat repl pfx suffix : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (lhsGenerated pat repl pfx suffix))
    (rhsGenerated pfx pat repl suffix)

private abbrev concl (pat repl pfx suffix : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lhs pat repl pfx suffix))
    (rhs pfx pat repl suffix)

private theorem prog_mk_form (pat repl pfx suffix : Term)
    (hp : pat ≠ Term.Stuck) (hr : repl ≠ Term.Stuck)
    (hpre : pfx ≠ Term.Stuck) (hsuf : suffix ≠ Term.Stuck) :
    __eo_prog_str_replace_find_pre pat repl pfx suffix =
      mkConcl pat repl pfx suffix := by
  exact __eo_prog_str_replace_find_pre.eq_5
    pat repl pfx suffix hp hr hpre hsuf

private theorem seq_eval_of_type
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    ∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq T := by
    simpa [hxTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hxTy]
        simp)
  exact seq_value_canonical hValTy

private theorem replace_type
    (x pat repl : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hpTy : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq T)
    (hrTy : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (replace x pat repl)) = SmtType.Seq T := by
  change __smtx_typeof
      (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
        (__eo_to_smt repl)) = SmtType.Seq T
  rw [typeof_str_replace_eq]
  simp [hxTy, hpTy, hrTy, __smtx_typeof_seq_op_3,
    native_ite, native_Teq]

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (pat repl pfx suffix U : Term)
    (hPrefixList : __eo_is_list op pfx = Term.Boolean true)
    (hSuffixList : __eo_is_list op suffix = Term.Boolean true)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hPrefixTrans : RuleProofs.eo_has_smt_translation pfx)
    (hSuffixTrans : RuleProofs.eo_has_smt_translation suffix)
    (hSourceEoTy : __eo_typeof (leftSource pfx pat suffix) =
      Term.Apply Term.Seq U)
    (hPatEoTy : __eo_typeof pat = Term.Apply Term.Seq U)
    (hReplEoTy : __eo_typeof repl = Term.Apply Term.Seq U)
    (hSuffixEoTy : __eo_typeof suffix = Term.Apply Term.Seq U)
    (hNilNe : StringRewriteSupport.prefixPatternNil pfx ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (concl pat repl pfx suffix) ∧
      eo_interprets M (concl pat repl pfx suffix) true := by
  let T := __eo_to_smt_type U
  have hPatTy : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      pat U hPatTrans hPatEoTy
  have hReplTy : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      repl U hReplTrans hReplEoTy
  have hSuffixTy : __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      suffix U hSuffixTrans hSuffixEoTy
  have hTailTy : __smtx_typeof (__eo_to_smt (leftTail pat suffix)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq pat suffix T hPatTy hSuffixTy
  have hTailList : __eo_is_list op (leftTail pat suffix) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op pat suffix
      (by simp) hSuffixList
  have hReduce : leftSource pfx pat suffix =
      __eo_list_concat_rec pfx (leftTail pat suffix) :=
    StringRewriteSupport.list_concat_reduce pfx (leftTail pat suffix)
      hPrefixList hTailList
  have hRecEoTy :
      __eo_typeof (__eo_list_concat_rec pfx (leftTail pat suffix)) =
        Term.Apply Term.Seq U := by
    simpa [hReduce] using hSourceEoTy
  have hTailTrans : RuleProofs.eo_has_smt_translation
      (leftTail pat suffix) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailTy]
    exact seq_ne_none T
  have hLeftSourceTy :
      __smtx_typeof (__eo_to_smt (leftSource pfx pat suffix)) =
        SmtType.Seq T := by
    rw [hReduce]
    simpa [T] using
      StrLeqConcatNarySupport.smtx_typeof_list_concat_rec_of_eo_type
        pfx (leftTail pat suffix) U hPrefixList hPrefixTrans
        hTailTrans hRecEoTy
  rcases seq_eval_of_type M hM pat T hPatTy with ⟨spat, hPatEval⟩
  rcases seq_eval_of_type M hM repl T hReplTy with ⟨srepl, hReplEval⟩
  rcases seq_eval_of_type M hM suffix T hSuffixTy with
    ⟨ssuffix, hSuffixEval⟩
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (leftTail pat suffix)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value spat)
            (native_unpack_seq spat ++ native_unpack_seq ssuffix)) := by
    rw [smtx_model_eval_str_concat_term_eq, hPatEval, hSuffixEval]
    rfl
  let tailOut := native_pack_seq (__smtx_elem_typeof_seq_value spat)
    (native_unpack_seq spat ++ native_unpack_seq ssuffix)
  rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
      M hM pfx (leftTail pat suffix) tailOut hPrefixList hTailList
      hPrefixTrans hTailEval with
    ⟨sleft, hLeftEval, hLeftUnpack⟩
  have hLeftUnpack' : native_unpack_seq sleft =
      (StringRewriteSupport.listEvalPrefix M pfx ++
        native_unpack_seq spat) ++ native_unpack_seq ssuffix := by
    rw [hLeftUnpack]
    simp [tailOut, Smtm.native_unpack_pack_seq, List.append_assoc]
  rcases StringRewriteSupport.prefix_pattern_source_type_eval M hM
      pfx pat (leftTail pat suffix) U spat hPrefixList hPrefixTrans
      (by simpa [T] using hPatTy) hPatEval hRecEoTy (by simp) hNilNe with
    ⟨score, hCoreTy, hCoreEval, hCoreUnpack⟩
  have hLhsTy := replace_type (leftSource pfx pat suffix) pat repl T
    hLeftSourceTy hPatTy hReplTy
  have hCoreReplaceTy := replace_type
    (StringRewriteSupport.prefixPatternSource pfx pat) pat repl T
    (by simpa [T] using hCoreTy) hPatTy hReplTy
  let lhsOut := native_pack_seq (__smtx_elem_typeof_seq_value sleft)
    (native_seq_replace (native_unpack_seq sleft)
      (native_unpack_seq spat) (native_unpack_seq srepl))
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs pat repl pfx suffix)) =
        SmtValue.Seq lhsOut := by
    change __smtx_model_eval M
        (SmtTerm.str_replace
          (__eo_to_smt (leftSource pfx pat suffix))
          (__eo_to_smt pat) (__eo_to_smt repl)) = _
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      hLeftEval, hPatEval, hReplEval]
    rfl
  let coreOut := native_pack_seq (__smtx_elem_typeof_seq_value score)
    (native_seq_replace (native_unpack_seq score)
      (native_unpack_seq spat) (native_unpack_seq srepl))
  have hCoreReplaceEval :
      __smtx_model_eval M
          (__eo_to_smt (coreReplace pfx pat repl)) =
        SmtValue.Seq coreOut := by
    change __smtx_model_eval M
        (SmtTerm.str_replace
          (__eo_to_smt
            (StringRewriteSupport.prefixPatternSource pfx pat))
          (__eo_to_smt pat) (__eo_to_smt repl)) = _
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      hCoreEval, hPatEval, hReplEval]
    rfl
  have hRightJoinedTy :
      __smtx_typeof
          (__eo_to_smt (rightJoined pfx pat repl suffix)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (coreReplace pfx pat repl) suffix T
      hCoreReplaceTy hSuffixTy
  have hRightJoinedList :
      __eo_is_list op (rightJoined pfx pat repl suffix) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op
      (coreReplace pfx pat repl) suffix (by simp) hSuffixList
  let joinedOut := native_pack_seq (__smtx_elem_typeof_seq_value coreOut)
    (native_unpack_seq coreOut ++ native_unpack_seq ssuffix)
  have hRightJoinedEval :
      __smtx_model_eval M
          (__eo_to_smt (rightJoined pfx pat repl suffix)) =
        SmtValue.Seq joinedOut := by
    rw [smtx_model_eval_str_concat_term_eq,
      hCoreReplaceEval, hSuffixEval]
    rfl
  have hRhsTy := StringRewriteSupport.singleton_elim_has_seq_type
    (rightJoined pfx pat repl suffix) T hRightJoinedList hRightJoinedTy
  have hRhsEval := StringRewriteSupport.singleton_elim_eval M hM
    (rightJoined pfx pat repl suffix) T joinedOut
    hRightJoinedList hRightJoinedTy hRightJoinedEval
  have hLeftSeqTy : __smtx_typeof_seq_value sleft = SmtType.Seq T := by
    have hValTy := smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt (leftSource pfx pat suffix)) (by
        unfold term_has_non_none_type
        rw [hLeftSourceTy]
        simp)
    simpa [hLeftEval, hLeftSourceTy, __smtx_typeof_value] using hValTy
  have hCoreSeqTy : __smtx_typeof_seq_value score = SmtType.Seq T := by
    have hValTy := smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt (StringRewriteSupport.prefixPatternSource pfx pat)) (by
        unfold term_has_non_none_type
        rw [hCoreTy]
        simp)
    simpa [hCoreEval, hCoreTy, __smtx_typeof_value] using hValTy
  have hLeftElem : __smtx_elem_typeof_seq_value sleft = T :=
    elem_typeof_seq_value_of_typeof_seq_value hLeftSeqTy
  have hCoreElem : __smtx_elem_typeof_seq_value score = T :=
    elem_typeof_seq_value_of_typeof_seq_value hCoreSeqTy
  have hCoreOutUnpack : native_unpack_seq coreOut =
      native_seq_replace (native_unpack_seq score)
        (native_unpack_seq spat) (native_unpack_seq srepl) := by
    simp [coreOut, Smtm.native_unpack_pack_seq]
  have hCoreOutElem : __smtx_elem_typeof_seq_value coreOut = T := by
    unfold coreOut
    rw [hCoreElem]
    exact elem_typeof_pack_seq T _
  have hNative :
      native_seq_replace (native_unpack_seq sleft)
          (native_unpack_seq spat) (native_unpack_seq srepl) =
        native_seq_replace (native_unpack_seq score)
            (native_unpack_seq spat) (native_unpack_seq srepl) ++
          native_unpack_seq ssuffix := by
    rw [hLeftUnpack', hCoreUnpack]
    exact StringRewriteSupport.native_seq_replace_append_after_present
      (StringRewriteSupport.listEvalPrefix M pfx)
      (native_unpack_seq spat) (native_unpack_seq ssuffix)
      (native_unpack_seq srepl)
  have hOutEq : lhsOut = joinedOut := by
    unfold lhsOut joinedOut
    rw [hLeftElem, hCoreOutElem, hCoreOutUnpack, hNative]
  have hBool : RuleProofs.eo_has_bool_type (concl pat repl pfx suffix) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs pat repl pfx suffix) (rhs pfx pat repl suffix)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M
      (lhs pat repl pfx suffix) (rhs pfx pat repl suffix) hBool <| by
    rw [hLhsEval, hRhsEval, hOutEq]
    exact RuleProofs.smt_value_rel_refl _

end StrReplaceFindPreProof

public theorem cmd_step_str_replace_find_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_find_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_find_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_find_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_replace_find_pre args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hTrans.1
              have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                hTrans.2.1
              have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                hTrans.2.2.1
              have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                hTrans.2.2.2.1
              have hA1Ne := RuleProofs.term_ne_stuck_of_has_smt_translation
                a1 hA1Trans
              have hA2Ne := RuleProofs.term_ne_stuck_of_has_smt_translation
                a2 hA2Trans
              have hA3Ne := RuleProofs.term_ne_stuck_of_has_smt_translation
                a3 hA3Trans
              have hA4Ne := RuleProofs.term_ne_stuck_of_has_smt_translation
                a4 hA4Trans
              have hProgMk :
                  __eo_cmd_step_proven s CRule.str_replace_find_pre
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3
                          (CArgList.cons a4 CArgList.nil))))
                      CIndexList.nil =
                    StrReplaceFindPreProof.mkConcl a1 a2 a3 a4 :=
                StrReplaceFindPreProof.prog_mk_form
                  a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne
              have hMkNe : StrReplaceFindPreProof.mkConcl
                  a1 a2 a3 a4 ≠ Term.Stuck := by
                rwa [hProgMk] at hProg
              have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                _ _ hMkNe
              have hRhsGeneratedNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                _ _ hMkNe
              have hLhsGeneratedNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                _ _ hEqFunNe
              have hLeft2Ne := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                _ _ hLhsGeneratedNe
              have hLeft1Ne := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                _ _ hLeft2Ne
              have hLeftSourceNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                _ _ hLeft1Ne
              have hLeftLists :=
                RegexRewriteSupport.list_concat_lists_of_ne_stuck
                  (Term.UOp UserOp.str_concat) a3
                  (StrReplaceFindPreProof.leftTail a1 a4) hLeftSourceNe
              have hA4List :
                  __eo_is_list (Term.UOp UserOp.str_concat) a4 =
                    Term.Boolean true :=
                eo_is_list_tail_true_of_cons_self
                  (Term.UOp UserOp.str_concat) a1 a4 hLeftLists.2
              have hRightJoinedGeneratedNe :=
                str_nary_elim_arg_ne_stuck_of_ne_stuck
                  (StrReplaceFindPreProof.rightJoinedGenerated
                    a3 a1 a2 a4) hRhsGeneratedNe
              have hRightJoinFunNe :=
                eo_mk_apply_fun_ne_stuck_of_ne_stuck
                  _ _ hRightJoinedGeneratedNe
              have hCoreReplaceGeneratedNe :=
                eo_mk_apply_arg_ne_stuck_of_ne_stuck
                  _ _ hRightJoinFunNe
              have hCoreReplace2Ne :=
                eo_mk_apply_fun_ne_stuck_of_ne_stuck
                  _ _ hCoreReplaceGeneratedNe
              have hCoreReplace1Ne :=
                eo_mk_apply_fun_ne_stuck_of_ne_stuck
                  _ _ hCoreReplace2Ne
              have hCoreSourceGeneratedNe :=
                eo_mk_apply_arg_ne_stuck_of_ne_stuck
                  _ _ hCoreReplace1Ne
              have hCoreJoinedGeneratedNe :=
                str_nary_elim_arg_ne_stuck_of_ne_stuck
                  (StrReplaceFindPreProof.coreJoinedGenerated a3 a1)
                  hCoreSourceGeneratedNe
              have hCoreLists :=
                RegexRewriteSupport.list_concat_lists_of_ne_stuck
                  (Term.UOp UserOp.str_concat) a3
                  (StrReplaceFindPreProof.coreTailGenerated a1 a3)
                  hCoreJoinedGeneratedNe
              have hCoreTailGeneratedNe :
                  StrReplaceFindPreProof.coreTailGenerated a1 a3 ≠
                    Term.Stuck := by
                intro h
                rw [h] at hCoreLists
                simp [__eo_is_list] at hCoreLists
              have hNilNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                _ _ hCoreTailGeneratedNe
              have hCoreTailEq :
                  StrReplaceFindPreProof.coreTailGenerated a1 a3 =
                    StringRewriteSupport.prefixPatternTail a3 a1 :=
                eo_mk_apply_eq_apply_of_ne_stuck
                  _ _ hCoreTailGeneratedNe
              have hCoreSourceEq :
                  StrReplaceFindPreProof.coreSourceGenerated a3 a1 =
                    StringRewriteSupport.prefixPatternSource a3 a1 := by
                simp only [StrReplaceFindPreProof.coreSourceGenerated,
                  StrReplaceFindPreProof.coreJoinedGenerated,
                  StringRewriteSupport.prefixPatternSource,
                  StringRewriteSupport.prefixPatternJoined]
                rw [hCoreTailEq]
              have hCoreReplaceEq :
                  StrReplaceFindPreProof.coreReplaceGenerated a3 a1 a2 =
                    StrReplaceFindPreProof.coreReplace a3 a1 a2 := by
                unfold StrReplaceFindPreProof.coreReplaceGenerated
                  StrReplaceFindPreProof.coreReplace
                  StrReplaceFindPreProof.replace
                rw [eo_mk_apply_eq_apply_of_ne_stuck
                  _ _ hCoreReplaceGeneratedNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck
                  _ _ hCoreReplace2Ne]
                rw [eo_mk_apply_eq_apply_of_ne_stuck
                  _ _ hCoreReplace1Ne]
                rw [hCoreSourceEq]
              have hRightJoinedEq :
                  StrReplaceFindPreProof.rightJoinedGenerated
                      a3 a1 a2 a4 =
                    StrReplaceFindPreProof.rightJoined a3 a1 a2 a4 := by
                unfold StrReplaceFindPreProof.rightJoinedGenerated
                  StrReplaceFindPreProof.rightJoined
                  StrReplaceFindPreProof.concat
                rw [eo_mk_apply_eq_apply_of_ne_stuck
                  _ _ hRightJoinedGeneratedNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRightJoinFunNe]
                rw [hCoreReplaceEq]
              have hRhsEq :
                  StrReplaceFindPreProof.rhsGenerated a3 a1 a2 a4 =
                    StrReplaceFindPreProof.rhs a3 a1 a2 a4 := by
                simp only [StrReplaceFindPreProof.rhsGenerated,
                  StrReplaceFindPreProof.rhs]
                rw [hRightJoinedEq]
              have hLhsEq :
                  StrReplaceFindPreProof.lhsGenerated a1 a2 a3 a4 =
                    StrReplaceFindPreProof.lhs a1 a2 a3 a4 := by
                unfold StrReplaceFindPreProof.lhsGenerated
                  StrReplaceFindPreProof.lhs StrReplaceFindPreProof.replace
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsGeneratedNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLeft2Ne]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLeft1Ne]
              have hProgApply :
                  __eo_cmd_step_proven s CRule.str_replace_find_pre
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3
                          (CArgList.cons a4 CArgList.nil))))
                      CIndexList.nil =
                    StrReplaceFindPreProof.concl a1 a2 a3 a4 := by
                rw [hProgMk]
                unfold StrReplaceFindPreProof.mkConcl
                  StrReplaceFindPreProof.concl
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                rw [hLhsEq, hRhsEq]
              have hConclEoTy :
                  __eo_typeof
                      (StrReplaceFindPreProof.concl a1 a2 a3 a4) =
                    Term.Bool := by
                rwa [← hProgApply]
              have hLhsTyNe :
                  __eo_typeof
                      (StrReplaceFindPreProof.lhs a1 a2 a3 a4) ≠
                    Term.Stuck := by
                change __eo_typeof_eq
                    (__eo_typeof
                      (StrReplaceFindPreProof.lhs a1 a2 a3 a4))
                    (__eo_typeof
                      (StrReplaceFindPreProof.rhs a3 a1 a2 a4)) =
                  Term.Bool at hConclEoTy
                exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  _ _ hConclEoTy).1
              change __eo_typeof_str_replace
                  (__eo_typeof
                    (StrReplaceFindPreProof.leftSource a3 a1 a4))
                  (__eo_typeof a1) (__eo_typeof a2) ≠ Term.Stuck
                at hLhsTyNe
              rcases StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                  _ _ _ hLhsTyNe with
                ⟨U, hSourceEoTy, hA1EoTy, hA2EoTy⟩
              have hTailEoTy :
                  __eo_typeof (StrReplaceFindPreProof.leftTail a1 a4) =
                    Term.Apply Term.Seq U := by
                have hRecEoTy :
                    __eo_typeof
                        (__eo_list_concat_rec a3
                          (StrReplaceFindPreProof.leftTail a1 a4)) =
                      Term.Apply Term.Seq U := by
                  rw [← StringRewriteSupport.list_concat_reduce a3
                    (StrReplaceFindPreProof.leftTail a1 a4)
                    hLeftLists.1 hLeftLists.2]
                  exact hSourceEoTy
                exact
                  StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                    a3 (StrReplaceFindPreProof.leftTail a1 a4) U
                    hLeftLists.1 hRecEoTy
              have hTailArgs :=
                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                  a1 a4 U hTailEoTy
              have hFacts := StrReplaceFindPreProof.type_and_facts M hM
                a1 a2 a3 a4 U hLeftLists.1 hA4List
                hA1Trans hA2Trans hA3Trans hA4Trans
                hSourceEoTy hA1EoTy hA2EoTy hTailArgs.2 hNilNe
              refine ⟨?_, ?_⟩
              · intro _hTrue
                rw [hProgApply]
                exact hFacts.2
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by simpa [hProgApply] using hFacts.1)
