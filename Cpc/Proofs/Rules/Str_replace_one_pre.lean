module

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrReplaceOnePreProof

private abbrev op : Term := Term.UOp UserOp.str_concat

private abbrev concat (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private abbrev replace (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) pat) repl

private abbrev lenPremise (pat : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len pat))
    (Term.Numeral 1)

private abbrev nilFor (x : Term) : Term :=
  __eo_nil op (__eo_typeof x)

private abbrev endTail (t pfx : Term) : Term :=
  concat t (nilFor pfx)

private abbrev middleJoined (middle t pfx : Term) : Term :=
  __eo_list_concat op middle (endTail t pfx)

private abbrev leftTail (t middle pfx : Term) : Term :=
  concat t (middleJoined middle t pfx)

private abbrev leftSource (t pfx middle : Term) : Term :=
  __eo_list_concat op pfx (leftTail t middle pfx)

private abbrev lhs (t pat repl pfx middle : Term) : Term :=
  replace (leftSource t pfx middle) pat repl

private abbrev coreSource (t pfx middle : Term) : Term :=
  StringRewriteSupport.prefixListSource pfx t middle

private abbrev coreReplace
    (t pat repl pfx middle : Term) : Term :=
  replace (coreSource t pfx middle) pat repl

private abbrev rhsTail
    (t pat repl pfx middle : Term) : Term :=
  concat t (nilFor (coreReplace t pat repl pfx middle))

private abbrev rhs (t pat repl pfx middle : Term) : Term :=
  concat (coreReplace t pat repl pfx middle)
    (rhsTail t pat repl pfx middle)

private abbrev concl (t pat repl pfx middle : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lhs t pat repl pfx middle))
    (rhs t pat repl pfx middle)

private abbrev endTailGenerated (t pfx : Term) : Term :=
  __eo_mk_apply (Term.Apply op t) (nilFor pfx)

private abbrev middleJoinedGenerated (middle t pfx : Term) : Term :=
  __eo_list_concat op middle (endTailGenerated t pfx)

private abbrev leftTailGenerated (t middle pfx : Term) : Term :=
  __eo_mk_apply (Term.Apply op t)
    (middleJoinedGenerated middle t pfx)

private abbrev leftSourceGenerated (t pfx middle : Term) : Term :=
  __eo_list_concat op pfx (leftTailGenerated t middle pfx)

private abbrev lhsGenerated (t pat repl pfx middle : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_replace)
        (leftSourceGenerated t pfx middle)) pat) repl

private abbrev coreSourceGenerated (t pfx middle : Term) : Term :=
  __eo_list_singleton_elim op
    (__eo_list_concat op pfx (Term.Apply (Term.Apply op t) middle))

private abbrev coreReplaceGenerated
    (t pat repl pfx middle : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_replace)
        (coreSourceGenerated t pfx middle)) pat) repl

private abbrev rhsTailGenerated
    (t pat repl pfx middle : Term) : Term :=
  __eo_mk_apply (Term.Apply op t)
    (__eo_nil op
      (__eo_typeof (coreReplaceGenerated t pat repl pfx middle)))

private abbrev rhsGenerated
    (t pat repl pfx middle : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply op (coreReplaceGenerated t pat repl pfx middle))
    (rhsTailGenerated t pat repl pfx middle)

private abbrev bodyGenerated
    (t pat repl pfx middle : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (lhsGenerated t pat repl pfx middle))
    (rhsGenerated t pat repl pfx middle)

private theorem prog_info
    (t pat repl pfx middle P : Term)
    (hProg :
      __eo_prog_str_replace_one_pre t pat repl pfx middle (Proof.pf P) ≠
        Term.Stuck) :
    P = lenPremise pat ∧
      __eo_prog_str_replace_one_pre t pat repl pfx middle (Proof.pf P) =
        bodyGenerated t pat repl pfx middle := by
  unfold __eo_prog_str_replace_one_pre at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hp := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨rfl, ?_⟩
    simp [__eo_prog_str_replace_one_pre, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      bodyGenerated, lhsGenerated, leftSourceGenerated,
      leftTailGenerated, middleJoinedGenerated, endTailGenerated,
      coreSourceGenerated, coreReplaceGenerated, rhsGenerated,
      rhsTailGenerated]

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
    (t pat repl pfx middle U : Term)
    (hPfxList : __eo_is_list op pfx = Term.Boolean true)
    (hMiddleList : __eo_is_list op middle = Term.Boolean true)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hPfxTrans : RuleProofs.eo_has_smt_translation pfx)
    (hMiddleTrans : RuleProofs.eo_has_smt_translation middle)
    (hTEoTy : __eo_typeof t = Term.Apply Term.Seq U)
    (hPatEoTy : __eo_typeof pat = Term.Apply Term.Seq U)
    (hReplEoTy : __eo_typeof repl = Term.Apply Term.Seq U)
    (hPfxEoTy : __eo_typeof pfx = Term.Apply Term.Seq U)
    (hSourceEoTy : __eo_typeof (leftSource t pfx middle) =
      Term.Apply Term.Seq U)
    (hMiddleRecEoTy :
      __eo_typeof (__eo_list_concat_rec middle (endTail t pfx)) =
        Term.Apply Term.Seq U)
    (hCoreSourceEoTy : __eo_typeof (coreSource t pfx middle) =
      Term.Apply Term.Seq U) :
    RuleProofs.eo_has_bool_type (concl t pat repl pfx middle) ∧
      ∃ spat,
        __smtx_model_eval M (__eo_to_smt pat) = SmtValue.Seq spat ∧
        ((native_unpack_seq spat).length = 1 →
          eo_interprets M (concl t pat repl pfx middle) true) := by
  let T := __eo_to_smt_type U
  have hTTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      t U hTTrans hTEoTy
  have hPatTy : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      pat U hPatTrans hPatEoTy
  have hReplTy : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      repl U hReplTrans hReplEoTy
  have hPfxTy : __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
    simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
      pfx U hPfxTrans hPfxEoTy
  rcases seq_eval_of_type M hM t T hTTy with ⟨st, hTEval⟩
  rcases seq_eval_of_type M hM pat T hPatTy with ⟨spat, hPatEval⟩
  rcases seq_eval_of_type M hM repl T hReplTy with ⟨srepl, hReplEval⟩
  have hNilPfxTy :
      __smtx_typeof (__eo_to_smt (nilFor pfx)) = SmtType.Seq T :=
    smt_typeof_nil_str_concat_typeof_of_smt_type_seq pfx T hPfxTy
  have hNilPfxEval :
      __smtx_model_eval M (__eo_to_smt (nilFor pfx)) =
        SmtValue.Seq (SmtSeq.empty T) :=
    eval_nil_str_concat_typeof_of_smt_type_seq M pfx T hPfxTy
  have hNilPfxNil : __eo_is_list_nil op (nilFor pfx) =
      Term.Boolean true := by
    have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
      pfx (by rw [hPfxTy]; exact seq_ne_none T)
    have hTy : __eo_to_smt_type (__eo_typeof pfx) = SmtType.Seq T := by
      rw [← hMatch, hPfxTy]
    exact strConcat_nil_is_list_nil_of_type hTy
  have hNilPfxList : __eo_is_list op (nilFor pfx) = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true _ hNilPfxNil
  have hEndList : __eo_is_list op (endTail t pfx) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op t (nilFor pfx)
      (by simp) hNilPfxList
  have hEndTy : __smtx_typeof (__eo_to_smt (endTail t pfx)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t (nilFor pfx) T hTTy hNilPfxTy
  let endOut := native_pack_seq (__smtx_elem_typeof_seq_value st)
    (native_unpack_seq st)
  have hEndEval :
      __smtx_model_eval M (__eo_to_smt (endTail t pfx)) =
        SmtValue.Seq endOut := by
    rw [smtx_model_eval_str_concat_term_eq, hTEval, hNilPfxEval]
    change SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value st)
          (native_unpack_seq st ++ [])) = _
    rw [List.append_nil]
  have hEndTrans : RuleProofs.eo_has_smt_translation (endTail t pfx) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hEndTy]
    exact seq_ne_none T
  have hMiddleJoinedTy :
      __smtx_typeof (__eo_to_smt (middleJoined middle t pfx)) =
        SmtType.Seq T := by
    change __smtx_typeof
        (__eo_to_smt
          (__eo_list_concat (Term.UOp UserOp.str_concat) middle
            (endTail t pfx))) = SmtType.Seq T
    rw [StringRewriteSupport.list_concat_reduce middle (endTail t pfx)
      hMiddleList hEndList]
    simpa [T] using
      StrLeqConcatNarySupport.smtx_typeof_list_concat_rec_of_eo_type
        middle (endTail t pfx) U hMiddleList hMiddleTrans
        hEndTrans hMiddleRecEoTy
  rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
      M hM middle (endTail t pfx) endOut hMiddleList hEndList
      hMiddleTrans hEndEval with
    ⟨smiddle, hMiddleEval, hMiddleUnpack⟩
  have hMiddleUnpack' : native_unpack_seq smiddle =
      StringRewriteSupport.listEvalPrefix M middle ++ native_unpack_seq st := by
    simpa [endOut, Smtm.native_unpack_pack_seq] using hMiddleUnpack
  have hLeftTailList : __eo_is_list op (leftTail t middle pfx) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op t
      (middleJoined middle t pfx) (by simp)
      (StringRewriteSupport.list_concat_is_list middle (endTail t pfx)
        hMiddleList hEndList)
  have hLeftTailTy :
      __smtx_typeof (__eo_to_smt (leftTail t middle pfx)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t (middleJoined middle t pfx) T
      hTTy hMiddleJoinedTy
  let leftTailOut := native_pack_seq (__smtx_elem_typeof_seq_value st)
    (native_unpack_seq st ++ native_unpack_seq smiddle)
  have hLeftTailEval :
      __smtx_model_eval M (__eo_to_smt (leftTail t middle pfx)) =
        SmtValue.Seq leftTailOut := by
    rw [smtx_model_eval_str_concat_term_eq, hTEval, hMiddleEval]
    rfl
  have hLeftSourceTy :
      __smtx_typeof (__eo_to_smt (leftSource t pfx middle)) =
        SmtType.Seq T :=
    StringRewriteSupport.list_concat_has_seq_type pfx
      (leftTail t middle pfx) T hPfxList hLeftTailList
      hPfxTy hLeftTailTy
  rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
      M hM pfx (leftTail t middle pfx) leftTailOut
      hPfxList hLeftTailList hPfxTrans hLeftTailEval with
    ⟨sleft, hLeftEval, hLeftUnpack⟩
  have hLeftUnpack' : native_unpack_seq sleft =
      (((StringRewriteSupport.listEvalPrefix M pfx ++ native_unpack_seq st) ++
          StringRewriteSupport.listEvalPrefix M middle) ++
        native_unpack_seq st) := by
    rw [hLeftUnpack]
    simp [leftTailOut, Smtm.native_unpack_pack_seq,
      hMiddleUnpack', List.append_assoc]
  rcases StringRewriteSupport.prefix_list_source_type_eval M hM
      pfx t middle (endTail t pfx) U st hPfxList hMiddleList
      (by simpa [T] using hPfxTy) hMiddleTrans
      (by simpa [T] using hTTy) hTEval hMiddleRecEoTy (by simp)
      hCoreSourceEoTy with
    ⟨score, hCoreTy, hCoreEval, hCoreUnpack⟩
  have hLhsTy := replace_type (leftSource t pfx middle) pat repl T
    hLeftSourceTy hPatTy hReplTy
  have hCoreReplaceTy := replace_type (coreSource t pfx middle)
    pat repl T (by simpa [T] using hCoreTy) hPatTy hReplTy
  let lhsOut := native_pack_seq (__smtx_elem_typeof_seq_value sleft)
    (native_seq_replace (native_unpack_seq sleft)
      (native_unpack_seq spat) (native_unpack_seq srepl))
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs t pat repl pfx middle)) =
        SmtValue.Seq lhsOut := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt (leftSource t pfx middle))
          (__eo_to_smt pat) (__eo_to_smt repl)) = _
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      hLeftEval, hPatEval, hReplEval]
    rfl
  let coreOut := native_pack_seq (__smtx_elem_typeof_seq_value score)
    (native_seq_replace (native_unpack_seq score)
      (native_unpack_seq spat) (native_unpack_seq srepl))
  have hCoreReplaceEval :
      __smtx_model_eval M
          (__eo_to_smt (coreReplace t pat repl pfx middle)) =
        SmtValue.Seq coreOut := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt (coreSource t pfx middle))
          (__eo_to_smt pat) (__eo_to_smt repl)) = _
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      hCoreEval, hPatEval, hReplEval]
    rfl
  have hNilCoreTy :
      __smtx_typeof
          (__eo_to_smt (nilFor (coreReplace t pat repl pfx middle))) =
        SmtType.Seq T :=
    smt_typeof_nil_str_concat_typeof_of_smt_type_seq _ T hCoreReplaceTy
  have hNilCoreEval :
      __smtx_model_eval M
          (__eo_to_smt (nilFor (coreReplace t pat repl pfx middle))) =
        SmtValue.Seq (SmtSeq.empty T) :=
    eval_nil_str_concat_typeof_of_smt_type_seq M _ T hCoreReplaceTy
  have hRhsTailTy :
      __smtx_typeof
          (__eo_to_smt (rhsTail t pat repl pfx middle)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t _ T hTTy hNilCoreTy
  let rhsTailOut := native_pack_seq (__smtx_elem_typeof_seq_value st)
    (native_unpack_seq st)
  have hRhsTailEval :
      __smtx_model_eval M
          (__eo_to_smt (rhsTail t pat repl pfx middle)) =
        SmtValue.Seq rhsTailOut := by
    rw [smtx_model_eval_str_concat_term_eq, hTEval, hNilCoreEval]
    change SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value st)
          (native_unpack_seq st ++ [])) = _
    rw [List.append_nil]
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhs t pat repl pfx middle)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (coreReplace t pat repl pfx middle)
      (rhsTail t pat repl pfx middle) T hCoreReplaceTy hRhsTailTy
  let rhsOut := native_pack_seq (__smtx_elem_typeof_seq_value coreOut)
    (native_unpack_seq coreOut ++ native_unpack_seq rhsTailOut)
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhs t pat repl pfx middle)) =
        SmtValue.Seq rhsOut := by
    rw [smtx_model_eval_str_concat_term_eq,
      hCoreReplaceEval, hRhsTailEval]
    rfl
  have hLeftSeqTy : __smtx_typeof_seq_value sleft = SmtType.Seq T := by
    have hValTy := smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt (leftSource t pfx middle)) (by
        unfold term_has_non_none_type
        rw [hLeftSourceTy]
        simp)
    simpa [hLeftEval, hLeftSourceTy, __smtx_typeof_value] using hValTy
  have hCoreSeqTy : __smtx_typeof_seq_value score = SmtType.Seq T := by
    have hValTy := smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt (coreSource t pfx middle)) (by
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
  have hRhsTailUnpack : native_unpack_seq rhsTailOut =
      native_unpack_seq st := by
    simp [rhsTailOut, Smtm.native_unpack_pack_seq]
  have hBool : RuleProofs.eo_has_bool_type (concl t pat repl pfx middle) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs t pat repl pfx middle) (rhs t pat repl pfx middle)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  refine ⟨hBool, spat, hPatEval, ?_⟩
  intro hPatLen
  have hNative :
      native_seq_replace (native_unpack_seq sleft)
          (native_unpack_seq spat) (native_unpack_seq srepl) =
        native_seq_replace (native_unpack_seq score)
            (native_unpack_seq spat) (native_unpack_seq srepl) ++
          native_unpack_seq st := by
    rw [hLeftUnpack', hCoreUnpack]
    exact StringRewriteSupport.native_seq_replace_duplicate_suffix_of_pattern_length_one
      (StringRewriteSupport.listEvalPrefix M pfx)
      (native_unpack_seq st)
      (StringRewriteSupport.listEvalPrefix M middle)
      (native_unpack_seq spat) (native_unpack_seq srepl) hPatLen
  have hOutEq : lhsOut = rhsOut := by
    unfold lhsOut rhsOut
    rw [hLeftElem, hCoreOutElem, hCoreOutUnpack,
      hRhsTailUnpack, hNative]
  exact RuleProofs.eo_interprets_eq_of_rel M
      (lhs t pat repl pfx middle) (rhs t pat repl pfx middle) hBool <| by
    rw [hLhsEval, hRhsEval, hOutEq]
    exact RuleProofs.smt_value_rel_refl _

end StrReplaceOnePreProof

public theorem cmd_step_str_replace_one_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_one_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_one_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_one_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_replace_one_pre args premises ≠
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
          | nil => exact False.elim (hProg rfl)
          | cons a5 args =>
            cases args with
            | cons _ _ => exact False.elim (hProg rfl)
            | nil =>
              cases premises with
              | nil => exact False.elim (hProg rfl)
              | cons n premises =>
                cases premises with
                | cons _ _ => exact False.elim (hProg rfl)
                | nil =>
                  let P := __eo_state_proven_nth s n
                  have hTrans : cArgListTranslationOk
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3 (CArgList.cons a4
                          (CArgList.cons a5 CArgList.nil))))) :=
                    hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                    hTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                    hTrans.2.1
                  have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                    hTrans.2.2.1
                  have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                    hTrans.2.2.2.1
                  have hA5Trans : RuleProofs.eo_has_smt_translation a5 :=
                    hTrans.2.2.2.2.1
                  change __eo_typeof
                      (__eo_prog_str_replace_one_pre a1 a2 a3 a4 a5
                        (Proof.pf P)) = Term.Bool at hResultTy
                  have hProgLocal :
                      __eo_prog_str_replace_one_pre a1 a2 a3 a4 a5
                          (Proof.pf P) ≠ Term.Stuck :=
                    term_ne_stuck_of_typeof_bool hResultTy
                  rcases StrReplaceOnePreProof.prog_info
                      a1 a2 a3 a4 a5 P hProgLocal with
                    ⟨hPremShape, hBodyEq⟩
                  have hBodyNe :
                      StrReplaceOnePreProof.bodyGenerated
                          a1 a2 a3 a4 a5 ≠ Term.Stuck := by
                    rwa [hBodyEq] at hProgLocal
                  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                    _ _ hBodyNe
                  have hRhsGeneratedNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                    _ _ hBodyNe
                  have hLhsGeneratedNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                    _ _ hEqFunNe
                  have hLeft2Ne := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                    _ _ hLhsGeneratedNe
                  have hLeft1Ne := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                    _ _ hLeft2Ne
                  have hLeftSourceGeneratedNe :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hLeft1Ne
                  have hOuterLists :=
                    RegexRewriteSupport.list_concat_lists_of_ne_stuck
                      (Term.UOp UserOp.str_concat) a4
                      (StrReplaceOnePreProof.leftTailGenerated a1 a5 a4)
                      hLeftSourceGeneratedNe
                  have hLeftTailGeneratedNe :
                      StrReplaceOnePreProof.leftTailGenerated a1 a5 a4 ≠
                        Term.Stuck := by
                    intro h
                    rw [h] at hOuterLists
                    simp [__eo_is_list] at hOuterLists
                  have hMiddleJoinedGeneratedNe :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck
                      _ _ hLeftTailGeneratedNe
                  have hMiddleLists :=
                    RegexRewriteSupport.list_concat_lists_of_ne_stuck
                      (Term.UOp UserOp.str_concat) a5
                      (StrReplaceOnePreProof.endTailGenerated a1 a4)
                      hMiddleJoinedGeneratedNe
                  have hEndTailGeneratedNe :
                      StrReplaceOnePreProof.endTailGenerated a1 a4 ≠
                        Term.Stuck := by
                    intro h
                    rw [h] at hMiddleLists
                    simp [__eo_is_list] at hMiddleLists
                  have hNilPfxNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                    _ _ hEndTailGeneratedNe
                  have hEndTailEq :
                      StrReplaceOnePreProof.endTailGenerated a1 a4 =
                        StrReplaceOnePreProof.endTail a1 a4 :=
                    eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hEndTailGeneratedNe
                  have hMiddleJoinedEq :
                      StrReplaceOnePreProof.middleJoinedGenerated a5 a1 a4 =
                        StrReplaceOnePreProof.middleJoined a5 a1 a4 := by
                    simp only [StrReplaceOnePreProof.middleJoinedGenerated,
                      StrReplaceOnePreProof.middleJoined]
                    rw [hEndTailEq]
                  have hLeftTailEq :
                      StrReplaceOnePreProof.leftTailGenerated a1 a5 a4 =
                        StrReplaceOnePreProof.leftTail a1 a5 a4 := by
                    unfold StrReplaceOnePreProof.leftTailGenerated
                      StrReplaceOnePreProof.leftTail
                      StrReplaceOnePreProof.concat
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hLeftTailGeneratedNe]
                    rw [hMiddleJoinedEq]
                  have hLeftSourceEq :
                      StrReplaceOnePreProof.leftSourceGenerated a1 a4 a5 =
                        StrReplaceOnePreProof.leftSource a1 a4 a5 := by
                    simp only [StrReplaceOnePreProof.leftSourceGenerated,
                      StrReplaceOnePreProof.leftSource]
                    rw [hLeftTailEq]
                  have hLhsEq :
                      StrReplaceOnePreProof.lhsGenerated a1 a2 a3 a4 a5 =
                        StrReplaceOnePreProof.lhs a1 a2 a3 a4 a5 := by
                    unfold StrReplaceOnePreProof.lhsGenerated
                      StrReplaceOnePreProof.lhs StrReplaceOnePreProof.replace
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hLhsGeneratedNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLeft2Ne]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLeft1Ne]
                    rw [hLeftSourceEq]
                  have hRhsFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                    _ _ hRhsGeneratedNe
                  have hRhsTailGeneratedNe :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck
                      _ _ hRhsGeneratedNe
                  have hCoreReplaceGeneratedNe :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhsFunNe
                  have hCoreReplace2Ne :=
                    eo_mk_apply_fun_ne_stuck_of_ne_stuck
                      _ _ hCoreReplaceGeneratedNe
                  have hCoreReplace1Ne :=
                    eo_mk_apply_fun_ne_stuck_of_ne_stuck
                      _ _ hCoreReplace2Ne
                  have hCoreSourceGeneratedNe :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck
                      _ _ hCoreReplace1Ne
                  have hCoreSourceEq :
                      StrReplaceOnePreProof.coreSourceGenerated a1 a4 a5 =
                        StrReplaceOnePreProof.coreSource a1 a4 a5 := by
                    rfl
                  have hCoreReplaceEq :
                      StrReplaceOnePreProof.coreReplaceGenerated
                          a1 a2 a3 a4 a5 =
                        StrReplaceOnePreProof.coreReplace
                          a1 a2 a3 a4 a5 := by
                    unfold StrReplaceOnePreProof.coreReplaceGenerated
                      StrReplaceOnePreProof.coreReplace
                      StrReplaceOnePreProof.replace
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hCoreReplaceGeneratedNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hCoreReplace2Ne]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hCoreReplace1Ne]
                  have hNilCoreGeneratedNe :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck
                      _ _ hRhsTailGeneratedNe
                  have hRhsTailEq :
                      StrReplaceOnePreProof.rhsTailGenerated
                          a1 a2 a3 a4 a5 =
                        StrReplaceOnePreProof.rhsTail
                          a1 a2 a3 a4 a5 := by
                    unfold StrReplaceOnePreProof.rhsTailGenerated
                      StrReplaceOnePreProof.rhsTail
                      StrReplaceOnePreProof.concat StrReplaceOnePreProof.nilFor
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hRhsTailGeneratedNe]
                    rw [hCoreReplaceEq]
                  have hRhsEq :
                      StrReplaceOnePreProof.rhsGenerated
                          a1 a2 a3 a4 a5 =
                        StrReplaceOnePreProof.rhs a1 a2 a3 a4 a5 := by
                    unfold StrReplaceOnePreProof.rhsGenerated
                      StrReplaceOnePreProof.rhs StrReplaceOnePreProof.concat
                    rw [eo_mk_apply_eq_apply_of_ne_stuck
                      _ _ hRhsGeneratedNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsFunNe]
                    rw [hCoreReplaceEq, hRhsTailEq]
                  have hBodyConcl :
                      StrReplaceOnePreProof.bodyGenerated
                          a1 a2 a3 a4 a5 =
                        StrReplaceOnePreProof.concl a1 a2 a3 a4 a5 := by
                    unfold StrReplaceOnePreProof.bodyGenerated
                      StrReplaceOnePreProof.concl
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hBodyNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                    rw [hLhsEq, hRhsEq]
                  have hProgApply :
                      __eo_prog_str_replace_one_pre a1 a2 a3 a4 a5
                          (Proof.pf P) =
                        StrReplaceOnePreProof.concl a1 a2 a3 a4 a5 :=
                    hBodyEq.trans hBodyConcl
                  have hConclEoTy :
                      __eo_typeof
                          (StrReplaceOnePreProof.concl
                            a1 a2 a3 a4 a5) = Term.Bool := by
                    rwa [← hProgApply]
                  have hEqOperands :
                      __eo_typeof
                          (StrReplaceOnePreProof.lhs a1 a2 a3 a4 a5) =
                        __eo_typeof
                          (StrReplaceOnePreProof.rhs a1 a2 a3 a4 a5) := by
                    change __eo_typeof_eq
                        (__eo_typeof
                          (StrReplaceOnePreProof.lhs a1 a2 a3 a4 a5))
                        (__eo_typeof
                          (StrReplaceOnePreProof.rhs a1 a2 a3 a4 a5)) =
                      Term.Bool at hConclEoTy
                    exact support_eo_typeof_eq_bool_operands_eq _ _
                      hConclEoTy
                  have hLhsTyNe :
                      __eo_typeof
                          (StrReplaceOnePreProof.lhs a1 a2 a3 a4 a5) ≠
                        Term.Stuck := by
                    change __eo_typeof_eq
                        (__eo_typeof
                          (StrReplaceOnePreProof.lhs a1 a2 a3 a4 a5))
                        (__eo_typeof
                          (StrReplaceOnePreProof.rhs a1 a2 a3 a4 a5)) =
                      Term.Bool at hConclEoTy
                    exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      _ _ hConclEoTy).1
                  change __eo_typeof_str_replace
                      (__eo_typeof
                        (StrReplaceOnePreProof.leftSource a1 a4 a5))
                      (__eo_typeof a2) (__eo_typeof a3) ≠ Term.Stuck
                    at hLhsTyNe
                  rcases StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                      _ _ _ hLhsTyNe with
                    ⟨U, hSourceEoTy, hA2EoTy, hA3EoTy⟩
                  have hLhsEoTy :
                      __eo_typeof
                          (StrReplaceOnePreProof.lhs a1 a2 a3 a4 a5) =
                        Term.Apply Term.Seq U := by
                    change __eo_typeof_str_replace
                        (__eo_typeof
                          (StrReplaceOnePreProof.leftSource a1 a4 a5))
                        (__eo_typeof a2) (__eo_typeof a3) =
                      Term.Apply Term.Seq U
                    rw [hSourceEoTy, hA2EoTy, hA3EoTy]
                    exact StrEqReplSupport.eo_typeof_str_replace_result_of_seq_args
                      U (by simpa [hSourceEoTy, hA2EoTy, hA3EoTy]
                        using hLhsTyNe)
                  have hRhsEoTy :
                      __eo_typeof
                          (StrReplaceOnePreProof.rhs a1 a2 a3 a4 a5) =
                        Term.Apply Term.Seq U := by
                    rw [← hEqOperands]
                    exact hLhsEoTy
                  have hLeftTailList :
                      __eo_is_list (Term.UOp UserOp.str_concat)
                          (StrReplaceOnePreProof.leftTail a1 a5 a4) =
                        Term.Boolean true := by
                    rw [← hLeftTailEq]
                    exact hOuterLists.2
                  have hEndList :
                      __eo_is_list (Term.UOp UserOp.str_concat)
                          (StrReplaceOnePreProof.endTail a1 a4) =
                        Term.Boolean true := by
                    rw [← hEndTailEq]
                    exact hMiddleLists.2
                  have hSourceRecEoTy :
                      __eo_typeof
                          (__eo_list_concat_rec a4
                            (StrReplaceOnePreProof.leftTail a1 a5 a4)) =
                        Term.Apply Term.Seq U := by
                    rw [← StringRewriteSupport.list_concat_reduce a4
                      (StrReplaceOnePreProof.leftTail a1 a5 a4)
                      hOuterLists.1 hLeftTailList]
                    exact hSourceEoTy
                  have hLeftTailEoTy :=
                    StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                      a4 (StrReplaceOnePreProof.leftTail a1 a5 a4) U
                      hOuterLists.1 hSourceRecEoTy
                  have hLeftTailArgs :=
                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                      a1 (StrReplaceOnePreProof.middleJoined a5 a1 a4)
                      U hLeftTailEoTy
                  have hMiddleJoinedEoTy := hLeftTailArgs.2
                  have hMiddleRecEoTy :
                      __eo_typeof
                          (__eo_list_concat_rec a5
                            (StrReplaceOnePreProof.endTail a1 a4)) =
                        Term.Apply Term.Seq U := by
                    rw [← StringRewriteSupport.list_concat_reduce a5
                      (StrReplaceOnePreProof.endTail a1 a4)
                      hMiddleLists.1 hEndList]
                    exact hMiddleJoinedEoTy
                  have hEndEoTy :=
                    StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                      a5 (StrReplaceOnePreProof.endTail a1 a4) U
                      hMiddleLists.1 hMiddleRecEoTy
                  have hEndArgs :=
                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                      a1 (StrReplaceOnePreProof.nilFor a4) U hEndEoTy
                  have hA4EoTy :=
                    StringRewriteSupport.source_typeof_eq_seq_of_str_concat_nil_typeof_eq_seq
                      a4 U hEndArgs.2
                  have hRhsArgs :=
                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                      (StrReplaceOnePreProof.coreReplace a1 a2 a3 a4 a5)
                      (StrReplaceOnePreProof.rhsTail a1 a2 a3 a4 a5)
                      U hRhsEoTy
                  have hCoreReplaceTyNe :
                      __eo_typeof
                          (StrReplaceOnePreProof.coreReplace
                            a1 a2 a3 a4 a5) ≠ Term.Stuck := by
                    rw [hRhsArgs.1]
                    intro h
                    cases h
                  change __eo_typeof_str_replace
                      (__eo_typeof
                        (StrReplaceOnePreProof.coreSource a1 a4 a5))
                      (__eo_typeof a2) (__eo_typeof a3) ≠ Term.Stuck
                    at hCoreReplaceTyNe
                  rcases StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                      _ _ _ hCoreReplaceTyNe with
                    ⟨V, hCoreSourceV, hA2V, _hA3V⟩
                  have hVU : V = U := by
                    rw [hA2EoTy] at hA2V
                    exact ((Term.Apply.inj hA2V).2).symm
                  have hCoreSourceEoTy :
                      __eo_typeof
                          (StrReplaceOnePreProof.coreSource a1 a4 a5) =
                        Term.Apply Term.Seq U := by
                    simpa [hVU] using hCoreSourceV
                  have hBundle := StrReplaceOnePreProof.type_and_facts M hM
                    a1 a2 a3 a4 a5 U hOuterLists.1 hMiddleLists.1
                    hA1Trans hA2Trans hA3Trans hA4Trans hA5Trans
                    hLeftTailArgs.1 hA2EoTy hA3EoTy hA4EoTy
                    hSourceEoTy hMiddleRecEoTy hCoreSourceEoTy
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hPremRaw : eo_interprets M P true :=
                      hTrue P (by simp [P, premiseTermList])
                    have hPrem :
                        eo_interprets M
                          (StrReplaceOnePreProof.lenPremise a2) true := by
                      simpa [hPremShape] using hPremRaw
                    rcases hBundle.2 with
                      ⟨spat, hPatEval, hSemantic⟩
                    have hPatLen : (native_unpack_seq spat).length = 1 := by
                      rw [RuleProofs.eo_interprets_iff_smt_interprets]
                        at hPrem
                      cases hPrem with
                      | intro_true _ hEval =>
                          change __smtx_model_eval M
                              (SmtTerm.eq
                                (SmtTerm.str_len (__eo_to_smt a2))
                                (SmtTerm.Numeral 1)) =
                            SmtValue.Boolean true at hEval
                          rw [smtx_eval_eq_term_eq,
                            smtx_eval_str_len_term_eq, hPatEval,
                            StrEqReplSupport.smtx_eval_numeral_term_eq]
                            at hEval
                          have hLenInt :
                              native_seq_len (native_unpack_seq spat) = 1 := by
                            simpa [__smtx_model_eval_str_len,
                              __smtx_model_eval_eq, native_veq] using hEval
                          have hLenCast :
                              ((native_unpack_seq spat).length : Int) = 1 := by
                            simpa [native_seq_len] using hLenInt
                          exact Int.ofNat_inj.mp hLenCast
                    change eo_interprets M
                      (__eo_prog_str_replace_one_pre a1 a2 a3 a4 a5
                        (Proof.pf P)) true
                    rw [hProgApply]
                    exact hSemantic hPatLen
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_str_replace_one_pre a1 a2 a3 a4 a5
                        (Proof.pf P))
                    rw [hProgApply]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      hBundle.1
