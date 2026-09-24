module

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrIndexofContainsConcatPreProof

private abbrev op : Term := Term.UOp UserOp.str_concat

private abbrev concat (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private abbrev leftTail (t2 s1 t3 : Term) : Term :=
  concat t2 (concat s1 t3)

private abbrev leftSource (t1 t2 t3 s1 : Term) : Term :=
  __eo_list_concat op t1 (leftTail t2 s1 t3)

private abbrev nilFor (t1 : Term) : Term :=
  __eo_nil op (__eo_typeof t1)

private abbrev rightTailGenerated (t1 t2 : Term) : Term :=
  __eo_mk_apply (Term.Apply op t2) (nilFor t1)

private abbrev rightTail (t1 t2 : Term) : Term :=
  concat t2 (nilFor t1)

private abbrev rightJoinedGenerated (t1 t2 : Term) : Term :=
  __eo_list_concat op t1 (rightTailGenerated t1 t2)

private abbrev rightJoined (t1 t2 : Term) : Term :=
  __eo_list_concat op t1 (rightTail t1 t2)

private abbrev rightSourceGenerated (t1 t2 : Term) : Term :=
  __eo_list_singleton_elim op (rightJoinedGenerated t1 t2)

private abbrev rightSource (t1 t2 : Term) : Term :=
  __eo_list_singleton_elim op (rightJoined t1 t2)

private abbrev idx (source pat : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply Term.str_indexof source) pat)
    (Term.Numeral 0)

private abbrev lhs (t1 t2 t3 s1 : Term) : Term :=
  idx (leftSource t1 t2 t3 s1) t2

private abbrev lhsGenerated (t1 t2 t3 s1 : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_indexof)
        (leftSource t1 t2 t3 s1)) t2)
    (Term.Numeral 0)

private abbrev rhsGenerated (t1 t2 : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_indexof)
        (rightSourceGenerated t1 t2)) t2)
    (Term.Numeral 0)

private abbrev rhs (t1 t2 : Term) : Term :=
  idx (rightSource t1 t2) t2

private abbrev mkConcl (t1 t2 t3 s1 : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (lhsGenerated t1 t2 t3 s1))
    (rhsGenerated t1 t2)

private abbrev concl (t1 t2 t3 s1 : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lhs t1 t2 t3 s1)) (rhs t1 t2)

private theorem prog_mk_form (t1 t2 t3 s1 : Term)
    (h1 : t1 ≠ Term.Stuck) (h2 : t2 ≠ Term.Stuck)
    (h3 : t3 ≠ Term.Stuck) (hs : s1 ≠ Term.Stuck) :
    __eo_prog_str_indexof_contains_concat_pre t1 t2 t3 s1 =
      mkConcl t1 t2 t3 s1 := by
  exact __eo_prog_str_indexof_contains_concat_pre.eq_5
    t1 t2 t3 s1 h1 h2 h3 hs

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

private theorem right_source_eq_pattern_of_not_cons
    (t1 t2 : Term)
    (hT1List : __eo_is_list op t1 = Term.Boolean true)
    (hNotCons :
      ¬ ∃ head tail,
        t1 = Term.Apply (Term.Apply op head) tail)
    (hNilNe : nilFor t1 ≠ Term.Stuck) :
    rightSource t1 t2 = t2 := by
  have hT1Nil : __eo_is_list_nil op t1 = Term.Boolean true :=
    StringRewriteSupport.list_nil_of_list_not_cons t1 hT1List hNotCons
  rcases StringRewriteSupport.typeof_seq_of_str_concat_nil_ne_stuck
      (__eo_typeof t1) hNilNe with ⟨U, hT1EoTy⟩
  have hNilNil : __eo_is_list_nil op (nilFor t1) =
      Term.Boolean true := by
    change __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof t1)) =
        Term.Boolean true
    rw [hT1EoTy]
    cases U <;>
      simp [nilFor, __eo_nil, __eo_nil_str_concat, __seq_empty,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
        native_teq] at hNilNe ⊢
    case UOp uop => cases uop <;> simp at hNilNe ⊢
  have hNilList : __eo_is_list op (nilFor t1) = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true (nilFor t1) hNilNil
  have hRightTailList : __eo_is_list op (rightTail t1 t2) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op t2 (nilFor t1)
      (by simp) hNilList
  have hJoinedList : __eo_is_list op (rightJoined t1 t2) =
      Term.Boolean true :=
    StringRewriteSupport.list_concat_is_list t1 (rightTail t1 t2)
      hT1List hRightTailList
  have hRecT1 : __eo_list_concat_rec t1 (rightTail t1 t2) =
      rightTail t1 t2 :=
    eo_list_concat_rec_str_concat_nil_eq_of_nil_true t1
      (rightTail t1 t2) hT1Nil
  unfold rightSource rightJoined
  rw [StringRewriteSupport.list_concat_reduce t1 (rightTail t1 t2)
    hT1List hRightTailList, hRecT1]
  simp [__eo_list_singleton_elim, hRightTailList,
    __eo_list_singleton_elim_2, hNilNil, __eo_ite, native_ite,
    native_teq, __eo_requires, native_not, SmtEval.native_not]

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (t1 t2 t3 s1 U : Term)
    (hT1List : __eo_is_list op t1 = Term.Boolean true)
    (hT3List : __eo_is_list op t3 = Term.Boolean true)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hT2Trans : RuleProofs.eo_has_smt_translation t2)
    (hT3Trans : RuleProofs.eo_has_smt_translation t3)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hSourceEoTy : __eo_typeof (leftSource t1 t2 t3 s1) =
      Term.Apply Term.Seq U)
    (hT2EoTy : __eo_typeof t2 = Term.Apply Term.Seq U)
    (hS1EoTy : __eo_typeof s1 = Term.Apply Term.Seq U)
    (hT3EoTy : __eo_typeof t3 = Term.Apply Term.Seq U)
    (hNilNe : nilFor t1 ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (concl t1 t2 t3 s1) ∧
      eo_interprets M (concl t1 t2 t3 s1) true := by
  let T := __eo_to_smt_type U
  have hT2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T := by
    simpa [T] using
      StrEqReplSupport.smtx_typeof_of_eo_seq t2 U hT2Trans hT2EoTy
  have hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq T := by
    simpa [T] using
      StrEqReplSupport.smtx_typeof_of_eo_seq s1 U hS1Trans hS1EoTy
  have hT3Ty : __smtx_typeof (__eo_to_smt t3) = SmtType.Seq T := by
    simpa [T] using
      StrEqReplSupport.smtx_typeof_of_eo_seq t3 U hT3Trans hT3EoTy
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (concat s1 t3)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq s1 t3 T hS1Ty hT3Ty
  have hTailTy :
      __smtx_typeof (__eo_to_smt (leftTail t2 s1 t3)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t2 (concat s1 t3) T hT2Ty hInnerTy
  have hInnerList : __eo_is_list op (concat s1 t3) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op s1 t3 (by simp) hT3List
  have hTailList : __eo_is_list op (leftTail t2 s1 t3) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op t2 (concat s1 t3)
      (by simp) hInnerList
  have hReduce : leftSource t1 t2 t3 s1 =
      __eo_list_concat_rec t1 (leftTail t2 s1 t3) :=
    StringRewriteSupport.list_concat_reduce t1 (leftTail t2 s1 t3)
      hT1List hTailList
  have hRecEoTy :
      __eo_typeof (__eo_list_concat_rec t1 (leftTail t2 s1 t3)) =
        Term.Apply Term.Seq U := by
    simpa [hReduce] using hSourceEoTy
  have hTailTrans : RuleProofs.eo_has_smt_translation
      (leftTail t2 s1 t3) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailTy]
    exact seq_ne_none T
  have hLeftSourceTy :
      __smtx_typeof (__eo_to_smt (leftSource t1 t2 t3 s1)) =
        SmtType.Seq T := by
    rw [hReduce]
    simpa [T] using
      StrLeqConcatNarySupport.smtx_typeof_list_concat_rec_of_eo_type
        t1 (leftTail t2 s1 t3) U hT1List hT1Trans hTailTrans hRecEoTy
  rcases seq_eval_of_type M hM t2 T hT2Ty with ⟨st2, hT2Eval⟩
  rcases seq_eval_of_type M hM s1 T hS1Ty with ⟨ss1, hS1Eval⟩
  rcases seq_eval_of_type M hM t3 T hT3Ty with ⟨st3, hT3Eval⟩
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt (concat s1 t3)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
            (native_unpack_seq ss1 ++ native_unpack_seq st3)) := by
    rw [smtx_model_eval_str_concat_term_eq, hS1Eval, hT3Eval]
    rfl
  let innerOut := native_pack_seq (__smtx_elem_typeof_seq_value ss1)
    (native_unpack_seq ss1 ++ native_unpack_seq st3)
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (leftTail t2 s1 t3)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value st2)
            (native_unpack_seq st2 ++ native_unpack_seq innerOut)) := by
    rw [smtx_model_eval_str_concat_term_eq, hT2Eval]
    change __smtx_model_eval_str_concat (SmtValue.Seq st2)
        (__smtx_model_eval M (__eo_to_smt (concat s1 t3))) = _
    rw [hInnerEval]
    rfl
  let tailOut := native_pack_seq (__smtx_elem_typeof_seq_value st2)
    (native_unpack_seq st2 ++ native_unpack_seq innerOut)
  rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
      M hM t1 (leftTail t2 s1 t3) tailOut hT1List hTailList
      hT1Trans hTailEval with
    ⟨sleft, hLeftEval, hLeftUnpack⟩
  have hTailUnpack : native_unpack_seq tailOut =
      native_unpack_seq st2 ++
        (native_unpack_seq ss1 ++ native_unpack_seq st3) := by
    simp [tailOut, innerOut, Smtm.native_unpack_pack_seq,
      List.append_assoc]
  have hLeftUnpack' : native_unpack_seq sleft =
      (StringRewriteSupport.listEvalPrefix M t1 ++ native_unpack_seq st2) ++
        (native_unpack_seq ss1 ++ native_unpack_seq st3) := by
    rw [hLeftUnpack, hTailUnpack]
    simp [List.append_assoc]
  have hRightData :
      ∃ sright,
        __smtx_typeof (__eo_to_smt (rightSource t1 t2)) = SmtType.Seq T ∧
        __smtx_model_eval M (__eo_to_smt (rightSource t1 t2)) =
          SmtValue.Seq sright ∧
        native_unpack_seq sright =
          StringRewriteSupport.listEvalPrefix M t1 ++ native_unpack_seq st2 := by
    by_cases hCons :
        ∃ head tail,
          t1 = Term.Apply (Term.Apply op head) tail
    · rcases hCons with ⟨head, rest, rfl⟩
      have hRestList : __eo_is_list op rest = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self op head rest hT1List
      have hRecNe := eo_list_concat_rec_ne_stuck_of_list op rest
        (leftTail t2 s1 t3) hRestList (by simp)
      have hRecEq :
          __eo_list_concat_rec (concat head rest) (leftTail t2 s1 t3) =
            concat head
              (__eo_list_concat_rec rest (leftTail t2 s1 t3)) :=
        eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          head rest (leftTail t2 s1 t3) hRecNe
      have hHeadEoTy : __eo_typeof head = Term.Apply Term.Seq U := by
        rw [hRecEq] at hRecEoTy
        exact (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
          head (__eo_list_concat_rec rest (leftTail t2 s1 t3)) U
          hRecEoTy).1
      have hT1NN : __smtx_typeof
          (__eo_to_smt (concat head rest)) ≠ SmtType.None := hT1Trans
      rcases str_concat_args_of_non_none head rest hT1NN with
        ⟨V, hHeadTyV, hRestTyV⟩
      have hHeadTrans : RuleProofs.eo_has_smt_translation head := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hHeadTyV]
        exact seq_ne_none V
      have hHeadTyT : __smtx_typeof (__eo_to_smt head) =
          SmtType.Seq T := by
        simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
          head U hHeadTrans hHeadEoTy
      have hVT : V = T := by
        have hEq : SmtType.Seq V = SmtType.Seq T := by
          rw [← hHeadTyV, hHeadTyT]
        injection hEq
      have hT1Ty : __smtx_typeof
          (__eo_to_smt (concat head rest)) = SmtType.Seq T :=
        smt_typeof_str_concat_of_seq head rest T hHeadTyT
          (by simpa [hVT] using hRestTyV)
      have hNilTy : __smtx_typeof
          (__eo_to_smt (nilFor (concat head rest))) = SmtType.Seq T :=
        smt_typeof_nil_str_concat_typeof_of_smt_type_seq
          (concat head rest) T hT1Ty
      have hNilEval : __smtx_model_eval M
          (__eo_to_smt (nilFor (concat head rest))) =
          SmtValue.Seq (SmtSeq.empty T) :=
        eval_nil_str_concat_typeof_of_smt_type_seq M
          (concat head rest) T hT1Ty
      have hNilNil : __eo_is_list_nil op (nilFor (concat head rest)) =
          Term.Boolean true := by
        have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
          (concat head rest) (by
            rw [hT1Ty]
            exact seq_ne_none T)
        have hTy : __eo_to_smt_type (__eo_typeof (concat head rest)) =
            SmtType.Seq T := by rw [← hMatch, hT1Ty]
        exact strConcat_nil_is_list_nil_of_type hTy
      have hNilList : __eo_is_list op (nilFor (concat head rest)) =
          Term.Boolean true :=
        eo_is_list_str_concat_nil_true_of_nil_true _ hNilNil
      have hRTList : __eo_is_list op (rightTail (concat head rest) t2) =
          Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list op t2 _ (by simp) hNilList
      have hRTTy : __smtx_typeof
          (__eo_to_smt (rightTail (concat head rest) t2)) =
          SmtType.Seq T :=
        smt_typeof_str_concat_of_seq t2 _ T hT2Ty hNilTy
      have hRTEval : __smtx_model_eval M
          (__eo_to_smt (rightTail (concat head rest) t2)) =
          SmtValue.Seq
            (native_pack_seq (__smtx_elem_typeof_seq_value st2)
              (native_unpack_seq st2)) := by
        rw [smtx_model_eval_str_concat_term_eq, hT2Eval, hNilEval]
        change SmtValue.Seq
            (native_pack_seq (__smtx_elem_typeof_seq_value st2)
              (native_unpack_seq st2 ++ [])) = _
        rw [List.append_nil]
      let rtOut := native_pack_seq (__smtx_elem_typeof_seq_value st2)
        (native_unpack_seq st2)
      rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
          M hM (concat head rest) (rightTail (concat head rest) t2)
          rtOut hT1List hRTList hT1Trans hRTEval with
        ⟨sjoined, hJoinedEval, hJoinedUnpack⟩
      have hJoinedTy : __smtx_typeof
          (__eo_to_smt (rightJoined (concat head rest) t2)) =
          SmtType.Seq T :=
        StringRewriteSupport.list_concat_has_seq_type
          (concat head rest) (rightTail (concat head rest) t2) T
          hT1List hRTList hT1Ty hRTTy
      have hJoinedList : __eo_is_list op
          (rightJoined (concat head rest) t2) = Term.Boolean true :=
        StringRewriteSupport.list_concat_is_list
          (concat head rest) (rightTail (concat head rest) t2)
          hT1List hRTList
      have hRightTy := StringRewriteSupport.singleton_elim_has_seq_type
        (rightJoined (concat head rest) t2) T hJoinedList hJoinedTy
      have hRightEval := StringRewriteSupport.singleton_elim_eval
        M hM (rightJoined (concat head rest) t2) T sjoined
        hJoinedList hJoinedTy hJoinedEval
      refine ⟨sjoined, hRightTy, hRightEval, ?_⟩
      simpa [rtOut, Smtm.native_unpack_pack_seq] using hJoinedUnpack
    · have hRightEq := right_source_eq_pattern_of_not_cons
        t1 t2 hT1List hCons hNilNe
      refine ⟨st2, ?_, ?_, ?_⟩
      · rwa [hRightEq]
      · rwa [hRightEq]
      · rw [StringRewriteSupport.listEvalPrefix_eq_nil_of_not_cons
          M t1 hCons]
        simp
  rcases hRightData with ⟨sright, hRightTy, hRightEval, hRightUnpack⟩
  have hZeroTy : __smtx_typeof (__eo_to_smt (Term.Numeral 0)) =
      SmtType.Int := by rfl
  have hLhsTy := StringRewriteSupport.smt_typeof_str_indexof_of_seq
    (leftSource t1 t2 t3 s1) t2 (Term.Numeral 0) T
    hLeftSourceTy hT2Ty hZeroTy
  have hRhsTy := StringRewriteSupport.smt_typeof_str_indexof_of_seq
    (rightSource t1 t2) t2 (Term.Numeral 0) T
    hRightTy hT2Ty hZeroTy
  have hBool : RuleProofs.eo_has_bool_type (concl t1 t2 t3 s1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs t1 t2 t3 s1) (rhs t1 t2)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M
      (lhs t1 t2 t3 s1) (rhs t1 t2) hBool <| by
    have hIdxEq :
        native_seq_indexof (native_unpack_seq sleft)
            (native_unpack_seq st2) 0 =
          native_seq_indexof (native_unpack_seq sright)
            (native_unpack_seq st2) 0 := by
      rw [hLeftUnpack', hRightUnpack]
      exact StringRewriteSupport.native_seq_indexof_append_after_present
        (StringRewriteSupport.listEvalPrefix M t1)
        (native_unpack_seq st2)
        (native_unpack_seq ss1 ++ native_unpack_seq st3)
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_indexof
          (__eo_to_smt (leftSource t1 t2 t3 s1)) (__eo_to_smt t2)
          (SmtTerm.Numeral 0)))
      (__smtx_model_eval M
        (SmtTerm.str_indexof
          (__eo_to_smt (rightSource t1 t2)) (__eo_to_smt t2)
          (SmtTerm.Numeral 0)))
    rw [StringRewriteSupport.smtx_eval_str_indexof_term_eq,
      StringRewriteSupport.smtx_eval_str_indexof_term_eq,
      hLeftEval, hRightEval, hT2Eval]
    simp [__smtx_model_eval, __smtx_model_eval_str_indexof, hIdxEq]
    exact RuleProofs.smt_value_rel_refl _

end StrIndexofContainsConcatPreProof

public theorem cmd_step_str_indexof_contains_concat_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_contains_concat_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_contains_concat_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_contains_concat_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_indexof_contains_concat_pre
          args premises ≠ Term.Stuck :=
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
                  __eo_cmd_step_proven s
                      CRule.str_indexof_contains_concat_pre
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3
                          (CArgList.cons a4 CArgList.nil))))
                      CIndexList.nil =
                    StrIndexofContainsConcatPreProof.mkConcl
                      a1 a2 a3 a4 :=
                StrIndexofContainsConcatPreProof.prog_mk_form
                  a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne
              have hMkNe :
                  StrIndexofContainsConcatPreProof.mkConcl
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
                  (Term.UOp UserOp.str_concat) a1
                  (StrIndexofContainsConcatPreProof.leftTail a2 a4 a3)
                  hLeftSourceNe
              have hInnerList :
                  __eo_is_list (Term.UOp UserOp.str_concat)
                      (StrIndexofContainsConcatPreProof.concat a4 a3) =
                    Term.Boolean true :=
                eo_is_list_tail_true_of_cons_self
                  (Term.UOp UserOp.str_concat) a2
                  (StrIndexofContainsConcatPreProof.concat a4 a3)
                  hLeftLists.2
              have hA3List :
                  __eo_is_list (Term.UOp UserOp.str_concat) a3 =
                    Term.Boolean true :=
                eo_is_list_tail_true_of_cons_self
                  (Term.UOp UserOp.str_concat) a4 a3 hInnerList
              have hRight2Ne := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                _ _ hRhsGeneratedNe
              have hRight1Ne := eo_mk_apply_fun_ne_stuck_of_ne_stuck
                _ _ hRight2Ne
              have hRightSourceGeneratedNe :=
                eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRight1Ne
              have hRightJoinedGeneratedNe :=
                str_nary_elim_arg_ne_stuck_of_ne_stuck
                  (StrIndexofContainsConcatPreProof.rightJoinedGenerated
                    a1 a2) hRightSourceGeneratedNe
              have hRightLists :=
                RegexRewriteSupport.list_concat_lists_of_ne_stuck
                  (Term.UOp UserOp.str_concat) a1
                  (StrIndexofContainsConcatPreProof.rightTailGenerated a1 a2)
                  hRightJoinedGeneratedNe
              have hRightTailGeneratedNe :
                  StrIndexofContainsConcatPreProof.rightTailGenerated
                      a1 a2 ≠ Term.Stuck := by
                intro h
                rw [h] at hRightLists
                simp [__eo_is_list] at hRightLists
              have hNilNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck
                _ _ hRightTailGeneratedNe
              have hRightTailEq :
                  StrIndexofContainsConcatPreProof.rightTailGenerated
                      a1 a2 =
                    StrIndexofContainsConcatPreProof.rightTail a1 a2 :=
                eo_mk_apply_eq_apply_of_ne_stuck _ _ hRightTailGeneratedNe
              have hRightSourceEq :
                  StrIndexofContainsConcatPreProof.rightSourceGenerated
                      a1 a2 =
                    StrIndexofContainsConcatPreProof.rightSource a1 a2 := by
                simp only [
                  StrIndexofContainsConcatPreProof.rightSourceGenerated,
                  StrIndexofContainsConcatPreProof.rightSource,
                  StrIndexofContainsConcatPreProof.rightJoinedGenerated,
                  StrIndexofContainsConcatPreProof.rightJoined]
                rw [hRightTailEq]
              have hLhsEq :
                  StrIndexofContainsConcatPreProof.lhsGenerated
                      a1 a2 a3 a4 =
                    StrIndexofContainsConcatPreProof.lhs a1 a2 a3 a4 := by
                unfold StrIndexofContainsConcatPreProof.lhsGenerated
                  StrIndexofContainsConcatPreProof.lhs
                  StrIndexofContainsConcatPreProof.idx
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsGeneratedNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLeft2Ne]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLeft1Ne]
              have hRhsEq :
                  StrIndexofContainsConcatPreProof.rhsGenerated a1 a2 =
                    StrIndexofContainsConcatPreProof.rhs a1 a2 := by
                unfold StrIndexofContainsConcatPreProof.rhsGenerated
                  StrIndexofContainsConcatPreProof.rhs
                  StrIndexofContainsConcatPreProof.idx
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsGeneratedNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRight2Ne]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRight1Ne]
                rw [hRightSourceEq]
              have hProgApply :
                  __eo_cmd_step_proven s
                      CRule.str_indexof_contains_concat_pre
                      (CArgList.cons a1 (CArgList.cons a2
                        (CArgList.cons a3
                          (CArgList.cons a4 CArgList.nil))))
                      CIndexList.nil =
                    StrIndexofContainsConcatPreProof.concl
                      a1 a2 a3 a4 := by
                rw [hProgMk]
                unfold StrIndexofContainsConcatPreProof.mkConcl
                  StrIndexofContainsConcatPreProof.concl
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                rw [hLhsEq, hRhsEq]
              have hConclEoTy :
                  __eo_typeof
                      (StrIndexofContainsConcatPreProof.concl
                        a1 a2 a3 a4) = Term.Bool := by
                rwa [← hProgApply]
              have hLeftTyNe :
                  __eo_typeof
                      (StrIndexofContainsConcatPreProof.lhs
                        a1 a2 a3 a4) ≠ Term.Stuck := by
                change __eo_typeof_eq
                    (__eo_typeof
                      (StrIndexofContainsConcatPreProof.lhs
                        a1 a2 a3 a4))
                    (__eo_typeof
                      (StrIndexofContainsConcatPreProof.rhs a1 a2)) =
                  Term.Bool at hConclEoTy
                exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  _ _ hConclEoTy).1
              change __eo_typeof_str_indexof
                  (__eo_typeof
                    (StrIndexofContainsConcatPreProof.leftSource
                      a1 a2 a3 a4))
                  (__eo_typeof a2) (__eo_typeof (Term.Numeral 0)) ≠
                Term.Stuck at hLeftTyNe
              rcases StringRewriteSupport.eo_typeof_str_indexof_args_of_ne_stuck
                  _ _ _ hLeftTyNe with
                ⟨U, hSourceEoTy, hA2EoTy, _hZeroEoTy⟩
              have hTailEoTy :
                  __eo_typeof
                      (StrIndexofContainsConcatPreProof.leftTail
                        a2 a4 a3) = Term.Apply Term.Seq U := by
                have hRecEoTy :
                    __eo_typeof
                        (__eo_list_concat_rec a1
                          (StrIndexofContainsConcatPreProof.leftTail
                            a2 a4 a3)) =
                      Term.Apply Term.Seq U := by
                  rw [← StringRewriteSupport.list_concat_reduce a1
                    (StrIndexofContainsConcatPreProof.leftTail a2 a4 a3)
                    hLeftLists.1 hLeftLists.2]
                  exact hSourceEoTy
                exact
                  StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                    a1
                    (StrIndexofContainsConcatPreProof.leftTail a2 a4 a3)
                    U hLeftLists.1 hRecEoTy
              have hTailArgs :=
                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                  a2 (StrIndexofContainsConcatPreProof.concat a4 a3)
                  U hTailEoTy
              have hInnerArgs :=
                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                  a4 a3 U hTailArgs.2
              have hFacts :=
                StrIndexofContainsConcatPreProof.type_and_facts M hM
                  a1 a2 a3 a4 U hLeftLists.1 hA3List
                  hA1Trans hA2Trans hA3Trans hA4Trans
                  hSourceEoTy hA2EoTy hInnerArgs.1 hInnerArgs.2 hNilNe
              refine ⟨?_, ?_⟩
              · intro _hTrue
                rw [hProgApply]
                exact hFacts.2
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by simpa [hProgApply] using hFacts.1)
