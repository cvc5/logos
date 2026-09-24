module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReConcatStarRepeatProof

private abbrev mkReConcat (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r) s

private abbrev star (r : Term) : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) r

private abbrev shortTail (r ys : Term) : Term :=
  mkReConcat (star r) ys

private abbrev longTail (r ys : Term) : Term :=
  mkReConcat (star r) (shortTail r ys)

private abbrev lhs (xs r ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_concat) xs (longTail r ys)

private abbrev joined (xs r ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_concat) xs (shortTail r ys)

private abbrev rhs (xs r ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_concat) (joined xs r ys)

private abbrev concl (xs r ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs r ys)) (rhs xs r ys)

private abbrev mkConcl (xs r ys : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs xs r ys))
    (rhs xs r ys)

private theorem prog_mk_form (xs r ys : Term)
    (hxs : xs ≠ Term.Stuck) (hr : r ≠ Term.Stuck)
    (hys : ys ≠ Term.Stuck) :
    __eo_prog_re_concat_star_repeat xs r ys = mkConcl xs r ys := by
  exact __eo_prog_re_concat_star_repeat.eq_4 xs r ys hxs hr hys

private theorem eo_typeof_re_mult_eq_reglan_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ =>
      simp [__eo_typeof_re_mult] at h

private theorem smtx_typeof_re_mult_of_reglan (r : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (star r)) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan
  rw [typeof_re_mult_eq]
  simp [hr, native_ite, native_Teq]

private theorem smtx_typeof_re_concat_of_reglan (r s : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (mkReConcat r s)) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_re_concat_eq]
  simp [hr, hs, native_ite, native_Teq]

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (xs r ys : Term)
    (hXsList :
      __eo_is_list (Term.UOp UserOp.re_concat) xs = Term.Boolean true)
    (hYsList :
      __eo_is_list (Term.UOp UserOp.re_concat) ys = Term.Boolean true)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hYsTrans : RuleProofs.eo_has_smt_translation ys)
    (hREoTy : __eo_typeof r = Term.RegLan) :
    RuleProofs.eo_has_bool_type (concl xs r ys) ∧
      eo_interprets M (concl xs r ys) true := by
  have hXsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.RegLan :=
    RegexRewriteSupport.reConcat_list_smt_typeof_reglan_of_non_none
      xs hXsList (by
        simpa [RuleProofs.eo_has_smt_translation] using hXsTrans)
  have hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan :=
    RegexRewriteSupport.reConcat_list_smt_typeof_reglan_of_non_none
      ys hYsList (by
        simpa [RuleProofs.eo_has_smt_translation] using hYsTrans)
  have hRTyRaw :=
    TranslationProofs.eo_to_smt_typeof_matches_translation r hRTrans
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    rw [hREoTy, TranslationProofs.eo_to_smt_type_reglan] at hRTyRaw
    exact hRTyRaw
  have hStarTy :
      __smtx_typeof (__eo_to_smt (star r)) = SmtType.RegLan :=
    smtx_typeof_re_mult_of_reglan r hRTy
  have hShortList :
      __eo_is_list (Term.UOp UserOp.re_concat) (shortTail r ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_concat) (star r) ys (by simp) hYsList
  have hLongList :
      __eo_is_list (Term.UOp UserOp.re_concat) (longTail r ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_concat) (star r) (shortTail r ys)
      (by simp) hShortList
  have hShortTy :
      __smtx_typeof (__eo_to_smt (shortTail r ys)) = SmtType.RegLan :=
    smtx_typeof_re_concat_of_reglan (star r) ys hStarTy hYsTy
  have hLongTy :
      __smtx_typeof (__eo_to_smt (longTail r ys)) = SmtType.RegLan :=
    smtx_typeof_re_concat_of_reglan (star r) (shortTail r ys)
      hStarTy hShortTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rxs, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM r hRTy with
    ⟨rr, hREval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  have hStarEval :
      __smtx_model_eval M (__eo_to_smt (star r)) =
        SmtValue.RegLan (native_re_mult rr) := by
    change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_mult, hREval]
  have hShortEval :
      __smtx_model_eval M (__eo_to_smt (shortTail r ys)) =
        SmtValue.RegLan (native_re_concat (native_re_mult rr) rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt (star r)) (__eo_to_smt ys)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      hStarEval, hYsEval]
  have hLongEval :
      __smtx_model_eval M (__eo_to_smt (longTail r ys)) =
        SmtValue.RegLan
          (native_re_concat (native_re_mult rr)
            (native_re_concat (native_re_mult rr) rys)) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt (star r))
          (__eo_to_smt (shortTail r ys))) = _
    simp only [__smtx_model_eval]
    rw [hStarEval, hShortEval]
    simp [__smtx_model_eval_re_concat]
  rcases RuleProofs.reConcat_list_concat_eval_rel M xs (longTail r ys)
      rxs (native_re_concat (native_re_mult rr)
        (native_re_concat (native_re_mult rr) rys))
      hXsList hLongList hXsTy hLongTy hXsEval hLongEval with
    ⟨rlhs, hLhsEval, hLhsTy, hLhsRel⟩
  rcases RuleProofs.reConcat_list_concat_eval_rel M xs (shortTail r ys)
      rxs (native_re_concat (native_re_mult rr) rys)
      hXsList hShortList hXsTy hShortTy hXsEval hShortEval with
    ⟨rjoined, hJoinedEval, hJoinedTy, hJoinedRel⟩
  have hJoinedList :
      __eo_is_list (Term.UOp UserOp.re_concat) (joined xs r ys) =
        Term.Boolean true := by
    have hReduce : joined xs r ys = __eo_list_concat_rec xs (shortTail r ys) := by
      simp [joined, __eo_list_concat, hXsList, hShortList, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
    rw [hReduce]
    exact eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.re_concat) xs (shortTail r ys)
      hXsList hShortList
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs xs r ys)) = SmtType.RegLan :=
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
      (joined xs r ys) hJoinedList hJoinedTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM (rhs xs r ys) hRhsTy with
    ⟨rrhs, hRhsEval⟩
  have hRhsRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rrhs)
        (SmtValue.RegLan rjoined) := by
    simpa [hRhsEval, hJoinedEval] using
      RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_rel_eval
        M (joined xs r ys) hJoinedList ⟨rjoined, hJoinedEval⟩
  have hBool : RuleProofs.eo_has_bool_type (concl xs r ys) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs r ys) (rhs xs r ys)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M
      (lhs xs r ys) (rhs xs r ys) hBool <| by
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_trans _ _ _ hLhsRel <|
      RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_re_concat_star_repeat rxs rr rys) <|
      RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_symm _ _ hJoinedRel)
        (RuleProofs.smt_value_rel_symm _ _ hRhsRel)

end ReConcatStarRepeatProof

public theorem cmd_step_re_concat_star_repeat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_repeat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_concat_star_repeat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_repeat args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_concat_star_repeat args premises ≠
        Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
    cases args with
    | nil => exact absurd rfl hProg
    | cons a2 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a3 args =>
        cases args with
        | cons _ _ => exact absurd rfl hProg
        | nil =>
          cases premises with
          | cons _ _ => exact absurd rfl hProg
          | nil =>
            have hTrans : cArgListTranslationOk
                (CArgList.cons a1
                  (CArgList.cons a2 (CArgList.cons a3 CArgList.nil))) :=
              hCmdTrans
            have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hTrans.1
            have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hTrans.2.1
            have hA3Trans : RuleProofs.eo_has_smt_translation a3 := hTrans.2.2.1
            have hA1Ne := RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
            have hA2Ne := RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
            have hA3Ne := RuleProofs.term_ne_stuck_of_has_smt_translation a3 hA3Trans
            have hProgMk :
                __eo_cmd_step_proven s CRule.re_concat_star_repeat
                    (CArgList.cons a1
                      (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                    CIndexList.nil =
                  ReConcatStarRepeatProof.mkConcl a1 a2 a3 :=
              ReConcatStarRepeatProof.prog_mk_form
                a1 a2 a3 hA1Ne hA2Ne hA3Ne
            have hMkNe : ReConcatStarRepeatProof.mkConcl a1 a2 a3 ≠
                Term.Stuck := by simpa [hProgMk] using hProg
            have hEqFunNe :
                __eo_mk_apply (Term.UOp UserOp.eq)
                    (ReConcatStarRepeatProof.lhs a1 a2 a3) ≠ Term.Stuck :=
              eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
            have hLhsNe : ReConcatStarRepeatProof.lhs a1 a2 a3 ≠
                Term.Stuck :=
              eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
            have hLists := RegexRewriteSupport.list_concat_lists_of_ne_stuck
              (Term.UOp UserOp.re_concat) a1
              (ReConcatStarRepeatProof.longTail a2 a3) hLhsNe
            have hShortList :
                __eo_is_list (Term.UOp UserOp.re_concat)
                    (ReConcatStarRepeatProof.shortTail a2 a3) =
                  Term.Boolean true :=
              eo_is_list_tail_true_of_cons_self
                (Term.UOp UserOp.re_concat)
                (ReConcatStarRepeatProof.star a2)
                (ReConcatStarRepeatProof.shortTail a2 a3) hLists.2
            have hYsList :
                __eo_is_list (Term.UOp UserOp.re_concat) a3 =
                  Term.Boolean true :=
              eo_is_list_tail_true_of_cons_self
                (Term.UOp UserOp.re_concat)
                (ReConcatStarRepeatProof.star a2) a3 hShortList
            have hProgApply :
                __eo_cmd_step_proven s CRule.re_concat_star_repeat
                    (CArgList.cons a1
                      (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                    CIndexList.nil =
                  ReConcatStarRepeatProof.concl a1 a2 a3 := by
              rw [hProgMk]
              unfold ReConcatStarRepeatProof.mkConcl ReConcatStarRepeatProof.concl
              rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
              rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
            have hConclTy :
                __eo_typeof (ReConcatStarRepeatProof.concl a1 a2 a3) =
                  Term.Bool := by rwa [← hProgApply]
            have hLhsTyNe :
                __eo_typeof (ReConcatStarRepeatProof.lhs a1 a2 a3) ≠
                  Term.Stuck := by
              change __eo_typeof_eq
                  (__eo_typeof (ReConcatStarRepeatProof.lhs a1 a2 a3))
                  (__eo_typeof (ReConcatStarRepeatProof.rhs a1 a2 a3)) =
                Term.Bool at hConclTy
              exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
                hConclTy).1
            have hLhsTyNe' := hLhsTyNe
            change __eo_typeof
                (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                  (ReConcatStarRepeatProof.longTail a2 a3)) ≠
              Term.Stuck at hLhsTyNe'
            rw [RuleProofs.list_concat_reduce
              (Term.UOp UserOp.re_concat) a1
              (ReConcatStarRepeatProof.longTail a2 a3)
              hLists.1 hLists.2] at hLhsTyNe'
            have hLongTyNe := RuleProofs.list_concat_rec_tail_typeof_ne_stuck
              a1 (ReConcatStarRepeatProof.longTail a2 a3)
              hLists.1 hLhsTyNe'
            have hLongInv := RuleProofs.eo_typeof_re_concat_term_args
              (ReConcatStarRepeatProof.star a2)
              (ReConcatStarRepeatProof.shortTail a2 a3) hLongTyNe
            have hStarTyNe :
                __eo_typeof (ReConcatStarRepeatProof.star a2) ≠
                  Term.Stuck := by rw [hLongInv.1]; decide
            change __eo_typeof_re_mult (__eo_typeof a2) ≠ Term.Stuck
              at hStarTyNe
            have hA2EoTy :=
              ReConcatStarRepeatProof.eo_typeof_re_mult_eq_reglan_of_ne_stuck
                (__eo_typeof a2) hStarTyNe
            have hFacts := ReConcatStarRepeatProof.type_and_facts
              M hM a1 a2 a3 hLists.1 hYsList
              hA1Trans hA2Trans hA3Trans hA2EoTy
            refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
              (by simpa [hProgApply] using hFacts.1)⟩
            intro _hTrue
            rw [hProgApply]
            exact hFacts.2
