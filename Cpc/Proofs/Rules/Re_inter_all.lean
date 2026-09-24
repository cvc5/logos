module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInterAllProof

private abbrev sigma : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar)

private abbrev mkReInter (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) s

private abbrev tail (ys : Term) : Term :=
  mkReInter sigma ys

private abbrev joined (xs ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_inter) xs ys

private abbrev lhs (xs ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_inter) xs (tail ys)

private abbrev rhs (xs ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_inter) (joined xs ys)

private abbrev concl (xs ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs ys)) (rhs xs ys)

private abbrev mkConcl (xs ys : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs xs ys)) (rhs xs ys)

private theorem prog_mk_form (xs ys : Term)
    (hxs : xs ≠ Term.Stuck) (hys : ys ≠ Term.Stuck) :
    __eo_prog_re_inter_all xs ys = mkConcl xs ys := by
  change __eo_prog_re_inter_all xs ys =
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__eo_list_concat (Term.UOp UserOp.re_inter) xs
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.UOp UserOp.re_mult)
                (Term.UOp UserOp.re_allchar)))
            ys)))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_inter)
        (__eo_list_concat (Term.UOp UserOp.re_inter) xs ys))
  exact __eo_prog_re_inter_all.eq_3 xs ys hxs hys

private theorem list_concat_lists_of_ne_stuck (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have ha : __eo_is_list f a = Term.Boolean true :=
    RuleProofs.eo_requires_eq_of_ne_stuck
      (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) hReq
  have hReqEq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) =
        __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) :=
    RuleProofs.eo_requires_result_eq_of_ne_stuck
      (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) hReq
  have hReqTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck := by
    rwa [hReqEq] at hReq
  have hb : __eo_is_list f b = Term.Boolean true :=
    RuleProofs.eo_requires_eq_of_ne_stuck
      (__eo_is_list f b) (Term.Boolean true)
      (__eo_list_concat_rec a b) hReqTail
  exact ⟨ha, hb⟩

private theorem reInter_list_smt_typeof_reglan_of_non_none (t : Term) :
    __eo_is_list (Term.UOp UserOp.re_inter) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro hList hNN
  cases t <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList ⊢
  next op =>
    cases op <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, __smtx_typeof] at hList ⊢
  next f y =>
    cases f <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList ⊢
    next g x =>
      rw [← hList.1] at hNN ⊢
      have hArgs :
          __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
            __smtx_typeof (__eo_to_smt y) = SmtType.RegLan :=
        reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
          (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN
      change __smtx_typeof
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan
      rw [typeof_re_inter_eq]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]

private theorem smtx_typeof_sigma :
    __smtx_typeof (__eo_to_smt sigma) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult SmtTerm.re_allchar) =
    SmtType.RegLan
  rw [typeof_re_mult_eq, __smtx_typeof.eq_104]
  native_decide

private theorem smtx_model_eval_sigma (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt sigma) =
      SmtValue.RegLan native_re_all := by
  change __smtx_model_eval M (SmtTerm.re_mult SmtTerm.re_allchar) =
    SmtValue.RegLan native_re_all
  simp [__smtx_model_eval, RuleProofs.smtx_model_eval_re_mult_allchar]

private theorem smtx_typeof_re_inter_of_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkReInter x y)) = SmtType.RegLan := by
  intro hx hy
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hx, hy, native_ite, native_Teq]

private theorem smt_value_rel_inter_all
    (rxs rys : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter rxs (native_re_inter native_re_all rys)))
      (SmtValue.RegLan (native_re_inter rxs rys)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  simp only [← RuleProofs.native_str_in_re_eq_model]
  rw [RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_all str hValid]
  simp

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (xs ys : Term)
    (hXsList :
      __eo_is_list (Term.UOp UserOp.re_inter) xs = Term.Boolean true)
    (hYsList :
      __eo_is_list (Term.UOp UserOp.re_inter) ys = Term.Boolean true)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hYsTrans : RuleProofs.eo_has_smt_translation ys) :
    RuleProofs.eo_has_bool_type (concl xs ys) ∧
      eo_interprets M (concl xs ys) true := by
  have hXsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.RegLan :=
    reInter_list_smt_typeof_reglan_of_non_none xs hXsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hXsTrans)
  have hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan :=
    reInter_list_smt_typeof_reglan_of_non_none ys hYsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hYsTrans)
  have hTailList :
      __eo_is_list (Term.UOp UserOp.re_inter) (tail ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_inter) sigma ys (by simp) hYsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt (tail ys)) = SmtType.RegLan :=
    smtx_typeof_re_inter_of_args sigma ys smtx_typeof_sigma hYsTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rxs, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (tail ys)) =
        SmtValue.RegLan (native_re_inter native_re_all rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt sigma) (__eo_to_smt ys)) =
      SmtValue.RegLan (native_re_inter native_re_all rys)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter,
      smtx_model_eval_sigma M, hYsEval]
  rcases RuleProofs.reInter_list_concat_eval_rel M xs (tail ys)
      rxs (native_re_inter native_re_all rys)
      hXsList hTailList hXsTy hTailTy hXsEval hTailEval with
    ⟨rlhs, hLhsEval, hLhsTy, hLhsRel⟩
  rcases RuleProofs.reInter_list_concat_eval_rel M xs ys rxs rys
      hXsList hYsList hXsTy hYsTy hXsEval hYsEval with
    ⟨rjoined, hJoinedEval, hJoinedTy, hJoinedRel⟩
  have hJoinedList :
      __eo_is_list (Term.UOp UserOp.re_inter) (joined xs ys) =
        Term.Boolean true := by
    have hReduce :
        joined xs ys = __eo_list_concat_rec xs ys := by
      simp [joined, __eo_list_concat, hXsList, hYsList, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
    rw [hReduce]
    exact eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.re_inter) xs ys hXsList hYsList
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs xs ys)) = SmtType.RegLan :=
    RuleProofs.reInter_singleton_elim_has_reglan_type
      (joined xs ys) hJoinedList hJoinedTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM (rhs xs ys) hRhsTy with
    ⟨rrhs, hRhsEval⟩
  have hRhsRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rrhs)
        (SmtValue.RegLan rjoined) := by
    simpa [hRhsEval, hJoinedEval] using
      RuleProofs.reInter_singleton_elim_rel_eval M (joined xs ys)
        hJoinedList ⟨rjoined, hJoinedEval⟩
  have hBool : RuleProofs.eo_has_bool_type (concl xs ys) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys) (rhs xs ys)
      (by rw [hLhsTy, hRhsTy])
      (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs xs ys) (rhs xs ys) hBool <| by
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_trans _ _ _ hLhsRel <|
      RuleProofs.smt_value_rel_trans _ _ _
        (smt_value_rel_inter_all rxs rys) <|
      RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_symm _ _ hJoinedRel)
        (RuleProofs.smt_value_rel_symm _ _ hRhsRel)

end ReInterAllProof

public theorem cmd_step_re_inter_all_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_all args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_inter_all args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_all args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_inter_all args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  have hTrans :
                      cArgListTranslationOk
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil)) :=
                    hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                    hTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                    hTrans.2.1
                  have hProgLocal :
                      __eo_prog_re_inter_all a1 a2 ≠ Term.Stuck := by
                    change __eo_prog_re_inter_all a1 a2 ≠ Term.Stuck at hProg
                    exact hProg
                  have hA1Ne : a1 ≠ Term.Stuck := by
                    intro h
                    subst a1
                    exact hProgLocal (__eo_prog_re_inter_all.eq_1 a2)
                  have hA2Ne : a2 ≠ Term.Stuck := by
                    intro h
                    subst a2
                    exact hProgLocal
                      (__eo_prog_re_inter_all.eq_2 a1 hA1Ne)
                  have hProgMk :
                      __eo_cmd_step_proven s CRule.re_inter_all
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReInterAllProof.mkConcl a1 a2 :=
                    ReInterAllProof.prog_mk_form a1 a2 hA1Ne hA2Ne
                  have hMkNe :
                      ReInterAllProof.mkConcl a1 a2 ≠ Term.Stuck := by
                    simpa [hProgMk] using hProg
                  have hEqFunNe :
                      __eo_mk_apply (Term.UOp UserOp.eq)
                          (ReInterAllProof.lhs a1 a2) ≠ Term.Stuck :=
                    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
                  have hLhsNe : ReInterAllProof.lhs a1 a2 ≠ Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
                  have hLists :=
                    ReInterAllProof.list_concat_lists_of_ne_stuck
                      (Term.UOp UserOp.re_inter) a1
                      (ReInterAllProof.tail a2) hLhsNe
                  have hYsList :
                      __eo_is_list (Term.UOp UserOp.re_inter) a2 =
                        Term.Boolean true :=
                    eo_is_list_tail_true_of_cons_self
                      (Term.UOp UserOp.re_inter) ReInterAllProof.sigma a2
                      hLists.2
                  have hProgApply :
                      __eo_cmd_step_proven s CRule.re_inter_all
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReInterAllProof.concl a1 a2 := by
                    rw [hProgMk]
                    unfold ReInterAllProof.mkConcl ReInterAllProof.concl
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                  have hFacts :=
                    ReInterAllProof.type_and_facts M hM a1 a2
                      hLists.1 hYsList hA1Trans hA2Trans
                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    (by simpa [hProgApply] using hFacts.1)⟩
                  intro _hTrue
                  rw [hProgApply]
                  exact hFacts.2
