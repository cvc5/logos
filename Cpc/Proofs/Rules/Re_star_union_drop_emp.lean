module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReStarUnionDropEmpProof

private abbrev epsilon : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])

private abbrev mkReUnion (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) s

private abbrev tail (ys : Term) : Term :=
  mkReUnion epsilon ys

private abbrev body (xs ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_union) xs (tail ys)

private abbrev joined (xs ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_union) xs ys

private abbrev reduced (xs ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_union) (joined xs ys)

private abbrev lhs (xs ys : Term) : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (body xs ys)

private abbrev rhs (xs ys : Term) : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (reduced xs ys)

private abbrev concl (xs ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs ys)) (rhs xs ys)

private abbrev mkConcl (xs ys : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.UOp UserOp.re_mult) (body xs ys)))
    (__eo_mk_apply (Term.UOp UserOp.re_mult) (reduced xs ys))

private theorem prog_mk_form (xs ys : Term)
    (hxs : xs ≠ Term.Stuck) (hys : ys ≠ Term.Stuck) :
    __eo_prog_re_star_union_drop_emp xs ys = mkConcl xs ys := by
  exact __eo_prog_re_star_union_drop_emp.eq_3 xs ys hxs hys

private theorem smtx_typeof_epsilon :
    __smtx_typeof (__eo_to_smt epsilon) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  native_decide

private theorem smtx_model_eval_epsilon (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt epsilon) =
      SmtValue.RegLan (native_str_to_re []) := by
  change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String [])) = _
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
    native_pack_string, native_unpack_string, native_pack_seq,
    native_unpack_seq]

private theorem smtx_typeof_re_union_of_args (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (mkReUnion x y)) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_union_eq]
  simp [hx, hy, native_ite, native_Teq]

private theorem smtx_typeof_re_mult_of_reglan (r : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r)) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) =
    SmtType.RegLan
  rw [typeof_re_mult_eq]
  simp [hr, native_ite, native_Teq]

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (xs ys : Term)
    (hXsList :
      __eo_is_list (Term.UOp UserOp.re_union) xs = Term.Boolean true)
    (hYsList :
      __eo_is_list (Term.UOp UserOp.re_union) ys = Term.Boolean true)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hYsTrans : RuleProofs.eo_has_smt_translation ys) :
    RuleProofs.eo_has_bool_type (concl xs ys) ∧
      eo_interprets M (concl xs ys) true := by
  have hXsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.RegLan :=
    RegexRewriteSupport.reUnion_list_smt_typeof_reglan_of_non_none xs
      hXsList (by
        simpa [RuleProofs.eo_has_smt_translation] using hXsTrans)
  have hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan :=
    RegexRewriteSupport.reUnion_list_smt_typeof_reglan_of_non_none ys
      hYsList (by
        simpa [RuleProofs.eo_has_smt_translation] using hYsTrans)
  have hTailList :
      __eo_is_list (Term.UOp UserOp.re_union) (tail ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_union) epsilon ys (by simp) hYsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt (tail ys)) = SmtType.RegLan :=
    smtx_typeof_re_union_of_args epsilon ys smtx_typeof_epsilon hYsTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rxs, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (tail ys)) =
        SmtValue.RegLan
          (native_re_union (native_str_to_re []) rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt epsilon) (__eo_to_smt ys)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_union,
      smtx_model_eval_epsilon M, hYsEval]
  rcases RuleProofs.reUnion_list_concat_eval_rel M xs (tail ys)
      rxs (native_re_union (native_str_to_re []) rys)
      hXsList hTailList hXsTy hTailTy hXsEval hTailEval with
    ⟨rbody, hBodyEval, hBodyTy, hBodyRel⟩
  rcases RuleProofs.reUnion_list_concat_eval_rel M xs ys rxs rys
      hXsList hYsList hXsTy hYsTy hXsEval hYsEval with
    ⟨rjoined, hJoinedEval, hJoinedTy, hJoinedRel⟩
  have hJoinedList :
      __eo_is_list (Term.UOp UserOp.re_union) (joined xs ys) =
        Term.Boolean true := by
    have hReduce : joined xs ys = __eo_list_concat_rec xs ys := by
      simp [joined, __eo_list_concat, hXsList, hYsList, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
    rw [hReduce]
    exact eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.re_union) xs ys hXsList hYsList
  have hReducedTy :
      __smtx_typeof (__eo_to_smt (reduced xs ys)) = SmtType.RegLan :=
    RuleProofs.reUnion_singleton_elim_has_reglan_type
      (joined xs ys) hJoinedList hJoinedTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM
      (reduced xs ys) hReducedTy with
    ⟨rreduced, hReducedEval⟩
  have hReducedRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rreduced)
        (SmtValue.RegLan rjoined) := by
    simpa [hReducedEval, hJoinedEval] using
      RuleProofs.reUnion_singleton_elim_rel_eval M (joined xs ys)
        hJoinedList ⟨rjoined, hJoinedEval⟩
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs xs ys)) = SmtType.RegLan :=
    smtx_typeof_re_mult_of_reglan (body xs ys) hBodyTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs xs ys)) = SmtType.RegLan :=
    smtx_typeof_re_mult_of_reglan (reduced xs ys) hReducedTy
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs xs ys)) =
        SmtValue.RegLan (native_re_mult rbody) := by
    change __smtx_model_eval M
        (SmtTerm.re_mult (__eo_to_smt (body xs ys))) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_mult, hBodyEval]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhs xs ys)) =
        SmtValue.RegLan (native_re_mult rreduced) := by
    change __smtx_model_eval M
        (SmtTerm.re_mult (__eo_to_smt (reduced xs ys))) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_mult, hReducedEval]
  have hBool : RuleProofs.eo_has_bool_type (concl xs ys) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys) (rhs xs ys)
      (by rw [hLhsTy, hRhsTy])
      (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs xs ys) (rhs xs ys) hBool <| by
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_trans _ _ _
      (RuleProofs.smt_value_rel_re_mult_congr hBodyRel) <|
      RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_re_star_union_drop_epsilon rxs rys) <|
      RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_re_mult_congr
          (RuleProofs.smt_value_rel_symm _ _ hJoinedRel))
        (RuleProofs.smt_value_rel_re_mult_congr
          (RuleProofs.smt_value_rel_symm _ _ hReducedRel))

end ReStarUnionDropEmpProof

public theorem cmd_step_re_star_union_drop_emp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_union_drop_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_star_union_drop_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_union_drop_emp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_star_union_drop_emp args premises ≠
        Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | cons _ _ => exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ => exact False.elim (hProg rfl)
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
                      __eo_prog_re_star_union_drop_emp a1 a2 ≠ Term.Stuck :=
                    hProg
                  have hA1Ne : a1 ≠ Term.Stuck := by
                    intro h
                    subst a1
                    exact hProgLocal
                      (__eo_prog_re_star_union_drop_emp.eq_1 a2)
                  have hA2Ne : a2 ≠ Term.Stuck := by
                    intro h
                    subst a2
                    exact hProgLocal
                      (__eo_prog_re_star_union_drop_emp.eq_2 a1 hA1Ne)
                  have hProgMk :
                      __eo_cmd_step_proven s CRule.re_star_union_drop_emp
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReStarUnionDropEmpProof.mkConcl a1 a2 :=
                    ReStarUnionDropEmpProof.prog_mk_form
                      a1 a2 hA1Ne hA2Ne
                  have hMkNe : ReStarUnionDropEmpProof.mkConcl a1 a2 ≠
                      Term.Stuck := by
                    simpa [hProgMk] using hProg
                  have hEqFunNe :
                      __eo_mk_apply (Term.UOp UserOp.eq)
                          (__eo_mk_apply (Term.UOp UserOp.re_mult)
                            (ReStarUnionDropEmpProof.body a1 a2)) ≠
                        Term.Stuck :=
                    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
                  have hLhsMkNe :
                      __eo_mk_apply (Term.UOp UserOp.re_mult)
                          (ReStarUnionDropEmpProof.body a1 a2) ≠ Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
                  have hBodyNe : ReStarUnionDropEmpProof.body a1 a2 ≠
                      Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hLhsMkNe
                  have hRhsMkNe :
                      __eo_mk_apply (Term.UOp UserOp.re_mult)
                          (ReStarUnionDropEmpProof.reduced a1 a2) ≠
                        Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMkNe
                  have hLists :=
                    RegexRewriteSupport.list_concat_lists_of_ne_stuck
                      (Term.UOp UserOp.re_union) a1
                      (ReStarUnionDropEmpProof.tail a2) hBodyNe
                  have hYsList :
                      __eo_is_list (Term.UOp UserOp.re_union) a2 =
                        Term.Boolean true :=
                    eo_is_list_tail_true_of_cons_self
                      (Term.UOp UserOp.re_union)
                      ReStarUnionDropEmpProof.epsilon a2 hLists.2
                  have hProgApply :
                      __eo_cmd_step_proven s CRule.re_star_union_drop_emp
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReStarUnionDropEmpProof.concl a1 a2 := by
                    rw [hProgMk]
                    unfold ReStarUnionDropEmpProof.mkConcl
                      ReStarUnionDropEmpProof.concl
                      ReStarUnionDropEmpProof.lhs
                      ReStarUnionDropEmpProof.rhs
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsMkNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsMkNe]
                  have hFacts := ReStarUnionDropEmpProof.type_and_facts
                    M hM a1 a2 hLists.1 hYsList hA1Trans hA2Trans
                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    (by simpa [hProgApply] using hFacts.1)⟩
                  intro _hTrue
                  rw [hProgApply]
                  exact hFacts.2
