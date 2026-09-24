module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReStarUnionCharProof

private abbrev allchar : Term := Term.UOp UserOp.re_allchar

private abbrev sigma : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) allchar

private abbrev mkReUnion (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) s

private abbrev tail (ys : Term) : Term :=
  mkReUnion allchar ys

private abbrev body (xs ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_union) xs (tail ys)

private abbrev lhs (xs ys : Term) : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (body xs ys)

private abbrev concl (xs ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs ys)) sigma

private abbrev mkConcl (xs ys : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.UOp UserOp.re_mult) (body xs ys))) sigma

private theorem prog_mk_form (xs ys : Term)
    (hxs : xs ≠ Term.Stuck) (hys : ys ≠ Term.Stuck) :
    __eo_prog_re_star_union_char xs ys = mkConcl xs ys := by
  exact __eo_prog_re_star_union_char.eq_3 xs ys hxs hys

private theorem smtx_typeof_allchar :
    __smtx_typeof (__eo_to_smt allchar) = SmtType.RegLan := by
  rfl

private theorem smtx_typeof_sigma :
    __smtx_typeof (__eo_to_smt sigma) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult SmtTerm.re_allchar) =
    SmtType.RegLan
  rw [typeof_re_mult_eq, __smtx_typeof.eq_104]
  native_decide

private theorem smtx_model_eval_allchar (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt allchar) =
      SmtValue.RegLan native_re_allchar := by
  rfl

private theorem smtx_model_eval_sigma (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt sigma) =
      SmtValue.RegLan native_re_all := by
  change __smtx_model_eval M (SmtTerm.re_mult SmtTerm.re_allchar) =
    SmtValue.RegLan native_re_all
  simp [__smtx_model_eval, RuleProofs.smtx_model_eval_re_mult_allchar]

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
      (Term.UOp UserOp.re_union) allchar ys (by simp) hYsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt (tail ys)) = SmtType.RegLan :=
    smtx_typeof_re_union_of_args allchar ys smtx_typeof_allchar hYsTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rxs, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (tail ys)) =
        SmtValue.RegLan (native_re_union native_re_allchar rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt allchar) (__eo_to_smt ys)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_union,
      smtx_model_eval_allchar M, hYsEval]
  rcases RuleProofs.reUnion_list_concat_eval_rel M xs (tail ys)
      rxs (native_re_union native_re_allchar rys)
      hXsList hTailList hXsTy hTailTy hXsEval hTailEval with
    ⟨rbody, hBodyEval, hBodyTy, hBodyRel⟩
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs xs ys)) = SmtType.RegLan :=
    smtx_typeof_re_mult_of_reglan (body xs ys) hBodyTy
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs xs ys)) =
        SmtValue.RegLan (native_re_mult rbody) := by
    change __smtx_model_eval M
        (SmtTerm.re_mult (__eo_to_smt (body xs ys))) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_mult, hBodyEval]
  have hBool : RuleProofs.eo_has_bool_type (concl xs ys) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys) sigma
      (by rw [hLhsTy, smtx_typeof_sigma])
      (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs xs ys) sigma hBool <| by
    rw [hLhsEval, smtx_model_eval_sigma M]
    exact RuleProofs.smt_value_rel_trans _ _ _
      (RuleProofs.smt_value_rel_re_mult_congr hBodyRel)
      (RuleProofs.smt_value_rel_re_star_union_allchar rxs rys)

end ReStarUnionCharProof

public theorem cmd_step_re_star_union_char_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_union_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_star_union_char args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_union_char args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_star_union_char args premises ≠
      Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | cons _ _ =>
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
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
                      __eo_prog_re_star_union_char a1 a2 ≠ Term.Stuck := by
                    exact hProg
                  have hA1Ne : a1 ≠ Term.Stuck := by
                    intro h
                    subst a1
                    exact hProgLocal (__eo_prog_re_star_union_char.eq_1 a2)
                  have hA2Ne : a2 ≠ Term.Stuck := by
                    intro h
                    subst a2
                    exact hProgLocal
                      (__eo_prog_re_star_union_char.eq_2 a1 hA1Ne)
                  have hProgMk :
                      __eo_cmd_step_proven s CRule.re_star_union_char
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReStarUnionCharProof.mkConcl a1 a2 :=
                    ReStarUnionCharProof.prog_mk_form a1 a2 hA1Ne hA2Ne
                  have hMkNe : ReStarUnionCharProof.mkConcl a1 a2 ≠
                      Term.Stuck := by
                    simpa [hProgMk] using hProg
                  have hEqFunNe :
                      __eo_mk_apply (Term.UOp UserOp.eq)
                          (__eo_mk_apply (Term.UOp UserOp.re_mult)
                            (ReStarUnionCharProof.body a1 a2)) ≠
                        Term.Stuck :=
                    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
                  have hLhsMkNe :
                      __eo_mk_apply (Term.UOp UserOp.re_mult)
                          (ReStarUnionCharProof.body a1 a2) ≠ Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
                  have hBodyNe : ReStarUnionCharProof.body a1 a2 ≠
                      Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hLhsMkNe
                  have hLists :=
                    RegexRewriteSupport.list_concat_lists_of_ne_stuck
                      (Term.UOp UserOp.re_union) a1
                      (ReStarUnionCharProof.tail a2) hBodyNe
                  have hYsList :
                      __eo_is_list (Term.UOp UserOp.re_union) a2 =
                        Term.Boolean true :=
                    eo_is_list_tail_true_of_cons_self
                      (Term.UOp UserOp.re_union)
                      ReStarUnionCharProof.allchar a2 hLists.2
                  have hProgApply :
                      __eo_cmd_step_proven s CRule.re_star_union_char
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReStarUnionCharProof.concl a1 a2 := by
                    rw [hProgMk]
                    unfold ReStarUnionCharProof.mkConcl
                      ReStarUnionCharProof.concl ReStarUnionCharProof.lhs
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsMkNe]
                  have hFacts := ReStarUnionCharProof.type_and_facts
                    M hM a1 a2 hLists.1 hYsList hA1Trans hA2Trans
                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    (by simpa [hProgApply] using hFacts.1)⟩
                  intro _hTrue
                  rw [hProgApply]
                  exact hFacts.2
