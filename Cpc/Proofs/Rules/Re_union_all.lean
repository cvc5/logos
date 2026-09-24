module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReUnionAllProof

private abbrev sigma : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar)

private abbrev mkReUnion (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) s

private abbrev tail (ys : Term) : Term :=
  mkReUnion sigma ys

private abbrev lhs (xs ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_union) xs (tail ys)

private abbrev concl (xs ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs ys)) sigma

private abbrev mkConcl (xs ys : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs xs ys)) sigma

private theorem prog_mk_form (xs ys : Term)
    (hxs : xs ≠ Term.Stuck) (hys : ys ≠ Term.Stuck) :
    __eo_prog_re_union_all xs ys = mkConcl xs ys := by
  change __eo_prog_re_union_all xs ys =
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__eo_list_concat (Term.UOp UserOp.re_union) xs
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union)
              (Term.Apply (Term.UOp UserOp.re_mult)
                (Term.UOp UserOp.re_allchar)))
            ys)))
      (Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar))
  exact __eo_prog_re_union_all.eq_3 xs ys hxs hys

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
  have ha :
      __eo_is_list f a = Term.Boolean true :=
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
  have hb :
      __eo_is_list f b = Term.Boolean true :=
    RuleProofs.eo_requires_eq_of_ne_stuck
      (__eo_is_list f b) (Term.Boolean true)
      (__eo_list_concat_rec a b) hReqTail
  exact ⟨ha, hb⟩

private theorem reUnion_list_smt_typeof_reglan_of_non_none (t : Term) :
    __eo_is_list (Term.UOp UserOp.re_union) t = Term.Boolean true ->
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
        reglan_binop_args_of_non_none (op := SmtTerm.re_union)
          (typeof_re_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN
      change __smtx_typeof
          (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan
      rw [typeof_re_union_eq]
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

private theorem smtx_typeof_re_union_of_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkReUnion x y)) = SmtType.RegLan := by
  intro hx hy
  change __smtx_typeof (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_union_eq]
  simp [hx, hy, native_ite, native_Teq]

private theorem smt_value_rel_union_all
    (rxs rys : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union rxs (native_re_union native_re_all rys)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  simp only [← RuleProofs.native_str_in_re_eq_model]
  rw [RuleProofs.native_str_in_re_re_union,
    RuleProofs.native_str_in_re_re_union,
    RuleProofs.native_str_in_re_re_all str hValid]
  simp

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
  have hXsTy :
      __smtx_typeof (__eo_to_smt xs) = SmtType.RegLan :=
    reUnion_list_smt_typeof_reglan_of_non_none xs hXsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hXsTrans)
  have hYsTy :
      __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan :=
    reUnion_list_smt_typeof_reglan_of_non_none ys hYsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hYsTrans)
  have hTailList :
      __eo_is_list (Term.UOp UserOp.re_union) (tail ys) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_union) sigma ys (by simp) hYsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt (tail ys)) = SmtType.RegLan :=
    smtx_typeof_re_union_of_args sigma ys smtx_typeof_sigma hYsTy
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rxs, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (tail ys)) =
        SmtValue.RegLan (native_re_union native_re_all rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt sigma) (__eo_to_smt ys)) =
      SmtValue.RegLan (native_re_union native_re_all rys)
    simp [__smtx_model_eval, __smtx_model_eval_re_union,
      smtx_model_eval_sigma M, hYsEval]
  rcases RuleProofs.reUnion_list_concat_eval_rel M xs (tail ys)
      rxs (native_re_union native_re_all rys)
      hXsList hTailList hXsTy hTailTy hXsEval hTailEval with
    ⟨rlhs, hLhsEval, hLhsTy, hConcatRel⟩
  have hBool :
      RuleProofs.eo_has_bool_type (concl xs ys) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs ys) sigma
      (by rw [hLhsTy, smtx_typeof_sigma])
      (by rw [hLhsTy]; simp)
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt sigma) =
        SmtValue.RegLan native_re_all :=
    smtx_model_eval_sigma M
  refine ⟨hBool, ?_⟩
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs xs ys) sigma hBool <| by
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_trans
      (SmtValue.RegLan rlhs)
      (SmtValue.RegLan
        (native_re_union rxs (native_re_union native_re_all rys)))
      (SmtValue.RegLan native_re_all)
      hConcatRel
      (smt_value_rel_union_all rxs rys)

end ReUnionAllProof

public theorem cmd_step_re_union_all_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_union_all args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_union_all args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_union_all args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_union_all args premises ≠
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
                      __eo_prog_re_union_all a1 a2 ≠ Term.Stuck := by
                    change __eo_prog_re_union_all a1 a2 ≠ Term.Stuck at hProg
                    exact hProg
                  have hA1Ne : a1 ≠ Term.Stuck := by
                    intro h
                    subst a1
                    exact hProgLocal (__eo_prog_re_union_all.eq_1 a2)
                  have hA2Ne : a2 ≠ Term.Stuck := by
                    intro h
                    subst a2
                    exact hProgLocal
                      (__eo_prog_re_union_all.eq_2 a1 hA1Ne)
                  have hProgMk :
                      __eo_cmd_step_proven s CRule.re_union_all
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReUnionAllProof.mkConcl a1 a2 :=
                    ReUnionAllProof.prog_mk_form a1 a2 hA1Ne hA2Ne
                  have hMkNe :
                      ReUnionAllProof.mkConcl a1 a2 ≠ Term.Stuck := by
                    simpa [hProgMk] using hProg
                  have hEqFunNe :
                      __eo_mk_apply (Term.UOp UserOp.eq)
                          (ReUnionAllProof.lhs a1 a2) ≠ Term.Stuck :=
                    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
                  have hLhsNe :
                      ReUnionAllProof.lhs a1 a2 ≠ Term.Stuck :=
                    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
                  have hLists :=
                    ReUnionAllProof.list_concat_lists_of_ne_stuck
                      (Term.UOp UserOp.re_union) a1
                      (ReUnionAllProof.tail a2) hLhsNe
                  have hYsList :
                      __eo_is_list (Term.UOp UserOp.re_union) a2 =
                        Term.Boolean true :=
                    eo_is_list_tail_true_of_cons_self
                      (Term.UOp UserOp.re_union) ReUnionAllProof.sigma a2
                      hLists.2
                  have hProgApply :
                      __eo_cmd_step_proven s CRule.re_union_all
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        ReUnionAllProof.concl a1 a2 := by
                    rw [hProgMk]
                    unfold ReUnionAllProof.mkConcl ReUnionAllProof.concl
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe]
                    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
                  have hFacts :=
                    ReUnionAllProof.type_and_facts M hM a1 a2
                      hLists.1 hYsList hA1Trans hA2Trans
                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    (by simpa [hProgApply] using hFacts.1)⟩
                  intro _hTrue
                  rw [hProgApply]
                  exact hFacts.2
