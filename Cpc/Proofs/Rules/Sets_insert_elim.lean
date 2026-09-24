module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def setInsertTerm (es s : Term) : Term :=
  Term.Apply (Term.Apply Term.set_insert es) s

private def mkEqTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply Term.eq a) b

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_requires_left_ne_stuck_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro hReq hx
  subst x
  have hxy : Term.Stuck = y := eo_requires_arg_eq_of_ne_stuck hReq
  subst y
  simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
    at hReq

private theorem eo_requires_result_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro hReq
  have hxy : x = y := eo_requires_arg_eq_of_ne_stuck hReq
  have hx : x ≠ Term.Stuck := eo_requires_left_ne_stuck_of_ne_stuck hReq
  subst y
  cases x <;> simp [__eo_requires, native_teq, native_ite, native_not,
    SmtEval.native_not] at hx ⊢

private theorem eo_mk_apply_eq_of_ne_stuck
    {f x : Term}
    (hf : f ≠ Term.Stuck)
    (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_to_smt_set_eval_insert_eq_of_ne_stuck
    (es s : Term)
    (hEval : __set_eval_insert es s ≠ Term.Stuck)
    (hInsertNonNone :
      __smtx_typeof (__eo_to_smt_set_insert es (__eo_to_smt s)) ≠
        SmtType.None) :
    __eo_to_smt (__set_eval_insert es s) =
      __eo_to_smt_set_insert es (__eo_to_smt s) := by
  induction es, s using __set_eval_insert.induct with
  | case1 es =>
      simp [__set_eval_insert] at hEval
  | case2 x xs t ht ih =>
      have hTail : __set_eval_insert xs t ≠ Term.Stuck := by
        intro hTail
        apply hEval
        simp [__set_eval_insert, __eo_mk_apply, hTail]
      rw [show
          __set_eval_insert
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) t =
            __eo_mk_apply
              (Term.Apply Term.set_union
                (Term.Apply Term.set_singleton x))
              (__set_eval_insert xs t) by
          simp [__set_eval_insert]]
      rw [eo_mk_apply_eq_of_ne_stuck (by simp) hTail]
      have hTailInsertNonNone :
          __smtx_typeof (__eo_to_smt_set_insert xs (__eo_to_smt t)) ≠
            SmtType.None := by
        have hWholeNN :
            term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt x))
                (__eo_to_smt_set_insert xs (__eo_to_smt t))) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_set_insert] using hInsertNonNone
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq (SmtTerm.set_singleton (__eo_to_smt x))
              (__eo_to_smt_set_insert xs (__eo_to_smt t))) hWholeNN with
          ⟨A, _hHead, hTailTy⟩
        rw [hTailTy]
        intro h
        cases h
      change
        SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt x))
          (__eo_to_smt (__set_eval_insert xs t)) =
          SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt x))
            (__eo_to_smt_set_insert xs (__eo_to_smt t))
      rw [ih hTail hTailInsertNonNone]
  | case3 T t =>
      cases hTy :
          native_Teq (__smtx_typeof (__eo_to_smt t))
            (SmtType.Set (__eo_to_smt_type T))
      · exfalso
        apply hInsertNonNone
        simp [__eo_to_smt_set_insert, hTy, native_ite]
      · simp [__set_eval_insert, __eo_to_smt_set_insert, hTy, native_ite]
  | case4 es s =>
      simp [__set_eval_insert] at hEval

private theorem eo_to_smt_set_insert_top_eq_of_non_none
    (es s : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (setInsertTerm es s)) ≠ SmtType.None) :
    __eo_to_smt (setInsertTerm es s) =
      __eo_to_smt_set_insert es (__eo_to_smt s) := by
  rfl

private theorem typed___eo_prog_sets_insert_elim_impl
    (es s t : Term)
    (hArgTrans : RuleProofs.eo_has_smt_translation
      (mkEqTerm (setInsertTerm es s) t))
    (hProg : __eo_prog_sets_insert_elim
      (mkEqTerm (setInsertTerm es s) t) ≠ Term.Stuck)
    (hTy : __eo_typeof (__eo_prog_sets_insert_elim
      (mkEqTerm (setInsertTerm es s) t)) = Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_sets_insert_elim
        (mkEqTerm (setInsertTerm es s) t)) := by
  let body := mkEqTerm (setInsertTerm es s) t
  let evaluated := __set_eval_insert es s
  have hResultEq :
      __eo_prog_sets_insert_elim body = body := by
    change __eo_requires evaluated t body = body
    exact eo_requires_result_eq_of_ne_stuck hProg
  have hBodyTy : __eo_typeof body = Term.Bool := by
    change __eo_typeof (__eo_prog_sets_insert_elim body) = Term.Bool at hTy
    rwa [hResultEq] at hTy
  have hBodyBool : RuleProofs.eo_has_bool_type body :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type body hArgTrans hBodyTy
  rw [hResultEq]
  exact hBodyBool

private theorem facts___eo_prog_sets_insert_elim_impl
    (M : SmtModel) (hM : model_wf M)
    (es s t : Term)
    (hArgTrans : RuleProofs.eo_has_smt_translation
      (mkEqTerm (setInsertTerm es s) t))
    (hProg : __eo_prog_sets_insert_elim
      (mkEqTerm (setInsertTerm es s) t) ≠ Term.Stuck)
    (hTy : __eo_typeof (__eo_prog_sets_insert_elim
      (mkEqTerm (setInsertTerm es s) t)) = Term.Bool) :
    eo_interprets M
      (__eo_prog_sets_insert_elim
        (mkEqTerm (setInsertTerm es s) t)) true := by
  let lhs := setInsertTerm es s
  let body := mkEqTerm lhs t
  let evaluated := __set_eval_insert es s
  have hResultEq :
      __eo_prog_sets_insert_elim body = body := by
    change __eo_requires evaluated t body = body
    exact eo_requires_result_eq_of_ne_stuck hProg
  have hEvalEq : evaluated = t := by
    change __eo_requires evaluated t body ≠ Term.Stuck at hProg
    exact eo_requires_arg_eq_of_ne_stuck hProg
  have hEvalNe : evaluated ≠ Term.Stuck := by
    change __eo_requires evaluated t body ≠ Term.Stuck at hProg
    exact eo_requires_left_ne_stuck_of_ne_stuck hProg
  have hBodyTy : __eo_typeof body = Term.Bool := by
    change __eo_typeof (__eo_prog_sets_insert_elim body) = Term.Bool at hTy
    rwa [hResultEq] at hTy
  have hBodyBool : RuleProofs.eo_has_bool_type body :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type body hArgTrans hBodyTy
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type lhs t
      hBodyBool with
    ⟨_hSameTy, hLhsNonNone⟩
  have hLhsSmt :
      __eo_to_smt lhs = __eo_to_smt_set_insert es (__eo_to_smt s) :=
    eo_to_smt_set_insert_top_eq_of_non_none es s hLhsNonNone
  have hInsertNonNone :
      __smtx_typeof (__eo_to_smt_set_insert es (__eo_to_smt s)) ≠
        SmtType.None := by
    rw [← hLhsSmt]
    exact hLhsNonNone
  have hEvalSmt :
      __eo_to_smt evaluated =
        __eo_to_smt_set_insert es (__eo_to_smt s) :=
    eo_to_smt_set_eval_insert_eq_of_ne_stuck es s hEvalNe hInsertNonNone
  have hSmtEq : __eo_to_smt lhs = __eo_to_smt t := by
    rw [hLhsSmt, ← hEvalSmt, hEvalEq]
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt t)) := by
    rw [hSmtEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt t))
  rw [hResultEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs t hBodyBool hRel

public theorem cmd_step_sets_insert_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_insert_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_insert_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_insert_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_insert_elim args premises ≠ Term.Stuck :=
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
              cases a1 with
              | Apply f t =>
                  cases f with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp op =>
                          cases op with
                          | eq =>
                              cases lhs with
                              | Apply setInsertFn s =>
                                  cases setInsertFn with
                                  | Apply setInsertOp es =>
                                      cases setInsertOp with
                                      | UOp op =>
                                          cases op with
                                          | set_insert =>
                                              let body :=
                                                mkEqTerm (setInsertTerm es s) t
                                              have hATransPair :
                                                  RuleProofs.eo_has_smt_translation body ∧
                                                    True := by
                                                simpa [cmdTranslationOk,
                                                  cArgListTranslationOk, body,
                                                  mkEqTerm, setInsertTerm]
                                                  using hCmdTrans
                                              have hProgInsert :
                                                  __eo_prog_sets_insert_elim body ≠
                                                    Term.Stuck := by
                                                change __eo_prog_sets_insert_elim body ≠
                                                  Term.Stuck at hProg
                                                exact hProg
                                              have hTyInsert :
                                                  __eo_typeof
                                                    (__eo_prog_sets_insert_elim body) =
                                                    Term.Bool := by
                                                change __eo_typeof
                                                  (__eo_prog_sets_insert_elim body) =
                                                  Term.Bool at hResultTy
                                                exact hResultTy
                                              refine ⟨?_, ?_⟩
                                              · intro _hTrue
                                                change eo_interprets M
                                                  (__eo_prog_sets_insert_elim body) true
                                                exact facts___eo_prog_sets_insert_elim_impl
                                                  M hM es s t hATransPair.1
                                                  hProgInsert hTyInsert
                                              · change RuleProofs.eo_has_smt_translation
                                                  (__eo_prog_sets_insert_elim body)
                                                exact
                                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                    (__eo_prog_sets_insert_elim body)
                                                    (typed___eo_prog_sets_insert_elim_impl
                                                      es s t hATransPair.1
                                                      hProgInsert hTyInsert)
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
