module

public import Cpc.Proofs.RuleSupport.SetsEvalOpSupport
import all Cpc.Proofs.RuleSupport.SetsEvalOpSupport

open Eo
open SmtEval
open Smtm
open SetsEvalOpSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shape of `__eo_prog_sets_eval_op (eq a b)` when it does not get stuck: the
`__eo_list_meq` guard holds and the proven result is the original equality. -/
private theorem prog_sets_eval_op_shape {a b : Term}
    (h : __eo_prog_sets_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠
      Term.Stuck) :
    __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a))
        (__set_union_to_list b) = Term.Boolean true ∧
      __eo_prog_sets_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
  have hForm :
      __eo_prog_sets_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
        __eo_requires (__eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
          (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a))
          (__set_union_to_list b)) (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := rfl
  rw [hForm] at h ⊢
  exact ⟨req_arg_eq h, req_result h⟩

/-- The equality `(eq a b)` proven by the rule is interpreted as `true`: the SMT
set-model values of `a` and `b` coincide. All three set operators (`set.union`,
`set.inter`, `set.minus`) are fully established. -/
private theorem facts_sets_eval_op
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hTransA : RuleProofs.eo_has_smt_translation a)
    (hTransB : RuleProofs.eo_has_smt_translation b)
    (hEqBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
    (hGuard : __eo_list_meq (Term.UOp UserOp._at__at_TypedList_cons)
        (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) (__eval_sets_op a))
        (__set_union_to_list b) = Term.Boolean true) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M a b hEqBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
    ⟨hSameTy, _⟩
  have hEvalNe := guard_eval_ne_stuck a b hGuard
  cases a with
  | Apply f1 t =>
      cases f1 with
      | Apply op s =>
          cases op with
          | UOp uop =>
              cases uop with
              | set_union =>
                  exact union_model_eval_rel M hM s t b hTransA hTransB hSameTy hGuard
              | set_inter =>
                  exact inter_model_eval_rel M hM s t b hTransA hTransB hSameTy hGuard
              | set_minus =>
                  exact minus_model_eval_rel M hM s t b hTransA hTransB hSameTy hGuard
              | _ => exact (hEvalNe rfl).elim
          | _ => exact (hEvalNe rfl).elim
      | _ => exact (hEvalNe rfl).elim
  | _ => exact (hEvalNe rfl).elim

public theorem cmd_step_sets_eval_op_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_eval_op args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_eval_op args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_eval_op args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_eval_op args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
              change __eo_typeof (__eo_prog_sets_eval_op a1) = Term.Bool at hResultTy
              change __eo_prog_sets_eval_op a1 ≠ Term.Stuck at hProg
              cases a1 with
              | Apply f b =>
                  cases f with
                  | Apply eqop a =>
                      cases eqop with
                      | UOp op =>
                          cases op with
                          | eq =>
                              obtain ⟨hGuard, hProgEq⟩ := prog_sets_eval_op_shape hProg
                              have hTransA1 :
                                  RuleProofs.eo_has_smt_translation
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
                                simpa [cmdTranslationOk, cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                                  using hCmdTrans
                              have hTyEq :
                                  __eo_typeof
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
                                    Term.Bool := by
                                rw [← hProgEq]; exact hResultTy
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
                                RuleProofs.eo_typeof_bool_implies_has_bool_type _ hTransA1 hTyEq
                              rcases
                                RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b
                                  hEqBool with ⟨hSameTy, hAne⟩
                              have hTransA : RuleProofs.eo_has_smt_translation a := hAne
                              have hTransB : RuleProofs.eo_has_smt_translation b := by
                                unfold RuleProofs.eo_has_smt_translation
                                rw [← hSameTy]; exact hAne
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M (__eo_prog_sets_eval_op
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) true
                                rw [hProgEq]
                                exact facts_sets_eval_op M hM a b hTransA hTransB hEqBool hGuard
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_sets_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
                                rw [hProgEq]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
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
