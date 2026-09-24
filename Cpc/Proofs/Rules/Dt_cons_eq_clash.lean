module

public import Cpc.Proofs.RuleSupport.DistinctTermsSupport
import all Cpc.Proofs.RuleSupport.DistinctTermsSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_dt_cons_eq_clash_shape_of_not_stuck
    (t s : Term) :
    __eo_prog_dt_cons_eq_clash
        (Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s))
          (Term.Boolean false)) ≠
      Term.Stuck ->
    let guard :=
      __eo_ite (__eo_eq t s) (Term.Boolean false)
        (__are_distinct_terms_type t s (__eo_typeof t))
    guard = Term.Boolean true ∧
      __eo_prog_dt_cons_eq_clash
          (Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s))
            (Term.Boolean false)) =
        Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s))
          (Term.Boolean false) := by
  intro hProg
  let guard :=
      __eo_ite (__eo_eq t s) (Term.Boolean false)
        (__are_distinct_terms_type t s (__eo_typeof t))
  let result :=
      Term.Apply
        (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s))
        (Term.Boolean false)
  have hReq : __eo_requires guard (Term.Boolean true) result ≠ Term.Stuck := by
    simpa [__eo_prog_dt_cons_eq_clash, guard, result] using hProg
  constructor
  · exact _root_.eo_requires_arg_eq_of_ne_stuck hReq
  · simpa [__eo_prog_dt_cons_eq_clash, guard, result] using
      _root_.eo_requires_result_eq_of_ne_stuck hReq

public theorem cmd_step_dt_cons_eq_clash_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cons_eq_clash args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_cons_eq_clash args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cons_eq_clash args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_cons_eq_clash args premises ≠
      Term.Stuck :=
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
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              have hProgRule : __eo_prog_dt_cons_eq_clash a1 ≠ Term.Stuck := by
                have hsimpa := hProg
                try simp at hsimpa ⊢
                exact hsimpa
              cases a1 with
              | Apply f B =>
                  cases B with
                  | Boolean b =>
                      cases b
                      · cases f with
                        | Apply g lhs =>
                            cases g with
                            | UOp op =>
                                cases op with
                                | eq =>
                                    cases lhs with
                                    | Apply f' s' =>
                                        cases f' with
                                        | Apply g' t' =>
                                            cases g' with
                                            | UOp op' =>
                                                cases op' with
                                                | eq =>
                                                    let proven :=
                                                      Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply
                                                            (Term.Apply Term.eq t') s'))
                                                        (Term.Boolean false)
                                                    have hShape :=
                                                      prog_dt_cons_eq_clash_shape_of_not_stuck
                                                        t' s' hProgRule
                                                    have hGuardEq :
                                                        __eo_ite (__eo_eq t' s')
                                                            (Term.Boolean false)
                                                            (__are_distinct_terms_type t' s'
                                                              (__eo_typeof t')) =
                                                          Term.Boolean true :=
                                                      hShape.1
                                                    have hProgEq :
                                                        __eo_prog_dt_cons_eq_clash proven =
                                                          proven := by
                                                      simpa [proven] using hShape.2
                                                    have hAType : __eo_typeof proven = Term.Bool := by
                                                      have hResultTy' := hResultTy
                                                      change __eo_typeof
                                                          (__eo_prog_dt_cons_eq_clash proven) =
                                                        Term.Bool at hResultTy'
                                                      rw [hProgEq] at hResultTy'
                                                      exact hResultTy'
                                                    have hABool :
                                                        RuleProofs.eo_has_bool_type proven :=
                                                      RuleProofs.eo_typeof_bool_implies_has_bool_type
                                                        _ hATrans hAType
                                                    have hInnerBool :
                                                        RuleProofs.eo_has_bool_type
                                                          (Term.Apply (Term.Apply Term.eq t') s') :=
                                                      eo_eq_has_bool_type_of_eq_has_bool_type
                                                        t' s' (Term.Boolean false) hABool
                                                    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                        t' s' hInnerBool with
                                                      ⟨hTyEq, hTTrans⟩
                                                    have hSTrans : RuleProofs.eo_has_smt_translation s' := by
                                                      change
                                                        __smtx_typeof (__eo_to_smt s') ≠
                                                          SmtType.None
                                                      rw [← hTyEq]
                                                      exact hTTrans
                                                    rcases eo_ite_eq_false_guard_true hGuardEq with
                                                      ⟨hEqFalse, hDistinct⟩
                                                    have hEvalEqFalse :
                                                        __smtx_model_eval_eq
                                                          (__smtx_model_eval M (__eo_to_smt t'))
                                                          (__smtx_model_eval M (__eo_to_smt s')) =
                                                          SmtValue.Boolean false :=
                                                      are_distinct_terms_type_model_eval_eq_false
                                                        M hM t' s' hTTrans hSTrans
                                                        hEqFalse hDistinct
                                                    refine ⟨?_, ?_⟩
                                                    · intro _hTrue
                                                      change eo_interprets M
                                                        (__eo_prog_dt_cons_eq_clash proven) true
                                                      rw [hProgEq]
                                                      have hInnerEval :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt
                                                                (Term.Apply
                                                                  (Term.Apply Term.eq t') s')) =
                                                            SmtValue.Boolean false := by
                                                        change __smtx_model_eval M
                                                            (SmtTerm.eq (__eo_to_smt t')
                                                              (__eo_to_smt s')) =
                                                          SmtValue.Boolean false
                                                        simp [__smtx_model_eval, hEvalEqFalse]
                                                      have hFalseEval :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt (Term.Boolean false)) =
                                                            SmtValue.Boolean false := by
                                                        simp [__smtx_model_eval]
                                                      have hRel :
                                                          RuleProofs.smt_value_rel
                                                            (__smtx_model_eval M
                                                              (__eo_to_smt
                                                                (Term.Apply
                                                                  (Term.Apply Term.eq t') s')))
                                                            (__smtx_model_eval M
                                                              (__eo_to_smt (Term.Boolean false))) := by
                                                        rw [hInnerEval, hFalseEval]
                                                        exact RuleProofs.smt_value_rel_refl
                                                          (SmtValue.Boolean false)
                                                      exact RuleProofs.eo_interprets_eq_of_rel M
                                                        (Term.Apply (Term.Apply Term.eq t') s')
                                                        (Term.Boolean false) hABool hRel
                                                    · change RuleProofs.eo_has_smt_translation
                                                        (__eo_prog_dt_cons_eq_clash proven)
                                                      rw [hProgEq]
                                                      exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                        _ hABool
                                                | _ =>
                                                    simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                                            | _ =>
                                                simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                                        | _ =>
                                            simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                                    | _ =>
                                        simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                                | _ =>
                                    simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                            | _ =>
                                simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                        | _ =>
                            simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                      · simp [__eo_prog_dt_cons_eq_clash] at hProgRule
                  | _ =>
                      simp [__eo_prog_dt_cons_eq_clash] at hProgRule
              | _ =>
                  simp [__eo_prog_dt_cons_eq_clash] at hProgRule
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
