module

public import Cpc.Proofs.RuleSupport.DtConsEqSupport
import all Cpc.Proofs.RuleSupport.DtConsEqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_dt_cons_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cons_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_cons_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cons_eq args premises) := by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_cons_eq args premises ≠ Term.Stuck :=
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
              have hProgRule : __eo_prog_dt_cons_eq a1 ≠ Term.Stuck := by
                exact hProg
              cases a1 with
              | Apply f B =>
                  cases f with
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
                                              let cond :=
                                                __eo_list_singleton_elim
                                                  (Term.UOp UserOp.and) (__mk_dt_cons_eq t' s')
                                              have hCondData :=
                                                prog_dt_cons_eq_condition_of_not_stuck t' s' B hProgRule
                                              have hCondEq : cond = B := hCondData.1
                                              have hCondNe : cond ≠ Term.Stuck := hCondData.2
                                              have hProgEq :
                                                  __eo_prog_dt_cons_eq
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply (Term.Apply Term.eq t') s'))
                                                        B) =
                                                    Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B :=
                                                prog_dt_cons_eq_eq_input_of_not_stuck t' s' B hProgRule
                                              have hAType :
                                                  __eo_typeof
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply (Term.Apply Term.eq t') s'))
                                                        B) = Term.Bool := by
                                                have hResultTy' := hResultTy
                                                change __eo_typeof
                                                    (__eo_prog_dt_cons_eq
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply (Term.Apply Term.eq t') s'))
                                                        B)) = Term.Bool at hResultTy'
                                                rw [hProgEq] at hResultTy'
                                                exact hResultTy'
                                              have hABool :
                                                  RuleProofs.eo_has_bool_type
                                                    (Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B) :=
                                                RuleProofs.eo_typeof_bool_implies_has_bool_type
                                                  _ hATrans hAType
                                              have hInnerBool :
                                                  RuleProofs.eo_has_bool_type
                                                    (Term.Apply (Term.Apply Term.eq t') s') :=
                                                eo_eq_has_bool_type_of_eq_has_bool_type t' s' B hABool
                                              refine ⟨?_, ?_⟩
                                              · intro _hTrue
                                                change eo_interprets M
                                                  (__eo_prog_dt_cons_eq
                                                    (Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B)) true
                                                rw [hProgEq]
                                                have hCondRel :
                                                    RuleProofs.smt_value_rel
                                                      (__smtx_model_eval M
                                                        (__eo_to_smt
                                                          (Term.Apply
                                                            (Term.Apply Term.eq t') s')))
                                                      (__smtx_model_eval M (__eo_to_smt cond)) :=
                                                  dt_cons_eq_condition_rel M hM t' s' hInnerBool hCondNe
                                                subst B
                                                simpa using
                                                  RuleProofs.eo_interprets_eq_of_rel M
                                                    (Term.Apply (Term.Apply Term.eq t') s')
                                                    cond
                                                    hABool
                                                    hCondRel
                                              · change RuleProofs.eo_has_smt_translation
                                                  (__eo_prog_dt_cons_eq
                                                    (Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B))
                                                rw [hProgEq]
                                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                  _ hABool
                                          | _ =>
                                              simp [__eo_prog_dt_cons_eq] at hProgRule
                                      | _ =>
                                          simp [__eo_prog_dt_cons_eq] at hProgRule
                                  | _ =>
                                      simp [__eo_prog_dt_cons_eq] at hProgRule
                              | _ =>
                                  simp [__eo_prog_dt_cons_eq] at hProgRule
                          | _ =>
                              simp [__eo_prog_dt_cons_eq] at hProgRule
                      | _ =>
                          simp [__eo_prog_dt_cons_eq] at hProgRule
                  | _ =>
                      simp [__eo_prog_dt_cons_eq] at hProgRule
              | _ =>
                  simp [__eo_prog_dt_cons_eq] at hProgRule
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
