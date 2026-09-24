module

public import Cpc.Proofs.RuleSupport.ArithStringEntailSupport
import all Cpc.Proofs.RuleSupport.ArithStringEntailSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def arithStringPredEntailFormula (n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
    (Term.Boolean true)

private theorem requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : x = y
  · exact hEq
  · exfalso
    have hTeq : native_teq x y = false := by
      simp [native_teq, hEq]
    simp [__eo_requires, hTeq, native_ite] at hReq

private theorem arith_string_pred_entail_shape_of_ne_stuck
    (a1 : Term) :
  __eo_prog_arith_string_pred_entail a1 ≠ Term.Stuck ->
  ∃ n,
    a1 = arithStringPredEntailFormula n ∧
    __str_arith_entail_simple_rec (__get_arith_poly_norm n) = Term.Boolean true ∧
    __eo_prog_arith_string_pred_entail a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f rhs =>
      cases f with
      | Apply op lhs =>
          cases op with
          | UOp u =>
              cases u with
              | eq =>
                  cases lhs with
                  | Apply geqF zero =>
                      cases geqF with
                      | Apply geqOp n =>
                          cases geqOp with
                          | UOp geqU =>
                              cases geqU with
                              | geq =>
                                  cases zero with
                                  | Numeral k =>
                                      cases rhs with
                                      | Boolean b =>
                                          cases b
                                          · simp [__eo_prog_arith_string_pred_entail] at hProg
                                          · by_cases hk : k = 0
                                            · subst k
                                              have hReq :
                                                  __eo_requires
                                                      (__str_arith_entail_simple_rec
                                                        (__get_arith_poly_norm n))
                                                      (Term.Boolean true)
                                                      (arithStringPredEntailFormula n) ≠
                                                    Term.Stuck := by
                                                simpa [__eo_prog_arith_string_pred_entail,
                                                  arithStringPredEntailFormula] using hProg
                                              have hGuard :
                                                  __str_arith_entail_simple_rec
                                                      (__get_arith_poly_norm n) =
                                                    Term.Boolean true :=
                                                requires_arg_eq_of_ne_stuck hReq
                                              have hProgEq :
                                                  __eo_prog_arith_string_pred_entail
                                                      (arithStringPredEntailFormula n) =
                                                    arithStringPredEntailFormula n := by
                                                simp [arithStringPredEntailFormula,
                                                  __eo_prog_arith_string_pred_entail,
                                                  __eo_requires, hGuard, native_teq,
                                                  native_ite, native_not, SmtEval.native_not]
                                              exact ⟨n, rfl, hGuard, hProgEq⟩
                                            · simp [__eo_prog_arith_string_pred_entail, hk] at hProg
                                      | _ =>
                                          simp [__eo_prog_arith_string_pred_entail] at hProg
                                  | _ =>
                                      simp [__eo_prog_arith_string_pred_entail] at hProg
                              | _ =>
                                  simp [__eo_prog_arith_string_pred_entail] at hProg
                          | _ =>
                              simp [__eo_prog_arith_string_pred_entail] at hProg
                      | _ =>
                          simp [__eo_prog_arith_string_pred_entail] at hProg
                  | _ =>
                      simp [__eo_prog_arith_string_pred_entail] at hProg
              | _ =>
                  simp [__eo_prog_arith_string_pred_entail] at hProg
          | _ =>
              simp [__eo_prog_arith_string_pred_entail] at hProg
      | _ =>
          simp [__eo_prog_arith_string_pred_entail] at hProg
  | _ =>
      simp [__eo_prog_arith_string_pred_entail] at hProg

public theorem cmd_step_arith_string_pred_entail_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_string_pred_entail args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_string_pred_entail args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_string_pred_entail args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_string_pred_entail args premises ≠
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
              change __eo_prog_arith_string_pred_entail a1 ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_arith_string_pred_entail a1) = Term.Bool
                at hResultTy
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              obtain ⟨n, hA1Eq, hSimple, hProgEq⟩ :=
                arith_string_pred_entail_shape_of_ne_stuck a1 hProg
              have hA1Bool : RuleProofs.eo_has_bool_type a1 :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans
                  (by simpa [hProgEq] using hResultTy)
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_string_pred_entail a1) true
                rw [hProgEq]
                rw [hA1Eq]
                have hFormulaBool :
                    RuleProofs.eo_has_bool_type (arithStringPredEntailFormula n) := by
                  simpa [hA1Eq] using hA1Bool
                simpa [arithStringPredEntailFormula] using
                  arith_string_pred_entail_formula_true M hM n hFormulaBool hSimple
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_arith_string_pred_entail a1)
                rw [hProgEq]
                exact hA1Trans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
