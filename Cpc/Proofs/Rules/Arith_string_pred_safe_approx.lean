module

public import Cpc.Proofs.RuleSupport.ArithStringEntailSupport
import all Cpc.Proofs.RuleSupport.ArithStringEntailSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def geqZero (n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)

private def arithStringPredSafeApproxFormula (n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (geqZero n)) (geqZero m)

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

private theorem requires_body_ne_stuck_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro hReq
  have hxy : x = y := requires_arg_eq_of_ne_stuck hReq
  by_cases hxSt : x = Term.Stuck
  · subst x
    subst y
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at hReq
  · intro hz
    subst z
    have hReqSt : __eo_requires x y Term.Stuck = Term.Stuck := by
      simp [__eo_requires, hxy, native_teq, native_ite, native_not, SmtEval.native_not]
    exact hReq hReqSt

private theorem arith_string_pred_safe_approx_shape_of_ne_stuck
    (a1 : Term) :
  __eo_prog_arith_string_pred_safe_approx a1 ≠ Term.Stuck ->
  ∃ n m,
    a1 = arithStringPredSafeApproxFormula n m ∧
    __str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ∧
    __str_arith_entail_simple_pred (geqZero m) = Term.Boolean true ∧
    __eo_prog_arith_string_pred_safe_approx a1 = a1 := by
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
                                      | Apply rhsF rhsZero =>
                                          cases rhsF with
                                          | Apply rhsGeqOp m =>
                                              cases rhsGeqOp with
                                              | UOp rhsGeqU =>
                                                  cases rhsGeqU with
                                                  | geq =>
                                                      cases rhsZero with
                                                      | Numeral rhsK =>
                                                          by_cases hk : k = 0
                                                          · subst k
                                                            by_cases hrhsK : rhsK = 0
                                                            · subst rhsK
                                                              have hReq :
                                                                  __eo_requires
                                                                      (__str_arith_entail_is_approx
                                                                        n m (Term.Boolean true))
                                                                      (Term.Boolean true)
                                                                      (__eo_requires
                                                                        (__str_arith_entail_simple_pred
                                                                          (geqZero m))
                                                                        (Term.Boolean true)
                                                                        (arithStringPredSafeApproxFormula
                                                                          n m)) ≠
                                                                  Term.Stuck := by
                                                                simpa [__eo_prog_arith_string_pred_safe_approx,
                                                                  geqZero,
                                                                  arithStringPredSafeApproxFormula] using hProg
                                                              have hApprox :
                                                                  __str_arith_entail_is_approx
                                                                      n m (Term.Boolean true) =
                                                                    Term.Boolean true :=
                                                                requires_arg_eq_of_ne_stuck hReq
                                                              have hReqBody :
                                                                  __eo_requires
                                                                      (__str_arith_entail_simple_pred
                                                                        (geqZero m))
                                                                      (Term.Boolean true)
                                                                      (arithStringPredSafeApproxFormula
                                                                        n m) ≠
                                                                    Term.Stuck :=
                                                                requires_body_ne_stuck_of_ne_stuck hReq
                                                              have hSimple :
                                                                  __str_arith_entail_simple_pred
                                                                      (geqZero m) =
                                                                    Term.Boolean true :=
                                                                requires_arg_eq_of_ne_stuck hReqBody
                                                              have hProgEq :
                                                                  __eo_prog_arith_string_pred_safe_approx
                                                                      (arithStringPredSafeApproxFormula
                                                                        n m) =
                                                                    arithStringPredSafeApproxFormula n m := by
                                                                have hSimple' :
                                                                    __str_arith_entail_simple_pred
                                                                        (Term.Apply
                                                                          (Term.Apply
                                                                            (Term.UOp UserOp.geq) m)
                                                                          (Term.Numeral 0)) =
                                                                      Term.Boolean true := by
                                                                  simpa [geqZero] using hSimple
                                                                simp [arithStringPredSafeApproxFormula,
                                                                  geqZero,
                                                                  __eo_prog_arith_string_pred_safe_approx,
                                                                  __eo_requires, hApprox, hSimple',
                                                                  native_teq, native_ite, native_not,
                                                                  SmtEval.native_not]
                                                              exact ⟨n, m, rfl, hApprox, hSimple, hProgEq⟩
                                                            · simp [__eo_prog_arith_string_pred_safe_approx,
                                                                hrhsK] at hProg
                                                          · simp [__eo_prog_arith_string_pred_safe_approx,
                                                              hk] at hProg
                                                      | _ =>
                                                          simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                                                  | _ =>
                                                      simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                                              | _ =>
                                                  simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                                          | _ =>
                                              simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                                      | _ =>
                                          simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                                  | _ =>
                                      simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                              | _ =>
                                  simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                          | _ =>
                              simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                      | _ =>
                          simp [__eo_prog_arith_string_pred_safe_approx] at hProg
                  | _ =>
                      simp [__eo_prog_arith_string_pred_safe_approx] at hProg
              | _ =>
                  simp [__eo_prog_arith_string_pred_safe_approx] at hProg
          | _ =>
              simp [__eo_prog_arith_string_pred_safe_approx] at hProg
      | _ =>
          simp [__eo_prog_arith_string_pred_safe_approx] at hProg
  | _ =>
      simp [__eo_prog_arith_string_pred_safe_approx] at hProg

public theorem cmd_step_arith_string_pred_safe_approx_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_string_pred_safe_approx args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_string_pred_safe_approx args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_string_pred_safe_approx args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_string_pred_safe_approx args premises ≠
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
              change __eo_prog_arith_string_pred_safe_approx a1 ≠ Term.Stuck at hProg
              change __eo_typeof (__eo_prog_arith_string_pred_safe_approx a1) = Term.Bool
                at hResultTy
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              obtain ⟨n, m, hA1Eq, hApprox, hSimple, hProgEq⟩ :=
                arith_string_pred_safe_approx_shape_of_ne_stuck a1 hProg
              have hA1Bool : RuleProofs.eo_has_bool_type a1 :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans
                  (by simpa [hProgEq] using hResultTy)
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_string_pred_safe_approx a1) true
                rw [hProgEq]
                rw [hA1Eq]
                have hFormulaBool :
                    RuleProofs.eo_has_bool_type (arithStringPredSafeApproxFormula n m) := by
                  simpa [hA1Eq] using hA1Bool
                simpa [arithStringPredSafeApproxFormula, geqZero] using
                  arith_string_pred_safe_approx_formula_true
                    M hM n m hFormulaBool hApprox
                    (by simpa [geqZero] using hSimple)
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_arith_string_pred_safe_approx a1)
                rw [hProgEq]
                exact hA1Trans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
