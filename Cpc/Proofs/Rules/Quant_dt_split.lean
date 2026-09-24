module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.QuantDtSplitSupport
import all Cpc.Proofs.RuleSupport.QuantDtSplitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def quantDtSplitFormula (x ys F G : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.forall)
          (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
        F))
    G

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem quant_dt_split_shape_of_non_stuck (a : Term) :
    __eo_prog_quant_dt_split a ≠ Term.Stuck ->
    ∃ x ys F G,
      a = quantDtSplitFormula x ys F G ∧
      __is_quant_dt_split x (__dt_get_constructors (__eo_typeof x)) ys F G =
        Term.Boolean true ∧
      __eo_prog_quant_dt_split a = a := by
  intro hProg
  cases a with
  | Apply f G =>
      cases f with
      | Apply op lhs =>
          cases op with
          | UOp u =>
              cases u with
              | eq =>
                  cases lhs with
                  | Apply qF F =>
                      cases qF with
                      | Apply q vars =>
                          cases q with
                          | UOp qop =>
                              cases qop with
                              | «forall» =>
                                  cases vars with
                                  | Apply consX ys =>
                                      cases consX with
                                      | Apply cons x =>
                                          cases cons <;>
                                            try
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                          let body := quantDtSplitFormula x ys F G
                                          let guard :=
                                            __is_quant_dt_split x
                                              (__dt_get_constructors (__eo_typeof x)) ys F G
                                          have hGuard : guard = Term.Boolean true :=
                                            eo_requires_eq_of_ne_stuck guard
                                              (Term.Boolean true) body
                                              (by
                                                simpa [__eo_prog_quant_dt_split,
                                                  quantDtSplitFormula, body, guard]
                                                  using hProg)
                                          have hProgEq :
                                              __eo_prog_quant_dt_split
                                                  (quantDtSplitFormula x ys F G) =
                                                quantDtSplitFormula x ys F G := by
                                            simp [__eo_prog_quant_dt_split,
                                              quantDtSplitFormula, guard, hGuard,
                                              __eo_requires, native_teq, native_ite,
                                              SmtEval.native_not]
                                          exact ⟨x, ys, F, G, rfl, hGuard, by
                                            simpa [quantDtSplitFormula] using hProgEq⟩
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
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem quant_dt_split_formula_true
    (M : SmtModel) (hM : model_wf M)
    (x ys F G : Term) :
    RuleProofs.eo_has_smt_translation (quantDtSplitFormula x ys F G) ->
    __eo_typeof (quantDtSplitFormula x ys F G) = Term.Bool ->
    __is_quant_dt_split x (__dt_get_constructors (__eo_typeof x)) ys F G =
      Term.Boolean true ->
    eo_interprets M (quantDtSplitFormula x ys F G) true := by
  intro hTrans hTy hGuard
  exact QuantDtSplitRule.qds_formula_true M hM x ys F G hGuard hTrans hTy

public theorem cmd_step_quant_dt_split_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_dt_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_dt_split args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_dt_split args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.quant_dt_split args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATransPair : RuleProofs.eo_has_smt_translation a ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a := hATransPair.1
              rcases quant_dt_split_shape_of_non_stuck a (by
                  change __eo_prog_quant_dt_split a ≠ Term.Stuck at hProg
                  exact hProg) with
                ⟨x, ys, F, G, hAEq, hGuard, hProgEq⟩
              have hFormulaTy :
                  __eo_typeof (quantDtSplitFormula x ys F G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_dt_split a) = Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                simpa [hAEq] using hResultTy
              have hFormulaTrans :
                  RuleProofs.eo_has_smt_translation
                    (quantDtSplitFormula x ys F G) := by
                simpa [hAEq] using hATrans
              have hFact : eo_interprets M (quantDtSplitFormula x ys F G) true :=
                quant_dt_split_formula_true M hM x ys F G
                  hFormulaTrans hFormulaTy hGuard
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_dt_split a) true
                rw [hProgEq]
                rw [hAEq]
                exact hFact
              · change RuleProofs.eo_has_smt_translation (__eo_prog_quant_dt_split a)
                rw [hProgEq]
                rw [hAEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_typeof_bool_implies_has_bool_type _
                    hFormulaTrans hFormulaTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
