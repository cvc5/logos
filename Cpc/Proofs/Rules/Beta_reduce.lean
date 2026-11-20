module

public import Cpc.Proofs.RuleSupport.BetaReduceSupport
import all Cpc.Proofs.RuleSupport.BetaReduceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


public theorem cmd_step_beta_reduce_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.beta_reduce args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.beta_reduce args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.beta_reduce args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.beta_reduce args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons e args =>
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
              change __eo_prog_beta_reduce e ≠ Term.Stuck at hProg
              change eoHasSmtTranslation e ∧ True at hCmdTrans
              have hETrans : RuleProofs.eo_has_smt_translation e := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
                  hCmdTrans.1
              -- The argument is an equality `(= a b)` with `a` beta-reducing to `b`.
              have hShape : ∃ a b, e = Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b ∧
                  __beta_reduce a Term.__eo_List_nil = b := by
                unfold __eo_prog_beta_reduce at hProg
                split at hProg
                · rename_i a b
                  exact ⟨a, b, rfl, support_eo_requires_cond_eq_of_non_stuck hProg⟩
                · exact absurd rfl hProg
              obtain ⟨a, b, rfl, hBeta⟩ := hShape
              have hProgEq :
                  __eo_prog_beta_reduce (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
                    Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
                change __eo_requires (__beta_reduce a Term.__eo_List_nil) b
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = _
                exact instantiate_eo_requires_result_eq_of_ne_stuck hProg
              obtain ⟨hSame, hANN⟩ := BetaReduceRule.eq_operands_same_smt_type a b hETrans
              have hEqBool :
                  RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
                RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b hSame hANN
              refine ⟨?_, ?_⟩
              · intro _hEvid
                change eo_interprets M
                  (__eo_prog_beta_reduce (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
                  true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                · exact hEqBool
                · rw [BetaReduceRule.beta_reduce_eval M hM a b hETrans hBeta]
                  exact RuleProofs.smt_value_rel_refl _
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_beta_reduce (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
                rw [hProgEq]
                exact hETrans
