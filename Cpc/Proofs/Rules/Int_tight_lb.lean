module

public import Cpc.Proofs.RuleSupport.IntTightSupport
import all Cpc.Proofs.RuleSupport.IntTightSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_int_tight_lb_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.int_tight_lb args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.int_tight_lb args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.int_tight_lb args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  cases args with
  | cons _ _ =>
      change __eo_typeof Term.Stuck = Term.Bool at hResultTy
      exact False.elim ((by native_decide : __eo_typeof Term.Stuck ≠ Term.Bool) hResultTy)
  | nil =>
    cases premises with
    | nil =>
        change __eo_typeof Term.Stuck = Term.Bool at hResultTy
        exact False.elim ((by native_decide : __eo_typeof Term.Stuck ≠ Term.Bool) hResultTy)
    | cons n premisesTail =>
    cases premisesTail with
    | cons _ _ =>
        change __eo_typeof Term.Stuck = Term.Bool at hResultTy
        exact False.elim ((by native_decide : __eo_typeof Term.Stuck ≠ Term.Bool) hResultTy)
    | nil =>
    let P := __eo_state_proven_nth s n
    have hPremBool : RuleProofs.eo_has_bool_type P :=
      hPremisesBool P (by simp [P, premiseTermList])
    change __eo_typeof (__eo_prog_int_tight_lb (Proof.pf P)) = Term.Bool at hResultTy
    refine ⟨?_, ?_⟩
    · intro hTrue
      have hPremTrue : eo_interprets M P true :=
        hTrue P (by simp [P, premiseTermList])
      change eo_interprets M (__eo_prog_int_tight_lb (Proof.pf P)) true
      exact IntTightSupport.int_tight_lb_prog_interprets
        M hM P hPremBool hResultTy hPremTrue
    · change RuleProofs.eo_has_smt_translation (__eo_prog_int_tight_lb (Proof.pf P))
      exact IntTightSupport.int_tight_lb_prog_has_smt_translation
        P hPremBool hResultTy
