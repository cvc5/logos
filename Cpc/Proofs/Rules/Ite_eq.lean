module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem ite_term_same_smt_type_then
    (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E)) =
      __smtx_typeof (__eo_to_smt T) ∧
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E)) ≠
      SmtType.None := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hNN : term_has_non_none_type
      (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) := by
    unfold term_has_non_none_type
    simpa [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl] using hTrans
  rcases ite_args_of_non_none hNN with ⟨U, hC, hT, hE, hUNonNone⟩
  constructor
  · rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
    rw [typeof_ite_eq]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hC, hT, hE]
  · rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
    rw [typeof_ite_eq]
    simpa [__smtx_typeof_ite, native_ite, native_Teq, hC, hT, hE] using hUNonNone

private theorem ite_term_same_smt_type_else
    (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E)) =
      __smtx_typeof (__eo_to_smt E) ∧
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E)) ≠
      SmtType.None := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hNN : term_has_non_none_type
      (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) := by
    unfold term_has_non_none_type
    simpa [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl] using hTrans
  rcases ite_args_of_non_none hNN with ⟨U, hC, hT, hE, hUNonNone⟩
  constructor
  · rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
    rw [typeof_ite_eq]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hC, hT, hE]
  · rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
    rw [typeof_ite_eq]
    simpa [__smtx_typeof_ite, native_ite, native_Teq, hC, hT, hE] using hUNonNone

private theorem eo_interprets_ite_eq_then_true
    (M : SmtModel) (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    eo_interprets M C true ->
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E))
        T) true := by
  intro hTrans hCTrue
  have hSame := ite_term_same_smt_type_then C T E hTrans
  apply RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) T
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) T
      hSame.1 hSame.2
  · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hCTrue
    cases hCTrue with
    | intro_true _ hCEval =>
        rw [show __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
            SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
        rw [smtx_eval_ite_term_eq, hCEval]
        simpa [__smtx_model_eval_ite] using
          RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt T))

private theorem eo_interprets_ite_eq_else_true
    (M : SmtModel) (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    eo_interprets M C false ->
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E))
        E) true := by
  intro hTrans hCFalse
  have hSame := ite_term_same_smt_type_else C T E hTrans
  apply RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) E
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) E
      hSame.1 hSame.2
  · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hCFalse
    cases hCFalse with
    | intro_false _ hCEval =>
        rw [show __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
            SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
        rw [smtx_eval_ite_term_eq, hCEval]
        simpa [__smtx_model_eval_ite] using
          RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt E))

public theorem cmd_step_ite_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_eq args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons F args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change __eo_prog_ite_eq F ≠ Term.Stuck at hProg
              cases F with
              | Apply f E =>
                  cases f with
                  | Apply g T =>
                      cases g with
                      | Apply op C =>
                          cases op with
                          | UOp op =>
                              cases op with
                              | ite =>
                                  let iteTerm :=
                                    Term.Apply
                                      (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E
                                  let eqThen :=
                                    Term.Apply (Term.Apply (Term.UOp UserOp.eq) iteTerm) T
                                  let eqElse :=
                                    Term.Apply (Term.Apply (Term.UOp UserOp.eq) iteTerm) E
                                  have hIteTrans :
                                      RuleProofs.eo_has_smt_translation iteTerm := by
                                    simpa [iteTerm, cmdTranslationOk, cArgListTranslationOk]
                                      using hCmdTrans
                                  have hCBool : RuleProofs.eo_has_bool_type C :=
                                    CnfSupport.ite_cond_has_bool_type_of_translation C T E
                                      (by simpa [iteTerm] using hIteTrans)
                                  have hSameThen :=
                                    ite_term_same_smt_type_then C T E
                                      (by simpa [iteTerm] using hIteTrans)
                                  have hSameElse :=
                                    ite_term_same_smt_type_else C T E
                                      (by simpa [iteTerm] using hIteTrans)
                                  have hEqThenBool : RuleProofs.eo_has_bool_type eqThen := by
                                    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                      iteTerm T (by simpa [iteTerm] using hSameThen.1)
                                      (by simpa [iteTerm] using hSameThen.2)
                                  have hEqElseBool : RuleProofs.eo_has_bool_type eqElse := by
                                    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                      iteTerm E (by simpa [iteTerm] using hSameElse.1)
                                      (by simpa [iteTerm] using hSameElse.2)
                                  have hResultTrue : eo_interprets M (__eo_prog_ite_eq iteTerm) true := by
                                    rcases CnfSupport.eo_interprets_bool_cases M hM C hCBool with
                                      hCTrue | hCFalse
                                    · have hEqThenTrue : eo_interprets M eqThen true := by
                                        simpa [iteTerm, eqThen] using
                                          eo_interprets_ite_eq_then_true M C T E
                                            (by simpa [iteTerm] using hIteTrans) hCTrue
                                      simpa [__eo_prog_ite_eq, iteTerm, eqThen, eqElse] using
                                        CnfSupport.eo_interprets_ite_true_of_cond_true M
                                          C eqThen eqElse hCTrue hEqThenTrue hEqElseBool
                                    · have hEqElseTrue : eo_interprets M eqElse true := by
                                        simpa [iteTerm, eqElse] using
                                          eo_interprets_ite_eq_else_true M C T E
                                            (by simpa [iteTerm] using hIteTrans) hCFalse
                                      simpa [__eo_prog_ite_eq, iteTerm, eqThen, eqElse] using
                                        CnfSupport.eo_interprets_ite_true_of_cond_false M
                                          C eqThen eqElse hCFalse hEqThenBool hEqElseTrue
                                  refine ⟨?_, ?_⟩
                                  · intro _hPremisesTrue
                                    exact hResultTrue
                                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (RuleProofs.eo_has_bool_type_of_interprets_true M _ hResultTrue)
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
