module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem set_singleton_arg_non_none (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hSingleton hNone
  change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) ≠
    SmtType.None at hSingleton
  rw [smtx_typeof_set_singleton_term_eq] at hSingleton
  have hSingletonNone :
      __smtx_typeof_guard_wf (SmtType.Set SmtType.None) (SmtType.Set SmtType.None) =
        SmtType.None := by
    have hWfNone : __smtx_type_wf (SmtType.Set SmtType.None) = false := by
      simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        SmtEval.native_and]
    simp [__smtx_typeof_guard_wf, hWfNone, native_ite]
  rw [hNone] at hSingleton
  exact hSingleton hSingletonNone

private theorem set_singleton_type_of_non_none (x : Term)
    (h : __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) =
      SmtType.Set (__smtx_typeof (__eo_to_smt x)) := by
  change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) =
    SmtType.Set (__smtx_typeof (__eo_to_smt x))
  rw [smtx_typeof_set_singleton_term_eq]
  exact smtx_typeof_guard_wf_of_non_none
    (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
    (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
    (by
      change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) ≠
        SmtType.None at h
      rwa [smtx_typeof_set_singleton_term_eq] at h)

private theorem singleton_rel_implies_eq
    {v w : SmtValue}
    (h :
      RuleProofs.smt_value_rel
        (__smtx_model_eval_set_singleton v)
        (__smtx_model_eval_set_singleton w)) :
    w = v := by
  have hNotReg :
      ¬ ∃ r1 r2,
        __smtx_model_eval_set_singleton v = SmtValue.RegLan r1 ∧
          __smtx_model_eval_set_singleton w = SmtValue.RegLan r2 := by
    intro hReg
    rcases hReg with ⟨r1, _r2, h1, _h2⟩
    simp [__smtx_model_eval_set_singleton] at h1
  have hEq := (RuleProofs.smt_value_rel_iff_eq _ _ hNotReg).1 h
  simp [__smtx_model_eval_set_singleton] at hEq
  exact hEq.1.symm

private theorem typed___eo_prog_sets_singleton_inj_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_sets_singleton_inj (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_sets_singleton_inj (Proof.pf x1)) := by
  intro hXBool hProg
  cases x1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply f1 a =>
                      cases f1 with
                      | UOp op1 =>
                          cases op1 with
                          | set_singleton =>
                              cases rhs with
                              | Apply f2 b =>
                                  cases f2 with
                                  | UOp op2 =>
                                      cases op2 with
                                      | set_singleton =>
                                          have hPremBool :
                                              RuleProofs.eo_has_bool_type
                                                (Term.Apply
                                                  (Term.Apply Term.eq (Term.Apply Term.set_singleton a))
                                                  (Term.Apply Term.set_singleton b)) := by
                                            simpa using hXBool
                                          rcases
                                              RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                (Term.Apply Term.set_singleton a)
                                                (Term.Apply Term.set_singleton b)
                                                hPremBool with
                                            ⟨hSingletonTyEq, hSingletonNN⟩
                                          have hSingletonNNB :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton b)) ≠
                                                SmtType.None := by
                                            rwa [← hSingletonTyEq]
                                          have hATrans : RuleProofs.eo_has_smt_translation a :=
                                            set_singleton_arg_non_none a hSingletonNN
                                          have hBTrans : RuleProofs.eo_has_smt_translation b :=
                                            set_singleton_arg_non_none b hSingletonNNB
                                          have hSingletonATy :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton a)) =
                                                SmtType.Set (__smtx_typeof (__eo_to_smt a)) :=
                                            set_singleton_type_of_non_none a hSingletonNN
                                          have hSingletonBTy :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton b)) =
                                                SmtType.Set (__smtx_typeof (__eo_to_smt b)) :=
                                            set_singleton_type_of_non_none b hSingletonNNB
                                          have hABTy :
                                              __smtx_typeof (__eo_to_smt a) =
                                                __smtx_typeof (__eo_to_smt b) := by
                                            have hSetTy :
                                                SmtType.Set (__smtx_typeof (__eo_to_smt a)) =
                                                  SmtType.Set (__smtx_typeof (__eo_to_smt b)) := by
                                              rw [← hSingletonATy, ← hSingletonBTy]
                                              exact hSingletonTyEq
                                            injection hSetTy with hABTy
                                          simpa [__eo_prog_sets_singleton_inj] using
                                            RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                              a b hABTy hATrans
                                      | _ =>
                                          simp [__eo_prog_sets_singleton_inj] at hProg
                                  | _ =>
                                      simp [__eo_prog_sets_singleton_inj] at hProg
                              | _ =>
                                  simp [__eo_prog_sets_singleton_inj] at hProg
                          | _ =>
                              simp [__eo_prog_sets_singleton_inj] at hProg
                      | _ =>
                          simp [__eo_prog_sets_singleton_inj] at hProg
                  | _ =>
                      simp [__eo_prog_sets_singleton_inj] at hProg
              | _ =>
                  simp [__eo_prog_sets_singleton_inj] at hProg
          | _ =>
              simp [__eo_prog_sets_singleton_inj] at hProg
      | _ =>
          simp [__eo_prog_sets_singleton_inj] at hProg
  | _ =>
      simp [__eo_prog_sets_singleton_inj] at hProg

private theorem singleton_term_rel_implies_eq
    (M : SmtModel) (a b : Term)
    (h :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.set_singleton a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.set_singleton b)))) :
    __smtx_model_eval M (__eo_to_smt b) =
      __smtx_model_eval M (__eo_to_smt a) := by
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt a)))
    (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt b))) at h
  rw [smtx_eval_set_singleton_term_eq, smtx_eval_set_singleton_term_eq] at h
  exact singleton_rel_implies_eq h

private theorem facts___eo_prog_sets_singleton_inj_impl
    (M : SmtModel) (x1 : Term) :
    eo_interprets M x1 true ->
    __eo_prog_sets_singleton_inj (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_sets_singleton_inj (Proof.pf x1)) true := by
  intro hXTrue hProg
  have hXBool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hXTrue
  have hOutBool :
      RuleProofs.eo_has_bool_type (__eo_prog_sets_singleton_inj (Proof.pf x1)) :=
    typed___eo_prog_sets_singleton_inj_impl x1 hXBool hProg
  cases x1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply f1 a =>
                      cases f1 with
                      | UOp op1 =>
                          cases op1 with
                          | set_singleton =>
                              cases rhs with
                              | Apply f2 b =>
                                  cases f2 with
                                  | UOp op2 =>
                                      cases op2 with
                                      | set_singleton =>
                                          have hPremTrue :
                                              eo_interprets M
                                                (Term.Apply
                                                  (Term.Apply Term.eq (Term.Apply Term.set_singleton a))
                                                  (Term.Apply Term.set_singleton b)) true := by
                                            simpa using hXTrue
                                          have hSetRel :
                                              RuleProofs.smt_value_rel
                                                (__smtx_model_eval M
                                                  (__eo_to_smt (Term.Apply Term.set_singleton a)))
                                                (__smtx_model_eval M
                                                  (__eo_to_smt (Term.Apply Term.set_singleton b))) :=
                                            RuleProofs.eo_interprets_eq_rel M
                                              (Term.Apply Term.set_singleton a)
                                              (Term.Apply Term.set_singleton b)
                                              hPremTrue
                                          have hEvalEq :
                                              __smtx_model_eval M (__eo_to_smt b) =
                                                __smtx_model_eval M (__eo_to_smt a) :=
                                            singleton_term_rel_implies_eq M a b hSetRel
                                          simpa [__eo_prog_sets_singleton_inj] using
                                            RuleProofs.eo_interprets_eq_of_rel M a b hOutBool <| by
                                              rw [hEvalEq]
                                              exact RuleProofs.smt_value_rel_refl
                                                (__smtx_model_eval M (__eo_to_smt a))
                                      | _ =>
                                          simp [__eo_prog_sets_singleton_inj] at hProg
                                  | _ =>
                                      simp [__eo_prog_sets_singleton_inj] at hProg
                              | _ =>
                                  simp [__eo_prog_sets_singleton_inj] at hProg
                          | _ =>
                              simp [__eo_prog_sets_singleton_inj] at hProg
                      | _ =>
                          simp [__eo_prog_sets_singleton_inj] at hProg
                  | _ =>
                      simp [__eo_prog_sets_singleton_inj] at hProg
              | _ =>
                  simp [__eo_prog_sets_singleton_inj] at hProg
          | _ =>
              simp [__eo_prog_sets_singleton_inj] at hProg
      | _ =>
          simp [__eo_prog_sets_singleton_inj] at hProg
  | _ =>
      simp [__eo_prog_sets_singleton_inj] at hProg

public theorem cmd_step_sets_singleton_inj_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_singleton_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_singleton_inj args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_singleton_inj args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_singleton_inj args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgSingleton :
                  __eo_prog_sets_singleton_inj (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_sets_singleton_inj
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_sets_singleton_inj (Proof.pf X1)) true
                exact facts___eo_prog_sets_singleton_inj_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgSingleton
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_sets_singleton_inj (Proof.pf X1))
                    exact typed___eo_prog_sets_singleton_inj_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgSingleton)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
