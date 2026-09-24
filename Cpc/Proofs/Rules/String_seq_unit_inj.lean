module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Extracts non-`None` typing of a `seq_unit` argument from the application. -/
private theorem seq_unit_arg_non_none (x : Term) :
  __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit x)) ≠ SmtType.None ->
  __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hSeq hNone
  change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt x)) ≠ SmtType.None at hSeq
  have hSeqNone :
      __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt x)) = SmtType.None := by
    rw [smtx_typeof_seq_unit_term_eq]
    have hWfNone : __smtx_type_wf (SmtType.Seq SmtType.None) = false := by
      simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        SmtEval.native_and]
    rw [hNone]
    simp [__smtx_typeof_guard_wf, hWfNone, native_ite]
  exact hSeq hSeqNone

/-- Shows that the EO program for `string_seq_unit_inj` is well typed. -/
private theorem typed___eo_prog_string_seq_unit_inj_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_string_seq_unit_inj (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_string_seq_unit_inj (Proof.pf x1)) := by
  intro hXBool hProg
  cases x1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases a with
                  | Apply f1 a1 =>
                      cases f1 with
                      | UOp op1 =>
                          cases op1 with
                          | seq_unit =>
                              cases b with
                              | Apply f2 b1 =>
                                  cases f2 with
                                  | UOp op2 =>
                                      cases op2 with
                                      | seq_unit =>
                                          rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                              (Term.Apply Term.seq_unit a1)
                                              (Term.Apply Term.seq_unit b1) hXBool with
                                            ⟨hSeqTy, hSeqANonNone⟩
                                          have hSeqBNonNone :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit b1)) ≠
                                                SmtType.None := by
                                            rwa [← hSeqTy]
                                          have hANonNone :
                                              __smtx_typeof (__eo_to_smt a1) ≠ SmtType.None :=
                                            seq_unit_arg_non_none a1 hSeqANonNone
                                          have hBNonNone :
                                              __smtx_typeof (__eo_to_smt b1) ≠ SmtType.None :=
                                            seq_unit_arg_non_none b1 hSeqBNonNone
                                          have hArgTy :
                                              __smtx_typeof (__eo_to_smt a1) =
                                                __smtx_typeof (__eo_to_smt b1) := by
                                            have hSeqATy :
                                                __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit a1)) =
                                                  SmtType.Seq (__smtx_typeof (__eo_to_smt a1)) := by
                                              change
                                                __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt a1)) =
                                                  SmtType.Seq (__smtx_typeof (__eo_to_smt a1))
                                              rw [smtx_typeof_seq_unit_term_eq]
                                              exact smtx_typeof_guard_wf_of_non_none
                                                (SmtType.Seq (__smtx_typeof (__eo_to_smt a1)))
                                                (SmtType.Seq (__smtx_typeof (__eo_to_smt a1)))
                                                (by
                                                  change
                                                    __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt a1)) ≠
                                                      SmtType.None at hSeqANonNone
                                                  rwa [smtx_typeof_seq_unit_term_eq] at hSeqANonNone)
                                            have hSeqBTy :
                                                __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit b1)) =
                                                  SmtType.Seq (__smtx_typeof (__eo_to_smt b1)) := by
                                              change
                                                __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt b1)) =
                                                  SmtType.Seq (__smtx_typeof (__eo_to_smt b1))
                                              rw [smtx_typeof_seq_unit_term_eq]
                                              exact smtx_typeof_guard_wf_of_non_none
                                                (SmtType.Seq (__smtx_typeof (__eo_to_smt b1)))
                                                (SmtType.Seq (__smtx_typeof (__eo_to_smt b1)))
                                                (by
                                                  change
                                                    __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt b1)) ≠
                                                      SmtType.None at hSeqBNonNone
                                                  rwa [smtx_typeof_seq_unit_term_eq] at hSeqBNonNone)
                                            have hSeqTy' :
                                                SmtType.Seq (__smtx_typeof (__eo_to_smt a1)) =
                                                  SmtType.Seq (__smtx_typeof (__eo_to_smt b1)) := by
                                              rw [← hSeqATy, ← hSeqBTy]
                                              exact hSeqTy
                                            injection hSeqTy' with hArgTy
                                          simpa [__eo_prog_string_seq_unit_inj] using
                                            RuleProofs.eo_has_bool_type_eq_of_same_smt_type a1 b1
                                              hArgTy hANonNone
                                      | _ =>
                                          simp [__eo_prog_string_seq_unit_inj] at hProg
                                  | _ =>
                                      simp [__eo_prog_string_seq_unit_inj] at hProg
                              | _ =>
                                  simp [__eo_prog_string_seq_unit_inj] at hProg
                          | _ =>
                              simp [__eo_prog_string_seq_unit_inj] at hProg
                      | _ =>
                          simp [__eo_prog_string_seq_unit_inj] at hProg
                  | _ =>
                      simp [__eo_prog_string_seq_unit_inj] at hProg
              | _ =>
                  simp [__eo_prog_string_seq_unit_inj] at hProg
          | _ =>
              simp [__eo_prog_string_seq_unit_inj] at hProg
      | _ =>
          simp [__eo_prog_string_seq_unit_inj] at hProg
  | _ =>
      simp [__eo_prog_string_seq_unit_inj] at hProg

/-- Extracts head equality from equality of two `seq_unit` evaluations. -/
private theorem smt_value_rel_of_seq_unit_rel (M : SmtModel) (a b : Term) :
  RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.seq_unit a)))
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.seq_unit b))) ->
  RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hRel
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt a)))
    (__smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt b))) at hRel
  have hNotReg :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt a)) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt b)) = SmtValue.RegLan r2 := by
    intro hReg
    rcases hReg with ⟨r1, _r2, h1, _h2⟩
    rw [smtx_eval_seq_unit_term_eq] at h1
    simp at h1
  have hEq := (RuleProofs.smt_value_rel_iff_eq _ _ hNotReg).1 hRel
  rw [smtx_eval_seq_unit_term_eq, smtx_eval_seq_unit_term_eq] at hEq
  injection hEq with hSeq
  injection hSeq with hHead _hTail
  rw [hHead]
  exact RuleProofs.smt_value_rel_refl _

/-- Derives the checker facts exposed by the EO program for `string_seq_unit_inj`. -/
private theorem facts___eo_prog_string_seq_unit_inj_impl (M : SmtModel) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_string_seq_unit_inj (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_string_seq_unit_inj (Proof.pf x1)) true := by
  intro hXTrue hProg
  have hXBool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hXTrue
  have hOutBool :
      RuleProofs.eo_has_bool_type (__eo_prog_string_seq_unit_inj (Proof.pf x1)) :=
    typed___eo_prog_string_seq_unit_inj_impl x1 hXBool hProg
  cases x1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases a with
                  | Apply f1 a1 =>
                      cases f1 with
                      | UOp op1 =>
                          cases op1 with
                          | seq_unit =>
                              cases b with
                              | Apply f2 b1 =>
                                  cases f2 with
                                  | UOp op2 =>
                                      cases op2 with
                                      | seq_unit =>
                                          have hRelSeq :
                                              RuleProofs.smt_value_rel
                                                (__smtx_model_eval M
                                                  (__eo_to_smt (Term.Apply Term.seq_unit a1)))
                                                (__smtx_model_eval M
                                                  (__eo_to_smt (Term.Apply Term.seq_unit b1))) :=
                                            RuleProofs.eo_interprets_eq_rel M
                                              (Term.Apply Term.seq_unit a1)
                                              (Term.Apply Term.seq_unit b1) hXTrue
                                          have hRelArgs :
                                              RuleProofs.smt_value_rel
                                                (__smtx_model_eval M (__eo_to_smt a1))
                                                (__smtx_model_eval M (__eo_to_smt b1)) :=
                                            smt_value_rel_of_seq_unit_rel M a1 b1 hRelSeq
                                          simpa [__eo_prog_string_seq_unit_inj] using
                                            RuleProofs.eo_interprets_eq_of_rel M a1 b1 hOutBool hRelArgs
                                      | _ =>
                                          simp [__eo_prog_string_seq_unit_inj] at hProg
                                  | _ =>
                                      simp [__eo_prog_string_seq_unit_inj] at hProg
                              | _ =>
                                  simp [__eo_prog_string_seq_unit_inj] at hProg
                          | _ =>
                              simp [__eo_prog_string_seq_unit_inj] at hProg
                      | _ =>
                          simp [__eo_prog_string_seq_unit_inj] at hProg
                  | _ =>
                      simp [__eo_prog_string_seq_unit_inj] at hProg
              | _ =>
                  simp [__eo_prog_string_seq_unit_inj] at hProg
          | _ =>
              simp [__eo_prog_string_seq_unit_inj] at hProg
      | _ =>
          simp [__eo_prog_string_seq_unit_inj] at hProg
  | _ =>
      simp [__eo_prog_string_seq_unit_inj] at hProg

public theorem cmd_step_string_seq_unit_inj_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_seq_unit_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_seq_unit_inj args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_seq_unit_inj args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_seq_unit_inj args premises ≠ Term.Stuck :=
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
              have hProgSeqUnitInj' :
                  __eo_prog_string_seq_unit_inj
                    (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck := by
                change __eo_prog_string_seq_unit_inj
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                exact hProg
              let X1 := __eo_state_proven_nth s n1
              have hProgSeqUnitInj :
                  __eo_prog_string_seq_unit_inj (Proof.pf X1) ≠ Term.Stuck := by
                simpa [X1] using hProgSeqUnitInj'
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_string_seq_unit_inj (Proof.pf X1)) true
                exact facts___eo_prog_string_seq_unit_inj_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgSeqUnitInj
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_string_seq_unit_inj (Proof.pf X1))
                    exact typed___eo_prog_string_seq_unit_inj_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgSeqUnitInj)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
