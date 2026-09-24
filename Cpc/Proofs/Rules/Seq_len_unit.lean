module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem smtx_eval_seq_unit_term_eq'
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_unit x) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M x)
          (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M x)))) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem seq_unit_smt_type
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt a1)) =
      SmtType.Seq (__smtx_typeof (__eo_to_smt a1)) := by
  have hSeqWf :
      __smtx_type_wf (SmtType.Seq (__smtx_typeof (__eo_to_smt a1))) = true :=
    type_wf_seq_of_component (__smtx_typeof (__eo_to_smt a1)) hWf
  rw [smtx_typeof_seq_unit_term_eq]
  simp [__smtx_typeof_guard_wf, hSeqWf, native_ite]

private theorem a1_trans_of_wfElem
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    RuleProofs.eo_has_smt_translation a1 := by
  unfold RuleProofs.eo_has_smt_translation
  intro hNone
  rw [hNone] at hWf
  simp [__smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

private theorem typed___eo_prog_seq_len_unit_impl
    (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    RuleProofs.eo_has_bool_type (__eo_prog_seq_len_unit a1) := by
  have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
    a1_trans_of_wfElem a1 hWf
  have hA1NotStuck : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
  let lhs := Term.Apply Term.str_len (Term.Apply Term.seq_unit a1)
  let rhs := Term.Numeral 1
  have hUnitTy := seq_unit_smt_type a1 hWf
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_len (SmtTerm.seq_unit (__eo_to_smt a1))) = SmtType.Int
    rw [typeof_str_len_eq, hUnitTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral 1) = SmtType.Int
    rw [__smtx_typeof.eq_def] <;> simp only
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hProg :
      __eo_prog_seq_len_unit a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_seq_len_unit a1 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_len (Term.Apply Term.seq_unit a1)))
            (Term.Numeral 1) := by
      cases a1 <;> simp [__eo_prog_seq_len_unit] at hA1NotStuck ⊢
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_seq_len_unit_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term)
    (hWf : __smtx_type_wf_component (__smtx_typeof (__eo_to_smt a1)) = true) :
    eo_interprets M (__eo_prog_seq_len_unit a1) true := by
  have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
    a1_trans_of_wfElem a1 hWf
  have hA1NotStuck : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
  let lhs := Term.Apply Term.str_len (Term.Apply Term.seq_unit a1)
  let rhs := Term.Numeral 1
  have hProg :
      __eo_prog_seq_len_unit a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_seq_len_unit a1 =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_len (Term.Apply Term.seq_unit a1)))
            (Term.Numeral 1) := by
      cases a1 <;> simp [__eo_prog_seq_len_unit] at hA1NotStuck ⊢
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using typed___eo_prog_seq_len_unit_impl a1 hWf
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_len (SmtTerm.seq_unit (__eo_to_smt a1))) =
      __smtx_model_eval M (SmtTerm.Numeral 1)
    rw [smtx_eval_str_len_term_eq, smtx_eval_seq_unit_term_eq']
    change __smtx_model_eval_str_len
        (SmtValue.Seq
          (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt a1))
            (SmtSeq.empty
              (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)))))) =
      __smtx_model_eval M (SmtTerm.Numeral 1)
    simp [__smtx_model_eval_str_len, native_seq_len, native_unpack_seq,
      __smtx_model_eval]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_seq_len_unit_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_len_unit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_len_unit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_len_unit args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.seq_len_unit args premises ≠
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
              have hWf :
                  __smtx_type_wf_component
                      (__smtx_typeof (__eo_to_smt a1)) = true := by
                have hMask :
                    argTranslationOkMasked ArgTranslationKind.wfElem a1 ∧ True := by
                  simpa [cmdTranslationOk, cArgListTranslationOkMask] using hCmdTrans
                simpa [argTranslationOkMasked] using hMask.1
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_seq_len_unit a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_seq_len_unit_impl a1 hWf)⟩
                intro _hTrue
                exact facts___eo_prog_seq_len_unit_impl M hM a1 hWf
              change StepRuleProperties M [] (__eo_prog_seq_len_unit a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
