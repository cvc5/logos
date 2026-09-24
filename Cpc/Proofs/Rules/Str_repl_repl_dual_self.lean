module

public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev replDualSelfInner (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) x

private abbrev replDualSelfLhs (x y : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply Term.str_replace x) (replDualSelfInner x y)) x

private abbrev replDualSelfConclusion (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replDualSelfLhs x y)) x

private theorem prog_str_repl_repl_dual_self_eq
    (x y : Term) (hX : x ≠ Term.Stuck) (hY : y ≠ Term.Stuck) :
    __eo_prog_str_repl_repl_dual_self x y =
      replDualSelfConclusion x y := by
  unfold __eo_prog_str_repl_repl_dual_self
  split
  · contradiction
  · contradiction
  · rfl

private theorem typed___eo_prog_str_repl_repl_dual_self_impl
    (x y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_repl_repl_dual_self x y) := by
  let inner := replDualSelfInner x y
  let lhs := replDualSelfLhs x y
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hInnerTy :
      __smtx_typeof (__eo_to_smt inner) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_3, native_ite,
      native_Teq]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt x))
          (__eo_to_smt x)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq, typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_3, native_ite,
      native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (replDualSelfConclusion x y) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs x
      (by rw [hLhsTy, hXSmtTy]) (by rw [hLhsTy]; simp)
  have hXNN := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNN := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  rw [prog_str_repl_repl_dual_self_eq x y hXNN hYNN]
  exact hBool

private theorem facts___eo_prog_str_repl_repl_dual_self_impl
    (M : SmtModel) (hM : model_wf M)
    (x y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_repl_repl_dual_self x y) true := by
  let lhs := replDualSelfLhs x y
  have hXNN := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNN := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hProgEq := prog_str_repl_repl_dual_self_eq x y hXNN hYNN
  have hBool : RuleProofs.eo_has_bool_type
      (replDualSelfConclusion x y) := by
    simpa [hProgEq] using
      typed___eo_prog_str_repl_repl_dual_self_impl
        x y hXTrans hYTrans hXTy hYTy
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt x) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt x))
          (__eo_to_smt x)) =
      __smtx_model_eval M (__eo_to_smt x)
    rw [smtx_eval_str_replace_term_eq, smtx_eval_str_replace_term_eq,
      hXEval, hYEval]
    simp [__smtx_model_eval_str_replace, Smtm.native_unpack_pack_seq,
      native_seq_replace_dual_self, native_pack_unpack_seq]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs x hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt x))

public theorem cmd_step_str_repl_repl_dual_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_dual_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_repl_repl_dual_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_dual_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_repl_repl_dual_self args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | cons _ _ => exact absurd rfl hProg
          | nil =>
              cases premises with
              | cons _ _ => exact absurd rfl hProg
              | nil =>
                  have hA1Trans :
                      RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk]
                      using hCmdTrans.1
                  have hA2Trans :
                      RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk]
                      using hCmdTrans.2.1
                  have hA1NN :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hA2NN :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                  change __eo_typeof
                      (__eo_prog_str_repl_repl_dual_self a1 a2) =
                    Term.Bool at hResultTy
                  have hProgEq :=
                    prog_str_repl_repl_dual_self_eq a1 a2 hA1NN hA2NN
                  rw [hProgEq] at hResultTy
                  have hLhsNN :
                      __eo_typeof (replDualSelfLhs a1 a2) ≠
                        Term.Stuck := by
                    change __eo_typeof_eq
                        (__eo_typeof (replDualSelfLhs a1 a2))
                        (__eo_typeof a1) = Term.Bool at hResultTy
                    exact
                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                        (__eo_typeof (replDualSelfLhs a1 a2))
                        (__eo_typeof a1) hResultTy).1
                  change __eo_typeof_str_replace
                      (__eo_typeof a1)
                      (__eo_typeof (replDualSelfInner a1 a2))
                      (__eo_typeof a1) ≠
                    Term.Stuck at hLhsNN
                  rcases eo_typeof_str_replace_args_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof (replDualSelfInner a1 a2))
                      (__eo_typeof a1) hLhsNN with
                    ⟨T, hA1Ty, hInnerTy, _hA1Ty'⟩
                  have hInnerNN :
                      __eo_typeof (replDualSelfInner a1 a2) ≠
                        Term.Stuck := by
                    rw [hInnerTy]
                    simp
                  change __eo_typeof_str_replace
                      (__eo_typeof a1) (__eo_typeof a2)
                      (__eo_typeof a1) ≠
                    Term.Stuck at hInnerNN
                  rcases eo_typeof_str_replace_args_of_ne_stuck
                      (__eo_typeof a1) (__eo_typeof a2)
                      (__eo_typeof a1) hInnerNN with
                    ⟨U, hA1Ty', hA2Ty, _hA1Ty''⟩
                  rw [hA1Ty] at hA1Ty'
                  cases hA1Ty'
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    exact facts___eo_prog_str_repl_repl_dual_self_impl
                      M hM a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
                  · exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type _
                        (typed___eo_prog_str_repl_repl_dual_self_impl
                          a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty)
