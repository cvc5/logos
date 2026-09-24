module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_replace_self_args_of_ne_stuck
    (T U : Term)
    (h : __eo_typeof_str_replace T T U ≠ Term.Stuck) :
    ∃ V, T = Term.Apply Term.Seq V ∧ U = Term.Apply Term.Seq V := by
  cases T <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases U <;> simp at h ⊢
        case Apply g y =>
          cases g <;> simp at h ⊢
          case UOp opg =>
            cases opg <;> simp at h ⊢
            case Seq =>
              have hEq :=
                RuleProofs.eqs_of_requires_and_eq_true_not_stuck x x x y
                  (Term.Apply Term.Seq x) h
              exact hEq.2

private theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

private theorem native_seq_replace_self
    (xs repl : List SmtValue) :
    native_seq_replace xs xs repl = repl := by
  cases xs with
  | nil =>
      simp [native_seq_replace]
  | cons x xs =>
      simp [native_seq_replace, native_seq_indexof_self_zero]

private theorem smtx_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem typed___eo_prog_str_replace_self_impl
    (t repl : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_replace_self t repl) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_replace t) t) repl
  let rhs := repl
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hReplSmtTy := smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt t)
          (__eo_to_smt repl)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hTSmtTy, hReplSmtTy, __smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hReplSmtTy]) (by rw [hLhsTy]; simp)
  have hTNotStuck : t ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hReplNotStuck : repl ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation repl hReplTrans
  have hProg :
      __eo_prog_str_replace_self t repl =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_replace_self t repl =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_replace t) t) repl))
            repl := by
      cases ht : t <;> cases hr : repl <;> first
        | exact False.elim (hTNotStuck ht)
        | exact False.elim (hReplNotStuck hr)
        | rfl
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_replace_self_impl
    (M : SmtModel) (hM : model_wf M) (t repl : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_replace_self t repl) true := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_replace t) t) repl
  let rhs := repl
  have hTNotStuck : t ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hReplNotStuck : repl ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation repl hReplTrans
  have hProg :
      __eo_prog_str_replace_self t repl =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_replace_self t repl =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_replace t) t) repl))
            repl := by
      cases ht : t <;> cases hr : repl <;> first
        | exact False.elim (hTNotStuck ht)
        | exact False.elim (hReplNotStuck hr)
        | rfl
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_replace_self_impl t repl hTTrans hReplTrans hTTy hReplTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hReplSmtTy := smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hReplEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hReplSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨replSeq, hReplEval⟩
  have hTSeqTy :
      __smtx_typeof_seq_value ts = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hTEval] using hTEvalTy
  have hReplSeqTy :
      __smtx_typeof_seq_value replSeq = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hReplEval] using hReplEvalTy
  have hTElem : __smtx_elem_typeof_seq_value ts = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hReplElem : __smtx_elem_typeof_seq_value replSeq = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hReplSeqTy
  have hPack :
      native_pack_seq (__smtx_elem_typeof_seq_value ts)
          (native_unpack_seq replSeq) =
        replSeq := by
    rw [hTElem, ← hReplElem]
    exact native_pack_unpack_seq replSeq
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt t)
          (__eo_to_smt repl)) =
      __smtx_model_eval M (__eo_to_smt repl)
    rw [smtx_eval_str_replace_term_eq]
    rw [hTEval, hReplEval]
    simp [__smtx_model_eval_str_replace, native_seq_replace_self, hPack]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_self args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    intro hStuck
                    subst a1
                    apply hProg
                    rfl
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    intro hStuck
                    subst a2
                    apply hProg
                    cases a1 <;> rfl
                  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_replace a1) a1) a2
                  let rhs := a2
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_replace_self
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply (Term.Apply Term.eq lhs) rhs := by
                    have hProgEqRaw :
                        __eo_cmd_step_proven s CRule.str_replace_self
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                          Term.Apply
                            (Term.Apply Term.eq
                              (Term.Apply
                                (Term.Apply (Term.Apply Term.str_replace a1) a1)
                                a2))
                            a2 := by
                      cases hA1 : a1 <;> cases hA2 : a2 <;> first
                        | exact False.elim (hA1NotStuck hA1)
                        | exact False.elim (hA2NotStuck hA2)
                        | rfl
                    simpa [lhs, rhs] using hProgEqRaw
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                    Term.Bool at hResultTy
                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                  have hArgTypes :
                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                        __eo_typeof a2 = Term.Apply Term.Seq T := by
                    change __eo_typeof_str_replace (__eo_typeof a1) (__eo_typeof a1)
                      (__eo_typeof a2) ≠ Term.Stuck at hLhsNotStuck
                    exact eo_typeof_str_replace_self_args_of_ne_stuck
                      (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                  rcases hArgTypes with ⟨T, hA1Ty, hA2Ty⟩
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_replace_self a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_str_replace_self_impl a1 a2 hA1Trans hA2Trans
                        hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact facts___eo_prog_str_replace_self_impl M hM a1 a2
                      hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M [] (__eo_prog_str_replace_self a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
