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
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev replacePrefixTail (t2 r : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat t2) r

private abbrev replacePrefixHaystack (t1 t2 r : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat t1) (replacePrefixTail t2 r)

private abbrev replacePrefixLhs (t1 t2 r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace (replacePrefixHaystack t1 t2 r))
    t1) s

private abbrev replacePrefixRhs (t2 r s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s) (replacePrefixTail t2 r)

private abbrev replacePrefixConclusion (t1 t2 r s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replacePrefixLhs t1 t2 r s))
    (replacePrefixRhs t2 r s)

private theorem eo_typeof_str_concat_args_seq
    (A B U : Term)
    (h : __eo_typeof_str_concat A B = Term.Apply Term.Seq U) :
    A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_concat, Term.Seq] at h ⊢
  case Apply fA xA =>
    cases fA <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp opA =>
      cases opA <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply fB xB =>
          cases fB <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opB =>
            cases opB <;> simp [__eo_typeof_str_concat, Term.Seq] at h ⊢
            case Seq =>
              have hNe : __eo_requires (__eo_eq xA xB) (Term.Boolean true)
                  (Term.Apply Term.Seq xA) ≠ Term.Stuck := by
                rw [h]
                simp [Term.Seq]
              have hRes : Term.Apply Term.Seq xA = Term.Apply Term.Seq U := by
                rw [← eo_requires_eq_result_of_ne_stuck (__eo_eq xA xB)
                  (Term.Boolean true) (Term.Apply Term.Seq xA) hNe]
                exact h
              have hxAU : xA = U := (Term.Apply.inj hRes).2
              have hCond : __eo_eq xA xB = Term.Boolean true :=
                eo_requires_eq_of_ne_stuck (__eo_eq xA xB) (Term.Boolean true)
                  (Term.Apply Term.Seq xA) hNe
              have hxBA : xB = xA := RuleProofs.eq_of_eo_eq_true xA xB hCond
              exact ⟨by rw [hxAU], by rw [hxBA, hxAU]⟩

private theorem eo_typeof_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case Apply g y =>
          cases g <;> simp at h ⊢
          case UOp opg =>
            cases opg <;> simp at h ⊢
            case Seq =>
              cases C <;> simp at h ⊢
              case Apply k z =>
                cases k <;> simp at h ⊢
                case UOp opk =>
                  cases opk <;> simp at h ⊢
                  case Seq =>
                    have hEq := RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                      x x y z (Term.Apply Term.Seq x) h
                    exact hEq

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

private theorem native_seq_prefix_eq_append
    (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil =>
      simp [native_seq_prefix_eq]
  | cons p ps ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

private theorem native_seq_indexof_prefix_zero
    (pat rest : List SmtValue) :
    native_seq_indexof (pat ++ rest) pat 0 = 0 := by
  unfold native_seq_indexof
  have hBounds : pat.length ≤ (pat ++ rest).length := by
    simp
  simp [hBounds]
  unfold native_seq_indexof_rec
  simp [native_seq_prefix_eq_append]

private theorem native_seq_replace_prefix
    (pre rest repl : List SmtValue) :
    native_seq_replace (pre ++ rest) pre repl = repl ++ rest := by
  cases pre with
  | nil =>
      simp [native_seq_replace]
  | cons p ps =>
      have hIdx := native_seq_indexof_prefix_zero (p :: ps) rest
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      rw [hIdx]
      simp

private theorem smtx_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem prog_str_replace_prefix_eq
    (t1 t2 r s : Term)
    (hT1 : t1 ≠ Term.Stuck) (hT2 : t2 ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck) (hS : s ≠ Term.Stuck) :
    __eo_prog_str_replace_prefix t1 t2 r s =
      replacePrefixConclusion t1 t2 r s := by
  have hRaw :
      __eo_prog_str_replace_prefix t1 t2 r s =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.str_replace
                  (Term.Apply (Term.Apply Term.str_concat t1)
                    (Term.Apply (Term.Apply Term.str_concat t2) r)))
                t1) s))
          (Term.Apply (Term.Apply Term.str_concat s)
            (Term.Apply (Term.Apply Term.str_concat t2) r)) := by
    unfold __eo_prog_str_replace_prefix
    split
    · exact False.elim (hT1 rfl)
    · exact False.elim (hT2 rfl)
    · exact False.elim (hR rfl)
    · exact False.elim (hS rfl)
    · rfl
  simpa [replacePrefixConclusion, replacePrefixLhs, replacePrefixRhs,
    replacePrefixHaystack, replacePrefixTail] using hRaw

private theorem typed___eo_prog_str_replace_prefix_impl
    (t1 t2 r s : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hT2Trans : RuleProofs.eo_has_smt_translation t2)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hT1Ty : __eo_typeof t1 = Term.Apply Term.Seq T)
    (hT2Ty : __eo_typeof t2 = Term.Apply Term.Seq T)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_replace_prefix t1 t2 r s) := by
  let lhs := replacePrefixLhs t1 t2 r s
  let rhs := replacePrefixRhs t2 r s
  have hT1SmtTy := smtx_typeof_of_eo_seq t1 T hT1Trans hT1Ty
  have hT2SmtTy := smtx_typeof_of_eo_seq t2 T hT2Trans hT2Ty
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTailSmtTy :
      __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hT2SmtTy, hRSmtTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hTailTy :
      __smtx_typeof (__eo_to_smt (replacePrefixTail t2 r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [replacePrefixTail] using hTailSmtTy
  have hHaystackSmtTy :
      __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt t1)
          (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r))) =
      SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hT1SmtTy, hTailSmtTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hHaystackTy :
      __smtx_typeof (__eo_to_smt (replacePrefixHaystack t1 t2 r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [replacePrefixHaystack, replacePrefixTail] using hHaystackSmtTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace
          (SmtTerm.str_concat (__eo_to_smt t1)
            (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r)))
          (__eo_to_smt t1) (__eo_to_smt s)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hHaystackSmtTy, hT1SmtTy, hSSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s)
          (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hSSmtTy, hTailSmtTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (replacePrefixConclusion t1 t2 r s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hRNotStuck : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hSNotStuck : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  rw [prog_str_replace_prefix_eq t1 t2 r s hT1NotStuck hT2NotStuck hRNotStuck
    hSNotStuck]
  exact hBoolEq

private theorem facts___eo_prog_str_replace_prefix_impl
    (M : SmtModel) (hM : model_wf M) (t1 t2 r s : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hT2Trans : RuleProofs.eo_has_smt_translation t2)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hT1Ty : __eo_typeof t1 = Term.Apply Term.Seq T)
    (hT2Ty : __eo_typeof t2 = Term.Apply Term.Seq T)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_replace_prefix t1 t2 r s) true := by
  let lhs := replacePrefixLhs t1 t2 r s
  let rhs := replacePrefixRhs t2 r s
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hRNotStuck : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hSNotStuck : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProg :
      __eo_prog_str_replace_prefix t1 t2 r s =
        replacePrefixConclusion t1 t2 r s :=
    prog_str_replace_prefix_eq t1 t2 r s hT1NotStuck hT2NotStuck
      hRNotStuck hSNotStuck
  have hBoolEq :
      RuleProofs.eo_has_bool_type (replacePrefixConclusion t1 t2 r s) := by
    simpa [hProg] using
      typed___eo_prog_str_replace_prefix_impl t1 t2 r s hT1Trans hT2Trans
        hRTrans hSTrans hT1Ty hT2Ty hRTy hSTy
  have hT1SmtTy := smtx_typeof_of_eo_seq t1 T hT1Trans hT1Ty
  have hT2SmtTy := smtx_typeof_of_eo_seq t2 T hT2Trans hT2Ty
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hT1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hT1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1) (by
        unfold term_has_non_none_type
        rw [hT1SmtTy]
        simp)
  have hT2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hT2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2) (by
        unfold term_has_non_none_type
        rw [hT2SmtTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  rcases seq_value_canonical hT1EvalTy with ⟨ts1, hT1Eval⟩
  rcases seq_value_canonical hT2EvalTy with ⟨ts2, hT2Eval⟩
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hT1SeqTy :
      __smtx_typeof_seq_value ts1 = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hT1Eval] using hT1EvalTy
  have hT2SeqTy :
      __smtx_typeof_seq_value ts2 = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hT2Eval] using hT2EvalTy
  have hRSeqTy :
      __smtx_typeof_seq_value rs = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hREval] using hREvalTy
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hT1Elem : __smtx_elem_typeof_seq_value ts1 = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hT1SeqTy
  have hT2Elem : __smtx_elem_typeof_seq_value ts2 = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hT2SeqTy
  have hRElem : __smtx_elem_typeof_seq_value rs = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hRSeqTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace
          (SmtTerm.str_concat (__eo_to_smt t1)
            (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r)))
          (__eo_to_smt t1) (__eo_to_smt s)) =
      __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s)
          (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r)))
    rw [smtx_eval_str_replace_term_eq]
    rw [smtx_eval_str_concat_term_eq M (__eo_to_smt t1)
      (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r))]
    rw [smtx_eval_str_concat_term_eq M (__eo_to_smt t2) (__eo_to_smt r)]
    rw [smtx_eval_str_concat_term_eq M (__eo_to_smt s)
      (SmtTerm.str_concat (__eo_to_smt t2) (__eo_to_smt r))]
    rw [smtx_eval_str_concat_term_eq M (__eo_to_smt t2) (__eo_to_smt r)]
    rw [hT1Eval, hT2Eval, hREval, hSEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_concat,
      native_seq_concat, native_seq_replace_prefix, Smtm.native_unpack_pack_seq,
      elem_typeof_pack_seq, hT1Elem, hT2Elem, hRElem, hSElem]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_prefix_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_prefix args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_prefix args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_prefix args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_prefix args premises ≠
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
                          have hA4Trans : RuleProofs.eo_has_smt_translation a4 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.2.1
                          have hA1NotStuck : a1 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                          have hA2NotStuck : a2 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                          have hA3NotStuck : a3 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a3 hA3Trans
                          have hA4NotStuck : a4 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a4 hA4Trans
                          let lhs := replacePrefixLhs a1 a2 a3 a4
                          let rhs := replacePrefixRhs a2 a3 a4
                          have hProgEq :
                              __eo_cmd_step_proven s CRule.str_replace_prefix
                                (CArgList.cons a1 (CArgList.cons a2
                                  (CArgList.cons a3 (CArgList.cons a4 CArgList.nil))))
                                CIndexList.nil =
                                replacePrefixConclusion a1 a2 a3 a4 := by
                            change __eo_prog_str_replace_prefix a1 a2 a3 a4 =
                              replacePrefixConclusion a1 a2 a3 a4
                            exact prog_str_replace_prefix_eq a1 a2 a3 a4
                              hA1NotStuck hA2NotStuck hA3NotStuck hA4NotStuck
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Apply Term.Seq T ∧
                                __eo_typeof a4 = Term.Apply Term.Seq T := by
                            change __eo_typeof_str_replace
                              (__eo_typeof (replacePrefixHaystack a1 a2 a3))
                              (__eo_typeof a1) (__eo_typeof a4) ≠ Term.Stuck
                              at hLhsNotStuck
                            rcases eo_typeof_str_replace_args_of_ne_stuck
                                (__eo_typeof (replacePrefixHaystack a1 a2 a3))
                                (__eo_typeof a1) (__eo_typeof a4) hLhsNotStuck with
                              ⟨T, hHaystackTy, hA1Ty, hA4Ty⟩
                            change __eo_typeof_str_concat (__eo_typeof a1)
                                (__eo_typeof (replacePrefixTail a2 a3)) =
                              Term.Apply Term.Seq T at hHaystackTy
                            obtain ⟨hA1Ty', hTailTy⟩ :=
                              eo_typeof_str_concat_args_seq _ _ T hHaystackTy
                            change __eo_typeof_str_concat (__eo_typeof a2)
                                (__eo_typeof a3) =
                              Term.Apply Term.Seq T at hTailTy
                            obtain ⟨hA2Ty, hA3Ty⟩ :=
                              eo_typeof_str_concat_args_seq _ _ T hTailTy
                            exact ⟨T, hA1Ty', hA2Ty, hA3Ty, hA4Ty⟩
                          rcases hArgTypes with
                            ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                          have hProps :
                              StepRuleProperties M (premiseTermList s CIndexList.nil)
                                (__eo_prog_str_replace_prefix a1 a2 a3 a4) := by
                            refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_replace_prefix_impl a1 a2 a3 a4
                                hA1Trans hA2Trans hA3Trans hA4Trans
                                hA1Ty hA2Ty hA3Ty hA4Ty)⟩
                            intro _hTrue
                            exact facts___eo_prog_str_replace_prefix_impl M hM a1 a2
                              a3 a4 hA1Trans hA2Trans hA3Trans hA4Trans
                              hA1Ty hA2Ty hA3Ty hA4Ty
                          change StepRuleProperties M []
                            (__eo_prog_str_replace_prefix a1 a2 a3 a4)
                          simpa [premiseTermList] using hProps
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
