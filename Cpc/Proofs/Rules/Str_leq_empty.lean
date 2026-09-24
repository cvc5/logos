module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_lt_args_of_ne_stuck
    (T U : Term)
    (h : __eo_typeof_str_lt T U ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char ∧ U = Term.Apply Term.Seq Term.Char := by
  cases T <;> simp [__eo_typeof_str_lt] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases x <;> simp at h ⊢
        case UOp opx =>
          cases opx <;> simp at h ⊢
          case Char =>
            cases U <;> simp [__eo_typeof_str_lt] at h ⊢
            case Apply g y =>
              cases g <;> simp at h ⊢
              case UOp opg =>
                cases opg <;> simp at h ⊢
                case Seq =>
                  cases y <;> simp at h ⊢
                  case UOp opy =>
                    cases opy <;> simp at h ⊢

private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  have hCharNN : __eo_to_smt_type Term.Char ≠ SmtType.None := by decide
  simpa [TranslationProofs.eo_to_smt_type_char] using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type Term.Char) (SmtType.Seq (__eo_to_smt_type Term.Char))
      hCharNN)

private theorem smtx_eval_str_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_leq x y) =
      __smtx_model_eval_str_leq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem prog_str_leq_empty_eq_of_ne_stuck (s : Term)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_str_leq_empty s =
      Term.Apply
        (Term.Apply Term.eq
          (Term.Apply (Term.Apply Term.str_leq (Term.String [])) s))
        (Term.Boolean true) := by
  cases hS : s <;> first
    | exact False.elim (hs hS)
    | rfl

private theorem eo_has_bool_type_str_leq_of_seq_char (s t : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.str_leq s) t) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.str_leq (__eo_to_smt s) (__eo_to_smt t)) =
    SmtType.Bool
  rw [typeof_str_leq_eq]
  simp [hsTy, htTy, native_ite, native_Teq]

private theorem smtx_typeof_empty_string :
    __smtx_typeof (__eo_to_smt (Term.String [])) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.String []) = SmtType.Seq SmtType.Char
  rw [__smtx_typeof.eq_def]
  have hValid : native_string_valid ([] : native_String) = true := rfl
  simp [hValid, native_ite]

private theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [impl_native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

private theorem native_pack_string_unpack_string_of_typeof_seq_char
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  unfold native_pack_string native_unpack_string
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) =
    ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq ss

private theorem smtx_model_eval_str_leq_empty_pack_string
    (t : native_String) :
    __smtx_model_eval_str_leq
        (SmtValue.Seq (native_pack_string []))
        (SmtValue.Seq (native_pack_string t)) =
      SmtValue.Boolean true := by
  cases t with
  | nil =>
      simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
        __smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
        native_str_lt, native_pack_string, native_pack_seq,
        native_unpack_string, native_unpack_seq, SmtEval.native_or]
  | cons c cs =>
      simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
        __smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
        native_str_lt, native_pack_string, native_pack_seq,
        native_unpack_string, native_unpack_seq, SmtEval.native_or]

private theorem typed___eo_prog_str_leq_empty_impl
    (s : Term)
    (hsTrans : RuleProofs.eo_has_smt_translation s)
    (hsTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_leq_empty s) := by
  have hsSmtTy := smtx_typeof_of_eo_seq_char s hsTrans hsTy
  have hsNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hsTrans
  rw [prog_str_leq_empty_eq_of_ne_stuck s hsNotStuck]
  have hLeq := eo_has_bool_type_str_leq_of_seq_char (Term.String []) s
    smtx_typeof_empty_string hsSmtTy
  have hTrueTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLeq, hTrueTy]) (by rw [hLeq]; simp)

private theorem facts___eo_prog_str_leq_empty_impl
    (M : SmtModel) (hM : model_wf M) (s : Term)
    (hsTrans : RuleProofs.eo_has_smt_translation s)
    (hsTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_str_leq_empty s) true := by
  let lhs := Term.Apply (Term.Apply Term.str_leq (Term.String [])) s
  let rhs := Term.Boolean true
  have hsNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hsTrans
  have hProgEq :
      __eo_prog_str_leq_empty s =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [lhs, rhs] using prog_str_leq_empty_eq_of_ne_stuck s hsNotStuck
  have hProgBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq] using
      typed___eo_prog_str_leq_empty_impl s hsTrans hsTy
  have hsSmtTy := smtx_typeof_of_eo_seq_char s hsTrans hsTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hsSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hsSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hSEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hSEvalTy
  have hPack : native_pack_string (native_unpack_string ss) = ss :=
    native_pack_string_unpack_string_of_typeof_seq_char ss hSeqTy
  rw [hProgEq]
  apply RuleProofs.eo_interprets_eq_of_rel M lhs rhs hProgBool
  change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.str_leq (SmtTerm.String []) (__eo_to_smt s)))
      (__smtx_model_eval M (SmtTerm.Boolean true))
  rw [smtx_eval_str_leq_term_eq, smtx_eval_boolean_term_eq, hSEval]
  rw [show __smtx_model_eval M (SmtTerm.String []) =
      SmtValue.Seq (native_pack_string []) by
    rw [__smtx_model_eval.eq_def]]
  rw [← hPack]
  rw [smtx_model_eval_str_leq_empty_pack_string]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_str_leq_empty_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_leq_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_empty args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_leq_empty args premises ≠
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              have hA1NotStuck : a1 ≠ Term.Stuck := by
                intro hStuck
                subst a1
                apply hProg
                rfl
              have hProgEq :
                  __eo_cmd_step_proven s CRule.str_leq_empty
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                    Term.Apply
                      (Term.Apply Term.eq
                        (Term.Apply (Term.Apply Term.str_leq (Term.String [])) a1))
                      (Term.Boolean true) := by
                change __eo_prog_str_leq_empty a1 = _
                exact prog_str_leq_empty_eq_of_ne_stuck a1 hA1NotStuck
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq
                  (__eo_typeof
                    (Term.Apply (Term.Apply Term.str_leq (Term.String [])) a1))
                  (__eo_typeof (Term.Boolean true)) = Term.Bool
                at hResultTy
              have hLeqNotStuck :
                  __eo_typeof
                    (Term.Apply (Term.Apply Term.str_leq (Term.String [])) a1) ≠
                    Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
                  hResultTy).1
              have hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                change __eo_typeof_str_lt (__eo_typeof (Term.String []))
                    (__eo_typeof a1) ≠ Term.Stuck at hLeqNotStuck
                exact (eo_typeof_str_lt_args_of_ne_stuck _ _ hLeqNotStuck).2
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_str_leq_empty a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_str_leq_empty_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_str_leq_empty_impl M hM a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_str_leq_empty a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
