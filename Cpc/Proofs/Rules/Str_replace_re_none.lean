module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.SmtModel

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_replace_re_args_of_ne_stuck
    (T R U : Term)
    (h : __eo_typeof_str_replace_re T R U ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char ∧ R = Term.RegLan ∧
      U = Term.Apply Term.Seq Term.Char := by
  cases T <;> simp [__eo_typeof_str_replace_re] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases x <;> simp at h ⊢
        case UOp opx =>
          cases opx <;> simp at h ⊢
          cases R <;> simp at h ⊢
          case UOp opr =>
            cases opr <;> simp at h ⊢
            case RegLan =>
              cases U <;> simp at h ⊢
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
  exact hTyRaw

private theorem native_re_prefix_match_len_go_none :
    ∀ (xs : List SmtValue) (n : Nat),
      impl_native_re_prefix_match_len_go native_re_none xs n = none
  | [], n => by
      rw [impl_native_re_prefix_match_len_go.eq_1]
      simp [native_re_none, native_re_nullable]
  | c :: cs, n => by
      rw [impl_native_re_prefix_match_len_go.eq_2]
      simp [native_re_none, native_re_nullable, native_re_deriv]
      exact native_re_prefix_match_len_go_none cs (n + 1)

private theorem native_re_prefix_match_len_none (xs : List SmtValue) :
    native_re_prefix_match_len? native_re_none xs = none := by
  rw [native_re_prefix_match_len?.eq_1]
  exact native_re_prefix_match_len_go_none xs 0

private theorem native_re_find_idx_aux_none :
    ∀ (xs : List SmtValue) (idx : Nat),
      impl_native_re_find_idx_aux native_re_none xs idx = none
  | [], idx => by
      rw [impl_native_re_find_idx_aux.eq_def]
      simp [native_re_prefix_match_len_none]
  | _ :: cs, idx => by
      rw [impl_native_re_find_idx_aux.eq_def]
      simp [native_re_prefix_match_len_none,
        native_re_find_idx_aux_none cs (idx + 1)]

private theorem native_re_find_idx_from_none
    (xs : List SmtValue) (start : Nat) :
    native_re_find_idx_from native_re_none xs start = none := by
  unfold native_re_find_idx_from
  exact native_re_find_idx_aux_none (xs.drop start) start

private theorem native_str_replace_re_none
    (s repl : List SmtValue) :
    native_str_replace_re s native_re_none repl = s := by
  simp [native_str_replace_re, native_re_find_idx_from_none]

private theorem native_pack_unpack_seq_local :
    (ss : SmtSeq) ->
      native_pack_seq (__smtx_elem_typeof_seq_value ss) (native_unpack_seq ss) = ss
  | SmtSeq.empty _ => rfl
  | SmtSeq.cons _ ss => by
      simp [native_pack_seq, native_unpack_seq, __smtx_elem_typeof_seq_value,
        native_pack_unpack_seq_local ss]

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
      ((native_unpack_seq ss).map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) =
    ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq_local ss

private theorem smtx_eval_str_replace_re_term_eq
    (M : SmtModel) (s r repl : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_re s r repl) =
      __smtx_model_eval_str_replace_re
        (__smtx_model_eval M s) (__smtx_model_eval M r)
        (__smtx_model_eval M repl) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem typed___eo_prog_str_replace_re_none_impl
    (t repl : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_replace_re_none t repl) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_replace_re t) Term.re_none) repl
  let rhs := t
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hReplSmtTy := smtx_typeof_of_eo_seq_char repl hReplTrans hReplTy
  have hNoneTy : __smtx_typeof SmtTerm.re_none = SmtType.RegLan := by
    rw [__smtx_typeof.eq_def]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_replace_re (__eo_to_smt t) SmtTerm.re_none (__eo_to_smt repl)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_replace_re_eq]
    simp [hTSmtTy, hReplSmtTy, hNoneTy, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hTSmtTy]) (by rw [hLhsTy]; simp)
  have hTNotStuck : t ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hTTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hTTy
  have hReplNotStuck : repl ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hReplTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hReplTy
  have hProg :
      __eo_prog_str_replace_re_none t repl = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_replace_re_none t repl =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re t) Term.re_none)
                repl))
            t := by
      cases ht : t <;> cases hr : repl <;> first
        | exact False.elim (hTNotStuck ht)
        | exact False.elim (hReplNotStuck hr)
        | rfl
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_replace_re_none_impl
    (M : SmtModel) (hM : model_wf M) (t repl : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_str_replace_re_none t repl) true := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_replace_re t) Term.re_none) repl
  let rhs := t
  have hTNotStuck : t ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hTTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hTTy
  have hReplNotStuck : repl ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hReplTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hReplTy
  have hProg :
      __eo_prog_str_replace_re_none t repl = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_replace_re_none t repl =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re t) Term.re_none)
                repl))
            t := by
      cases ht : t <;> cases hr : repl <;> first
        | exact False.elim (hTNotStuck ht)
        | exact False.elim (hReplNotStuck hr)
        | rfl
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_replace_re_none_impl t repl hTTrans hReplTrans hTTy hReplTy
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hReplSmtTy := smtx_typeof_of_eo_seq_char repl hReplTrans hReplTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hReplEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq SmtType.Char := by
    simpa [hReplSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ss, hTEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨replSeq, hReplEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace_re (__eo_to_smt t) SmtTerm.re_none (__eo_to_smt repl)) =
      __smtx_model_eval M (__eo_to_smt t)
    rw [smtx_eval_str_replace_re_term_eq]
    have hNoneEval :
        __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan native_re_none := by
      rw [__smtx_model_eval.eq_def]
    rw [hTEval, hReplEval, hNoneEval]
    simp [__smtx_model_eval_str_replace_re, native_str_replace_re_none,
      native_pack_unpack_seq_local]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_re_none_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_re_none args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_re_none args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_re_none args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_re_none args premises ≠
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
                  let lhs :=
                    Term.Apply
                      (Term.Apply (Term.Apply Term.str_replace_re a1) Term.re_none) a2
                  let rhs := a1
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_replace_re_none
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply (Term.Apply Term.eq lhs) rhs := by
                    have hProgEqRaw :
                        __eo_cmd_step_proven s CRule.str_replace_re_none
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                          Term.Apply
                            (Term.Apply Term.eq
                              (Term.Apply
                                (Term.Apply (Term.Apply Term.str_replace_re a1)
                                  Term.re_none)
                                a2))
                            a1 := by
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
                      __eo_typeof a1 = Term.Apply Term.Seq Term.Char ∧
                        __eo_typeof a2 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_replace_re (__eo_typeof a1) Term.RegLan
                      (__eo_typeof a2) ≠ Term.Stuck at hLhsNotStuck
                    have hArgs :=
                      eo_typeof_str_replace_re_args_of_ne_stuck
                        (__eo_typeof a1) Term.RegLan (__eo_typeof a2) hLhsNotStuck
                    exact ⟨hArgs.1, hArgs.2.2⟩
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_replace_re_none a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_str_replace_re_none_impl a1 a2 hA1Trans hA2Trans
                        hArgTypes.1 hArgTypes.2)⟩
                    intro _hTrue
                    exact facts___eo_prog_str_replace_re_none_impl M hM a1 a2
                      hA1Trans hA2Trans hArgTypes.1 hArgTypes.2
                  change StepRuleProperties M [] (__eo_prog_str_replace_re_none a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
