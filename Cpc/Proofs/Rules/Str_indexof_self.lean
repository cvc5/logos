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

private theorem native_seq_indexof_self_eq_empty_self
    (xs : List SmtValue) (i : native_Int) :
    native_seq_indexof xs xs i = native_seq_indexof ([] : List SmtValue) [] i := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          exact (native_seq_indexof_self_zero xs).trans (native_seq_indexof_self_zero ([] : List SmtValue)).symm
      | succ n =>
          unfold native_seq_indexof
          have hLeft : ¬ Nat.succ n + xs.length ≤ xs.length := by
            omega
          simp [hLeft]
  | negSucc n =>
      simp [native_seq_indexof]

private theorem eo_typeof_str_indexof_self_args_of_ne_stuck
    (T N : Term)
    (h : __eo_typeof_str_indexof T T N ≠ Term.Stuck) :
    ∃ U, T = Term.Apply Term.Seq U ∧ N = Term.Int := by
  cases T <;> simp [__eo_typeof_str_indexof] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases N <;> simp at h ⊢
        case UOp opn =>
          cases opn <;> simp at h ⊢

private theorem prog_str_indexof_self_eq_of_seq
    (t n U : Term) (ht : t ≠ Term.Stuck) (hn : n ≠ Term.Stuck) :
    __eo_prog_str_indexof_self t n (Term.Apply Term.Seq U) =
      Term.Apply
        (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) t) n))
        (Term.Apply
          (Term.Apply (Term.Apply Term.str_indexof
            (__seq_empty (Term.Apply Term.Seq U)))
            (__seq_empty (Term.Apply Term.Seq U)))
          n) := by
  unfold __eo_prog_str_indexof_self
  split
  · contradiction
  · contradiction
  · next heq =>
      cases heq
      cases U <;> simp [__eo_mk_apply, __seq_empty]
      case UOp op =>
        cases op <;> simp [__eo_mk_apply, __seq_empty]
  · next hno =>
      exact False.elim (hno U rfl)

private theorem prog_str_indexof_self_type_arg_seq_of_ne_stuck
    (t n ty : Term)
    (h : __eo_prog_str_indexof_self t n ty ≠ Term.Stuck) :
    ∃ U, ty = Term.Apply Term.Seq U := by
  unfold __eo_prog_str_indexof_self at h
  split at h <;> try contradiction
  next =>
    exact ⟨_, rfl⟩

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

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

private theorem eo_to_smt_type_seq_of_wf
    (T : Term)
    (hWf :
      __smtx_type_wf (__eo_to_smt_type (Term.Apply Term.Seq T)) = true) :
    __eo_to_smt_type (Term.Apply Term.Seq T) =
      SmtType.Seq (__eo_to_smt_type T) := by
  rw [TranslationProofs.eo_to_smt_type_seq]
  apply TranslationProofs.smtx_typeof_guard_of_non_none
  intro hNone
  rw [TranslationProofs.eo_to_smt_type_seq] at hWf
  simp [__smtx_typeof_guard, hNone, native_ite, native_Teq,
    __smtx_type_wf, __smtx_type_wf_component, native_inhabited_type,
    native_not, native_and] at hWf

private theorem smt_typeof_seq_empty_of_wf_type
    (A : Term) (T : SmtType)
    (hA : __eo_to_smt_type A = SmtType.Seq T)
    (hAWf : __smtx_type_wf (__eo_to_smt_type A) = true) :
    __smtx_typeof (__eo_to_smt (__seq_empty A)) = SmtType.Seq T := by
  apply smt_typeof_seq_empty_of_type A T hA
  by_cases hSpecial : A = Term.Apply Term.Seq Term.Char
  · subst A
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) ≠
      SmtType.None
    rw [__smtx_typeof.eq_4]
    simp [native_string_lit, native_string_valid, native_ite]
  · by_cases hStuck : A = Term.Stuck
    · subst A
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault]
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None
      rw [hA]
      change __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None
      rw [__smtx_typeof.eq_def]
      have hSeqWf : __smtx_type_wf (SmtType.Seq T) = true := by
        simpa [hA] using hAWf
      simp [__smtx_typeof_guard_wf, hSeqWf, native_ite]

private theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem typed___eo_prog_str_indexof_self_impl
    (t n ty : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hTySeq : ∃ U, ty = Term.Apply Term.Seq U)
    (hTyWf : __smtx_type_wf (__eo_to_smt_type ty) = true) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_indexof_self t n ty) := by
  rcases hTTy with ⟨T, hTTy⟩
  rcases hTySeq with ⟨U, hTySeq⟩
  let empty := __seq_empty ty
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) t) n
  let rhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof empty) empty) n
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTypeSmt :
      __eo_to_smt_type ty = SmtType.Seq (__eo_to_smt_type U) := by
    rw [hTySeq]
    exact eo_to_smt_type_seq_of_wf U (by simpa [hTySeq] using hTyWf)
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt empty) =
        SmtType.Seq (__eo_to_smt_type U) :=
    smt_typeof_seq_empty_of_wf_type ty (__eo_to_smt_type U) hTypeSmt hTyWf
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt t) (__eo_to_smt n)) =
      SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hTSmtTy, hNSmtTy, __smtx_typeof_str_indexof, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt empty) (__eo_to_smt empty)
          (__eo_to_smt n)) =
      SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hEmptyTy, hNSmtTy, __smtx_typeof_str_indexof, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hNNotStuck : n ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hProg :
      __eo_prog_str_indexof_self t n ty =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_indexof_self t n ty =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) t) n))
            (Term.Apply
              (Term.Apply (Term.Apply Term.str_indexof (__seq_empty ty))
                (__seq_empty ty))
              n) := by
      rw [hTySeq]
      exact prog_str_indexof_self_eq_of_seq t n U hTNotStuck hNNotStuck
    simpa [lhs, rhs, empty] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_indexof_self_impl
    (M : SmtModel) (hM : model_wf M) (t n ty : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hTySeq : ∃ U, ty = Term.Apply Term.Seq U)
    (hTyWf : __smtx_type_wf (__eo_to_smt_type ty) = true) :
    eo_interprets M (__eo_prog_str_indexof_self t n ty) true := by
  rcases hTTy with ⟨T, hTTy⟩
  rcases hTySeq with ⟨U, hTySeq⟩
  let empty := __seq_empty ty
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) t) n
  let rhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof empty) empty) n
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hNNotStuck : n ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hProg :
      __eo_prog_str_indexof_self t n ty =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_str_indexof_self t n ty =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) t) n))
            (Term.Apply
              (Term.Apply (Term.Apply Term.str_indexof (__seq_empty ty))
                (__seq_empty ty))
              n) := by
      rw [hTySeq]
      exact prog_str_indexof_self_eq_of_seq t n U hTNotStuck hNNotStuck
    simpa [lhs, rhs, empty] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_indexof_self_impl t n ty hTTrans hNTrans
        ⟨T, hTTy⟩ hNTy ⟨U, hTySeq⟩ hTyWf
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTypeSmt :
      __eo_to_smt_type ty = SmtType.Seq (__eo_to_smt_type U) := by
    rw [hTySeq]
    exact eo_to_smt_type_seq_of_wf U (by simpa [hTySeq] using hTyWf)
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ss, hTEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt empty) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) :=
    eval_seq_empty_of_type M ty (__eo_to_smt_type U) hTypeSmt
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt t) (__eo_to_smt n)) =
      __smtx_model_eval M
        (SmtTerm.str_indexof (__eo_to_smt empty) (__eo_to_smt empty)
          (__eo_to_smt n))
    rw [smtx_eval_str_indexof_term_eq, smtx_eval_str_indexof_term_eq]
    rw [hTEval, hNEval, hEmptyEval]
    simp [__smtx_model_eval_str_indexof, native_seq_indexof_self_eq_empty_self]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_indexof_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_self args premises ≠
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
                  cases premises with
                  | nil =>
                      change __eo_prog_str_indexof_self a1 a2 a3 ≠
                        Term.Stuck at hProg
                      have hMask :
                          argTranslationOkMasked ArgTranslationKind.term a1 ∧
                            argTranslationOkMasked ArgTranslationKind.term a2 ∧
                              argTranslationOkMasked ArgTranslationKind.type a3 ∧
                                True := by
                        simpa [cmdTranslationOk, cArgListTranslationOkMask]
                          using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        exact hMask.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        exact hMask.2.1
                      have hA3Wf :
                          __smtx_type_wf (__eo_to_smt_type a3) = true := by
                        simpa [argTranslationOkMasked] using hMask.2.2.1
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
                      have hA3Seq : ∃ U, a3 = Term.Apply Term.Seq U :=
                        prog_str_indexof_self_type_arg_seq_of_ne_stuck
                          a1 a2 a3 hProg
                      let empty := __seq_empty a3
                      let lhs :=
                        Term.Apply (Term.Apply (Term.Apply Term.str_indexof a1) a1) a2
                      let rhs :=
                        Term.Apply (Term.Apply (Term.Apply Term.str_indexof empty) empty) a2
                      have hProgEq :
                          __eo_cmd_step_proven s CRule.str_indexof_self
                            (CArgList.cons a1
                              (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                            CIndexList.nil =
                            Term.Apply (Term.Apply Term.eq lhs) rhs := by
                        have hProgEqRaw :
                            __eo_cmd_step_proven s CRule.str_indexof_self
                              (CArgList.cons a1
                                (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                              CIndexList.nil =
                              Term.Apply
                                (Term.Apply Term.eq
                                  (Term.Apply
                                    (Term.Apply (Term.Apply Term.str_indexof a1) a1)
                                    a2))
                                (Term.Apply
                                  (Term.Apply
                                    (Term.Apply Term.str_indexof (__seq_empty a3))
                                    (__seq_empty a3))
                                  a2) := by
                          rcases hA3Seq with ⟨U, hA3Eq⟩
                          rw [hA3Eq]
                          exact prog_str_indexof_self_eq_of_seq
                            a1 a2 U hA1NotStuck hA2NotStuck
                        simpa [lhs, rhs, empty] using hProgEqRaw
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                        Term.Bool at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                      have hArgTypes :
                          (∃ T, __eo_typeof a1 = Term.Apply Term.Seq T) ∧
                            __eo_typeof a2 = Term.Int := by
                        change __eo_typeof_str_indexof (__eo_typeof a1)
                          (__eo_typeof a1) (__eo_typeof a2) ≠ Term.Stuck
                          at hLhsNotStuck
                        rcases eo_typeof_str_indexof_self_args_of_ne_stuck
                            (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck with
                          ⟨T, hA1Ty, hA2Ty⟩
                        exact ⟨⟨T, hA1Ty⟩, hA2Ty⟩
                      have hProps :
                          StepRuleProperties M (premiseTermList s CIndexList.nil)
                            (__eo_prog_str_indexof_self a1 a2 a3) := by
                        refine ⟨?_,
                          RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (typed___eo_prog_str_indexof_self_impl a1 a2 a3
                              hA1Trans hA2Trans hArgTypes.1 hArgTypes.2
                              hA3Seq hA3Wf)⟩
                        intro _hTrue
                        exact facts___eo_prog_str_indexof_self_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hArgTypes.1 hArgTypes.2 hA3Seq hA3Wf
                      change StepRuleProperties M []
                        (__eo_prog_str_indexof_self a1 a2 a3)
                      simpa [premiseTermList] using hProps
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
