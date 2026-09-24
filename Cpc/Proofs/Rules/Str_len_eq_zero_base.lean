module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev lenZeroBaseLhs (x : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len x)) (Term.Numeral 0)

private abbrev lenZeroBaseRhs (x A : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) (__seq_empty A)

private abbrev lenZeroBaseConclusion (x A : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lenZeroBaseLhs x)) (lenZeroBaseRhs x A)

private theorem eo_typeof_seq_empty_seq_of_ne_stuck
    (T : Term)
    (h : __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) ≠ Term.Stuck) :
    __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) =
      Term.Apply Term.Seq T := by
  by_cases hChar : T = Term.Char
  · subst T
    rfl
  · have hDefault :
        __seq_empty (Term.Apply Term.Seq T) =
          Term.seq_empty (Term.Apply Term.Seq T) := by
      cases T <;> simp [__seq_empty] at hChar ⊢
      case UOp op =>
        cases op <;> simp [__seq_empty] at hChar ⊢
    rw [hDefault] at h
    rw [hDefault]
    change
      __eo_typeof_seq_empty
          (__eo_typeof_Seq (__eo_typeof T))
          (Term.Apply Term.Seq T) =
        Term.Apply Term.Seq T
    change
      __eo_typeof_seq_empty
          (__eo_typeof_Seq (__eo_typeof T))
          (Term.Apply Term.Seq T) ≠ Term.Stuck at h
    cases hTy : __eo_typeof T <;>
      simp [__eo_typeof_Seq, __eo_typeof_seq_empty,
        __eo_disamb_type_seq_empty, hTy] at h ⊢

private theorem eo_typeof_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals
    assumption

private theorem prog_str_len_eq_zero_base_eq_of_ne_stuck
    (s T : Term)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_str_len_eq_zero_base s (Term.Apply Term.Seq T) =
      lenZeroBaseConclusion s (Term.Apply Term.Seq T) := by
  cases hS : s <;> first
    | exact False.elim (hs hS)
    | cases T <;>
        simp [__eo_prog_str_len_eq_zero_base, lenZeroBaseConclusion,
          lenZeroBaseLhs, lenZeroBaseRhs, __eo_mk_apply, __seq_empty]
      case UOp op =>
        cases op <;>
          simp [__eo_prog_str_len_eq_zero_base, lenZeroBaseConclusion,
            lenZeroBaseLhs, lenZeroBaseRhs, __eo_mk_apply, __seq_empty]

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

private theorem smtx_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

private theorem typed___eo_prog_str_len_eq_zero_base_impl
    (x T : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_len_eq_zero_base x (Term.Apply Term.Seq T)) := by
  let A := Term.Apply Term.Seq T
  let lhs := lenZeroBaseLhs x
  let rhs := lenZeroBaseRhs x A
  have hXNotStuck : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProgEq :
      __eo_prog_str_len_eq_zero_base x A =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [A, lhs, rhs, lenZeroBaseConclusion] using
      prog_str_len_eq_zero_base_eq_of_ne_stuck x T hXNotStuck
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hLenTy :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len x)) =
        SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt x)) = SmtType.Int
    rw [typeof_str_len_eq, hXSmtTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hZeroTy :
      __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
    rw [__smtx_typeof.eq_def]
  have hLhsBool : RuleProofs.eo_has_bool_type lhs :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (Term.Apply Term.str_len x) (Term.Numeral 0)
      (by rw [hLenTy, hZeroTy]) (by rw [hLenTy]; simp)
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty A)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    have hEmptyTy' :=
      smtx_typeof_seq_empty_typeof_of_smt_type_seq x
        (__eo_to_smt_type T) hXSmtTy
    simpa [A, hXTy] using hEmptyTy'
  have hRhsBool : RuleProofs.eo_has_bool_type rhs :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x (__seq_empty A)
      (by rw [hXSmtTy, hEmptyTy]) (by rw [hXSmtTy]; simp)
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsBool, hRhsBool]) (by rw [hLhsBool]; simp)

private theorem smtx_model_eval_str_len_zero_eq_seq_empty
    (sx : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof_seq_value sx = SmtType.Seq T) :
    __smtx_model_eval_eq
        (__smtx_model_eval_str_len (SmtValue.Seq sx))
        (SmtValue.Numeral 0) =
      __smtx_model_eval_eq
        (SmtValue.Seq sx) (SmtValue.Seq (SmtSeq.empty T)) := by
  cases sx with
  | empty U =>
      simp [__smtx_typeof_seq_value] at hTy
      subst U
      simp [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_seq_len,
        native_veq, native_unpack_seq]
  | cons v vs =>
      simp [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_seq_len,
        native_veq, native_unpack_seq]
      intro h
      have hPos : (0 : Int) < (native_unpack_seq vs).length + 1 := by
        have hNonneg : (0 : Int) <= (native_unpack_seq vs).length := by
          exact Int.natCast_nonneg _
        omega
      rw [h] at hPos
      omega

private theorem facts___eo_prog_str_len_eq_zero_base_impl
    (M : SmtModel) (hM : model_wf M) (x T : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T) :
    eo_interprets M
      (__eo_prog_str_len_eq_zero_base x (Term.Apply Term.Seq T)) true := by
  let A := Term.Apply Term.Seq T
  let lhs := lenZeroBaseLhs x
  let rhs := lenZeroBaseRhs x A
  have hXNotStuck : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProgEq :
      __eo_prog_str_len_eq_zero_base x A =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [A, lhs, rhs, lenZeroBaseConclusion] using
      prog_str_len_eq_zero_base_eq_of_ne_stuck x T hXNotStuck
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    have hTyped :=
      typed___eo_prog_str_len_eq_zero_base_impl x T hXTrans hXTy
    rw [hProgEq] at hTyped
    exact hTyped
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  have hSeqTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hXEvalTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty A)) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) := by
    have hEmptyEval' :=
      eval_seq_empty_typeof M x (__eo_to_smt_type T) hXSmtTy
    simpa [A, hXTy] using hEmptyEval'
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x)) (SmtTerm.Numeral 0)))
      (__smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (__seq_empty A))))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hXEval]
    rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
      rw [__smtx_model_eval.eq_def]]
    rw [smtx_eval_eq_term_eq, hXEval, hEmptyEval]
    rw [smtx_model_eval_str_len_zero_eq_seq_empty sx (__eo_to_smt_type T)
      hSeqTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_str_len_eq_zero_base_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_eq_zero_base args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_len_eq_zero_base args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_eq_zero_base args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_len_eq_zero_base args premises ≠
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
                  change __eo_prog_str_len_eq_zero_base a1 a2 ≠
                    Term.Stuck at hProg
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked] using
                      hCmdTrans.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    exact RuleProofs.term_ne_stuck_of_has_smt_translation
                      a1 hA1Trans
                  have hA2Seq : ∃ T, a2 = Term.Apply Term.Seq T := by
                    cases a2 <;>
                      simp [__eo_prog_str_len_eq_zero_base, hA1NotStuck] at hProg ⊢
                    case Apply f x =>
                      cases f <;>
                        simp [__eo_prog_str_len_eq_zero_base, hA1NotStuck] at hProg ⊢
                      case UOp op =>
                        cases op <;>
                          simp [__eo_prog_str_len_eq_zero_base, hA1NotStuck] at hProg ⊢
                  rcases hA2Seq with ⟨T, hA2⟩
                  subst a2
                  let A := Term.Apply Term.Seq T
                  let lhs := lenZeroBaseLhs a1
                  let rhs := lenZeroBaseRhs a1 A
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_len_eq_zero_base
                          (CArgList.cons a1
                            (CArgList.cons A CArgList.nil)) CIndexList.nil =
                        Term.Apply (Term.Apply Term.eq lhs) rhs := by
                    change __eo_prog_str_len_eq_zero_base a1 A = _
                    simpa [A, lhs, rhs, lenZeroBaseConclusion] using
                      prog_str_len_eq_zero_base_eq_of_ne_stuck a1 T
                        hA1NotStuck
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                    Term.Bool at hResultTy
                  have hRhsTypeNotStuck : __eo_typeof rhs ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).2
                  have hRhsTypeBool : __eo_typeof rhs = Term.Bool := by
                    change __eo_typeof_eq (__eo_typeof a1)
                        (__eo_typeof (__seq_empty A)) = Term.Bool
                    exact eo_typeof_eq_bool_of_ne_stuck
                      (__eo_typeof a1) (__eo_typeof (__seq_empty A))
                      hRhsTypeNotStuck
                  have hEmptyTypeNotStuck :
                      __eo_typeof (__seq_empty A) ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof a1) (__eo_typeof (__seq_empty A))
                      hRhsTypeBool).2
                  have hEmptyType :
                      __eo_typeof (__seq_empty A) = A := by
                    simpa [A] using
                      eo_typeof_seq_empty_seq_of_ne_stuck T
                        (by simpa [A] using hEmptyTypeNotStuck)
                  have hA1Ty : __eo_typeof a1 = A := by
                    have hTypesEq :=
                      RuleProofs.eo_typeof_eq_bool_operands_eq
                        (__eo_typeof a1) (__eo_typeof (__seq_empty A))
                        hRhsTypeBool
                    simpa [hEmptyType] using hTypesEq
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_len_eq_zero_base a1 A) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_str_len_eq_zero_base_impl a1 T
                        hA1Trans (by simpa [A] using hA1Ty))⟩
                    intro _hTrue
                    exact facts___eo_prog_str_len_eq_zero_base_impl M hM a1 T
                      hA1Trans (by simpa [A] using hA1Ty)
                  change StepRuleProperties M []
                    (__eo_prog_str_len_eq_zero_base a1 A)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
