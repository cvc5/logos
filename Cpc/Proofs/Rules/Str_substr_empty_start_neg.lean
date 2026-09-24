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

private abbrev substrStartNegPremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.lt n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev substrStartNegLhs (x n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) m

private abbrev substrStartNegConclusion (x n m A : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrStartNegLhs x n m)) (__seq_empty A)

private theorem eo_typeof_str_substr_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_substr A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Int ∧ C = Term.Int := by
  cases A <;> simp [__eo_typeof_str_substr] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case UOp opb =>
          cases opb <;> simp at h ⊢
          case Int =>
            cases C <;> simp at h ⊢
            case UOp opc =>
              cases opc <;> simp at h ⊢

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

private theorem smtx_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

private theorem smtx_eval_str_substr_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_lt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt x y) =
      __smtx_model_eval_lt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_extract_empty_of_start_neg
    (xs : List SmtValue) (i n : native_Int)
    (h : i < 0) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  simp [h]

private theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty]
  case UOp op =>
    cases op <;> simp [__seq_empty]

private theorem eo_mk_apply_eq_seq_empty
    (lhs T : Term) :
    __eo_mk_apply (Term.Apply Term.eq lhs)
        (__seq_empty (Term.Apply Term.Seq T)) =
      Term.Apply (Term.Apply Term.eq lhs)
        (__seq_empty (Term.Apply Term.Seq T)) := by
  have hEmpty : __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck :=
    seq_empty_seq_ne_stuck T
  cases hE : __seq_empty (Term.Apply Term.Seq T) <;>
    simp [__eo_mk_apply]
  exact False.elim (hEmpty hE)

private theorem prog_str_substr_empty_start_neg_info
    (x n m A P : Term)
    (hProg : __eo_prog_str_substr_empty_start_neg x n m A (Proof.pf P) ≠
      Term.Stuck) :
    ∃ T n0,
      A = Term.Apply Term.Seq T ∧
      P = substrStartNegPremise n0 ∧
      n0 = n ∧
      __eo_prog_str_substr_empty_start_neg x n m A (Proof.pf P) =
        substrStartNegConclusion x n m (Term.Apply Term.Seq T) := by
  unfold __eo_prog_str_substr_empty_start_neg at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hn :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_empty_start_neg, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      eo_mk_apply_eq_seq_empty, substrStartNegConclusion, substrStartNegLhs]

private theorem seq_type_arg_eq_of_result_type
    (lhs : Term) (U T : Term)
    (hLhsTy : __eo_typeof lhs = Term.Apply Term.Seq U)
    (hEmptyTy :
      __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) =
        Term.Apply Term.Seq T)
    (hResultTy :
      __eo_typeof (Term.Apply (Term.Apply Term.eq lhs)
          (__seq_empty (Term.Apply Term.Seq T))) = Term.Bool) :
    U = T := by
  change __eo_typeof_eq (__eo_typeof lhs)
      (__eo_typeof (__seq_empty (Term.Apply Term.Seq T))) = Term.Bool
    at hResultTy
  rw [hLhsTy, hEmptyTy] at hResultTy
  change
      __eo_requires
        (__eo_eq (Term.Apply Term.Seq U) (Term.Apply Term.Seq T))
        (Term.Boolean true) Term.Bool = Term.Bool
    at hResultTy
  have hReqNe :
      __eo_requires
        (__eo_eq (Term.Apply Term.Seq U) (Term.Apply Term.Seq T))
        (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
    rw [hResultTy]
    simp
  have hSeqEq :
      Term.Apply Term.Seq T = Term.Apply Term.Seq U :=
    RuleProofs.eq_of_requires_eq_true_not_stuck
      (Term.Apply Term.Seq U) (Term.Apply Term.Seq T) Term.Bool hReqNe
  cases hSeqEq
  rfl

private theorem facts___eo_prog_str_substr_empty_start_neg_impl
    (M : SmtModel) (hM : model_wf M) (x n m P T : Term)
    (hBoolEq :
      RuleProofs.eo_has_bool_type
        (substrStartNegConclusion x n m (Term.Apply Term.Seq T)))
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hPrem : eo_interprets M (substrStartNegPremise n) true)
    (hProgEq :
      __eo_prog_str_substr_empty_start_neg x n m (Term.Apply Term.Seq T)
          (Proof.pf P) =
        substrStartNegConclusion x n m (Term.Apply Term.Seq T)) :
    eo_interprets M
      (__eo_prog_str_substr_empty_start_neg x n m (Term.Apply Term.Seq T)
        (Proof.pf P)) true := by
  let lhs := substrStartNegLhs x n m
  let rhs := __seq_empty (Term.Apply Term.Seq T)
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  have hMEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
        SmtType.Int := by
    simpa [hMSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m) (by
        unfold term_has_non_none_type
        rw [hMSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hNStartNeg : ni < 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.lt (__eo_to_smt n) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_lt_term_eq, hNEval,
          smtx_eval_numeral_term_eq,
          smtx_eval_boolean_term_eq] at hEval
        have hLtBool : native_zlt ni 0 = true := by
          simpa [__smtx_model_eval_lt,
            __smtx_model_eval_eq, native_veq] using hEval
        simpa [SmtEval.native_zlt] using hLtBool
  have hXSeqTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hXEvalTy
  have hXElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hXSeqTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) := by
    have hEmptyEval' :=
      eval_seq_empty_typeof M x (__eo_to_smt_type T) hXSmtTy
    simpa [rhs, hXTy] using hEmptyEval'
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt n) (__eo_to_smt m)) =
      __smtx_model_eval M (__eo_to_smt rhs)
    rw [smtx_eval_str_substr_term_eq, hXEval, hNEval, hMEval, hEmptyEval]
    simp [__smtx_model_eval_str_substr, hXElem,
      native_seq_extract_empty_of_start_neg _ _ _ hNStartNeg,
      native_pack_seq]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs
    (by simpa [substrStartNegConclusion, lhs, rhs] using hBoolEq) <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_empty_start_neg_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_empty_start_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_empty_start_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_empty_start_neg args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_empty_start_neg args premises ≠
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
              | cons A args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p premises =>
                          cases premises with
                          | nil =>
                              let P := __eo_state_proven_nth s p
                              have hA1Trans :
                                  RuleProofs.eo_has_smt_translation a1 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked]
                                  using hCmdTrans.1
                              have hA2Trans :
                                  RuleProofs.eo_has_smt_translation a2 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked]
                                  using hCmdTrans.2.1
                              have hA3Trans :
                                  RuleProofs.eo_has_smt_translation a3 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked]
                                  using hCmdTrans.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_substr_empty_start_neg a1 a2 a3 A
                                    (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hProgRule :
                                  __eo_prog_str_substr_empty_start_neg a1 a2 a3 A
                                      (Proof.pf P) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_substr_empty_start_neg_info a1 a2 a3 A P
                                  hProgRule with
                                ⟨T, n0, hATyArg, hPremShape, hn0, hProgEq⟩
                              subst A
                              subst n0
                              let lhs := substrStartNegLhs a1 a2 a3
                              rw [hProgEq] at hResultTy
                              change __eo_typeof
                                  (Term.Apply (Term.Apply Term.eq lhs)
                                    (__seq_empty (Term.Apply Term.Seq T))) =
                                Term.Bool at hResultTy
                              change __eo_typeof_eq (__eo_typeof lhs)
                                  (__eo_typeof
                                    (__seq_empty (Term.Apply Term.Seq T))) =
                                Term.Bool at hResultTy
                              have hOperandTypes :=
                                RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof lhs)
                                  (__eo_typeof
                                    (__seq_empty (Term.Apply Term.Seq T)))
                                  hResultTy
                              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                hOperandTypes.1
                              have hRhsNotStuck :
                                  __eo_typeof
                                      (__seq_empty (Term.Apply Term.Seq T)) ≠
                                    Term.Stuck :=
                                hOperandTypes.2
                              have hArgTypes :
                                  ∃ U, __eo_typeof a1 = Term.Apply Term.Seq U ∧
                                    __eo_typeof a2 = Term.Int ∧
                                    __eo_typeof a3 = Term.Int := by
                                change __eo_typeof_str_substr (__eo_typeof a1)
                                    (__eo_typeof a2) (__eo_typeof a3) ≠
                                  Term.Stuck at hLhsNotStuck
                                exact eo_typeof_str_substr_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a2)
                                  (__eo_typeof a3) hLhsNotStuck
                              rcases hArgTypes with ⟨U, hA1TyU, hA2Ty, hA3Ty⟩
                              have hLhsTy :
                                  __eo_typeof lhs = Term.Apply Term.Seq U := by
                                change __eo_typeof_str_substr (__eo_typeof a1)
                                  (__eo_typeof a2) (__eo_typeof a3) =
                                  Term.Apply Term.Seq U
                                simp [hA1TyU, hA2Ty, hA3Ty,
                                  __eo_typeof_str_substr]
                              have hEmptyTy :
                                  __eo_typeof
                                      (__seq_empty (Term.Apply Term.Seq T)) =
                                    Term.Apply Term.Seq T :=
                                eo_typeof_seq_empty_seq_of_ne_stuck T
                                  hRhsNotStuck
                              have hUT : U = T :=
                                seq_type_arg_eq_of_result_type lhs U T hLhsTy
                                  hEmptyTy (by
                                    change __eo_typeof
                                      (Term.Apply (Term.Apply Term.eq lhs)
                                        (__seq_empty (Term.Apply Term.Seq T))) =
                                      Term.Bool
                                    exact hResultTy)
                              subst U
                              let rhs := __seq_empty (Term.Apply Term.Seq T)
                              have hA1SmtTy :=
                                smtx_typeof_of_eo_seq a1 T hA1Trans hA1TyU
                              have hA2SmtTy :=
                                smtx_typeof_of_eo_int a2 hA2Trans hA2Ty
                              have hA3SmtTy :=
                                smtx_typeof_of_eo_int a3 hA3Trans hA3Ty
                              have hLhsSmtTy :
                                  __smtx_typeof (__eo_to_smt lhs) =
                                    SmtType.Seq (__eo_to_smt_type T) := by
                                change __smtx_typeof
                                    (SmtTerm.str_substr (__eo_to_smt a1)
                                      (__eo_to_smt a2) (__eo_to_smt a3)) =
                                  SmtType.Seq (__eo_to_smt_type T)
                                rw [typeof_str_substr_eq]
                                simp [hA1SmtTy, hA2SmtTy, hA3SmtTy,
                                  __smtx_typeof_str_substr]
                              have hRhsSmtTy :
                                  __smtx_typeof (__eo_to_smt rhs) =
                                    SmtType.Seq (__eo_to_smt_type T) := by
                                have hEmptyTy' :=
                                  smtx_typeof_seq_empty_typeof_of_smt_type_seq
                                    a1 (__eo_to_smt_type T) hA1SmtTy
                                simpa [rhs, hA1TyU] using hEmptyTy'
                              have hBoolEq :
                                  RuleProofs.eo_has_bool_type
                                    (substrStartNegConclusion a1 a2 a3
                                      (Term.Apply Term.Seq T)) := by
                                have hEqBool :
                                    RuleProofs.eo_has_bool_type
                                      (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
                                  RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                    lhs rhs
                                    (by rw [hLhsSmtTy, hRhsSmtTy])
                                    (by rw [hLhsSmtTy]; simp)
                                simpa [substrStartNegConclusion, lhs, rhs] using
                                  hEqBool
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M (substrStartNegPremise a2) true := by
                                  simpa [hPremShape] using hPremRaw
                                change eo_interprets M
                                  (__eo_prog_str_substr_empty_start_neg a1 a2 a3
                                    (Term.Apply Term.Seq T) (Proof.pf P)) true
                                exact facts___eo_prog_str_substr_empty_start_neg_impl
                                  M hM a1 a2 a3 P T hBoolEq hA1Trans
                                  hA2Trans hA3Trans hA1TyU hA2Ty hA3Ty hPrem
                                  hProgEq
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_substr_empty_start_neg a1 a2 a3
                                    (Term.Apply Term.Seq T) (Proof.pf P))
                                rw [hProgEq]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hBoolEq
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
