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

private abbrev substrEmptyPremise (x : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len x)) (Term.Numeral 0)

private abbrev substrEmptyLhs (x n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) m

private abbrev substrEmptyConclusion (x n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrEmptyLhs x n m)) x

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

private theorem smtx_eval_str_substr_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem list_eq_nil_of_native_seq_len_zero (xs : List SmtValue)
    (h : native_seq_len xs = 0) :
    xs = [] := by
  have hLenInt : (xs.length : Int) = 0 := by
    simpa [native_seq_len] using h
  have hLenNat : xs.length = 0 := by
    omega
  cases xs with
  | nil => rfl
  | cons _ _ => simp at hLenNat

private theorem native_seq_extract_nil (i n : native_Int) :
    native_seq_extract [] i n = [] := by
  simp [native_seq_extract]

private theorem prog_str_substr_empty_str_info
    (x n m P : Term)
    (hProg : __eo_prog_str_substr_empty_str x n m (Proof.pf P) ≠ Term.Stuck) :
    ∃ x0,
      P = substrEmptyPremise x0 ∧
      x0 = x ∧
      __eo_prog_str_substr_empty_str x n m (Proof.pf P) =
        substrEmptyConclusion x n m := by
  unfold __eo_prog_str_substr_empty_str at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hx :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_empty_str, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      substrEmptyConclusion, substrEmptyLhs]

private theorem typed___eo_prog_str_substr_empty_str_impl
    (x n m P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_empty_str x n m (Proof.pf P) =
        substrEmptyConclusion x n m) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_empty_str x n m (Proof.pf P)) := by
  let lhs := substrEmptyLhs x n m
  let rhs := x
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt n) (__eo_to_smt m)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hXSmtTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [rhs] using hXSmtTy
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_str_substr_empty_str_impl
    (M : SmtModel) (hM : model_wf M) (x n m P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hPrem : eo_interprets M (substrEmptyPremise x) true)
    (hProgEq :
      __eo_prog_str_substr_empty_str x n m (Proof.pf P) =
        substrEmptyConclusion x n m) :
    eo_interprets M (__eo_prog_str_substr_empty_str x n m (Proof.pf P)) true := by
  let lhs := substrEmptyLhs x n m
  let rhs := x
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, lhs, rhs, substrEmptyConclusion] using
      typed___eo_prog_str_substr_empty_str_impl x n m P
        hXTrans hNTrans hMTrans hXTy hNTy hMTy hProgEq
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
  have hXLenZero : native_seq_len (native_unpack_seq sx) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x)) (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hXEval] at hEval
        rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
          rw [__smtx_model_eval.eq_def]] at hEval
        simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq]
          using hEval
  have hXNil : native_unpack_seq sx = [] :=
    list_eq_nil_of_native_seq_len_zero (native_unpack_seq sx) hXLenZero
  have hXSeqTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hXEvalTy
  have hXElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hXSeqTy
  have hXPack :
      native_pack_seq (__smtx_elem_typeof_seq_value sx) (native_unpack_seq sx) =
        sx :=
    native_pack_unpack_seq sx
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt n) (__eo_to_smt m)) =
      __smtx_model_eval M (__eo_to_smt x)
    rw [smtx_eval_str_substr_term_eq, hXEval, hNEval, hMEval]
    rw [← hXPack]
    simp [__smtx_model_eval_str_substr, hXNil, hXElem,
      native_seq_extract_nil, native_pack_seq, native_unpack_seq,
      __smtx_elem_typeof_seq_value]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_empty_str_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_empty_str args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_empty_str args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_empty_str args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_empty_str args premises ≠
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
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons p premises =>
                      cases premises with
                      | nil =>
                          let P := __eo_state_proven_nth s p
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using
                              hCmdTrans.2.2.1
                          change __eo_typeof
                              (__eo_prog_str_substr_empty_str a1 a2 a3
                                (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_substr_empty_str a1 a2 a3
                                  (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_substr_empty_str_info a1 a2 a3 P
                              hProgRule with
                            ⟨x0, hPremShape, hx0, hProgEq⟩
                          subst x0
                          let lhs := substrEmptyLhs a1 a2 a3
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs)
                              (__eo_typeof a1) = Term.Bool
                            at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs) (__eo_typeof a1) hResultTy).1
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Int ∧
                                __eo_typeof a3 = Term.Int := by
                            change __eo_typeof_str_substr (__eo_typeof a1)
                                (__eo_typeof a2) (__eo_typeof a3) ≠
                              Term.Stuck at hLhsNotStuck
                            exact eo_typeof_str_substr_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a3) hLhsNotStuck
                          rcases hArgTypes with ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M (substrEmptyPremise a1) true := by
                              simpa [hPremShape] using hPremRaw
                            change eo_interprets M
                              (__eo_prog_str_substr_empty_str a1 a2 a3
                                (Proof.pf P)) true
                            exact facts___eo_prog_str_substr_empty_str_impl M hM
                              a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_substr_empty_str_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hA1Ty hA2Ty hA3Ty hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
