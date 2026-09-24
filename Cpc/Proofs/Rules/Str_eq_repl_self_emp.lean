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

private abbrev selfEmpPremise (emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len emp))
    (Term.Numeral 0)

private abbrev selfEmpValue (x pat : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) pat) x

private abbrev selfEmpLhs (x pat emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (selfEmpValue x pat)) emp

private abbrev selfEmpRhs (x emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) emp

private abbrev selfEmpConclusion (x pat emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (selfEmpLhs x pat emp))
    (selfEmpRhs x emp)

private theorem eo_typeof_eq_nonstuck_bool (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals assumption

private theorem eo_typeof_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_replace] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_replace] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_replace] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_replace] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_replace] at h ⊢
            case Seq =>
              cases C <;> simp [__eo_typeof_str_replace] at h ⊢
              case Apply k z =>
                cases k <;> simp [__eo_typeof_str_replace] at h ⊢
                case UOp opk =>
                  cases opk <;> simp [__eo_typeof_str_replace] at h ⊢
                  case Seq =>
                    have hEq :=
                      RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                        x x y z (Term.Apply Term.Seq x) h
                    rcases hEq with ⟨hy, hz⟩
                    subst y
                    subst z
                    simp

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

private theorem smtx_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_replace_self_eq_nil_iff
    (xs pat : List SmtValue) :
    native_seq_replace xs pat xs = [] ↔ xs = [] := by
  constructor
  · intro hReplace
    cases pat with
    | nil =>
        simp [native_seq_replace] at hReplace
        exact hReplace
    | cons p ps =>
        by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
        · simpa [native_seq_replace, hNeg] using hReplace
        · have hExpanded :
              xs.take (Int.toNat (native_seq_indexof xs (p :: ps) 0)) ++
                  xs ++
                  xs.drop
                    (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
                      (p :: ps).length) =
                [] := by
              simpa [native_seq_replace, hNeg] using hReplace
          have hLen := congrArg List.length hExpanded
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_append, List.length_nil] at hLen
          omega
  · intro hXs
    subst xs
    cases pat with
    | nil => rfl
    | cons p ps =>
        simp [native_seq_replace, native_seq_indexof]

private theorem list_eq_nil_of_native_seq_len_zero (xs : List SmtValue)
    (h : native_seq_len xs = 0) :
    xs = [] := by
  have hLenInt : (xs.length : Int) = 0 := by
    simpa [native_seq_len] using h
  have hLenNat : xs.length = 0 := by
    omega
  exact List.eq_nil_of_length_eq_zero hLenNat

private theorem prog_str_eq_repl_self_emp_info
    (x pat emp P : Term)
    (hProg : __eo_prog_str_eq_repl_self_emp x pat emp (Proof.pf P) ≠
      Term.Stuck) :
    ∃ emp0,
      P = selfEmpPremise emp0 ∧ emp0 = emp ∧
      __eo_prog_str_eq_repl_self_emp x pat emp (Proof.pf P) =
        selfEmpConclusion x pat emp := by
  unfold __eo_prog_str_eq_repl_self_emp at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hEmp :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_eq_repl_self_emp, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      selfEmpConclusion, selfEmpLhs, selfEmpRhs, selfEmpValue]

private theorem typed___eo_prog_str_eq_repl_self_emp_impl
    (x pat emp P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_eq_repl_self_emp x pat emp (Proof.pf P) =
        selfEmpConclusion x pat emp) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_eq_repl_self_emp x pat emp (Proof.pf P)) := by
  let value := selfEmpValue x pat
  let lhs := selfEmpLhs x pat emp
  let rhs := selfEmpRhs x emp
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hPatSmtTy := smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
          (__eo_to_smt x)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hPatSmtTy, __smtx_typeof_seq_op_3, native_ite,
      native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type value emp
      (by rw [hValueTy, hEmpSmtTy]) (by rw [hValueTy]; simp)
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x emp
      (by rw [hXSmtTy, hEmpSmtTy]) (by rw [hXSmtTy]; simp)
  have hBool : RuleProofs.eo_has_bool_type (selfEmpConclusion x pat emp) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_eq_repl_self_emp_impl
    (M : SmtModel) (hM : model_wf M) (x pat emp P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (selfEmpPremise emp) true)
    (hProgEq :
      __eo_prog_str_eq_repl_self_emp x pat emp (Proof.pf P) =
        selfEmpConclusion x pat emp) :
    eo_interprets M
      (__eo_prog_str_eq_repl_self_emp x pat emp (Proof.pf P)) true := by
  let lhs := selfEmpLhs x pat emp
  let rhs := selfEmpRhs x emp
  have hBool : RuleProofs.eo_has_bool_type
      (selfEmpConclusion x pat emp) := by
    simpa [hProgEq] using
      typed___eo_prog_str_eq_repl_self_emp_impl x pat emp P
        hXTrans hPatTrans hEmpTrans hXTy hPatTy hEmpTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hPatSmtTy := smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hPatEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt pat)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPatSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt pat) (by
        unfold term_has_non_none_type
        rw [hPatSmtTy]
        simp)
  have hEmpEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt emp)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hEmpSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt emp) (by
        unfold term_has_non_none_type
        rw [hEmpSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hPatEvalTy with ⟨spat, hPatEval⟩
  rcases seq_value_canonical hEmpEvalTy with ⟨semp, hEmpEval⟩
  have hEmpNil : native_unpack_seq semp = [] := by
    have hLenZero : native_seq_len (native_unpack_seq semp) = 0 := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
      cases hPrem with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt emp))
                (SmtTerm.Numeral 0)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hEmpEval,
            smtx_eval_numeral_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq] using hEval
    exact list_eq_nil_of_native_seq_len_zero _ hLenZero
  have hSxTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSempTy :
      __smtx_typeof_seq_value semp = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hEmpEval] using hEmpEvalTy
  have hSxElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSempElem : __smtx_elem_typeof_seq_value semp = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSempTy
  have hSeqEqIff :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
            (native_unpack_seq sx)) = semp ↔
        sx = semp := by
    constructor
    · intro hEq
      have hLists :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
              (native_unpack_seq sx) = [] := by
        have hUnpack := congrArg native_unpack_seq hEq
        simpa [Smtm.native_unpack_pack_seq, hEmpNil] using hUnpack
      have hXNil : native_unpack_seq sx = [] :=
        (native_seq_replace_self_eq_nil_iff _ _).mp hLists
      calc
        sx = native_pack_seq (__smtx_elem_typeof_seq_value sx)
            (native_unpack_seq sx) := (native_pack_unpack_seq sx).symm
        _ = native_pack_seq (__smtx_elem_typeof_seq_value semp)
            (native_unpack_seq semp) := by
              rw [hSxElem, hSempElem, hXNil, hEmpNil]
        _ = semp := native_pack_unpack_seq semp
    · intro hEq
      subst semp
      have hXNil : native_unpack_seq sx = [] := hEmpNil
      have hReplaceNil :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
              (native_unpack_seq sx) = [] :=
        (native_seq_replace_self_eq_nil_iff _ _).2 hXNil
      rw [hReplaceNil]
      simpa [hXNil] using native_pack_unpack_seq sx
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
            (__eo_to_smt x))
          (__eo_to_smt emp)) =
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt emp))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_eq_term_eq, hXEval, hPatEval, hEmpEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_eq, native_veq,
      hSeqEqIff]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_repl_self_emp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_self_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_repl_self_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_self_emp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_repl_self_emp args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons a3 args =>
              cases args with
              | cons _ _ => exact absurd rfl hProg
              | nil =>
                  cases premises with
                  | nil => exact absurd rfl hProg
                  | cons n premises =>
                      cases premises with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          let P := __eo_state_proven_nth s n
                          have hA1Trans :
                              RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.1
                          have hA2Trans :
                              RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.1
                          have hA3Trans :
                              RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.2.1
                          change __eo_typeof
                              (__eo_prog_str_eq_repl_self_emp a1 a2 a3
                                (Proof.pf P)) = Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_eq_repl_self_emp a1 a2 a3
                                  (Proof.pf P) ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_eq_repl_self_emp_info
                              a1 a2 a3 P hRuleProg with
                            ⟨emp0, hPremShape, hEmp0, hProgEq⟩
                          subst emp0
                          rw [hProgEq] at hResultTy
                          have hOuterLeftTy :
                              __eo_typeof (selfEmpLhs a1 a2 a3) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof (selfEmpLhs a1 a2 a3))
                                (__eo_typeof (selfEmpRhs a1 a3)) =
                              Term.Bool at hResultTy
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof (selfEmpLhs a1 a2 a3))
                                (__eo_typeof (selfEmpRhs a1 a3))
                                hResultTy).1
                          have hInnerLeftBool :
                              __eo_typeof (selfEmpLhs a1 a2 a3) =
                                Term.Bool := by
                            change __eo_typeof_eq
                                (__eo_typeof (selfEmpValue a1 a2))
                                (__eo_typeof a3) = Term.Bool
                            exact eo_typeof_eq_nonstuck_bool _ _ hOuterLeftTy
                          have hValueTy :
                              __eo_typeof (selfEmpValue a1 a2) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof (selfEmpValue a1 a2))
                                (__eo_typeof a3) = Term.Bool at hInnerLeftBool
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof (selfEmpValue a1 a2))
                                (__eo_typeof a3) hInnerLeftBool).1
                          rcases eo_typeof_str_replace_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a1) hValueTy with
                            ⟨T, hA1Ty, hA2Ty, _hA1Ty'⟩
                          have hValueTyEq :
                              __eo_typeof (selfEmpValue a1 a2) =
                                Term.Apply Term.Seq T := by
                            change __eo_typeof_str_replace (__eo_typeof a1)
                                (__eo_typeof a2) (__eo_typeof a1) =
                              Term.Apply Term.Seq T
                            change __eo_typeof_str_replace (__eo_typeof a1)
                                (__eo_typeof a2) (__eo_typeof a1) ≠
                              Term.Stuck at hValueTy
                            rw [hA1Ty, hA2Ty]
                            rw [hA1Ty, hA2Ty] at hValueTy
                            cases T <;>
                              simp [__eo_typeof_str_replace, __eo_requires,
                                __eo_eq, native_ite, native_teq,
                                SmtEval.native_not, __eo_and, native_and]
                              at hValueTy ⊢
                          have hSameTy :
                              __eo_typeof (selfEmpValue a1 a2) =
                                __eo_typeof a3 :=
                            RuleProofs.eo_typeof_eq_bool_operands_eq
                              (__eo_typeof (selfEmpValue a1 a2))
                              (__eo_typeof a3) hInnerLeftBool
                          have hA3Ty :
                              __eo_typeof a3 = Term.Apply Term.Seq T := by
                            rw [← hSameTy]
                            exact hValueTyEq
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M (selfEmpPremise a3) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_eq_repl_self_emp_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (typed___eo_prog_str_eq_repl_self_emp_impl
                                  a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                  hA1Ty hA2Ty hA3Ty hProgEq)
