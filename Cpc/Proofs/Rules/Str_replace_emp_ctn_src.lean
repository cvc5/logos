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

private abbrev replaceEmpCtnSrcPremise (emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len emp))
    (Term.Numeral 0)

private abbrev replaceEmpCtnSrcRepl (s t emp : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace emp) s) t

private abbrev replaceEmpCtnSrcLhs (s t emp : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains s) (replaceEmpCtnSrcRepl s t emp)

private abbrev replaceEmpCtnSrcRhs (s t emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq emp) (replaceEmpCtnSrcRepl s t emp)

private abbrev replaceEmpCtnSrcConclusion (s t emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceEmpCtnSrcLhs s t emp))
    (replaceEmpCtnSrcRhs s t emp)

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

private theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

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

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_indexof_rec_nil
    (xs : List SmtValue) (i fuel : Nat)
    (hFuel : fuel ≠ 0) :
    native_seq_indexof_rec xs [] i fuel = Int.ofNat i := by
  cases fuel with
  | zero => exact False.elim (hFuel rfl)
  | succ fuel =>
      rw [Smtm.native_seq_indexof_rec.eq_def]
      simp [native_seq_prefix_eq]

private theorem native_seq_indexof_nil_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  unfold native_seq_indexof
  simp [native_seq_indexof_rec_nil]

private theorem native_seq_contains_nil (xs : List SmtValue) :
    native_seq_contains xs [] = true := by
  unfold native_seq_contains
  rw [native_seq_indexof_nil_zero]
  simp

private theorem native_seq_indexof_empty_nonempty
    (x : SmtValue) (xs : List SmtValue) :
    native_seq_indexof [] (x :: xs) 0 = -1 := by
  unfold native_seq_indexof
  simp

private theorem native_seq_replace_empty_src
    (pat repl : List SmtValue) :
    native_seq_replace [] pat repl = if pat = [] then repl else [] := by
  exact StrEqReplSupport.native_seq_replace_empty_src pat repl

private theorem native_seq_contains_replace_empty_src_eq_empty_eq
    (T : SmtType) (pat repl : List SmtValue) :
    native_seq_contains pat (native_seq_replace [] pat repl) =
      native_veq (SmtValue.Seq (SmtSeq.empty T))
        (SmtValue.Seq (native_pack_seq T (native_seq_replace [] pat repl))) := by
  cases pat with
  | nil =>
      cases repl with
      | nil =>
          simp [native_seq_replace_empty_src, native_seq_contains_nil, native_veq,
            native_pack_seq]
      | cons r rs =>
          simp [native_seq_replace_empty_src, native_seq_contains, native_seq_indexof_eq_rec,
            native_veq, native_pack_seq]
  | cons p ps =>
      have hReplace : native_seq_replace [] (p :: ps) repl = [] := by
        simp [native_seq_replace_empty_src]
      rw [hReplace]
      simp [native_seq_contains_nil, native_veq, native_pack_seq]

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

private theorem prog_str_replace_emp_ctn_src_info
    (s t emp P : Term)
    (hProg : __eo_prog_str_replace_emp_ctn_src s t emp (Proof.pf P) ≠
      Term.Stuck) :
    ∃ emp0,
      P = replaceEmpCtnSrcPremise emp0 ∧
      emp0 = emp ∧
      __eo_prog_str_replace_emp_ctn_src s t emp (Proof.pf P) =
        replaceEmpCtnSrcConclusion s t emp := by
  unfold __eo_prog_str_replace_emp_ctn_src at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hemp :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_emp_ctn_src, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      replaceEmpCtnSrcConclusion, replaceEmpCtnSrcLhs,
      replaceEmpCtnSrcRhs, replaceEmpCtnSrcRepl]

private theorem typed___eo_prog_str_replace_emp_ctn_src_impl
    (s t emp P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_replace_emp_ctn_src s t emp (Proof.pf P) =
        replaceEmpCtnSrcConclusion s t emp) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_emp_ctn_src s t emp (Proof.pf P)) := by
  let repl := replaceEmpCtnSrcRepl s t emp
  let lhs := replaceEmpCtnSrcLhs s t emp
  let rhs := replaceEmpCtnSrcRhs s t emp
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hReplSmtTy :
      __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt emp) (__eo_to_smt s)
          (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_replace_eq]
    simp [hEmpSmtTy, hSSmtTy, hTSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hReplTy :
      __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [repl, replaceEmpCtnSrcRepl, __eo_to_smt, __eo_to_smt_type, __smtx_typeof] using hReplSmtTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt s)
          (SmtTerm.str_replace (__eo_to_smt emp) (__eo_to_smt s)
            (__eo_to_smt t))) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hSSmtTy, hReplSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.eq (__eo_to_smt emp)
          (SmtTerm.str_replace (__eo_to_smt emp) (__eo_to_smt s)
            (__eo_to_smt t))) =
      SmtType.Bool
    rw [typeof_eq_eq]
    simp [hEmpSmtTy, hReplSmtTy, __smtx_typeof_eq, __smtx_typeof_guard,
      native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [replaceEmpCtnSrcConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_replace_emp_ctn_src_impl
    (M : SmtModel) (hM : model_wf M) (s t emp P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replaceEmpCtnSrcPremise emp) true)
    (hProgEq :
      __eo_prog_str_replace_emp_ctn_src s t emp (Proof.pf P) =
        replaceEmpCtnSrcConclusion s t emp) :
    eo_interprets M
      (__eo_prog_str_replace_emp_ctn_src s t emp (Proof.pf P)) true := by
  let repl := replaceEmpCtnSrcRepl s t emp
  let lhs := replaceEmpCtnSrcLhs s t emp
  let rhs := replaceEmpCtnSrcRhs s t emp
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, replaceEmpCtnSrcConclusion, lhs, rhs] using
      typed___eo_prog_str_replace_emp_ctn_src_impl s t emp P
        hSTrans hTTrans hEmpTrans hSTy hTTy hEmpTy hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hEmpEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt emp)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hEmpSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt emp) (by
        unfold term_has_non_none_type
        rw [hEmpSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hEmpEvalTy with ⟨emps, hEmpEval⟩
  have hEmpLenZero : native_seq_len (native_unpack_seq emps) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt emp)) (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hEmpEval] at hEval
        rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
          rw [__smtx_model_eval.eq_def]] at hEval
        simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq]
          using hEval
  have hEmpNil : native_unpack_seq emps = [] :=
    list_eq_nil_of_native_seq_len_zero (native_unpack_seq emps) hEmpLenZero
  have hEmpSeqTy :
      __smtx_typeof_seq_value emps = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hEmpEval] using hEmpEvalTy
  have hEmpElem : __smtx_elem_typeof_seq_value emps = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hEmpSeqTy
  have hEmpPack :
      emps =
        native_pack_seq (__smtx_elem_typeof_seq_value emps) [] := by
    rw [← hEmpNil]
    exact (native_pack_unpack_seq emps).symm
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    have hNative :=
      native_seq_contains_replace_empty_src_eq_empty_eq
        (__eo_to_smt_type T) (native_unpack_seq ss) (native_unpack_seq ts)
    change __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt s)
          (SmtTerm.str_replace (__eo_to_smt emp) (__eo_to_smt s)
            (__eo_to_smt t))) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt emp)
          (SmtTerm.str_replace (__eo_to_smt emp) (__eo_to_smt s)
            (__eo_to_smt t)))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_eq_term_eq,
      smtx_eval_str_replace_term_eq]
    rw [hSEval, hTEval, hEmpEval]
    simp only [__smtx_model_eval_str_contains, __smtx_model_eval_str_replace,
      __smtx_model_eval_eq]
    rw [hEmpPack, hEmpElem]
    simp [hEmpNil, Smtm.native_unpack_pack_seq, hNative, native_pack_seq,
      native_unpack_seq, __smtx_elem_typeof_seq_value, elem_typeof_pack_seq]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_emp_ctn_src_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_emp_ctn_src args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_emp_ctn_src args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_emp_ctn_src args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_emp_ctn_src args premises ≠
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
                  | cons n premises =>
                      cases premises with
                      | nil =>
                          let P := __eo_state_proven_nth s n
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
                              (__eo_prog_str_replace_emp_ctn_src a1 a2 a3
                                (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_replace_emp_ctn_src a1 a2 a3
                                  (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_replace_emp_ctn_src_info
                              a1 a2 a3 P hProgRule with
                            ⟨emp0, hPremShape, hemp0, hProgEq⟩
                          subst emp0
                          let lhs := replaceEmpCtnSrcLhs a1 a2 a3
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs)
                              (__eo_typeof (replaceEmpCtnSrcRhs a1 a2 a3)) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs)
                              (__eo_typeof (replaceEmpCtnSrcRhs a1 a2 a3))
                              hResultTy).1
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Apply Term.Seq T := by
                            change __eo_typeof_str_contains (__eo_typeof a1)
                                (__eo_typeof (replaceEmpCtnSrcRepl a1 a2 a3)) ≠
                              Term.Stuck at hLhsNotStuck
                            rcases eo_typeof_str_contains_args_of_ne_stuck
                                (__eo_typeof a1)
                                (__eo_typeof (replaceEmpCtnSrcRepl a1 a2 a3))
                                hLhsNotStuck with
                              ⟨T, hA1Ty, hReplTy⟩
                            have hReplNotStuck :
                                __eo_typeof (replaceEmpCtnSrcRepl a1 a2 a3) ≠
                                  Term.Stuck := by
                              rw [hReplTy]
                              simp
                            change __eo_typeof_str_replace (__eo_typeof a3)
                                (__eo_typeof a1) (__eo_typeof a2) ≠
                              Term.Stuck at hReplNotStuck
                            rcases eo_typeof_str_replace_args_of_ne_stuck
                                (__eo_typeof a3) (__eo_typeof a1)
                                (__eo_typeof a2) hReplNotStuck with
                              ⟨U, hA3Ty, hA1Ty', hA2Ty⟩
                            rw [hA1Ty] at hA1Ty'
                            cases hA1Ty'
                            exact ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          rcases hArgTypes with ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M (replaceEmpCtnSrcPremise a3)
                                  true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_replace_emp_ctn_src_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_replace_emp_ctn_src_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hA1Ty hA2Ty hA3Ty hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
