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

private abbrev substrLenNormPremise (m s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq m) (Term.Apply Term.str_len s)))
    (Term.Boolean true)

private abbrev substrLenNormLhs (s n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m

private abbrev substrLenNormRhs (s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n)
    (Term.Apply Term.str_len s)

private abbrev substrLenNormConclusion (s n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrLenNormLhs s n m))
    (substrLenNormRhs s n)

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

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_extract_len_norm
    (xs : List SmtValue) (i m : native_Int)
    (hLen : native_seq_len xs <= m) :
    native_seq_extract xs i m =
      native_seq_extract xs i (native_seq_len xs) := by
  have hLenInt : (Int.ofNat xs.length : native_Int) <= m := by
    simpa [native_seq_len] using hLen
  unfold native_seq_extract
  by_cases hEmpty : xs.length = 0
  · have hLen0 : (Int.ofNat xs.length : native_Int) = 0 := by
      simp [hEmpty]
    by_cases hiNeg : i < 0
    · simp [hLen0, hiNeg]
    · have hiNonneg : 0 <= i := int_nonneg_of_not_neg hiNeg
      have hiGe : i >= (Int.ofNat xs.length : native_Int) := by
        rw [hLen0]
        exact hiNonneg
      have hGeLen : (Int.ofNat xs.length : native_Int) <= i := by
        simpa [ge_iff_le] using hiGe
      have hGeLen' : (↑xs.length : native_Int) <= i := by
        simpa using hGeLen
      have hXsNil : xs = [] := List.eq_nil_of_length_eq_zero hEmpty
      simp [native_seq_len, hLen0, hiNeg, hGeLen', hXsNil]
  · have hLenPos : (0 : native_Int) < Int.ofNat xs.length := by
      exact Int.ofNat_lt.mpr (Nat.pos_of_ne_zero hEmpty)
    by_cases hiNeg : i < 0
    · simp [hiNeg]
    · have hiNonneg : 0 <= i := int_nonneg_of_not_neg hiNeg
      by_cases hiGe : i >= (Int.ofNat xs.length : native_Int)
      · have hGeLen : (Int.ofNat xs.length : native_Int) <= i := by
          simpa [ge_iff_le] using hiGe
        have hGeLen' : (↑xs.length : native_Int) <= i := by
          simpa using hGeLen
        simp [native_seq_len, hiNeg, hGeLen']
      · have hiLt : i < (Int.ofNat xs.length : native_Int) :=
          Int.lt_of_not_ge hiGe
        have hNotGeLen : ¬ (Int.ofNat xs.length : native_Int) <= i := by
          simpa [ge_iff_le] using hiGe
        have hNotGeLen' : ¬ (↑xs.length : native_Int) <= i := by
          simpa using hNotGeLen
        have hmPos : (0 : native_Int) < m :=
          Int.lt_of_lt_of_le hLenPos hLenInt
        have hmNotNonpos : ¬ m <= 0 := by
          intro hm
          exact (Int.lt_irrefl 0) (Int.lt_of_lt_of_le hmPos hm)
        have hLenNotNonpos :
            ¬ (Int.ofNat xs.length : native_Int) <= 0 :=
          by
            intro hle
            exact (Int.lt_irrefl 0) (Int.lt_of_lt_of_le hLenPos hle)
        have hDiffLeLen :
            (Int.ofNat xs.length : native_Int) - i <=
              Int.ofNat xs.length :=
          Int.sub_le_self _ hiNonneg
        have hDiffLeM :
            (Int.ofNat xs.length : native_Int) - i <= m :=
          Int.le_trans hDiffLeLen hLenInt
        have hMinM :
            min m ((Int.ofNat xs.length : native_Int) - i) =
              (Int.ofNat xs.length : native_Int) - i :=
          Int.min_eq_right hDiffLeM
        have hMinLen :
            min (Int.ofNat xs.length : native_Int)
                ((Int.ofNat xs.length : native_Int) - i) =
              (Int.ofNat xs.length : native_Int) - i :=
          Int.min_eq_right hDiffLeLen
        have hMinM' :
            min m ((↑xs.length : native_Int) - i) =
              (↑xs.length : native_Int) - i := by
          simpa using hMinM
        have hMinLen' :
            min (↑xs.length : native_Int)
                ((↑xs.length : native_Int) - i) =
              (↑xs.length : native_Int) - i := by
          simpa using hMinLen
        have hXsNotNil : xs ≠ [] := by
          intro hNil
          apply hEmpty
          simp [hNil]
        simp [native_seq_len, hiNeg, hmNotNonpos, hLenNotNonpos,
          hMinM', hMinLen', hNotGeLen', hXsNotNil]

private theorem prog_str_substr_len_norm_info
    (s n m P : Term)
    (hProg : __eo_prog_str_substr_len_norm s n m (Proof.pf P) ≠
      Term.Stuck) :
    ∃ m0 s0,
      P = substrLenNormPremise m0 s0 ∧
      m0 = m ∧
      s0 = s ∧
      __eo_prog_str_substr_len_norm s n m (Proof.pf P) =
        substrLenNormConclusion s n m := by
  unfold __eo_prog_str_substr_len_norm at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg with
      ⟨hm, hs⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_len_norm, __eo_requires, __eo_and, __eo_eq,
      SmtEval.native_ite, native_teq, native_and, SmtEval.native_not,
      substrLenNormConclusion, substrLenNormLhs, substrLenNormRhs]

private theorem typed___eo_prog_str_substr_len_norm_impl
    (s n m P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧ __eo_typeof m = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_len_norm s n m (Proof.pf P) =
        substrLenNormConclusion s n m) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_len_norm s n m (Proof.pf P)) := by
  rcases hTy with ⟨T, hSTy, hNTy, hMTy⟩
  let lhs := substrLenNormLhs s n m
  let rhs := substrLenNormRhs s n
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hLenTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int := by
    rw [typeof_str_len_eq, hSSmtTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt m)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr,
      __smtx_typeof.eq_def]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (SmtTerm.str_len (__eo_to_smt s))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, hLenTy, __smtx_typeof_str_substr,
      __smtx_typeof.eq_def]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [substrLenNormConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_substr_len_norm_impl
    (M : SmtModel) (hM : model_wf M) (s n m P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧ __eo_typeof m = Term.Int)
    (hPrem : eo_interprets M (substrLenNormPremise m s) true)
    (hProgEq :
      __eo_prog_str_substr_len_norm s n m (Proof.pf P) =
        substrLenNormConclusion s n m) :
    eo_interprets M
      (__eo_prog_str_substr_len_norm s n m (Proof.pf P)) true := by
  rcases hTy with ⟨T, hSTy, hNTy, hMTy⟩
  let lhs := substrLenNormLhs s n m
  let rhs := substrLenNormRhs s n
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, substrLenNormConclusion, lhs, rhs] using
      typed___eo_prog_str_substr_len_norm_impl s n m P
        hSTrans hNTrans hMTrans ⟨T, hSTy, hNTy, hMTy⟩ hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
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
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hLenLeM :
      native_seq_len (native_unpack_seq ss) <= mi := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt m)
                (SmtTerm.str_len (__eo_to_smt s)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq, hMEval,
          smtx_eval_str_len_term_eq, hSEval,
          smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq (native_seq_len (native_unpack_seq ss)) mi = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq]
            using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt m)) =
      __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (SmtTerm.str_len (__eo_to_smt s)))
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_substr_term_eq]
    rw [hSEval, hNEval, hMEval, smtx_eval_str_len_term_eq, hSEval]
    simp [__smtx_model_eval_str_substr, __smtx_model_eval_str_len,
      native_seq_extract_len_norm _ _ _ hLenLeM]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_len_norm_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_len_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_len_norm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_len_norm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_len_norm args premises ≠
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
                              (__eo_prog_str_substr_len_norm a1 a2 a3
                                (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_substr_len_norm a1 a2 a3
                                  (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_substr_len_norm_info
                              a1 a2 a3 P hProgRule with
                            ⟨m0, s0, hPremShape, hm0, hs0, hProgEq⟩
                          subst m0
                          subst s0
                          let lhs := substrLenNormLhs a1 a2 a3
                          let rhs := substrLenNormRhs a1 a2
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
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
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (substrLenNormPremise a3 a1) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_substr_len_norm_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hArgTypes hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_substr_len_norm_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hArgTypes hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
