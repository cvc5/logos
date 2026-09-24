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

private abbrev indexofFindEmpPremiseEmpty (emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len emp))
    (Term.Numeral 0)

private abbrev indexofFindEmpPremiseLenGe (t n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len t)) n))
    (Term.Boolean true)

private abbrev indexofFindEmpPremiseNGe (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev indexofFindEmpLhs (t emp n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) emp) n

private abbrev indexofFindEmpConclusion (t emp n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (indexofFindEmpLhs t emp n)) n

private theorem eo_and_eq_true_parts
    (A B : Term)
    (h : __eo_and A B = Term.Boolean true) :
    A = Term.Boolean true ∧ B = Term.Boolean true := by
  cases A <;> cases B <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean =>
    exact h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;>
      simp [__eo_requires, hw, native_teq, native_ite,
        SmtEval.native_not] at h

private theorem eqs4_of_requires_nested_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term)
    (h :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4))
        (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  have hProg := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg
  have hTop := eo_and_eq_true_parts _ _ hProg.1
  have hMid := eo_and_eq_true_parts _ _ hTop.1
  have hBot := eo_and_eq_true_parts _ _ hMid.1
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 hBot.1,
    RuleProofs.eq_of_eo_eq_true x2 y2 hBot.2,
    RuleProofs.eq_of_eo_eq_true x3 y3 hMid.2,
    RuleProofs.eq_of_eo_eq_true x4 y4 hTop.2⟩

private theorem eo_typeof_str_indexof_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_indexof A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Apply Term.Seq T ∧
      C = Term.Int := by
  cases A <;> simp [__eo_typeof_str_indexof] at h ⊢
  case Apply fA aA =>
    cases fA <;> simp at h ⊢
    case UOp opA =>
      cases opA <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case Apply fB aB =>
          cases fB <;> simp at h ⊢
          case UOp opB =>
            cases opB <;> simp at h ⊢
            case Seq =>
              cases C <;> simp at h ⊢
              case UOp opC =>
                cases opC <;> simp at h ⊢
                case Int =>
                  have hCond : __eo_eq aA aB = Term.Boolean true :=
                    support_eo_requires_cond_eq_of_non_stuck h
                  have hBA : aB = aA :=
                    support_eq_of_eo_eq_true aA aB hCond
                  subst aB
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

private theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_len_find_emp_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_len x) =
      __smtx_model_eval_str_len (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_prefix_eq_nil_left (xs : List SmtValue) :
    native_seq_prefix_eq [] xs = true := by
  cases xs <;> rfl

private theorem native_seq_indexof_rec_empty_succ
    (xs : List SmtValue) (i fuel : Nat) :
    native_seq_indexof_rec xs [] i (fuel + 1) = Int.ofNat i := by
  unfold native_seq_indexof_rec
  rw [if_pos (native_seq_prefix_eq_nil_left xs)]

private theorem native_seq_indexof_empty_of_bounds
    (xs : List SmtValue) (i : native_Int)
    (hNonneg : 0 ≤ i)
    (hLeLen : i ≤ native_seq_len xs) :
    native_seq_indexof xs [] i = i := by
  unfold native_seq_indexof
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
  have hToNat : (Int.toNat i : Int) = i :=
    Int.toNat_of_nonneg hNonneg
  have hStartLeInt : (Int.toNat i : Int) ≤ (xs.length : Int) := by
    simpa [hToNat, native_seq_len] using hLeLen
  have hStartLeNat : Int.toNat i ≤ xs.length :=
    Int.ofNat_le.mp hStartLeInt
  have hBounds : Int.toNat i + 0 ≤ xs.length := by
    simpa using hStartLeNat
  simp [hNotNeg, hBounds]
  rw [native_seq_indexof_rec_empty_succ]
  rw [if_pos (by simpa [native_seq_len] using hLeLen)]
  exact hToNat

private theorem list_eq_nil_of_native_seq_len_zero
    (xs : List SmtValue)
    (h : native_seq_len xs = 0) :
    xs = [] := by
  have hLenInt : (xs.length : Int) = 0 := by
    simpa [native_seq_len] using h
  have hLenNat : xs.length = 0 := by
    omega
  cases xs with
  | nil => rfl
  | cons _ _ => simp at hLenNat

private theorem prog_str_indexof_find_emp_info
    (t emp n P1 P2 P3 : Term)
    (hProg :
      __eo_prog_str_indexof_find_emp t emp n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠
        Term.Stuck) :
    ∃ emp0 t0 n0 n1,
      P1 = indexofFindEmpPremiseEmpty emp0 ∧
      P2 = indexofFindEmpPremiseLenGe t0 n0 ∧
      P3 = indexofFindEmpPremiseNGe n1 ∧
      emp0 = emp ∧
      t0 = t ∧
      n0 = n ∧
      n1 = n ∧
      __eo_prog_str_indexof_find_emp t emp n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        indexofFindEmpConclusion t emp n := by
  unfold __eo_prog_str_indexof_find_emp at hProg
  split at hProg <;> try contradiction
  next hP1 hP2 hP3 =>
    cases hP1
    cases hP2
    cases hP3
    rcases eqs4_of_requires_nested_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ hProg with
      ⟨hemp, ht, hn0, hn1⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_find_emp, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, indexofFindEmpConclusion, indexofFindEmpLhs]

private theorem typed___eo_prog_str_indexof_find_emp_impl
    (t emp n P1 P2 P3 : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof emp = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int)
    (hProgEq :
      __eo_prog_str_indexof_find_emp t emp n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        indexofFindEmpConclusion t emp n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_indexof_find_emp t emp n
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) := by
  rcases hTy with ⟨T, hTTy, hEmpTy, hNTy⟩
  let lhs := indexofFindEmpLhs t emp n
  let rhs := n
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt emp)
          (__eo_to_smt n)) =
      SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hTSmtTy, hEmpSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hNSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [indexofFindEmpConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_indexof_find_emp_impl
    (M : SmtModel) (hM : model_wf M)
    (t emp n P1 P2 P3 : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof emp = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int)
    (hPremEmpty : eo_interprets M (indexofFindEmpPremiseEmpty emp) true)
    (hPremLenGe : eo_interprets M (indexofFindEmpPremiseLenGe t n) true)
    (hPremNGe : eo_interprets M (indexofFindEmpPremiseNGe n) true)
    (hProgEq :
      __eo_prog_str_indexof_find_emp t emp n
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        indexofFindEmpConclusion t emp n) :
    eo_interprets M
      (__eo_prog_str_indexof_find_emp t emp n
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) true := by
  rcases hTy with ⟨T, hTTy, hEmpTy, hNTy⟩
  let lhs := indexofFindEmpLhs t emp n
  let rhs := n
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, indexofFindEmpConclusion, lhs, rhs] using
      typed___eo_prog_str_indexof_find_emp_impl t emp n P1 P2 P3
        hTTrans hEmpTrans hNTrans ⟨T, hTTy, hEmpTy, hNTy⟩ hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
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
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hEmpEvalTy with ⟨es, hEmpEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hEmpLenZero :
      native_seq_len (native_unpack_seq es) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremEmpty
    cases hPremEmpty with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt emp))
              (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_find_emp_term_eq,
          hEmpEval, smtx_eval_numeral_term_eq] at hEval
        simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
          native_veq] using hEval
  have hEmpNil : native_unpack_seq es = [] :=
    list_eq_nil_of_native_seq_len_zero (native_unpack_seq es) hEmpLenZero
  have hNLeLen :
      ni ≤ native_seq_len (native_unpack_seq ts) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremLenGe
    cases hPremLenGe with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt t))
                (__eo_to_smt n))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_find_emp_term_eq, hTEval, hNEval,
          smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
          __smtx_model_eval_str_len, __smtx_model_eval_eq,
          native_veq, native_zleq] using hEval
  have hNNonneg : 0 ≤ ni := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremNGe
    cases hPremNGe with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          hNEval, smtx_eval_numeral_term_eq,
          smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
          __smtx_model_eval_eq, native_veq, native_zleq] using hEval
  have hIndexof :
      native_seq_indexof (native_unpack_seq ts) (native_unpack_seq es) ni = ni := by
    rw [hEmpNil]
    exact native_seq_indexof_empty_of_bounds
      (native_unpack_seq ts) ni hNNonneg hNLeLen
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt emp)
          (__eo_to_smt n)) =
      __smtx_model_eval M (__eo_to_smt n)
    rw [smtx_eval_str_indexof_term_eq, hTEval, hEmpEval, hNEval]
    simp [__smtx_model_eval_str_indexof, hIndexof]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_indexof_find_emp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_find_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_find_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_find_emp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_find_emp args premises ≠
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
                  | cons i1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons i2 premises =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons i3 premises =>
                              cases premises with
                              | nil =>
                                  let P1 := __eo_state_proven_nth s i1
                                  let P2 := __eo_state_proven_nth s i2
                                  let P3 := __eo_state_proven_nth s i3
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
                                      (__eo_prog_str_indexof_find_emp a1 a2 a3
                                        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) =
                                    Term.Bool at hResultTy
                                  have hProgRule :
                                      __eo_prog_str_indexof_find_emp a1 a2 a3
                                          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_indexof_find_emp_info
                                      a1 a2 a3 P1 P2 P3 hProgRule with
                                    ⟨emp0, t0, n0, n1, hP1Shape, hP2Shape,
                                      hP3Shape, hemp0, ht0, hn0, hn1, hProgEq⟩
                                  subst emp0
                                  subst t0
                                  subst n0
                                  subst n1
                                  let lhs := indexofFindEmpLhs a1 a2 a3
                                  let rhs := a3
                                  rw [hProgEq] at hResultTy
                                  change __eo_typeof_eq (__eo_typeof lhs)
                                      (__eo_typeof rhs) =
                                    Term.Bool at hResultTy
                                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                                  have hArgTypes :
                                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                        __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                        __eo_typeof a3 = Term.Int := by
                                    change __eo_typeof_str_indexof (__eo_typeof a1)
                                        (__eo_typeof a2) (__eo_typeof a3) ≠
                                      Term.Stuck at hLhsNotStuck
                                    exact eo_typeof_str_indexof_args_of_ne_stuck
                                      (__eo_typeof a1) (__eo_typeof a2)
                                      (__eo_typeof a3) hLhsNotStuck
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem1Raw : eo_interprets M P1 true :=
                                      hTrue P1 (by simp [P1, premiseTermList])
                                    have hPrem2Raw : eo_interprets M P2 true :=
                                      hTrue P2 (by simp [P2, premiseTermList])
                                    have hPrem3Raw : eo_interprets M P3 true :=
                                      hTrue P3 (by simp [P3, premiseTermList])
                                    have hPrem1 :
                                        eo_interprets M
                                          (indexofFindEmpPremiseEmpty a2) true := by
                                      simpa [hP1Shape] using hPrem1Raw
                                    have hPrem2 :
                                        eo_interprets M
                                          (indexofFindEmpPremiseLenGe a1 a3) true := by
                                      simpa [hP2Shape] using hPrem2Raw
                                    have hPrem3 :
                                        eo_interprets M
                                          (indexofFindEmpPremiseNGe a3) true := by
                                      simpa [hP3Shape] using hPrem3Raw
                                    exact facts___eo_prog_str_indexof_find_emp_impl
                                      M hM a1 a2 a3 P1 P2 P3
                                      hA1Trans hA2Trans hA3Trans hArgTypes
                                      hPrem1 hPrem2 hPrem3 hProgEq
                                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (typed___eo_prog_str_indexof_find_emp_impl
                                        a1 a2 a3 P1 P2 P3
                                        hA1Trans hA2Trans hA3Trans
                                        hArgTypes hProgEq)
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
