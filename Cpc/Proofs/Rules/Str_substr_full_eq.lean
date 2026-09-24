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

private abbrev substrFullEqPremise (s n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len s))
    n

private abbrev substrFullEqLhs (s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) n

private abbrev substrFullEqConclusion (s n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrFullEqLhs s n)) s

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

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_extract_zero_nat_any
    (xs : List SmtValue) (n : Nat) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  by_cases hle : n <= xs.length
  · exact native_seq_extract_zero_nat xs n hle
  · cases xs with
    | nil =>
        simp [native_seq_extract]
    | cons x xs =>
        unfold native_seq_extract
        have hn : n ≠ 0 := by
          intro hn
          subst n
          simp at hle
        have hLenLt : (x :: xs).length < n := Nat.lt_of_not_ge hle
        have hLenLe : (x :: xs).length <= n := Nat.le_of_lt hLenLt
        have hLenNotLe :
            ¬ ((Int.ofNat xs.length : Int) + 1 <= 0) := by
          have hNonneg : (0 : Int) <= Int.ofNat xs.length :=
            Int.natCast_nonneg xs.length
          omega
        have hmin :
            min (Int.ofNat n) (Int.ofNat (x :: xs).length) =
              Int.ofNat (x :: xs).length :=
          Int.min_eq_right (Int.ofNat_le.mpr hLenLe)
        have hminToNat :
            (min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat =
              (x :: xs).length := by
          rw [hmin]
          simp
        simp [hn]
        change
          (x :: xs).take
              ((min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat) =
            (x :: xs).take n
        rw [hminToNat, List.take_of_length_le (Nat.le_refl (x :: xs).length),
          List.take_of_length_le hLenLe]

private theorem native_seq_extract_zero_of_len_le
    (xs : List SmtValue) (n : native_Int)
    (hLen : (Int.ofNat xs.length : Int) <= n) :
    native_seq_extract xs 0 n = xs := by
  have hnNonneg : 0 <= n :=
    Int.le_trans (Int.natCast_nonneg xs.length) hLen
  let k := Int.toNat n
  have hnEq : n = Int.ofNat k := by
    exact (Int.toNat_of_nonneg hnNonneg).symm
  have hLenLeK : xs.length <= k := by
    apply Int.ofNat_le.mp
    simpa [hnEq] using hLen
  rw [hnEq]
  calc
    native_seq_extract xs 0 (Int.ofNat k) = xs.take k := by
      exact native_seq_extract_zero_nat_any xs k
    _ = xs := List.take_of_length_le hLenLeK

private theorem prog_str_substr_full_eq_info
    (s n P : Term)
    (hProg : __eo_prog_str_substr_full_eq s n (Proof.pf P) ≠ Term.Stuck) :
    ∃ s0 n0,
      P = substrFullEqPremise s0 n0 ∧
      s0 = s ∧
      n0 = n ∧
      __eo_prog_str_substr_full_eq s n (Proof.pf P) =
        substrFullEqConclusion s n := by
  unfold __eo_prog_str_substr_full_eq at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg with
      ⟨hn, hs⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_full_eq, __eo_requires, __eo_and, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not, SmtEval.native_and,
      substrFullEqPremise, substrFullEqConclusion, substrFullEqLhs]

private theorem typed___eo_prog_str_substr_full_eq_impl
    (s n P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_full_eq s n (Proof.pf P) =
        substrFullEqConclusion s n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_full_eq s n (Proof.pf P)) := by
  let lhs := substrFullEqLhs s n
  let rhs := s
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
          (__eo_to_smt n)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, __smtx_typeof_str_substr,
      __smtx_typeof.eq_def]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [rhs] using hSSmtTy
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_str_substr_full_eq_impl
    (M : SmtModel) (hM : model_wf M) (s n P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPrem : eo_interprets M (substrFullEqPremise s n) true)
    (hProgEq :
      __eo_prog_str_substr_full_eq s n (Proof.pf P) =
        substrFullEqConclusion s n) :
    eo_interprets M (__eo_prog_str_substr_full_eq s n (Proof.pf P)) true := by
  let lhs := substrFullEqLhs s n
  let rhs := s
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, lhs, rhs, substrFullEqConclusion] using
      typed___eo_prog_str_substr_full_eq_impl s n P hSTrans hNTrans
        hSTy hNTy hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
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
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hLenLeN :
      (Int.ofNat (native_unpack_seq ss).length : Int) <= ni := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s)) (__eo_to_smt n)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hSEval,
          hNEval] at hEval
        have hLenEq :
            (Int.ofNat (native_unpack_seq ss).length : Int) = ni := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        rw [hLenEq]
        exact Int.le_refl ni
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hSEvalTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hSPack :
      native_pack_seq (__smtx_elem_typeof_seq_value ss) (native_unpack_seq ss) =
        ss :=
    native_pack_unpack_seq ss
  have hExtract :
      native_seq_extract (native_unpack_seq ss) 0 ni = native_unpack_seq ss :=
    native_seq_extract_zero_of_len_le (native_unpack_seq ss) ni hLenLeN
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
          (__eo_to_smt n)) =
      __smtx_model_eval M (__eo_to_smt s)
    rw [smtx_eval_str_substr_term_eq, hSEval, smtx_eval_numeral_term_eq,
      hNEval]
    simp [__smtx_model_eval_str_substr, hExtract, hSElem]
    rw [← hSElem]
    exact hSPack
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_full_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_full_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_full_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_full_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_full_eq args premises ≠
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
                      change __eo_typeof
                          (__eo_prog_str_substr_full_eq a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_substr_full_eq a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_substr_full_eq_info a1 a2 P hProgRule with
                        ⟨s0, n0, hPremShape, hs0, hn0, hProgEq⟩
                      subst s0
                      subst n0
                      let lhs := substrFullEqLhs a1 a2
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof a1) =
                        Term.Bool at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs) (__eo_typeof a1) hResultTy).1
                      have hArgTypes :
                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                            __eo_typeof (Term.Numeral 0) = Term.Int ∧
                            __eo_typeof a2 = Term.Int := by
                        change __eo_typeof_str_substr (__eo_typeof a1)
                            (__eo_typeof (Term.Numeral 0)) (__eo_typeof a2) ≠
                              Term.Stuck at hLhsNotStuck
                        exact eo_typeof_str_substr_args_of_ne_stuck
                          (__eo_typeof a1) (__eo_typeof (Term.Numeral 0))
                          (__eo_typeof a2) hLhsNotStuck
                      rcases hArgTypes with ⟨T, hA1Ty, _hZeroTy, hA2Ty⟩
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPremRaw : eo_interprets M P true :=
                          hTrue P (by simp [P, premiseTermList])
                        have hPrem :
                            eo_interprets M (substrFullEqPremise a1 a2) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_substr_full_eq_impl M hM a1 a2 P
                          hA1Trans hA2Trans hA1Ty hA2Ty hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_substr_full_eq_impl a1 a2 P
                            hA1Trans hA2Trans hA1Ty hA2Ty hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
