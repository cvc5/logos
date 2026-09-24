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

private abbrev prefixEqPremise (s t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s))
        (Term.Apply Term.str_len t)))
    (Term.Boolean true)

private abbrev prefixEqLhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.str_prefixof s) t

private abbrev prefixEqRhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq s) t

private abbrev prefixEqConclusion (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (prefixEqLhs s t)) (prefixEqRhs s t)

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

private theorem smtx_eval_str_prefixof_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_prefixof x y) =
      __smtx_model_eval_str_prefixof
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
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

private theorem eval_str_prefixof_seq_eq_of_len_ge
    (sx sy : SmtSeq)
    (hLen :
      (native_unpack_seq sy).length <= (native_unpack_seq sx).length) :
    __smtx_model_eval_str_prefixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      __smtx_model_eval_eq (SmtValue.Seq sx) (SmtValue.Seq sy) := by
  let xs := native_unpack_seq sx
  let ys := native_unpack_seq sy
  have hExtract :
      native_seq_extract ys 0 (Int.ofNat xs.length) = ys := by
    calc
      native_seq_extract ys 0 (Int.ofNat xs.length) = ys.take xs.length := by
        simpa [xs, ys] using native_seq_extract_zero_nat_any ys xs.length
      _ = ys := List.take_of_length_le (by simpa [xs, ys] using hLen)
  have hPack :
      native_pack_seq (__smtx_elem_typeof_seq_value sy) ys = sy := by
    simpa [ys] using native_pack_unpack_seq sy
  simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
    __smtx_model_eval_str_substr, native_seq_len, xs, ys, hExtract, hPack]
  change __smtx_model_eval_eq (SmtValue.Seq sx)
      (SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value sy)
          (native_seq_extract ys 0 (Int.ofNat xs.length)))) =
    __smtx_model_eval_eq (SmtValue.Seq sx) (SmtValue.Seq sy)
  rw [hExtract, hPack]

private theorem prog_str_prefixof_eq_info
    (s t P : Term)
    (hProg : __eo_prog_str_prefixof_eq s t (Proof.pf P) ≠ Term.Stuck) :
    ∃ s0 t0,
      P = prefixEqPremise s0 t0 ∧
      s0 = s ∧
      t0 = t ∧
      __eo_prog_str_prefixof_eq s t (Proof.pf P) =
        prefixEqConclusion s t := by
  unfold __eo_prog_str_prefixof_eq at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hEq :=
      RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg
    rcases hEq with ⟨hs, ht⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_prefixof_eq, __eo_requires, __eo_eq, __eo_and,
      SmtEval.native_ite, native_teq, native_and, SmtEval.native_not,
      prefixEqConclusion, prefixEqLhs, prefixEqRhs]

private theorem typed___eo_prog_str_prefixof_eq_impl
    (s t P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_prefixof_eq s t (Proof.pf P) =
        prefixEqConclusion s t) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_prefixof_eq s t (Proof.pf P)) := by
  rcases hTy with ⟨T, hSTy, hTTy⟩
  let lhs := prefixEqLhs s t
  let rhs := prefixEqRhs s t
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_prefixof (__eo_to_smt s) (__eo_to_smt t)) =
      SmtType.Bool
    rw [typeof_str_prefixof_eq]
    simp [hSSmtTy, hTSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy : RuleProofs.eo_has_bool_type rhs := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type s t
      (by rw [hSSmtTy, hTSmtTy]) (by rw [hSSmtTy]; simp)
  have hRhsSmtTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := hRhsTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [prefixEqConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_prefixof_eq_impl
    (M : SmtModel) (hM : model_wf M) (s t P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (prefixEqPremise s t) true)
    (hProgEq :
      __eo_prog_str_prefixof_eq s t (Proof.pf P) =
        prefixEqConclusion s t) :
    eo_interprets M (__eo_prog_str_prefixof_eq s t (Proof.pf P)) true := by
  rcases hTy with ⟨T, hSTy, hTTy⟩
  let lhs := prefixEqLhs s t
  let rhs := prefixEqRhs s t
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, prefixEqConclusion, lhs, rhs] using
      typed___eo_prog_str_prefixof_eq_impl s t P hSTrans hTTrans
        ⟨T, hSTy, hTTy⟩ hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
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
  rcases seq_value_canonical hSEvalTy with ⟨sx, hSEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨sy, hTEval⟩
  have hLen :
      (native_unpack_seq sy).length <= (native_unpack_seq sx).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt s))
                (SmtTerm.str_len (__eo_to_smt t)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
          hSEval, hTEval, smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq (Int.ofNat (native_unpack_seq sy).length)
              (Int.ofNat (native_unpack_seq sx).length) = true := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq,
            native_seq_len] using hEval
        have hLeInt :
            (Int.ofNat (native_unpack_seq sy).length : Int) <=
              Int.ofNat (native_unpack_seq sx).length := by
          simpa [native_zleq] using hLeBool
        exact Int.ofNat_le.mp hLeInt
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_prefixof (__eo_to_smt s) (__eo_to_smt t)) =
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt t))
    rw [smtx_eval_str_prefixof_term_eq, smtx_eval_eq_term_eq,
      hSEval, hTEval]
    exact eval_str_prefixof_seq_eq_of_len_ge sx sy hLen
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_prefixof_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_prefixof_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_prefixof_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_prefixof_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_prefixof_eq args premises ≠
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
                      change __eo_typeof
                          (__eo_prog_str_prefixof_eq a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_prefixof_eq a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_prefixof_eq_info a1 a2 P hProgRule with
                        ⟨s0, t0, hPremShape, hs0, ht0, hProgEq⟩
                      subst s0
                      subst t0
                      let lhs := prefixEqLhs a1 a2
                      let rhs := prefixEqRhs a1 a2
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                        Term.Bool at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                      have hArgTypes :
                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                            __eo_typeof a2 = Term.Apply Term.Seq T := by
                        change __eo_typeof_str_contains (__eo_typeof a1)
                            (__eo_typeof a2) ≠ Term.Stuck at hLhsNotStuck
                        exact eo_typeof_str_contains_args_of_ne_stuck
                          (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPremRaw : eo_interprets M P true :=
                          hTrue P (by simp [P, premiseTermList])
                        have hPrem :
                            eo_interprets M (prefixEqPremise a1 a2) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_prefixof_eq_impl M hM a1 a2 P
                          hA1Trans hA2Trans hArgTypes hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_prefixof_eq_impl a1 a2 P
                            hA1Trans hA2Trans hArgTypes hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
