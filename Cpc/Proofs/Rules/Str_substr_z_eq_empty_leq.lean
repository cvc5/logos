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

private abbrev substrZNonemptyPremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.eq (Term.Apply Term.str_len s))
        (Term.Numeral 0)))
    (Term.Boolean false)

private abbrev substrZEmptyPremise (r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len r))
    (Term.Numeral 0)

private abbrev substrZExtract (s m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) m

private abbrev substrZLhs (s r m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrZExtract s m)) r

private abbrev substrZRhs (m : Term) : Term :=
  Term.Apply (Term.Apply Term.leq m) (Term.Numeral 0)

private abbrev substrZConclusion (s r m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrZLhs s r m)) (substrZRhs m)

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

private theorem eo_typeof_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not] at h ⊢
      exact h

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

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq
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

private theorem native_seq_extract_zero_ne_nil_of_pos
    (xs : List SmtValue) (n : native_Int)
    (hxs : xs ≠ []) (hn : 0 < n) :
    native_seq_extract xs 0 n ≠ [] := by
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          simp at hn
      | succ k =>
          rw [native_seq_extract_zero_nat_any xs (Nat.succ k)]
          cases xs with
          | nil =>
              exact False.elim (hxs rfl)
          | cons x xs =>
              simp
  | negSucc k =>
      simp at hn

private theorem native_seq_extract_zero_eq_empty_iff_nonpos
    (xs : List SmtValue) (n : native_Int)
    (hxs : xs ≠ []) :
    native_seq_extract xs 0 n = [] ↔ n <= 0 := by
  constructor
  · intro hExtract
    by_cases hn : n <= 0
    · exact hn
    · have hnPos : 0 < n := Int.lt_of_not_ge hn
      exact False.elim
        (native_seq_extract_zero_ne_nil_of_pos xs n hxs hnPos hExtract)
  · intro hn
    exact native_seq_extract_empty_of_len_nonpos xs 0 n hn

private theorem native_veq_zero_substr_empty_eq_leq
    (T : SmtType) (xs : List SmtValue) (rseq : SmtSeq) (n : native_Int)
    (hxs : xs ≠ [])
    (hrseq : native_pack_seq T [] = rseq) :
    native_veq
        (SmtValue.Seq (native_pack_seq T (native_seq_extract xs 0 n)))
        (SmtValue.Seq rseq) =
      native_zleq n 0 := by
  by_cases hn : n <= 0
  · have hExtract : native_seq_extract xs 0 n = [] :=
      (native_seq_extract_zero_eq_empty_iff_nonpos xs n hxs).2 hn
    simp [native_veq, native_zleq, hExtract, hrseq, hn]
  · have hnPos : 0 < n := Int.lt_of_not_ge hn
    have hExtractNe : native_seq_extract xs 0 n ≠ [] :=
      native_seq_extract_zero_ne_nil_of_pos xs n hxs hnPos
    have hSeqNe :
        SmtValue.Seq (native_pack_seq T (native_seq_extract xs 0 n)) ≠
          SmtValue.Seq rseq := by
      intro hEq
      injection hEq with hPackEq
      rw [← hrseq] at hPackEq
      cases hExtract : native_seq_extract xs 0 n with
      | nil =>
          exact hExtractNe hExtract
      | cons v vs =>
          rw [hExtract] at hPackEq
          simp [native_pack_seq] at hPackEq
    simp [native_veq, native_zleq, hSeqNe, hn]

private theorem eqs_of_requires2_and_eq_true_not_stuck {x1 y1 x2 y2 body : Term}
    (h :
      __eo_requires
        (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
        (Term.Boolean true) body ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 := by
  exact RuleProofs.eqs_of_requires_and_eq_true_not_stuck x1 x2 y1 y2 body h

private theorem prog_str_substr_z_eq_empty_leq_info
    (s r m P Q : Term)
    (hProg :
      __eo_prog_str_substr_z_eq_empty_leq s r m (Proof.pf P) (Proof.pf Q) ≠
        Term.Stuck) :
    ∃ s0 r0,
      P = substrZNonemptyPremise s0 ∧
      Q = substrZEmptyPremise r0 ∧
      s0 = s ∧
      r0 = r ∧
      __eo_prog_str_substr_z_eq_empty_leq s r m (Proof.pf P) (Proof.pf Q) =
        substrZConclusion s r m := by
  unfold __eo_prog_str_substr_z_eq_empty_leq at hProg
  split at hProg <;> try contradiction
  next heqP heqQ =>
    cases heqP
    cases heqQ
    rcases eqs_of_requires2_and_eq_true_not_stuck hProg with ⟨hs, hr⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_z_eq_empty_leq, __eo_requires, __eo_and,
      __eo_eq, SmtEval.native_ite, native_teq, SmtEval.native_not,
      SmtEval.native_and, substrZConclusion, substrZLhs, substrZRhs,
      substrZExtract, substrZNonemptyPremise, substrZEmptyPremise]

private theorem facts___eo_prog_str_substr_z_eq_empty_leq_impl
    (M : SmtModel) (hM : model_wf M) (s r m P Q T : Term)
    (hBoolEq : RuleProofs.eo_has_bool_type (substrZConclusion s r m))
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T)
    (hMTy : __eo_typeof m = Term.Int)
    (hPremS : eo_interprets M (substrZNonemptyPremise s) true)
    (hPremR : eo_interprets M (substrZEmptyPremise r) true)
    (hProgEq :
      __eo_prog_str_substr_z_eq_empty_leq s r m (Proof.pf P) (Proof.pf Q) =
        substrZConclusion s r m) :
    eo_interprets M
      (__eo_prog_str_substr_z_eq_empty_leq s r m (Proof.pf P) (Proof.pf Q))
      true := by
  let lhs := substrZLhs s r m
  let rhs := substrZRhs m
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
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
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hSLenNeZero : native_seq_len (native_unpack_seq ss) ≠ 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremS
    cases hPremS with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s))
                (SmtTerm.Numeral 0))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq,
          smtx_eval_str_len_term_eq, hSEval,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len,
          native_veq, SmtEval.native_zeq] using hEval
  have hSNonempty : native_unpack_seq ss ≠ [] := by
    intro hNil
    apply hSLenNeZero
    simp [native_seq_len, hNil]
  have hRLenZero : native_seq_len (native_unpack_seq rs) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremR
    cases hPremR with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt r))
              (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hREval,
          smtx_eval_numeral_term_eq] at hEval
        simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len,
          native_veq, SmtEval.native_zeq] using hEval
  have hRNil : native_unpack_seq rs = [] := by
    have hLenNat : (native_unpack_seq rs).length = 0 := by
      have hLenInt : Int.ofNat (native_unpack_seq rs).length = 0 := by
        simpa [native_seq_len] using hRLenZero
      exact Int.ofNat_eq_zero.mp hLenInt
    exact List.eq_nil_of_length_eq_zero hLenNat
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSEval, __smtx_typeof_seq_value, __smtx_typeof_value] using hSEvalTy
  have hRSeqTy :
      __smtx_typeof_seq_value rs = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hREval, __smtx_typeof_seq_value, __smtx_typeof_value] using hREvalTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hRElem : __smtx_elem_typeof_seq_value rs = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hRSeqTy
  have hRPack : native_pack_seq (__eo_to_smt_type T) [] = rs := by
    have hPack := native_pack_unpack_seq rs
    rw [← hRElem]
    simpa [hRNil] using hPack
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
            (__eo_to_smt m))
          (__eo_to_smt r)) =
      __smtx_model_eval M
        (SmtTerm.leq (__eo_to_smt m) (SmtTerm.Numeral 0))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_substr_term_eq, hSEval,
      smtx_eval_numeral_term_eq, hMEval, hREval]
    rw [smtx_eval_leq_term_eq, hMEval, smtx_eval_numeral_term_eq]
    simp [__smtx_model_eval_eq, __smtx_model_eval_str_substr,
      __smtx_model_eval_leq, hSElem,
      native_veq_zero_substr_empty_eq_leq (__eo_to_smt_type T)
        (native_unpack_seq ss) rs mi hSNonempty hRPack]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs
    (by simpa [substrZConclusion, lhs, rhs] using hBoolEq) <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_z_eq_empty_leq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_z_eq_empty_leq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_z_eq_empty_leq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_z_eq_empty_leq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_z_eq_empty_leq args premises ≠
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
                  | cons p1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p2 premises =>
                          cases premises with
                          | nil =>
                              let P := __eo_state_proven_nth s p1
                              let Q := __eo_state_proven_nth s p2
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
                                  (__eo_prog_str_substr_z_eq_empty_leq a1 a2 a3
                                    (Proof.pf P) (Proof.pf Q)) =
                                Term.Bool at hResultTy
                              have hProgRule :
                                  __eo_prog_str_substr_z_eq_empty_leq a1 a2 a3
                                      (Proof.pf P) (Proof.pf Q) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_substr_z_eq_empty_leq_info a1 a2 a3 P Q
                                  hProgRule with
                                ⟨s0, r0, hPremSShape, hPremRShape, hs0, hr0,
                                  hProgEq⟩
                              subst s0
                              subst r0
                              let lhs := substrZLhs a1 a2 a3
                              let rhs := substrZRhs a3
                              let extract := substrZExtract a1 a3
                              rw [hProgEq] at hResultTy
                              change __eo_typeof
                                  (Term.Apply (Term.Apply Term.eq lhs) rhs) =
                                Term.Bool at hResultTy
                              change __eo_typeof_eq (__eo_typeof lhs)
                                  (__eo_typeof rhs) =
                                Term.Bool at hResultTy
                              have hOuterOperands :=
                                RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy
                              have hLhsTy : __eo_typeof lhs = Term.Bool := by
                                change __eo_typeof_eq (__eo_typeof extract)
                                    (__eo_typeof a2) = Term.Bool
                                exact eo_typeof_eq_bool_of_ne_stuck
                                  (__eo_typeof extract) (__eo_typeof a2)
                                  hOuterOperands.1
                              have hInnerOperands :=
                                RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof extract) (__eo_typeof a2) hLhsTy
                              have hArgTypes :
                                  ∃ U, __eo_typeof a1 = Term.Apply Term.Seq U ∧
                                    __eo_typeof (Term.Numeral 0) = Term.Int ∧
                                    __eo_typeof a3 = Term.Int := by
                                have hSubstrNotStuck := hInnerOperands.1
                                change __eo_typeof_str_substr (__eo_typeof a1)
                                    (__eo_typeof (Term.Numeral 0))
                                    (__eo_typeof a3) ≠ Term.Stuck at hSubstrNotStuck
                                exact eo_typeof_str_substr_args_of_ne_stuck
                                  (__eo_typeof a1)
                                  (__eo_typeof (Term.Numeral 0))
                                  (__eo_typeof a3) hSubstrNotStuck
                              rcases hArgTypes with ⟨T, hA1TyT, hZeroTy, hA3Ty⟩
                              have hExtractTy :
                                  __eo_typeof extract = Term.Apply Term.Seq T := by
                                change __eo_typeof_str_substr (__eo_typeof a1)
                                  (__eo_typeof (Term.Numeral 0))
                                  (__eo_typeof a3) =
                                  Term.Apply Term.Seq T
                                simp [hA1TyT, hZeroTy, hA3Ty,
                                  __eo_typeof_str_substr]
                              have hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq T := by
                                have hInnerEq :=
                                  RuleProofs.eo_typeof_eq_bool_operands_eq
                                    (__eo_typeof extract) (__eo_typeof a2) hLhsTy
                                rw [← hInnerEq, hExtractTy]
                              have hA1SmtTy :=
                                smtx_typeof_of_eo_seq a1 T hA1Trans hA1TyT
                              have hA2SmtTy :=
                                smtx_typeof_of_eo_seq a2 T hA2Trans hA2Ty
                              have hA3SmtTy :=
                                smtx_typeof_of_eo_int a3 hA3Trans hA3Ty
                              have hZeroSmtTy :
                                  __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
                                rw [__smtx_typeof.eq_def]
                              have hExtractSmtTy :
                                  __smtx_typeof (__eo_to_smt extract) =
                                    SmtType.Seq (__eo_to_smt_type T) := by
                                change __smtx_typeof
                                    (SmtTerm.str_substr (__eo_to_smt a1)
                                      (SmtTerm.Numeral 0) (__eo_to_smt a3)) =
                                  SmtType.Seq (__eo_to_smt_type T)
                                rw [typeof_str_substr_eq]
                                simp [hA1SmtTy, hZeroSmtTy, hA3SmtTy,
                                  __smtx_typeof_str_substr]
                              have hLhsSmtTy :
                                  __smtx_typeof (__eo_to_smt lhs) =
                                    SmtType.Bool := by
                                have hEqBool :
                                    RuleProofs.eo_has_bool_type
                                      (Term.Apply (Term.Apply Term.eq extract) a2) :=
                                  RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                    extract a2
                                    (by rw [hExtractSmtTy, hA2SmtTy])
                                    (by rw [hExtractSmtTy]; simp)
                                simpa [lhs, substrZLhs, __eo_to_smt, __smtx_typeof, extract,
                                substrZExtract,
                                RuleProofs.eo_has_bool_type] using hEqBool
                              have hRhsSmtTy :
                                  __smtx_typeof (__eo_to_smt rhs) =
                                    SmtType.Bool := by
                                change __smtx_typeof
                                    (SmtTerm.leq (__eo_to_smt a3)
                                      (SmtTerm.Numeral 0)) =
                                  SmtType.Bool
                                rw [typeof_leq_eq]
                                simp [hA3SmtTy, hZeroSmtTy,
                                  __smtx_typeof_arith_overload_op_2_ret,
                                  native_ite, native_Teq]
                              have hBoolEq :
                                  RuleProofs.eo_has_bool_type
                                    (substrZConclusion a1 a2 a3) := by
                                have hEqBool :
                                    RuleProofs.eo_has_bool_type
                                      (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
                                  RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                    lhs rhs
                                    (by rw [hLhsSmtTy, hRhsSmtTy])
                                    (by rw [hLhsSmtTy]; simp)
                                simpa [substrZConclusion, lhs, rhs] using hEqBool
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremSRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, Q, premiseTermList])
                                have hPremRRaw : eo_interprets M Q true :=
                                  hTrue Q (by simp [P, Q, premiseTermList])
                                have hPremS :
                                    eo_interprets M (substrZNonemptyPremise a1) true := by
                                  simpa [hPremSShape] using hPremSRaw
                                have hPremR :
                                    eo_interprets M (substrZEmptyPremise a2) true := by
                                  simpa [hPremRShape] using hPremRRaw
                                change eo_interprets M
                                  (__eo_prog_str_substr_z_eq_empty_leq a1 a2 a3
                                    (Proof.pf P) (Proof.pf Q)) true
                                exact facts___eo_prog_str_substr_z_eq_empty_leq_impl
                                  M hM a1 a2 a3 P Q T hBoolEq hA1Trans hA2Trans
                                  hA3Trans hA1TyT hA2Ty hA3Ty hPremS hPremR
                                  hProgEq
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_substr_z_eq_empty_leq a1 a2 a3
                                    (Proof.pf P) (Proof.pf Q))
                                rw [hProgEq]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hBoolEq
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
