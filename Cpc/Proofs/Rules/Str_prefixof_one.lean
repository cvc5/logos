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

private abbrev prefixOnePremise (t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len t))
    (Term.Numeral 1)

private abbrev prefixOneLhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.str_prefixof s) t

private abbrev prefixOneRhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains t) s

private abbrev prefixOneConclusion (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (prefixOneLhs s t)) (prefixOneRhs s t)

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

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
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

private theorem native_seq_contains_singleton_singleton
    (x y : SmtValue) :
    native_seq_contains [x] [y] = native_veq x y := by
  by_cases hxy : x = y
  · subst y
    simpa [native_veq] using native_seq_contains_self [x]
  · unfold native_seq_contains
    unfold native_seq_indexof
    have hyx : ¬ y = x := by
      intro hyx
      exact hxy hyx.symm
    simp [native_seq_indexof_rec, native_seq_prefix_eq, native_veq, hxy, hyx]

private theorem native_seq_contains_singleton_long
    (x y z : SmtValue) (zs : List SmtValue) :
    native_seq_contains [x] (y :: z :: zs) = false := by
  unfold native_seq_contains
  unfold native_seq_indexof
  simp

private theorem eval_str_prefixof_one_eq_contains
    (sx sy : SmtSeq) (T : SmtType)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T)
    (hLen : (native_unpack_seq sy).length = 1) :
    __smtx_model_eval_str_prefixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      __smtx_model_eval_str_contains (SmtValue.Seq sy) (SmtValue.Seq sx) := by
  have hSyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  have hSxPack :
      native_pack_seq T (native_unpack_seq sx) = sx := by
    rw [← elem_typeof_seq_value_of_typeof_seq_value hSxTy]
    exact native_pack_unpack_seq sx
  cases hys : native_unpack_seq sy with
  | nil =>
      simp [hys] at hLen
  | cons y ysTail =>
      cases ysTail with
      | nil =>
          cases hxs : native_unpack_seq sx with
          | nil =>
              rw [← hSxPack]
              simp [__smtx_model_eval_str_prefixof,
                __smtx_model_eval_str_contains, __smtx_model_eval_str_len,
                __smtx_model_eval_str_substr, __smtx_model_eval_eq,
                native_seq_len, native_seq_extract, native_seq_extract_zero_nat_any,
                native_seq_contains_nil, hxs, hys, hSyElem, native_veq,
                native_pack_seq, native_unpack_seq]
          | cons x xsTail =>
              cases xsTail with
              | nil =>
                  rw [← hSxPack]
                  simp [__smtx_model_eval_str_prefixof,
                    __smtx_model_eval_str_contains, __smtx_model_eval_str_len,
                    __smtx_model_eval_str_substr, __smtx_model_eval_eq,
                    native_seq_len, native_seq_extract, native_seq_extract_zero_nat_any,
                    native_seq_contains_singleton_singleton, hxs, hys, hSyElem,
                    hSxPack, native_veq, native_pack_seq, native_unpack_seq]
                  constructor <;> intro h <;> exact h.symm
              | cons z zs =>
                  rw [← hSxPack]
                  have hLenNonneg : (0 : Int) <= Int.ofNat zs.length :=
                    Int.natCast_nonneg zs.length
                  simp [__smtx_model_eval_str_prefixof,
                    __smtx_model_eval_str_contains, __smtx_model_eval_str_len,
                    __smtx_model_eval_str_substr, __smtx_model_eval_eq,
                    native_seq_len, native_seq_extract, native_seq_extract_zero_nat_any,
                    native_seq_contains_singleton_long, hxs, hys, hSyElem,
                    hSxPack, native_veq, native_pack_seq, native_unpack_seq,
                    Smtm.native_unpack_pack_seq]
                  by_cases hIf : (↑zs.length + 1 + 1 : Int) <= 0
                  · omega
                  · have hMin :
                        min (↑zs.length + 1 + 1 : Int) 1 = 1 :=
                      Int.min_eq_right (by omega)
                    simp [hIf, hMin, native_pack_seq]
      | cons z zs =>
          simp [hys] at hLen

private theorem prog_str_prefixof_one_info
    (s t P : Term)
    (hProg : __eo_prog_str_prefixof_one s t (Proof.pf P) ≠ Term.Stuck) :
    ∃ t0,
      P = prefixOnePremise t0 ∧
      t0 = t ∧
      __eo_prog_str_prefixof_one s t (Proof.pf P) =
        prefixOneConclusion s t := by
  unfold __eo_prog_str_prefixof_one at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have ht :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_prefixof_one, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      prefixOnePremise, prefixOneConclusion, prefixOneLhs, prefixOneRhs]

private theorem typed___eo_prog_str_prefixof_one_impl
    (s t P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_prefixof_one s t (Proof.pf P) =
        prefixOneConclusion s t) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_prefixof_one s t (Proof.pf P)) := by
  rcases hTy with ⟨T, hSTy, hTTy⟩
  let lhs := prefixOneLhs s t
  let rhs := prefixOneRhs s t
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
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hSSmtTy, hTSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [prefixOneConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_prefixof_one_impl
    (M : SmtModel) (hM : model_wf M) (s t P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (prefixOnePremise t) true)
    (hProgEq :
      __eo_prog_str_prefixof_one s t (Proof.pf P) =
        prefixOneConclusion s t) :
    eo_interprets M (__eo_prog_str_prefixof_one s t (Proof.pf P)) true := by
  rcases hTy with ⟨T, hSTy, hTTy⟩
  let lhs := prefixOneLhs s t
  let rhs := prefixOneRhs s t
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, prefixOneConclusion, lhs, rhs] using
      typed___eo_prog_str_prefixof_one_impl s t P hSTrans hTTrans
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
  have hSSeqTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hTSeqTy :
      __smtx_typeof_seq_value sy = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hTEval] using hTEvalTy
  have hLenOne : (native_unpack_seq sy).length = 1 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t)) (SmtTerm.Numeral 1)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hTEval,
          smtx_eval_numeral_term_eq] at hEval
        have hLenInt :
            (Int.ofNat (native_unpack_seq sy).length : Int) = 1 := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        change Int.ofNat (native_unpack_seq sy).length = Int.ofNat 1 at hLenInt
        exact Int.ofNat.inj hLenInt
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_prefixof (__eo_to_smt s) (__eo_to_smt t)) =
      __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s))
    rw [smtx_eval_str_prefixof_term_eq, smtx_eval_str_contains_term_eq,
      hSEval, hTEval]
    exact eval_str_prefixof_one_eq_contains sx sy (__eo_to_smt_type T)
      hSSeqTy hTSeqTy hLenOne
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_prefixof_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_prefixof_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_prefixof_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_prefixof_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_prefixof_one args premises ≠
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
                          (__eo_prog_str_prefixof_one a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_prefixof_one a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_prefixof_one_info a1 a2 P hProgRule with
                        ⟨t0, hPremShape, ht0, hProgEq⟩
                      subst t0
                      let lhs := prefixOneLhs a1 a2
                      let rhs := prefixOneRhs a1 a2
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
                            eo_interprets M (prefixOnePremise a2) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_prefixof_one_impl M hM a1 a2 P
                          hA1Trans hA2Trans hArgTypes hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_prefixof_one_impl a1 a2 P
                            hA1Trans hA2Trans hArgTypes hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
