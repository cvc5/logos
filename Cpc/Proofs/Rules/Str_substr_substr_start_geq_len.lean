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

private abbrev substrSubstrStartPremise (n2 m1 : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n2) m1))
    (Term.Boolean true)

private abbrev substrSubstrStartInner (x n1 m1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n1) m1

private abbrev substrSubstrStartLhs
    (x n1 m1 n2 m2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply Term.str_substr
      (substrSubstrStartInner x n1 m1)) n2) m2

private abbrev substrSubstrStartConclusion
    (x n1 m1 n2 m2 A : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrSubstrStartLhs x n1 m1 n2 m2))
    (__seq_empty A)

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

private theorem native_seq_extract_empty_of_len_nonpos
    (xs : List SmtValue) (i n : native_Int)
    (h : n ≤ 0) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  simp [h]

private theorem native_seq_extract_empty_of_start_ge_len
    (xs : List SmtValue) (i n : native_Int)
    (h : native_seq_len xs <= i) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  have hLen : (↑xs.length : native_Int) <= i := by
    simpa [native_seq_len] using h
  simp [hLen]

private theorem native_seq_extract_len_le_arg_of_nonneg
    (xs : List SmtValue) (i n : native_Int) :
    0 <= n -> Int.ofNat (native_seq_extract xs i n).length <= n := by
  intro hn
  simp only [native_seq_extract]
  split
  · simp [hn]
  · rename_i h
    have hProp : ¬ ((i < 0 ∨ n <= 0) ∨ Int.ofNat xs.length <= i) := by
      simpa [Bool.or_eq_true, decide_eq_true_eq] using h
    have hiNonneg : 0 <= i := by
      have hiNot : ¬ i < 0 := by
        intro hi
        exact hProp (Or.inl (Or.inl hi))
      exact Int.le_of_not_gt hiNot
    have hTake :
        ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.toNat (min n (Int.ofNat xs.length - i)) :=
      List.length_take_le _ _
    have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by omega
    have hMinNonneg : 0 <= min n (Int.ofNat xs.length - i) :=
      (Int.le_min).2 ⟨hn, hDiffNonneg⟩
    have hCast :
        Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) =
          min n (Int.ofNat xs.length - i) :=
      Int.toNat_of_nonneg hMinNonneg
    have hLenLe :
        Int.ofNat
            ((xs.drop (Int.toNat i)).take
              (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) :=
      Int.ofNat_le.mpr hTake
    have hMinLe : min n (Int.ofNat xs.length - i) <= n :=
      Int.min_le_left _ _
    omega

private theorem native_seq_extract_nested_empty_of_start_ge_len_arg
    (xs : List SmtValue) (i m j n : native_Int)
    (h : m <= j) :
    native_seq_extract (native_seq_extract xs i m) j n = [] := by
  by_cases hm : 0 <= m
  · have hLenLeM :
        Int.ofNat (native_seq_extract xs i m).length <= m :=
      native_seq_extract_len_le_arg_of_nonneg xs i m hm
    have hLenLeJ :
        native_seq_len (native_seq_extract xs i m) <= j := by
      exact Int.le_trans (by simpa [native_seq_len] using hLenLeM) h
    exact native_seq_extract_empty_of_start_ge_len
      (native_seq_extract xs i m) j n hLenLeJ
  · have hmNeg : m < 0 := Int.lt_of_not_ge hm
    have hInner : native_seq_extract xs i m = [] :=
      native_seq_extract_empty_of_len_nonpos xs i m (Int.le_of_lt hmNeg)
    rw [hInner]
    simp [native_seq_extract]

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

private theorem prog_str_substr_substr_start_geq_len_info
    (x n1 m1 n2 m2 A P : Term)
    (hProg :
      __eo_prog_str_substr_substr_start_geq_len x n1 m1 n2 m2 A
          (Proof.pf P) ≠
        Term.Stuck) :
    ∃ T n20 m10,
      A = Term.Apply Term.Seq T ∧
      P = substrSubstrStartPremise n20 m10 ∧
      n20 = n2 ∧
      m10 = m1 ∧
      __eo_prog_str_substr_substr_start_geq_len x n1 m1 n2 m2 A
          (Proof.pf P) =
        substrSubstrStartConclusion x n1 m1 n2 m2
          (Term.Apply Term.Seq T) := by
  unfold __eo_prog_str_substr_substr_start_geq_len at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg with
      ⟨hn2, hm1⟩
    subst_vars
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_substr_start_geq_len, __eo_requires, __eo_and,
      __eo_eq, SmtEval.native_ite, native_teq, SmtEval.native_not,
      SmtEval.native_and, eo_mk_apply_eq_seq_empty,
      substrSubstrStartConclusion, substrSubstrStartLhs,
      substrSubstrStartInner, substrSubstrStartPremise]

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

private theorem facts___eo_prog_str_substr_substr_start_geq_len_impl
    (M : SmtModel) (hM : model_wf M)
    (x n1 m1 n2 m2 P T : Term)
    (hBoolEq :
      RuleProofs.eo_has_bool_type
        (substrSubstrStartConclusion x n1 m1 n2 m2
          (Term.Apply Term.Seq T)))
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hN1Trans : RuleProofs.eo_has_smt_translation n1)
    (hM1Trans : RuleProofs.eo_has_smt_translation m1)
    (hN2Trans : RuleProofs.eo_has_smt_translation n2)
    (hM2Trans : RuleProofs.eo_has_smt_translation m2)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hN1Ty : __eo_typeof n1 = Term.Int)
    (hM1Ty : __eo_typeof m1 = Term.Int)
    (hN2Ty : __eo_typeof n2 = Term.Int)
    (hM2Ty : __eo_typeof m2 = Term.Int)
    (hPrem : eo_interprets M (substrSubstrStartPremise n2 m1) true)
    (hProgEq :
      __eo_prog_str_substr_substr_start_geq_len x n1 m1 n2 m2
          (Term.Apply Term.Seq T) (Proof.pf P) =
        substrSubstrStartConclusion x n1 m1 n2 m2
          (Term.Apply Term.Seq T)) :
    eo_interprets M
      (__eo_prog_str_substr_substr_start_geq_len x n1 m1 n2 m2
        (Term.Apply Term.Seq T) (Proof.pf P)) true := by
  let inner := substrSubstrStartInner x n1 m1
  let lhs := substrSubstrStartLhs x n1 m1 n2 m2
  let rhs := __seq_empty (Term.Apply Term.Seq T)
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hN1SmtTy := smtx_typeof_of_eo_int n1 hN1Trans hN1Ty
  have hM1SmtTy := smtx_typeof_of_eo_int m1 hM1Trans hM1Ty
  have hN2SmtTy := smtx_typeof_of_eo_int n2 hN2Trans hN2Ty
  have hM2SmtTy := smtx_typeof_of_eo_int m2 hM2Trans hM2Ty
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hN1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n1)) =
        SmtType.Int := by
    simpa [hN1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n1) (by
        unfold term_has_non_none_type
        rw [hN1SmtTy]
        simp)
  have hM1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m1)) =
        SmtType.Int := by
    simpa [hM1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m1) (by
        unfold term_has_non_none_type
        rw [hM1SmtTy]
        simp)
  have hN2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n2)) =
        SmtType.Int := by
    simpa [hN2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n2) (by
        unfold term_has_non_none_type
        rw [hN2SmtTy]
        simp)
  have hM2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m2)) =
        SmtType.Int := by
    simpa [hM2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m2) (by
        unfold term_has_non_none_type
        rw [hM2SmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases int_value_canonical hN1EvalTy with ⟨n1i, hN1Eval⟩
  rcases int_value_canonical hM1EvalTy with ⟨m1i, hM1Eval⟩
  rcases int_value_canonical hN2EvalTy with ⟨n2i, hN2Eval⟩
  rcases int_value_canonical hM2EvalTy with ⟨m2i, hM2Eval⟩
  have hM1LeN2 : m1i <= n2i := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt n2) (__eo_to_smt m1))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq, hN2Eval,
          hM1Eval, smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq m1i n2i = true := by
          simpa [__smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, native_veq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
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
        (SmtTerm.str_substr
          (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt n1)
            (__eo_to_smt m1))
          (__eo_to_smt n2) (__eo_to_smt m2)) =
      __smtx_model_eval M (__eo_to_smt rhs)
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_substr_term_eq, hXEval,
      hN1Eval, hM1Eval, hN2Eval, hM2Eval, hEmptyEval]
    simp [__smtx_model_eval_str_substr, hXElem, elem_typeof_pack_seq]
    rw [Smtm.native_unpack_pack_seq]
    rw [native_seq_extract_nested_empty_of_start_ge_len_arg
      (native_unpack_seq sx) n1i m1i n2i m2i hM1LeN2]
    rfl
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs
    (by simpa [substrSubstrStartConclusion, lhs, rhs] using hBoolEq) <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_substr_start_geq_len_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_substr_start_geq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_substr_start_geq_len args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_substr_start_geq_len args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_substr_substr_start_geq_len args premises ≠
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
              | cons a4 args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons a5 args =>
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
                                      have hA4Trans :
                                          RuleProofs.eo_has_smt_translation a4 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked]
                                          using hCmdTrans.2.2.2.1
                                      have hA5Trans :
                                          RuleProofs.eo_has_smt_translation a5 := by
                                        simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked]
                                          using hCmdTrans.2.2.2.2.1
                                      change __eo_typeof
                                          (__eo_prog_str_substr_substr_start_geq_len
                                            a1 a2 a3 a4 a5 A (Proof.pf P)) =
                                        Term.Bool at hResultTy
                                      have hProgRule :
                                          __eo_prog_str_substr_substr_start_geq_len
                                              a1 a2 a3 a4 a5 A (Proof.pf P) ≠
                                            Term.Stuck :=
                                        term_ne_stuck_of_typeof_bool hResultTy
                                      rcases
                                          prog_str_substr_substr_start_geq_len_info
                                            a1 a2 a3 a4 a5 A P hProgRule with
                                        ⟨T, n20, m10, hATyArg, hPremShape,
                                          hn20, hm10, hProgEq⟩
                                      subst A
                                      subst n20
                                      subst m10
                                      let inner := substrSubstrStartInner a1 a2 a3
                                      let lhs := substrSubstrStartLhs a1 a2 a3 a4 a5
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
                                      have hOuterArgTypes :
                                          ∃ U, __eo_typeof inner = Term.Apply Term.Seq U ∧
                                            __eo_typeof a4 = Term.Int ∧
                                            __eo_typeof a5 = Term.Int := by
                                        change __eo_typeof_str_substr (__eo_typeof inner)
                                            (__eo_typeof a4) (__eo_typeof a5) ≠
                                          Term.Stuck at hLhsNotStuck
                                        exact eo_typeof_str_substr_args_of_ne_stuck
                                          (__eo_typeof inner) (__eo_typeof a4)
                                          (__eo_typeof a5) hLhsNotStuck
                                      rcases hOuterArgTypes with
                                        ⟨U, hInnerTyU, hA4Ty, hA5Ty⟩
                                      have hInnerNotStuck : __eo_typeof inner ≠ Term.Stuck := by
                                        rw [hInnerTyU]
                                        simp
                                      have hInnerArgTypes :
                                          ∃ V, __eo_typeof a1 = Term.Apply Term.Seq V ∧
                                            __eo_typeof a2 = Term.Int ∧
                                            __eo_typeof a3 = Term.Int := by
                                        change __eo_typeof_str_substr (__eo_typeof a1)
                                            (__eo_typeof a2) (__eo_typeof a3) ≠
                                          Term.Stuck at hInnerNotStuck
                                        exact eo_typeof_str_substr_args_of_ne_stuck
                                          (__eo_typeof a1) (__eo_typeof a2)
                                          (__eo_typeof a3) hInnerNotStuck
                                      rcases hInnerArgTypes with
                                        ⟨V, hA1TyV, hA2Ty, hA3Ty⟩
                                      have hInnerTyV :
                                          __eo_typeof inner = Term.Apply Term.Seq V := by
                                        change __eo_typeof_str_substr (__eo_typeof a1)
                                          (__eo_typeof a2) (__eo_typeof a3) =
                                          Term.Apply Term.Seq V
                                        simp [hA1TyV, hA2Ty, hA3Ty,
                                          __eo_typeof_str_substr]
                                      have hVU : V = U := by
                                        rw [hInnerTyV] at hInnerTyU
                                        cases hInnerTyU
                                        rfl
                                      subst V
                                      have hLhsTy :
                                          __eo_typeof lhs = Term.Apply Term.Seq U := by
                                        change __eo_typeof_str_substr (__eo_typeof inner)
                                          (__eo_typeof a4) (__eo_typeof a5) =
                                          Term.Apply Term.Seq U
                                        simp [hInnerTyU, hA4Ty, hA5Ty,
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
                                        smtx_typeof_of_eo_seq a1 T hA1Trans hA1TyV
                                      have hA2SmtTy :=
                                        smtx_typeof_of_eo_int a2 hA2Trans hA2Ty
                                      have hA3SmtTy :=
                                        smtx_typeof_of_eo_int a3 hA3Trans hA3Ty
                                      have hA4SmtTy :=
                                        smtx_typeof_of_eo_int a4 hA4Trans hA4Ty
                                      have hA5SmtTy :=
                                        smtx_typeof_of_eo_int a5 hA5Trans hA5Ty
                                      have hInnerSmtTy :
                                          __smtx_typeof (__eo_to_smt inner) =
                                            SmtType.Seq (__eo_to_smt_type T) := by
                                        change __smtx_typeof
                                            (SmtTerm.str_substr (__eo_to_smt a1)
                                              (__eo_to_smt a2) (__eo_to_smt a3)) =
                                          SmtType.Seq (__eo_to_smt_type T)
                                        rw [typeof_str_substr_eq]
                                        simp [hA1SmtTy, hA2SmtTy, hA3SmtTy,
                                          __smtx_typeof_str_substr]
                                      have hLhsSmtTy :
                                          __smtx_typeof (__eo_to_smt lhs) =
                                            SmtType.Seq (__eo_to_smt_type T) := by
                                        change __smtx_typeof
                                            (SmtTerm.str_substr (__eo_to_smt inner)
                                              (__eo_to_smt a4) (__eo_to_smt a5)) =
                                          SmtType.Seq (__eo_to_smt_type T)
                                        rw [typeof_str_substr_eq]
                                        simp [hInnerSmtTy, hA4SmtTy, hA5SmtTy,
                                          __smtx_typeof_str_substr]
                                      have hRhsSmtTy :
                                          __smtx_typeof (__eo_to_smt rhs) =
                                            SmtType.Seq (__eo_to_smt_type T) := by
                                        have hEmptyTy' :=
                                          smtx_typeof_seq_empty_typeof_of_smt_type_seq
                                            a1 (__eo_to_smt_type T) hA1SmtTy
                                        simpa [rhs, hA1TyV] using hEmptyTy'
                                      have hBoolEq :
                                          RuleProofs.eo_has_bool_type
                                            (substrSubstrStartConclusion a1 a2 a3 a4 a5
                                              (Term.Apply Term.Seq T)) := by
                                        have hEqBool :
                                            RuleProofs.eo_has_bool_type
                                              (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
                                          RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                            lhs rhs
                                            (by rw [hLhsSmtTy, hRhsSmtTy])
                                            (by rw [hLhsSmtTy]; simp)
                                        simpa [substrSubstrStartConclusion, lhs, rhs] using
                                          hEqBool
                                      refine ⟨?_, ?_⟩
                                      · intro hTrue
                                        have hPremRaw : eo_interprets M P true :=
                                          hTrue P (by simp [P, premiseTermList])
                                        have hPrem :
                                            eo_interprets M
                                              (substrSubstrStartPremise a4 a3) true := by
                                          simpa [hPremShape] using hPremRaw
                                        change eo_interprets M
                                          (__eo_prog_str_substr_substr_start_geq_len
                                            a1 a2 a3 a4 a5 (Term.Apply Term.Seq T)
                                            (Proof.pf P)) true
                                        exact
                                          facts___eo_prog_str_substr_substr_start_geq_len_impl
                                            M hM a1 a2 a3 a4 a5 P T hBoolEq hA1Trans
                                            hA2Trans hA3Trans hA4Trans hA5Trans
                                            hA1TyV hA2Ty hA3Ty hA4Ty hA5Ty hPrem
                                            hProgEq
                                      · change RuleProofs.eo_has_smt_translation
                                          (__eo_prog_str_substr_substr_start_geq_len
                                            a1 a2 a3 a4 a5 (Term.Apply Term.Seq T)
                                            (Proof.pf P))
                                        rw [hProgEq]
                                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                          hBoolEq
                                  | cons _ _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
