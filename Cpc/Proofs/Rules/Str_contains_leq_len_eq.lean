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

private abbrev containsLeqLenPremise (x y : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len y))
        (Term.Apply Term.str_len x)))
    (Term.Boolean true)

private abbrev containsLeqLenLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) y

private abbrev containsLeqLenRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) y

private abbrev containsLeqLenConclusion (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (containsLeqLenLhs x y))
    (containsLeqLenRhs x y)

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

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
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

private theorem native_seq_contains_decomp_exists_local
    (xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    ∃ before after, xs = before ++ pat ++ after := by
  have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at h
    exact of_decide_eq_true h
  exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩

private theorem smt_seq_eq_of_unpack_eq_same_type
    (sx sy : SmtSeq) (T : SmtType)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T)
    (hUnpack : native_unpack_seq sx = native_unpack_seq sy) :
    sx = sy := by
  have hSxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  calc
    sx = native_pack_seq (__smtx_elem_typeof_seq_value sx)
        (native_unpack_seq sx) := (native_pack_unpack_seq sx).symm
    _ = native_pack_seq (__smtx_elem_typeof_seq_value sy)
        (native_unpack_seq sy) := by
          rw [hSxElem, hSyElem, hUnpack]
    _ = sy := native_pack_unpack_seq sy

private theorem native_seq_contains_false_of_len_ge_ne
    (sx sy : SmtSeq) (T : SmtType)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T)
    (hLen :
      (native_unpack_seq sx).length <= (native_unpack_seq sy).length)
    (hNe : sx ≠ sy) :
    native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy) =
      false := by
  cases hContains :
      native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy)
  · rfl
  · exfalso
    have hContainsTrue :
        native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy) =
          true := by
      simpa using hContains
    rcases native_seq_contains_decomp_exists_local
        (native_unpack_seq sx) (native_unpack_seq sy) hContainsTrue with
      ⟨before, after, hDecomp⟩
    have hLenEq :
        (native_unpack_seq sx).length =
          before.length + (native_unpack_seq sy).length + after.length := by
      simpa [List.length_append, Nat.add_assoc] using
        congrArg List.length hDecomp
    have hBeforeZero : before.length = 0 := by omega
    have hAfterZero : after.length = 0 := by omega
    have hBeforeNil : before = [] := by
      cases before <;> simp at hBeforeZero ⊢
    have hAfterNil : after = [] := by
      cases after <;> simp at hAfterZero ⊢
    have hUnpack :
        native_unpack_seq sx = native_unpack_seq sy := by
      simpa [hBeforeNil, hAfterNil] using hDecomp
    exact hNe
      (smt_seq_eq_of_unpack_eq_same_type sx sy T hSxTy hSyTy hUnpack)

private theorem eval_str_contains_seq_eq_of_len_ge
    (sx sy : SmtSeq) (T : SmtType)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T)
    (hLen :
      (native_unpack_seq sx).length <= (native_unpack_seq sy).length) :
    __smtx_model_eval_str_contains (SmtValue.Seq sx) (SmtValue.Seq sy) =
      __smtx_model_eval_eq (SmtValue.Seq sx) (SmtValue.Seq sy) := by
  by_cases hEq : sx = sy
  · subst sy
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
      native_seq_contains_self, native_veq]
  · have hContainsFalse :=
      native_seq_contains_false_of_len_ge_ne sx sy T hSxTy hSyTy hLen hEq
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_eq, native_veq,
      hContainsFalse, hEq]

private theorem prog_str_contains_leq_len_eq_info
    (x y P : Term)
    (hProg : __eo_prog_str_contains_leq_len_eq x y (Proof.pf P) ≠
      Term.Stuck) :
    ∃ x0 y0,
      P = containsLeqLenPremise x0 y0 ∧
      x0 = x ∧
      y0 = y ∧
      __eo_prog_str_contains_leq_len_eq x y (Proof.pf P) =
        containsLeqLenConclusion x y := by
  unfold __eo_prog_str_contains_leq_len_eq at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hEq :=
      RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg
    rcases hEq with ⟨hy, hx⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_leq_len_eq, __eo_requires, __eo_eq, __eo_and,
      SmtEval.native_ite, native_teq, native_and, SmtEval.native_not,
      containsLeqLenConclusion, containsLeqLenLhs, containsLeqLenRhs]

private theorem typed___eo_prog_str_contains_leq_len_eq_impl
    (x y P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : ∃ T, __eo_typeof x = Term.Apply Term.Seq T ∧
      __eo_typeof y = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_contains_leq_len_eq x y (Proof.pf P) =
        containsLeqLenConclusion x y) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_contains_leq_len_eq x y (Proof.pf P)) := by
  rcases hTy with ⟨T, hXTy, hYTy⟩
  let lhs := containsLeqLenLhs x y
  let rhs := containsLeqLenRhs x y
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy : RuleProofs.eo_has_bool_type rhs := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x y
      (by rw [hXSmtTy, hYSmtTy]) (by rw [hXSmtTy]; simp)
  have hRhsSmtTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := hRhsTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [containsLeqLenConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_contains_leq_len_eq_impl
    (M : SmtModel) (hM : model_wf M) (x y P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : ∃ T, __eo_typeof x = Term.Apply Term.Seq T ∧
      __eo_typeof y = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (containsLeqLenPremise x y) true)
    (hProgEq :
      __eo_prog_str_contains_leq_len_eq x y (Proof.pf P) =
        containsLeqLenConclusion x y) :
    eo_interprets M
      (__eo_prog_str_contains_leq_len_eq x y (Proof.pf P)) true := by
  rcases hTy with ⟨T, hXTy, hYTy⟩
  let lhs := containsLeqLenLhs x y
  let rhs := containsLeqLenRhs x y
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, containsLeqLenConclusion, lhs, rhs] using
      typed___eo_prog_str_contains_leq_len_eq_impl x y P hXTrans hYTrans
        ⟨T, hXTy, hYTy⟩ hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  have hSxSeqTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSySeqTy :
      __smtx_typeof_seq_value sy = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hYEval] using hYEvalTy
  have hLen :
      (native_unpack_seq sx).length <= (native_unpack_seq sy).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt y))
                (SmtTerm.str_len (__eo_to_smt x)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
          hYEval, hXEval, smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq (Int.ofNat (native_unpack_seq sx).length)
              (Int.ofNat (native_unpack_seq sy).length) = true := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq,
            native_seq_len] using hEval
        have hLeInt :
            (Int.ofNat (native_unpack_seq sx).length : Int) <=
              Int.ofNat (native_unpack_seq sy).length := by
          simpa [native_zleq] using hLeBool
        exact Int.ofNat_le.mp hLeInt
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_eq_term_eq,
      hXEval, hYEval]
    exact eval_str_contains_seq_eq_of_len_ge sx sy (__eo_to_smt_type T)
      hSxSeqTy hSySeqTy hLen
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_leq_len_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_leq_len_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_leq_len_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_leq_len_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_contains_leq_len_eq args premises ≠
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
                          (__eo_prog_str_contains_leq_len_eq a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_contains_leq_len_eq a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_contains_leq_len_eq_info a1 a2 P hProgRule with
                        ⟨x0, y0, hPremShape, hx0, hy0, hProgEq⟩
                      subst x0
                      subst y0
                      let lhs := containsLeqLenLhs a1 a2
                      let rhs := containsLeqLenRhs a1 a2
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
                            eo_interprets M (containsLeqLenPremise a1 a2) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_contains_leq_len_eq_impl
                          M hM a1 a2 P hA1Trans hA2Trans hArgTypes hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_contains_leq_len_eq_impl
                            a1 a2 P hA1Trans hA2Trans hArgTypes hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
