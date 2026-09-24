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

private abbrev replReplLenIdPremise (y x : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.geq (Term.Apply Term.str_len y))
        (Term.Apply Term.str_len x)))
    (Term.Boolean true)

private abbrev replReplLenIdLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) x

private abbrev replReplLenIdConclusion (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replReplLenIdLhs x y)) x

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

private theorem native_seq_indexof_zero_decomp_take_drop
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ pat ++
        xs.drop (Int.toNat (native_seq_indexof xs pat 0) + pat.length) =
      xs := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  unfold native_seq_indexof at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    change xs.take j ++ pat ++ xs.drop (j + pat.length) = xs
    rw [hXs, ← hBeforeLen']
    simp
  · simp [hBounds] at hIdx

private theorem native_seq_replace_source_of_pat_len_ge
    (xs pat : List SmtValue)
    (hLen : xs.length <= pat.length) :
    native_seq_replace xs pat xs = xs := by
  cases pat with
  | nil =>
      have hXsLen : xs.length = 0 := Nat.eq_zero_of_le_zero hLen
      have hXsNil : xs = [] := List.eq_nil_of_length_eq_zero hXsLen
      subst xs
      simp [native_seq_replace]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace, hNeg]
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
          int_nonneg_of_not_neg hNeg
        let idx := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hDecomp :=
          native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
        have hLenDecomp := congrArg List.length hDecomp
        simp [List.length_append, idx] at hLenDecomp
        have hLen' : xs.length <= ps.length + 1 := by
          simpa using hLen
        have hLenDecomp' :
            min idx xs.length +
                (ps.length + (xs.length - (idx + (ps.length + 1))) + 1) =
              xs.length := by
          simpa [idx] using hLenDecomp
        have hTakeNil : xs.take idx = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [List.length_take]
          have hTakeLenZero : min idx xs.length = 0 := by
            omega
          exact hTakeLenZero
        have hDropNil : xs.drop (idx + (p :: ps).length) = [] := by
          apply List.drop_eq_nil_of_le
          have hDropBound : xs.length <= idx + (ps.length + 1) := by
            omega
          simpa using hDropBound
        rw [StrEqReplSupport.native_seq_replace_eq_indexof]
        rw [if_neg hNeg]
        change xs.take idx ++ xs ++ xs.drop (idx + (p :: ps).length) = xs
        rw [hTakeNil, hDropNil]
        simp

private theorem prog_str_repl_repl_len_id_info
    (x y P : Term)
    (hProg : __eo_prog_str_repl_repl_len_id x y (Proof.pf P) ≠
      Term.Stuck) :
    ∃ y0 x0,
      P = replReplLenIdPremise y0 x0 ∧
      y0 = y ∧
      x0 = x ∧
      __eo_prog_str_repl_repl_len_id x y (Proof.pf P) =
        replReplLenIdConclusion x y := by
  unfold __eo_prog_str_repl_repl_len_id at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg with
      ⟨hy, hx⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_repl_repl_len_id, __eo_requires, __eo_and, __eo_eq,
      SmtEval.native_ite, native_teq, native_and, SmtEval.native_not,
      replReplLenIdConclusion, replReplLenIdLhs]

private theorem typed___eo_prog_str_repl_repl_len_id_impl
    (x y P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : ∃ T, __eo_typeof x = Term.Apply Term.Seq T ∧
      __eo_typeof y = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_repl_repl_len_id x y (Proof.pf P) =
        replReplLenIdConclusion x y) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_repl_repl_len_id x y (Proof.pf P)) := by
  rcases hTy with ⟨T, hXTy, hYTy⟩
  let lhs := replReplLenIdLhs x y
  let rhs := x
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hXSmtTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [replReplLenIdConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_repl_repl_len_id_impl
    (M : SmtModel) (hM : model_wf M) (x y P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : ∃ T, __eo_typeof x = Term.Apply Term.Seq T ∧
      __eo_typeof y = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replReplLenIdPremise y x) true)
    (hProgEq :
      __eo_prog_str_repl_repl_len_id x y (Proof.pf P) =
        replReplLenIdConclusion x y) :
    eo_interprets M
      (__eo_prog_str_repl_repl_len_id x y (Proof.pf P)) true := by
  rcases hTy with ⟨T, hXTy, hYTy⟩
  let lhs := replReplLenIdLhs x y
  let rhs := x
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, replReplLenIdConclusion, lhs, rhs] using
      typed___eo_prog_str_repl_repl_len_id_impl x y P
        hXTrans hYTrans ⟨T, hXTy, hYTy⟩ hProgEq
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
  have hLenLe :
      (native_unpack_seq sx).length <= (native_unpack_seq sy).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_len (__eo_to_smt y))
                (SmtTerm.str_len (__eo_to_smt x)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
          hYEval, hXEval, smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq (Int.ofNat (native_unpack_seq sx).length)
                (Int.ofNat (native_unpack_seq sy).length) = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq,
            native_seq_len] using hEval
        exact Int.ofNat_le.mp (by
          simpa [SmtEval.native_zleq] using hLeBool)
  have hPack :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx) =
        sx :=
    native_pack_unpack_seq sx
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x)) =
      __smtx_model_eval M (__eo_to_smt x)
    rw [smtx_eval_str_replace_term_eq, hXEval, hYEval]
    simp [__smtx_model_eval_str_replace,
      native_seq_replace_source_of_pat_len_ge, hLenLe, hPack]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_repl_repl_len_id_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_len_id args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_repl_repl_len_id args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_len_id args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_repl_repl_len_id args premises ≠
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
                          (__eo_prog_str_repl_repl_len_id a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_repl_repl_len_id a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_repl_repl_len_id_info
                          a1 a2 P hProgRule with
                        ⟨y0, x0, hPremShape, hy0, hx0, hProgEq⟩
                      subst y0
                      subst x0
                      let lhs := replReplLenIdLhs a1 a2
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof a1) =
                        Term.Bool at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs) (__eo_typeof a1) hResultTy).1
                      have hArgTypes :
                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                            __eo_typeof a2 = Term.Apply Term.Seq T := by
                        change __eo_typeof_str_replace (__eo_typeof a1)
                            (__eo_typeof a2) (__eo_typeof a1) ≠
                          Term.Stuck at hLhsNotStuck
                        rcases eo_typeof_str_replace_args_of_ne_stuck
                            (__eo_typeof a1) (__eo_typeof a2)
                            (__eo_typeof a1) hLhsNotStuck with
                          ⟨T, hA1Ty, hA2Ty, _hA1Ty'⟩
                        exact ⟨T, hA1Ty, hA2Ty⟩
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPremRaw : eo_interprets M P true :=
                          hTrue P (by simp [P, premiseTermList])
                        have hPrem :
                            eo_interprets M
                              (replReplLenIdPremise a2 a1) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_repl_repl_len_id_impl
                          M hM a1 a2 P hA1Trans hA2Trans hArgTypes hPrem
                          hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_repl_repl_len_id_impl
                            a1 a2 P hA1Trans hA2Trans hArgTypes hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
