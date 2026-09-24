module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev lenReplaceAllPremise (s r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len s))
    (Term.Apply Term.str_len r)

private abbrev lenReplaceAllLhs (t s r : Term) : Term :=
  Term.Apply Term.str_len
    (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) s) r)

private abbrev lenReplaceAllRhs (t : Term) : Term :=
  Term.Apply Term.str_len t

private abbrev lenReplaceAllConclusion (t s r : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lenReplaceAllLhs t s r))
    (lenReplaceAllRhs t)

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

private theorem eo_typeof_str_len_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_len (__eo_typeof_str_replace A B C) ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  have hReplace : __eo_typeof_str_replace A B C ≠ Term.Stuck := by
    intro hStuck
    apply h
    rw [hStuck]
    simp [__eo_typeof_str_len]
  exact eo_typeof_str_replace_args_of_ne_stuck A B C hReplace

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

private theorem smtx_eval_str_replace_all_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_all x y z) =
      __smtx_model_eval_str_replace_all
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

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

private theorem native_seq_replace_all_aux_length_eq_of_same_len
    (fuel : Nat) (xs pat repl : List SmtValue)
    (hLen : pat.length = repl.length) :
    (native_seq_replace_all xs pat repl).length = xs.length := by
  exact StrReplaceAllSupport.replace_all_length_eq_of_same_len
    pat repl xs hLen

private theorem native_seq_replace_all_length_eq_of_same_len
    (xs pat repl : List SmtValue)
    (hLen : pat.length = repl.length) :
    (native_seq_replace_all xs pat repl).length = xs.length := by
  exact native_seq_replace_all_aux_length_eq_of_same_len
    (xs.length + 1) xs pat repl hLen

private theorem prog_str_len_replace_all_inv_info
    (t s r P : Term)
    (hProg : __eo_prog_str_len_replace_all_inv t s r (Proof.pf P) ≠
      Term.Stuck) :
    ∃ s0 r0,
      P = lenReplaceAllPremise s0 r0 ∧
      s0 = s ∧
      r0 = r ∧
      __eo_prog_str_len_replace_all_inv t s r (Proof.pf P) =
        lenReplaceAllConclusion t s r := by
  unfold __eo_prog_str_len_replace_all_inv at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hEq :=
      RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg
    rcases hEq with ⟨hs, hr⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_len_replace_all_inv, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, lenReplaceAllConclusion, lenReplaceAllLhs,
      lenReplaceAllRhs]

private theorem typed___eo_prog_str_len_replace_all_inv_impl
    (t s r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_len_replace_all_inv t s r (Proof.pf P) =
        lenReplaceAllConclusion t s r) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_len_replace_all_inv t s r (Proof.pf P)) := by
  rcases hTy with ⟨T, hTTy, hSTy, hRTy⟩
  let repl := Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) s) r
  let lhs := Term.Apply Term.str_len repl
  let rhs := Term.Apply Term.str_len t
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hReplTy :
      __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt r)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_all_eq]
    simp [hTSmtTy, hSSmtTy, hRSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_len
          (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt r))) =
      SmtType.Int
    rw [typeof_str_len_eq]
    rw [show
        __smtx_typeof
            (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt r)) =
          SmtType.Seq (__eo_to_smt_type T) by
      change __smtx_typeof (__eo_to_smt repl) =
        SmtType.Seq (__eo_to_smt_type T)
      exact hReplTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt t)) = SmtType.Int
    rw [typeof_str_len_eq, hTSmtTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [lenReplaceAllConclusion, lenReplaceAllLhs, lenReplaceAllRhs, lhs,
    rhs, repl] using hBoolEq

private theorem facts___eo_prog_str_len_replace_all_inv_impl
    (M : SmtModel) (hM : model_wf M) (t s r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (lenReplaceAllPremise s r) true)
    (hProgEq :
      __eo_prog_str_len_replace_all_inv t s r (Proof.pf P) =
        lenReplaceAllConclusion t s r) :
    eo_interprets M
      (__eo_prog_str_len_replace_all_inv t s r (Proof.pf P)) true := by
  rcases hTy with ⟨T, hTTy, hSTy, hRTy⟩
  let repl := Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) s) r
  let lhs := Term.Apply Term.str_len repl
  let rhs := Term.Apply Term.str_len t
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, lenReplaceAllConclusion, lenReplaceAllLhs,
      lenReplaceAllRhs, lhs, rhs, repl] using
      typed___eo_prog_str_len_replace_all_inv_impl t s r P
        hTTrans hSTrans hRTrans ⟨T, hTTy, hSTy, hRTy⟩ hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
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
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  have hLenEq :
      (native_unpack_seq ss).length = (native_unpack_seq rs).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_len (__eo_to_smt s))
              (SmtTerm.str_len (__eo_to_smt r))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
          smtx_eval_str_len_term_eq, hSEval, hREval] at hEval
        have hLenInt :
            Int.ofNat (native_unpack_seq ss).length =
              Int.ofNat (native_unpack_seq rs).length := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        exact Int.ofNat.inj hLenInt
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_len
          (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt r))) =
      __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t))
    rw [smtx_eval_str_len_term_eq, smtx_eval_str_replace_all_term_eq,
      smtx_eval_str_len_term_eq]
    rw [hTEval, hSEval, hREval]
    simp [__smtx_model_eval_str_replace_all, __smtx_model_eval_str_len,
      native_seq_len, Smtm.native_unpack_pack_seq,
      native_seq_replace_all_length_eq_of_same_len, hLenEq]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_len_replace_all_inv_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_replace_all_inv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_len_replace_all_inv args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_replace_all_inv args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_len_replace_all_inv args premises ≠
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
                              (__eo_prog_str_len_replace_all_inv a1 a2 a3 (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_len_replace_all_inv a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_len_replace_all_inv_info
                              a1 a2 a3 P hProgRule with
                            ⟨s0, r0, hPremShape, hs0, hr0, hProgEq⟩
                          subst s0
                          subst r0
                          let lhs := lenReplaceAllLhs a1 a2 a3
                          let rhs := lenReplaceAllRhs a1
                          rw [hProgEq] at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Apply Term.Seq T := by
                            change __eo_typeof_str_len
                                (__eo_typeof_str_replace (__eo_typeof a1)
                                  (__eo_typeof a2) (__eo_typeof a3)) ≠
                              Term.Stuck at hLhsNotStuck
                            exact eo_typeof_str_len_str_replace_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a3) hLhsNotStuck
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (lenReplaceAllPremise a2 a3) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_len_replace_all_inv_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hArgTypes hPrem hProgEq
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_len_replace_all_inv_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hArgTypes hProgEq)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
