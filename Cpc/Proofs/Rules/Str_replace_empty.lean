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

private abbrev replaceEmptyPremise (r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len r))
    (Term.Numeral 0)

private abbrev replaceEmptyLhs (t s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace t) r) s

private abbrev replaceEmptyGeneratedRhs (t s : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.str_concat s)
    (__eo_mk_apply (Term.Apply Term.str_concat t)
      (__eo_nil Term.str_concat (__eo_typeof s)))

private abbrev replaceEmptyGeneratedConclusion (t s r : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.eq (replaceEmptyLhs t s r))
    (replaceEmptyGeneratedRhs t s)

private abbrev replaceEmptyRhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s)
    (Term.Apply (Term.Apply Term.str_concat t)
      (__seq_empty (__eo_typeof s)))

private abbrev replaceEmptyConclusion (t s r : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceEmptyLhs t s r))
    (replaceEmptyRhs t s)

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

private theorem smtx_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

private theorem term_apply_ne_stuck (f a : Term) :
    Term.Apply f a ≠ Term.Stuck := by
  intro h
  cases h

private theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op =>
    cases op <;> simp [__seq_empty, Term.Seq]

private theorem mk_apply_apply_eq (f a b : Term)
    (hB : b ≠ Term.Stuck) :
    __eo_mk_apply (Term.Apply f a) b = Term.Apply (Term.Apply f a) b := by
  cases b <;> simp [__eo_mk_apply] at hB ⊢

private theorem generated_conclusion_eq
    (t s r : Term) (T : Term)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T) :
    replaceEmptyGeneratedConclusion t s r =
      replaceEmptyConclusion t s r := by
  have hNil :
      __eo_nil Term.str_concat (__eo_typeof s) =
        __seq_empty (__eo_typeof s) := by
    rw [hSTy]
    rfl
  have hEmptyNotStuck : __seq_empty (__eo_typeof s) ≠ Term.Stuck := by
    rw [hSTy]
    exact seq_empty_seq_ne_stuck T
  have hInner :
      __eo_mk_apply (Term.Apply Term.str_concat t)
          (__eo_nil Term.str_concat (__eo_typeof s)) =
        Term.Apply (Term.Apply Term.str_concat t)
          (__seq_empty (__eo_typeof s)) := by
    rw [hNil]
    exact mk_apply_apply_eq Term.str_concat t
      (__seq_empty (__eo_typeof s)) hEmptyNotStuck
  have hInnerNotStuck :
      Term.Apply (Term.Apply Term.str_concat t)
          (__seq_empty (__eo_typeof s)) ≠ Term.Stuck :=
    term_apply_ne_stuck (Term.Apply Term.str_concat t)
      (__seq_empty (__eo_typeof s))
  have hOuter :
      __eo_mk_apply (Term.Apply Term.str_concat s)
          (__eo_mk_apply (Term.Apply Term.str_concat t)
            (__eo_nil Term.str_concat (__eo_typeof s))) =
        replaceEmptyRhs t s := by
    rw [hInner]
    exact mk_apply_apply_eq Term.str_concat s
      (Term.Apply (Term.Apply Term.str_concat t)
        (__seq_empty (__eo_typeof s))) hInnerNotStuck
  have hOuterNotStuck : replaceEmptyRhs t s ≠ Term.Stuck :=
    term_apply_ne_stuck (Term.Apply Term.str_concat s)
      (Term.Apply (Term.Apply Term.str_concat t)
        (__seq_empty (__eo_typeof s)))
  rw [replaceEmptyGeneratedConclusion, replaceEmptyGeneratedRhs,
    replaceEmptyConclusion, hOuter]
  exact mk_apply_apply_eq Term.eq (replaceEmptyLhs t s r)
    (replaceEmptyRhs t s) hOuterNotStuck

private theorem lhs_type_ne_stuck_of_generated_type_bool
    (t s r : Term)
    (hTy : __eo_typeof (replaceEmptyGeneratedConclusion t s r) = Term.Bool) :
    __eo_typeof (replaceEmptyLhs t s r) ≠ Term.Stuck := by
  let lhs := replaceEmptyLhs t s r
  let rhsGen := replaceEmptyGeneratedRhs t s
  have hGeneratedNotStuck :
      replaceEmptyGeneratedConclusion t s r ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hRhsGenNotStuck : rhsGen ≠ Term.Stuck := by
    intro hStuck
    apply hGeneratedNotStuck
    dsimp [replaceEmptyGeneratedConclusion]
    change __eo_mk_apply (Term.Apply Term.eq (replaceEmptyLhs t s r)) rhsGen =
      Term.Stuck
    rw [hStuck]
    rfl
  have hGenEq :
      replaceEmptyGeneratedConclusion t s r =
        Term.Apply (Term.Apply Term.eq lhs) rhsGen := by
    dsimp [replaceEmptyGeneratedConclusion, lhs]
    exact mk_apply_apply_eq Term.eq (replaceEmptyLhs t s r) rhsGen
      hRhsGenNotStuck
  rw [hGenEq] at hTy
  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhsGen) =
    Term.Bool at hTy
  exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof lhs) (__eo_typeof rhsGen) hTy).1

private theorem smtx_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_replace_nil
    (xs repl : List SmtValue) :
    native_seq_replace xs [] repl = repl ++ xs := by
  simp [native_seq_replace]

private theorem list_eq_nil_of_native_seq_len_zero (xs : List SmtValue)
    (h : native_seq_len xs = 0) :
    xs = [] := by
  have hLenInt : (xs.length : Int) = 0 := by
    simpa [native_seq_len] using h
  have hLenNat : xs.length = 0 := by
    omega
  cases xs with
  | nil => rfl
  | cons _ _ => simp at hLenNat

private theorem prog_str_replace_empty_info
    (t s r P : Term)
    (hProg : __eo_prog_str_replace_empty t s r (Proof.pf P) ≠
      Term.Stuck) :
    ∃ r0,
      P = replaceEmptyPremise r0 ∧
      r0 = r ∧
      __eo_prog_str_replace_empty t s r (Proof.pf P) =
        replaceEmptyGeneratedConclusion t s r := by
  unfold __eo_prog_str_replace_empty at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hr :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_empty, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      replaceEmptyGeneratedConclusion, replaceEmptyGeneratedRhs,
      replaceEmptyLhs]

private theorem typed___eo_prog_str_replace_empty_impl
    (t s r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hProgGen :
      __eo_prog_str_replace_empty t s r (Proof.pf P) =
        replaceEmptyGeneratedConclusion t s r) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_empty t s r (Proof.pf P)) := by
  rcases hTy with ⟨T, hTTy, hSTy, hRTy⟩
  let lhs := replaceEmptyLhs t s r
  let rhs := replaceEmptyRhs t s
  have hProgEq :
      __eo_prog_str_replace_empty t s r (Proof.pf P) =
        replaceEmptyConclusion t s r := by
    rw [hProgGen, generated_conclusion_eq t s r T hSTy]
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) =
        SmtType.Seq (__eo_to_smt_type T) :=
    smtx_typeof_seq_empty_typeof_of_smt_type_seq s (__eo_to_smt_type T)
      hSSmtTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt r)
          (__eo_to_smt s)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hTSmtTy, hRSmtTy, hSSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hInnerSmtTy :
      __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt t)
          (__eo_to_smt (__seq_empty (__eo_typeof s)))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hTSmtTy, hEmptyTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply Term.str_concat t)
            (__seq_empty (__eo_typeof s)))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa using hInnerSmtTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s)
          (SmtTerm.str_concat (__eo_to_smt t)
            (__eo_to_smt (__seq_empty (__eo_typeof s))))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hSSmtTy, hInnerSmtTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  simpa [replaceEmptyConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_replace_empty_impl
    (M : SmtModel) (hM : model_wf M) (t s r P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hTy : ∃ T, __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replaceEmptyPremise r) true)
    (hProgGen :
      __eo_prog_str_replace_empty t s r (Proof.pf P) =
        replaceEmptyGeneratedConclusion t s r) :
    eo_interprets M
      (__eo_prog_str_replace_empty t s r (Proof.pf P)) true := by
  rcases hTy with ⟨T, hTTy, hSTy, hRTy⟩
  let lhs := replaceEmptyLhs t s r
  let rhs := replaceEmptyRhs t s
  have hProgEq :
      __eo_prog_str_replace_empty t s r (Proof.pf P) =
        replaceEmptyConclusion t s r := by
    rw [hProgGen, generated_conclusion_eq t s r T hSTy]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, replaceEmptyConclusion, lhs, rhs] using
      typed___eo_prog_str_replace_empty_impl t s r P
        hTTrans hSTrans hRTrans ⟨T, hTTy, hSTy, hRTy⟩ hProgGen
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
  have hRLenZero : native_seq_len (native_unpack_seq rs) = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt r)) (SmtTerm.Numeral 0)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hREval] at hEval
        rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
          rw [__smtx_model_eval.eq_def]] at hEval
        simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_veq]
          using hEval
  have hRNil : native_unpack_seq rs = [] :=
    list_eq_nil_of_native_seq_len_zero (native_unpack_seq rs) hRLenZero
  have hTSeqTy :
      __smtx_typeof_seq_value ts = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hTEval] using hTEvalTy
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hTElem : __smtx_elem_typeof_seq_value ts = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof s))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) :=
    eval_seq_empty_typeof M s (__eo_to_smt_type T) hSSmtTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt r)
          (__eo_to_smt s)) =
      __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s)
          (SmtTerm.str_concat (__eo_to_smt t)
            (__eo_to_smt (__seq_empty (__eo_typeof s)))))
    rw [smtx_eval_str_replace_term_eq]
    rw [smtx_eval_str_concat_term_eq M (__eo_to_smt s)
      (SmtTerm.str_concat (__eo_to_smt t)
        (__eo_to_smt (__seq_empty (__eo_typeof s))))]
    rw [smtx_eval_str_concat_term_eq M (__eo_to_smt t)
      (__eo_to_smt (__seq_empty (__eo_typeof s)))]
    rw [hTEval, hSEval, hREval, hEmptyEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_concat,
      native_seq_replace_nil, native_seq_concat, native_unpack_seq,
      Smtm.native_unpack_pack_seq, hRNil, hTElem, hSElem]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_empty_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_empty args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_empty args premises ≠
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
                              (__eo_prog_str_replace_empty a1 a2 a3 (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_replace_empty a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_replace_empty_info
                              a1 a2 a3 P hProgRule with
                            ⟨r0, hPremShape, hr0, hProgGen⟩
                          subst r0
                          let lhs := replaceEmptyLhs a1 a2 a3
                          let rhsGen := replaceEmptyGeneratedRhs a1 a2
                          rw [hProgGen] at hResultTy
                          change __eo_typeof (replaceEmptyGeneratedConclusion a1 a2 a3) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck := by
                            simpa [lhs] using
                              lhs_type_ne_stuck_of_generated_type_bool a1 a2 a3
                                hResultTy
                          have hArgTypes :
                              ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Apply Term.Seq T := by
                            change __eo_typeof_str_replace (__eo_typeof a1)
                                (__eo_typeof a3) (__eo_typeof a2) ≠
                              Term.Stuck at hLhsNotStuck
                            rcases eo_typeof_str_replace_args_of_ne_stuck
                                (__eo_typeof a1) (__eo_typeof a3)
                                (__eo_typeof a2) hLhsNotStuck with
                              ⟨T, hA1Ty, hA3Ty, hA2Ty⟩
                            exact ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M (replaceEmptyPremise a3) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_replace_empty_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hArgTypes hPrem hProgGen
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_replace_empty_impl
                                a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hArgTypes hProgGen)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
