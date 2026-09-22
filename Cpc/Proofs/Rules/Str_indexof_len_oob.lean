module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

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

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]


private abbrev needle (s w ss : Term) := mkConcat s (mkConcat w ss)
private abbrev lhs (t s w ss n : Term) :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) (needle s w ss)) n
private abbrev conclusion (t s w ss n : Term) :=
  Term.Apply (Term.Apply Term.eq (lhs t s w ss n)) (Term.Numeral (-1))
private abbrev lengthPremise (t s : Term) :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len t)) (Term.Apply Term.str_len s)
private abbrev positivePremise (w : Term) :=
  Term.Apply (Term.Apply Term.eq
    (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len w)) (Term.Numeral 0))) (Term.Boolean true)

private theorem program_info (t s w ss n P Q : Term)
    (h : __eo_prog_str_indexof_len_oob t s w ss n (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck) :
    P = lengthPremise t s ∧ Q = positivePremise w ∧
    __eo_prog_str_indexof_len_oob t s w ss n (Proof.pf P) (Proof.pf Q) = conclusion t s w ss n := by
  unfold __eo_prog_str_indexof_len_oob at h
  split at h <;> try contradiction
  next hp hq =>
    cases hp
    cases hq
    rcases StrEqReplSupport.eqs_of_requires3_and_eq_true_not_stuck h with ⟨ht, hs, hw⟩
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_len_oob, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not, conclusion, lhs, needle, mkConcat]

private theorem needle_type (s w ss : Term) (T : SmtType)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hw : __smtx_typeof (__eo_to_smt w) = SmtType.Seq T)
    (hss : __smtx_typeof (__eo_to_smt ss) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (needle s w ss)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt s)
    (SmtTerm.str_concat (__eo_to_smt w) (__eo_to_smt ss))) = _
  simp only [typeof_str_concat_eq, hs, hw, hss]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem conclusion_typed (t s w ss n : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hw : __smtx_typeof (__eo_to_smt w) = SmtType.Seq T)
    (hss : __smtx_typeof (__eo_to_smt ss) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (conclusion t s w ss n) := by
  have hl : __smtx_typeof (__eo_to_smt (lhs t s w ss n)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt (needle s w ss)) (__eo_to_smt n)) = _
    rw [typeof_str_indexof_eq, ht, needle_type s w ss T hs hw hss, hn]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs t s w ss n) (Term.Numeral (-1))
    hl (by rw [hl]; simp)

private theorem eval_seq (M : SmtModel) (hM : model_wf M) (a : Term) (T : SmtType)
    (h : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) :
    ∃ xs, __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq xs := by
  apply seq_value_canonical
  simpa [h] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
    (term_has_non_none_of_type_eq h (by simp))

private theorem eval_concat (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat a b) =
      __smtx_model_eval_str_concat (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M)
    (t s w ss n : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hw : __smtx_typeof (__eo_to_smt w) = SmtType.Seq T)
    (hss : __smtx_typeof (__eo_to_smt ss) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hLength : eo_interprets M (lengthPremise t s) true)
    (hPositive : eo_interprets M (positivePremise w) true) :
    eo_interprets M (conclusion t s w ss n) true := by
  rcases eval_seq M hM t T ht with ⟨ts, hte⟩
  rcases eval_seq M hM s T hs with ⟨sv, hse⟩
  rcases eval_seq M hM w T hw with ⟨wv, hwe⟩
  rcases eval_seq M hM ss T hss with ⟨ssv, hsse⟩
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases int_value_canonical hnVal with ⟨ni, hne⟩
  have hLen : (native_unpack_seq ts).length = (native_unpack_seq sv).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLength
    cases hLength with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t))
        (SmtTerm.str_len (__eo_to_smt s))) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hte, hse] at he
      apply Int.ofNat.inj
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq] using he
  have hPos : 0 < (native_unpack_seq wv).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPositive
    cases hPositive with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt w))
        (SmtTerm.Numeral 0)) (SmtTerm.Boolean true)) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq, smtx_eval_str_len_term_eq,
        smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq, hwe] at he
      simpa [__smtx_model_eval_eq, __smtx_model_eval_gt, __smtx_model_eval_lt,
        __smtx_model_eval_str_len, native_seq_len, native_veq, native_zlt] using he
  have hLong : (native_unpack_seq ts).length <
      (native_unpack_seq sv ++ (native_unpack_seq wv ++ native_unpack_seq ssv)).length := by
    simp only [List.length_append]
    omega
  have hEval : __smtx_model_eval M (__eo_to_smt (lhs t s w ss n)) =
      __smtx_model_eval M (__eo_to_smt (Term.Numeral (-1))) := by
    change __smtx_model_eval M (SmtTerm.str_indexof (__eo_to_smt t)
      (SmtTerm.str_concat (__eo_to_smt s) (SmtTerm.str_concat (__eo_to_smt w) (__eo_to_smt ss)))
      (__eo_to_smt n)) = __smtx_model_eval M (SmtTerm.Numeral (-1))
    simp only [smtx_eval_str_indexof_term_eq, eval_concat, smtx_eval_numeral_term_eq,
      hte, hse, hwe, hsse, hne]
    simp [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq,
      __smtx_model_eval_str_indexof, native_seq_indexof_of_length_lt _ _ _ hLong]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs t s w ss n) (Term.Numeral (-1))
    (conclusion_typed t s w ss n T ht hs hw hss hn)
    (by rw [hEval]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_str_indexof_len_oob_properties
    (M : SmtModel) (hM : model_wf M)
    (state : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_len_oob args premises) ->
  AllHaveBoolType (premiseTermList state premises) ->
  __eo_typeof (__eo_cmd_step_proven state CRule.str_indexof_len_oob args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList state premises)
    (__eo_cmd_step_proven state CRule.str_indexof_len_oob args premises) := by
  intro hCmd _ hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons t args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons s args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons w args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons ss args =>
          cases args with
          | nil => exact False.elim (hProg rfl)
          | cons n args =>
            cases args with
            | cons _ _ => exact False.elim (hProg rfl)
            | nil =>
              cases premises with
              | nil => exact False.elim (hProg rfl)
              | cons i premises =>
                cases premises with
                | nil => exact False.elim (hProg rfl)
                | cons j premises =>
                  cases premises with
                  | cons _ _ => exact False.elim (hProg rfl)
                  | nil =>
                    let P := __eo_state_proven_nth state i
                    let Q := __eo_state_proven_nth state j
                    change __eo_typeof (__eo_prog_str_indexof_len_oob t s w ss n (Proof.pf P) (Proof.pf Q)) = Term.Bool at hTy
                    rcases program_info t s w ss n P Q (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, hQ, hp⟩
                    change StepRuleProperties M _ (__eo_prog_str_indexof_len_oob t s w ss n (Proof.pf P) (Proof.pf Q))
                    rw [hp] at hTy ⊢
                    have hl : __eo_typeof (lhs t s w ss n) ≠ Term.Stuck :=
                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                    rcases eo_typeof_str_indexof_args_of_ne_stuck _ _ _ hl with ⟨T, ht, hneedle, hn⟩
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq s (mkConcat w ss) T hneedle with ⟨hs, hinner⟩
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq w ss T hinner with ⟨hw, hss⟩
                    have htS := smtx_typeof_of_eo_seq t T hCmd.1 ht
                    have hsS := smtx_typeof_of_eo_seq s T hCmd.2.1 hs
                    have hwS := smtx_typeof_of_eo_seq w T hCmd.2.2.1 hw
                    have hssS := smtx_typeof_of_eo_seq ss T hCmd.2.2.2.1 hss
                    have hnS := smtx_typeof_of_eo_int n hCmd.2.2.2.2.1 hn
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (conclusion_typed t s w ss n _ htS hsS hwS hssS hnS)⟩
                    intro hTrue
                    apply conclusion_facts M hM t s w ss n _ htS hsS hwS hssS hnS
                    · have h := hTrue P (by simp [P, premiseTermList])
                      simpa [hP] using h
                    · have h := hTrue Q (by simp [Q, premiseTermList])
                      simpa [hQ] using h
