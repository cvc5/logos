module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

public import Cpc.Proofs.RuleSupport.StrLeqConcatSupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_update_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_update A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Int ∧ C = Term.Apply Term.Seq T := by
  cases A <;> simp [__eo_typeof_str_update] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_update] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_update] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_update] at h ⊢
        case UOp opB =>
          cases opB <;> simp [__eo_typeof_str_update] at h ⊢
          case Int =>
            cases C <;>
              simp [__eo_typeof_str_update] at h ⊢
            case Apply g y =>
              cases g <;>
                simp [__eo_typeof_str_update] at h ⊢
              case UOp opC =>
                cases opC <;>
                  simp [__eo_typeof_str_update] at h ⊢
                case Seq =>
                  have hReqNe :
                      __eo_requires (__eo_eq x y) (Term.Boolean true)
                          (Term.Apply Term.Seq x) ≠ Term.Stuck := by
                    intro hReq
                    apply h
                    rw [hReq]
                  exact RuleProofs.eq_of_requires_eq_true_not_stuck x y
                    (Term.Apply Term.Seq x) hReqNe

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

private theorem smtx_eval_str_update_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_update x y n) =
      __smtx_model_eval_str_update
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


private abbrev source (p r qs : Term) := mkConcat p (mkConcat r qs)
private abbrev lhs (p r qs n x : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_update (source p r qs)) n) x
private abbrev conclusion (p r qs n x : Term) := Term.Apply (Term.Apply Term.eq (lhs p r qs n x)) (source p x qs)
private abbrev indexPremise (p n : Term) := Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len p)) n
private abbrev lengthPremise (r x : Term) := Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len r)) (Term.Apply Term.str_len x)

private theorem program_info (p r qs n x P Q : Term)
    (h : __eo_prog_str_update_concat_fit p r qs n x (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck) :
    P = indexPremise p n ∧ Q = lengthPremise r x ∧
    __eo_prog_str_update_concat_fit p r qs n x (Proof.pf P) (Proof.pf Q) = conclusion p r qs n x := by
  unfold __eo_prog_str_update_concat_fit at h
  split at h <;> try contradiction
  next hp hq =>
    cases hp
    cases hq
    rcases StrLeqConcatSupport.eqs_of_requires4_and_eq_true_not_stuck _ _ _ _ _ _ _ _ _ h with ⟨hp, hn, hr, hx⟩
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp [__eo_prog_str_update_concat_fit, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not, conclusion, lhs, source, mkConcat]

private theorem source_type (p r qs : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (source p r qs)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt p)
    (SmtTerm.str_concat (__eo_to_smt r) (__eo_to_smt qs))) = _
  simp only [typeof_str_concat_eq, hp, hr, hqs]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem conclusion_typed (p r qs n x : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (conclusion p r qs n x) := by
  have hl : __smtx_typeof (__eo_to_smt (lhs p r qs n x)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_update (__eo_to_smt (source p r qs)) (__eo_to_smt n) (__eo_to_smt x)) = _
    rw [typeof_str_update_eq, source_type p r qs T hp hr hqs, hn, hx]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hl.trans (source_type p x qs T hp hx hqs).symm) (by rw [hl]; simp)

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M)
    (p r qs n x : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIndex : eo_interprets M (indexPremise p n) true)
    (hLength : eo_interprets M (lengthPremise r x) true) :
    eo_interprets M (conclusion p r qs n x) true := by
  rcases eval_seq M hM p T hp with ⟨ps, hpe⟩
  rcases eval_seq M hM r T hr with ⟨rs, hre⟩
  rcases eval_seq M hM qs T hqs with ⟨qss, hqse⟩
  rcases eval_seq M hM x T hx with ⟨xs, hxe⟩
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases int_value_canonical hnVal with ⟨ni, hne⟩
  have hi : ni = ((native_unpack_seq ps).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hIndex
    cases hIndex with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt p)) (__eo_to_smt n)) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hpe, hne] at he
      symm
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq] using he
  have hLen : (native_unpack_seq rs).length = (native_unpack_seq xs).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLength
    cases hLength with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt r))
        (SmtTerm.str_len (__eo_to_smt x))) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hre, hxe] at he
      apply Int.ofNat.inj
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq] using he
  have hu := native_seq_update_replace_middle (native_unpack_seq ps) (native_unpack_seq rs)
    (native_unpack_seq qss) (native_unpack_seq xs) hLen
  have heq : __smtx_model_eval M (__eo_to_smt (lhs p r qs n x)) =
      __smtx_model_eval M (__eo_to_smt (source p x qs)) := by
    change __smtx_model_eval M (SmtTerm.str_update
      (SmtTerm.str_concat (__eo_to_smt p) (SmtTerm.str_concat (__eo_to_smt r) (__eo_to_smt qs)))
      (__eo_to_smt n) (__eo_to_smt x)) =
      __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt p) (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt qs)))
    simp only [smtx_eval_str_update_term_eq, eval_concat, hpe, hre, hqse, hxe, hne, hi]
    simp [__smtx_model_eval_str_update, __smtx_model_eval_str_concat, native_seq_concat,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, ← List.append_assoc]
    exact congrArg (native_pack_seq (__smtx_elem_typeof_seq_value ps)) hu
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ (conclusion_typed p r qs n x T hp hr hqs hn hx)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_str_update_concat_fit_properties
    (M : SmtModel) (hM : model_wf M)
    (state : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_concat_fit args premises) ->
  AllHaveBoolType (premiseTermList state premises) ->
  __eo_typeof (__eo_cmd_step_proven state CRule.str_update_concat_fit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList state premises)
    (__eo_cmd_step_proven state CRule.str_update_concat_fit args premises) := by
  intro hCmd _ hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons p args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons r args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons qs args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons n args =>
          cases args with
          | nil => exact False.elim (hProg rfl)
          | cons x args =>
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
                    change __eo_typeof (__eo_prog_str_update_concat_fit p r qs n x (Proof.pf P) (Proof.pf Q)) = Term.Bool at hTy
                    rcases program_info p r qs n x P Q (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, hQ, he⟩
                    change StepRuleProperties M _ (__eo_prog_str_update_concat_fit p r qs n x (Proof.pf P) (Proof.pf Q))
                    rw [he] at hTy ⊢
                    have hl : __eo_typeof (lhs p r qs n x) ≠ Term.Stuck :=
                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                    rcases eo_typeof_str_update_args_of_ne_stuck _ _ _ hl with ⟨T, hsource, hn, hx⟩
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq p (mkConcat r qs) T hsource with ⟨hp, hinner⟩
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq r qs T hinner with ⟨hr, hqs⟩
                    have hpS := smtx_typeof_of_eo_seq p T hCmd.1 hp
                    have hrS := smtx_typeof_of_eo_seq r T hCmd.2.1 hr
                    have hqsS := smtx_typeof_of_eo_seq qs T hCmd.2.2.1 hqs
                    have hnS := smtx_typeof_of_eo_int n hCmd.2.2.2.1 hn
                    have hxS := smtx_typeof_of_eo_seq x T hCmd.2.2.2.2.1 hx
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (conclusion_typed p r qs n x _ hpS hrS hqsS hnS hxS)⟩
                    intro hTrue
                    apply conclusion_facts M hM p r qs n x _ hpS hrS hqsS hnS hxS
                    · have h := hTrue P (by simp [P, premiseTermList])
                      simpa [hP] using h
                    · have h := hTrue Q (by simp [Q, premiseTermList])
                      simpa [hQ] using h
