module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

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


private abbrev update (t n r : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_update t) n) r
private abbrev rev (t : Term) := Term.Apply Term.str_rev t
private abbrev reflected (t n : Term) := Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len t))
  (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))
private abbrev conclusion (t n r : Term) :=
  Term.Apply (Term.Apply Term.eq (update (rev t) n r)) (rev (update t (reflected t n) r))
private abbrev premise (r : Term) :=
  Term.Apply (Term.Apply Term.eq
    (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_len r)) (Term.Numeral 1))) (Term.Boolean true)

private theorem program_info (t n r P : Term)
    (h : __eo_prog_str_update_rev t n r (Proof.pf P) ≠ Term.Stuck) :
    P = premise r ∧ __eo_prog_str_update_rev t n r (Proof.pf P) = conclusion t n r := by
  unfold __eo_prog_str_update_rev at h
  split at h <;> try contradiction
  next hp =>
    cases hp
    have hr := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ h
    subst_vars
    refine ⟨rfl, ?_⟩
    simp [__eo_prog_str_update_rev, __eo_requires, __eo_eq, native_ite, native_teq,
      SmtEval.native_not, conclusion, update, rev, reflected]

private theorem rev_arg_type (A T : Term) (h : __eo_typeof_str_rev A = Term.Apply Term.Seq T) :
    A = Term.Apply Term.Seq T := by
  cases A <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f a =>
    cases f <;> simp at h ⊢
    case UOp op => cases op <;> simp_all

private theorem conclusion_typed (t n r : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (conclusion t n r) := by
  have hRev : __smtx_typeof (__eo_to_smt (rev t)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt t)) = _
    rw [typeof_str_rev_eq, ht]; rfl
  have hIndex : __smtx_typeof (__eo_to_smt (reflected t n)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
      (SmtTerm.plus (__eo_to_smt n) (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)))) = _
    simp only [typeof_neg_eq, typeof_plus_eq, typeof_str_len_eq, ht, hn]
    rfl
  have hu (a i : Term) (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
      (hi : __smtx_typeof (__eo_to_smt i) = SmtType.Int) :
      __smtx_typeof (__eo_to_smt (update a i r)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_update (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt r)) = _
    rw [typeof_str_update_eq, ha, hi, hr]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  have hl := hu (rev t) n hRev hn
  have hright : __smtx_typeof (__eo_to_smt (rev (update t (reflected t n) r))) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt (update t (reflected t n) r))) = _
    rw [typeof_str_rev_eq, hu t (reflected t n) ht hIndex]; rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hl.trans hright.symm) (by rw [hl]; simp)

private theorem eval_rev (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_rev a) = __smtx_model_eval_str_rev (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def]
private theorem eval_plus (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus a b) =
      __smtx_model_eval_plus (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]
private theorem eval_neg (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg a b) =
      __smtx_model_eval__ (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]
private theorem eval_leq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq a b) =
      __smtx_model_eval_leq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

private theorem elem_pack (T : SmtType) (xs : List SmtValue) :
    __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [native_pack_seq, __smtx_elem_typeof_seq_value] using ih

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M) (t n r : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hPrem : eo_interprets M (premise r) true) :
    eo_interprets M (conclusion t n r) true := by
  rcases eval_seq M hM t T ht with ⟨ts, hte⟩
  rcases eval_seq M hM r T hr with ⟨rs, hre⟩
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases int_value_canonical hnVal with ⟨ni, hne⟩
  have hLen : (native_unpack_seq rs).length ≤ 1 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.leq (SmtTerm.str_len (__eo_to_smt r))
        (SmtTerm.Numeral 1)) (SmtTerm.Boolean true)) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, eval_leq, smtx_eval_str_len_term_eq,
        smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq, hre] at he
      have hi : ((native_unpack_seq rs).length : Int) ≤ 1 := by
        simpa [__smtx_model_eval_eq, __smtx_model_eval_leq, __smtx_model_eval_str_len,
          native_seq_len, native_veq, native_zleq] using he
      omega
  have heq : __smtx_model_eval M (__eo_to_smt (update (rev t) n r)) =
      __smtx_model_eval M (__eo_to_smt (rev (update t (reflected t n) r))) := by
    change __smtx_model_eval M (SmtTerm.str_update (SmtTerm.str_rev (__eo_to_smt t))
      (__eo_to_smt n) (__eo_to_smt r)) =
      __smtx_model_eval M (SmtTerm.str_rev (SmtTerm.str_update (__eo_to_smt t)
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
          (SmtTerm.plus (__eo_to_smt n) (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))))
        (__eo_to_smt r)))
    simp only [smtx_eval_str_update_term_eq, eval_rev, eval_neg, eval_plus,
      smtx_eval_str_len_term_eq, smtx_eval_numeral_term_eq, hte, hre, hne]
    simp [__smtx_model_eval_str_update, __smtx_model_eval_str_rev, __smtx_model_eval_str_len,
      __smtx_model_eval__, __smtx_model_eval_plus, native_zplus, native_zneg,
      native_seq_len, native_seq_rev, Smtm.native_unpack_pack_seq, elem_pack,
      native_seq_update_reverse_of_length_le_one _ _ ni hLen, Int.sub_eq_add_neg]
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ (conclusion_typed t n r T ht hn hr)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_str_update_rev_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_update_rev args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_update_rev args premises) := by
  intro hCmd _ hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons t args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons n args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons r args =>
        cases args with
        | cons _ _ => exact False.elim (hProg rfl)
        | nil =>
          cases premises with
          | nil => exact False.elim (hProg rfl)
          | cons idx premises =>
            cases premises with
            | cons _ _ => exact False.elim (hProg rfl)
            | nil =>
              let P := __eo_state_proven_nth s idx
              change __eo_typeof (__eo_prog_str_update_rev t n r (Proof.pf P)) = Term.Bool at hTy
              rcases program_info t n r P (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, hp⟩
              change StepRuleProperties M _ (__eo_prog_str_update_rev t n r (Proof.pf P))
              rw [hp] at hTy ⊢
              have hl : __eo_typeof (update (rev t) n r) ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
              rcases eo_typeof_str_update_args_of_ne_stuck _ _ _ hl with ⟨T, hrev, hn, hr⟩
              have ht := rev_arg_type (__eo_typeof t) T hrev
              have htS := smtx_typeof_of_eo_seq t T hCmd.1 ht
              have hnS := smtx_typeof_of_eo_int n hCmd.2.1 hn
              have hrS := smtx_typeof_of_eo_seq r T hCmd.2.2.1 hr
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                (conclusion_typed t n r _ htS hnS hrS)⟩
              intro hTrue
              apply conclusion_facts M hM t n r _ htS hnS hrS
              have h := hTrue P (by simp [P, premiseTermList])
              simpa [hP] using h
