module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport

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


private abbrev joined (ts rs : Term) := __eo_list_concat Term.str_concat ts rs
private abbrev source (t ts rs : Term) := mkConcat t (joined ts rs)
private abbrev pattern (t ts : Term) := mkConcat t ts
private abbrev lhs (t ts rs : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_indexof (source t ts rs)) (pattern t ts)) (Term.Numeral 0)
private abbrev conclusion (t ts rs : Term) := Term.Apply (Term.Apply Term.eq (lhs t ts rs)) (Term.Numeral 0)

private theorem program_info (t ts rs : Term)
    (ht : t ≠ Term.Stuck) (hts : ts ≠ Term.Stuck) (hrs : rs ≠ Term.Stuck)
    (h : __eo_prog_str_indexof_prefix_concat t ts rs ≠ Term.Stuck) :
    __eo_is_list Term.str_concat ts = Term.Boolean true ∧
    __eo_is_list Term.str_concat rs = Term.Boolean true ∧
    __eo_prog_str_indexof_prefix_concat t ts rs = conclusion t ts rs := by
  rw [__eo_prog_str_indexof_prefix_concat.eq_4 t ts rs ht hts hrs] at h ⊢
  have h1 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have h2 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h1
  have h3 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h2
  have h4 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h3
  have h5 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h4
  have h6 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h5
  have htsList := support_eo_requires_cond_eq_of_non_stuck h6
  have hinner := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h6
  have hrsList := support_eo_requires_cond_eq_of_non_stuck hinner
  refine ⟨htsList, hrsList, ?_⟩
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ h1,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ h2,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ h3,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ h4,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ h5]

private theorem concat_type (a b : Term) (T : SmtType)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat a b)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [typeof_str_concat_eq, ha, hb]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem conclusion_typed (t ts rs : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hts : __smtx_typeof (__eo_to_smt ts) = SmtType.Seq T)
    (hrs : __smtx_typeof (__eo_to_smt rs) = SmtType.Seq T)
    (htsList : __eo_is_list Term.str_concat ts = Term.Boolean true)
    (hrsList : __eo_is_list Term.str_concat rs = Term.Boolean true) :
    RuleProofs.eo_has_bool_type (conclusion t ts rs) := by
  have hjoin := StringRewriteSupport.list_concat_has_seq_type ts rs T htsList hrsList hts hrs
  have hsource := concat_type t (joined ts rs) T ht hjoin
  have hpat := concat_type t ts T ht hts
  have hl : __smtx_typeof (__eo_to_smt (lhs t ts rs)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_indexof (__eo_to_smt (source t ts rs))
      (__eo_to_smt (pattern t ts)) (SmtTerm.Numeral 0)) = _
    rw [typeof_str_indexof_eq, hsource, hpat]
    simp [__smtx_typeof, __smtx_typeof_str_indexof, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ hl (by rw [hl]; simp)

private theorem prefix_index (pat rest : List SmtValue) :
    native_seq_indexof (pat ++ rest) pat 0 = 0 := by
  rw [native_seq_indexof_eq_rec]
  have hb : pat.length ≤ (pat ++ rest).length := by simp
  simp only [List.length_append] at hb
  simp [hb]
  rw [native_seq_indexof_rec.eq_def]
  simp [StringRewriteSupport.native_seq_prefix_eq_append_self]

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M)
    (t ts rs : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hts : __smtx_typeof (__eo_to_smt ts) = SmtType.Seq T)
    (hrs : __smtx_typeof (__eo_to_smt rs) = SmtType.Seq T)
    (htsList : __eo_is_list Term.str_concat ts = Term.Boolean true)
    (hrsList : __eo_is_list Term.str_concat rs = Term.Boolean true) :
    eo_interprets M (conclusion t ts rs) true := by
  rcases eval_seq M hM t T ht with ⟨tv, hte⟩
  rcases eval_seq M hM ts T hts with ⟨tsv, htse⟩
  rcases eval_seq M hM rs T hrs with ⟨rsv, hrse⟩
  have hjoin := StringRewriteSupport.list_concat_eval M hM ts rs T tsv rsv
    htsList hrsList hts hrs htse hrse
  have heq : __smtx_model_eval M (__eo_to_smt (lhs t ts rs)) =
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) := by
    change __smtx_model_eval M (SmtTerm.str_indexof
      (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt (joined ts rs)))
      (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt ts)) (SmtTerm.Numeral 0)) =
      __smtx_model_eval M (SmtTerm.Numeral 0)
    simp only [smtx_eval_str_indexof_term_eq, eval_concat, smtx_eval_numeral_term_eq,
      hte, htse, hjoin]
    simp [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq,
      __smtx_model_eval_str_indexof, ← List.append_assoc, prefix_index]
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ (conclusion_typed t ts rs T ht hts hrs htsList hrsList)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

private theorem translated_ne (a : Term) (h : RuleProofs.eo_has_smt_translation a) : a ≠ Term.Stuck := by
  intro ha
  subst a
  exact h rfl

public theorem cmd_step_str_indexof_prefix_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (state : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_prefix_concat args premises) ->
  AllHaveBoolType (premiseTermList state premises) ->
  __eo_typeof (__eo_cmd_step_proven state CRule.str_indexof_prefix_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList state premises)
    (__eo_cmd_step_proven state CRule.str_indexof_prefix_concat args premises) := by
  intro hCmd _ hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons t args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons ts args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons rs args =>
        cases args with
        | cons _ _ => exact False.elim (hProg rfl)
        | nil =>
          cases premises with
          | cons _ _ => exact False.elim (hProg rfl)
          | nil =>
            change __eo_typeof (__eo_prog_str_indexof_prefix_concat t ts rs) = Term.Bool at hTy
            rcases program_info t ts rs (translated_ne t hCmd.1) (translated_ne ts hCmd.2.1)
              (translated_ne rs hCmd.2.2.1) (term_ne_stuck_of_typeof_bool hTy) with ⟨htsList, hrsList, he⟩
            change StepRuleProperties M _ (__eo_prog_str_indexof_prefix_concat t ts rs)
            rw [he] at hTy ⊢
            have hl : __eo_typeof (lhs t ts rs) ≠ Term.Stuck :=
              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
            rcases eo_typeof_str_indexof_args_of_ne_stuck _ _ _ hl with ⟨T, hsource, hpat, _⟩
            rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq t ts T hpat with ⟨ht, hts⟩
            have hjoin := (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq t (joined ts rs) T hsource).2
            unfold joined at hjoin
            rw [StringRewriteSupport.list_concat_reduce ts rs htsList hrsList] at hjoin
            have hrs := StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq ts rs T htsList hjoin
            have htS := smtx_typeof_of_eo_seq t T hCmd.1 ht
            have htsS := smtx_typeof_of_eo_seq ts T hCmd.2.1 hts
            have hrsS := smtx_typeof_of_eo_seq rs T hCmd.2.2.1 hrs
            exact ⟨fun _ => conclusion_facts M hM t ts rs _ htS htsS hrsS htsList hrsList,
              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                (conclusion_typed t ts rs _ htS htsS hrsS htsList hrsList)⟩
