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

private theorem eo_typeof_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case Apply g y =>
          cases g <;> simp at h ⊢
          case UOp opg =>
            cases opg <;> simp at h ⊢
            case Seq =>
              cases C <;> simp at h ⊢
              case Apply k z =>
                cases k <;> simp at h ⊢
                case UOp opk =>
                  cases opk <;> simp at h ⊢
                  case Seq =>
                    have hEq := RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                      x x y z (Term.Apply Term.Seq x) h
                    exact hEq

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
private abbrev lhs (t ts rs r : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_replace (source t ts rs)) (pattern t ts)) r
private abbrev rhs (rs r : Term) := __eo_list_singleton_elim Term.str_concat (mkConcat r rs)
private abbrev conclusion (t ts rs r : Term) := Term.Apply (Term.Apply Term.eq (lhs t ts rs r)) (rhs rs r)

private theorem program_info (t ts rs r : Term)
    (ht : t ≠ Term.Stuck) (hts : ts ≠ Term.Stuck) (hrs : rs ≠ Term.Stuck) (hr : r ≠ Term.Stuck)
    (h : __eo_prog_str_replace_prefix_concat t ts rs r ≠ Term.Stuck) :
    __eo_is_list Term.str_concat ts = Term.Boolean true ∧
    __eo_is_list Term.str_concat rs = Term.Boolean true ∧
    __eo_is_list Term.str_concat (mkConcat r rs) = Term.Boolean true ∧
    __eo_prog_str_replace_prefix_concat t ts rs r = conclusion t ts rs r := by
  rw [__eo_prog_str_replace_prefix_concat.eq_5 t ts rs r ht hts hrs hr] at h ⊢
  have h1 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have h2 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h1
  have h3 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h2
  have h4 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h3
  have h5 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h4
  have h6 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h5
  have htsList := support_eo_requires_cond_eq_of_non_stuck h6
  have hinner := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h6
  have hrsList := support_eo_requires_cond_eq_of_non_stuck hinner
  have hright := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  have hrList := support_eo_requires_cond_eq_of_non_stuck hright
  refine ⟨htsList, hrsList, hrList, ?_⟩
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

private theorem conclusion_typed (t ts rs r : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hts : __smtx_typeof (__eo_to_smt ts) = SmtType.Seq T)
    (hrs : __smtx_typeof (__eo_to_smt rs) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hrList : __eo_is_list Term.str_concat (mkConcat r rs) = Term.Boolean true)
    (htsList : __eo_is_list Term.str_concat ts = Term.Boolean true)
    (hrsList : __eo_is_list Term.str_concat rs = Term.Boolean true) :
    RuleProofs.eo_has_bool_type (conclusion t ts rs r) := by
  have hjoin := StringRewriteSupport.list_concat_has_seq_type ts rs T htsList hrsList hts hrs
  have hsource := concat_type t (joined ts rs) T ht hjoin
  have hpat := concat_type t ts T ht hts
  have hl : __smtx_typeof (__eo_to_smt (lhs t ts rs r)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_replace (__eo_to_smt (source t ts rs))
      (__eo_to_smt (pattern t ts)) (__eo_to_smt r)) = _
    rw [typeof_str_replace_eq, hsource, hpat, hr]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hright := StringRewriteSupport.singleton_elim_has_seq_type (mkConcat r rs) T hrList
    (concat_type r rs T hr hrs)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ (hl.trans hright.symm) (by rw [hl]; simp)

private theorem prefix_index (pat rest : List SmtValue) :
    native_seq_indexof (pat ++ rest) pat 0 = 0 := by
  rw [native_seq_indexof_eq_rec]
  have hb : pat.length ≤ (pat ++ rest).length := by simp
  simp only [List.length_append] at hb
  simp [hb]
  rw [native_seq_indexof_rec.eq_def]
  simp [StringRewriteSupport.native_seq_prefix_eq_append_self]

private theorem prefix_replace (pre rest repl : List SmtValue) :
    native_seq_replace (pre ++ rest) pre repl = repl ++ rest := by
  rw [StrEqReplSupport.native_seq_replace_eq_indexof, prefix_index]
  simp

private theorem eval_replace (M : SmtModel) (a b c : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace a b c) =
      __smtx_model_eval_str_replace (__smtx_model_eval M a) (__smtx_model_eval M b) (__smtx_model_eval M c) := by
  rw [__smtx_model_eval.eq_def]

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M)
    (t ts rs r : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hts : __smtx_typeof (__eo_to_smt ts) = SmtType.Seq T)
    (hrs : __smtx_typeof (__eo_to_smt rs) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hrList : __eo_is_list Term.str_concat (mkConcat r rs) = Term.Boolean true)
    (htsList : __eo_is_list Term.str_concat ts = Term.Boolean true)
    (hrsList : __eo_is_list Term.str_concat rs = Term.Boolean true) :
    eo_interprets M (conclusion t ts rs r) true := by
  rcases eval_seq M hM t T ht with ⟨tv, hte⟩
  rcases eval_seq M hM ts T hts with ⟨tsv, htse⟩
  rcases eval_seq M hM rs T hrs with ⟨rsv, hrse⟩
  rcases eval_seq M hM r T hr with ⟨rv, hre⟩
  have hjoin := StringRewriteSupport.list_concat_eval M hM ts rs T tsv rsv
    htsList hrsList hts hrs htse hrse
  have helem : __smtx_elem_typeof_seq_value tv = __smtx_elem_typeof_seq_value rv := by
    have he (a : Term) (sa : SmtSeq) (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
        (hae : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa) :
        __smtx_elem_typeof_seq_value sa = T := by
      have hv := smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
        (term_has_non_none_of_type_eq ha (by simp))
      rw [hae, ha] at hv
      exact elem_typeof_seq_value_of_typeof_seq_value hv
    exact (he t tv ht hte).trans (he r rv hr hre).symm
  have hraw : __smtx_model_eval M (__eo_to_smt (mkConcat r rs)) =
      SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value rv)
        (native_unpack_seq rv ++ native_unpack_seq rsv)) := by
    change __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt r) (__eo_to_smt rs)) = _
    rw [eval_concat, hre, hrse]; rfl
  have hright := StringRewriteSupport.singleton_elim_eval M hM (mkConcat r rs) T _ hrList
    (concat_type r rs T hr hrs) hraw
  have heq : __smtx_model_eval M (__eo_to_smt (lhs t ts rs r)) =
      __smtx_model_eval M (__eo_to_smt (rhs rs r)) := by
    rw [hright]
    change __smtx_model_eval M (SmtTerm.str_replace
      (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt (joined ts rs)))
      (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt ts)) (__eo_to_smt r)) = _
    simp only [eval_replace, eval_concat, hte, htse, hjoin, hre]
    simp [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq,
      __smtx_model_eval_str_replace, elem_typeof_pack_seq, helem, ← List.append_assoc, prefix_replace]
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ (conclusion_typed t ts rs r T ht hts hrs hr hrList htsList hrsList)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

private theorem translated_ne (a : Term) (h : RuleProofs.eo_has_smt_translation a) : a ≠ Term.Stuck := by
  intro ha
  subst a
  exact h rfl

public theorem cmd_step_str_replace_prefix_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (state : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_prefix_concat args premises) ->
  AllHaveBoolType (premiseTermList state premises) ->
  __eo_typeof (__eo_cmd_step_proven state CRule.str_replace_prefix_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList state premises)
    (__eo_cmd_step_proven state CRule.str_replace_prefix_concat args premises) := by
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
        | nil => exact False.elim (hProg rfl)
        | cons r args =>
          cases args with
          | cons _ _ => exact False.elim (hProg rfl)
          | nil =>
            cases premises with
            | cons _ _ => exact False.elim (hProg rfl)
            | nil =>
              change __eo_typeof (__eo_prog_str_replace_prefix_concat t ts rs r) = Term.Bool at hTy
              rcases program_info t ts rs r (translated_ne t hCmd.1) (translated_ne ts hCmd.2.1)
                (translated_ne rs hCmd.2.2.1) (translated_ne r hCmd.2.2.2.1) (term_ne_stuck_of_typeof_bool hTy) with ⟨htsList, hrsList, hrList, he⟩
              change StepRuleProperties M _ (__eo_prog_str_replace_prefix_concat t ts rs r)
              rw [he] at hTy ⊢
              have hl : __eo_typeof (lhs t ts rs r) ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
              rcases eo_typeof_str_replace_args_of_ne_stuck _ _ _ hl with ⟨T, hsource, hpat, hr⟩
              rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq t ts T hpat with ⟨ht, hts⟩
              have hjoin := (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq t (joined ts rs) T hsource).2
              unfold joined at hjoin
              rw [StringRewriteSupport.list_concat_reduce ts rs htsList hrsList] at hjoin
              have hrs := StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq ts rs T htsList hjoin
              have htS := smtx_typeof_of_eo_seq t T hCmd.1 ht
              have htsS := smtx_typeof_of_eo_seq ts T hCmd.2.1 hts
              have hrsS := smtx_typeof_of_eo_seq rs T hCmd.2.2.1 hrs
              have hrS := smtx_typeof_of_eo_seq r T hCmd.2.2.2.1 hr
              exact ⟨fun _ => conclusion_facts M hM t ts rs r _ htS htsS hrsS hrS hrList htsList hrsList,
                RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (conclusion_typed t ts rs r _ htS htsS hrsS hrS hrList htsList hrsList)⟩
