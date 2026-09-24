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

public import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllSupport

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


private abbrev len (t : Term) := Term.Apply Term.str_len t
private abbrev idx (t pat : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) pat) (Term.Numeral 0)
private abbrev substr (t i n : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_substr t) i) n
private abbrev plus (a b : Term) := Term.Apply (Term.Apply Term.plus a) b
private abbrev eq (a b : Term) := Term.Apply (Term.Apply Term.eq a) b
private abbrev after (t pat : Term) := len pat
private abbrev indexPremise (t pat : Term) := eq (idx t pat) (Term.Numeral 0)
private abbrev positivePremise (pat : Term) := eq (Term.Apply (Term.Apply Term.gt (len pat)) (Term.Numeral 0)) (Term.Boolean true)
private abbrev prePremise (t pat pre : Term) := eq pre (substr t (Term.Numeral 0) (idx t pat))
private abbrev postPremise (t pat post : Term) := eq post (substr t (after t pat) (len t))
private abbrev replace (t pat repl : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) pat) repl
private abbrev nilFor (pre : Term) := __eo_nil Term.str_concat (__eo_typeof pre)
private abbrev rhs (pat repl post : Term) := mkConcat repl (mkConcat (replace post pat repl) (nilFor repl))
private abbrev conclusion (t pat repl post : Term) := eq (replace t pat repl) (rhs pat repl post)

private theorem program_info (t pat repl post P Q S : Term)
    (h : __eo_prog_str_replace_all_find_pre t pat repl post (Proof.pf P) (Proof.pf Q) (Proof.pf S) ≠ Term.Stuck) :
    P = indexPremise t pat ∧ Q = positivePremise pat ∧ S = postPremise t pat post ∧
    __eo_prog_str_replace_all_find_pre t pat repl post (Proof.pf P) (Proof.pf Q) (Proof.pf S) = conclusion t pat repl post := by
  unfold __eo_prog_str_replace_all_find_pre at h
  split at h <;> try contradiction
  next hp hq hs =>
    cases hp
    cases hq
    cases hs
    have hg7 := support_eo_requires_cond_eq_of_non_stuck h
    have hg6 := StrEqReplSupport.eo_and_eq_true_left hg7
    have hg5 := StrEqReplSupport.eo_and_eq_true_left hg6
    have hg4 := StrEqReplSupport.eo_and_eq_true_left hg5
    have hg3 := StrEqReplSupport.eo_and_eq_true_left hg4
    have hg2 := StrEqReplSupport.eo_and_eq_true_left hg3
    have he1 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_left hg2)
    have he2 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg2)
    have he3 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg3)
    have he4 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg4)
    have he5 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg5)
    have he6 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg6)
    have he7 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg7)
    subst_vars
    simp only [__eo_eq, native_teq, __eo_and, native_and, __eo_requires,
      native_ite, SmtEval.native_not] at h
    have h1 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
    have h2 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h1
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp only [__eo_prog_str_replace_all_find_pre, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h1,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h2]
    simp [conclusion, eq, replace, rhs, nilFor, mkConcat]

private theorem concat_type (a b : Term) (T : SmtType)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat a b)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [typeof_str_concat_eq, ha, hb]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem replace_type (t pat repl : Term) (T : SmtType)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hp : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (replace t pat repl)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt pat) (__eo_to_smt repl)) = _
  rw [typeof_str_replace_all_eq, ht, hp, hr]
  simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]

private theorem nil_type (a U : Term) (ha : __eo_typeof a = Term.Apply Term.Seq U)
    (hs : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type U)) :
    __smtx_typeof (__eo_to_smt (nilFor a)) = SmtType.Seq (__eo_to_smt_type U) := by
  have he : nilFor a = __seq_empty (__eo_typeof a) := by rw [nilFor, ha]; rfl
  rw [he]
  exact smt_typeof_seq_empty_typeof a _ hs
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf a _ hs
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt a) _ hs).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt a) _ hs).2)

private theorem conclusion_typed (t pat repl post U : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq (__eo_to_smt_type U))
    (hp : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq (__eo_to_smt_type U))
    (hr : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type U))
    (hpost : __smtx_typeof (__eo_to_smt post) = SmtType.Seq (__eo_to_smt_type U))
    (hreplEO : __eo_typeof repl = Term.Apply Term.Seq U) :
    RuleProofs.eo_has_bool_type (conclusion t pat repl post) := by
  have hl := replace_type t pat repl _ ht hp hr
  have htail := concat_type (replace post pat repl) (nilFor repl) _
    (replace_type post pat repl _ hpost hp hr) (nil_type repl U hreplEO hr)
  have hrhs := concat_type repl (mkConcat (replace post pat repl) (nilFor repl)) _ hr htail
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ (hl.trans hrhs.symm) (by rw [hl]; simp)

private theorem eval_replace (M : SmtModel) (a b c : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_all a b c) =
      __smtx_model_eval_str_replace_all (__smtx_model_eval M a) (__smtx_model_eval M b) (__smtx_model_eval M c) := by
  rw [__smtx_model_eval.eq_def]

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M) (t pat repl post T : Term)
    (hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq (__eo_to_smt_type T))
    (hPatSmtTy : __smtx_typeof (__eo_to_smt pat) = SmtType.Seq (__eo_to_smt_type T))
    (hReplSmtTy : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T))
    (hPostSmtTy : __smtx_typeof (__eo_to_smt post) = SmtType.Seq (__eo_to_smt_type T))
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (indexPremise t pat) true)
    (hPositive : eo_interprets M (positivePremise pat) true)
    (hPrem3 : eo_interprets M (postPremise t pat post) true) :
    eo_interprets M (conclusion t pat repl post) true := by
  have hTEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hPatEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt pat)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPatSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt pat) (by
        unfold term_has_non_none_type
        rw [hPatSmtTy]
        simp)
  have hReplEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hReplSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  have hPostEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt post)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPostSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt post) (by
        unfold term_has_non_none_type
        rw [hPostSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hPatEvalTy with ⟨spat, hPatEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨srepl, hReplEval⟩
  rcases seq_value_canonical hPostEvalTy with ⟨spost, hPostEval⟩
  let idx := native_seq_indexof (native_unpack_seq st)
    (native_unpack_seq spat) 0
  have hIndexZero : idx = 0 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
        (SmtTerm.Numeral 0)) (SmtTerm.Numeral 0)) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_indexof_term_eq, smtx_eval_numeral_term_eq, hTEval, hPatEval] at he
      simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_str_indexof, native_veq] using he
  have hIndexNonneg : 0 ≤ idx := by rw [hIndexZero]; exact Int.le_refl 0
  let unpackValue : SmtValue -> List SmtValue
    | SmtValue.Seq xs => native_unpack_seq xs
    | _ => []
  have hPostExtract : native_unpack_seq spost =
      native_seq_extract (native_unpack_seq st)
        (idx + Int.ofNat (native_unpack_seq spat).length)
        (native_seq_len (native_unpack_seq st)) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem3
    cases hPrem3 with
    | intro_true _ hEval =>
      change __smtx_model_eval M (SmtTerm.eq (__eo_to_smt post)
        (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.str_len (__eo_to_smt pat))
          (SmtTerm.str_len (__eo_to_smt t)))) = SmtValue.Boolean true at hEval
      simp only [smtx_eval_eq_term_eq, hPostEval, StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
        smtx_eval_str_len_term_eq, hTEval, hPatEval] at hEval
      have hBoolEq : decide (SmtValue.Seq spost = SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value st)
            (native_seq_extract (native_unpack_seq st)
              (idx + Int.ofNat (native_unpack_seq spat).length)
              (native_seq_len (native_unpack_seq st))))) = true := by
        simpa [hIndexZero, __smtx_model_eval_eq, __smtx_model_eval_str_substr,
          __smtx_model_eval_str_len, native_veq, native_seq_len] using hEval
      have hUnpack := congrArg unpackValue (of_decide_eq_true hBoolEq)
      simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hBounds : Int.toNat idx + (native_unpack_seq spat).length ≤
      (native_unpack_seq st).length :=
    StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
      (native_unpack_seq st) (native_unpack_seq spat) hIndexNonneg
  have hIdxCast : (Int.toNat idx : Int) = idx :=
    Int.toNat_of_nonneg hIndexNonneg
  have hIdxLe : Int.toNat idx ≤ (native_unpack_seq st).length := by omega
  have hAfterNonneg :
      0 ≤ idx + Int.ofNat (native_unpack_seq spat).length :=
    Int.add_nonneg hIndexNonneg (Int.natCast_nonneg _)
  have hAfterLe : idx + Int.ofNat (native_unpack_seq spat).length ≤
      native_seq_len (native_unpack_seq st) := by
    rw [← hIdxCast]
    simpa [native_seq_len] using Int.ofNat_le.mpr hBounds
  have hToNatAfter :
      Int.toNat (idx + Int.ofNat (native_unpack_seq spat).length) =
        Int.toNat idx + (native_unpack_seq spat).length := by
    simpa using
      (Int.toNat_add hIndexNonneg
        (Int.natCast_nonneg (native_unpack_seq spat).length))
  have hPostList : native_unpack_seq spost =
      (native_unpack_seq st).drop
        (Int.toNat idx + (native_unpack_seq spat).length) := by
    rw [hPostExtract,
      native_seq_extract_len_tail_of_bounds _ _ hAfterNonneg hAfterLe,
      hToNatAfter]
  have hNonempty : native_unpack_seq spat ≠ [] := by
    have hPos : (0 : Int) < (native_unpack_seq spat).length := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPositive
      cases hPositive with
      | intro_true _ he =>
        change __smtx_model_eval M (SmtTerm.eq (SmtTerm.gt (SmtTerm.str_len (__eo_to_smt pat))
          (SmtTerm.Numeral 0)) (SmtTerm.Boolean true)) = SmtValue.Boolean true at he
        simp only [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq, smtx_eval_str_len_term_eq,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq, hPatEval] at he
        simpa [__smtx_model_eval_eq, __smtx_model_eval_gt, __smtx_model_eval_lt,
          __smtx_model_eval_str_len, native_seq_len, native_veq, native_zlt] using he
    intro hn
    rw [hn] at hPos
    simp at hPos
  have hNativeReplace :
      native_seq_replace_all (native_unpack_seq st) (native_unpack_seq spat) (native_unpack_seq srepl) =
        native_unpack_seq srepl ++
          native_seq_replace_all (native_unpack_seq spost) (native_unpack_seq spat) (native_unpack_seq srepl) := by
    rw [StrReplaceAllSupport.replace_all_step _ _ _ hNonempty hIndexNonneg, ← hPostList]
    change (native_unpack_seq st).take (Int.toNat idx) ++ _ ++ _ = _
    simp [hIndexZero]
  have hTSeqTy : __smtx_typeof_seq_value st =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hTEvalTy
    try simp [hTEval] at hsimpa ⊢
    exact hsimpa
  have hPatSeqTy : __smtx_typeof_seq_value spat =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPatEvalTy
    try simp [hPatEval] at hsimpa ⊢
    exact hsimpa
  have hReplSeqTy : __smtx_typeof_seq_value srepl =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hReplEvalTy
    try simp [hReplEval] at hsimpa ⊢
    exact hsimpa
  have hPostSeqTy : __smtx_typeof_seq_value spost =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPostEvalTy
    try simp [hPostEval] at hsimpa ⊢
    exact hsimpa
  have hTElem := elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hPatElem := elem_typeof_seq_value_of_typeof_seq_value hPatSeqTy
  have hReplElem := elem_typeof_seq_value_of_typeof_seq_value hReplSeqTy
  have hPostElem := elem_typeof_seq_value_of_typeof_seq_value hPostSeqTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof repl))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) :=
    eval_seq_empty_typeof M repl (__eo_to_smt_type T) hReplSmtTy
  have hNil : nilFor repl = __seq_empty (__eo_typeof repl) := by rw [nilFor, hReplTy]; rfl
  have hEvalEq : __smtx_model_eval M (__eo_to_smt (replace t pat repl)) =
      __smtx_model_eval M (__eo_to_smt (rhs pat repl post)) := by
    unfold rhs
    rw [hNil]
    change __smtx_model_eval M (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt pat) (__eo_to_smt repl)) =
      __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt repl)
        (SmtTerm.str_concat (SmtTerm.str_replace_all (__eo_to_smt post) (__eo_to_smt pat) (__eo_to_smt repl))
          (__eo_to_smt (__seq_empty (__eo_typeof repl)))))
    simp only [eval_replace, eval_concat, hTEval, hPatEval, hReplEval, hPostEval, hEmptyEval]
    simp [__smtx_model_eval_str_replace_all, __smtx_model_eval_str_concat,
      native_seq_concat, native_unpack_seq, Smtm.native_unpack_pack_seq,
      hTElem, hPatElem, hReplElem, hPostElem, elem_typeof_pack_seq, hNativeReplace, List.append_assoc]
  exact RuleProofs.eo_interprets_eq_of_rel M _ _
    (conclusion_typed t pat repl post T hTSmtTy hPatSmtTy hReplSmtTy hPostSmtTy hReplTy)
    (by rw [hEvalEq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_str_replace_all_find_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_find_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_all_find_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_find_pre args premises) := by
  intro hCmd hPremTy hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons t args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons pat args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons repl args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons post args =>
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
                | nil => exact False.elim (hProg rfl)
                | cons k premises =>
                  cases premises with
                  | cons _ _ => exact False.elim (hProg rfl)
                  | nil =>
                    let P := __eo_state_proven_nth s i
                    let Q := __eo_state_proven_nth s j
                    let S := __eo_state_proven_nth s k
                    change __eo_typeof (__eo_prog_str_replace_all_find_pre t pat repl post (Proof.pf P) (Proof.pf Q) (Proof.pf S)) = Term.Bool at hTy
                    rcases program_info t pat repl post P Q S (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, hQ, hS, he⟩
                    change StepRuleProperties M _ (__eo_prog_str_replace_all_find_pre t pat repl post (Proof.pf P) (Proof.pf Q) (Proof.pf S))
                    rw [he] at hTy ⊢
                    have hl : __eo_typeof (replace t pat repl) ≠ Term.Stuck :=
                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                    rcases eo_typeof_str_replace_args_of_ne_stuck _ _ _ hl with ⟨T, ht, hpat, hrepl⟩
                    have hSBool : RuleProofs.eo_has_bool_type (postPremise t pat post) := by
                      have h := hPremTy S (by simp [S, premiseTermList]); simpa [hS] using h
                    have hpost : __eo_typeof post = Term.Apply Term.Seq T := by
                      have h := StrReplaceFindSupport.eo_typeof_eq_operands_of_has_bool_type _ _ hSBool
                      rw [h]
                      change __eo_typeof_str_substr (__eo_typeof t) (__eo_typeof_str_len (__eo_typeof pat)) (__eo_typeof_str_len (__eo_typeof t)) = _
                      simp [ht, hpat, __eo_typeof_str_substr, __eo_typeof_str_len]
                    have htS := smtx_typeof_of_eo_seq t T hCmd.1 ht
                    have hpS := smtx_typeof_of_eo_seq pat T hCmd.2.1 hpat
                    have hrS := smtx_typeof_of_eo_seq repl T hCmd.2.2.1 hrepl
                    have hpostS := smtx_typeof_of_eo_seq post T hCmd.2.2.2.1 hpost
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ (conclusion_typed t pat repl post T htS hpS hrS hpostS hrepl)⟩
                    intro hTrue
                    apply conclusion_facts M hM t pat repl post T htS hpS hrS hpostS hrepl
                    · have h := hTrue P (by simp [P, premiseTermList]); simpa [hP] using h
                    · have h := hTrue Q (by simp [Q, premiseTermList]); simpa [hQ] using h
                    · have h := hTrue S (by simp [S, premiseTermList]); simpa [hS] using h
