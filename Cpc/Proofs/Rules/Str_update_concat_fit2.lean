module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport
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


private abbrev tail (r qs : Term) := mkConcat r qs
private abbrev joined (ps r qs : Term) := __eo_list_concat Term.str_concat ps (tail r qs)
private abbrev pre (p u ps : Term) := mkConcat p (mkConcat u ps)
private abbrev source (p u ps r qs : Term) := pre p u (joined ps r qs)
private abbrev lhs (p u ps r qs n x : Term) := Term.Apply (Term.Apply (Term.Apply Term.str_update (source p u ps r qs)) n) x
private abbrev conclusion (p u ps r qs n x : Term) := Term.Apply (Term.Apply Term.eq (lhs p u ps r qs n x)) (source p u ps x qs)
private abbrev indexPremise (p u ps n : Term) := Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (pre p u ps))) n
private abbrev lengthPremise (r x : Term) := Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len r)) (Term.Apply Term.str_len x)

private theorem program_info (p u ps r qs n x P Q : Term)
    (h : __eo_prog_str_update_concat_fit2 p u ps r qs n x (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck) :
    P = indexPremise p u ps n ∧ Q = lengthPremise r x ∧
    __eo_is_list Term.str_concat ps = Term.Boolean true ∧
    __eo_is_list Term.str_concat (tail r qs) = Term.Boolean true ∧
    __eo_is_list Term.str_concat (tail x qs) = Term.Boolean true ∧
    __eo_prog_str_update_concat_fit2 p u ps r qs n x (Proof.pf P) (Proof.pf Q) = conclusion p u ps r qs n x := by
  unfold __eo_prog_str_update_concat_fit2 at h
  split at h <;> try contradiction
  next hp hq =>
    cases hp
    cases hq
    have hg6 := support_eo_requires_cond_eq_of_non_stuck h
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
    subst_vars
    simp only [__eo_eq, native_teq, __eo_and, native_and, __eo_requires,
      native_ite, SmtEval.native_not] at h
    have h1 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
    have hl := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h1
    have hl1 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hl
    have hl2 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hl1
    have hl3 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hl2
    have hl4 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hl3
    have hl5 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hl4
    have hr := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
    have hr1 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hr
    have hr2 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hr1
    have haList := support_eo_requires_cond_eq_of_non_stuck hl5
    have hbList := support_eo_requires_cond_eq_of_non_stuck (eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hl5)
    have hcList := support_eo_requires_cond_eq_of_non_stuck (eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hr2)
    refine ⟨rfl, rfl, haList, hbList, hcList, ?_⟩
    simp only [__eo_prog_str_update_concat_fit2, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h, eo_mk_apply_eq_apply_of_ne_stuck _ _ h1,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hl, eo_mk_apply_eq_apply_of_ne_stuck _ _ hl1,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hl2, eo_mk_apply_eq_apply_of_ne_stuck _ _ hl3,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hl4,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hr, eo_mk_apply_eq_apply_of_ne_stuck _ _ hr1]
    simp [conclusion, lhs, source, pre, joined, tail, mkConcat]

private theorem concat_type (a b : Term) (T : SmtType)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat a b)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [typeof_str_concat_eq, ha, hb]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem source_type (p u ps r qs : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hu : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (haList : __eo_is_list Term.str_concat ps = Term.Boolean true)
    (hbList : __eo_is_list Term.str_concat (tail r qs) = Term.Boolean true) :
    __smtx_typeof (__eo_to_smt (source p u ps r qs)) = SmtType.Seq T := by
  have hj := StringRewriteSupport.list_concat_has_seq_type ps (tail r qs) T haList hbList hps
    (concat_type r qs T hr hqs)
  exact concat_type p (mkConcat u (joined ps r qs)) T hp (concat_type u (joined ps r qs) T hu hj)

private theorem conclusion_typed (p u ps r qs n x : Term) (T : SmtType)
    (hl : __smtx_typeof (__eo_to_smt (source p u ps r qs)) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt (source p u ps x qs)) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (conclusion p u ps r qs n x) := by
  have ht : __smtx_typeof (__eo_to_smt (lhs p u ps r qs n x)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_update (__eo_to_smt (source p u ps r qs)) (__eo_to_smt n) (__eo_to_smt x)) = _
    rw [typeof_str_update_eq, hl, hn, hx]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ (ht.trans hr.symm) (by rw [ht]; simp)

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M)
    (p u ps r qs n x : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hu : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (haList : __eo_is_list Term.str_concat ps = Term.Boolean true)
    (hbList : __eo_is_list Term.str_concat (tail r qs) = Term.Boolean true)
    (hcList : __eo_is_list Term.str_concat (tail x qs) = Term.Boolean true)
    (hIndex : eo_interprets M (indexPremise p u ps n) true)
    (hLength : eo_interprets M (lengthPremise r x) true) :
    eo_interprets M (conclusion p u ps r qs n x) true := by
  rcases eval_seq M hM p T hp with ⟨pv, hpe⟩
  rcases eval_seq M hM u T hu with ⟨uv, hue⟩
  rcases eval_seq M hM ps T hps with ⟨psv, hpse⟩
  rcases eval_seq M hM r T hr with ⟨rs, hre⟩
  rcases eval_seq M hM qs T hqs with ⟨qss, hqse⟩
  rcases eval_seq M hM x T hx with ⟨xs, hxe⟩
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases int_value_canonical hnVal with ⟨ni, hne⟩
  have htEval (a : Term) (av : SmtSeq) (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq av) :
      __smtx_model_eval M (__eo_to_smt (tail a qs)) =
        SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value av) (native_unpack_seq av ++ native_unpack_seq qss)) := by
    change __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt qs)) = _
    rw [eval_concat, ha, hqse]; rfl
  have hjr := StringRewriteSupport.list_concat_eval M hM ps (tail r qs) T psv _
    haList hbList hps (concat_type r qs T hr hqs) hpse (htEval r rs hre)
  have hjx := StringRewriteSupport.list_concat_eval M hM ps (tail x qs) T psv _
    haList hcList hps (concat_type x qs T hx hqs) hpse (htEval x xs hxe)
  have hi : ni = ((native_unpack_seq pv ++ native_unpack_seq uv ++ native_unpack_seq psv).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hIndex
    cases hIndex with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (SmtTerm.str_concat (__eo_to_smt p)
        (SmtTerm.str_concat (__eo_to_smt u) (__eo_to_smt ps)))) (__eo_to_smt n)) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, eval_concat, hpe, hue, hpse, hne] at he
      symm
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq,
        __smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq, List.append_assoc] using he
  have hLen : (native_unpack_seq rs).length = (native_unpack_seq xs).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLength
    cases hLength with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt r))
        (SmtTerm.str_len (__eo_to_smt x))) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hre, hxe] at he
      apply Int.ofNat.inj
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq] using he
  have hupdate := native_seq_update_replace_middle
    (native_unpack_seq pv ++ native_unpack_seq uv ++ native_unpack_seq psv)
    (native_unpack_seq rs) (native_unpack_seq qss) (native_unpack_seq xs) hLen
  have heq : __smtx_model_eval M (__eo_to_smt (lhs p u ps r qs n x)) =
      __smtx_model_eval M (__eo_to_smt (source p u ps x qs)) := by
    change __smtx_model_eval M (SmtTerm.str_update
      (SmtTerm.str_concat (__eo_to_smt p) (SmtTerm.str_concat (__eo_to_smt u) (__eo_to_smt (joined ps r qs))))
      (__eo_to_smt n) (__eo_to_smt x)) =
      __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt p) (SmtTerm.str_concat (__eo_to_smt u) (__eo_to_smt (joined ps x qs))))
    simp only [smtx_eval_str_update_term_eq, eval_concat, hpe, hue, hjr, hjx, hxe, hne, hi]
    simp only [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq,
      __smtx_model_eval_str_update, elem_typeof_pack_seq, ← List.append_assoc]
    exact congrArg SmtValue.Seq (congrArg (native_pack_seq (__smtx_elem_typeof_seq_value pv)) hupdate)
  exact RuleProofs.eo_interprets_eq_of_rel M _ _
    (conclusion_typed p u ps r qs n x T
      (source_type p u ps r qs T hp hu hps hr hqs haList hbList)
      (source_type p u ps x qs T hp hu hps hx hqs haList hcList) hn hx)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

private theorem len_smt_arg (A : SmtType) (h : __smtx_typeof_seq_op_1_ret A SmtType.Int = SmtType.Int) :
    ∃ T, A = SmtType.Seq T := by
  cases A <;> simp_all [__smtx_typeof_seq_op_1_ret]

public theorem cmd_step_str_update_concat_fit2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_concat_fit2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_update_concat_fit2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_update_concat_fit2 args premises) := by
  intro hCmd hPremTy hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons p args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons u args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons ps args =>
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
                        let P := __eo_state_proven_nth s i
                        let Q := __eo_state_proven_nth s j
                        change __eo_typeof (__eo_prog_str_update_concat_fit2 p u ps r qs n x (Proof.pf P) (Proof.pf Q)) = Term.Bool at hTy
                        rcases program_info p u ps r qs n x P Q (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, hQ, haList, hbList, hcList, he⟩
                        change StepRuleProperties M _ (__eo_prog_str_update_concat_fit2 p u ps r qs n x (Proof.pf P) (Proof.pf Q))
                        rw [he] at hTy ⊢
                        have hl : __eo_typeof (lhs p u ps r qs n x) ≠ Term.Stuck :=
                          (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                        rcases eo_typeof_str_update_args_of_ne_stuck _ _ _ hl with ⟨T, hsource, hn, hx⟩
                        rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq p (mkConcat u (joined ps r qs)) T hsource with ⟨hp, hinner⟩
                        rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq u (joined ps r qs) T hinner with ⟨hu, hjoin⟩
                        unfold joined at hjoin
                        rw [StringRewriteSupport.list_concat_reduce ps (tail r qs) haList hbList] at hjoin
                        have htail := StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq ps (tail r qs) T haList hjoin
                        rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq r qs T htail with ⟨hr, hqs⟩
                        have hpS := smtx_typeof_of_eo_seq p T hCmd.1 hp
                        have huS := smtx_typeof_of_eo_seq u T hCmd.2.1 hu
                        have hrS := smtx_typeof_of_eo_seq r T hCmd.2.2.2.1 hr
                        have hqsS := smtx_typeof_of_eo_seq qs T hCmd.2.2.2.2.1 hqs
                        have hnS := smtx_typeof_of_eo_int n hCmd.2.2.2.2.2.1 hn
                        have hxS := smtx_typeof_of_eo_seq x T hCmd.2.2.2.2.2.2.1 hx
                        have hpTy : RuleProofs.eo_has_bool_type (indexPremise p u ps n) := by
                          have hp := hPremTy P (by simp [P, premiseTermList])
                          simpa [hP] using hp
                        have hlen := (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hpTy).1
                        rw [hnS] at hlen
                        change __smtx_typeof (SmtTerm.str_len (__eo_to_smt (pre p u ps))) = SmtType.Int at hlen
                        rw [typeof_str_len_eq] at hlen
                        rcases len_smt_arg _ hlen with ⟨U, hpre⟩
                        rcases strConcat_args_of_seq_type p (mkConcat u ps) U hpre with ⟨hpU, hrest⟩
                        have hUT : U = __eo_to_smt_type T := by rw [hpS] at hpU; exact (SmtType.Seq.inj hpU).symm
                        rw [hUT] at hrest
                        have hpsS := (strConcat_args_of_seq_type u ps _ hrest).2
                        refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (conclusion_typed p u ps r qs n x _
                            (source_type p u ps r qs _ hpS huS hpsS hrS hqsS haList hbList)
                            (source_type p u ps x qs _ hpS huS hpsS hxS hqsS haList hcList) hnS hxS)⟩
                        intro hTrue
                        apply conclusion_facts M hM p u ps r qs n x _ hpS huS hpsS hrS hqsS hnS hxS haList hbList hcList
                        · have hp := hTrue P (by simp [P, premiseTermList])
                          simpa [hP] using hp
                        · have hq := hTrue Q (by simp [Q, premiseTermList])
                          simpa [hQ] using hq
