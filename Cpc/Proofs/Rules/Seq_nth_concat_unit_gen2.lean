module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport

open Eo Smtm SmtEval
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem nth_arg_types (A B : Term)
    (h : __eo_typeof_seq_nth A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Int := by
  cases A <;> simp [__eo_typeof_seq_nth] at h ⊢
  case Apply f t =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case UOp op => cases op <;> simp at h ⊢

private theorem unit_arg_type (A T : Term)
    (h : __eo_typeof_seq_unit A = Term.Apply Term.Seq T) : A = T := by
  cases A <;> simp_all [__eo_typeof_seq_unit]

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


private abbrev tail (x ys : Term) := mkConcat (Term.Apply Term.seq_unit x) ys
private abbrev joined (ts x ys : Term) := __eo_list_concat Term.str_concat ts (tail x ys)
private abbrev pre (t u ts : Term) := mkConcat t (mkConcat u ts)
private abbrev source (t u ts x ys : Term) := pre t u (joined ts x ys)
private abbrev lhs (t u ts x ys n : Term) := Term.Apply (Term.Apply Term.seq_nth (source t u ts x ys)) n
private abbrev conclusion (t u ts x ys n : Term) := Term.Apply (Term.Apply Term.eq (lhs t u ts x ys n)) x
private abbrev premise (t u ts n : Term) := Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (pre t u ts))) n

private theorem program_info (t u ts x ys n P : Term)
    (h : __eo_prog_seq_nth_concat_unit_gen2 t u ts x ys n (Proof.pf P) ≠ Term.Stuck) :
    P = premise t u ts n ∧
    __eo_is_list Term.str_concat ts = Term.Boolean true ∧
    __eo_is_list Term.str_concat (tail x ys) = Term.Boolean true ∧
    __eo_prog_seq_nth_concat_unit_gen2 t u ts x ys n (Proof.pf P) = conclusion t u ts x ys n := by
  unfold __eo_prog_seq_nth_concat_unit_gen2 at h
  split at h <;> try contradiction
  next hp =>
    cases hp
    have hg := support_eo_requires_cond_eq_of_non_stuck h
    have hg3 := StrEqReplSupport.eo_and_eq_true_left hg
    have hg2 := StrEqReplSupport.eo_and_eq_true_left hg3
    have h1 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_left hg2)
    have h2 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg2)
    have h3 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg3)
    have h4 := support_eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    subst_vars
    simp only [__eo_eq, native_teq, __eo_and, native_and, __eo_requires,
      native_ite, SmtEval.native_not] at h
    have h1 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
    have h2 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h1
    have h3 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h2
    have h4 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h3
    have h5 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h4
    have h6 := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h5
    have haList := support_eo_requires_cond_eq_of_non_stuck h6
    have hbList := support_eo_requires_cond_eq_of_non_stuck (eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h6)
    refine ⟨rfl, haList, hbList, ?_⟩
    simp only [__eo_prog_seq_nth_concat_unit_gen2, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h1,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h2,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h3,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h4,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ h5]
    simp [conclusion, lhs, source, pre, joined, tail, mkConcat]

private theorem concat_type (a b : Term) (T : SmtType)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat a b)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [typeof_str_concat_eq, ha, hb]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem tail_type (x ys : Term)
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x))) :
    __smtx_typeof (__eo_to_smt (tail x ys)) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)) := by
  have hGood := smt_term_result_seq_components_wf_of_non_none (__eo_to_smt ys)
    (term_has_non_none_of_type_eq hy (by simp))
  rw [hy] at hGood
  apply concat_type _ _ _ _ hy
  change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt x)) = _
  rw [smtx_typeof_seq_unit_term_eq]
  change __smtx_type_wf (SmtType.Seq (__smtx_typeof (__eo_to_smt x))) = true at hGood
  simp [__smtx_typeof_guard_wf, hGood, native_ite]

private theorem conclusion_typed (t u ts x ys n : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hsource : __smtx_typeof (__eo_to_smt (source t u ts x ys)) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (conclusion t u ts x ys n) := by
  have hw := smt_term_result_seq_components_wf_of_non_none (__eo_to_smt (source t u ts x ys))
    (term_has_non_none_of_type_eq hsource (by simp))
  rw [hsource] at hw
  have helem := seq_type_wf_component_of_wf hw
  have hl : __smtx_typeof (__eo_to_smt (lhs t u ts x ys n)) = __smtx_typeof (__eo_to_smt x) := by
    change __smtx_typeof (SmtTerm.seq_nth (__eo_to_smt (source t u ts x ys)) (__eo_to_smt n)) = _
    rw [typeof_seq_nth_eq, hsource, hn]
    simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, helem, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ hl (by rw [hl]; exact hx)

private theorem nthConcatEvalNth (M : SmtModel) (x i : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_nth x i) =
      __smtx_seq_nth M (__smtx_model_eval M x) (__smtx_model_eval M i) := by
  rw [__smtx_model_eval.eq_def]

private theorem nthConcatEvalConcat (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def]

private theorem nthConcatEvalUnit (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_unit x) =
      SmtValue.Seq (SmtSeq.cons (__smtx_model_eval M x)
        (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M x)))) := by
  rw [__smtx_model_eval.eq_def]

private theorem seq_value_nth_pack_append_cons (T : SmtType) (pre : List SmtValue)
    (x : SmtValue) (ys : List SmtValue) (d : SmtValue) :
    __smtx_seq_value_nth (native_pack_seq T (pre ++ x :: ys)) (pre.length : Int) d = x := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    simp only [List.cons_append, native_pack_seq, List.length_cons]
    rw [__smtx_seq_value_nth.eq_3 _ _ _ _ (by exact Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero _))]
    simpa [native_zplus, native_zneg, Int.add_assoc] using ih

private theorem eval_seq (M : SmtModel) (hM : model_wf M) (a : Term) (T : SmtType)
    (h : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) :
    ∃ xs, __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq xs := by
  apply seq_value_canonical
  simpa [h] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
    (term_has_non_none_of_type_eq h (by simp))

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M) (t u ts x ys n : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hu : __smtx_typeof (__eo_to_smt u) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hts : __smtx_typeof (__eo_to_smt ts) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (haList : __eo_is_list Term.str_concat ts = Term.Boolean true)
    (hbList : __eo_is_list Term.str_concat (tail x ys) = Term.Boolean true)
    (hsource : __smtx_typeof (__eo_to_smt (source t u ts x ys)) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hPrem : eo_interprets M (premise t u ts n) true) :
    eo_interprets M (conclusion t u ts x ys n) true := by
  rcases eval_seq M hM t _ ht with ⟨tv, hte⟩
  rcases eval_seq M hM u _ hu with ⟨uv, hue⟩
  rcases eval_seq M hM ts _ hts with ⟨tsv, htse⟩
  rcases eval_seq M hM ys _ hy with ⟨yv, hye⟩
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases int_value_canonical hnVal with ⟨ni, hne⟩
  have htail : __smtx_model_eval M (__eo_to_smt (tail x ys)) =
      SmtValue.Seq (native_pack_seq (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)))
        (__smtx_model_eval M (__eo_to_smt x) :: native_unpack_seq yv)) := by
    change __smtx_model_eval M (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys)) = _
    simp [nthConcatEvalConcat, nthConcatEvalUnit, hye, __smtx_model_eval_str_concat,
      native_seq_concat, native_unpack_seq, __smtx_elem_typeof_seq_value]
  have hjoin := StringRewriteSupport.list_concat_eval M hM ts (tail x ys) _ tsv _
    haList hbList hts (tail_type x ys hy) htse htail
  have hi : ni = ((native_unpack_seq tv ++ native_unpack_seq uv ++ native_unpack_seq tsv).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (SmtTerm.str_concat (__eo_to_smt t)
        (SmtTerm.str_concat (__eo_to_smt u) (__eo_to_smt ts)))) (__eo_to_smt n)) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, nthConcatEvalConcat, hte, hue, htse, hne] at he
      symm
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq,
        __smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq, List.append_assoc] using he
  have heq : __smtx_model_eval M (__eo_to_smt (lhs t u ts x ys n)) = __smtx_model_eval M (__eo_to_smt x) := by
    change __smtx_model_eval M (SmtTerm.seq_nth (SmtTerm.str_concat (__eo_to_smt t)
      (SmtTerm.str_concat (__eo_to_smt u) (__eo_to_smt (joined ts x ys)))) (__eo_to_smt n)) = _
    simp only [nthConcatEvalNth, nthConcatEvalConcat, hte, hue, hjoin, hne, hi]
    simp only [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq,
      __smtx_seq_nth]
    simp only [← List.append_assoc]
    exact seq_value_nth_pack_append_cons _ _ _ _ _
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ (conclusion_typed t u ts x ys n hx hsource hn)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

private theorem len_smt_arg (A : SmtType) (h : __smtx_typeof_seq_op_1_ret A SmtType.Int = SmtType.Int) :
    ∃ T, A = SmtType.Seq T := by
  cases A <;> simp_all [__smtx_typeof_seq_op_1_ret]

public theorem cmd_step_seq_nth_concat_unit_gen2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_nth_concat_unit_gen2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen2 args premises) := by
  intro hCmd hPremTy hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons t args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons u args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons ts args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons x args =>
          cases args with
          | nil => exact False.elim (hProg rfl)
          | cons ys args =>
            cases args with
            | nil => exact False.elim (hProg rfl)
            | cons n args =>
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
                    change __eo_typeof (__eo_prog_seq_nth_concat_unit_gen2 t u ts x ys n (Proof.pf P)) = Term.Bool at hTy
                    rcases program_info t u ts x ys n P (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, haList, hbList, he⟩
                    change StepRuleProperties M _ (__eo_prog_seq_nth_concat_unit_gen2 t u ts x ys n (Proof.pf P))
                    rw [he] at hTy ⊢
                    have hl : __eo_typeof (lhs t u ts x ys n) ≠ Term.Stuck :=
                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                    rcases nth_arg_types _ _ hl with ⟨T, hsource, hn⟩
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq t (mkConcat u (joined ts x ys)) T hsource with ⟨ht, hinner⟩
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq u (joined ts x ys) T hinner with ⟨hu, hjoin⟩
                    unfold joined at hjoin
                    rw [StringRewriteSupport.list_concat_reduce ts (tail x ys) haList hbList] at hjoin
                    have htail := StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq ts (tail x ys) T haList hjoin
                    rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq (Term.Apply Term.seq_unit x) ys T htail with ⟨hunit, hy⟩
                    have hxTy := unit_arg_type (__eo_typeof x) T hunit
                    have hx : RuleProofs.eo_has_smt_translation x := hCmd.2.2.2.1
                    have hxRaw := TranslationProofs.eo_to_smt_typeof_matches_translation x hx
                    rw [hxTy] at hxRaw
                    have htS := smtx_typeof_of_eo_seq t T hCmd.1 ht
                    have huS := smtx_typeof_of_eo_seq u T hCmd.2.1 hu
                    have hyS := smtx_typeof_of_eo_seq ys T hCmd.2.2.2.2.1 hy
                    rw [← hxRaw] at htS huS hyS
                    have hnS : __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
                      have h := TranslationProofs.eo_to_smt_typeof_matches_translation n hCmd.2.2.2.2.2.1
                      simpa [hn, TranslationProofs.eo_to_smt_type_int] using h
                    have hpTy : RuleProofs.eo_has_bool_type (premise t u ts n) := by
                      have hp := hPremTy P (by simp [P, premiseTermList])
                      simpa [hP] using hp
                    have hlen := (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hpTy).1
                    rw [hnS] at hlen
                    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt (pre t u ts))) = SmtType.Int at hlen
                    rw [typeof_str_len_eq] at hlen
                    rcases len_smt_arg _ hlen with ⟨U, hpre⟩
                    rcases strConcat_args_of_seq_type t (mkConcat u ts) U hpre with ⟨htU, hrest⟩
                    have hUT : U = __smtx_typeof (__eo_to_smt x) := by
                      rw [htS] at htU
                      exact (SmtType.Seq.inj htU).symm
                    rw [hUT] at hrest
                    have htsS := (strConcat_args_of_seq_type u ts _ hrest).2
                    have hjS := StringRewriteSupport.list_concat_has_seq_type ts (tail x ys) _ haList hbList htsS (tail_type x ys hyS)
                    have hsourceS := concat_type t (mkConcat u (joined ts x ys)) _ htS (concat_type u (joined ts x ys) _ huS hjS)
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ (conclusion_typed t u ts x ys n hx hsourceS hnS)⟩
                    intro hTrue
                    apply conclusion_facts M hM t u ts x ys n hx htS huS htsS hyS hnS haList hbList hsourceS
                    have hp := hTrue P (by simp [P, premiseTermList])
                    simpa [hP] using hp
