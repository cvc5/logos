module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

import Cpc.Proofs.RuleSupport.StrEqReplSupport

open Eo Smtm SmtEval
open StrConcatClashSupport
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


private abbrev nthConcatTail (ts x ys : Term) : Term :=
  __eo_list_concat Term.str_concat ts (mkConcat (Term.Apply Term.seq_unit x) ys)

private abbrev nthConcatLhs (t ts x ys n : Term) : Term :=
  Term.Apply (Term.Apply Term.seq_nth (mkConcat t (nthConcatTail ts x ys))) n

private abbrev nthConcatConclusion (t ts x ys n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (nthConcatLhs t ts x ys n)) x

-- The generated premise implies n = len(t) + len(ts), the prefix before x.
private abbrev nthConcatPremise (t ts n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq
    (Term.Apply Term.str_len (mkConcat t (mkConcat t ts))))
    (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len t))
      (Term.Apply (Term.Apply Term.plus n) (Term.Numeral 0)))

private theorem nthConcatProgram (t ts x ys n P : Term)
    (ht : t ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hx : x ≠ Term.Stuck) (hy : ys ≠ Term.Stuck) (hn : n ≠ Term.Stuck)
    (h : __eo_prog_seq_nth_concat_unit_gen t ts x ys n (Proof.pf P) ≠ Term.Stuck) :
    P = nthConcatPremise t ts n ∧
      __eo_prog_seq_nth_concat_unit_gen t ts x ys n (Proof.pf P) =
        nthConcatConclusion t ts x ys n := by
  unfold __eo_prog_seq_nth_concat_unit_gen at h
  split at h <;> try contradiction
  next he =>
    cases he
    have hg := support_eo_requires_cond_eq_of_non_stuck h
    have hn' := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have ht4 := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have hts' := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have ht3 := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have ht2 := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_left hg)
    subst_vars
    refine ⟨rfl, ?_⟩
    simp_all [__eo_prog_seq_nth_concat_unit_gen, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not, __eo_mk_apply,
      nthConcatConclusion, nthConcatLhs, nthConcatTail, mkConcat]
    all_goals repeat (first | (split <;> simp_all [__eo_mk_apply]) | assumption)

private theorem nthConcatPremiseTypes (t ts n : Term)
    (hBool : RuleProofs.eo_has_bool_type (nthConcatPremise t ts n)) :
    ∃ T, __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt ts) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.eq
    (SmtTerm.str_len (__eo_to_smt (mkConcat t (mkConcat t ts))))
    (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt t))
      (SmtTerm.plus (__eo_to_smt n) (SmtTerm.Numeral 0)))) = SmtType.Bool at hBool
  rw [typeof_eq_eq] at hBool
  have hNN := fun he => (by decide : SmtType.Bool ≠ SmtType.None) (hBool.symm.trans he)
  have hLeft := (TranslationProofs.smtx_typeof_eq_non_none hNN).2
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len) (R := SmtType.Int)
    (typeof_str_len_eq _) hLeft with ⟨T, hSeq⟩
  rcases str_concat_args_of_seq_type t (mkConcat t ts) T hSeq with ⟨ht, hts⟩
  exact ⟨T, ht, (str_concat_args_of_seq_type t ts T hts).2⟩

private theorem nthConcatTyped (t ts x ys n : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hp : __smtx_typeof (__eo_to_smt t) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hTail : __smtx_typeof (__eo_to_smt (nthConcatTail ts x ys)) =
      SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (nthConcatConclusion t ts x ys n) := by
  let T := __smtx_typeof (__eo_to_smt x)
  have hGood := smt_term_result_seq_components_wf_of_non_none (__eo_to_smt t)
    (term_has_non_none_of_type_eq hp (by simp))
  rw [hp] at hGood
  change __smtx_type_wf (SmtType.Seq T) = true at hGood
  have hElem : __smtx_type_wf T = true := seq_type_wf_component_of_wf hGood
  have hAll := smt_typeof_str_concat_of_seq t (nthConcatTail ts x ys) T hp hTail
  have hLhs : __smtx_typeof (__eo_to_smt (nthConcatLhs t ts x ys n)) = T := by
    change __smtx_typeof (SmtTerm.seq_nth
      (__eo_to_smt (mkConcat t (nthConcatTail ts x ys))) (__eo_to_smt n)) = T
    rw [typeof_seq_nth_eq, hAll, hn]
    simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hElem, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ x hLhs (by rw [hLhs]; exact hx)

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

private theorem nthConcatEvalPlus (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus a b) =
      __smtx_model_eval_plus (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

private theorem nthConcatFacts (M : SmtModel) (hM : model_wf M) (t ts x ys n : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hts : __smtx_typeof (__eo_to_smt ts) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hTailNe : nthConcatTail ts x ys ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (nthConcatConclusion t ts x ys n) ∧
      (eo_interprets M (nthConcatPremise t ts n) true ->
       eo_interprets M (nthConcatConclusion t ts x ys n) true) := by
  let T := __smtx_typeof (__eo_to_smt x)
  let z := mkConcat (Term.Apply Term.seq_unit x) ys
  have hList := (concat_clash_rev_list_concat_facts ts z hTailNe).1
  have hRec := concat_clash_rev_list_concat_eq_rec ts z hTailNe
  have hGood := smt_term_result_seq_components_wf_of_non_none (__eo_to_smt ys)
    (term_has_non_none_of_type_eq hy (by simp))
  rw [hy] at hGood
  change __smtx_type_wf (SmtType.Seq T) = true at hGood
  have hUnit : __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit x)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt x)) = _
    rw [smtx_typeof_seq_unit_term_eq]
    simp [__smtx_typeof_guard_wf, hGood, native_ite, T]
  have hZ := smt_typeof_str_concat_of_seq (Term.Apply Term.seq_unit x) ys T hUnit hy
  have hTail : __smtx_typeof (__eo_to_smt (nthConcatTail ts x ys)) = SmtType.Seq T := by
    rw [show nthConcatTail ts x ys = __eo_list_concat_rec ts z from hRec]
    exact smt_typeof_list_concat_rec_str_concat_of_seq ts z T hList hts hZ
  have hTyped := nthConcatTyped t ts x ys n hx ht hTail hn
  refine ⟨hTyped, ?_⟩
  intro hPrem
  have htVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Seq T := by
    simpa [ht, T] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (term_has_non_none_of_type_eq ht (by simp))
  have htsVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt ts)) = SmtType.Seq T := by
    simpa [hts, T] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt ts)
      (term_has_non_none_of_type_eq hts (by simp))
  have hyVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt ys)) = SmtType.Seq T := by
    simpa [hy, T] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt ys)
      (term_has_non_none_of_type_eq hy (by simp))
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases seq_value_canonical htVal with ⟨st, hst⟩
  rcases seq_value_canonical htsVal with ⟨ss, hss⟩
  rcases seq_value_canonical hyVal with ⟨sy, hsy⟩
  rcases int_value_canonical hnVal with ⟨ni, hni⟩
  have hi : ni = ((native_unpack_seq st ++ native_unpack_seq ss).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq
        (SmtTerm.str_len (SmtTerm.str_concat (__eo_to_smt t)
          (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt ts))))
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt t))
          (SmtTerm.plus (__eo_to_smt n) (SmtTerm.Numeral 0)))) = SmtValue.Boolean true at he
      have hZero : __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
        rw [__smtx_model_eval.eq_def]
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, nthConcatEvalConcat,
        nthConcatEvalPlus, hst, hss, hni, hZero] at he
      simp [__smtx_model_eval_eq, __smtx_model_eval_str_len, __smtx_model_eval_str_concat,
        __smtx_model_eval_plus, native_seq_concat, native_seq_len,
        Smtm.native_unpack_pack_seq, native_veq, native_zplus, native_nat_to_int,
        List.length_append] at he ⊢
      exact he.symm
  let xv := __smtx_model_eval M (__eo_to_smt x)
  have hZeval : __smtx_model_eval M (__eo_to_smt z) =
      SmtValue.Seq (native_pack_seq (__smtx_typeof_value xv) (xv :: native_unpack_seq sy)) := by
    change __smtx_model_eval M (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys)) = _
    rw [nthConcatEvalConcat, nthConcatEvalUnit, hsy]
    rfl
  -- Appending the encoded list has the same value as sequence concatenation.
  have hFlatRel := smt_value_rel_list_concat_rec_str_concat M hM ts z T hList hts hZ
  rw [← hRec] at hFlatRel
  have hRhsEval : __smtx_model_eval M (__eo_to_smt (mkConcat ts z)) =
      SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_unpack_seq ss ++ xv :: native_unpack_seq sy)) := by
    change __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt ts) (__eo_to_smt z)) = _
    rw [nthConcatEvalConcat, hss, hZeval]
    simp [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq]
  rw [hRhsEval] at hFlatRel
  have hFlatEq := (RuleProofs.smt_value_rel_iff_eq _ _ (by
    rintro ⟨r1, r2, _, h⟩; cases h)).mp hFlatRel
  change __smtx_model_eval M (__eo_to_smt (nthConcatTail ts x ys)) = _ at hFlatEq
  have hEq : __smtx_model_eval M (__eo_to_smt (nthConcatLhs t ts x ys n)) = xv := by
    change __smtx_model_eval M (SmtTerm.seq_nth
      (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt (nthConcatTail ts x ys)))
      (__eo_to_smt n)) = xv
    simp only [nthConcatEvalNth, nthConcatEvalConcat, hst, hFlatEq, hni, hi]
    simp [__smtx_model_eval_str_concat, native_seq_concat, Smtm.native_unpack_pack_seq,
      __smtx_seq_nth, ← List.append_assoc]
    simpa only [List.length_append, Int.natCast_add] using
      (seq_value_nth_pack_append_cons (__smtx_elem_typeof_seq_value st)
        (native_unpack_seq st ++ native_unpack_seq ss) xv (native_unpack_seq sy) _)
  exact RuleProofs.eo_interprets_eq_of_rel M _ x hTyped
    (by rw [hEq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_seq_nth_concat_unit_gen_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_nth_concat_unit_gen args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen args premises) := by
  intro hCmd hBools hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons t args =>
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
                  have ht : RuleProofs.eo_has_smt_translation t := hCmd.1
                  have hts : RuleProofs.eo_has_smt_translation ts := hCmd.2.1
                  have hx : RuleProofs.eo_has_smt_translation x := hCmd.2.2.1
                  have hy : RuleProofs.eo_has_smt_translation ys := hCmd.2.2.2.1
                  have hn : RuleProofs.eo_has_smt_translation n := hCmd.2.2.2.2.1
                  change __eo_typeof (__eo_prog_seq_nth_concat_unit_gen t ts x ys n (Proof.pf P)) = Term.Bool at hTy
                  rcases nthConcatProgram t ts x ys n P
                      (RuleProofs.term_ne_stuck_of_has_smt_translation t ht)
                      (RuleProofs.term_ne_stuck_of_has_smt_translation ts hts)
                      (RuleProofs.term_ne_stuck_of_has_smt_translation x hx)
                      (RuleProofs.term_ne_stuck_of_has_smt_translation ys hy)
                      (RuleProofs.term_ne_stuck_of_has_smt_translation n hn)
                      (term_ne_stuck_of_typeof_bool hTy) with ⟨hPrem, hp⟩
                  change StepRuleProperties M _ (__eo_prog_seq_nth_concat_unit_gen t ts x ys n (Proof.pf P))
                  rw [hp] at hTy ⊢
                  have hLhs : __eo_typeof (nthConcatLhs t ts x ys n) ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                  rcases nth_arg_types _ _ hLhs with ⟨U, hAll, hNTy⟩
                  rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                      t (nthConcatTail ts x ys) U hAll with ⟨hTTy, hTailTy⟩
                  have hTailNe : nthConcatTail ts x ys ≠ Term.Stuck := by
                    intro he
                    rw [he] at hTailTy
                    cases hTailTy
                  let z := mkConcat (Term.Apply Term.seq_unit x) ys
                  have hList := (concat_clash_rev_list_concat_facts ts z hTailNe).1
                  have hRec := concat_clash_rev_list_concat_eq_rec ts z hTailNe
                  have hZTy := StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq ts z U hList
                    (by rw [← hRec]; exact hTailTy)
                  rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                      (Term.Apply Term.seq_unit x) ys U hZTy with ⟨hUnit, hYTy⟩
                  have hXTy := unit_arg_type (__eo_typeof x) U hUnit
                  have hXRaw := TranslationProofs.eo_to_smt_typeof_matches_translation x hx
                  rw [hXTy] at hXRaw
                  have htSmt := smtx_typeof_of_eo_seq t U ht hTTy
                  have hySmt := smtx_typeof_of_eo_seq ys U hy hYTy
                  rw [← hXRaw] at htSmt hySmt
                  have hnSmt : __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
                    have h := TranslationProofs.eo_to_smt_typeof_matches_translation n hn
                    simpa [hNTy, TranslationProofs.eo_to_smt_type_int] using h
                  have hPBool := hBools P (by simp [P, premiseTermList])
                  rw [hPrem] at hPBool
                  rcases nthConcatPremiseTypes t ts n hPBool with ⟨V, htV, htsV⟩
                  have hV : V = __smtx_typeof (__eo_to_smt x) := SmtType.Seq.inj (htV.symm.trans htSmt)
                  rw [hV] at htsV
                  have hFacts := nthConcatFacts M hM t ts x ys n hx htSmt htsV hySmt hnSmt hTailNe
                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hFacts.1⟩
                  intro hTrue
                  apply hFacts.2
                  have hP := hTrue P (by simp [P, premiseTermList])
                  simpa [hPrem] using hP
