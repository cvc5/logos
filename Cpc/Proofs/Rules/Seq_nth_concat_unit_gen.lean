module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

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


private abbrev nthConcatLhs (pre x ys n : Term) : Term :=
  Term.Apply (Term.Apply Term.seq_nth
    (mkConcat pre (mkConcat (Term.Apply Term.seq_unit x) ys))) n

private abbrev nthConcatConclusion (pre x ys n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (nthConcatLhs pre x ys n)) x

private abbrev nthConcatPremise (pre n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len pre)) n

private theorem nthConcatProgram (pre x ys n P : Term)
    (h : __eo_prog_seq_nth_concat_unit_gen pre x ys n (Proof.pf P) ≠ Term.Stuck) :
    P = nthConcatPremise pre n ∧
      __eo_prog_seq_nth_concat_unit_gen pre x ys n (Proof.pf P) =
        nthConcatConclusion pre x ys n := by
  unfold __eo_prog_seq_nth_concat_unit_gen at h
  split at h <;> try contradiction
  next he =>
    cases he
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ h with ⟨hp, hn⟩
    subst_vars
    refine ⟨rfl, ?_⟩
    simp [__eo_prog_seq_nth_concat_unit_gen, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not,
      nthConcatConclusion, nthConcatLhs, mkConcat]

private theorem nthConcatTyped (pre x ys n : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hp : __smtx_typeof (__eo_to_smt pre) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (nthConcatConclusion pre x ys n) := by
  let T := __smtx_typeof (__eo_to_smt x)
  have hGood := smt_term_result_seq_components_wf_of_non_none (__eo_to_smt ys)
    (term_has_non_none_of_type_eq hy (by simp))
  rw [hy] at hGood
  change __smtx_type_wf (SmtType.Seq T) = true at hGood
  have hElem : __smtx_type_wf T = true := seq_type_wf_component_of_wf hGood
  have hUnit : __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt x)) = SmtType.Seq T := by
    rw [smtx_typeof_seq_unit_term_eq]
    simp [__smtx_typeof_guard_wf, hGood, native_ite, T]
  have hConcat : __smtx_typeof
      (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys)) =
      SmtType.Seq T := by
    rw [typeof_str_concat_eq, hUnit, hy]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, T]
  have hAll : __smtx_typeof (SmtTerm.str_concat (__eo_to_smt pre)
      (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys))) =
      SmtType.Seq T := by
    rw [typeof_str_concat_eq, hp, hConcat]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, T]
  have hLhs : __smtx_typeof (__eo_to_smt (nthConcatLhs pre x ys n)) = T := by
    change __smtx_typeof (SmtTerm.seq_nth (SmtTerm.str_concat (__eo_to_smt pre)
      (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys)))
      (__eo_to_smt n)) = T
    rw [typeof_seq_nth_eq, hAll, hn]
    simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hElem, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (nthConcatLhs pre x ys n) x
    hLhs (by rw [hLhs]; exact hx)

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

private theorem nthConcatFacts (M : SmtModel) (hM : model_wf M) (pre x ys n : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hp : __smtx_typeof (__eo_to_smt pre) = SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hPrem : eo_interprets M (nthConcatPremise pre n) true) :
    eo_interprets M (nthConcatConclusion pre x ys n) true := by
  have hVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt ys)) =
      SmtType.Seq (__smtx_typeof (__eo_to_smt x)) := by
    simpa [hy] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt ys)
      (term_has_non_none_of_type_eq hy (by simp))
  have hpVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt pre)) =
      SmtType.Seq (__smtx_typeof (__eo_to_smt x)) := by
    simpa [hp] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt pre)
      (term_has_non_none_of_type_eq hp (by simp))
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases seq_value_canonical hVal with ⟨ss, hs⟩
  rcases seq_value_canonical hpVal with ⟨ps, hps⟩
  rcases int_value_canonical hnVal with ⟨ni, hni⟩
  have hi : ni = ((native_unpack_seq ps).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt pre))
        (__eo_to_smt n)) = SmtValue.Boolean true at he
      rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hps, hni] at he
      symm
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq] using he
  have hEq : __smtx_model_eval M (__eo_to_smt (nthConcatLhs pre x ys n)) =
      __smtx_model_eval M (__eo_to_smt x) := by
    change __smtx_model_eval M (SmtTerm.seq_nth (SmtTerm.str_concat (__eo_to_smt pre)
      (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys)))
      (__eo_to_smt n)) = _
    simp only [nthConcatEvalNth, nthConcatEvalConcat, nthConcatEvalUnit, hs, hps, hni, hi]
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_unpack_seq,
      Smtm.native_unpack_pack_seq, __smtx_seq_nth, seq_value_nth_pack_append_cons]
  exact RuleProofs.eo_interprets_eq_of_rel M (nthConcatLhs pre x ys n) x
    (nthConcatTyped pre x ys n hx hy hp hn) (by rw [hEq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_seq_nth_concat_unit_gen_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_nth_concat_unit_gen args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_nth_concat_unit_gen args premises) := by
  intro hCmd _ hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons pre args =>
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
                have hpre : RuleProofs.eo_has_smt_translation pre := hCmd.1
                have hx : RuleProofs.eo_has_smt_translation x := hCmd.2.1
                have hy : RuleProofs.eo_has_smt_translation ys := hCmd.2.2.1
                have hn : RuleProofs.eo_has_smt_translation n := hCmd.2.2.2.1
                change __eo_typeof (__eo_prog_seq_nth_concat_unit_gen pre x ys n (Proof.pf P)) = Term.Bool at hTy
                rcases nthConcatProgram pre x ys n P (term_ne_stuck_of_typeof_bool hTy) with ⟨hPrem, hp⟩
                change StepRuleProperties M _ (__eo_prog_seq_nth_concat_unit_gen pre x ys n (Proof.pf P))
                rw [hp] at hTy ⊢
                have hLhs : __eo_typeof (nthConcatLhs pre x ys n) ≠ Term.Stuck :=
                  (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                rcases nth_arg_types _ _ hLhs with ⟨T, hAll, hNTy⟩
                rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq pre
                    (mkConcat (Term.Apply Term.seq_unit x) ys) T hAll with ⟨hPTy, hInner⟩
                rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                    (Term.Apply Term.seq_unit x) ys T hInner with ⟨hUnit, hYTy⟩
                have hXTy := unit_arg_type (__eo_typeof x) T hUnit
                have hXRaw := TranslationProofs.eo_to_smt_typeof_matches_translation x hx
                rw [hXTy] at hXRaw
                have hpSmt := smtx_typeof_of_eo_seq pre T hpre hPTy
                have hySmt := smtx_typeof_of_eo_seq ys T hy hYTy
                rw [← hXRaw] at hpSmt hySmt
                have hnSmt : __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
                  have h := TranslationProofs.eo_to_smt_typeof_matches_translation n hn
                  simpa [hNTy, TranslationProofs.eo_to_smt_type_int] using h
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (nthConcatTyped pre x ys n hx hySmt hpSmt hnSmt)⟩
                intro hTrue
                have hP := hTrue P (by simp [P, premiseTermList])
                apply nthConcatFacts M hM pre x ys n hx hySmt hpSmt hnSmt
                simpa [hPrem] using hP
