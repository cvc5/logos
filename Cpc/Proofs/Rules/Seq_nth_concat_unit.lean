module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo Smtm SmtEval
set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem seq_nth_concat_unit_arg_types (A B : Term)
    (h : __eo_typeof_seq_nth
      (__eo_typeof_str_concat (__eo_typeof_seq_unit A) B) Term.Int ≠ Term.Stuck) :
    B = Term.Apply Term.Seq A := by
  have ha : A ≠ Term.Stuck := by
    intro hA
    subst A
    simp [__eo_typeof_seq_unit, __eo_typeof_str_concat, __eo_typeof_seq_nth] at h
  have hu : __eo_typeof_seq_unit A = Term.Apply Term.Seq A := by
    cases A <;> simp [__eo_typeof_seq_unit] at ha ⊢
  rw [hu] at h
  have hc : __eo_typeof_str_concat (Term.Apply Term.Seq A) B ≠ Term.Stuck := by
    intro he
    rw [he] at h
    exact h rfl
  cases B <;> try simp [__eo_typeof_str_concat] at hc
  case Apply f b =>
    cases f <;> try simp at hc
    case UOp op =>
      cases op <;> try simp at hc
      case Seq =>
        have he : b = A := RuleProofs.eq_of_requires_eq_true_not_stuck A b
          (Term.Apply Term.Seq A) hc
        subst b
        rfl

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


private abbrev nthConcatLhs (x ys : Term) : Term :=
  Term.Apply (Term.Apply Term.seq_nth
    (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit x)) ys))
    (Term.Numeral 0)

private abbrev nthConcatConclusion (x ys : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (nthConcatLhs x ys)) x

private theorem nthConcatTyped (x ys : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x))) :
    RuleProofs.eo_has_bool_type (nthConcatConclusion x ys) := by
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
  have hLhs : __smtx_typeof (__eo_to_smt (nthConcatLhs x ys)) = T := by
    change __smtx_typeof (SmtTerm.seq_nth
      (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys))
      (SmtTerm.Numeral 0)) = T
    rw [typeof_seq_nth_eq, hConcat]
    have hn : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
      rw [__smtx_typeof.eq_def]
    rw [hn]
    simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hElem, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (nthConcatLhs x ys) x
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

private theorem nthConcatFacts (M : SmtModel) (hM : model_wf M) (x ys : Term)
    (hx : RuleProofs.eo_has_smt_translation x)
    (hy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq (__smtx_typeof (__eo_to_smt x))) :
    eo_interprets M (nthConcatConclusion x ys) true := by
  have hVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt ys)) =
      SmtType.Seq (__smtx_typeof (__eo_to_smt x)) := by
    simpa [hy] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt ys)
      (term_has_non_none_of_type_eq hy (by simp))
  rcases seq_value_canonical hVal with ⟨ss, hs⟩
  have hEq : __smtx_model_eval M (__eo_to_smt (nthConcatLhs x ys)) =
      __smtx_model_eval M (__eo_to_smt x) := by
    change __smtx_model_eval M (SmtTerm.seq_nth
      (SmtTerm.str_concat (SmtTerm.seq_unit (__eo_to_smt x)) (__eo_to_smt ys))
      (SmtTerm.Numeral 0)) = _
    rw [nthConcatEvalNth, nthConcatEvalConcat, nthConcatEvalUnit, hs]
    have hn : __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
      rw [__smtx_model_eval.eq_def]
    rw [hn]
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_unpack_seq,
      native_pack_seq, __smtx_seq_nth, __smtx_seq_value_nth]
  exact RuleProofs.eo_interprets_eq_of_rel M (nthConcatLhs x ys) x
    (nthConcatTyped x ys hx hy) (by rw [hEq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_seq_nth_concat_unit_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_nth_concat_unit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_nth_concat_unit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_nth_concat_unit args premises) := by
  intro hCmd _ hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons x args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons ys args =>
      cases args with
      | cons _ _ => exact False.elim (hProg rfl)
      | nil =>
        cases premises with
        | cons _ _ => exact False.elim (hProg rfl)
        | nil =>
          have hx : RuleProofs.eo_has_smt_translation x := hCmd.1
          have hy : RuleProofs.eo_has_smt_translation ys := hCmd.2.1
          have hxn := RuleProofs.term_ne_stuck_of_has_smt_translation x hx
          have hyn := RuleProofs.term_ne_stuck_of_has_smt_translation ys hy
          have hp : __eo_cmd_step_proven s CRule.seq_nth_concat_unit
              (.cons x (.cons ys .nil)) .nil = nthConcatConclusion x ys := by
            change __eo_prog_seq_nth_concat_unit x ys = nthConcatConclusion x ys
            unfold __eo_prog_seq_nth_concat_unit
            split <;> simp_all [nthConcatConclusion, nthConcatLhs]
          rw [hp] at hTy ⊢
          have hLhs : __eo_typeof (nthConcatLhs x ys) ≠ Term.Stuck :=
            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
          have hYTy : __eo_typeof ys = Term.Apply Term.Seq (__eo_typeof x) :=
            seq_nth_concat_unit_arg_types _ _ hLhs
          have hySmt := smtx_typeof_of_eo_seq ys (__eo_typeof x) hy hYTy
          rw [← TranslationProofs.eo_to_smt_typeof_matches_translation x hx] at hySmt
          exact ⟨fun _ => nthConcatFacts M hM x ys hx hySmt,
            RuleProofs.eo_has_smt_translation_of_has_bool_type _
              (nthConcatTyped x ys hx hySmt)⟩
