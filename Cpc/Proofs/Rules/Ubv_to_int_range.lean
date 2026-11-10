module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem ubv_to_int_range_shape_of_ne_stuck (A : Term) :
    __eo_prog_ubv_to_int_range A ≠ Term.Stuck ->
    ∃ b, A = Term.Apply (Term.UOp UserOp.ubv_to_int) b := by
  intro h
  by_cases hShape : ∃ b, A = Term.Apply (Term.UOp UserOp.ubv_to_int) b
  · exact hShape
  · have hStuck : __eo_prog_ubv_to_int_range A = Term.Stuck := by
      rw [__eo_prog_ubv_to_int_range.eq_2]
      intro b hEq
      exact hShape ⟨b, hEq⟩
    exact False.elim (h hStuck)

/-- The bound appearing in the conclusion, once the bit-width is known. -/
private def ubvRangeBound (w : native_Nat) : Term :=
  Term.Numeral (native_zexp_total 2 (native_nat_to_int w))

private def ubvRangeConclusion (b : Term) (w : native_Nat) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) (Term.Numeral 0))
        (Term.Apply (Term.UOp UserOp.ubv_to_int) b)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.lt)
            (Term.Apply (Term.UOp UserOp.ubv_to_int) b))
          (ubvRangeBound w)))
      (Term.Boolean true))

private theorem ubv_to_int_range_prog_eq
    (b : Term) (w : native_Nat)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w) :
    __eo_prog_ubv_to_int_range (Term.Apply (Term.UOp UserOp.ubv_to_int) b) =
      ubvRangeConclusion b w := by
  have hbTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hbTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation b hbTrans
  have hEoSmt : __eo_to_smt_type (__eo_typeof b) = SmtType.BitVec w := by
    rw [← hMatch, hbTy]
  have hEoTy :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hEoSmt
  have hWidth :
      __bv_bitwidth (__eo_typeof b) = Term.Numeral (native_nat_to_int w) := by
    rw [hEoTy]
    rfl
  have hnot : ¬ ((native_nat_to_int w) < 0) := by
    simp [native_nat_to_int]
  rw [__eo_prog_ubv_to_int_range.eq_1]
  simp only [hWidth]
  simp [ubvRangeConclusion, ubvRangeBound, __eo_is_z, __eo_is_z_internal,
    __eo_is_neg, __eo_ite, __eo_pow, __eo_mk_apply, native_ite, native_teq,
    native_not, native_and, SmtEval.native_not, SmtEval.native_and,
    native_zlt, SmtEval.native_zlt, hnot]

private theorem eo_interprets_leq_of_numerals
    (M : SmtModel) (x y : Term) (a c : native_Int)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral a)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Numeral c)
    (hle : a <= c) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) true := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  change smt_interprets M (SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y)) true
  apply smt_interprets.intro_true
  · rw [typeof_leq_eq, hxTy, hyTy]
    rfl
  · rw [__smtx_model_eval.eq_def]
    simp only
    rw [hxEval, hyEval]
    simp [__smtx_model_eval_leq, native_zleq, SmtEval.native_zleq, hle]

private theorem eo_interprets_lt_of_numerals
    (M : SmtModel) (x y : Term) (a c : native_Int)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral a)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Numeral c)
    (hlt : a < c) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) true := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  change smt_interprets M (SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y)) true
  apply smt_interprets.intro_true
  · rw [typeof_lt_eq, hxTy, hyTy]
    rfl
  · rw [__smtx_model_eval.eq_def]
    simp only
    rw [hxEval, hyEval]
    simp [__smtx_model_eval_lt, native_zlt, SmtEval.native_zlt, hlt]

public theorem cmd_step_ubv_to_int_range_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ubv_to_int_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ubv_to_int_range args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ubv_to_int_range args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.ubv_to_int_range args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons A2 argsRest =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons n rest =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_ubv_to_int_range A)
              have hProgNe' : __eo_prog_ubv_to_int_range A ≠ Term.Stuck := by
                exact hProgNe
              rcases ubv_to_int_range_shape_of_ne_stuck A hProgNe' with
                ⟨b, hShape⟩
              subst A
              have hUbvNN :
                  term_has_non_none_type
                    (SmtTerm.ubv_to_int (__eo_to_smt b)) := by
                unfold term_has_non_none_type
                exact hATrans
              rcases
                  bv_unop_ret_arg_of_non_none
                    (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
                    (by rw [smtx_typeof_ubv_to_int_term_eq]) hUbvNN with
                ⟨w, hbTy⟩
              have hProgEq := ubv_to_int_range_prog_eq b w hbTy
              rw [hProgEq]
              -- Evaluate the bit-vector argument.
              have hbNN : term_has_non_none_type (__eo_to_smt b) := by
                unfold term_has_non_none_type
                rw [hbTy]
                intro h
                cases h
              have hEvalTy := type_preservation M hM (__eo_to_smt b) hbNN
              rw [hbTy] at hEvalTy
              rcases bitvec_value_canonical hEvalTy with ⟨n, hEvalB⟩
              have hValueTy :
                  __smtx_typeof_value (SmtValue.Binary (native_nat_to_int w) n) =
                    SmtType.BitVec w := by
                simpa [hEvalB] using hEvalTy
              have hWidthNonneg := bitvec_width_nonneg hValueTy
              have hPayloadMod := bitvec_payload_canonical hValueTy
              have hRange :=
                bitvec_payload_range_of_canonical hWidthNonneg hPayloadMod
              let x := Term.Apply (Term.UOp UserOp.ubv_to_int) b
              have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
                change __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt b)) =
                  SmtType.Int
                rw [smtx_typeof_ubv_to_int_term_eq, hbTy]
                rfl
              have hxEval :
                  __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral n := by
                change __smtx_model_eval M (SmtTerm.ubv_to_int (__eo_to_smt b)) =
                  SmtValue.Numeral n
                rw [smtx_eval_ubv_to_int_term_eq, hEvalB]
                rfl
              have hNumTy (k : native_Int) :
                  __smtx_typeof (__eo_to_smt (Term.Numeral k)) = SmtType.Int := by
                rfl
              have hNumEval (k : native_Int) :
                  __smtx_model_eval M (__eo_to_smt (Term.Numeral k)) =
                    SmtValue.Numeral k := by
                rfl
              have hLower :
                  eo_interprets M
                    (Term.Apply (Term.Apply (Term.UOp UserOp.leq)
                      (Term.Numeral 0)) x) true :=
                eo_interprets_leq_of_numerals M (Term.Numeral 0) x 0 n
                  (hNumTy 0) hxTy (hNumEval 0) hxEval hRange.1
              have hUpper :
                  eo_interprets M
                    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x)
                      (ubvRangeBound w)) true := by
                have hlt : n < native_zexp_total 2 (native_nat_to_int w) := by
                  simpa [native_int_pow2, SmtEval.native_int_pow2] using
                    hRange.2
                exact eo_interprets_lt_of_numerals M x (ubvRangeBound w) n
                  (native_zexp_total 2 (native_nat_to_int w))
                  hxTy (hNumTy _) hxEval (hNumEval _) hlt
              have hFact : eo_interprets M (ubvRangeConclusion b w) true :=
                RuleProofs.eo_interprets_and_intro M _ _ hLower
                  (RuleProofs.eo_interprets_and_intro M _ _ hUpper
                    (RuleProofs.eo_interprets_true M))
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    exact hFact
                  has_smt_translation :=
                    RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (RuleProofs.eo_has_bool_type_of_interprets_true M _
                        hFact) }
