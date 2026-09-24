module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev ctnFullFalsePremise (x y : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains y) x))
    (Term.Boolean false)

private abbrev ctnFullFalseLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) y

private abbrev ctnFullFalseConclusion (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (ctnFullFalseLhs x y)) (Term.Boolean false)

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_typeof_boolean_term_eq (b : native_Bool) :
    __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]

private theorem same_smt_type_of_ctn_full_false_conclusion_type
    (x y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : __eo_typeof (ctnFullFalseConclusion x y) = Term.Bool) :
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  let lhs := ctnFullFalseLhs x y
  change __eo_typeof_eq (__eo_typeof lhs) Term.Bool = Term.Bool at hTy
  have hLhsTy : __eo_typeof lhs = Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq (__eo_typeof lhs) Term.Bool hTy
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at hLhsTy
  have hSameEO : __eo_typeof x = __eo_typeof y :=
    RuleProofs.eo_typeof_eq_bool_operands_eq
      (__eo_typeof x) (__eo_typeof y) hLhsTy
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hYTrans
  refine ⟨?_, hXTrans⟩
  rw [hXSmtTy, hYSmtTy, hSameEO]

private theorem smt_seq_types_of_ctn_full_false_premise_type
    (x y : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (ctnFullFalsePremise x y)) =
        SmtType.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  change __smtx_typeof
      (SmtTerm.eq
        (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x))
        (SmtTerm.Boolean false)) = SmtType.Bool at hTy
  rw [typeof_eq_eq] at hTy
  rcases (RuleProofs.smtx_typeof_eq_bool_iff
      (__smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x)))
      (__smtx_typeof (SmtTerm.Boolean false))).mp hTy with
    ⟨_hContainsSame, hContainsNN⟩
  have hContainsNN' :
      term_has_non_none_type
        (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hContainsNN
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
      (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x))
      hContainsNN' with ⟨T, hYSmtTy, hXSmtTy⟩
  exact ⟨T, hXSmtTy, hYSmtTy⟩

private theorem prog_str_eq_ctn_full_false1_info
    (x y P : Term)
    (hProg : __eo_prog_str_eq_ctn_full_false1 x y (Proof.pf P) ≠ Term.Stuck) :
    ∃ x0 y0,
      P = ctnFullFalsePremise x0 y0 ∧
      x0 = x ∧
      y0 = y ∧
      __eo_prog_str_eq_ctn_full_false1 x y (Proof.pf P) =
        ctnFullFalseConclusion x y := by
  unfold __eo_prog_str_eq_ctn_full_false1 at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hEq :=
      RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg
    rcases hEq with ⟨hy, hx⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_eq_ctn_full_false1, __eo_requires, __eo_eq, __eo_and,
      SmtEval.native_ite, native_teq, native_and, SmtEval.native_not,
      ctnFullFalseConclusion, ctnFullFalseLhs]

private theorem typed___eo_prog_str_eq_ctn_full_false1_impl
    (x y P : Term)
    (hSameTy :
      __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y))
    (hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hProgEq :
      __eo_prog_str_eq_ctn_full_false1 x y (Proof.pf P) =
        ctnFullFalseConclusion x y) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_eq_ctn_full_false1 x y (Proof.pf P)) := by
  let lhs := ctnFullFalseLhs x y
  let rhs := Term.Boolean false
  have hLhsTy : RuleProofs.eo_has_bool_type lhs :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x y hSameTy hXNonNone
  have hLhsSmtTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := hLhsTy
  have hRhsSmtTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    simpa [rhs] using smtx_typeof_boolean_term_eq false
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsSmtTy, hRhsSmtTy]) (by rw [hLhsSmtTy]; simp)
  rw [hProgEq]
  simpa [ctnFullFalseConclusion, lhs, rhs] using hBoolEq

private theorem facts___eo_prog_str_eq_ctn_full_false1_impl
    (M : SmtModel) (hM : model_wf M) (x y P : Term)
    (hSameTy :
      __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y))
    (hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hPrem : eo_interprets M (ctnFullFalsePremise x y) true)
    (hProgEq :
      __eo_prog_str_eq_ctn_full_false1 x y (Proof.pf P) =
        ctnFullFalseConclusion x y) :
    eo_interprets M (__eo_prog_str_eq_ctn_full_false1 x y (Proof.pf P)) true := by
  let lhs := ctnFullFalseLhs x y
  let rhs := Term.Boolean false
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProgEq, ctnFullFalseConclusion, lhs, rhs] using
      typed___eo_prog_str_eq_ctn_full_false1_impl x y P
        hSameTy hXNonNone hProgEq
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true hPremTy hEval =>
      rcases smt_seq_types_of_ctn_full_false_premise_type x y hPremTy with
        ⟨T, hXSmtTy, hYSmtTy⟩
      have hXEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
            SmtType.Seq T := by
        simpa [hXSmtTy] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
            unfold term_has_non_none_type
            rw [hXSmtTy]
            simp)
      have hYEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
            SmtType.Seq T := by
        simpa [hYSmtTy] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
            unfold term_has_non_none_type
            rw [hYSmtTy]
            simp)
      rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
      rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
      have hSeqNe : sx ≠ sy := by
        intro hSeqEq
        have hEvalFalse :
            __smtx_model_eval M (__eo_to_smt (ctnFullFalsePremise x y)) =
              SmtValue.Boolean false := by
          change __smtx_model_eval M
              (SmtTerm.eq
                (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x))
                (SmtTerm.Boolean false)) =
            SmtValue.Boolean false
          rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
            hYEval, hXEval, smtx_eval_boolean_term_eq]
          rw [hSeqEq]
          simp [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
            native_seq_contains_self, native_veq]
        rw [hEvalFalse] at hEval
        cases hEval
      have hEvalEq :
          __smtx_model_eval M (__eo_to_smt lhs) =
            __smtx_model_eval M (__eo_to_smt rhs) := by
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) =
          __smtx_model_eval M (SmtTerm.Boolean false)
        rw [smtx_eval_eq_term_eq, hXEval, hYEval, smtx_eval_boolean_term_eq]
        simp [__smtx_model_eval_eq, native_veq, hSeqNe]
      rw [hProgEq]
      exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
        rw [hEvalEq]
        exact RuleProofs.smt_value_rel_refl
          (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_ctn_full_false1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_ctn_full_false1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_ctn_full_false1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_ctn_full_false1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_eq_ctn_full_false1 args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n premises =>
                  cases premises with
                  | nil =>
                      let P := __eo_state_proven_nth s n
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.2.1
                      change __eo_typeof
                          (__eo_prog_str_eq_ctn_full_false1 a1 a2 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      have hProgRule :
                          __eo_prog_str_eq_ctn_full_false1 a1 a2 (Proof.pf P) ≠
                            Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      rcases prog_str_eq_ctn_full_false1_info a1 a2 P hProgRule with
                        ⟨x0, y0, hPremShape, hx0, hy0, hProgEq⟩
                      subst x0
                      subst y0
                      rw [hProgEq] at hResultTy
                      have hSameSmt :=
                        same_smt_type_of_ctn_full_false_conclusion_type
                          a1 a2 hA1Trans hA2Trans hResultTy
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPremRaw : eo_interprets M P true :=
                          hTrue P (by simp [P, premiseTermList])
                        have hPrem :
                            eo_interprets M (ctnFullFalsePremise a1 a2) true := by
                          simpa [hPremShape] using hPremRaw
                        exact facts___eo_prog_str_eq_ctn_full_false1_impl
                          M hM a1 a2 P hSameSmt.1 hSameSmt.2 hPrem hProgEq
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_eq_ctn_full_false1_impl a1 a2 P
                            hSameSmt.1 hSameSmt.2 hProgEq)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
