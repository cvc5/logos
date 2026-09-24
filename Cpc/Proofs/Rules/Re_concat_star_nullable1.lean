module

public import Cpc.Proofs.RuleSupport.ReConcatNullableSupport
import all Cpc.Proofs.RuleSupport.ReConcatNullableSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace ReConcatStarNullable1Proof

/-- `str.in_re "" r = true`, the premise shape. -/
abbrev mkStrInReEmpty (r : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String [])) r))
    (Term.Boolean true)

/-- LHS of the conclusion: `xs · (Σ* · (r · ys))`. -/
abbrev lhs1 (xs1 r1 ys1 : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_concat) xs1
    (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat r1 ys1))

/-- RHS of the conclusion: `singleton_elim (xs · (Σ* · ys))`. -/
abbrev rhs1 (xs1 ys1 : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
    (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
      (RuleProofs.tReConcat RuleProofs.tSigma ys1))

/-- The conclusion produced by `re_concat_star_nullable1` (matching the program's
`__eo_mk_apply` shape). -/
abbrev mkConcl1 (xs1 r1 ys1 : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs1 xs1 r1 ys1)) (rhs1 xs1 ys1)

/-- Structural extraction of the program result, mirroring `Re_loop_star.prog_form`. -/
theorem prog_form (xs1 r1 ys1 P1 : Term)
    (hNe : __eo_prog_re_concat_star_nullable1 xs1 r1 ys1 (Proof.pf P1) ≠ Term.Stuck) :
    P1 = mkStrInReEmpty r1 ∧
      __eo_prog_re_concat_star_nullable1 xs1 r1 ys1 (Proof.pf P1) = mkConcl1 xs1 r1 ys1 := by
  unfold __eo_prog_re_concat_star_nullable1 at hNe ⊢
  split at hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · rename_i heqP1
    injection heqP1 with hP1
    have hCond := RuleProofs.eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := RuleProofs.eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    have hr12 := RuleProofs.eo_eq_eq_true hCond
    rw [hr12] at hP1
    exact ⟨hP1, hReqEq⟩
  · exact absurd rfl hNe

/-- The premise yields nullability of the regex argument. -/
theorem nullable_of_premise (M : SmtModel) (r1 : Term) (r1v : SmtRegLan)
    (hR1 : __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan r1v)
    (hP : eo_interprets M (mkStrInReEmpty r1) true) :
    native_re_nullable r1v = true := by
  have hRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String [])) r1)
      (Term.Boolean true) hP
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String [])) r1)) =
        SmtValue.Boolean (native_str_in_re ([] : native_String) r1v) :=
    RuleProofs.smtx_model_eval_str_in_re_string M ([] : native_String) r1 r1v hR1
  have hTrue :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) = SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = _
    rw [__smtx_model_eval.eq_1]
  rw [hEval, hTrue] at hRel
  have hEq : SmtValue.Boolean (native_str_in_re ([] : native_String) r1v) =
      SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by rintro ⟨a, b, hbad, _⟩; cases hbad)).1 hRel
  have hMem : native_str_in_re ([] : native_String) r1v = true := by
    simpa using hEq
  have hNull : native_re_nullable r1v = true := by
    simpa [Smtm.native_str_in_re, native_re_str_valid, impl_native_string_to_values]
      using hMem
  exact hNull

end ReConcatStarNullable1Proof

open ReConcatStarNullable1Proof

/-
The semantic content of this rule is proved by `RuleProofs.nullable1_eval_rel`
and assembled below.  The accompanying typing bundle (`eo_has_bool_type` of the
conclusion, the `re_concat`-list structure of `xs1`/`ys1`, and that the `RegLan`
arguments and the assembled `re.++` chains evaluate to regular-language values)
is discharged in full: it is obtained by threading the
`list_concat`/`singleton_elim` typing lemmas in `ReConcatNullableSupport` through
the EO→SMT type-preservation bridge.  This rule has no EO/SMT typing gap — every
operation involved (`re.concat`, `re.++`, `str.to_re`, `re.*`, `re.allchar`) is
faithfully translatable.
-/
public theorem cmd_step_re_concat_star_nullable1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_nullable1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_concat_star_nullable1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_nullable1 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_concat_star_nullable1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
  | cons a1 args =>
    cases args with
    | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
    | cons a2 args =>
      cases args with
      | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
      | cons a3 args =>
        cases args with
        | cons _ _ => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
        | nil =>
          cases premises with
          | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
          | cons n1 premises =>
            cases premises with
            | cons _ _ => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
            | nil =>
              -- Argument SMT-translations from the command translation side condition.
              have hTrans :
                  cArgListTranslationOk
                    (CArgList.cons a1 (CArgList.cons a2 (CArgList.cons a3 CArgList.nil))) :=
                hCmdTrans
              have hA1Trans : eoHasSmtTranslation a1 := hTrans.1
              have hA2Trans : eoHasSmtTranslation a2 := hTrans.2.1
              have hA3Trans : eoHasSmtTranslation a3 := hTrans.2.2.1
              -- The conclusion is `Bool`-typed.
              have hConclTy : __eo_typeof (mkConcl1 a1 a2 a3) = Term.Bool := by
                have hPNe :
                    __eo_prog_re_concat_star_nullable1 a1 a2 a3
                        (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck := hProg
                rw [← (prog_form a1 a2 a3 (__eo_state_proven_nth s n1) hPNe).2]
                exact hResultTy
              -- The conclusion is not stuck, hence its two operands are not stuck.
              have hConclNe : mkConcl1 a1 a2 a3 ≠ Term.Stuck :=
                term_ne_stuck_of_typeof_bool hConclTy
              have hRhsNe : rhs1 a1 a3 ≠ Term.Stuck := by
                intro h
                exact hConclNe (by
                  show __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs1 a1 a2 a3)) (rhs1 a1 a3)
                      = Term.Stuck
                  rw [h]; exact RuleProofs.mk_apply_right_stuck _)
              have hInnerNe :
                  __eo_mk_apply (Term.UOp UserOp.eq) (lhs1 a1 a2 a3) ≠ Term.Stuck := by
                intro h
                exact hConclNe (by
                  show __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs1 a1 a2 a3)) (rhs1 a1 a3)
                      = Term.Stuck
                  rw [h]; exact RuleProofs.mk_apply_left_stuck _)
              have hLhsNe : lhs1 a1 a2 a3 ≠ Term.Stuck := by
                intro h
                exact hInnerNe (by rw [h]; exact RuleProofs.mk_apply_right_stuck _)
              -- `mkConcl1` is literally an `eq` application of the two operands.
              have hConclForm :
                  mkConcl1 a1 a2 a3 =
                    Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs1 a1 a2 a3)) (rhs1 a1 a3) :=
                RuleProofs.mk_apply_eq_apply_eq_of_ne_stuck hLhsNe hRhsNe
              -- The list-concatenation `lhs1` is structurally well formed.
              have hReqOuter :
                  __eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) a1) (Term.Boolean true)
                    (__eo_requires
                      (__eo_is_list (Term.UOp UserOp.re_concat)
                        (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat a2 a3)))
                      (Term.Boolean true)
                      (__eo_list_concat_rec a1
                        (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat a2 a3)))) ≠
                    Term.Stuck := hLhsNe
              have hXsList := RuleProofs.eo_requires_arg_eq_of_ne_stuck hReqOuter
              have hReqInner := RuleProofs.eo_requires_eq_result_of_ne_stuck _ _ _ hReqOuter
              rw [hReqInner] at hReqOuter
              have hBList := RuleProofs.eo_requires_arg_eq_of_ne_stuck hReqOuter
              have hAB :=
                eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) RuleProofs.tSigma
                  (RuleProofs.tReConcat a2 a3) hBList
              have hYsList :=
                eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) a2 a3 hAB
              -- The type of `lhs1` is non-stuck, so the regex tail is non-stuck.
              have hLhsTyNe : __eo_typeof (lhs1 a1 a2 a3) ≠ Term.Stuck := by
                intro hS
                rw [hConclForm] at hConclTy
                change __eo_typeof_eq (__eo_typeof (lhs1 a1 a2 a3)) (__eo_typeof (rhs1 a1 a3)) =
                  Term.Bool at hConclTy
                rw [hS] at hConclTy
                simp [__eo_typeof_eq] at hConclTy
              have hLhsTyNe2 :
                  __eo_typeof
                      (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                        (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat a2 a3))) ≠
                    Term.Stuck := hLhsTyNe
              rw [RuleProofs.list_concat_reduce (Term.UOp UserOp.re_concat) a1 _ hXsList hBList]
                at hLhsTyNe2
              have hbTyNe :=
                RuleProofs.list_concat_rec_tail_typeof_ne_stuck a1 _ hXsList hLhsTyNe2
              -- Invert the regex tail to learn the regex arguments are `RegLan`-typed.
              have hbInv :=
                RuleProofs.eo_typeof_re_concat_term_args RuleProofs.tSigma
                  (RuleProofs.tReConcat a2 a3) hbTyNe
              have hInnerTyNe : __eo_typeof (RuleProofs.tReConcat a2 a3) ≠ Term.Stuck := by
                rw [hbInv.2]; decide
              have haInv :=
                RuleProofs.eo_typeof_re_concat_term_args a2 a3 hInnerTyNe
              -- Lift `RegLan` typing to the SMT side.
              have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
                have h := TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
                rw [haInv.1] at h; exact h
              have hA3SmtTy : __smtx_typeof (__eo_to_smt a3) = SmtType.RegLan := by
                have h := TranslationProofs.eo_to_smt_typeof_matches_translation a3 hA3Trans
                rw [haInv.2] at h; exact h
              have hAllcharTy :
                  __smtx_typeof (__eo_to_smt (Term.UOp UserOp.re_allchar)) = SmtType.RegLan := by
                change __smtx_typeof SmtTerm.re_allchar = SmtType.RegLan
                simp [__smtx_typeof]
              have hSigmaTy : __smtx_typeof (__eo_to_smt RuleProofs.tSigma) = SmtType.RegLan :=
                RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_of_reglan
                  (Term.UOp UserOp.re_allchar) hAllcharTy
              -- `RegLan` evaluations of the two regex arguments.
              obtain ⟨r1v, hR1⟩ :=
                RuleProofs.ReUnfoldNegSupport.smt_eval_reglan_of_smt_type_reglan M hM
                  (__eo_to_smt a2) hA2SmtTy
              obtain ⟨ys1v, hYs1⟩ :=
                RuleProofs.ReUnfoldNegSupport.smt_eval_reglan_of_smt_type_reglan M hM
                  (__eo_to_smt a3) hA3SmtTy
              -- `lhs1` evaluates to a regular language.
              have hInnerSmt :
                  __smtx_typeof (__eo_to_smt (RuleProofs.tReConcat a2 a3)) = SmtType.RegLan :=
                RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan a2 a3 hA2SmtTy hA3SmtTy
              have hBSmtTy :
                  __smtx_typeof
                      (__eo_to_smt
                        (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat a2 a3))) =
                    SmtType.RegLan :=
                RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan RuleProofs.tSigma
                  (RuleProofs.tReConcat a2 a3) hSigmaTy hInnerSmt
              have hLhsSmtTy :
                  __smtx_typeof (__eo_to_smt (lhs1 a1 a2 a3)) = SmtType.RegLan := by
                show __smtx_typeof
                    (__eo_to_smt
                      (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                        (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat a2 a3)))) =
                  SmtType.RegLan
                rw [RuleProofs.list_concat_reduce (Term.UOp UserOp.re_concat) a1 _ hXsList hBList]
                exact RuleProofs.reConcat_list_concat_rec_smt_typeof_reglan a1 _ hXsList hA1Trans
                  hBSmtTy
              have hLhsEval :
                  ∃ rr, __smtx_model_eval M (__eo_to_smt (lhs1 a1 a2 a3)) = SmtValue.RegLan rr :=
                RuleProofs.ReUnfoldNegSupport.smt_eval_reglan_of_smt_type_reglan M hM
                  (__eo_to_smt (lhs1 a1 a2 a3)) hLhsSmtTy
              -- `rhs1` is `RegLan`-typed (singleton elimination of a well-typed list).
              have hCpInnerList :
                  __eo_is_list (Term.UOp UserOp.re_concat) (RuleProofs.tReConcat RuleProofs.tSigma a3) =
                    Term.Boolean true :=
                eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) RuleProofs.tSigma
                  a3 (by simp) hYsList
              have hCList :
                  __eo_is_list (Term.UOp UserOp.re_concat)
                      (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                        (RuleProofs.tReConcat RuleProofs.tSigma a3)) =
                    Term.Boolean true := by
                rw [RuleProofs.list_concat_reduce (Term.UOp UserOp.re_concat) a1 _ hXsList
                    hCpInnerList]
                exact RuleProofs.list_concat_rec_is_list a1 _ hXsList hCpInnerList
              have hCpSmt :
                  __smtx_typeof (__eo_to_smt (RuleProofs.tReConcat RuleProofs.tSigma a3)) =
                    SmtType.RegLan :=
                RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan RuleProofs.tSigma a3
                  hSigmaTy hA3SmtTy
              have hCSmt :
                  __smtx_typeof
                      (__eo_to_smt
                        (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                          (RuleProofs.tReConcat RuleProofs.tSigma a3))) =
                    SmtType.RegLan := by
                rw [RuleProofs.list_concat_reduce (Term.UOp UserOp.re_concat) a1 _ hXsList
                    hCpInnerList]
                exact RuleProofs.reConcat_list_concat_rec_smt_typeof_reglan a1 _ hXsList hA1Trans
                  hCpSmt
              have hRhsSmtTy : __smtx_typeof (__eo_to_smt (rhs1 a1 a3)) = SmtType.RegLan := by
                show __smtx_typeof
                    (__eo_to_smt
                      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                        (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                          (RuleProofs.tReConcat RuleProofs.tSigma a3)))) =
                  SmtType.RegLan
                exact RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type _
                  hCList hCSmt
              have hbt :
                  RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs1 a1 a2 a3)) (rhs1 a1 a3)) :=
                RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs1 a1 a2 a3) (rhs1 a1 a3)
                  (by rw [hLhsSmtTy, hRhsSmtTy]) (by rw [hLhsSmtTy]; decide)
              -- Assemble the step properties.
              show StepRuleProperties M [__eo_state_proven_nth s n1]
                  (__eo_prog_re_concat_star_nullable1 a1 a2 a3
                    (Proof.pf (__eo_state_proven_nth s n1)))
              generalize hP1 : __eo_state_proven_nth s n1 = P1
              have hProgNe :
                  __eo_prog_re_concat_star_nullable1 a1 a2 a3 (Proof.pf P1) ≠ Term.Stuck := by
                rw [← hP1]; exact hProg
              obtain ⟨hf1, hProgEq⟩ := prog_form a1 a2 a3 P1 hProgNe
              rw [hProgEq, hConclForm]
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hbt⟩
              intro hEv
              have hPrem : eo_interprets M (mkStrInReEmpty a2) true := by
                have h := hEv.true_here P1 (by simp)
                rwa [hf1] at h
              have hNull : native_re_nullable r1v = true :=
                nullable_of_premise M a2 r1v hR1 hPrem
              have hRel := RuleProofs.nullable1_eval_rel M a1 a2 a3 r1v ys1v
                hXsList hYsList hR1 hYs1 hNull hLhsEval
              exact RuleProofs.eo_interprets_eq_of_rel M (lhs1 a1 a2 a3) (rhs1 a1 a3) hbt hRel
