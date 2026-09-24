module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace ReUnionInclusionProof

private abbrev mkReUnion (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) s

private abbrev mkReComp (r : Term) : Term :=
  Term.Apply (Term.UOp UserOp.re_comp) r

private abbrev body (r1 r2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (mkReUnion r1 (mkReUnion (mkReComp r2) (Term.UOp UserOp.re_none))))
    (Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar))

private theorem prog_form (a : Term)
    (hNe : __eo_prog_re_union_inclusion a ≠ Term.Stuck) :
    ∃ r1 r2 flat1 flat2 side,
      a = body r1 r2 ∧
        flat1 = __re_flatten (Term.Boolean true) r1 ∧
        flat2 = __re_flatten (Term.Boolean true) r2 ∧
        side =
          __eo_ite (__eo_eq flat1 flat2) (Term.Boolean true)
            (__str_re_includes_rec flat1 flat2) ∧
        side = Term.Boolean true ∧
        __eo_prog_re_union_inclusion a = body r1 r2 := by
  unfold __eo_prog_re_union_inclusion at hNe ⊢
  split at hNe
  · rename_i r1 r2 hEq
    let flat2 := __re_flatten (Term.Boolean true) hEq
    let flat1 := __re_flatten (Term.Boolean true) r2
    let side := __eo_ite (__eo_eq flat1 flat2) (Term.Boolean true)
      (__str_re_includes_rec flat1 flat2)
    let concl := body r2 hEq
    have hSide :
        side = Term.Boolean true :=
      eo_requires_eq_of_ne_stuck side (Term.Boolean true) concl hNe
    have hResult :
        __eo_requires side (Term.Boolean true) concl = concl :=
      eo_requires_eq_result_of_ne_stuck side (Term.Boolean true) concl hNe
    refine ⟨r2, hEq, flat1, flat2, side, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hSide
    · exact hResult
  · exact False.elim (hNe rfl)

private theorem facts
    (M : SmtModel) (hM : model_wf M)
    (r1 r2 flat1 flat2 side : Term)
    (hFlat1 :
      flat1 = __re_flatten (Term.Boolean true) r1)
    (hFlat2 :
      flat2 = __re_flatten (Term.Boolean true) r2)
    (hSide :
      side =
        __eo_ite (__eo_eq flat1 flat2) (Term.Boolean true)
          (__str_re_includes_rec flat1 flat2))
    (hSideTrue : side = Term.Boolean true)
    (hBool : RuleProofs.eo_has_bool_type (body r1 r2)) :
    eo_interprets M (body r1 r2) true := by
  let lhs := mkReUnion r1 (mkReUnion (mkReComp r2) (Term.UOp UserOp.re_none))
  let rhs := Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar)
  have hEqTy := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type lhs rhs
    (by simpa [body, lhs, rhs] using hBool)
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    native_decide
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan := by
    rw [hEqTy.1, hRhsTy]
  have hLhsNN :
      term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt r1)
          (SmtTerm.re_union (SmtTerm.re_comp (__eo_to_smt r2))
            SmtTerm.re_none)) := by
    unfold term_has_non_none_type
    rw [show __smtx_typeof
        (SmtTerm.re_union (__eo_to_smt r1)
          (SmtTerm.re_union (SmtTerm.re_comp (__eo_to_smt r2))
            SmtTerm.re_none)) = SmtType.RegLan by
      have hsimpa := hLhsTy; (try simp [lhs, mkReUnion, mkReComp] at hsimpa ⊢); exact hsimpa]
    simp
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt r1)
      (SmtTerm.re_union (SmtTerm.re_comp (__eo_to_smt r2)) SmtTerm.re_none))
    hLhsNN
  have hInnerNN :
      term_has_non_none_type
        (SmtTerm.re_union (SmtTerm.re_comp (__eo_to_smt r2))
          SmtTerm.re_none) := by
    unfold term_has_non_none_type
    rw [hArgs.2]
    simp
  have hInnerArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (SmtTerm.re_comp (__eo_to_smt r2)) SmtTerm.re_none)
    hInnerNN
  have hCompNN :
      term_has_non_none_type (SmtTerm.re_comp (__eo_to_smt r2)) := by
    unfold term_has_non_none_type
    rw [hInnerArgs.1]
    simp
  have hR2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_comp)
      (typeof_re_comp_eq (__eo_to_smt r2)) hCompNN
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM r1 hArgs.1 with
    ⟨rv1, hR1Eval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM r2 hR2Ty with
    ⟨rv2, hR2Eval⟩
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt lhs) =
        SmtValue.RegLan
          (native_re_union rv1
            (native_re_union (native_re_comp rv2) native_re_none)) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt r1)
          (SmtTerm.re_union (SmtTerm.re_comp (__eo_to_smt r2))
            SmtTerm.re_none)) =
      SmtValue.RegLan
        (native_re_union rv1
          (native_re_union (native_re_comp rv2) native_re_none))
    simp [__smtx_model_eval, __smtx_model_eval_re_union,
      __smtx_model_eval_re_comp, hR1Eval, hR2Eval]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.RegLan native_re_all := by
    change __smtx_model_eval M (SmtTerm.re_mult SmtTerm.re_allchar) =
      SmtValue.RegLan native_re_all
    simp [__smtx_model_eval, RuleProofs.smtx_model_eval_re_mult_allchar]
  have hSub : RuleProofs.NativeIncludes rv1 rv2 :=
    RuleProofs.re_inclusion_side_native_includes M hM r1 r2 flat1 flat2 side
      rv1 rv2 hArgs.1 hR2Ty hR1Eval hR2Eval hFlat1 hFlat2 hSide hSideTrue
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs
    (by simpa [body, lhs, rhs] using hBool) <| by
      rw [hLhsEval, hRhsEval]
      exact RuleProofs.smt_value_rel_re_union_subset_comp_none_all rv1 rv2 hSub

end ReUnionInclusionProof

public theorem cmd_step_re_union_inclusion_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_union_inclusion args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_union_inclusion args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_union_inclusion args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_union_inclusion args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M []
                (__eo_prog_re_union_inclusion a1)
              have hLocal : __eo_prog_re_union_inclusion a1 ≠ Term.Stuck := by
                have hsimpa := hProg
                try simp at hsimpa ⊢
                exact hsimpa
              rcases ReUnionInclusionProof.prog_form a1 hLocal with
                ⟨r1, r2, flat1, flat2, side, hA1Eq, hFlat1, hFlat2,
                  hSide, hSideTrue, hProgEq⟩
              have hBodyType :
                  __eo_typeof (ReUnionInclusionProof.body r1 r2) = Term.Bool := by
                change __eo_typeof (__eo_prog_re_union_inclusion a1) = Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hBodyTrans :
                  RuleProofs.eo_has_smt_translation
                    (ReUnionInclusionProof.body r1 r2) := by
                simpa [hA1Eq] using hA1Trans
              have hBodyBool :
                  RuleProofs.eo_has_bool_type
                    (ReUnionInclusionProof.body r1 r2) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (ReUnionInclusionProof.body r1 r2) hBodyTrans hBodyType
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                (by simpa [hProgEq] using hBodyBool)⟩
              intro _hTrue
              rw [hProgEq]
              exact ReUnionInclusionProof.facts M hM r1 r2 flat1 flat2 side
                hFlat1 hFlat2 hSide hSideTrue hBodyBool
