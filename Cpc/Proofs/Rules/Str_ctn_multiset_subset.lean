module

public import Cpc.Proofs.RuleSupport.StrCtnMultisetSupport
import all Cpc.Proofs.RuleSupport.StrCtnMultisetSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_ctn_multiset_subset_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_ctn_multiset_subset args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_ctn_multiset_subset args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_ctn_multiset_subset args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_ctn_multiset_subset args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | cons _ _ => exact absurd rfl hProg
      | nil =>
          cases premises with
          | cons _ _ => exact absurd rfl hProg
          | nil =>
              change StepRuleProperties M [] (__eo_prog_str_ctn_multiset_subset a1)
              change __eo_prog_str_ctn_multiset_subset a1 ≠ Term.Stuck at hProg
              unfold __eo_prog_str_ctn_multiset_subset at hProg ⊢
              split at hProg
              · rename_i hay needle
                have hStrictMk :
                    __str_is_multiset_subset_strict
                        (__str_flatten (__str_nary_intro needle))
                        (__str_multiset_overapprox hay)
                        (__eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
                          (__eo_typeof hay)) =
                      Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hProg
                rw [RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hProg]
                have hEqBool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) hay)
                        needle))
                      (Term.Boolean false)) := by
                  have hc := hCmdTrans
                  simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                  unfold RuleProofs.eo_has_bool_type
                  exact Smtm.eq_term_typeof_of_non_none hc.1
                have hc := hCmdTrans
                simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                obtain ⟨hContainsTrans, _⟩ :=
                  RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation
                    _ _ hc.1
                obtain ⟨T, hHayTy, hNeedleTy⟩ :=
                  seq_binop_args_of_non_none_ret
                    (op := SmtTerm.str_contains) (typeof_str_contains_eq _ _)
                    hContainsTrans
                have hStrict :
                    __str_is_multiset_subset_strict
                        (__str_flatten (__str_nary_intro needle))
                        (__str_multiset_overapprox hay)
                        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
                          (__eo_typeof hay)) =
                      Term.Boolean true := by
                  have hTyNe : __eo_typeof hay ≠ Term.Stuck :=
                    RuleProofs.eo_typeof_ne_stuck_of_smt_seq_type hay T hHayTy
                  rw [← SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTyNe]
                  exact hStrictMk
                have hContainsFalse :
                    __smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_contains) hay)
                            needle)) =
                      SmtValue.Boolean false :=
                  RuleProofs.str_ctn_multiset_subset_contains_false M hM
                    hay needle T hHayTy hNeedleTy hStrict
                refine ⟨fun _ => ?_, ?_⟩
                · refine RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool ?_
                  rw [hContainsFalse]
                  rw [show __eo_to_smt (Term.Boolean false) =
                      SmtTerm.Boolean false by rfl,
                    __smtx_model_eval.eq_1]
                  exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
              all_goals exact absurd rfl hProg
