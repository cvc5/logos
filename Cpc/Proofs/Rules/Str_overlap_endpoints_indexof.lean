module

public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_overlap_endpoints_indexof_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_indexof args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises ≠ Term.Stuck :=
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
              change StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_indexof a1)
              change __eo_prog_str_overlap_endpoints_indexof a1 ≠ Term.Stuck at hProg
              unfold __eo_prog_str_overlap_endpoints_indexof at hProg ⊢
              split at hProg
              · rename_i sw c emp t d lvemp2 lvs2 lvt2 lvd2 lvemp3
                have hand := RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hProg
                obtain ⟨hand1234, hand5⟩ := RuleProofs.eo_and_true_split _ _ hand
                obtain ⟨hand123, hand4⟩ := RuleProofs.eo_and_true_split _ _ hand1234
                obtain ⟨hand12, hand3⟩ := RuleProofs.eo_and_true_split _ _ hand123
                obtain ⟨hand1, hand2⟩ := RuleProofs.eo_and_true_split _ _ hand12
                have e1 := RuleProofs.eq_of_eo_eq _ _ hand1
                have e2 := RuleProofs.eq_of_eo_eq _ _ hand2
                have e3 := RuleProofs.eq_of_eo_eq _ _ hand3
                have e4 := RuleProofs.eq_of_eo_eq _ _ hand4
                have e5 := RuleProofs.eq_of_eo_eq _ _ hand5
                subst lvemp2; subst lvs2; subst lvt2; subst lvd2; subst lvemp3
                have h1 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
                have h2 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h1
                have h3 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h2
                have hemp : __str_is_empty emp = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h1
                have hdLenZ : __eo_is_z (__str_value_len d) = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h2
                have hgt :
                    __eo_gt (__str_value_len c)
                        (__str_overlap_rec
                          (__eo_list_rev (Term.UOp UserOp.str_concat)
                            (__str_flatten (__str_nary_intro c)))
                          (__eo_list_rev (Term.UOp UserOp.str_concat)
                            (__str_flatten (__str_nary_intro d)))) =
                      Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h3
                rw [RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hProg,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h1,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h2,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h3]
                let needle :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp)
                let hay :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) emp)
                let lhs :=
                  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) hay)
                    needle) (Term.Numeral 0)
                let rhs :=
                  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) sw)
                    needle) (Term.Numeral 0)
                have hEqBool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
                  have hc := hCmdTrans
                  simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                  unfold RuleProofs.eo_has_bool_type
                  exact Smtm.eq_term_typeof_of_non_none hc.1
                have hc := hCmdTrans
                simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                obtain ⟨hLHStrans, _hRHStrans⟩ :=
                  RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation _ _ hc.1
                obtain ⟨T, hHayTy, hNeedleTy, _hZeroTy⟩ :=
                  str_indexof_args_of_non_none (by have hsimpa := hLHStrans; (try simp [lhs, hay, needle] at hsimpa ⊢); exact hsimpa)
                obtain ⟨hswty, hCEty⟩ := strConcat_args_of_seq_type sw
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) emp) T hHayTy
                obtain ⟨hcty, _hempty⟩ := strConcat_args_of_seq_type c emp T hCEty
                obtain ⟨htty, hDEty⟩ := strConcat_args_of_seq_type t
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d) emp) T hNeedleTy
                obtain ⟨hdty, _hempNeedleTy⟩ := strConcat_args_of_seq_type d emp T hDEty
                have evalSeq (x : Term)
                    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
                    ∃ Sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq Sx := by
                  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
                    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
                  exact seq_value_canonical hxValTy
                rcases evalSeq sw hswty with ⟨Ss, hSs⟩
                rcases evalSeq c hcty with ⟨Sc, hSc⟩
                rcases evalSeq emp _hempty with ⟨Se, hSe⟩
                rcases evalSeq t htty with ⟨St, hSt⟩
                rcases evalSeq d hdty with ⟨Sd, hSd⟩
                have hempnil : native_unpack_seq Se = [] :=
                  RuleProofs.str_is_empty_eval_unpack_nil M emp Se hemp hSe
                have hNoRight : ∀ k, k < (native_unpack_seq Sc).reverse.length →
                    ¬ RuleProofs.native_seq_compat
                      ((native_unpack_seq Sc).reverse.drop k)
                      (native_unpack_seq Sd).reverse := by
                  exact RuleProofs.no_compat_dispatch_endpoint_right M hM c d Sc Sd T
                    hcty hdty hSc hSd hdLenZ hgt
                refine ⟨fun _ => ?_, ?_⟩
                · refine RuleProofs.eo_interprets_eq_of_rel M lhs rhs hEqBool ?_
                  rw [RuleProofs.overlap_endpoints_indexof_eval M sw c emp t d
                    Ss Sc Se St Sd hSs hSc hSe hSt hSd hempnil hNoRight]
                  exact RuleProofs.smt_value_rel_refl _
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
              all_goals exact absurd rfl hProg
