module

public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_overlap_endpoints_ctn_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises ≠ Term.Stuck :=
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
              change StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_ctn a1)
              change __eo_prog_str_overlap_endpoints_ctn a1 ≠ Term.Stuck at hProg
              unfold __eo_prog_str_overlap_endpoints_ctn at hProg ⊢
              split at hProg
              · rename_i c1 sw c2 emp d1 t d2 lvemp2 lvs2 lvd12 lvt2 lvd22 lvemp3
                have hand := RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hProg
                obtain ⟨hand12345, hand6⟩ := RuleProofs.eo_and_true_split _ _ hand
                obtain ⟨hand1234, hand5⟩ := RuleProofs.eo_and_true_split _ _ hand12345
                obtain ⟨hand123, hand4⟩ := RuleProofs.eo_and_true_split _ _ hand1234
                obtain ⟨hand12, hand3⟩ := RuleProofs.eo_and_true_split _ _ hand123
                obtain ⟨hand1, hand2⟩ := RuleProofs.eo_and_true_split _ _ hand12
                have e1 := RuleProofs.eq_of_eo_eq _ _ hand1
                have e2 := RuleProofs.eq_of_eo_eq _ _ hand2
                have e3 := RuleProofs.eq_of_eo_eq _ _ hand3
                have e4 := RuleProofs.eq_of_eo_eq _ _ hand4
                have e5 := RuleProofs.eq_of_eo_eq _ _ hand5
                have e6 := RuleProofs.eq_of_eo_eq _ _ hand6
                subst lvemp2; subst lvs2; subst lvd12; subst lvt2
                subst lvd22; subst lvemp3
                have h1 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
                have h2 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h1
                have h3 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h2
                have h4 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h3
                have h5 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h4
                have hemp : __str_is_empty emp = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h1
                have hd1LenZ : __eo_is_z (__str_value_len d1) = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h2
                have hd2LenZ : __eo_is_z (__str_value_len d2) = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h3
                have hgt1 :
                    __eo_gt (__str_value_len c1)
                        (__str_overlap_rec (__str_flatten (__str_nary_intro c1))
                          (__str_flatten (__str_nary_intro d1))) = Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h4
                have hgt2 :
                    __eo_gt (__str_value_len c2)
                        (__str_overlap_rec
                          (__eo_list_rev (Term.UOp UserOp.str_concat)
                            (__str_flatten (__str_nary_intro c2)))
                          (__eo_list_rev (Term.UOp UserOp.str_concat)
                            (__str_flatten (__str_nary_intro d2)))) =
                      Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h5
                rw [RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hProg,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h1,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h2,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h3,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h4,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h5]
                have hEqBool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) sw)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) := by
                  have hc := hCmdTrans
                  simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                  unfold RuleProofs.eo_has_bool_type
                  exact Smtm.eq_term_typeof_of_non_none hc.1
                have hc := hCmdTrans
                simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                obtain ⟨hLHStrans, _hRHStrans⟩ :=
                  RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation _ _ hc.1
                obtain ⟨T, hHayTy, hNeedleTy⟩ := seq_binop_args_of_non_none_ret
                  (op := SmtTerm.str_contains) (typeof_str_contains_eq _ _) hLHStrans
                obtain ⟨hc1ty, hSC2Ety⟩ := strConcat_args_of_seq_type c1
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp)) T hHayTy
                obtain ⟨hswty, hC2Ety⟩ := strConcat_args_of_seq_type sw
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp) T hSC2Ety
                obtain ⟨hc2ty, _hempty⟩ := strConcat_args_of_seq_type c2 emp T hC2Ety
                obtain ⟨hd1ty, hTD2Ety⟩ := strConcat_args_of_seq_type d1
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)) T hNeedleTy
                obtain ⟨htty, hD2Ety⟩ := strConcat_args_of_seq_type t
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp) T hTD2Ety
                obtain ⟨hd2ty, _hempNeedleTy⟩ := strConcat_args_of_seq_type d2 emp T hD2Ety
                have hLHSbool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))) := by
                  unfold RuleProofs.eo_has_bool_type
                  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))) =
                      SmtTerm.str_contains
                        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))) from rfl,
                    typeof_str_contains_eq, hHayTy, hNeedleTy]
                  simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
                obtain ⟨bL, hbL⟩ := RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM _ hLHSbool
                obtain ⟨⟨SHay, hSHay⟩, ⟨SNeedle, hSNeedle⟩⟩ :=
                  RuleProofs.contains_args_seq_of_eval_bool M
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp)))
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))
                    bL hbL
                obtain ⟨⟨Sc1, hSc1⟩, hrHay1⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M c1
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))
                    ⟨SHay, hSHay⟩
                obtain ⟨⟨Ss, hSs⟩, hrHay2⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M sw
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp)
                    hrHay1
                obtain ⟨⟨Sc2, hSc2⟩, ⟨Se, hSe⟩⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M c2 emp hrHay2
                obtain ⟨⟨Sd1, hSd1⟩, hrNeedle1⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M d1
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))
                    ⟨SNeedle, hSNeedle⟩
                obtain ⟨⟨St, hSt⟩, hrNeedle2⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M t
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)
                    hrNeedle1
                obtain ⟨⟨Sd2, hSd2⟩, _hEmpNeedle⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M d2 emp hrNeedle2
                have hempnil : native_unpack_seq Se = [] :=
                  RuleProofs.str_is_empty_eval_unpack_nil M emp Se hemp hSe
                have hNoLeft : ∀ k, k < (native_unpack_seq Sc1).length →
                    ¬ RuleProofs.native_seq_compat ((native_unpack_seq Sc1).drop k)
                      (native_unpack_seq Sd1) := by
                  exact RuleProofs.no_compat_dispatch_endpoint_left M hM c1 d1 Sc1 Sd1 T
                    hc1ty hd1ty hSc1 hSd1 hd1LenZ hgt1
                have hNoRight : ∀ k, k < (native_unpack_seq Sc2).reverse.length →
                    ¬ RuleProofs.native_seq_compat
                      ((native_unpack_seq Sc2).reverse.drop k)
                      (native_unpack_seq Sd2).reverse := by
                  exact RuleProofs.no_compat_dispatch_endpoint_right M hM c2 d2 Sc2 Sd2 T
                    hc2ty hd2ty hSc2 hSd2 hd2LenZ hgt2
                refine ⟨fun _ => ?_, ?_⟩
                · refine RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool ?_
                  rw [RuleProofs.overlap_endpoints_contains_eval M c1 sw c2 emp d1 t d2
                    Sc1 Ss Sc2 Se Sd1 St Sd2 hSc1 hSs hSc2 hSe hSd1 hSt hSd2
                    hempnil hNoLeft hNoRight]
                  exact RuleProofs.smt_value_rel_refl _
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
              all_goals exact absurd rfl hProg
