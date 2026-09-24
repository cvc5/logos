module

public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_overlap_split_ctn_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_split_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises ≠ Term.Stuck :=
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
              change StepRuleProperties M [] (__eo_prog_str_overlap_split_ctn a1)
              change __eo_prog_str_overlap_split_ctn a1 ≠ Term.Stuck at hProg
              unfold __eo_prog_str_overlap_split_ctn at hProg ⊢
              split at hProg
              · rename_i t c sw emp d lvt2 lvd2 lvs2 lvd3
                have hand := RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hProg
                obtain ⟨hand123, hand4⟩ := RuleProofs.eo_and_true_split _ _ hand
                obtain ⟨hand12, hand3⟩ := RuleProofs.eo_and_true_split _ _ hand123
                obtain ⟨hand1, hand2⟩ := RuleProofs.eo_and_true_split _ _ hand12
                have e1 := RuleProofs.eq_of_eo_eq _ _ hand1
                have e2 := RuleProofs.eq_of_eo_eq _ _ hand2
                have e3 := RuleProofs.eq_of_eo_eq _ _ hand3
                have e4 := RuleProofs.eq_of_eo_eq _ _ hand4
                subst lvt2; subst lvd2; subst lvs2; subst lvd3
                have h1 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
                have h2 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h1
                have h3 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h2
                have hemp : __str_is_empty emp = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h1
                have hgt1 :
                    __eo_gt (__str_value_len c)
                        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
                          (__str_flatten (__str_nary_intro d))) = Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h2
                have hgt2 :
                    __eo_gt (__str_value_len d)
                        (__str_overlap_rec (__str_flatten (__str_nary_intro d))
                          (__str_flatten (__str_nary_intro c))) = Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h3
                rw [RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hProg,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h1,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h2,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h3]
                -- goal: StepRuleProperties M [] (eq (contains (t·c·sw·emp) d) (or (contains t d) (or (contains sw d) false)))
                have hEqBool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)))) d))
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) t) d))
                        (Term.Apply (Term.Apply (Term.UOp UserOp.or)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) sw) d))
                          (Term.Boolean false)))) := by
                  have hc := hCmdTrans
                  simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                  unfold RuleProofs.eo_has_bool_type
                  exact Smtm.eq_term_typeof_of_non_none hc.1
                have hc := hCmdTrans
                simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                obtain ⟨hLHStrans, hRHStrans⟩ :=
                  RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation _ _ hc.1
                obtain ⟨T, hBCty, hdty⟩ := seq_binop_args_of_non_none_ret
                  (op := SmtTerm.str_contains) (typeof_str_contains_eq _ _) hLHStrans
                obtain ⟨_htty, hCSEty⟩ := strConcat_args_of_seq_type t
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)) T hBCty
                obtain ⟨hcty, _hSEty⟩ := strConcat_args_of_seq_type c
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp) T hCSEty
                have hLHSbool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)))) d) := by
                  unfold RuleProofs.eo_has_bool_type
                  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)))) d) =
                      SmtTerm.str_contains
                        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp))))
                        (__eo_to_smt d) from rfl,
                    typeof_str_contains_eq, hBCty, hdty]
                  simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
                obtain ⟨bL, hbL⟩ := RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM _ hLHSbool
                obtain ⟨⟨SBC, hSBC⟩, ⟨Sd, hSd⟩⟩ := RuleProofs.contains_args_seq_of_eval_bool M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp))) d bL hbL
                obtain ⟨⟨St, hSt⟩, hr1⟩ := strConcat_args_eval_seq_of_concat_eval_seq M t
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)) ⟨SBC, hSBC⟩
                obtain ⟨⟨Sc, hSc⟩, hr2⟩ := strConcat_args_eval_seq_of_concat_eval_seq M c
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp) hr1
                obtain ⟨⟨Ss, hSs⟩, ⟨Se, hSe⟩⟩ :=
                  strConcat_args_eval_seq_of_concat_eval_seq M sw emp hr2
                have hempnil : native_unpack_seq Se = [] :=
                  RuleProofs.str_is_empty_eval_unpack_nil M emp Se hemp hSe
                have hA : ∀ k, k < (native_unpack_seq Sc).length →
                    ¬ RuleProofs.native_seq_compat ((native_unpack_seq Sc).drop k)
                      (native_unpack_seq Sd) :=
                  RuleProofs.no_compat_dispatch M hM c d Sc Sd T hcty hdty hSc hSd hgt1 hgt2
                have hB : ∀ k, k < (native_unpack_seq Sd).length →
                    ¬ RuleProofs.native_seq_compat ((native_unpack_seq Sd).drop k)
                      (native_unpack_seq Sc) :=
                  RuleProofs.no_compat_dispatch M hM d c Sd Sc T hdty hcty hSd hSc hgt2 hgt1
                refine ⟨fun _ => ?_, ?_⟩
                · refine RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool ?_
                  rw [RuleProofs.overlap_split_eval M t c sw emp d St Sc Ss Se Sd
                    hSt hSc hSs hSe hSd hempnil hA hB]
                  exact RuleProofs.smt_value_rel_refl _
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
              all_goals exact absurd rfl hProg
