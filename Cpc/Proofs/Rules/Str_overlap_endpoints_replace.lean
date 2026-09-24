module

public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_str_overlap_endpoints_replace_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_replace args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_endpoints_replace args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_replace args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_endpoints_replace args premises ≠ Term.Stuck :=
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
              change StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_replace a1)
              change __eo_prog_str_overlap_endpoints_replace a1 ≠ Term.Stuck at hProg
              unfold __eo_prog_str_overlap_endpoints_replace at hProg ⊢
              split at hProg
              · rename_i c1 sw c2 emp d1 t d2 lvemp2 r lvc12 lvs2 lvd12 lvt2
                  lvd22 lvemp3 lvr2 lvc22 lvemp4
                have hand := RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hProg
                obtain ⟨hand123456789, hand10⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand
                obtain ⟨hand12345678, hand9⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand123456789
                obtain ⟨hand1234567, hand8⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand12345678
                obtain ⟨hand123456, hand7⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand1234567
                obtain ⟨hand12345, hand6⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand123456
                obtain ⟨hand1234, hand5⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand12345
                obtain ⟨hand123, hand4⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand1234
                obtain ⟨hand12, hand3⟩ :=
                  RuleProofs.eo_and_true_split _ _ hand123
                obtain ⟨hand1, hand2⟩ := RuleProofs.eo_and_true_split _ _ hand12
                have e1 := RuleProofs.eq_of_eo_eq _ _ hand1
                have e2 := RuleProofs.eq_of_eo_eq _ _ hand2
                have e3 := RuleProofs.eq_of_eo_eq _ _ hand3
                have e4 := RuleProofs.eq_of_eo_eq _ _ hand4
                have e5 := RuleProofs.eq_of_eo_eq _ _ hand5
                have e6 := RuleProofs.eq_of_eo_eq _ _ hand6
                have e7 := RuleProofs.eq_of_eo_eq _ _ hand7
                have e8 := RuleProofs.eq_of_eo_eq _ _ hand8
                have e9 := RuleProofs.eq_of_eo_eq _ _ hand9
                have e10 := RuleProofs.eq_of_eo_eq _ _ hand10
                subst lvemp2; subst lvc12; subst lvs2; subst lvd12; subst lvt2
                subst lvd22; subst lvemp3; subst lvr2; subst lvc22; subst lvemp4
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
                let c2emp :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp
                let swc2emp :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) c2emp
                let hay :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1) swc2emp
                let d2emp :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp
                let td2emp :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) d2emp
                let needle :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1) td2emp
                let replSw :=
                  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) sw)
                    needle) r
                let rhsTail :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) replSw) c2emp
                let lhs :=
                  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) hay)
                    needle) r
                let rhs :=
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1) rhsTail
                have hEqBool : RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
                  have hc := hCmdTrans
                  simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                  unfold RuleProofs.eo_has_bool_type
                  exact Smtm.eq_term_typeof_of_non_none hc.1
                have hc := hCmdTrans
                simp only [cmdTranslationOk, cArgListTranslationOk] at hc
                obtain ⟨hLHStrans, _hRHStrans⟩ :=
                  RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation
                    lhs rhs hc.1
                obtain ⟨T, hHayTy, hNeedleTy, hrTy⟩ :=
                  seq_triop_args_of_non_none (op := SmtTerm.str_replace)
                    (typeof_str_replace_eq (__eo_to_smt hay) (__eo_to_smt needle)
                      (__eo_to_smt r))
                    (by have hsimpa := hLHStrans; (try simp [lhs, hay, needle] at hsimpa ⊢); exact hsimpa)
                obtain ⟨hc1ty, hSWC2Ety⟩ := strConcat_args_of_seq_type c1
                  swc2emp T (by simpa [hay] using hHayTy)
                obtain ⟨hswty, hC2Ety⟩ := strConcat_args_of_seq_type sw
                  c2emp T (by simpa [swc2emp] using hSWC2Ety)
                obtain ⟨hc2ty, hempty⟩ := strConcat_args_of_seq_type c2 emp T
                  (by simpa [c2emp] using hC2Ety)
                obtain ⟨hd1ty, hTD2Ety⟩ := strConcat_args_of_seq_type d1
                  td2emp T (by simpa [needle] using hNeedleTy)
                obtain ⟨htty, hD2Ety⟩ := strConcat_args_of_seq_type t d2emp T
                  (by simpa [td2emp] using hTD2Ety)
                obtain ⟨hd2ty, _hempNeedleTy⟩ := strConcat_args_of_seq_type d2 emp T
                  (by simpa [d2emp] using hD2Ety)
                have evalSeq (x : Term)
                    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
                    ∃ Sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq Sx := by
                  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
                    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
                  exact seq_value_canonical hxValTy
                rcases evalSeq c1 hc1ty with ⟨Sc1, hSc1⟩
                rcases evalSeq sw hswty with ⟨Ss, hSs⟩
                rcases evalSeq c2 hc2ty with ⟨Sc2, hSc2⟩
                rcases evalSeq emp hempty with ⟨Se, hSe⟩
                rcases evalSeq d1 hd1ty with ⟨Sd1, hSd1⟩
                rcases evalSeq t htty with ⟨St, hSt⟩
                rcases evalSeq d2 hd2ty with ⟨Sd2, hSd2⟩
                rcases evalSeq r hrTy with ⟨Sr, hSr⟩
                have hempnil : native_unpack_seq Se = [] :=
                  RuleProofs.str_is_empty_eval_unpack_nil M emp Se hemp hSe
                have hSc1Ty : __smtx_typeof_seq_value Sc1 = SmtType.Seq T := by
                  have hValTy := smt_model_eval_preserves_type M hM (__eo_to_smt c1)
                    (SmtType.Seq T) hc1ty (seq_ne_none T) (type_inhabited_seq T)
                  rw [hSc1] at hValTy
                  simpa [__smtx_typeof_value] using hValTy
                have hSsTy : __smtx_typeof_seq_value Ss = SmtType.Seq T := by
                  have hValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sw)
                    (SmtType.Seq T) hswty (seq_ne_none T) (type_inhabited_seq T)
                  rw [hSs] at hValTy
                  simpa [__smtx_typeof_value] using hValTy
                have hSc1Elem : __smtx_elem_typeof_seq_value Sc1 = T :=
                  elem_typeof_seq_value_of_typeof_seq_value hSc1Ty
                have hSsElem : __smtx_elem_typeof_seq_value Ss = T :=
                  elem_typeof_seq_value_of_typeof_seq_value hSsTy
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
                · refine RuleProofs.eo_interprets_eq_of_rel M lhs rhs hEqBool ?_
                  rw [RuleProofs.overlap_endpoints_replace_eval M c1 sw c2 emp d1 t d2 r
                    Sc1 Ss Sc2 Se Sd1 St Sd2 Sr T hSc1 hSs hSc2 hSe hSd1 hSt hSd2
                    hSr hempnil hSc1Elem hSsElem hNoLeft hNoRight]
                  exact RuleProofs.smt_value_rel_refl _
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
              all_goals exact absurd rfl hProg
