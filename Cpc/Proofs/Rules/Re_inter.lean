module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkStrInRe (s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r

private abbrev mkReInter (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) s

private theorem re_inter_nonstuck_shape (p1 p2 : Term) :
    __eo_prog_re_inter (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck ->
    ∃ x r t,
      p1 = mkStrInRe x r ∧
      p2 = mkStrInRe x t ∧
      __eo_prog_re_inter (Proof.pf p1) (Proof.pf p2) =
        mkStrInRe x (mkReInter r (mkReInter t (Term.UOp UserOp.re_all))) := by
  intro h
  cases p1 with
  | Apply f1 r =>
      cases f1 with
      | Apply op1 x =>
          cases op1 with
          | UOp u1 =>
              cases u1 <;> try (simp [__eo_prog_re_inter] at h)
              case str_in_re =>
                cases p2 with
                | Apply f2 t =>
                    cases f2 with
                    | Apply op2 y =>
                        cases op2 with
                        | UOp u2 =>
                            cases u2 <;> try (simp at h)
                            case str_in_re =>
                              have hyx : y = x :=
                                RuleProofs.eq_of_requires_eq_true_not_stuck x y
                                  (mkStrInRe x
                                    (mkReInter r (mkReInter t (Term.UOp UserOp.re_all))))
                                  (by
                                    simpa [mkStrInRe, mkReInter, __eo_prog_re_inter]
                                      using h)
                              subst y
                              refine ⟨x, r, t, rfl, rfl, ?_⟩
                              cases x <;>
                                simp [mkStrInRe, mkReInter, __eo_prog_re_inter,
                                  __eo_requires, __eo_eq, native_ite, native_teq,
                                  native_not, SmtEval.native_not] at h ⊢
                        | _ => simp at h
                    | _ => simp at h
                | _ => simp at h
          | _ => simp [__eo_prog_re_inter] at h
      | _ => simp [__eo_prog_re_inter] at h
  | _ => simp [__eo_prog_re_inter] at h

private theorem re_inter_result_has_bool_type_of_premises_bool
    (x r t : Term) :
    RuleProofs.eo_has_bool_type (mkStrInRe x r) ->
    RuleProofs.eo_has_bool_type (mkStrInRe x t) ->
    RuleProofs.eo_has_bool_type
      (mkStrInRe x (mkReInter r (mkReInter t (Term.UOp UserOp.re_all)))) := by
  intro hXR hXT
  unfold RuleProofs.eo_has_bool_type at hXR hXT ⊢
  change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt r)) =
    SmtType.Bool at hXR
  change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt t)) =
    SmtType.Bool at hXT
  have hNNXR :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    rw [hXR]
    simp
  have hNNXT :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    rw [hXT]
    simp
  have hArgsXR := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re)
    (typeof_str_in_re_eq (__eo_to_smt x) (__eo_to_smt r)) hNNXR
  have hArgsXT := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re)
    (typeof_str_in_re_eq (__eo_to_smt x) (__eo_to_smt t)) hNNXT
  change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt x)
        (SmtTerm.re_inter (__eo_to_smt r)
          (SmtTerm.re_inter (__eo_to_smt t) SmtTerm.re_all))) = SmtType.Bool
  rw [typeof_str_in_re_eq, typeof_re_inter_eq, typeof_re_inter_eq]
  simp [hArgsXR.1, hArgsXR.2, hArgsXT.2, __smtx_typeof.eq_106,
    native_ite, native_Teq]

private theorem facts_re_inter
    (M : SmtModel) (x r t : Term)
    (hXRBool : RuleProofs.eo_has_bool_type (mkStrInRe x r))
    (hXTBool : RuleProofs.eo_has_bool_type (mkStrInRe x t))
    (hXRTrue : eo_interprets M (mkStrInRe x r) true)
    (hXTTrue : eo_interprets M (mkStrInRe x t) true) :
    eo_interprets M
      (mkStrInRe x (mkReInter r (mkReInter t (Term.UOp UserOp.re_all)))) true := by
  have hBool := re_inter_result_has_bool_type_of_premises_bool x r t hXRBool hXTBool
  apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hXRTrue hXTTrue
  cases hXRTrue with
  | intro_true _ hEvalXR =>
      cases hXTTrue with
      | intro_true _ hEvalXT =>
          change __smtx_model_eval M
              (SmtTerm.str_in_re (__eo_to_smt x)
                (SmtTerm.re_inter (__eo_to_smt r)
                  (SmtTerm.re_inter (__eo_to_smt t) SmtTerm.re_all))) =
            SmtValue.Boolean true
          rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_115,
            __smtx_model_eval.eq_115, __smtx_model_eval.eq_106]
          change __smtx_model_eval M
              (SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt r)) =
            SmtValue.Boolean true at hEvalXR
          change __smtx_model_eval M
              (SmtTerm.str_in_re (__eo_to_smt x) (__eo_to_smt t)) =
            SmtValue.Boolean true at hEvalXT
          rw [__smtx_model_eval.eq_119] at hEvalXR hEvalXT
          cases hx : __smtx_model_eval M (__eo_to_smt x) with
          | Seq ss =>
              cases hr : __smtx_model_eval M (__eo_to_smt r) with
              | RegLan rr =>
                  simp [hx, hr, __smtx_model_eval_str_in_re] at hEvalXR
                  cases ht : __smtx_model_eval M (__eo_to_smt t) with
                  | RegLan rt =>
                      simp [hx, ht, __smtx_model_eval_str_in_re] at hEvalXT
                      have hSSValid :
                          native_re_str_valid (native_unpack_seq ss) = true :=
                        RuleProofs.native_re_str_valid_of_model_str_in_re_true
                          hEvalXR
                      have hAll :
                          Smtm.native_str_in_re (native_unpack_seq ss)
                              native_re_all = true :=
                        RuleProofs.model_str_in_re_re_all _ hSSValid
                      simp [__smtx_model_eval_re_inter,
                        __smtx_model_eval_str_in_re,
                        RuleProofs.model_str_in_re_re_inter,
                        hEvalXR, hEvalXT, hAll]
                  | _ =>
                      simp [hx, ht, __smtx_model_eval_str_in_re] at hEvalXT
              | _ =>
                  simp [hx, hr, __smtx_model_eval_str_in_re] at hEvalXR
          | _ =>
              cases hr : __smtx_model_eval M (__eo_to_smt r) <;>
                simp [hx, hr, __smtx_model_eval_str_in_re] at hEvalXR

public theorem cmd_step_re_inter_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_inter args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_inter args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n2 premises =>
              cases premises with
              | nil =>
                  let p1 := __eo_state_proven_nth s n1
                  let p2 := __eo_state_proven_nth s n2
                  change StepRuleProperties M [p1, p2]
                    (__eo_prog_re_inter (Proof.pf p1) (Proof.pf p2))
                  have hProgLocal :
                      __eo_prog_re_inter (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck := by
                    change __eo_prog_re_inter (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck at hProg
                    exact hProg
                  rcases re_inter_nonstuck_shape p1 p2 hProgLocal with
                    ⟨x, r, t, hp1, hp2, hProgEq⟩
                  have hp1Bool : RuleProofs.eo_has_bool_type (mkStrInRe x r) := by
                    have h := hPremisesBool p1 (by simp [premiseTermList, p1])
                    simpa [hp1] using h
                  have hp2Bool : RuleProofs.eo_has_bool_type (mkStrInRe x t) := by
                    have h := hPremisesBool p2 (by simp [premiseTermList, p2])
                    simpa [hp2] using h
                  have hResultBool :
                      RuleProofs.eo_has_bool_type
                        (mkStrInRe x
                          (mkReInter r (mkReInter t (Term.UOp UserOp.re_all)))) :=
                    re_inter_result_has_bool_type_of_premises_bool x r t hp1Bool hp2Bool
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hp1True : eo_interprets M (mkStrInRe x r) true := by
                      have h := hTrue p1 (by simp [p1, p2])
                      simpa [hp1] using h
                    have hp2True : eo_interprets M (mkStrInRe x t) true := by
                      have h := hTrue p2 (by simp [p1, p2])
                      simpa [hp2] using h
                    simpa [hProgEq] using
                      facts_re_inter M x r t hp1Bool hp2Bool hp1True hp2True
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (by simpa [hProgEq] using hResultBool)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
