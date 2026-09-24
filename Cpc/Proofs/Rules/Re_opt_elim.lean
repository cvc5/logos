module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_re_mult_eq_reglan_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ =>
      simp [__eo_typeof_re_mult] at h

private theorem native_str_in_re_re_union_local
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  rw [← RuleProofs.native_str_in_re_eq_model str (native_re_union r s),
    ← RuleProofs.native_str_in_re_eq_model str r,
    ← RuleProofs.native_str_in_re_eq_model str s]
  by_cases hValid : native_string_valid str = true
  · simpa [native_re_union, RuleProofs.native_str_in_re, hValid, native_re_mk_union]
      using RuleProofs.nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid]

private theorem native_str_in_re_re_none_local (str : native_String) :
    native_str_in_re str native_re_none = false := by
  rw [← RuleProofs.native_str_in_re_eq_model str native_re_none]
  by_cases hValid : native_string_valid str = true
  · simpa [RuleProofs.native_str_in_re, hValid, native_re_none]
      using RuleProofs.nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid]

private theorem smt_value_rel_re_opt_elim (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_opt (SmtValue.RegLan r))
      (__smtx_model_eval_re_union
        (__smtx_model_eval_str_to_re (SmtValue.Seq (SmtSeq.empty SmtType.Char)))
        (__smtx_model_eval_re_union (SmtValue.RegLan r)
          (SmtValue.RegLan native_re_none))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_union r (native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))))
        (native_re_union
          (native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char)))
          (native_re_union r native_re_none))) =
    SmtValue.Boolean true
  let eps := native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))
  have hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str (native_re_union r eps) =
            native_str_in_re str (native_re_union eps (native_re_union r native_re_none)) := by
    intro str _hValid
    rw [native_str_in_re_re_union_local, native_str_in_re_re_union_local,
      native_str_in_re_re_union_local, native_str_in_re_re_none_local]
    cases native_str_in_re str r <;> cases native_str_in_re str eps <;> rfl
  simpa [eps, hExt]

private theorem typed___eo_prog_re_opt_elim_impl
    (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
    RuleProofs.eo_has_bool_type (__eo_prog_re_opt_elim a1) := by
  let eps := Term.Apply Term.str_to_re (Term.String [])
  let rhs := Term.Apply (Term.Apply Term.re_union eps)
    (Term.Apply (Term.Apply Term.re_union a1) Term.re_none)
  let lhs := Term.Apply Term.re_opt a1
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hEpsTy : __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) = SmtType.RegLan
    rw [typeof_str_to_re_eq, __smtx_typeof.eq_4]
    native_decide
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_union a1) Term.re_none)) =
        SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_union (__eo_to_smt a1) SmtTerm.re_none) =
      SmtType.RegLan
    rw [typeof_re_union_eq]
    simp [hA1SmtTy, __smtx_typeof.eq_105, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_union (__eo_to_smt eps)
          (__eo_to_smt (Term.Apply (Term.Apply Term.re_union a1) Term.re_none))) =
      SmtType.RegLan
    -- rewrite with the component types *before* `simp` normalises
    -- `__eo_to_smt (Apply ..)` into the `SmtTerm` spine, after which
    -- `hInnerTy`'s left-hand side no longer occurs.
    rw [typeof_re_union_eq, hEpsTy, hInnerTy]
    simp [native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_opt (__eo_to_smt a1)) = SmtType.RegLan
    rw [typeof_re_opt_eq]
    simp [hA1SmtTy, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hProg : __eo_prog_re_opt_elim a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    cases a1 <;> simp [__eo_prog_re_opt_elim, lhs, rhs, eps] at hA1NotStuck ⊢
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_opt_elim_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
    eo_interprets M (__eo_prog_re_opt_elim a1) true := by
  let eps := Term.Apply Term.str_to_re (Term.String [])
  let rhs := Term.Apply (Term.Apply Term.re_union eps)
    (Term.Apply (Term.Apply Term.re_union a1) Term.re_none)
  let lhs := Term.Apply Term.re_opt a1
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hProg : __eo_prog_re_opt_elim a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    cases a1 <;> simp [__eo_prog_re_opt_elim, lhs, rhs, eps] at hA1NotStuck ⊢
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    rw [← hProg]
    exact typed___eo_prog_re_opt_elim_impl a1 hA1Trans hA1Ty
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) = SmtType.RegLan := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1) (by
        unfold term_has_non_none_type
        rw [hA1SmtTy]
        simp)
  have hA1EvalShape :
      ∃ r : SmtRegLan, __smtx_model_eval M (__eo_to_smt a1) = SmtValue.RegLan r := by
    exact reglan_value_canonical hA1EvalTy
  rcases hA1EvalShape with ⟨r, hEval⟩
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.re_opt (__eo_to_smt a1)))
      (__smtx_model_eval M
        (SmtTerm.re_union (SmtTerm.str_to_re (SmtTerm.String []))
          (SmtTerm.re_union (__eo_to_smt a1) SmtTerm.re_none)))
    simp [__smtx_model_eval, hEval]
    exact smt_value_rel_re_opt_elim r

public theorem cmd_step_re_opt_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_opt_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_opt_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_opt_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_opt_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              have hA1NotStuck : a1 ≠ Term.Stuck := by
                intro hStuck
                subst a1
                apply hProg
                rfl
              let eps := Term.Apply Term.str_to_re (Term.String [])
              let rhs := Term.Apply (Term.Apply Term.re_union eps)
                (Term.Apply (Term.Apply Term.re_union a1) Term.re_none)
              let lhs := Term.Apply Term.re_opt a1
              have hProgEq :
                  __eo_cmd_step_proven s CRule.re_opt_elim
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq lhs) rhs := by
                have hProgEqRaw :
                    __eo_cmd_step_proven s CRule.re_opt_elim
                        (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                      Term.Apply
                        (Term.Apply Term.eq (Term.Apply Term.re_opt a1))
                        (Term.Apply
                          (Term.Apply Term.re_union
                            (Term.Apply Term.str_to_re (Term.String [])))
                          (Term.Apply
                            (Term.Apply Term.re_union a1) Term.re_none)) := by
                  cases hA1 : a1 <;> first | exact False.elim (hA1NotStuck hA1) | rfl
                simpa [lhs, rhs, eps] using hProgEqRaw
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) = Term.Bool at hResultTy
              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
              have hA1Ty : __eo_typeof a1 = Term.RegLan := by
                change __eo_typeof_re_mult (__eo_typeof a1) ≠ Term.Stuck at hLhsNotStuck
                exact eo_typeof_re_mult_eq_reglan_of_ne_stuck (__eo_typeof a1) hLhsNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_re_opt_elim a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_re_opt_elim_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_re_opt_elim_impl M hM a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_re_opt_elim a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
