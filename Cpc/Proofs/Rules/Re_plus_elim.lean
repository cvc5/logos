module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem native_string_lit_empty :
    native_string_lit "" = ([] : native_String) := by
  simp [native_string_lit]

private theorem eo_typeof_re_mult_eq_reglan_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ =>
      simp [__eo_typeof_re_mult] at h

private theorem smtx_model_eval_re_plus_elim
    (v : SmtValue) :
    __smtx_model_eval_re_plus v =
      __smtx_model_eval_re_concat v
        (__smtx_model_eval_re_concat (__smtx_model_eval_re_mult v)
          (__smtx_model_eval_str_to_re
            (SmtValue.Seq (native_pack_string (native_string_lit ""))))) := by
  cases v
  case RegLan r =>
    cases r <;>
      simp [__smtx_model_eval_re_plus, __smtx_model_eval_re_concat,
        __smtx_model_eval_re_mult, __smtx_model_eval_str_to_re,
        native_re_concat, native_re_mult,
        native_str_to_re, impl_native_re_of_list, native_pack_string,
        native_pack_seq, native_unpack_seq,
        native_string_lit_empty]
  all_goals
    simp [__smtx_model_eval_re_plus, __smtx_model_eval_re_concat]

private theorem typed___eo_prog_re_plus_elim_impl
    (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
  RuleProofs.eo_has_bool_type (__eo_prog_re_plus_elim a1) := by
  let lhs := Term.Apply Term.re_plus a1
  let rhs :=
    Term.Apply (Term.Apply Term.re_concat a1)
      (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
        (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hLhsTranslate :
      __eo_to_smt (Term.Apply Term.re_plus a1) =
        SmtTerm.re_plus (__eo_to_smt a1) := by
    rfl
  have hLhsTyRaw :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.re_plus a1)) = SmtType.RegLan := by
    rw [hLhsTranslate]
    rw [typeof_re_plus_eq]
    simp [hA1SmtTy, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan := by
    simpa [lhs] using hLhsTyRaw
  have hStarTranslate :
      __eo_to_smt (Term.Apply Term.re_mult a1) =
        SmtTerm.re_mult (__eo_to_smt a1) := by
    rfl
  have hStarTy : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_mult a1)) = SmtType.RegLan := by
    rw [hStarTranslate]
    rw [typeof_re_mult_eq]
    simp [hA1SmtTy, native_ite, native_Teq]
  have hEmpTy : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String (native_string_lit ""))) = SmtType.RegLan
    rw [typeof_str_to_re_eq]
    simp [__smtx_typeof.eq_4, native_ite, native_Teq, native_string_valid,
      native_string_lit]
  have hInnerConcatTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
            (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))) =
        SmtTerm.re_concat (__eo_to_smt (Term.Apply Term.re_mult a1))
          (__eo_to_smt (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))) := by
    rfl
  have hInnerConcatTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
              (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))) = SmtType.RegLan := by
    rw [hInnerConcatTranslate]
    rw [typeof_re_concat_eq]
    simp [hStarTy, hEmpTy, native_ite, native_Teq]
  have hRhsTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply Term.re_concat a1)
              (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
                (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))) = SmtType.RegLan := by
    change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt a1)
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
            (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))) = SmtType.RegLan
    -- rewrite the inner component type before `simp` normalises
    -- `__eo_to_smt (Apply ..)` past `hInnerConcatTy`'s left-hand side
    rw [typeof_re_concat_eq, hA1SmtTy, hInnerConcatTy]
    simp [native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    simpa [rhs] using hRhsTyRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hProg :
      __eo_prog_re_plus_elim a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    cases a1 <;> simp [__eo_prog_re_plus_elim, lhs, rhs, native_string_lit_empty] at hA1NotStuck ⊢
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_plus_elim_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
  eo_interprets M (__eo_prog_re_plus_elim a1) true := by
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hProg :
      __eo_prog_re_plus_elim a1 =
        Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_plus a1))
          (Term.Apply (Term.Apply Term.re_concat a1)
            (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
              (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))) := by
    cases a1 <;> simp [__eo_prog_re_plus_elim, native_string_lit_empty] at hA1NotStuck ⊢
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_plus a1))
          (Term.Apply (Term.Apply Term.re_concat a1)
            (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
              (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))) := by
    rw [← hProg]
    exact typed___eo_prog_re_plus_elim_impl a1 hA1Trans hA1Ty
  have hLhsTranslate :
      __eo_to_smt (Term.Apply Term.re_plus a1) =
        SmtTerm.re_plus (__eo_to_smt a1) := by
    rfl
  have hRhsTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply Term.re_concat a1)
            (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
              (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))) =
        SmtTerm.re_concat (__eo_to_smt a1)
          (__eo_to_smt
            (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
              (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))) := by
    rfl
  have hInnerConcatTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
            (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))) =
        SmtTerm.re_concat (__eo_to_smt (Term.Apply Term.re_mult a1))
          (__eo_to_smt (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))) := by
    rfl
  have hStarTranslate :
      __eo_to_smt (Term.Apply Term.re_mult a1) =
        SmtTerm.re_mult (__eo_to_smt a1) := by
    rfl
  have hEmpTranslate :
      __eo_to_smt (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))) =
        SmtTerm.str_to_re (__eo_to_smt (Term.String (native_string_lit ""))) := by
    rfl
  have hEmptyStringEval :
      __smtx_model_eval M (__eo_to_smt (Term.String (native_string_lit ""))) =
        SmtValue.Seq (native_pack_string (native_string_lit "")) := by
    change __smtx_model_eval M (SmtTerm.String (native_string_lit "")) =
      SmtValue.Seq (native_pack_string (native_string_lit ""))
    rw [__smtx_model_eval.eq_4]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (Term.Apply Term.re_plus a1)) =
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply Term.re_concat a1)
              (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
                (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))) := by
    rw [hLhsTranslate, hRhsTranslate, hInnerConcatTranslate, hStarTranslate, hEmpTranslate]
    rw [__smtx_model_eval.eq_109, __smtx_model_eval.eq_114,
      __smtx_model_eval.eq_114, __smtx_model_eval.eq_108, __smtx_model_eval.eq_107]
    simpa [hEmptyStringEval] using
      smtx_model_eval_re_plus_elim (__smtx_model_eval M (__eo_to_smt a1))
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply Term.re_plus a1)
    (Term.Apply (Term.Apply Term.re_concat a1)
      (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
        (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.re_concat a1)
            (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
              (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))))

public theorem cmd_step_re_plus_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_plus_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_plus_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_plus_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_plus_elim args premises ≠ Term.Stuck :=
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
              have hProgEq :
                  __eo_cmd_step_proven s CRule.re_plus_elim (CArgList.cons a1 CArgList.nil)
                    CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_plus a1))
                      (Term.Apply (Term.Apply Term.re_concat a1)
                        (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
                          (Term.Apply Term.str_to_re (Term.String (native_string_lit ""))))) := by
                cases hA1 : a1 <;> first | exact False.elim (hA1NotStuck hA1) | rfl
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq
                  (__eo_typeof (Term.Apply Term.re_plus a1))
                  (__eo_typeof
                    (Term.Apply (Term.Apply Term.re_concat a1)
                      (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
                        (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))) = Term.Bool at hResultTy
              have hLhsNotStuck :
                  __eo_typeof (Term.Apply Term.re_plus a1) ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof (Term.Apply Term.re_plus a1))
                  (__eo_typeof
                    (Term.Apply (Term.Apply Term.re_concat a1)
                      (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult a1))
                        (Term.Apply Term.str_to_re (Term.String (native_string_lit "")))))) hResultTy).1
              have hA1Ty : __eo_typeof a1 = Term.RegLan := by
                have hTypeNotStuck : __eo_typeof_re_mult (__eo_typeof a1) ≠ Term.Stuck := by
                  change __eo_typeof (Term.Apply Term.re_plus a1) ≠ Term.Stuck
                  exact hLhsNotStuck
                exact eo_typeof_re_mult_eq_reglan_of_ne_stuck (__eo_typeof a1) hTypeNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_re_plus_elim a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_re_plus_elim_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_re_plus_elim_impl M hM a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_re_plus_elim a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
