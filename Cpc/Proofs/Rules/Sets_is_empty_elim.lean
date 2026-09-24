module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SetsMemberSupport
import all Cpc.Proofs.RuleSupport.SetsMemberSupport
public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private def setsIsEmptyRhs (a1 T0 : Term) : Term :=
  SetsBasicRewritesSupport.mkEq a1 (SetsBasicRewritesSupport.mkSetEmpty T0)

private theorem prog_sets_is_empty_elim_eq_of_ne_stuck (a1 T0 : Term) :
    a1 ≠ Term.Stuck ->
    __eo_prog_sets_is_empty_elim a1 (Term.Apply (Term.UOp UserOp.Set) T0) =
      SetsBasicRewritesSupport.mkEq
        (Term.Apply (Term.UOp UserOp.set_is_empty) a1)
        (setsIsEmptyRhs a1 T0) := by
  intro hA1
  cases a1 <;>
    simp [__eo_prog_sets_is_empty_elim, SetsBasicRewritesSupport.mkEq,
      SetsBasicRewritesSupport.mkSetEmpty, setsIsEmptyRhs] at hA1 ⊢

private theorem prog_sets_is_empty_elim_ne_stuck_info (a1 a2 : Term)
    (hProg : __eo_prog_sets_is_empty_elim a1 a2 ≠ Term.Stuck) :
    a1 ≠ Term.Stuck ∧
      ∃ t, a2 = Term.Apply (Term.UOp UserOp.Set) t := by
  by_cases hx : a1 = Term.Stuck
  · subst a1
    simp [__eo_prog_sets_is_empty_elim] at hProg
  refine ⟨hx, ?_⟩
  cases a2 with
  | Apply f t =>
      cases f with
      | UOp op =>
          by_cases hSet : op = UserOp.Set
          · subst op
            exact ⟨t, rfl⟩
          · exfalso
            apply hProg
            simp [__eo_prog_sets_is_empty_elim, hx, hSet]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_sets_is_empty_elim, hx]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_sets_is_empty_elim, hx]

private theorem typeof_a1_set_of_result_bool (a1 T0 : Term) :
    a1 ≠ Term.Stuck ->
    __eo_typeof
        (__eo_prog_sets_is_empty_elim a1
          (Term.Apply (Term.UOp UserOp.Set) T0)) = Term.Bool ->
    __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) T0 := by
  intro hA1 hTy
  rw [prog_sets_is_empty_elim_eq_of_ne_stuck a1 T0 hA1] at hTy
  have hEqTy :
      __eo_typeof_eq
          (__eo_typeof_set_is_empty (__eo_typeof a1))
          (__eo_typeof (setsIsEmptyRhs a1 T0)) = Term.Bool := by
    have hsimpa := hTy
    try simp [SetsBasicRewritesSupport.mkEq] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hEqTy with ⟨hSame, hLNS⟩
  have hA1Set : ∃ U, __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) U := by
    cases hA1Ty : __eo_typeof a1
    all_goals try
      (exfalso; simpa [__eo_typeof_set_is_empty, hA1Ty] using hLNS)
    case Apply f a =>
      cases f
      all_goals try
        (exfalso; simpa [__eo_typeof_set_is_empty, hA1Ty] using hLNS)
      case UOp op =>
        cases op
        all_goals try
          (exfalso; simpa [__eo_typeof_set_is_empty, hA1Ty] using hLNS)
        case Set => exact ⟨a, rfl⟩
  rcases hA1Set with ⟨U, hUTy⟩
  have hLBool : __eo_typeof_set_is_empty (__eo_typeof a1) = Term.Bool := by
    simp [__eo_typeof_set_is_empty, hUTy]
  have hRhsBool : __eo_typeof (setsIsEmptyRhs a1 T0) = Term.Bool := by
    rw [← hSame, hLBool]
  have hInnerEqTy :
      __eo_typeof_eq (__eo_typeof a1)
          (__eo_typeof (SetsBasicRewritesSupport.mkSetEmpty T0)) = Term.Bool := by
    have hsimpa := hRhsBool
    try simp [setsIsEmptyRhs, SetsBasicRewritesSupport.mkEq] at hsimpa ⊢
    exact hsimpa
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hInnerEqTy with
    ⟨hInnerSame, _⟩
  have hEmptyTy :
      __eo_typeof (SetsBasicRewritesSupport.mkSetEmpty T0) =
        Term.Apply (Term.UOp UserOp.Set) U := by
    rw [← hInnerSame, hUTy]
  have hUT0 : U = T0 :=
    SetsBasicRewritesSupport.eo_typeof_set_empty_set_eq hEmptyTy
  rw [hUTy, hUT0]

private theorem to_smt_set_is_empty_eq_rhs (a1 T0 : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a1)
    (hTy : __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) T0) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) a1) =
      __eo_to_smt (setsIsEmptyRhs a1 T0) := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a1 hTrans
  have hXTyRaw :
      __smtx_typeof (__eo_to_smt a1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T0) := by
    rw [hMatch, hTy]
  have hXNonNone : __smtx_typeof (__eo_to_smt a1) ≠ SmtType.None := hTrans
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T0) ≠ SmtType.None := by
    rw [← hXTyRaw]
    exact hXNonNone
  have hSetTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T0) =
        SmtType.Set (__eo_to_smt_type T0) :=
    SetsBasicRewritesSupport.eo_to_smt_type_set_of_non_none T0 hSetNonNone
  have hXTy :
      __smtx_typeof (__eo_to_smt a1) = SmtType.Set (__eo_to_smt_type T0) := by
    rw [hXTyRaw, hSetTy]
  show
    SmtTerm.eq (__eo_to_smt a1)
        (SmtTerm.set_empty
          (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a1)))) =
      SmtTerm.eq (__eo_to_smt a1)
        (__eo_to_smt_set_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T0)))
  rw [hXTy, hSetTy]
  simp only [__eo_to_smt_set_elem_type, __eo_to_smt_set_empty]

private theorem smt_typeof_set_is_empty_bool (a1 T0 : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a1)
    (hTy : __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) T0) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) a1)) =
      SmtType.Bool := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a1 hTrans
  have hSetNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T0) ≠ SmtType.None := by
    rw [← hTy, ← hMatch]
    exact hTrans
  have hSetTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T0) =
        SmtType.Set (__eo_to_smt_type T0) :=
    SetsBasicRewritesSupport.eo_to_smt_type_set_of_non_none T0 hSetNonNone
  have hXTy :
      __smtx_typeof (__eo_to_smt a1) = SmtType.Set (__eo_to_smt_type T0) := by
    rw [hMatch, hTy, hSetTy]
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__eo_to_smt_type T0)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none (__eo_to_smt a1) hTrans hXTy
  show
    __smtx_typeof
        (SmtTerm.eq (__eo_to_smt a1)
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a1))))) =
      SmtType.Bool
  rw [typeof_eq_eq, hXTy]
  simp [__eo_to_smt_set_elem_type, smtx_typeof_set_empty_term_eq,
    __smtx_typeof_guard_wf, __smtx_typeof_eq, __smtx_typeof_guard,
    native_ite, native_Teq, hSetWf]

private theorem typed___eo_prog_sets_is_empty_elim_impl (a1 T0 : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a1)
    (hTy : __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) T0) :
    RuleProofs.eo_has_bool_type
      (SetsBasicRewritesSupport.mkEq
        (Term.Apply (Term.UOp UserOp.set_is_empty) a1)
        (setsIsEmptyRhs a1 T0)) := by
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [to_smt_set_is_empty_eq_rhs a1 T0 hTrans hTy]
  · rw [smt_typeof_set_is_empty_bool a1 T0 hTrans hTy]
    intro h
    cases h

private theorem facts___eo_prog_sets_is_empty_elim_impl
    (M : SmtModel) (a1 T0 : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a1)
    (hTy : __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) T0) :
    eo_interprets M
      (SetsBasicRewritesSupport.mkEq
        (Term.Apply (Term.UOp UserOp.set_is_empty) a1)
        (setsIsEmptyRhs a1 T0)) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact typed___eo_prog_sets_is_empty_elim_impl a1 T0 hTrans hTy
  · rw [to_smt_set_is_empty_eq_rhs a1 T0 hTrans hTy]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (setsIsEmptyRhs a1 T0)))

public theorem cmd_step_sets_is_empty_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_is_empty_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_is_empty_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_is_empty_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_is_empty_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  change
                    __eo_typeof (__eo_prog_sets_is_empty_elim a1 a2) =
                      Term.Bool at hResultTy
                  change
                    StepRuleProperties M (premiseTermList s CIndexList.nil)
                      (__eo_prog_sets_is_empty_elim a1 a2)
                  have hProg' :
                      __eo_prog_sets_is_empty_elim a1 a2 ≠ Term.Stuck :=
                    term_ne_stuck_of_typeof_bool hResultTy
                  rcases prog_sets_is_empty_elim_ne_stuck_info a1 a2 hProg' with
                    ⟨_hA1NS, t, hA2⟩
                  subst hA2
                  have hMask :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        __smtx_type_wf
                            (__eo_to_smt_type
                              (Term.Apply (Term.UOp UserOp.Set) t)) = true ∧
                          True := by
                    simpa [cmdTranslationOk, cArgListTranslationOkMask,
                      argTranslationOkMasked] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                    hMask.1
                  have hA1NotStuck : a1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hA1Ty :
                      __eo_typeof a1 = Term.Apply (Term.UOp UserOp.Set) t :=
                    typeof_a1_set_of_result_bool a1 t hA1NotStuck hResultTy
                  rw [prog_sets_is_empty_elim_eq_of_ne_stuck a1 t hA1NotStuck]
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    exact facts___eo_prog_sets_is_empty_elim_impl M a1 t
                      hA1Trans hA1Ty
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_sets_is_empty_elim_impl a1 t hA1Trans hA1Ty)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
