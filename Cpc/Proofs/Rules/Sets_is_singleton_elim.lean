module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SetsMemberSupport
import all Cpc.Proofs.RuleSupport.SetsMemberSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def setsIsSingletonRhs (x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
    (Term.Apply (Term.UOp UserOp.set_singleton)
      (Term.Apply (Term.UOp UserOp.set_choose) x))

private theorem prog_sets_is_singleton_elim_eq_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_prog_sets_is_singleton_elim x =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.set_is_singleton) x))
        (setsIsSingletonRhs x) := by
  intro hX
  cases x <;> simp [__eo_prog_sets_is_singleton_elim, setsIsSingletonRhs] at hX ⊢

private theorem typeof_set_of_prog_sets_is_singleton_elim_bool (x : Term) :
    x ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_sets_is_singleton_elim x) = Term.Bool ->
    ∃ T, __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T := by
  intro hX hTy
  rw [prog_sets_is_singleton_elim_eq_of_ne_stuck x hX] at hTy
  change
      __eo_typeof_eq
        (__eo_typeof (Term.Apply (Term.UOp UserOp.set_is_singleton) x))
        (__eo_typeof (setsIsSingletonRhs x)) = Term.Bool at hTy
  rcases SetsMemberSupport.eo_typeof_eq_eq_bool_info hTy with ⟨_hSame, hLhsNS⟩
  change __eo_typeof_set_is_empty (__eo_typeof x) ≠ Term.Stuck at hLhsNS
  cases hXTy : __eo_typeof x
  all_goals try
    (exfalso
     simpa [__eo_typeof_set_is_empty, hXTy] using hLhsNS)
  case Apply f a =>
    cases f
    all_goals try
      (exfalso
       simpa [__eo_typeof_set_is_empty, hXTy] using hLhsNS)
    case UOp op =>
      cases op
      all_goals try
        (exfalso
         simpa [__eo_typeof_set_is_empty, hXTy] using hLhsNS)
      case Set =>
        exact ⟨a, rfl⟩

private theorem smt_typeof_set_empty_of_set_arg
    {x T : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __smtx_typeof
        (SmtTerm.set_empty (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x)))) =
      __smtx_typeof (__eo_to_smt x) := by
  have hXMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXSet :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) := by
    simpa [hXTy, __eo_to_smt_type] using hXMatch
  have hGuardNS :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) ≠ SmtType.None := by
    intro hNone
    exact hXTrans (hXSet.trans hNone)
  have hGuard :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) =
        SmtType.Set (__eo_to_smt_type T) := by
    unfold __smtx_typeof_guard at hGuardNS ⊢
    cases hT : native_Teq (__eo_to_smt_type T) SmtType.None <;>
      simp [native_ite, hT] at hGuardNS ⊢
  have hXSet' :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    rw [hXSet, hGuard]
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none (__eo_to_smt x) hXTrans hXSet'
  rw [smtx_typeof_set_empty_term_eq, hXSet']
  simp [__eo_to_smt_set_elem_type, __smtx_typeof_guard_wf, hSetWf,
    native_ite]

private theorem smt_typeof_set_singleton_choose_of_set_arg
    {x T : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __smtx_typeof
        (SmtTerm.set_singleton
          (SmtTerm.map_diff (__eo_to_smt x)
            (SmtTerm.set_empty
              (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x)))))) =
      __smtx_typeof (__eo_to_smt x) := by
  have hEmpty := smt_typeof_set_empty_of_set_arg hXTrans hXTy
  have hXMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hXSetGuard :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) := by
    simpa [hXTy, __eo_to_smt_type] using hXMatch
  have hGuardNS :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) ≠ SmtType.None := by
    intro hNone
    exact hXTrans (hXSetGuard.trans hNone)
  have hGuard :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) =
        SmtType.Set (__eo_to_smt_type T) := by
    unfold __smtx_typeof_guard at hGuardNS ⊢
    cases hT : native_Teq (__eo_to_smt_type T) SmtType.None <;>
      simp [native_ite, hT] at hGuardNS ⊢
  have hXSet :
      __smtx_typeof (__eo_to_smt x) = SmtType.Set (__eo_to_smt_type T) := by
    rw [hXSetGuard, hGuard]
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none (__eo_to_smt x) hXTrans hXSet
  have hEmpty' :
      __smtx_typeof (SmtTerm.set_empty (__eo_to_smt_type T)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hXSet, __eo_to_smt_set_elem_type] using hEmpty
  have hMapDiff :
      __smtx_typeof
          (SmtTerm.map_diff (__eo_to_smt x)
            (SmtTerm.set_empty
              (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))))) =
        __eo_to_smt_type T := by
    rw [typeof_map_diff_eq, hXSet]
    simp [__eo_to_smt_set_elem_type, hEmpty', __smtx_typeof_map_diff,
      native_ite, native_Teq]
  have hSingletonGuard :
      __smtx_typeof_guard_wf
          (SmtType.Set
            (__smtx_typeof
              (SmtTerm.map_diff (__eo_to_smt x)
                (SmtTerm.set_empty
                  (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x)))))))
          (SmtType.Set
            (__smtx_typeof
              (SmtTerm.map_diff (__eo_to_smt x)
                (SmtTerm.set_empty
                  (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))))))) =
        SmtType.Set
          (__smtx_typeof
            (SmtTerm.map_diff (__eo_to_smt x)
              (SmtTerm.set_empty
                (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x)))))) :=
    by
      rw [hMapDiff]
      simp [__smtx_typeof_guard_wf, hSetWf, native_ite]
  rw [smtx_typeof_set_singleton_term_eq, hSingletonGuard, hMapDiff, hXSet]

private theorem set_is_singleton_rhs_same_translation (x : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x) =
      __eo_to_smt (setsIsSingletonRhs x) := by
  rfl

private theorem typed___eo_prog_sets_is_singleton_elim_impl (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (__eo_prog_sets_is_singleton_elim x) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_sets_is_singleton_elim x) := by
  intro hXTrans hResultTy
  have hXNotStuck : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  rcases typeof_set_of_prog_sets_is_singleton_elim_bool x hXNotStuck hResultTy with
    ⟨T, hXTy⟩
  rw [prog_sets_is_singleton_elim_eq_of_ne_stuck x hXNotStuck]
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [set_is_singleton_rhs_same_translation x]
  · have hXTransNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := hXTrans
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x) =
          SmtTerm.eq (__eo_to_smt x)
            (SmtTerm.set_singleton
              (SmtTerm.map_diff (__eo_to_smt x)
                (SmtTerm.set_empty
                  (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x)))))) := by
      rfl
    rw [hTranslate]
    rw [typeof_eq_eq]
    have hSingletonTy :=
      smt_typeof_set_singleton_choose_of_set_arg hXTrans hXTy
    have hEqBool :
        __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof
              (SmtTerm.set_singleton
                (SmtTerm.map_diff (__eo_to_smt x)
                  (SmtTerm.set_empty
                    (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))))))) =
          SmtType.Bool :=
      (RuleProofs.smtx_typeof_eq_bool_iff
        (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof
          (SmtTerm.set_singleton
            (SmtTerm.map_diff (__eo_to_smt x)
              (SmtTerm.set_empty
                (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x)))))))).mpr
          ⟨hSingletonTy.symm, hXTransNN⟩
    intro hNone
    rw [hEqBool] at hNone
    cases hNone

private theorem facts___eo_prog_sets_is_singleton_elim_impl
    (M : SmtModel) (x : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (__eo_prog_sets_is_singleton_elim x) = Term.Bool ->
    eo_interprets M (__eo_prog_sets_is_singleton_elim x) true := by
  intro hXTrans hResultTy
  have hXNotStuck : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProgBool :=
    typed___eo_prog_sets_is_singleton_elim_impl x hXTrans hResultTy
  rw [prog_sets_is_singleton_elim_eq_of_ne_stuck x hXNotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_sets_is_singleton_elim_eq_of_ne_stuck x hXNotStuck] using hProgBool
  · rw [set_is_singleton_rhs_same_translation x]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (setsIsSingletonRhs x)))

public theorem cmd_step_sets_is_singleton_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_is_singleton_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_is_singleton_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_is_singleton_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_is_singleton_elim args premises ≠ Term.Stuck :=
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
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              change __eo_typeof (__eo_prog_sets_is_singleton_elim a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_sets_is_singleton_elim a1) true
                exact facts___eo_prog_sets_is_singleton_elim_impl M a1 hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_sets_is_singleton_elim_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
