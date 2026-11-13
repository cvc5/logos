module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySeqHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySeqHelpers

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

theorem eo_typeof_set_singleton_arg_not_stuck_of_ne_stuck
    {A : Term}
    (h : __eo_typeof_set_singleton A ≠ Term.Stuck) :
    A ≠ Term.Stuck := by
  cases A <;> simp [__eo_typeof_set_singleton] at h ⊢

theorem smt_set_singleton_non_none_of_has_smt_translation_type_eq
    (A X : Term)
    (hAppTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.set_singleton) A))
    (hATrans : RuleProofs.eo_has_smt_translation A)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTyEq : __eo_typeof X = __eo_typeof A) :
    __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt X)) ≠
      SmtType.None := by
  have hOrig :
      __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt A)) ≠
        SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hAppTrans
    change
      __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt A)) ≠
        SmtType.None at hAppTrans
    exact hAppTrans
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation A hATrans
  have hSmtTy :
      __smtx_typeof (__eo_to_smt X) =
        __smtx_typeof (__eo_to_smt A) := by
    rw [hXMatch, hAMatch, hXTyEq]
  simpa [typeof_set_singleton_eq_closed, hSmtTy] using hOrig

theorem eo_typeof_set_union_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_union A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Set) T ∧
      B = Term.Apply (Term.UOp UserOp.Set) T := by
  cases A <;> cases B <;> simp [__eo_typeof_set_union] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_set_union] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_set_union] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.Set) n) ≠
            Term.Stuck := by
        simpa [__eo_typeof_set_union] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

theorem eo_typeof_set_union_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_union A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_set_union_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_set_binop_non_none_of_eo_typeof_set_union_ne_stuck
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          __smtx_typeof_sets_op_2
            (__smtx_typeof X) (__smtx_typeof Y))
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_set_union (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof (smtOp (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  rcases eo_typeof_set_union_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hXTrans hXTy
  have hYSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hYTrans hYTy
  rw [hSmtType, hXSmt, hYSmt]
  simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]

theorem eo_typeof_set_insert_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_insert A B ≠ Term.Stuck) :
    ∃ T, A = T ∧ B = Term.Apply (Term.UOp UserOp.Set) T := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_insert] at h
  · cases B <;> simp [__eo_typeof_set_insert, hA] at h ⊢
    rename_i f T
    cases f <;> simp [__eo_typeof_set_insert, hA] at h ⊢
    rename_i op
    cases op <;> simp [__eo_typeof_set_insert, hA] at h ⊢
    have hReq :
        __eo_requires (__eo_eq A T) (Term.Boolean true) (Term.Apply (Term.UOp UserOp.Set) A) ≠
          Term.Stuck := by
      simpa [__eo_typeof_set_insert, hA] using h
    have hT : T = A :=
      support_eq_of_eo_eq_true A T
        (support_eo_requires_cond_eq_of_non_stuck hReq)
    exact hT

theorem eo_typeof_set_insert_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_insert A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hAStuck : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_insert] at h
  · rcases eo_typeof_set_insert_arg_types_of_ne_stuck h with
      ⟨T, hA, hB⟩
    constructor
    · exact hAStuck
    · intro hStuck
      rw [hB] at hStuck
      cases hStuck

theorem smt_set_insert_non_none_of_eo_typeof_set_insert_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp : __eo_typeof_set_insert (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt X))
      (__eo_to_smt Y)) ≠ SmtType.None := by
  rcases eo_typeof_set_insert_arg_types_of_ne_stuck hApp with ⟨T, hXTy, hYTy⟩
  have hXSmt := TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt := smt_typeof_eo_to_smt_set_of_typeof_set hYTrans hYTy
  have hWf := Smtm.smt_term_set_type_wf_of_non_none (__eo_to_smt Y) hYTrans hYSmt
  rw [typeof_set_union_eq, smtx_typeof_set_singleton_term_eq, hXSmt, hXTy, hYSmt]
  simp [__smtx_typeof_guard_wf, hWf, native_ite, __smtx_typeof_sets_op_2, native_Teq]

theorem eo_typeof_set_member_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_member A B ≠ Term.Stuck) :
    ∃ T, A = T ∧ B = Term.Apply (Term.UOp UserOp.Set) T := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_member] at h
  · cases B <;> simp [__eo_typeof_set_member, hA] at h ⊢
    rename_i f T
    cases f <;> simp [__eo_typeof_set_member, hA] at h ⊢
    rename_i op
    cases op <;> simp [__eo_typeof_set_member, hA] at h ⊢
    have hReq :
        __eo_requires (__eo_eq A T) (Term.Boolean true) Term.Bool ≠
          Term.Stuck := by
      simpa [__eo_typeof_set_member, hA] using h
    have hT : T = A :=
      support_eq_of_eo_eq_true A T
        (support_eo_requires_cond_eq_of_non_stuck hReq)
    exact hT

theorem eo_typeof_set_member_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_member A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hAStuck : A = Term.Stuck
  · subst A
    simp [__eo_typeof_set_member] at h
  · rcases eo_typeof_set_member_arg_types_of_ne_stuck h with
      ⟨T, hA, hB⟩
    constructor
    · exact hAStuck
    · intro hStuck
      rw [hB] at hStuck
      cases hStuck

theorem smt_set_member_non_none_of_eo_typeof_set_member_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_set_member (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.set_member (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rcases eo_typeof_set_member_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hYSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hYTrans hYTy
  rw [typeof_set_member_eq, hXSmt, hYSmt, hXTy]
  simp [__smtx_typeof_set_member, native_ite, native_Teq]

theorem eo_typeof_set_subset_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_subset A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Set) T ∧
      B = Term.Apply (Term.UOp UserOp.Set) T := by
  cases A <;> cases B <;> simp [__eo_typeof_set_subset] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_set_subset] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_set_subset] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true) Term.Bool ≠
            Term.Stuck := by
        simpa [__eo_typeof_set_subset] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

theorem eo_typeof_set_subset_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_set_subset A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_set_subset_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_set_subset_non_none_of_eo_typeof_set_subset_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_set_subset (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.set_subset (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  rcases eo_typeof_set_subset_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hXTrans hXTy
  have hYSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hYTrans hYTy
  rw [typeof_set_subset_eq, hXSmt, hYSmt]
  simp [__smtx_typeof_sets_op_2_ret, native_ite, native_Teq]

end SubstitutePreservationSupport
