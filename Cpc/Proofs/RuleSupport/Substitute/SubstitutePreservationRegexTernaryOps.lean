module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTernaryCore
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTernaryCore

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

private theorem eo_typeof_str_replace_re_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_replace_re A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  cases A <;> cases B <;> cases C <;>
    simp [__eo_typeof_str_replace_re] at h ⊢

private theorem eo_typeof_str_replace_re_arg_types_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_replace_re A B C ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.UOp UserOp.RegLan ∧
        C = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  unfold __eo_typeof_str_replace_re at h
  split at h <;> simp at h ⊢

theorem substitute_simul_str_replace_re_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s regex repl xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) regex)
          repl))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) regex)
            repl)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecRegex :
      RuleProofs.eo_has_smt_translation regex ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) =
          __eo_typeof regex ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs))
    (hRecRepl :
      RuleProofs.eo_has_smt_translation repl ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs) =
          __eo_typeof repl ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) regex)
            repl)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) regex)
          repl) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) regex)
            repl)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_replace_re s regex repl xs ts bvs hXsEnv hBvsEnv hTs
      hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_replace_re) (smtOp := SmtTerm.str_replace_re)
          (by rfl)
          (fun hNN =>
            str_replace_re_args_have_smt_translation_of_non_none
              (typeof_str_replace_re_eq (__eo_to_smt s) (__eo_to_smt regex)
                (__eo_to_smt repl))
              hNN)
          h)
      (fun S R T hApp => by
        change
          __eo_typeof_str_replace_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof T) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_replace_re_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ R₁ T₁ S₂ R₂ T₂ hS hR hT => by
        change
          __eo_typeof_str_replace_re (__eo_typeof S₁) (__eo_typeof R₁)
              (__eo_typeof T₁) =
            __eo_typeof_str_replace_re (__eo_typeof S₂) (__eo_typeof R₂)
              (__eo_typeof T₂)
        rw [hS, hR, hT])
      (fun S R T hSTrans hRTrans hTTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_replace_re (__eo_to_smt S) (__eo_to_smt R)
                (__eo_to_smt T)) ≠
            SmtType.None
        change
          __eo_typeof_str_replace_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof T) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_replace_re_arg_types_of_ne_stuck hApp with
          ⟨hSTy, hRTy, hTTy⟩
        have hSSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hSTrans hSTy
        have hRSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hRTrans hRTy
        have hTSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hTTrans hTTy
        rw [typeof_str_replace_re_eq, hSSmt, hRSmt, hTSmt]
        simp [native_ite, native_Teq])
      hRecS hRecRegex hRecRepl

theorem substitute_simul_str_replace_re_all_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s regex repl xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s)
            regex)
          repl))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s)
              regex)
            repl)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecRegex :
      RuleProofs.eo_has_smt_translation regex ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) =
          __eo_typeof regex ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs))
    (hRecRepl :
      RuleProofs.eo_has_smt_translation repl ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs) =
          __eo_typeof repl ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s)
              regex)
            repl)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s)
            regex)
          repl) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s)
              regex)
            repl)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_replace_re_all s regex repl xs ts bvs hXsEnv hBvsEnv hTs
      hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_replace_re_all)
          (smtOp := SmtTerm.str_replace_re_all)
          (by rfl)
          (fun hNN =>
            str_replace_re_args_have_smt_translation_of_non_none
              (typeof_str_replace_re_all_eq (__eo_to_smt s)
                (__eo_to_smt regex) (__eo_to_smt repl))
              hNN)
          h)
      (fun S R T hApp => by
        change
          __eo_typeof_str_replace_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof T) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_replace_re_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ R₁ T₁ S₂ R₂ T₂ hS hR hT => by
        change
          __eo_typeof_str_replace_re (__eo_typeof S₁) (__eo_typeof R₁)
              (__eo_typeof T₁) =
            __eo_typeof_str_replace_re (__eo_typeof S₂) (__eo_typeof R₂)
              (__eo_typeof T₂)
        rw [hS, hR, hT])
      (fun S R T hSTrans hRTrans hTTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_replace_re_all (__eo_to_smt S) (__eo_to_smt R)
                (__eo_to_smt T)) ≠
            SmtType.None
        change
          __eo_typeof_str_replace_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof T) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_replace_re_arg_types_of_ne_stuck hApp with
          ⟨hSTy, hRTy, hTTy⟩
        have hSSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hSTrans hSTy
        have hRSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hRTrans hRTy
        have hTSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hTTrans hTTy
        rw [typeof_str_replace_re_all_eq, hSSmt, hRSmt, hTSmt]
        simp [native_ite, native_Teq])
      hRecS hRecRegex hRecRepl

private theorem eo_typeof_str_indexof_re_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof_re A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  cases A <;> cases B <;> cases C <;>
    simp [__eo_typeof_str_indexof_re] at h ⊢

private theorem eo_typeof_str_indexof_re_arg_types_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof_re A B C ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.UOp UserOp.RegLan ∧
        C = Term.UOp UserOp.Int := by
  unfold __eo_typeof_str_indexof_re at h
  split at h <;> simp at h ⊢

theorem substitute_simul_str_indexof_re_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s regex start xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) regex)
          start))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) regex)
            start)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecRegex :
      RuleProofs.eo_has_smt_translation regex ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) =
          __eo_typeof regex ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs))
    (hRecStart :
      RuleProofs.eo_has_smt_translation start ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) start xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) start xs ts bvs) =
          __eo_typeof start ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) start xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) regex)
            start)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) regex)
          start) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) regex)
            start)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_indexof_re s regex start xs ts bvs hXsEnv hBvsEnv hTs
      hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_indexof_re) (smtOp := SmtTerm.str_indexof_re)
          (by rfl) str_indexof_re_args_have_smt_translation_of_non_none h)
      (fun S R I hApp => by
        change
          __eo_typeof_str_indexof_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof I) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_indexof_re_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ R₁ I₁ S₂ R₂ I₂ hS hR hI => by
        change
          __eo_typeof_str_indexof_re (__eo_typeof S₁) (__eo_typeof R₁)
              (__eo_typeof I₁) =
            __eo_typeof_str_indexof_re (__eo_typeof S₂) (__eo_typeof R₂)
              (__eo_typeof I₂)
        rw [hS, hR, hI])
      (fun S R I hSTrans hRTrans hITrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_indexof_re (__eo_to_smt S) (__eo_to_smt R)
                (__eo_to_smt I)) ≠
            SmtType.None
        change
          __eo_typeof_str_indexof_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof I) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_indexof_re_arg_types_of_ne_stuck hApp with
          ⟨hSTy, hRTy, hITy⟩
        have hSSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hSTrans hSTy
        have hRSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hRTrans hRTy
        have hISmt :=
          smt_typeof_eo_to_smt_int_of_typeof_int hITrans hITy
        rw [typeof_str_indexof_re_eq, hSSmt, hRSmt, hISmt]
        simp [native_ite, native_Teq])
      hRecS hRecRegex hRecStart


end SubstitutePreservationSupport
