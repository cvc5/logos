module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericOps
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericOps

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

/-- Shared combined preservation proof for an application headed by a datatype
selector. The selector head itself has SMT type `None`, so this case rebuilds
translatability from the selector-application typing facts rather than from the
generic application helper. -/
theorem substitute_simul_apply_dtsel_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat)
    (a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.DtSel s d i j) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.DtSel s d i j) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.DtSel s d i j) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.DtSel s d i j) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.DtSel s d i j) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  have hType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.DtSel s d i j) a) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.DtSel s d i j) a) :=
    SubstituteSupport.substitute_simul_rec_apply_dtsel_typeof_eq_of_typeof_ne_stuck
      s d i j a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun hATrans hATy => (hARec hATrans hATy).1)
      hTy
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hNotBinder :
      ∀ q v vs,
        Term.DtSel s d i j ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs h
    cases h
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.DtSel s d i j) a) xs ts bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.DtSel s d i j) xs ts bvs)
          aSub := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.DtSel s d i j) a xs ts bvs
        hisr hxs hts hbvs hNotBinder
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.DtSel s d i j) xs ts bvs ≠
        Term.Stuck :=
    SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      (Term.DtSel s d i j) a xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hTy
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.DtSel s d i j) xs ts bvs =
        Term.DtSel s d i j :=
    SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
      (Term.DtSel s d i j) xs ts bvs hXsEnv hBvsEnv hTs
      (by intro f x h; cases h)
      (by intro name T h; cases h)
      (by intro h; cases h)
      hHeadNe
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.DtSel s d i j) aSub) ≠
        Term.Stuck := by
    simpa [hSubstEq, hHeadEq] using hTy
  have hMk :
      __eo_mk_apply (Term.DtSel s d i j) aSub =
        Term.Apply (Term.DtSel s d i j) aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.DtSel s d i j) a) xs ts bvs =
        Term.Apply (Term.DtSel s d i j) aSub := by
    rw [hSubstEq, hHeadEq, hMk]
  have hAppTy :
      __eo_typeof (Term.Apply (Term.DtSel s d i j) aSub) ≠
        Term.Stuck := by
    simpa [hResultEq] using hTy
  have hReserved :
      __eo_to_smt_reserved_datatype_name s = false :=
    SubstituteSupport.dtsel_reserved_false_of_apply_has_smt_translation hTrans
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
          (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    change
      __smtx_typeof
          (SmtTerm.Apply
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
            (__eo_to_smt a)) ≠
        SmtType.None at hTrans
    rw [hReserved] at hTrans
    simpa [native_ite] using hTrans
  have hATrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [dt_sel_arg_datatype_of_non_none hApplyNN]
    intro h
    cases h
  have hATy : __eo_typeof aSub ≠ Term.Stuck := by
    intro hArgTy
    apply hAppTy
    change
      __eo_typeof_apply
          (__eo_typeof (Term.DtSel s d i j))
          (__eo_typeof aSub) =
        Term.Stuck
    rw [hArgTy]
    rfl
  have hABoth :
      __eo_typeof aSub = __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation aSub :=
    hARec hATrans hATy
  have hASubSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation aSub hABoth.2
  have hASmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATrans
  have hSubArgSmt :
      __smtx_typeof (__eo_to_smt aSub) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl d) := by
    calc
      __smtx_typeof (__eo_to_smt aSub) =
          __eo_to_smt_type (__eo_typeof aSub) := hASubSmt
      _ = __eo_to_smt_type (__eo_typeof a) := by rw [hABoth.1]
      _ = __smtx_typeof (__eo_to_smt a) := hASmt.symm
      _ = SmtType.Datatype s (__eo_to_smt_datatype_decl d) :=
          dt_sel_arg_datatype_of_non_none hApplyNN
  let R := __smtx_ret_typeof_sel s (__eo_to_smt_datatype_decl d) i j
  let inner :=
    __smtx_typeof_apply
      (SmtType.FunType (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) R)
      (__smtx_typeof (__eo_to_smt a))
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at hApplyNN
    rw [typeof_dt_sel_apply_eq] at hApplyNN
    simpa [R, inner] using hApplyNN
  have hRetWf : __smtx_type_wf R = true :=
    smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  have hRetNN : R ≠ SmtType.None := by
    have hTermTy := dt_sel_term_typeof_of_non_none hApplyNN
    unfold term_has_non_none_type at hApplyNN
    intro hNone
    apply hApplyNN
    rw [hTermTy]
    simpa [R] using hNone
  have hSubApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
          (__eo_to_smt aSub)) := by
    unfold term_has_non_none_type
    rw [typeof_dt_sel_apply_eq]
    simpa [R, __smtx_typeof_apply, __smtx_typeof_guard,
      __smtx_typeof_guard_wf, native_ite, native_Teq, hSubArgSmt, hRetWf]
      using hRetNN
  refine ⟨hType, ?_⟩
  rw [hResultEq]
  unfold RuleProofs.eo_has_smt_translation
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
            (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
          (__eo_to_smt aSub)) ≠
      SmtType.None
  rw [hReserved]
  simpa [native_ite, term_has_non_none_type] using hSubApplyNN

end SubstitutePreservationSupport
