module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationIndexedOps
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationIndexedOps

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

private theorem eo_typeof_re_exp_arg_reglan_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_re_exp A idx C ≠ Term.Stuck) :
    C = Term.UOp UserOp.RegLan := by
  unfold __eo_typeof_re_exp at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_int_to_bv_arg_int_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_int_to_bv A idx C ≠ Term.Stuck) :
    C = Term.UOp UserOp.Int := by
  unfold __eo_typeof_int_to_bv at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_repeat_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_repeat A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_repeat at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_zero_extend_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_zero_extend A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_zero_extend at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_rotate_left_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_rotate_left A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_rotate_left at h
  split at h <;> simp at h ⊢

theorem substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp1) (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 op idx) a))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) a) ->
        eoHasSmtTranslation a)
    (hArgTyNe :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp1 op idx) X) ≠ Term.Stuck ->
          __eo_typeof X ≠ Term.Stuck)
    (hTypeCong :
      ∀ X Y,
        __eo_typeof X = __eo_typeof Y ->
          __eo_typeof (Term.Apply (Term.UOp1 op idx) X) =
            __eo_typeof (Term.Apply (Term.UOp1 op idx) Y))
    (hBuild :
      ∀ X,
        RuleProofs.eo_has_smt_translation X ->
          __eo_typeof X = __eo_typeof a ->
          __eo_typeof (Term.Apply (Term.UOp1 op idx) X) ≠ Term.Stuck ->
            RuleProofs.eo_has_smt_translation
              (Term.Apply (Term.UOp1 op idx) X))
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
            (Term.Apply (Term.UOp1 op idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 op idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hNotBinder :
      ∀ q v vs,
        Term.UOp1 op idx ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs h
    cases h
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ts bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.UOp1 op idx) xs ts bvs)
          aSub := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp1 op idx) a xs ts bvs
        hisr hxs hts hbvs hNotBinder
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 op idx) xs ts bvs ≠
        Term.Stuck :=
    SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      (Term.UOp1 op idx) a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hTy
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 op idx) xs ts bvs =
        Term.UOp1 op idx :=
    SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
      (Term.UOp1 op idx) xs ts bvs hXsEnv hBvsEnv hTs
      (by intro f x h; cases h)
      (by intro name T h; cases h)
      (by intro h; cases h)
      hHeadNe
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp1 op idx) aSub) ≠
        Term.Stuck := by
    simpa [hSubstEq, hHeadEq] using hTy
  have hMk :
      __eo_mk_apply (Term.UOp1 op idx) aSub =
        Term.Apply (Term.UOp1 op idx) aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ts bvs =
        Term.Apply (Term.UOp1 op idx) aSub := by
    rw [hSubstEq, hHeadEq, hMk]
  have hTyApply :
      __eo_typeof (Term.Apply (Term.UOp1 op idx) aSub) ≠
        Term.Stuck := by
    simpa [hResultEq] using hTy
  have hTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hArgExtract hTransEo
  have hABoth :
      __eo_typeof aSub = __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation aSub :=
    hARec hATrans (hArgTyNe aSub hTyApply)
  refine ⟨?_, ?_⟩
  · rw [hResultEq]
    exact hTypeCong aSub a hABoth.1
  · rw [hResultEq]
    exact hBuild aSub hABoth.2 hABoth.1 hTyApply

theorem substitute_simul_apply_re_exp_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.re_exp idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.re_exp idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.re_exp idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.re_exp idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.re_exp idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.re_exp idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_re_exp (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        have hXTy := eo_typeof_re_exp_arg_reglan_of_ne_stuck hApp
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_re_exp (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_re_exp (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans _hXTyEq hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hTransEo :
            eoHasSmtTranslation
              (Term.Apply (Term.UOp1 UserOp1.re_exp idx) a) := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hTrans
        rcases re_exp_index_nat_valid_and_arg_has_smt_translation hTransEo with
          ⟨hIdxValid, _hATrans⟩
        rcases smt_numeral_nonneg_of_eo_to_smt_nat_is_valid hIdxValid with
          ⟨idxN, hIdxNum, hIdxNonneg⟩
        change
          __eo_typeof_re_exp (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        have hXTy := eo_typeof_re_exp_arg_reglan_of_ne_stuck hApp
        have hXSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hXTrans hXTy
        rw [typeof_re_exp_eq, hIdxNum, hXSmt]
        simp [__smtx_typeof_re_exp, hIdxNonneg, native_ite])
      hARec hTy

theorem substitute_simul_apply_int_to_bv_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.int_to_bv idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_int_to_bv (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        have hXTy := eo_typeof_int_to_bv_arg_int_of_ne_stuck hApp
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_int_to_bv (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_int_to_bv (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans _hXTyEq hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hTransEo :
            eoHasSmtTranslation
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) a) := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hTrans
        rcases int_to_bv_index_nat_valid_and_arg_has_smt_translation hTransEo with
          ⟨hIdxValid, _hATrans⟩
        rcases smt_numeral_nonneg_of_eo_to_smt_nat_is_valid hIdxValid with
          ⟨idxN, hIdxNum, hIdxNonneg⟩
        change
          __eo_typeof_int_to_bv (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        have hXTy := eo_typeof_int_to_bv_arg_int_of_ne_stuck hApp
        have hXSmt :=
          smt_typeof_eo_to_smt_int_of_typeof_int hXTrans hXTy
        rw [typeof_int_to_bv_eq, hIdxNum, hXSmt]
        simp [__smtx_typeof_int_to_bv, hIdxNonneg, native_ite])
      hARec hTy

theorem substitute_simul_apply_repeat_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.repeat idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.repeat idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.repeat idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.repeat idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.repeat idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.repeat idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_repeat (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_repeat_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_repeat (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_repeat (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.repeat idx a hTrans
        have hNN :
            term_has_non_none_type
              (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None at hRaw
          exact hRaw
        rcases repeat_args_of_non_none hNN with
          ⟨idxN, w, hIdxNum, hASmtTy, hIdxBound⟩
        have hXSmtTy :=
          smt_typeof_subst_arg_eq_bitvec_of_type_eq
            hXTrans hATrans hXTyEq hASmtTy
        rw [typeof_repeat_eq, hIdxNum, hXSmtTy]
        simp [__smtx_typeof_repeat, native_ite, hIdxBound])
      hARec hTy

theorem substitute_simul_apply_zero_extend_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.zero_extend idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_zero_extend (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_zero_extend_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_zero_extend (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_zero_extend (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.zero_extend idx a hTrans
        have hNN :
            term_has_non_none_type
              (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None at hRaw
          exact hRaw
        rcases zero_extend_args_of_non_none hNN with
          ⟨idxN, w, hIdxNum, hASmtTy, hIdxBound⟩
        have hXSmtTy :=
          smt_typeof_subst_arg_eq_bitvec_of_type_eq
            hXTrans hATrans hXTyEq hASmtTy
        rw [typeof_zero_extend_eq, hIdxNum, hXSmtTy]
        simp [__smtx_typeof_zero_extend, native_ite, hIdxBound])
      hARec hTy

theorem substitute_simul_apply_sign_extend_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.sign_extend idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_zero_extend (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_zero_extend_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_zero_extend (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_zero_extend (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.sign_extend idx a hTrans
        have hNN :
            term_has_non_none_type
              (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None at hRaw
          exact hRaw
        rcases sign_extend_args_of_non_none hNN with
          ⟨idxN, w, hIdxNum, hASmtTy, hIdxBound⟩
        have hXSmtTy :=
          smt_typeof_subst_arg_eq_bitvec_of_type_eq
            hXTrans hATrans hXTyEq hASmtTy
        rw [typeof_sign_extend_eq, hIdxNum, hXSmtTy]
        simp [__smtx_typeof_sign_extend, native_ite, hIdxBound])
      hARec hTy

theorem substitute_simul_apply_rotate_left_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.rotate_left idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_rotate_left (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_rotate_left_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_rotate_left (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_rotate_left (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.rotate_left idx a hTrans
        have hNN :
            term_has_non_none_type
              (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None at hRaw
          exact hRaw
        rcases rotate_left_args_of_non_none hNN with
          ⟨idxN, w, hIdxNum, hASmtTy, hIdxBound⟩
        have hXSmtTy :=
          smt_typeof_subst_arg_eq_bitvec_of_type_eq
            hXTrans hATrans hXTyEq hASmtTy
        rw [typeof_rotate_left_eq, hIdxNum, hXSmtTy]
        simp [__smtx_typeof_rotate_left, native_ite, hIdxBound])
      hARec hTy

theorem substitute_simul_apply_rotate_right_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.rotate_right idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_rotate_left (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_rotate_left_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_rotate_left (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_rotate_left (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.rotate_right idx a hTrans
        have hNN :
            term_has_non_none_type
              (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None at hRaw
          exact hRaw
        rcases rotate_right_args_of_non_none hNN with
          ⟨idxN, w, hIdxNum, hASmtTy, hIdxBound⟩
        have hXSmtTy :=
          smt_typeof_subst_arg_eq_bitvec_of_type_eq
            hXTrans hATrans hXTyEq hASmtTy
        rw [typeof_rotate_right_eq, hIdxNum, hXSmtTy]
        simp [__smtx_typeof_rotate_right, native_ite, hIdxBound])
      hARec hTy

private theorem smt_typeof_binary_one_one :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  decide +kernel

private theorem eo_typeof_at_bit_arg_bitvec_of_ne_stuck
    {A C : Term}
    (h : __eo_typeof__at_bit A C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof__at_bit at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_is_arg_ne_stuck_of_ne_stuck
    {A C : Term}
    (h : __eo_typeof_is A C ≠ Term.Stuck) :
    C ≠ Term.Stuck := by
  by_cases hC : C = Term.Stuck
  · subst C
    cases A <;> simp [__eo_typeof_is] at h
  · exact hC

private theorem eo_typeof_tuple_select_arg_ne_stuck_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_tuple_select A idx C ≠ Term.Stuck) :
    C ≠ Term.Stuck := by
  by_cases hC : C = Term.Stuck
  · subst C
    cases A <;> cases idx <;> simp [__eo_typeof_tuple_select] at h
  · exact hC

private theorem smt_typeof_tuple_select_non_none_of_arg_type_eq
    (idx : Term) (a X : SmtTerm)
    (hTyEq : __smtx_typeof X = __smtx_typeof a)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_tuple_select (__smtx_typeof a) (__eo_to_smt idx) a) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt_tuple_select (__smtx_typeof X) (__eo_to_smt idx) X) ≠
      SmtType.None := by
  cases hA : __smtx_typeof a with
  | Datatype s d =>
      cases hIdx : __eo_to_smt idx with
      | Numeral n =>
          cases d with
          | nil =>
              exfalso
              apply hNN
              simp [__eo_to_smt_tuple_select, hA, hIdx]
          | cons s2 body rest =>
              cases rest with
              | cons s3 body3 rest3 =>
                  exfalso
                  apply hNN
                  simp [__eo_to_smt_tuple_select, hA, hIdx]
              | nil =>
                  cases hCond :
                      native_and
                        (native_and
                          (native_streq s (native_string_lit "@Tuple"))
                          (native_streq s2 (native_string_lit "@Tuple")))
                        (native_zleq 0 n)
                  · exfalso
                    apply hNN
                    simp [__eo_to_smt_tuple_select, hA, hIdx, hCond, native_ite]
                  · have hNN' := hNN
                    simp [__eo_to_smt_tuple_select, hA, hIdx, hCond, native_ite]
                      at hNN'
                    rw [hTyEq, hA]
                    simp [__eo_to_smt_tuple_select, hCond, native_ite]
                    rw [typeof_dt_sel_apply_eq]
                    rw [typeof_dt_sel_apply_eq] at hNN'
                    simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                      native_Teq, hA, hTyEq] using hNN'
      | _ =>
          exfalso
          apply hNN
          simp [__eo_to_smt_tuple_select, hA, hIdx]
  | _ =>
      exfalso
      apply hNN
      simp [__eo_to_smt_tuple_select, hA]

theorem substitute_simul_apply_at_bit_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1._at_bit idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1._at_bit idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1._at_bit idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1._at_bit idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1._at_bit idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1._at_bit idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof__at_bit (__eo_typeof idx) (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_at_bit_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof__at_bit (__eo_typeof idx) (__eo_typeof X) =
            __eo_typeof__at_bit (__eo_typeof idx) (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.eq
                (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                  (__eo_to_smt X))
                (SmtTerm.Binary 1 1)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1._at_bit idx a hTrans
        have hNN :
            term_has_non_none_type
              (SmtTerm.eq
                (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                  (__eo_to_smt a))
                (SmtTerm.Binary 1 1)) := by
          unfold term_has_non_none_type
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (SmtTerm.eq
                  (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                    (__eo_to_smt a))
                  (SmtTerm.Binary 1 1)) ≠
              SmtType.None at hRaw
          exact hRaw
        have hEqNN :
            __smtx_typeof_eq
                (__smtx_typeof
                  (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                    (__eo_to_smt a)))
                (SmtType.BitVec 1) ≠
              SmtType.None := by
          unfold term_has_non_none_type at hNN
          rw [typeof_eq_eq, smt_typeof_binary_one_one] at hNN
          exact hNN
        have hExtTy :
            __smtx_typeof
                (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                  (__eo_to_smt a)) =
              SmtType.BitVec 1 := by
          by_cases hNone :
              __smtx_typeof
                  (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                    (__eo_to_smt a)) =
                SmtType.None
          · exfalso
            exact hEqNN (by
              rw [hNone]
              simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                native_Teq])
          · by_cases hEq :
              __smtx_typeof
                  (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                    (__eo_to_smt a)) =
                SmtType.BitVec 1
            · exact hEq
            · exfalso
              exact hEqNN (by
                simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
                  native_Teq, hNone, hEq])
        have hExtNN :
            term_has_non_none_type
              (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
                (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          rw [hExtTy]
          simp
        rcases extract_args_of_non_none hExtNN with
          ⟨hiN, loN, w, hHiNum, hLoNum, hASmtTy, hLoNonneg,
            hWidth, hHiBound⟩
        have hIdxEq : hiN = loN := by
          have hTerm : SmtTerm.Numeral hiN = SmtTerm.Numeral loN :=
            hHiNum.symm.trans hLoNum
          cases hTerm
          rfl
        subst loN
        have hWidthNat :
            native_int_to_nat
                (native_zplus (native_zplus hiN 1) (native_zneg hiN)) =
              1 := by
          have hExtTy' := hExtTy
          rw [typeof_extract_eq, hHiNum, hASmtTy] at hExtTy'
          simp [__smtx_typeof_extract, native_ite, hLoNonneg, hWidth,
            hHiBound] at hExtTy'
          simpa using hExtTy'
        have hXSmtTy :=
          smt_typeof_subst_arg_eq_bitvec_of_type_eq
            hXTrans hATrans hXTyEq hASmtTy
        rw [typeof_eq_eq, typeof_extract_eq, hHiNum, hXSmtTy,
          smt_typeof_binary_one_one]
        simp [__smtx_typeof_extract, __smtx_typeof_eq, __smtx_typeof_guard,
          native_ite, native_Teq, hLoNonneg, hWidth, hHiBound, hWidthNat])
      hARec hTy

theorem substitute_simul_apply_is_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.is idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.is idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.is idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.is idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.is idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.is idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_is (__eo_typeof idx) (__eo_typeof X) ≠
            Term.Stuck at hApp
        exact eo_typeof_is_arg_ne_stuck_of_ne_stuck hApp)
      (fun X Y hXY => by
        change
          __eo_typeof_is (__eo_typeof idx) (__eo_typeof X) =
            __eo_typeof_is (__eo_typeof idx) (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
                (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.is idx a hTrans
        cases hCons : __eo_to_smt idx with
        | DtCons s d i =>
            change
              __smtx_typeof
                  (SmtTerm.Apply (SmtTerm.DtTester s d i)
                    (__eo_to_smt X)) ≠
                SmtType.None
            have hNN :
                term_has_non_none_type
                  (SmtTerm.Apply (SmtTerm.DtTester s d i)
                    (__eo_to_smt a)) := by
              unfold term_has_non_none_type
              have hRaw := hTrans
              unfold RuleProofs.eo_has_smt_translation at hRaw
              change
                __smtx_typeof
                    (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
                      (__eo_to_smt a)) ≠
                  SmtType.None at hRaw
              rw [hCons] at hRaw
              simpa [__eo_to_smt_tester] using hRaw
            have hASmtTy := dt_tester_arg_datatype_of_non_none hNN
            have hCtor := dt_tester_ctor_type_non_none_of_non_none hNN
            have hXSmtTy :=
              smt_typeof_subst_arg_eq_of_type_eq
                hXTrans hATrans hXTyEq hASmtTy
            rw [typeof_dt_tester_apply_eq, hXSmtTy]
            simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
              native_Teq, hCtor]
        | _ =>
            have hRaw := hTrans
            unfold RuleProofs.eo_has_smt_translation at hRaw
            change
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
                    (__eo_to_smt a)) ≠
                SmtType.None at hRaw
            rw [hCons] at hRaw
            simp [__eo_to_smt_tester, TranslationProofs.typeof_apply_none_eq]
              at hRaw)
      hARec hTy

theorem substitute_simul_apply_tuple_select_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a))
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
            (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.tuple_select idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_tuple_select (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        exact eo_typeof_tuple_select_arg_ne_stuck_of_ne_stuck hApp)
      (fun X Y hXY => by
        change
          __eo_typeof_tuple_select (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_tuple_select (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt X))
                (__eo_to_smt idx) (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.tuple_select idx a hTrans
        have hXSmtTyEq :
            __smtx_typeof (__eo_to_smt X) =
              __smtx_typeof (__eo_to_smt a) :=
          smt_typeof_subst_arg_eq_of_type_eq
            (T := __smtx_typeof (__eo_to_smt a))
            hXTrans hATrans hXTyEq rfl
        have hNN :
            __smtx_typeof
                (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt a))
                  (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None := by
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          change
            __smtx_typeof
                (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt a))
                  (__eo_to_smt idx) (__eo_to_smt a)) ≠
              SmtType.None at hRaw
          exact hRaw
        exact
          smt_typeof_tuple_select_non_none_of_arg_type_eq
            idx (__eo_to_smt a) (__eo_to_smt X) hXSmtTyEq hNN)
      hARec hTy

end SubstitutePreservationSupport
