module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationAtomGeneric
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationAtomGeneric
public import Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport
import all Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport

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

private theorem eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
    (f x y : Term)
    (hFTrans : RuleProofs.eo_has_smt_translation f)
    (hTy : __eo_typeof (Term.Apply (Term.Apply f x) y) ≠ Term.Stuck) :
    __eo_typeof (Term.Apply f x) ≠ Term.Stuck := by
  have hOuterGeneric :
      __eo_typeof (Term.Apply (Term.Apply f x) y) =
        __eo_typeof_apply (__eo_typeof (Term.Apply f x)) (__eo_typeof y) := by
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hFTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hFTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case FunType =>
      exfalso
      apply hFTrans
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hFTrans
          change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt b)) =
            SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply,
            TranslationProofs.smtx_typeof_none]
      case Apply f'' c =>
        cases f'' <;> try rfl
        case UOp op =>
          cases op <;> try rfl
          all_goals
            exfalso
            apply hFTrans
            exact TranslationProofs.typeof_apply_apply_none_head_eq
              (__eo_to_smt c) (__eo_to_smt b)
  rw [hOuterGeneric] at hTy
  exact SubstituteSupport.eo_typeof_apply_head_ne_stuck hTy

private def applyApplyApplyUOpNeedsSpecialType : UserOp -> Prop
  | UserOp.ite => True
  | UserOp.store => True
  | UserOp.bvite => True
  | UserOp.str_substr => True
  | UserOp.str_replace => True
  | UserOp.str_replace_all => True
  | UserOp.str_indexof => True
  | UserOp.str_update => True
  | UserOp.str_replace_re => True
  | UserOp.str_replace_re_all => True
  | UserOp.str_indexof_re => True
  | UserOp._at_strings_occur_index => True
  | UserOp._at_strings_occur_index_re => True
  | _ => False

private def applyApplyApplyApplyUOpNeedsSpecialType : UserOp -> Prop
  | UserOp._at_strings_replace_all_result => True
  | UserOp._at_strings_replace_re_all_result => True
  | _ => False

private theorem false_of_special_type_uop_has_smt_translation
    (op : UserOp)
    (hSpecial : applyApplyApplyUOpNeedsSpecialType op)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.UOp op)) :
    False := by
  cases op <;> simp [applyApplyApplyUOpNeedsSpecialType] at hSpecial
  all_goals
    exact hTrans (by
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none)

private theorem false_of_quaternary_special_partial_has_smt_translation
    (op : UserOp) (w : Term)
    (hSpecial : applyApplyApplyApplyUOpNeedsSpecialType op)
    (hTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) w)) :
    False := by
  cases op <;>
    simp [applyApplyApplyApplyUOpNeedsSpecialType] at hSpecial
  all_goals
    exact hTrans (by
      change
        __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt w)) =
          SmtType.None
      exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt w))

private theorem false_of_quaternary_special_uop_has_smt_translation
    (op : UserOp)
    (hSpecial : applyApplyApplyApplyUOpNeedsSpecialType op)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.UOp op)) :
    False := by
  cases op <;>
    simp [applyApplyApplyApplyUOpNeedsSpecialType] at hSpecial
  all_goals
    exact hTrans (by
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none)

private theorem var_has_smt_translation_of_ternary_application
    (name T y x a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) y) x) a)) :
    RuleProofs.eo_has_smt_translation (Term.Var name T) := by
  have hHead2Trans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Var name T) y) x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Apply (Term.Var name T) y) x) a (by rfl)
      (generic_apply_type_of_non_special_head_closed
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) y) x))
        (__eo_to_smt a)
        (TranslationProofs.eo_to_smt_apply_ne_dt_sel
          (Term.Apply (Term.Var name T) y) x)
        (TranslationProofs.eo_to_smt_apply_ne_dt_tester
          (Term.Apply (Term.Var name T) y) x))
      hTrans).1
  have hHead1Trans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Var name T) y) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Var name T) y) x (by rfl)
      (generic_apply_type_of_non_special_head_closed
        (__eo_to_smt (Term.Apply (Term.Var name T) y)) (__eo_to_smt x)
        (TranslationProofs.eo_to_smt_apply_ne_dt_sel
          (Term.Var name T) y)
        (TranslationProofs.eo_to_smt_apply_ne_dt_tester
          (Term.Var name T) y))
      hHead2Trans).1
  exact
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Var name T) y (by rfl)
      (SubstituteSupport.var_apply_generic_smt_type name T y)
      hHead1Trans).1

private theorem var_has_smt_translation_of_quaternary_application
    (name T w z y x : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y) x)) :
    RuleProofs.eo_has_smt_translation (Term.Var name T) := by
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y) x
      (by rfl)
      (generic_apply_type_of_non_special_head_closed
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y))
        (__eo_to_smt x)
        (TranslationProofs.eo_to_smt_apply_ne_dt_sel
          (Term.Apply (Term.Apply (Term.Var name T) w) z) y)
        (TranslationProofs.eo_to_smt_apply_ne_dt_tester
          (Term.Apply (Term.Apply (Term.Var name T) w) z) y))
      hTrans).1
  exact var_has_smt_translation_of_ternary_application
    name T w z y hHeadTrans

private theorem eo_typeof_apply_apply_residual_head_typeof_ne_stuck
    (g x a : Term)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotFunType : g ≠ Term.FunType)
    (hNoUpdate : ∀ idx, g ≠ Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate : ∀ idx, g ≠ Term.UOp1 UserOp1.tuple_update idx)
    (hNoApplyUOp :
      ∀ op y, applyApplyApplyUOpNeedsSpecialType op ->
        g ≠ Term.Apply (Term.UOp op) y)
    (hNoApplyApplyUOp :
      ∀ op w z, applyApplyApplyApplyUOpNeedsSpecialType op ->
        g ≠ Term.Apply (Term.Apply (Term.UOp op) w) z)
    (hTy : __eo_typeof (Term.Apply (Term.Apply g x) a) ≠ Term.Stuck) :
    __eo_typeof (Term.Apply g x) ≠ Term.Stuck := by
  have hOuterGeneric :
      __eo_typeof (Term.Apply (Term.Apply g x) a) =
        __eo_typeof_apply (__eo_typeof (Term.Apply g x)) (__eo_typeof a) := by
    cases g <;> try rfl
    · rename_i op
      exact False.elim (hNotUOp op rfl)
    · rename_i op idx
      cases op <;> try rfl
      · exact False.elim (hNoUpdate idx rfl)
      · exact False.elim (hNoTupleUpdate idx rfl)
    · rename_i head y
      cases head <;> try rfl
      · rename_i op
        cases op <;> try rfl
        all_goals
          exact False.elim
            (hNoApplyUOp _ y
              (by simp [applyApplyApplyUOpNeedsSpecialType]) rfl)
      · rename_i head' z
        cases head' <;> try rfl
        · rename_i op
          cases op <;> try rfl
          all_goals
            exact False.elim
              (hNoApplyApplyUOp _ z y
                (by simp [applyApplyApplyApplyUOpNeedsSpecialType]) rfl)
    · exact False.elim (hNotFunType rfl)
  rw [hOuterGeneric] at hTy
  exact SubstituteSupport.eo_typeof_apply_head_ne_stuck hTy

private theorem substitute_simul_apply_apply_atom_base_ne_head
    {isRename : Bool}
    (f y x xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ p q, f ≠ Term.Apply p q)
    (hNotVar : ∀ name T, f ≠ Term.Var name T)
    (target ySub xSub : Term)
    (hNotTarget : f ≠ target)
    (hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply f y) x) xs ts bvs ≠
        Term.Stuck)
    (hHeadShape :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply f y) x) xs ts bvs =
        Term.Apply (Term.Apply target ySub) xSub) :
    False := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply f y =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqBinder⟩
    cases hEqBinder
    let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    rcases
        SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
          f v vs x xs ts bvs hisr hxs hts hbvs
          (by simpa [binder] using hHeadNe)
      with ⟨binderSub, bodySub, hQuantRaw⟩
    have hQuant :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply f binder) x) xs ts bvs =
          __eo_mk_apply (Term.Apply f binderSub) bodySub := by
      simpa [binder] using hQuantRaw
    have hMkNe :
        __eo_mk_apply (Term.Apply f binderSub) bodySub ≠ Term.Stuck := by
      rw [← hQuant]
      simpa [binder] using hHeadNe
    have hMk :
        __eo_mk_apply (Term.Apply f binderSub) bodySub =
          Term.Apply (Term.Apply f binderSub) bodySub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply f binderSub) bodySub hMkNe
    have hExplicit :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply f binder) x) xs ts bvs =
          Term.Apply (Term.Apply f binderSub) bodySub := by
      rw [hQuant, hMk]
    have hShape :
        Term.Apply (Term.Apply f binderSub) bodySub =
          Term.Apply (Term.Apply target ySub) xSub := by
      rw [← hExplicit]
      simpa [binder] using hHeadShape
    injection hShape with hHeadEq _hBodyEq
    injection hHeadEq with hFEq _hBinderEq
    exact hNotTarget hFEq
  · let fSub := __substitute_simul_rec (Term.Boolean isRename) f xs ts bvs
    let y0Sub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
    let x0Sub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
    have hInner :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply f y) xs ts bvs =
          __eo_mk_apply fSub y0Sub := by
      simpa [fSub, y0Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) f y xs ts bvs hisr hxs hts hbvs
          (by
            intro q v vs hEq
            exact hNotApply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
    have hHeadRaw :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply f y) x) xs ts bvs =
          __eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply f y) xs ts bvs)
            x0Sub := by
      simpa [x0Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) (Term.Apply f y) x xs ts bvs
          hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hInnerNe : __eo_mk_apply fSub y0Sub ≠ Term.Stuck := by
      rw [← hInner]
      exact
        SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
          (by
            rw [← hHeadRaw]
            exact hHeadNe)
    have hFSubNe : fSub ≠ Term.Stuck :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
        hInnerNe
    have hFNotStuck : f ≠ Term.Stuck := by
      intro hFStuck
      subst f
      have hStuckSub :
          __substitute_simul_rec (Term.Boolean isRename) Term.Stuck xs ts bvs =
            Term.Stuck := by
        rfl
      exact hFSubNe (by simpa [fSub] using hStuckSub)
    have hFSubEq : fSub = f := by
      simpa [fSub] using
        SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
          f xs ts bvs hXsEnv hBvsEnv hTs
          hNotApply hNotVar hFNotStuck
          (by simpa [fSub] using hFSubNe)
    have hInnerMk : __eo_mk_apply fSub y0Sub = Term.Apply fSub y0Sub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        fSub y0Sub hInnerNe
    have hHeadMkNe :
        __eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply f y) xs ts bvs)
            x0Sub ≠
          Term.Stuck := by
      rw [← hHeadRaw]
      exact hHeadNe
    have hHeadMk :
        __eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply f y) xs ts bvs)
            x0Sub =
          Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply f y) xs ts bvs)
            x0Sub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f y) xs ts bvs)
        x0Sub hHeadMkNe
    have hExplicit :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply f y) x) xs ts bvs =
          Term.Apply (Term.Apply f y0Sub) x0Sub := by
      rw [hHeadRaw, hHeadMk, hInner, hInnerMk, hFSubEq]
    have hShape :
        Term.Apply (Term.Apply f y0Sub) x0Sub =
          Term.Apply (Term.Apply target ySub) xSub := by
      rw [← hExplicit]
      exact hHeadShape
    injection hShape with hHeadEq _hXEq
    injection hHeadEq with hFEq _hYEq
    exact hNotTarget hFEq

private theorem substitute_simul_rec_apply_apply_apply_apply_eq_of_ne_stuck
    {isRename : Bool}
    (g w z y x xs ts bvs : Term)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g w) z) y) x)
          xs ts bvs ≠
        Term.Stuck) :
    ∃ gSub wSub zSub ySub xSub,
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g w) z) y) x)
          xs ts bvs =
        Term.Apply
          (Term.Apply (Term.Apply (Term.Apply gSub wSub) zSub) ySub) xSub := by
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply (Term.Apply (Term.Apply g w) z) y =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqHead⟩
    cases hEqHead
    rcases
        SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
          (Term.Apply (Term.Apply g w) z) v vs x xs ts bvs
          hisr hxs hts hbvs hNe
      with ⟨binderSub, bodySub, hEq⟩
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.Apply (Term.Apply g w) z) binderSub) bodySub ≠
          Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hMk :
        __eo_mk_apply
            (Term.Apply (Term.Apply (Term.Apply g w) z) binderSub) bodySub =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Apply g w) z) binderSub) bodySub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.Apply (Term.Apply g w) z) binderSub) bodySub hMkNe
    exact ⟨g, w, z, binderSub, bodySub, by rw [hEq, hMk]⟩
  · let headSub :=
      __substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.Apply g w) z) y) xs ts bvs
    let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
    have hEq :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.Apply g w) z) y) x)
            xs ts bvs =
          __eo_mk_apply headSub xSub := by
      simpa [headSub, xSub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g w) z) y) x xs ts bvs
          hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hMkNe : __eo_mk_apply headSub xSub ≠ Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hHeadNe : headSub ≠ Term.Stuck :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
        hMkNe
    rcases
        SubstituteTranslatabilitySupport.substitute_simul_rec_apply_apply_apply_eq_apply_apply_apply_of_ne_stuck
          g w z y xs ts bvs hisr hxs hts hbvs
          (by simpa [headSub] using hHeadNe)
      with ⟨gSub, wSub, zSub, ySub, hHeadShape⟩
    have hMk : __eo_mk_apply headSub xSub = Term.Apply headSub xSub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        headSub xSub hMkNe
    have hHeadShape' :
        headSub =
          Term.Apply (Term.Apply (Term.Apply gSub wSub) zSub) ySub := by
      simpa [headSub] using hHeadShape
    exact ⟨gSub, wSub, zSub, ySub, xSub, by rw [hEq, hMk, hHeadShape']⟩

private theorem substitute_simul_apply_apply_var_head_ne_untranslatable_target
    {isRename : Bool}
    (name T y x xs ts bvs target ySub xSub : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T))
    (hVarTarget : Term.Var name T ≠ target)
    (hTargetNoTrans : ¬ RuleProofs.eo_has_smt_translation target)
    (hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs ≠
        Term.Stuck)
    (hHeadShape :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs =
        Term.Apply (Term.Apply target ySub) xSub) :
    False := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply (Term.Var name T) y =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqBinder⟩
    cases hEqBinder
    let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    rcases
        SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
          (Term.Var name T) v vs x xs ts bvs hisr hxs hts hbvs
          (by simpa [binder] using hHeadNe)
      with ⟨binderSub, bodySub, hQuantRaw⟩
    have hQuant :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name T) binder) x)
            xs ts bvs =
          __eo_mk_apply (Term.Apply (Term.Var name T) binderSub)
            bodySub := by
      simpa [binder] using hQuantRaw
    have hMkNe :
        __eo_mk_apply (Term.Apply (Term.Var name T) binderSub) bodySub ≠
          Term.Stuck := by
      rw [← hQuant]
      simpa [binder] using hHeadNe
    have hMk :
        __eo_mk_apply (Term.Apply (Term.Var name T) binderSub) bodySub =
          Term.Apply (Term.Apply (Term.Var name T) binderSub) bodySub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.Var name T) binderSub) bodySub hMkNe
    have hExplicit :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name T) binder) x)
            xs ts bvs =
          Term.Apply (Term.Apply (Term.Var name T) binderSub) bodySub := by
      rw [hQuant, hMk]
    have hShape :
        Term.Apply (Term.Apply (Term.Var name T) binderSub) bodySub =
          Term.Apply (Term.Apply target ySub) xSub := by
      rw [← hExplicit]
      simpa [binder] using hHeadShape
    injection hShape with hHeadEq _hBodyEq
    injection hHeadEq with hVarEq _hBinderEq
    exact hVarTarget hVarEq
  · let varSub :=
      __substitute_simul_rec (Term.Boolean isRename)
        (Term.Var name T) xs ts bvs
    let y0Sub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
    let x0Sub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
    have hInner :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name T) y) xs ts bvs =
          __eo_mk_apply varSub y0Sub := by
      simpa [varSub, y0Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) (Term.Var name T) y xs ts bvs
          hisr hxs hts hbvs (by intro q v vs hEq; cases hEq)
    have hHeadRaw :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs =
          __eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Var name T) y) xs ts bvs)
            x0Sub := by
      simpa [x0Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) (Term.Apply (Term.Var name T) y)
          x xs ts bvs hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hInnerNe : __eo_mk_apply varSub y0Sub ≠ Term.Stuck := by
      rw [← hInner]
      exact
        SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
          (by
            rw [← hHeadRaw]
            exact hHeadNe)
    have hVarNe : varSub ≠ Term.Stuck :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
        hInnerNe
    have hInnerMk : __eo_mk_apply varSub y0Sub = Term.Apply varSub y0Sub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        varSub y0Sub hInnerNe
    have hHeadMkNe :
        __eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Var name T) y) xs ts bvs)
            x0Sub ≠
          Term.Stuck := by
      rw [← hHeadRaw]
      exact hHeadNe
    have hHeadMk :
        __eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Var name T) y) xs ts bvs)
            x0Sub =
          Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Var name T) y) xs ts bvs)
            x0Sub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name T) y) xs ts bvs)
        x0Sub hHeadMkNe
    have hExplicit :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs =
          Term.Apply (Term.Apply varSub y0Sub) x0Sub := by
      rw [hHeadRaw, hHeadMk, hInner, hInnerMk]
    have hShape :
        Term.Apply (Term.Apply varSub y0Sub) x0Sub =
          Term.Apply (Term.Apply target ySub) xSub := by
      rw [← hExplicit]
      exact hHeadShape
    injection hShape with hHeadEq _hXEq
    injection hHeadEq with hVarSubEq _hYEq
    have hVarSubTrans : RuleProofs.eo_has_smt_translation varSub := by
      simpa [varSub] using
        SubstituteSupport.substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
          name T xs ts bvs hXsEnv hBvsEnv hTs hVarTrans
          (by simpa [varSub] using hVarNe)
    exact hTargetNoTrans (by simpa [varSub, hVarSubEq] using hVarSubTrans)

private theorem substitute_simul_apply_apply_apply_atom_base_ne_head
    {isRename : Bool}
    (f w z y xs ts bvs target wSub zSub ySub : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ p q, f ≠ Term.Apply p q)
    (hNotVar : ∀ name T, f ≠ Term.Var name T)
    (hNotTarget : f ≠ target)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply f w) z) y) xs ts bvs ≠
        Term.Stuck)
    (hShape :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply f w) z) y) xs ts bvs =
        Term.Apply (Term.Apply (Term.Apply target wSub) zSub) ySub) :
    False := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply (Term.Apply f w) z =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqBinder⟩
    cases hEqBinder
    let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    rcases
        SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
          (Term.Apply f w) v vs y xs ts bvs hisr hxs hts hbvs
          (by simpa [binder] using hNe)
      with ⟨binderSub, bodySub, hQuantRaw⟩
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.Apply f w) binderSub) bodySub ≠ Term.Stuck := by
      rw [← hQuantRaw]
      simpa [binder] using hNe
    have hMk :
        __eo_mk_apply (Term.Apply (Term.Apply f w) binderSub) bodySub =
          Term.Apply
            (Term.Apply (Term.Apply f w) binderSub) bodySub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.Apply f w) binderSub) bodySub hMkNe
    have hExplicit :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply f w) binder) y) xs ts bvs =
          Term.Apply
            (Term.Apply (Term.Apply f w) binderSub) bodySub := by
      rw [hQuantRaw, hMk]
    have hEq :
        Term.Apply (Term.Apply (Term.Apply f w) binderSub) bodySub =
          Term.Apply (Term.Apply (Term.Apply target wSub) zSub) ySub := by
      rw [← hExplicit]
      simpa [binder] using hShape
    injection hEq with hHeadEq _hBodyEq
    injection hHeadEq with hHeadEq' _hBinderEq
    injection hHeadEq' with hFEq _hWEq
    exact hNotTarget hFEq
  · let innerSub :=
      __substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply (Term.Apply f w) z) xs ts bvs
    let y0Sub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
    have hRaw :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply f w) z) y) xs ts bvs =
          __eo_mk_apply innerSub y0Sub := by
      simpa [innerSub, y0Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) (Term.Apply (Term.Apply f w) z) y
          xs ts bvs hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hMkNe : __eo_mk_apply innerSub y0Sub ≠ Term.Stuck := by
      rw [← hRaw]
      exact hNe
    have hInnerNe : innerSub ≠ Term.Stuck :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
        hMkNe
    have hMk : __eo_mk_apply innerSub y0Sub = Term.Apply innerSub y0Sub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        innerSub y0Sub hMkNe
    have hInnerShape :
        innerSub = Term.Apply (Term.Apply target wSub) zSub := by
      have hEq :
          Term.Apply innerSub y0Sub =
            Term.Apply
              (Term.Apply (Term.Apply target wSub) zSub) ySub := by
        rw [← hMk, ← hRaw]
        exact hShape
      injection hEq
    exact
      substitute_simul_apply_apply_atom_base_ne_head
        f w z xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar
        target wSub zSub hNotTarget
        (by simpa [innerSub] using hInnerNe)
        (by simpa [innerSub] using hInnerShape)

private theorem substitute_simul_apply_apply_apply_var_head_ne_untranslatable_target
    {isRename : Bool}
    (name T w z y xs ts bvs target wSub zSub ySub : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T))
    (hVarTarget : Term.Var name T ≠ target)
    (hTargetNoTrans : ¬ RuleProofs.eo_has_smt_translation target)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y)
          xs ts bvs ≠
        Term.Stuck)
    (hShape :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y)
          xs ts bvs =
        Term.Apply (Term.Apply (Term.Apply target wSub) zSub) ySub) :
    False := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply (Term.Apply (Term.Var name T) w) z =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqBinder⟩
    cases hEqBinder
    let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    rcases
        SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
          (Term.Apply (Term.Var name T) w) v vs y xs ts bvs
          hisr hxs hts hbvs (by simpa [binder] using hNe)
      with ⟨binderSub, bodySub, hQuantRaw⟩
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.Apply (Term.Var name T) w) binderSub)
            bodySub ≠
          Term.Stuck := by
      rw [← hQuantRaw]
      simpa [binder] using hNe
    have hMk :
        __eo_mk_apply
            (Term.Apply (Term.Apply (Term.Var name T) w) binderSub)
            bodySub =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Var name T) w) binderSub)
            bodySub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.Apply (Term.Var name T) w) binderSub)
        bodySub hMkNe
    have hExplicit :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var name T) w) binder) y)
            xs ts bvs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Var name T) w) binderSub)
            bodySub := by
      rw [hQuantRaw, hMk]
    have hEq :
        Term.Apply
            (Term.Apply (Term.Apply (Term.Var name T) w) binderSub)
            bodySub =
          Term.Apply (Term.Apply (Term.Apply target wSub) zSub) ySub := by
      rw [← hExplicit]
      simpa [binder] using hShape
    injection hEq with hHeadEq _hBodyEq
    injection hHeadEq with hHeadEq' _hBinderEq
    injection hHeadEq' with hVarEq _hWEq
    exact hVarTarget hVarEq
  · let innerSub :=
      __substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.Var name T) w) z) xs ts bvs
    let y0Sub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
    have hRaw :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.Var name T) w) z) y)
            xs ts bvs =
          __eo_mk_apply innerSub y0Sub := by
      simpa [innerSub, y0Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name T) w) z) y
          xs ts bvs hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hMkNe : __eo_mk_apply innerSub y0Sub ≠ Term.Stuck := by
      rw [← hRaw]
      exact hNe
    have hInnerNe : innerSub ≠ Term.Stuck :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
        hMkNe
    have hMk : __eo_mk_apply innerSub y0Sub = Term.Apply innerSub y0Sub :=
      SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        innerSub y0Sub hMkNe
    have hInnerShape :
        innerSub = Term.Apply (Term.Apply target wSub) zSub := by
      have hEq :
          Term.Apply innerSub y0Sub =
            Term.Apply
              (Term.Apply (Term.Apply target wSub) zSub) ySub := by
        rw [← hMk, ← hRaw]
        exact hShape
      injection hEq
    exact
      substitute_simul_apply_apply_var_head_ne_untranslatable_target
        name T w z xs ts bvs target wSub zSub
        hXsEnv hBvsEnv hTs hVarTrans hVarTarget hTargetNoTrans
        (by simpa [innerSub] using hInnerNe)
        (by simpa [innerSub] using hInnerShape)

/--
Substitution cannot change the head of a translatable quaternary application
into an untranslatable atom.

The applied-head case has one more constructor in its substitution spine, an
atomic head is preserved structurally, and a variable head can only be
replaced by one of the translatable simultaneous-substitution arguments.
-/
theorem substitute_simul_apply_apply_apply_head_ne_untranslatable_target
    {isRename : Bool}
    (g w z y x xs ts bvs target gSub wSub zSub ySub : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotTarget : g ≠ target)
    (hTargetNoTrans : ¬ RuleProofs.eo_has_smt_translation target)
    (hTargetNotApply : ∀ p q, Term.Apply p q ≠ target)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.Apply g w) z) y) x))
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g w) z) y) xs ts bvs ≠
        Term.Stuck)
    (hShape :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g w) z) y) xs ts bvs =
        Term.Apply (Term.Apply (Term.Apply gSub wSub) zSub) ySub) :
    gSub ≠ target := by
  intro hGSub
  subst gSub
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  cases g with
  | Var name T =>
      exact
        substitute_simul_apply_apply_apply_var_head_ne_untranslatable_target
          name T w z y xs ts bvs target wSub zSub ySub
          hXsEnv hBvsEnv hTs
          (var_has_smt_translation_of_quaternary_application
            name T w z y x hFTrans)
          hNotTarget hTargetNoTrans hNe hShape
  | Apply f v =>
      rcases
          substitute_simul_rec_apply_apply_apply_apply_eq_of_ne_stuck
            f v w z y xs ts bvs hisr hxs hts hbvs hNe
        with ⟨fSub, vSub, wSub', zSub', ySub', hShape4⟩
      rw [hShape4] at hShape
      have hHeadEq : Term.Apply fSub vSub = target := by
        injection hShape with hMidEq _
        injection hMidEq with hInnerEq _
        injection hInnerEq
      exact hTargetNotApply fSub vSub hHeadEq
  | _ =>
      exact
        substitute_simul_apply_apply_apply_atom_base_ne_head
          _ w z y xs ts bvs target wSub zSub ySub
          hXsEnv hBvsEnv hTs
          (by intro p q h; cases h)
          (by intro name T h; cases h)
          hNotTarget hNe hShape

theorem substitute_simul_apply_apply_var_head_generic_head_typeof_ne_stuck
    {isRename : Bool}
    (name T x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Var name T) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Var name T) x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name T) x) xs ts bvs) ≠
      Term.Stuck := by
  let varSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Var name T) xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename)
      (Term.Apply (Term.Var name T) x) xs ts bvs
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
          (__eo_to_smt a) := by
    rfl
  have hOuterGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
            (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Var name T) x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply (Term.Var name T) x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel (Term.Var name T) x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester (Term.Var name T) x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Var name T) x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Var name T) x) a hOuterTranslate hOuterGeneric
      hFTrans).1
  have hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Var name T) x (by rfl)
      (SubstituteSupport.var_apply_generic_smt_type name T x)
      hHeadTrans).1
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply varSub xSub := by
    simpa [headSub, varSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Var name T) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.Var name T) x) a xs ts bvs
        hisr hxs hts hbvs
        hNotBinderOuter
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply varSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hVarNe : varSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hVarSubTrans :
      RuleProofs.eo_has_smt_translation varSub := by
    simpa [varSub] using
      SubstituteSupport.substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
        name T xs ts bvs hXsEnv hBvsEnv hTs hVarTrans
        (by simpa [varSub] using hVarNe)
  have hHeadMk : __eo_mk_apply varSub xSub = Term.Apply varSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck varSub xSub hHeadMkNe
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterApplyTy' :
      __eo_typeof (Term.Apply (Term.Apply varSub xSub) aSub) ≠
        Term.Stuck := by
    simpa [hHeadRaw, hHeadMk] using hOuterApplyTy
  have hHeadApplyTy :
      __eo_typeof (Term.Apply varSub xSub) ≠ Term.Stuck :=
    eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
      varSub xSub aSub hVarSubTrans hOuterApplyTy'
  simpa [headSub, hHeadRaw, hHeadMk] using hHeadApplyTy

theorem substitute_simul_apply_apply_atom_base_generic_head_typeof_ne_stuck
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hInnerTranslate :
      __eo_to_smt (Term.Apply g x) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x))
    (hInnerGeneric :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt g)) (__smtx_typeof (__eo_to_smt x)))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  let gSub := __substitute_simul_rec (Term.Boolean isRename) g xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ts bvs
  have hOuterGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel g x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester g x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply g x) a hOuterTranslate hOuterGeneric hFTrans).1
  have hGTrans : RuleProofs.eo_has_smt_translation g :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      g x hInnerTranslate hInnerGeneric hHeadTrans).1
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply gSub xSub := by
    simpa [headSub, gSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) g x xs ts bvs hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotApply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotBinderOuter q v vs hEq)
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply gSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hGSubNe : gSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubEq : gSub = g := by
    simpa [gSub] using
      SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
        g xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        (by simpa [gSub] using hGSubNe)
  have hGSubTrans : RuleProofs.eo_has_smt_translation gSub := by
    simpa [hGSubEq] using hGTrans
  have hHeadMk : __eo_mk_apply gSub xSub = Term.Apply gSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck gSub xSub hHeadMkNe
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterApplyTy' :
      __eo_typeof (Term.Apply (Term.Apply gSub xSub) aSub) ≠
        Term.Stuck := by
    simpa [hHeadRaw, hHeadMk] using hOuterApplyTy
  have hHeadApplyTy :
      __eo_typeof (Term.Apply gSub xSub) ≠ Term.Stuck :=
    eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
      gSub xSub aSub hGSubTrans hOuterApplyTy'
  simpa [headSub, hHeadRaw, hHeadMk] using hHeadApplyTy

theorem substitute_simul_apply_apply_atom_head_typeof_ne_stuck_of_head_translation
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hGTrans : RuleProofs.eo_has_smt_translation g)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  let gSub := __substitute_simul_rec (Term.Boolean isRename) g xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply gSub xSub := by
    simpa [headSub, gSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) g x xs ts bvs hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotApply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotBinderOuter q v vs hEq)
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply gSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hGSubNe : gSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubEq : gSub = g := by
    simpa [gSub] using
      SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
        g xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        (by simpa [gSub] using hGSubNe)
  have hGSubTrans : RuleProofs.eo_has_smt_translation gSub := by
    simpa [hGSubEq] using hGTrans
  have hHeadMk : __eo_mk_apply gSub xSub = Term.Apply gSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck gSub xSub hHeadMkNe
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterApplyTy' :
      __eo_typeof (Term.Apply (Term.Apply gSub xSub) aSub) ≠
        Term.Stuck := by
    simpa [hHeadRaw, hHeadMk] using hOuterApplyTy
  have hHeadApplyTy :
      __eo_typeof (Term.Apply gSub xSub) ≠ Term.Stuck :=
    eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
      gSub xSub aSub hGSubTrans hOuterApplyTy'
  simpa [headSub, hHeadRaw, hHeadMk] using hHeadApplyTy

theorem substitute_simul_apply_apply_atom_residual_head_typeof_ne_stuck
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  let gSub := __substitute_simul_rec (Term.Boolean isRename) g xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ts bvs
  have hNotStuck : g ≠ Term.Stuck := by
    intro hEq
    subst g
    apply hFTrans
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
            (__eo_to_smt a)) =
        SmtType.None
    simp [__smtx_typeof, __smtx_typeof_apply,
      TranslationProofs.smtx_typeof_none]
  have hNotFunType : g ≠ Term.FunType := by
    intro hEq
    subst g
    apply hFTrans
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
            (__eo_to_smt a)) =
        SmtType.None
    simp [__smtx_typeof, __smtx_typeof_apply,
      TranslationProofs.smtx_typeof_none]
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply gSub xSub := by
    simpa [headSub, gSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) g x xs ts bvs hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotApply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotBinderOuter q v vs hEq)
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply gSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hGSubNe : gSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubEq : gSub = g := by
    simpa [gSub] using
      SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
        g xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        (by simpa [gSub] using hGSubNe)
  have hHeadMk : __eo_mk_apply gSub xSub = Term.Apply gSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck gSub xSub hHeadMkNe
  have hHeadShape : headSub = Term.Apply g xSub := by
    rw [hHeadRaw, hHeadMk, hGSubEq]
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterGeneric :
      __eo_typeof (Term.Apply headSub aSub) =
        __eo_typeof_apply (__eo_typeof headSub) (__eo_typeof aSub) := by
    rw [hHeadShape]
    cases g <;> try rfl
    · rename_i op
      exact False.elim (hNotUOp op rfl)
    · rename_i op idx
      cases op <;> try rfl
      · exact False.elim (hNoUpdate ⟨idx, rfl⟩)
      · exact False.elim (hNoTupleUpdate ⟨idx, rfl⟩)
    · rename_i f y
      exact False.elim (hNotApply f y rfl)
    · exact False.elim (hNotFunType rfl)
  rw [hOuterGeneric] at hOuterApplyTy
  exact SubstituteSupport.eo_typeof_apply_head_ne_stuck hOuterApplyTy

theorem substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) =
        __eo_typeof (Term.Apply g x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply g x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ts bvs
  have hGenericOuter :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel g x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester g x)
  have hArgs :=
    SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply g x) a hOuterTranslate hGenericOuter hFTrans
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs hNotBinderOuter
  have hTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMk :
      __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hTyMk
  have hHeadBoth := hRecHead hHeadTrans (by simpa [headSub] using hHeadSubTy)
  have hATy : __eo_typeof aSub ≠ Term.Stuck := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
        (Term.Apply g x) a xs ts bvs hXsEnv hBvsEnv hTs
        hNotBinderOuter hHeadBoth.2 hTy
  have hABoth := hRecA hATrans hATy
  refine ⟨?_, ?_⟩
  · exact
      SubstituteSupport.substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
        (Term.Apply g x) a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
        hHeadTrans hHeadBoth.2 hHeadBoth.1 hABoth.1 hTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
        (Term.Apply g x) a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
        hHeadBoth.2 hABoth.2 hTy

theorem substitute_simul_apply_apply_uop_generic_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
          (__eo_to_smt y))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) x) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.UOp op) x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) x) xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
        __eo_typeof y ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    SubstituteSupport.substitute_simul_rec_uop_eq_self
      op xs ts bvs hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x) xs ts bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.UOp op) x) y xs ts bvs
        hisr hxs hts hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub ≠
        Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp op) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp op) xSub) ySub (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
            (__eo_to_smt y)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)))
          (__smtx_typeof (__eo_to_smt y)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply (Term.UOp op) x)) (__eo_to_smt y)
      (SubstituteSupport.eo_to_smt_uop_apply_ne_dt_sel op x)
      (SubstituteSupport.eo_to_smt_uop_apply_ne_dt_tester op x)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hFTransEo
  rcases apply_args_have_smt_translation_of_non_none hGeneric hNN with
    ⟨hHeadTransEo, hYTransEo⟩
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hHeadTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  have hUnary : SubstituteSupport.substitute_uopHasUnarySmtTranslation op = true :=
    SubstituteSupport.substitute_uopHasUnarySmtTranslation_eq_true_of_apply_translation
      hHeadTrans
  have hTypeSupport :=
    SubstituteSupport.eo_typeof_apply_apply_uop_generic_support_of_unary_smt_translation
      hUnary
  rcases hTypeSupport.1 xSub ySub hTyApply with ⟨hHeadSubTy, hYSubTy⟩
  have hHeadSubTy' :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) x) xs ts bvs) ≠
        Term.Stuck := by
    rw [hInnerSub, hInnerMk]
    exact hHeadSubTy
  have hHeadBoth := hRecHead hHeadTrans hHeadSubTy'
  have hYBoth := hRecY hYTrans (by simpa [ySub] using hYSubTy)
  have hHeadTy :
      __eo_typeof (Term.Apply (Term.UOp op) xSub) =
        __eo_typeof (Term.Apply (Term.UOp op) x) := by
    simpa [hInnerSub, hInnerMk] using hHeadBoth.1
  have hYTy : __eo_typeof ySub = __eo_typeof y := by
    simpa [ySub] using hYBoth.1
  refine ⟨?_, ?_⟩
  · rw [hSubstEq, hInnerMk, hOuterMk]
    exact hTypeSupport.2 x xSub y ySub hHeadTy hYTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
        (Term.Apply (Term.UOp op) x) y xs ts bvs
        hXsEnv hBvsEnv hTs hNotBinder hHeadBoth.2 hYBoth.2 hTy

theorem substitute_simul_apply_apply_var_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (name T x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Var name T) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Var name T) x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Var name T) x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name T) x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name T) x) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.Var name T) x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name T) x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name T) x) xs ts bvs) ≠
        Term.Stuck)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.Var name T) x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) := by
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
          (__eo_to_smt a) := by
    rfl
  have hGenericOuter :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
            (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Var name T) x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply (Term.Var name T) x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel (Term.Var name T) x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester (Term.Var name T) x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Var name T) x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Var name T) x) a hOuterTranslate hGenericOuter
      hFTrans).1
  exact
    substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
      (Term.Var name T) x a xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinderOuter hOuterTranslate
      hFTrans hRecHead hRecA hHeadSubTy hTy

/--
Residual higher-order application head non-vacuity.

In the fully generic `((g x) a)` branch, the outer substituted application
being typeable forces the substituted applied head `(g x)[xs := ts]` to be
typeable as well. This is the remaining operator-spine non-vacuity obligation
shared with the old type-only substitution engine.
-/
theorem substitute_simul_apply_apply_branch_residual_head_typeof_ne_stuck
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hUOp : ApplyApplyUOpBranchExclusions g)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hApplyUOp : ApplyApplyApplyUOpBranchExclusions g)
    (hApplyApplyUOp : ApplyApplyApplyApplyUOpBranchExclusions g)
    (hNotUOpTop : ∀ op, g ≠ Term.UOp op)
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  cases g with
  | Var name T =>
      exact
        substitute_simul_apply_apply_var_head_generic_head_typeof_ne_stuck
          name T x a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
          hFTrans hTy
  | Apply f y =>
      have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
      have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
      have hts : ts ≠ Term.Stuck :=
        SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      let headSub :=
        __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply f y) x) xs ts bvs
      let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
      have hOuterRaw :
          __substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply (Term.Apply f y) x) a) xs ts bvs =
            __eo_mk_apply headSub aSub := by
        simpa [headSub, aSub] using
          SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean isRename) (Term.Apply (Term.Apply f y) x) a xs ts bvs
            hisr hxs hts hbvs hNotBinderOuter
      have hOuterTyMk :
          __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
        rwa [hOuterRaw] at hTy
      have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
        SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
      have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
        SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
      have hOuterApplyTy :
          __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
        rwa [hOuterMk] at hOuterTyMk
      have hHeadNe : headSub ≠ Term.Stuck :=
        SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
          (Term.Apply (Term.Apply f y) x) a xs ts bvs
          hXsEnv hBvsEnv hTs hNotBinderOuter (by
            rw [hOuterRaw]
            exact hOuterTyMk)
      rcases
          SubstituteTranslatabilitySupport.substitute_simul_rec_apply_apply_eq_apply_apply_of_ne_stuck
            f y x xs ts bvs hisr hxs hts hbvs
            (by simpa [headSub] using hHeadNe)
        with ⟨fSub, ySub, xSub, hHeadShape⟩
      have hOuterTyShape :
          __eo_typeof
              (Term.Apply (Term.Apply (Term.Apply fSub ySub) xSub) aSub) ≠
            Term.Stuck := by
        simpa [headSub, hHeadShape] using hOuterApplyTy
      have hNoApplyUOp :
          ∀ op z, applyApplyApplyUOpNeedsSpecialType op ->
            Term.Apply fSub ySub ≠ Term.Apply (Term.UOp op) z := by
        intro op z hSpecial hEq
        cases hEq
        by_cases hFUOp : ∃ op0, f = Term.UOp op0
        ·
            rcases hFUOp with ⟨op0, rfl⟩
            have hHeadShape2 :
                __substitute_simul_rec (Term.Boolean isRename)
                    (Term.Apply (Term.Apply (Term.UOp op0) y) x) xs ts bvs =
                  Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
              simpa [headSub] using hHeadShape
            have hOpEq : op0 = op := by
              by_cases hBinder :
                  ∃ q v vs,
                    Term.Apply (Term.UOp op0) y =
                      Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              · rcases hBinder with ⟨q, v, vs, hEqBinder⟩
                cases hEqBinder
                let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
                rcases
                    SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
                      (Term.UOp op0) v vs x xs ts bvs hisr hxs hts hbvs
                      (by simpa [headSub, binder] using hHeadNe)
                  with ⟨binderSub, bodySub, hQuantRaw⟩
                have hQuant :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Apply (Term.UOp op0) binder) x)
                        xs ts bvs =
                      __eo_mk_apply (Term.Apply (Term.UOp op0) binderSub)
                        bodySub := by
                  simpa [binder] using hQuantRaw
                have hMkNe :
                    __eo_mk_apply (Term.Apply (Term.UOp op0) binderSub)
                        bodySub ≠
                      Term.Stuck := by
                  rw [← hQuant]
                  simpa [headSub, binder] using hHeadNe
                have hMk :
                    __eo_mk_apply (Term.Apply (Term.UOp op0) binderSub)
                        bodySub =
                      Term.Apply (Term.Apply (Term.UOp op0) binderSub) bodySub :=
                  SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                    (Term.Apply (Term.UOp op0) binderSub) bodySub hMkNe
                have hExplicit :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Apply (Term.UOp op0) binder) x)
                        xs ts bvs =
                      Term.Apply (Term.Apply (Term.UOp op0) binderSub) bodySub := by
                  rw [hQuant, hMk]
                have hShape :
                    Term.Apply (Term.Apply (Term.UOp op0) binderSub) bodySub =
                      Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
                  rw [← hExplicit]
                  simpa [binder] using hHeadShape2
                injection hShape with hHeadEq _hBodyEq
                injection hHeadEq with hOpEq _hBinderEq
                cases hOpEq
                rfl
              · let y0Sub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
                let x0Sub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
                have hUOpSub :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.UOp op0) xs ts bvs =
                      Term.UOp op0 :=
                  SubstituteSupport.substitute_simul_rec_uop_eq_self
                    op0 xs ts bvs hXsEnv hBvsEnv hTs
                have hInner :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.UOp op0) y) xs ts bvs =
                      __eo_mk_apply (Term.UOp op0) y0Sub := by
                  have hApply :=
                    SubstituteSupport.substitute_simul_rec_apply
                      (Term.Boolean isRename) (Term.UOp op0) y xs ts bvs
                      hisr hxs hts hbvs
                      (by intro q v vs hEq; cases hEq)
                  simpa [y0Sub, hUOpSub] using hApply
                have hHeadRaw :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Apply (Term.UOp op0) y) x) xs ts bvs =
                      __eo_mk_apply
                        (__substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp op0) y) xs ts bvs)
                        x0Sub := by
                  simpa [x0Sub] using
                    SubstituteSupport.substitute_simul_rec_apply
                      (Term.Boolean isRename) (Term.Apply (Term.UOp op0) y)
                      x xs ts bvs hisr hxs hts hbvs
                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                have hInnerNe :
                    __eo_mk_apply (Term.UOp op0) y0Sub ≠ Term.Stuck := by
                  rw [← hInner]
                  exact
                    SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
                      (by
                        rw [← hHeadRaw]
                        simpa [headSub] using hHeadNe)
                have hInnerMk :
                    __eo_mk_apply (Term.UOp op0) y0Sub =
                      Term.Apply (Term.UOp op0) y0Sub :=
                  SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                    (Term.UOp op0) y0Sub hInnerNe
                have hHeadMkNe :
                    __eo_mk_apply
                        (__substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp op0) y) xs ts bvs)
                        x0Sub ≠
                      Term.Stuck := by
                  rw [← hHeadRaw]
                  simpa [headSub] using hHeadNe
                have hHeadMk :
                    __eo_mk_apply
                        (__substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp op0) y) xs ts bvs)
                        x0Sub =
                      Term.Apply
                        (__substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp op0) y) xs ts bvs)
                        x0Sub :=
                  SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                    (__substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.UOp op0) y) xs ts bvs)
                    x0Sub hHeadMkNe
                have hExplicit :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Apply (Term.UOp op0) y) x) xs ts bvs =
                      Term.Apply (Term.Apply (Term.UOp op0) y0Sub) x0Sub := by
                  rw [hHeadRaw, hHeadMk, hInner, hInnerMk]
                have hShape :
                    Term.Apply (Term.Apply (Term.UOp op0) y0Sub) x0Sub =
                      Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
                  rw [← hExplicit]
                  exact hHeadShape2
                injection hShape with hHeadEq _hXEq
                injection hHeadEq with hOpEq _hYEq
                cases hOpEq
                rfl
            subst op0
            cases op <;> simp [applyApplyApplyUOpNeedsSpecialType] at hSpecial
            all_goals
              first
              | exact hApplyUOp.notIte ⟨y, rfl⟩
              | exact hApplyUOp.notStore ⟨y, rfl⟩
              | exact hApplyUOp.notBvite ⟨y, rfl⟩
              | exact hApplyUOp.notStrSubstr ⟨y, rfl⟩
              | exact hApplyUOp.notStrReplace ⟨y, rfl⟩
              | exact hApplyUOp.notStrReplaceAll ⟨y, rfl⟩
              | exact hApplyUOp.notStrIndexof ⟨y, rfl⟩
              | exact hApplyUOp.notStrUpdate ⟨y, rfl⟩
              | exact hApplyUOp.notStrReplaceRe ⟨y, rfl⟩
              | exact hApplyUOp.notStrReplaceReAll ⟨y, rfl⟩
              | exact hApplyUOp.notStrIndexofRe ⟨y, rfl⟩
              | exact hApplyUOp.notStringsOccurIndex ⟨y, rfl⟩
              | exact hApplyUOp.notStringsOccurIndexRe ⟨y, rfl⟩
              | exact hFTrans (by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply
                          (SmtTerm.Apply
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
                            (__eo_to_smt x))
                          (__eo_to_smt a)) =
                      SmtType.None
                  simp [__smtx_typeof, __smtx_typeof_apply,
                    TranslationProofs.smtx_typeof_none])
        · by_cases hFVar : ∃ name T, f = Term.Var name T
          · rcases hFVar with ⟨name, T, rfl⟩
            have hOuterTranslate :
                __eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.Apply (Term.Var name T) y) x) a) =
                  SmtTerm.Apply
                    (__eo_to_smt
                      (Term.Apply (Term.Apply (Term.Var name T) y) x))
                    (__eo_to_smt a) := by
              rfl
            have hOuterGeneric :
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt
                        (Term.Apply (Term.Apply (Term.Var name T) y) x))
                      (__eo_to_smt a)) =
                  __smtx_typeof_apply
                    (__smtx_typeof
                      (__eo_to_smt
                        (Term.Apply (Term.Apply (Term.Var name T) y) x)))
                    (__smtx_typeof (__eo_to_smt a)) :=
              generic_apply_type_of_non_special_head_closed
                (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) y) x))
                (__eo_to_smt a)
                (TranslationProofs.eo_to_smt_apply_ne_dt_sel
                  (Term.Apply (Term.Var name T) y) x)
                (TranslationProofs.eo_to_smt_apply_ne_dt_tester
                  (Term.Apply (Term.Var name T) y) x)
            have hHead2Trans :
                RuleProofs.eo_has_smt_translation
                  (Term.Apply (Term.Apply (Term.Var name T) y) x) :=
              (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                (Term.Apply (Term.Apply (Term.Var name T) y) x) a
                hOuterTranslate hOuterGeneric hFTrans).1
            have hHead1Translate :
                __eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) y) x) =
                  SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) y))
                    (__eo_to_smt x) := by
              rfl
            have hHead1Generic :
                __smtx_typeof
                    (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) y))
                      (__eo_to_smt x)) =
                  __smtx_typeof_apply
                    (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Var name T) y)))
                    (__smtx_typeof (__eo_to_smt x)) :=
              generic_apply_type_of_non_special_head_closed
                (__eo_to_smt (Term.Apply (Term.Var name T) y)) (__eo_to_smt x)
                (TranslationProofs.eo_to_smt_apply_ne_dt_sel
                  (Term.Var name T) y)
                (TranslationProofs.eo_to_smt_apply_ne_dt_tester
                  (Term.Var name T) y)
            have hHead1Trans :
                RuleProofs.eo_has_smt_translation
                  (Term.Apply (Term.Var name T) y) :=
              (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                (Term.Apply (Term.Var name T) y) x
                hHead1Translate hHead1Generic hHead2Trans).1
            have hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T) :=
              (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                (Term.Var name T) y (by rfl)
                (SubstituteSupport.var_apply_generic_smt_type name T y)
                hHead1Trans).1
            have hHeadShape2 :
                __substitute_simul_rec (Term.Boolean isRename)
                    (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs =
                  Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
              simpa [headSub] using hHeadShape
            by_cases hBinder :
                ∃ q v vs,
                  Term.Apply (Term.Var name T) y =
                    Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            · rcases hBinder with ⟨q, v, vs, hEqBinder⟩
              cases hEqBinder
              let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
              rcases
                  SubstituteTranslatabilitySupport.substitute_simul_quant_apply_shape_of_ne_stuck
                    (Term.Var name T) v vs x xs ts bvs hisr hxs hts hbvs
                    (by simpa [headSub, binder] using hHeadNe)
                with ⟨binderSub, bodySub, hQuantRaw⟩
              have hQuant :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Apply (Term.Var name T) binder) x)
                      xs ts bvs =
                    __eo_mk_apply (Term.Apply (Term.Var name T) binderSub)
                      bodySub := by
                simpa [binder] using hQuantRaw
              have hMkNe :
                  __eo_mk_apply (Term.Apply (Term.Var name T) binderSub)
                      bodySub ≠
                    Term.Stuck := by
                rw [← hQuant]
                simpa [headSub, binder] using hHeadNe
              have hMk :
                  __eo_mk_apply (Term.Apply (Term.Var name T) binderSub)
                      bodySub =
                    Term.Apply (Term.Apply (Term.Var name T) binderSub) bodySub :=
                SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                  (Term.Apply (Term.Var name T) binderSub) bodySub hMkNe
              have hExplicit :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Apply (Term.Var name T) binder) x)
                      xs ts bvs =
                    Term.Apply (Term.Apply (Term.Var name T) binderSub) bodySub := by
                rw [hQuant, hMk]
              have hShape :
                  Term.Apply (Term.Apply (Term.Var name T) binderSub) bodySub =
                    Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
                rw [← hExplicit]
                simpa [binder] using hHeadShape2
              injection hShape with hHeadEq _hBodyEq
              injection hHeadEq with hVarEq _hBinderEq
              cases hVarEq
            · let varSub :=
                __substitute_simul_rec (Term.Boolean isRename)
                  (Term.Var name T) xs ts bvs
              let y0Sub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
              let x0Sub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
              have hInner :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Var name T) y) xs ts bvs =
                    __eo_mk_apply varSub y0Sub := by
                simpa [varSub, y0Sub] using
                  SubstituteSupport.substitute_simul_rec_apply
                    (Term.Boolean isRename) (Term.Var name T) y xs ts bvs
                    hisr hxs hts hbvs
                    (by intro q v vs hEq; cases hEq)
              have hHeadRaw :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs =
                    __eo_mk_apply
                      (__substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Var name T) y) xs ts bvs)
                      x0Sub := by
                simpa [x0Sub] using
                  SubstituteSupport.substitute_simul_rec_apply
                    (Term.Boolean isRename) (Term.Apply (Term.Var name T) y)
                    x xs ts bvs hisr hxs hts hbvs
                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
              have hInnerNe :
                  __eo_mk_apply varSub y0Sub ≠ Term.Stuck := by
                rw [← hInner]
                exact
                  SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
                    (by
                      rw [← hHeadRaw]
                      simpa [headSub] using hHeadNe)
              have hVarNe : varSub ≠ Term.Stuck :=
                SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck
                  hInnerNe
              have hInnerMk :
                  __eo_mk_apply varSub y0Sub = Term.Apply varSub y0Sub :=
                SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                  varSub y0Sub hInnerNe
              have hHeadMkNe :
                  __eo_mk_apply
                      (__substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Var name T) y) xs ts bvs)
                      x0Sub ≠
                    Term.Stuck := by
                rw [← hHeadRaw]
                simpa [headSub] using hHeadNe
              have hHeadMk :
                  __eo_mk_apply
                      (__substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Var name T) y) xs ts bvs)
                      x0Sub =
                    Term.Apply
                      (__substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply (Term.Var name T) y) xs ts bvs)
                      x0Sub :=
                SubstituteTranslatabilitySupport.instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                  (__substitute_simul_rec (Term.Boolean isRename)
                    (Term.Apply (Term.Var name T) y) xs ts bvs)
                  x0Sub hHeadMkNe
              have hExplicit :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Apply (Term.Var name T) y) x) xs ts bvs =
                    Term.Apply (Term.Apply varSub y0Sub) x0Sub := by
                rw [hHeadRaw, hHeadMk, hInner, hInnerMk]
              have hShape :
                  Term.Apply (Term.Apply varSub y0Sub) x0Sub =
                    Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
                rw [← hExplicit]
                exact hHeadShape2
              injection hShape with hHeadEq _hXEq
              injection hHeadEq with hVarSubEq _hYEq
              have hVarSubTrans :
                  RuleProofs.eo_has_smt_translation varSub := by
                simpa [varSub] using
                  SubstituteSupport.substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
                    name T xs ts bvs hXsEnv hBvsEnv hTs hVarTrans
                    (by simpa [varSub] using hVarNe)
              exact
                false_of_special_type_uop_has_smt_translation op hSpecial
                  (by simpa [varSub, hVarSubEq] using hVarSubTrans)
          · by_cases hFApply : ∃ f0 y0, f = Term.Apply f0 y0
            · rcases hFApply with ⟨f0, y0, rfl⟩
              have hHeadNe' :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Apply (Term.Apply f0 y0) y) x)
                      xs ts bvs ≠
                    Term.Stuck := by
                simpa [headSub] using hHeadNe
              rcases
                  SubstituteTranslatabilitySupport.substitute_simul_rec_apply_apply_apply_eq_apply_apply_apply_of_ne_stuck
                    f0 y0 y x xs ts bvs hisr hxs hts hbvs hHeadNe'
                with ⟨gSub, y0Sub, ySub', xSub', hShape3⟩
              have hShape2 :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.Apply (Term.Apply f0 y0) y) x)
                      xs ts bvs =
                    Term.Apply (Term.Apply (Term.UOp op) ySub) xSub := by
                simpa [headSub] using hHeadShape
              rw [hShape3] at hShape2
              cases hShape2
            · exact
                substitute_simul_apply_apply_atom_base_ne_head
                  f y x xs ts bvs hXsEnv hBvsEnv hTs
                  (by intro p q h; exact hFApply ⟨p, q, h⟩)
                  (by intro name T h; exact hFVar ⟨name, T, h⟩)
                  (Term.UOp op) ySub xSub
                  (by intro h; exact hFUOp ⟨op, h⟩)
                  (by simpa [headSub] using hHeadNe)
                  (by simpa [headSub] using hHeadShape)
      have hNoApplyApplyUOp :
          ∀ op w z, applyApplyApplyApplyUOpNeedsSpecialType op ->
            Term.Apply fSub ySub ≠
              Term.Apply (Term.Apply (Term.UOp op) w) z := by
        intro op w z hSpecial hEq
        have hBadShape :
            __substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.Apply f y) x) xs ts bvs =
              Term.Apply
                (Term.Apply (Term.Apply (Term.UOp op) w) z) xSub := by
          rw [show
            __substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.Apply f y) x) xs ts bvs =
              Term.Apply (Term.Apply fSub ySub) xSub by
                simpa [headSub] using hHeadShape]
          rw [hEq]
        by_cases hFApply : ∃ f0 y0, f = Term.Apply f0 y0
        · rcases hFApply with ⟨f0, y0, rfl⟩
          by_cases hF0Apply : ∃ k v, f0 = Term.Apply k v
          · rcases hF0Apply with ⟨k, v, rfl⟩
            rcases
                substitute_simul_rec_apply_apply_apply_apply_eq_of_ne_stuck
                  k v y0 y x xs ts bvs hisr hxs hts hbvs
                  (by simpa [headSub] using hHeadNe)
              with ⟨kSub, vSub, y0Sub, ySub', xSub', hShape4⟩
            have hBadShape' :
                __substitute_simul_rec (Term.Boolean isRename)
                    (Term.Apply
                      (Term.Apply
                        (Term.Apply (Term.Apply k v) y0) y) x)
                    xs ts bvs =
                  Term.Apply
                    (Term.Apply (Term.Apply (Term.UOp op) w) z) xSub := by
              simpa using hBadShape
            rw [hShape4] at hBadShape'
            cases hBadShape'
          · by_cases hF0Var : ∃ name T, f0 = Term.Var name T
            · rcases hF0Var with ⟨name, T, rfl⟩
              exact
                substitute_simul_apply_apply_apply_var_head_ne_untranslatable_target
                  name T y0 y x xs ts bvs (Term.UOp op) w z xSub
                  hXsEnv hBvsEnv hTs
                  (var_has_smt_translation_of_quaternary_application
                    name T y0 y x a hFTrans)
                  (by intro h; cases h)
                  (fun h =>
                    false_of_quaternary_special_uop_has_smt_translation
                      op hSpecial h)
                  (by simpa [headSub] using hHeadNe)
                  (by simpa using hBadShape)
            · by_cases hF0Target : f0 = Term.UOp op
              · subst f0
                cases op <;>
                  simp [applyApplyApplyApplyUOpNeedsSpecialType] at hSpecial
                all_goals
                  first
                  | exact
                      hApplyApplyUOp.notStringsReplaceAllResult
                        ⟨y0, y, rfl⟩
                  | exact
                      hApplyApplyUOp.notStringsReplaceReAllResult
                        ⟨y0, y, rfl⟩
              · exact
                  substitute_simul_apply_apply_apply_atom_base_ne_head
                    f0 y0 y x xs ts bvs (Term.UOp op) w z xSub
                    hXsEnv hBvsEnv hTs
                    (by intro p q h; exact hF0Apply ⟨p, q, h⟩)
                    (by intro name T h; exact hF0Var ⟨name, T, h⟩)
                    hF0Target
                    (by simpa [headSub] using hHeadNe)
                    (by simpa using hBadShape)
        · by_cases hFVar : ∃ name T, f = Term.Var name T
          · rcases hFVar with ⟨name, T, rfl⟩
            exact
              substitute_simul_apply_apply_var_head_ne_untranslatable_target
                name T y x xs ts bvs
                (Term.Apply (Term.UOp op) w) z xSub
                hXsEnv hBvsEnv hTs
                (var_has_smt_translation_of_ternary_application
                  name T y x a hFTrans)
                (by intro h; cases h)
                (fun h =>
                  false_of_quaternary_special_partial_has_smt_translation
                    op w hSpecial h)
                (by simpa [headSub] using hHeadNe)
                (by simpa using hBadShape)
          · exact
              substitute_simul_apply_apply_atom_base_ne_head
                f y x xs ts bvs hXsEnv hBvsEnv hTs
                (by intro p q h; exact hFApply ⟨p, q, h⟩)
                (by intro name T h; exact hFVar ⟨name, T, h⟩)
                (Term.Apply (Term.UOp op) w) z xSub
                (by intro h; exact hFApply ⟨Term.UOp op, w, h⟩)
                (by simpa [headSub] using hHeadNe)
                (by simpa using hBadShape)
      have hHeadTyShape :
          __eo_typeof (Term.Apply (Term.Apply fSub ySub) xSub) ≠
            Term.Stuck :=
        eo_typeof_apply_apply_residual_head_typeof_ne_stuck
          (Term.Apply fSub ySub) xSub aSub
          (by intro op h; cases h)
          (by intro h; cases h)
          (by intro idx h; cases h)
          (by intro idx h; cases h)
          hNoApplyUOp hNoApplyApplyUOp hOuterTyShape
      simpa [headSub, hHeadShape] using hHeadTyShape
  | UOp op =>
      exact False.elim (hNotUOpTop op rfl)
  | Stuck =>
      exact
        substitute_simul_apply_apply_atom_residual_head_typeof_ne_stuck
          Term.Stuck x a xs ts bvs hXsEnv hBvsEnv hTs
          (by intro f y h; cases h)
          (by intro name T h; cases h)
          (by intro op h; cases h)
          hNoUpdate hNoTupleUpdate
          hNotBinderOuter hFTrans hTy
  | _ =>
      exact
        substitute_simul_apply_apply_atom_residual_head_typeof_ne_stuck
          _ x a xs ts bvs hXsEnv hBvsEnv hTs
          (by intro f y h; cases h)
          (by intro name T h; cases h)
          (by intro op h; cases h)
          hNoUpdate hNoTupleUpdate
          hNotBinderOuter hFTrans hTy

theorem substitute_simul_apply_apply_branch_residual_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hUOp : ApplyApplyUOpBranchExclusions g)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hApplyUOp : ApplyApplyApplyUOpBranchExclusions g)
    (hApplyApplyUOp : ApplyApplyApplyApplyUOpBranchExclusions g)
    (hNotUOpTop : ∀ op, g ≠ Term.UOp op)
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) =
        __eo_typeof (Term.Apply g x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs))
    (hRecA :
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
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply g x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) := by
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a) :=
    eo_to_smt_apply_apply_generic_of_branch_exclusions
      (g := g) (x := x) (a := a)
      hUOp hNoUpdate hNoTupleUpdate hApplyUOp hApplyApplyUOp
  have hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck :=
    substitute_simul_apply_apply_branch_residual_head_typeof_ne_stuck
      g x a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
      hUOp hNoUpdate hNoTupleUpdate hApplyUOp hApplyApplyUOp hNotUOpTop
      hFTrans hTy
  exact
    substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
      g x a xs ts bvs
      hXsEnv hBvsEnv hTs
      hNotBinderOuter
      hOuterTranslate
      hFTrans hRecHead hRecA hHeadSubTy hTy

theorem substitute_simul_apply_apply_atom_base_generic_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hInnerTranslate :
      __eo_to_smt (Term.Apply g x) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x))
    (hInnerGeneric :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt g)) (__smtx_typeof (__eo_to_smt x)))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) =
        __eo_typeof (Term.Apply g x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply g x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) := by
  have hGenericOuter :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel g x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester g x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply g x) a hOuterTranslate hGenericOuter hFTrans).1
  exact
    substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
      g x a xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinderOuter hOuterTranslate
      hFTrans hRecHead hRecA hHeadSubTy hTy

end SubstitutePreservationSupport
