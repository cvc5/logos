module

public import Cpc.Proofs.RuleSupport.SubstituteTypeSupport
import all Cpc.Proofs.RuleSupport.SubstituteTypeSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Typed-list substitution support

This module collects typed-list facts needed by substitution preservation
lemmas whose SMT translation is not obtained by translating the typed-list term
as an ordinary EO subterm. The `distinct` operator, for example, inspects its
argument through
`__eo_to_smt_typed_list_elem_type`.
-/

namespace TypedListSubstitutionSupport

inductive TypedListShape : Term -> Prop where
  | nil (T : Term) :
      TypedListShape (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T)
  | cons (x xs : Term) :
      TypedListShape xs ->
      TypedListShape
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs)

theorem typed_list_elem_type_non_none_not_stuck
    {xs : Term}
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  exact hElemNN (by simp [__eo_to_smt_typed_list_elem_type])

theorem typed_list_shape_of_elem_type_non_none :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      TypedListShape xs := by
  intro xs hNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            exact TypedListShape.nil tail
          all_goals
            exact False.elim
              (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                have hTailNN :
                    __eo_to_smt_typed_list_elem_type tail ≠ SmtType.None := by
                  intro hTail
                  apply hNN
                  cases hHead : __smtx_typeof (__eo_to_smt head) <;>
                    simp [__eo_to_smt_typed_list_elem_type, hHead, hTail,
                      native_ite, native_Teq]
                exact TypedListShape.cons head tail
                  (typed_list_shape_of_elem_type_non_none tail hTailNN)
              all_goals
                exact False.elim
                  (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs _ => xs

theorem typed_list_cons_elem_type_parts
    (x xs : Term)
    (hNN :
      __eo_to_smt_typed_list_elem_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_typed_list_elem_type xs ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
        __smtx_typeof (__eo_to_smt x) := by
  let headTy := __smtx_typeof (__eo_to_smt x)
  let tailTy := __eo_to_smt_typed_list_elem_type xs
  have hEqBool : native_Teq headTy tailTy = true := by
    cases hEq : native_Teq headTy tailTy <;>
      simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy, native_ite, hEq]
        at hNN ⊢
  have hHeadTail : headTy = tailTy := by
    simpa [native_Teq] using hEqBool
  have hHeadNN : headTy ≠ SmtType.None := by
    intro hHeadNone
    apply hNN
    simp [__eo_to_smt_typed_list_elem_type, headTy, native_ite, hHeadNone]
  have hTailNN : tailTy ≠ SmtType.None := by
    rw [← hHeadTail]
    exact hHeadNN
  have hConsEq :
      __eo_to_smt_typed_list_elem_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
        headTy := by
    simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy, native_ite,
      hEqBool]
  exact ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩

theorem typed_list_nil_elem_type_eq_of_non_none
    (T : Term)
    (hNN :
      __eo_to_smt_typed_list_elem_type
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) ≠
        SmtType.None) :
    __eo_to_smt_typed_list_elem_type
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) =
      __eo_to_smt_type T := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type T) <;>
    simp [__eo_to_smt_typed_list_elem_type, hWf, native_ite] at hNN ⊢

theorem native_Teq_none_false_of_non_none
    {T : SmtType}
    (h : T ≠ SmtType.None) :
    native_Teq T SmtType.None = false := by
  cases T <;> simp [native_Teq] at h ⊢

private theorem substitute_simul_rec_closed_atom_eq_self
    {isRename : Bool}
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hClosed : __is_closed_rec F Term.__eo_List_nil = Term.Boolean true) :
    __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs = F := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil)
          (Term.Boolean true) F :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean isRename) F xs ss bvs
      hisr hxs hss hbvs hNotApply hNotVar hNotStuck
  rw [hHeadEq, hClosed]
  simp [__eo_requires, native_ite, native_teq, SmtEval.native_not]

private theorem substitute_simul_rec_apply_eq_apply_of_parts
    {isRename : Bool}
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hF :
      __substitute_simul_rec (Term.Boolean isRename) f xs ss bvs = f)
    (hA :
      __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs = a)
    (hFNe : f ≠ Term.Stuck)
    (hANe : a ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean isRename) (Term.Apply f a) xs ss bvs =
      Term.Apply f a := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rw [SubstituteSupport.substitute_simul_rec_apply
    (Term.Boolean isRename) f a xs ss bvs hisr hxs hss hbvs hNotBinder]
  rw [hF, hA]
  cases f <;> cases a <;> simp [__eo_mk_apply] at hFNe hANe ⊢

theorem substitute_simul_rec_eo_type_valid_rec_eq_self
    {isRename : Bool}
    (T xs ss bvs : Term)
    {refs : List native_String} {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hValid : TranslationProofs.eo_type_valid_rec refs T) :
    __substitute_simul_rec (Term.Boolean isRename) T xs ss bvs = T := by
  let rec go (T : Term) :
      ∀ {refs : List native_String} (xs ss bvs : Term)
        {xsVars bvsVars : List EoVarKey},
        EoVarEnvPerm xs xsVars ->
          EoVarEnvPerm bvs bvsVars ->
            EoListAllHaveSmtTranslation ss ->
              TranslationProofs.eo_type_valid_rec refs T ->
                __substitute_simul_rec
                    (Term.Boolean isRename) T xs ss bvs = T := by
    intro refs xs ss bvs xsVars bvsVars hXsEnv hBvsEnv hSs hValid
    cases T with
    | Apply f a =>
        cases f with
        | UOp op =>
            have hValidOrig := hValid
            cases op <;>
              try
                (simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __smtx_typeof_guard, native_ite, native_Teq] at hValid)
            case BitVec =>
              cases a with
              | Numeral n =>
                  have hHead :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.UOp UserOp.BitVec) xs ss bvs =
                        Term.UOp UserOp.BitVec :=
                    SubstituteSupport.substitute_simul_rec_uop_eq_self
                      UserOp.BitVec xs ss bvs hXsEnv hBvsEnv hSs
                  have hArg :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Numeral n) xs ss bvs =
                        Term.Numeral n :=
                    substitute_simul_rec_closed_atom_eq_self
                      (Term.Numeral n) xs ss bvs hXsEnv hBvsEnv hSs
                      (by intro f a h; cases h)
                      (by intro s S h; cases h)
                      (by intro h; cases h)
                      (by simp [__is_closed_rec])
                  exact
                    substitute_simul_rec_apply_eq_apply_of_parts
                      (Term.UOp UserOp.BitVec) (Term.Numeral n) xs ss bvs
                      hXsEnv hBvsEnv hSs
                      (by intro q v vs h; cases h)
                      hHead hArg
                      (by intro h; cases h)
                      (by intro h; cases h)
              | _ =>
                  simp [__eo_to_smt_type, TranslationProofs.noNoneTy] at hValid
            case Seq =>
              have hAValid :
                  TranslationProofs.eo_type_valid_rec [] a := by
                exact eo_type_valid_rec_seq_arg (refs := refs) hValidOrig
              have hHead :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.UOp UserOp.Seq) xs ss bvs =
                    Term.UOp UserOp.Seq :=
                SubstituteSupport.substitute_simul_rec_uop_eq_self
                  UserOp.Seq xs ss bvs hXsEnv hBvsEnv hSs
              have hArg := go a xs ss bvs hXsEnv hBvsEnv hSs hAValid
              exact
                substitute_simul_rec_apply_eq_apply_of_parts
                  (Term.UOp UserOp.Seq) a xs ss bvs
                  hXsEnv hBvsEnv hSs
                  (by intro q v vs h; cases h)
                  hHead hArg
                  (by intro h; cases h)
                  (TranslationProofs.eo_type_valid_rec_not_stuck hAValid)
            case Set =>
              have hAValid :
                  TranslationProofs.eo_type_valid_rec [] a := by
                exact eo_type_valid_rec_set_arg (refs := refs) hValidOrig
              have hHead :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.UOp UserOp.Set) xs ss bvs =
                    Term.UOp UserOp.Set :=
                SubstituteSupport.substitute_simul_rec_uop_eq_self
                  UserOp.Set xs ss bvs hXsEnv hBvsEnv hSs
              have hArg := go a xs ss bvs hXsEnv hBvsEnv hSs hAValid
              exact
                substitute_simul_rec_apply_eq_apply_of_parts
                  (Term.UOp UserOp.Set) a xs ss bvs
                  hXsEnv hBvsEnv hSs
                  (by intro q v vs h; cases h)
                  hHead hArg
                  (by intro h; cases h)
                  (TranslationProofs.eo_type_valid_rec_not_stuck hAValid)
        | Apply g y =>
            cases g with
            | FunType =>
                rcases eo_type_valid_rec_fun_args (refs := refs) hValid with
                  ⟨hYValid, hAValid⟩
                have hFun :
                    __substitute_simul_rec (Term.Boolean isRename)
                        Term.FunType xs ss bvs =
                      Term.FunType :=
                  substitute_simul_rec_closed_atom_eq_self
                    Term.FunType xs ss bvs hXsEnv hBvsEnv hSs
                    (by intro f a h; cases h)
                    (by intro s S h; cases h)
                    (by intro h; cases h)
                    (by simp [__is_closed_rec])
                have hY := go y xs ss bvs hXsEnv hBvsEnv hSs hYValid
                have hInner :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply Term.FunType y) xs ss bvs =
                      Term.Apply Term.FunType y :=
                  substitute_simul_rec_apply_eq_apply_of_parts
                    Term.FunType y xs ss bvs hXsEnv hBvsEnv hSs
                    (by intro q v vs h; cases h)
                    hFun hY
                    (by intro h; cases h)
                    (TranslationProofs.eo_type_valid_rec_not_stuck hYValid)
                have hA := go a xs ss bvs hXsEnv hBvsEnv hSs hAValid
                exact
                  substitute_simul_rec_apply_eq_apply_of_parts
                    (Term.Apply Term.FunType y) a xs ss bvs
                    hXsEnv hBvsEnv hSs
                    (apply_head_not_list_branch_of_arg_not_list
                      (eo_type_valid_rec_not_eo_list_cons hYValid))
                    hInner hA
                    (by intro h; cases h)
                    (TranslationProofs.eo_type_valid_rec_not_stuck hAValid)
            | UOp op =>
                have hValidOrig := hValid
                cases op <;>
                  try
                    (simp [TranslationProofs.eo_type_valid_rec,
                      __eo_to_smt_type, TranslationProofs.noNoneTy,
                      __smtx_typeof_guard, native_ite, native_Teq] at hValid)
                case Array =>
                  rcases eo_type_valid_rec_array_args
                      (refs := refs) hValidOrig with
                    ⟨hYValid, hAValid⟩
                  have hHead :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.UOp UserOp.Array) xs ss bvs =
                        Term.UOp UserOp.Array :=
                    SubstituteSupport.substitute_simul_rec_uop_eq_self
                      UserOp.Array xs ss bvs hXsEnv hBvsEnv hSs
                  have hY := go y xs ss bvs hXsEnv hBvsEnv hSs hYValid
                  have hInner :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp UserOp.Array) y) xs ss bvs =
                        Term.Apply (Term.UOp UserOp.Array) y :=
                    substitute_simul_rec_apply_eq_apply_of_parts
                      (Term.UOp UserOp.Array) y xs ss bvs
                      hXsEnv hBvsEnv hSs
                      (by intro q v vs h; cases h)
                      hHead hY
                      (by intro h; cases h)
                      (TranslationProofs.eo_type_valid_rec_not_stuck hYValid)
                  have hA := go a xs ss bvs hXsEnv hBvsEnv hSs hAValid
                  exact
                    substitute_simul_rec_apply_eq_apply_of_parts
                      (Term.Apply (Term.UOp UserOp.Array) y) a xs ss bvs
                      hXsEnv hBvsEnv hSs
                      (apply_head_not_list_branch_of_arg_not_list
                        (eo_type_valid_rec_not_eo_list_cons hYValid))
                      hInner hA
                      (by intro h; cases h)
                      (TranslationProofs.eo_type_valid_rec_not_stuck hAValid)
                case Tuple =>
                  rcases eo_type_valid_rec_tuple_args
                      (refs := refs) hValid with
                    ⟨hYValid, hAValid, _hWf⟩
                  have hHead :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.UOp UserOp.Tuple) xs ss bvs =
                        Term.UOp UserOp.Tuple :=
                    SubstituteSupport.substitute_simul_rec_uop_eq_self
                      UserOp.Tuple xs ss bvs hXsEnv hBvsEnv hSs
                  have hY := go y xs ss bvs hXsEnv hBvsEnv hSs hYValid
                  have hInner :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp UserOp.Tuple) y) xs ss bvs =
                        Term.Apply (Term.UOp UserOp.Tuple) y :=
                    substitute_simul_rec_apply_eq_apply_of_parts
                      (Term.UOp UserOp.Tuple) y xs ss bvs
                      hXsEnv hBvsEnv hSs
                      (by intro q v vs h; cases h)
                      hHead hY
                      (by intro h; cases h)
                      (TranslationProofs.eo_type_valid_rec_not_stuck hYValid)
                  have hA := go a xs ss bvs hXsEnv hBvsEnv hSs hAValid
                  exact
                    substitute_simul_rec_apply_eq_apply_of_parts
                      (Term.Apply (Term.UOp UserOp.Tuple) y) a xs ss bvs
                      hXsEnv hBvsEnv hSs
                      (apply_head_not_list_branch_of_arg_not_list
                        (eo_type_valid_rec_not_eo_list_cons hYValid))
                      hInner hA
                      (by intro h; cases h)
                      (TranslationProofs.eo_type_valid_rec_not_stuck hAValid)
            | _ =>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy] at hValid
        | _ =>
            simp [TranslationProofs.eo_type_valid_rec,
              __eo_to_smt_type, TranslationProofs.noNoneTy] at hValid
    | UOp op =>
        exact
          SubstituteSupport.substitute_simul_rec_uop_eq_self
            op xs ss bvs hXsEnv hBvsEnv hSs
    | Bool =>
        exact
          substitute_simul_rec_closed_atom_eq_self Term.Bool xs ss bvs
            hXsEnv hBvsEnv hSs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            (is_closed_rec_eq_true_of_eo_type_valid_rec
              EoSmtVarEnv.nil hValid)
    | DatatypeType s d =>
        exact
          substitute_simul_rec_closed_atom_eq_self
            (Term.DatatypeType s d) xs ss bvs
            hXsEnv hBvsEnv hSs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            (is_closed_rec_eq_true_of_eo_type_valid_rec
              EoSmtVarEnv.nil hValid)
    | DatatypeTypeRef s =>
        exact
          substitute_simul_rec_closed_atom_eq_self
            (Term.DatatypeTypeRef s) xs ss bvs
            hXsEnv hBvsEnv hSs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            (is_closed_rec_eq_true_of_eo_type_valid_rec
              EoSmtVarEnv.nil hValid)
    | DtcAppType T U =>
        exact
          substitute_simul_rec_closed_atom_eq_self
            (Term.DtcAppType T U) xs ss bvs
            hXsEnv hBvsEnv hSs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            (is_closed_rec_eq_true_of_eo_type_valid_rec
              EoSmtVarEnv.nil hValid)
    | USort i =>
        exact
          substitute_simul_rec_closed_atom_eq_self
            (Term.USort i) xs ss bvs
            hXsEnv hBvsEnv hSs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            (is_closed_rec_eq_true_of_eo_type_valid_rec
              EoSmtVarEnv.nil hValid)
    | Var name S =>
        simp [TranslationProofs.eo_type_valid_rec, __eo_to_smt_type,
          TranslationProofs.noNoneTy] at hValid
    | Stuck =>
        simp [TranslationProofs.eo_type_valid_rec, __eo_to_smt_type,
          TranslationProofs.noNoneTy] at hValid
    | _ =>
        simp [TranslationProofs.eo_type_valid_rec, __eo_to_smt_type,
          TranslationProofs.noNoneTy] at hValid
  exact go T xs ss bvs hXsEnv hBvsEnv hSs hValid

theorem substitute_simul_rec_eo_type_valid_eq_self
    {isRename : Bool}
    (T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hValid : TranslationProofs.eo_type_valid T) :
    __substitute_simul_rec (Term.Boolean isRename) T xs ss bvs = T := by
  by_cases hUOp : ∃ op, T = Term.UOp op
  · rcases hUOp with ⟨op, rfl⟩
    exact
      SubstituteSupport.substitute_simul_rec_uop_eq_self
        op xs ss bvs hXsEnv hBvsEnv hSs
  · have hValidRec :
        TranslationProofs.eo_type_valid_rec [] T := by
      cases T with
      | UOp op =>
          exact False.elim (hUOp ⟨op, rfl⟩)
      | _ =>
          simpa [TranslationProofs.eo_type_valid,
            TranslationProofs.eo_type_valid_rec] using hValid
    exact
      substitute_simul_rec_eo_type_valid_rec_eq_self
        T xs ss bvs hXsEnv hBvsEnv hSs hValidRec

private theorem smtx_typeof_non_none_not_eo_list_cons
    {t : Term}
    (hTy : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    ∀ v vs, t ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs := by
  intro v vs hEq
  subst t
  exact hTy (smtx_typeof_eo_list_cons_eq_none v vs)

theorem eo_typeof_distinct_arg_typed_list_of_ne_stuck
    (xs : Term)
    (hTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.distinct) xs) ≠
        Term.Stuck) :
    ∃ T, __eo_typeof xs =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T := by
  change __eo_typeof_distinct (__eo_typeof xs) ≠ Term.Stuck at hTy
  cases hXsTy : __eo_typeof xs with
  | Apply f T =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList =>
            exact ⟨T, rfl⟩
          all_goals
            exfalso
            apply hTy
            rw [hXsTy]
            rfl
      | _ =>
          exfalso
          apply hTy
          rw [hXsTy]
          rfl
  | _ =>
      exfalso
      apply hTy
      rw [hXsTy]
      rfl

private theorem eo_typeof_typed_list_cons_head_ne_stuck_of_typed
    (head tail T : Term)
    (hTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
            tail) =
        Term.Apply (Term.UOp UserOp._at__at_TypedList) T) :
    __eo_typeof head ≠ Term.Stuck := by
  intro hHead
  change
    __eo_typeof__at__at_TypedList_cons
        (__eo_typeof head) (__eo_typeof tail) =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T at hTy
  rw [hHead] at hTy
  simp [__eo_typeof__at__at_TypedList_cons] at hTy

private theorem eo_typeof_typed_list_cons_tail_typed_of_typed
    (head tail T : Term)
    (hTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
            tail) =
        Term.Apply (Term.UOp UserOp._at__at_TypedList) T) :
    ∃ U, __eo_typeof tail =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) U := by
  change
    __eo_typeof__at__at_TypedList_cons
        (__eo_typeof head) (__eo_typeof tail) =
      Term.Apply (Term.UOp UserOp._at__at_TypedList) T at hTy
  cases hTail : __eo_typeof tail with
  | Apply f U =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList =>
            exact ⟨U, rfl⟩
          all_goals
            exfalso
            cases hHead : __eo_typeof head <;>
              simp [__eo_typeof__at__at_TypedList_cons, hHead, hTail] at hTy
      | _ =>
          exfalso
          cases hHead : __eo_typeof head <;>
            simp [__eo_typeof__at__at_TypedList_cons, hHead, hTail] at hTy
  | _ =>
      exfalso
      cases hHead : __eo_typeof head <;>
        simp [__eo_typeof__at__at_TypedList_cons, hHead, hTail] at hTy

theorem substitute_simul_rec_typed_list_elem_type_eq_of_non_none
    {isRename : Bool}
    (typedList xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hSmtType :
      ∀ t,
        sizeOf t < sizeOf typedList ->
        RuleProofs.eo_has_smt_translation t ->
          __eo_typeof
              (__substitute_simul_rec (Term.Boolean isRename) t xs ss bvs) ≠
            Term.Stuck ->
            __smtx_typeof
                (__eo_to_smt
                  (__substitute_simul_rec (Term.Boolean isRename) t xs ss bvs)) =
              __smtx_typeof (__eo_to_smt t))
    (hSubTyped :
      ∃ T,
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) typedList xs ss bvs) =
          Term.Apply (Term.UOp UserOp._at__at_TypedList) T)
    (hElemNN : __eo_to_smt_typed_list_elem_type typedList ≠ SmtType.None) :
    __eo_to_smt_typed_list_elem_type
        (__substitute_simul_rec (Term.Boolean isRename) typedList xs ss bvs) =
      __eo_to_smt_typed_list_elem_type typedList := by
  cases typedList with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            have hWf : __smtx_type_wf (__eo_to_smt_type tail) = true := by
              cases h :
                  __smtx_type_wf (__eo_to_smt_type tail) <;>
                simp [__eo_to_smt_typed_list_elem_type, h, native_ite]
                  at hElemNN ⊢
            have hValid : TranslationProofs.eo_type_valid tail :=
              TranslationProofs.eo_type_valid_of_smt_wf tail hWf
            have hHead :
                __substitute_simul_rec (Term.Boolean isRename)
                    (Term.UOp UserOp._at__at_TypedList_nil) xs ss bvs =
                  Term.UOp UserOp._at__at_TypedList_nil :=
              SubstituteSupport.substitute_simul_rec_uop_eq_self
                UserOp._at__at_TypedList_nil xs ss bvs
                hXsEnv hBvsEnv hSs
            have hTail :
                __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs =
                  tail :=
              substitute_simul_rec_eo_type_valid_eq_self
                tail xs ss bvs hXsEnv hBvsEnv hSs hValid
            have hSubEq :
                __substitute_simul_rec (Term.Boolean isRename)
                    (Term.Apply
                      (Term.UOp UserOp._at__at_TypedList_nil) tail)
                    xs ss bvs =
                  Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail :=
              substitute_simul_rec_apply_eq_apply_of_parts
                (Term.UOp UserOp._at__at_TypedList_nil) tail xs ss bvs
                hXsEnv hBvsEnv hSs
                (by intro q v vs h; cases h)
                hHead hTail
                (by intro h; cases h)
                (TranslationProofs.eo_type_valid_not_stuck hValid)
            rw [hSubEq]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_cons_elem_type_parts head tail hElemNN with
                  ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩
                let headSub :=
                  __substitute_simul_rec
                    (Term.Boolean isRename) head xs ss bvs
                let tailSub :=
                  __substitute_simul_rec
                    (Term.Boolean isRename) tail xs ss bvs
                have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
                have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
                have hss : ss ≠ Term.Stuck :=
                  SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hSs
                have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
                have hConsHead :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.UOp UserOp._at__at_TypedList_cons) xs ss bvs =
                      Term.UOp UserOp._at__at_TypedList_cons :=
                  SubstituteSupport.substitute_simul_rec_uop_eq_self
                    UserOp._at__at_TypedList_cons xs ss bvs
                    hXsEnv hBvsEnv hSs
                have hInnerRaw :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) head)
                        xs ss bvs =
                      __eo_mk_apply
                        (Term.UOp UserOp._at__at_TypedList_cons) headSub := by
                  have hApplyEq :=
                    SubstituteSupport.substitute_simul_rec_apply
                      (Term.Boolean isRename)
                      (Term.UOp UserOp._at__at_TypedList_cons) head
                      xs ss bvs hisr hxs hss hbvs
                      (by intro q v vs h; cases h)
                  simpa [headSub, hConsHead] using hApplyEq
                have hOuterNotBinder :
                    ∀ q v vs,
                      Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) head ≠
                        Term.Apply q
                          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
                  apply_head_not_list_branch_of_arg_not_list
                    (smtx_typeof_non_none_not_eo_list_cons hHeadNN)
                have hSubRaw :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons) head)
                          tail) xs ss bvs =
                      __eo_mk_apply
                        (__eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                        tailSub := by
                  have hApplyEq :=
                    SubstituteSupport.substitute_simul_rec_apply
                      (Term.Boolean isRename)
                      (Term.Apply
                        (Term.UOp UserOp._at__at_TypedList_cons) head)
                      tail xs ss bvs hisr hxs hss hbvs hOuterNotBinder
                  simpa [tailSub, hInnerRaw] using hApplyEq
                rcases hSubTyped with ⟨TSub, hSubTypedEq⟩
                have hSubRawTy :
                    __eo_typeof
                        (__eo_mk_apply
                          (__eo_mk_apply
                            (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                          tailSub) =
                      Term.Apply (Term.UOp UserOp._at__at_TypedList) TSub := by
                  rw [← hSubRaw]
                  exact hSubTypedEq
                have hSubRawTyNe :
                    __eo_typeof
                        (__eo_mk_apply
                          (__eo_mk_apply
                            (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                          tailSub) ≠
                      Term.Stuck := by
                  rw [hSubRawTy]
                  intro h
                  cases h
                have hOuterNe :
                    __eo_mk_apply
                        (__eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                        tailSub ≠
                      Term.Stuck :=
                  SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck
                    hSubRawTyNe
                have hInnerNe :
                    __eo_mk_apply
                        (Term.UOp UserOp._at__at_TypedList_cons) headSub ≠
                      Term.Stuck :=
                  SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck
                    hOuterNe
                have hInnerMk :
                    __eo_mk_apply
                        (Term.UOp UserOp._at__at_TypedList_cons) headSub =
                      Term.Apply
                        (Term.UOp UserOp._at__at_TypedList_cons) headSub :=
                  SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck
                    (Term.UOp UserOp._at__at_TypedList_cons) headSub hInnerNe
                have hOuterMk :
                    __eo_mk_apply
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                        tailSub =
                      Term.Apply
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                        tailSub :=
                  SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck
                    (Term.Apply
                      (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                    tailSub
                    (by
                      rw [← hInnerMk]
                      exact hOuterNe)
                have hSubEq :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.Apply
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons) head)
                          tail) xs ss bvs =
                      Term.Apply
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                        tailSub := by
                  rw [hSubRaw, hInnerMk, hOuterMk]
                have hSubConsTy :
                    __eo_typeof
                        (Term.Apply
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                          tailSub) =
                      Term.Apply (Term.UOp UserOp._at__at_TypedList) TSub := by
                  rw [← hSubEq]
                  exact hSubTypedEq
                have hHeadSubTyNe :
                    __eo_typeof headSub ≠ Term.Stuck :=
                  eo_typeof_typed_list_cons_head_ne_stuck_of_typed
                    headSub tailSub TSub hSubConsTy
                have hTailSubTyped :
                    ∃ U,
                      __eo_typeof tailSub =
                        Term.Apply (Term.UOp UserOp._at__at_TypedList) U :=
                  eo_typeof_typed_list_cons_tail_typed_of_typed
                    headSub tailSub TSub hSubConsTy
                have hHeadTrans :
                    RuleProofs.eo_has_smt_translation head := by
                  unfold RuleProofs.eo_has_smt_translation
                  exact hHeadNN
                have hHeadSubTy :
                    __smtx_typeof
                        (__eo_to_smt
                          headSub) =
                      __smtx_typeof (__eo_to_smt head) :=
                  hSmtType head (by simp; omega) hHeadTrans
                    (by simpa [headSub] using hHeadSubTyNe)
                have hHeadSubNN :
                    __smtx_typeof
                        (__eo_to_smt
                          headSub) ≠
                      SmtType.None := by
                  rw [hHeadSubTy]
                  exact hHeadNN
                have hTailSubEq :
                    __eo_to_smt_typed_list_elem_type
                        tailSub =
                      __eo_to_smt_typed_list_elem_type tail :=
                  substitute_simul_rec_typed_list_elem_type_eq_of_non_none
                    tail xs ss bvs hXsEnv hBvsEnv hSs
                    (fun t hLt hTrans hTy =>
                      hSmtType t (by simp at hLt ⊢; omega) hTrans hTy)
                    hTailSubTyped
                    hTailNN
                have hTailSubNN :
                    __eo_to_smt_typed_list_elem_type
                        tailSub ≠
                      SmtType.None := by
                  rw [hTailSubEq]
                  exact hTailNN
                have hEqBool :
                    native_Teq
                        (__smtx_typeof
                          (__eo_to_smt headSub))
                        (__eo_to_smt_typed_list_elem_type
                          tailSub) =
                      true := by
                  rw [hHeadSubTy, hTailSubEq, hHeadTail]
                  simp [native_Teq]
                have hSubConsEq :
                    __eo_to_smt_typed_list_elem_type
                        (Term.Apply
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub) =
                      __smtx_typeof
                        (__eo_to_smt headSub) := by
                  simp [__eo_to_smt_typed_list_elem_type, hEqBool,
                    native_ite]
                rw [hSubEq, hSubConsEq, hHeadSubTy, hConsEq]
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by typedList

theorem substitute_simul_rec_typed_list_elem_type_non_none
    {isRename : Bool}
    (typedList xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hSmtType :
      ∀ t,
        sizeOf t < sizeOf typedList ->
        RuleProofs.eo_has_smt_translation t ->
          __eo_typeof
              (__substitute_simul_rec (Term.Boolean isRename) t xs ss bvs) ≠
            Term.Stuck ->
            __smtx_typeof
                (__eo_to_smt
                  (__substitute_simul_rec (Term.Boolean isRename) t xs ss bvs)) =
              __smtx_typeof (__eo_to_smt t))
    (hSubTyped :
      ∃ T,
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) typedList xs ss bvs) =
          Term.Apply (Term.UOp UserOp._at__at_TypedList) T)
    (hElemNN : __eo_to_smt_typed_list_elem_type typedList ≠ SmtType.None) :
    __eo_to_smt_typed_list_elem_type
        (__substitute_simul_rec (Term.Boolean isRename) typedList xs ss bvs) ≠
      SmtType.None := by
  rw [substitute_simul_rec_typed_list_elem_type_eq_of_non_none
    typedList xs ss bvs hXsEnv hBvsEnv hSs hSmtType hSubTyped hElemNN]
  exact hElemNN

theorem eo_to_smt_distinct_eq_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) =
      __eo_to_smt_distinct xs := by
  change
    native_ite (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
      __eo_to_smt_distinct xs
  rw [native_Teq_none_false_of_non_none hElemNN]
  simp [native_ite]

theorem typed_list_elem_type_non_none_of_distinct_has_smt_translation
    {xs : Term}
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.distinct) xs)) :
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) ≠
        SmtType.None at hTrans
  intro hNone
  exact hTrans (by
    simp [hNone, native_ite, TranslationProofs.smtx_typeof_none])

theorem eo_typeof_distinct_eq_bool_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.distinct) xs) = Term.Bool := by
  rcases
      TranslationProofs.eo_to_smt_typed_list_elem_type_of_non_none
        xs hElemNN with
    ⟨T, hType, _hSmt, _hValid⟩
  change __eo_typeof_distinct (__eo_typeof xs) = Term.Bool
  rw [hType]
  rfl

theorem eo_typeof_distinct_ne_stuck_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ Term.Stuck := by
  rw [eo_typeof_distinct_eq_bool_of_elem_type_non_none xs hElemNN]
  intro h
  cases h

theorem smtx_typeof_distinct_pairs_of_elem_type :
    ∀ (s : SmtTerm) (xs : Term),
      __smtx_typeof s = __eo_to_smt_typed_list_elem_type xs ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt_distinct_pairs s xs) = SmtType.Bool := by
  intro s xs hS hElemNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
            rw [__smtx_typeof.eq_1]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_cons_elem_type_parts head tail hElemNN with
                  ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩
                have hSElem :
                    __smtx_typeof s = __smtx_typeof (__eo_to_smt head) := by
                  rw [hS, hConsEq]
                have hEqBool :
                    __smtx_typeof
                      (SmtTerm.eq s (__eo_to_smt head)) = SmtType.Bool := by
                  rw [typeof_eq_eq]
                  exact (RuleProofs.smtx_typeof_eq_bool_iff
                    (__smtx_typeof s)
                    (__smtx_typeof (__eo_to_smt head))).mpr
                    ⟨hSElem, by rw [hSElem]; exact hHeadNN⟩
                have hNotBool :
                    __smtx_typeof
                      (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head))) =
                        SmtType.Bool := by
                  rw [typeof_not_eq, hEqBool]
                  rfl
                have hRec :
                    __smtx_typeof
                      (__eo_to_smt_distinct_pairs s tail) = SmtType.Bool :=
                  smtx_typeof_distinct_pairs_of_elem_type s tail
                    (hSElem.trans hHeadTail)
                    hTailNN
                change
                  __smtx_typeof
                    (SmtTerm.and
                      (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                      (__eo_to_smt_distinct_pairs s tail)) = SmtType.Bool
                rw [typeof_and_eq, hNotBool, hRec]
                rfl
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by s xs _ _ => xs

theorem smtx_typeof_distinct_of_elem_type_non_none :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool := by
  intro xs hElemNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
            rw [__smtx_typeof.eq_1]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_cons_elem_type_parts head tail hElemNN with
                  ⟨hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                have hPairs :
                    __smtx_typeof
                      (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail) =
                        SmtType.Bool :=
                  smtx_typeof_distinct_pairs_of_elem_type
                    (__eo_to_smt head) tail hHeadTail hTailNN
                have hTailDistinct :
                    __smtx_typeof (__eo_to_smt_distinct tail) =
                      SmtType.Bool :=
                  smtx_typeof_distinct_of_elem_type_non_none tail hTailNN
                change
                  __smtx_typeof
                    (SmtTerm.and
                      (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                      (__eo_to_smt_distinct tail)) = SmtType.Bool
                rw [typeof_and_eq, hPairs, hTailDistinct]
                rfl
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs _ => xs

theorem eo_has_smt_translation_distinct_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [eo_to_smt_distinct_eq_of_elem_type_non_none xs hElemNN]
  rw [smtx_typeof_distinct_of_elem_type_non_none xs hElemNN]
  simp

end TypedListSubstitutionSupport
