module

public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationShared
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationClassifiers
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericApply
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationAtomApply
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericOps
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryOps
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationSetInsert
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationDistinct
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTernaryOps
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationDtSel
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationIndexedOps
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationUOp1
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTupleOps
public import Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport
import all Cpc.Logos
import all Cpc.Proofs.RuleSupport.SubstituteTypeSupport

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

/-!
# Combined substitution preservation support

This module is a staging point for merging the two structural preservation
proofs for substitution mode (`isr = false`):

* EO type preservation of `__substitute_simul_rec`;
* SMT-translatability preservation of `__substitute_simul_rec`.

The instantiate-facing projection wrappers and old recursive engines have been
removed; callers now use the combined theorem directly. The remaining
application/operator-spine proof obligations live here as explicit fallback
holes until those cases are folded into the combined induction.
-/

namespace SubstitutePreservationSupport

abbrev substResult (isRename : Bool) (F xs ts bvs : Term) : Term :=
  __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs

abbrev SubstitutionPreservationResult
    (isRename : Bool) (F xs ts bvs : Term) : Prop :=
  __eo_typeof (substResult isRename F xs ts bvs) = __eo_typeof F ∧
    RuleProofs.eo_has_smt_translation (substResult isRename F xs ts bvs)

abbrev SubstitutionPreservationRec
    (isRename : Bool) (F xs ts : Term) :=
  ∀ {G bvs' : Term} {xsVars' bvsVars' : List EoVarKey},
    sizeOf G < sizeOf F →
    EoVarEnvPerm xs xsVars' →
    EoVarEnvPerm bvs' bvsVars' →
    RuleProofs.eo_has_smt_translation G →
    EoListAllHaveSmtTranslation ts →
    SubstActualsHaveSmtTypes xs ts →
    __eo_typeof (substResult isRename G xs ts bvs') ≠ Term.Stuck →
    SubstitutionPreservationResult isRename G xs ts bvs'

abbrev SubstitutionBinderHandler (isRename : Bool) (xs ts : Term) :=
  ∀ (q v vs a bvs : Term) {xsVars bvsVars : List EoVarKey},
    EoVarEnvPerm xs xsVars →
    EoVarEnvPerm bvs bvsVars →
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) →
    EoListAllHaveSmtTranslation ts →
    SubstActualsHaveSmtTypes xs ts →
    __eo_typeof
      (substResult isRename
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs) ≠ Term.Stuck →
    SubstitutionPreservationRec isRename
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) xs ts →
    SubstitutionPreservationResult isRename
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
      xs ts bvs

private theorem eo_typeof_eq_eq_bool_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp [__eo_typeof_eq] at h
  by_cases hEq : __eo_eq A B = Term.Boolean true
  · simp [__eo_typeof_eq, __eo_requires, hEq, native_ite,
      native_teq, native_not]
  · exfalso
    apply h
    simp [__eo_typeof_eq, __eo_requires, hEq, native_ite, native_teq]

private theorem eo_typeof_eq_bool_operands_not_stuck
    (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp [__eo_typeof_eq] at h
  · exact ⟨hA, hB⟩

private theorem false_of_exhausted_unary_uop_apply_has_smt_translation
    {f a : Term} {op : UserOp}
    (hEq : f = Term.UOp op)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a))
    (hHeadNot : f ≠ Term.UOp UserOp.not)
    (hHeadDistinct : f ≠ Term.UOp UserOp.distinct)
    (hHeadPurify : f ≠ Term.UOp UserOp._at_purify)
    (hHeadToReal : f ≠ Term.UOp UserOp.to_real)
    (hHeadToInt : f ≠ Term.UOp UserOp.to_int)
    (hHeadIsInt : f ≠ Term.UOp UserOp.is_int)
    (hHeadAbs : f ≠ Term.UOp UserOp.abs)
    (hHeadUneg : f ≠ Term.UOp UserOp.__eoo_neg_2)
    (hHeadPow2 : f ≠ Term.UOp UserOp.int_pow2)
    (hHeadLog2 : f ≠ Term.UOp UserOp.int_log2)
    (hHeadIntIspow2 : f ≠ Term.UOp UserOp.int_ispow2)
    (hHeadIntDivByZero :
      f ≠ Term.UOp UserOp._at_int_div_by_zero)
    (hHeadModByZero : f ≠ Term.UOp UserOp._at_mod_by_zero)
    (hHeadBvsize : f ≠ Term.UOp UserOp._at_bvsize)
    (hHeadBvnot : f ≠ Term.UOp UserOp.bvnot)
    (hHeadBvneg : f ≠ Term.UOp UserOp.bvneg)
    (hHeadBvnego : f ≠ Term.UOp UserOp.bvnego)
    (hHeadBvredand : f ≠ Term.UOp UserOp.bvredand)
    (hHeadBvredor : f ≠ Term.UOp UserOp.bvredor)
    (hHeadStrLen : f ≠ Term.UOp UserOp.str_len)
    (hHeadStrRev : f ≠ Term.UOp UserOp.str_rev)
    (hHeadStrToLower : f ≠ Term.UOp UserOp.str_to_lower)
    (hHeadStrToUpper : f ≠ Term.UOp UserOp.str_to_upper)
    (hHeadStrToCode : f ≠ Term.UOp UserOp.str_to_code)
    (hHeadStrFromCode : f ≠ Term.UOp UserOp.str_from_code)
    (hHeadStrIsDigit : f ≠ Term.UOp UserOp.str_is_digit)
    (hHeadStrToInt : f ≠ Term.UOp UserOp.str_to_int)
    (hHeadStrFromInt : f ≠ Term.UOp UserOp.str_from_int)
    (hHeadStrToRe : f ≠ Term.UOp UserOp.str_to_re)
    (hHeadStringsStoiNonDigit :
      f ≠ Term.UOp UserOp._at_strings_stoi_non_digit)
    (hHeadReMult : f ≠ Term.UOp UserOp.re_mult)
    (hHeadRePlus : f ≠ Term.UOp UserOp.re_plus)
    (hHeadReOpt : f ≠ Term.UOp UserOp.re_opt)
    (hHeadReComp : f ≠ Term.UOp UserOp.re_comp)
    (hHeadSeqUnit : f ≠ Term.UOp UserOp.seq_unit)
    (hHeadSetSingleton : f ≠ Term.UOp UserOp.set_singleton)
    (hHeadSetChoose : f ≠ Term.UOp UserOp.set_choose)
    (hHeadSetIsEmpty : f ≠ Term.UOp UserOp.set_is_empty)
    (hHeadSetIsSingleton : f ≠ Term.UOp UserOp.set_is_singleton)
    (hHeadQDivByZero : f ≠ Term.UOp UserOp._at_div_by_zero)
    (hHeadUbvToInt : f ≠ Term.UOp UserOp.ubv_to_int)
    (hHeadSbvToInt : f ≠ Term.UOp UserOp.sbv_to_int) :
    False := by
  subst f
  have hUnary :
      SubstituteSupport.substitute_uopHasUnarySmtTranslation op = true :=
    SubstituteSupport.substitute_uopHasUnarySmtTranslation_eq_true_of_apply_translation
      hTrans
  cases op <;>
    simp [SubstituteSupport.substitute_uopHasUnarySmtTranslation] at hUnary
  all_goals
    first
    | exact hHeadNot rfl
    | exact hHeadDistinct rfl
    | exact hHeadPurify rfl
    | exact hHeadToReal rfl
    | exact hHeadToInt rfl
    | exact hHeadIsInt rfl
    | exact hHeadAbs rfl
    | exact hHeadUneg rfl
    | exact hHeadPow2 rfl
    | exact hHeadLog2 rfl
    | exact hHeadIntIspow2 rfl
    | exact hHeadIntDivByZero rfl
    | exact hHeadModByZero rfl
    | exact hHeadBvsize rfl
    | exact hHeadBvnot rfl
    | exact hHeadBvneg rfl
    | exact hHeadBvnego rfl
    | exact hHeadBvredand rfl
    | exact hHeadBvredor rfl
    | exact hHeadStrLen rfl
    | exact hHeadStrRev rfl
    | exact hHeadStrToLower rfl
    | exact hHeadStrToUpper rfl
    | exact hHeadStrToCode rfl
    | exact hHeadStrFromCode rfl
    | exact hHeadStrIsDigit rfl
    | exact hHeadStrToInt rfl
    | exact hHeadStrFromInt rfl
    | exact hHeadStrToRe rfl
    | exact hHeadStringsStoiNonDigit rfl
    | exact hHeadReMult rfl
    | exact hHeadRePlus rfl
    | exact hHeadReOpt rfl
    | exact hHeadReComp rfl
    | exact hHeadSeqUnit rfl
    | exact hHeadSetSingleton rfl
    | exact hHeadSetChoose rfl
    | exact hHeadSetIsEmpty rfl
    | exact hHeadSetIsSingleton rfl
    | exact hHeadQDivByZero rfl
    | exact hHeadUbvToInt rfl
    | exact hHeadSbvToInt rfl
    | cases hUnary


/--
Size-recursive form of combined substitution preservation under an arbitrary
bound-variable accumulator.

`SubstActualsHaveSmtTypes` is the stronger, instantiate-facing side condition:
it implies the exact EO entry type facts consumed by the older type-preservation
theorem and also carries the SMT-translation/type facts consumed by the older
translatability theorem.
-/
theorem substitute_simul_preserves_type_and_translation_with_binder_lt
    {isRename : Bool}
    (n : Nat) (F xs ts bvs : Term)
    (hBinderCase : SubstitutionBinderHandler isRename xs ts)
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
      (hFTrans : RuleProofs.eo_has_smt_translation F)
      (hTs : EoListAllHaveSmtTranslation ts)
      (hActuals : SubstActualsHaveSmtTypes xs ts)
      (hTy : __eo_typeof (substResult isRename F xs ts bvs) ≠ Term.Stuck) :
      SubstitutionPreservationResult isRename F xs ts bvs := by
    cases n with
    | zero =>
        omega
    | succ n =>
      have hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ts :=
        SubstActualsHaveSmtTypes.entry_eo_type_eq hActuals
      let hRec : SubstitutionPreservationRec isRename F xs ts :=
        fun {G bvs'} {xsVars' bvsVars'} hGLt hXsEnv' hBvsEnv'
            hGTrans hTs' hActuals' hGTy =>
          substitute_simul_preserves_type_and_translation_with_binder_lt
            n G xs ts bvs' hBinderCase
            (by omega) hXsEnv' hBvsEnv' hGTrans hTs' hActuals' hGTy
      by_cases hApply : ∃ f a, F = Term.Apply f a
      · rcases hApply with ⟨f, a, rfl⟩
        by_cases hBinder :
            ∃ q v vs,
              f =
                Term.Apply q
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        · rcases hBinder with ⟨q, v, vs, rfl⟩
          exact
            hBinderCase q v vs a bvs
              hXsEnv hBvsEnv hFTrans hTs hActuals hTy hRec
        · by_cases hHeadVar : ∃ name T, f = Term.Var name T
          · rcases hHeadVar with ⟨name, T, rfl⟩
            let aSub :=
              __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
            have hNotBinder :
                ∀ q v vs,
                  Term.Var name T ≠
                    Term.Apply q
                      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
              intro q v vs hEq
              cases hEq
            have hArgs :=
              SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                (Term.Var name T) a
                (by rfl)
                (SubstituteSupport.var_apply_generic_smt_type name T a)
                hFTrans
            have hHeadTrans :
                RuleProofs.eo_has_smt_translation (Term.Var name T) :=
              hArgs.1
            have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
            have hHeadNe :
                __substitute_simul_rec (Term.Boolean isRename)
                    (Term.Var name T) xs ts bvs ≠
                  Term.Stuck :=
              SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
                (Term.Var name T) a xs ts bvs hXsEnv hBvsEnv hTs
                hNotBinder hTy
            have hHeadSubTrans :
                RuleProofs.eo_has_smt_translation
                  (__substitute_simul_rec (Term.Boolean isRename)
                    (Term.Var name T) xs ts bvs) :=
              SubstituteSupport.substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
                name T xs ts bvs hXsEnv hBvsEnv hTs hHeadTrans hHeadNe
            have hATy : __eo_typeof aSub ≠ Term.Stuck := by
              simpa [aSub] using
                SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
                  (Term.Var name T) a xs ts bvs hXsEnv hBvsEnv hTs
                  hNotBinder hHeadSubTrans hTy
            have hABoth :
                __eo_typeof aSub = __eo_typeof a ∧
                  RuleProofs.eo_has_smt_translation aSub := by
              simpa [aSub] using
                hRec
                  (G := a) (bvs' := bvs)
                  (by
                    simp
                    omega)
                  hXsEnv hBvsEnv hATrans hTs hActuals
                  (by simpa [aSub] using hATy)
            refine ⟨?_, ?_⟩
            · exact
                SubstituteSupport.substitute_simul_rec_apply_var_typeof_eq_of_typeof_ne_stuck
                  name T a xs ts bvs
                  hXsEnv hBvsEnv hTs hEntryTypes hNotBinder
                  (by rfl)
                  (SubstituteSupport.var_apply_generic_smt_type name T a)
                  hFTrans
                  (fun _ _ => by simpa [aSub] using hABoth.1)
                  hTy
            · exact
                SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
                  (Term.Var name T) a xs ts bvs hXsEnv hBvsEnv hTs
                  hNotBinder hHeadSubTrans
                  (by simpa [aSub] using hABoth.2)
                  hTy
          · by_cases hHeadUConst : ∃ i U, f = Term.UConst i U
            · rcases hHeadUConst with ⟨i, U, rfl⟩
              let aSub :=
                __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
              have hNotBinder :
                  ∀ q v vs,
                    Term.UConst i U ≠
                      Term.Apply q
                        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
                intro q v vs hEq
                cases hEq
              have hTranslate :
                  __eo_to_smt (Term.Apply (Term.UConst i U) a) =
                    SmtTerm.Apply (__eo_to_smt (Term.UConst i U))
                      (__eo_to_smt a) := by
                rfl
              have hGeneric :
                  __smtx_typeof
                      (SmtTerm.Apply (__eo_to_smt (Term.UConst i U))
                        (__eo_to_smt a)) =
                    __smtx_typeof_apply
                      (__smtx_typeof (__eo_to_smt (Term.UConst i U)))
                      (__smtx_typeof (__eo_to_smt a)) := by
                change
                  __smtx_typeof
                      (SmtTerm.Apply
                        (SmtTerm.UConst
                          (native_uconst_id i)
                          (__eo_to_smt_type U))
                        (__eo_to_smt a)) =
                    __smtx_typeof_apply
                      (__smtx_typeof
                        (SmtTerm.UConst
                          (native_uconst_id i)
                          (__eo_to_smt_type U)))
                      (__smtx_typeof (__eo_to_smt a))
                rw [__smtx_typeof.eq_def]
              have hArgs :=
                SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                  (Term.UConst i U) a hTranslate hGeneric hFTrans
              have hHeadTrans :
                  RuleProofs.eo_has_smt_translation (Term.UConst i U) :=
                hArgs.1
              have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
              have hHeadNe :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.UConst i U) xs ts bvs ≠
                    Term.Stuck :=
                SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
                  (Term.UConst i U) a xs ts bvs hXsEnv hBvsEnv hTs
                  hNotBinder hTy
              have hHeadSubTrans :
                  RuleProofs.eo_has_smt_translation
                    (__substitute_simul_rec (Term.Boolean isRename)
                      (Term.UConst i U) xs ts bvs) :=
                SubstituteSupport.substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
                  (Term.UConst i U) xs ts bvs hXsEnv hBvsEnv hTs
                  (by intro f x h; cases h)
                  (by intro name T h; cases h)
                  (by intro h; cases h)
                  hHeadTrans hHeadNe
              have hATy : __eo_typeof aSub ≠ Term.Stuck := by
                simpa [aSub] using
                  SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
                    (Term.UConst i U) a xs ts bvs hXsEnv hBvsEnv hTs
                    hNotBinder hHeadSubTrans hTy
              have hABoth :
                  __eo_typeof aSub = __eo_typeof a ∧
                    RuleProofs.eo_has_smt_translation aSub := by
                simpa [aSub] using
                  hRec
                    (G := a) (bvs' := bvs)
                    (by
                      simp
                      omega)
                    hXsEnv hBvsEnv hATrans hTs hActuals
                    (by simpa [aSub] using hATy)
              refine ⟨?_, ?_⟩
              · exact
                  SubstituteSupport.substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
                    (Term.UConst i U) a xs ts bvs
                    hXsEnv hBvsEnv hTs
                    (by intro f x h; cases h)
                    (by intro name T h; cases h)
                    (by intro h; cases h)
                    hNotBinder hTranslate hGeneric hFTrans
                    (fun _ _ => by simpa [aSub] using hABoth.1)
                    hTy
              · exact
                  SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
                    (Term.UConst i U) a xs ts bvs hXsEnv hBvsEnv hTs
                    hNotBinder hHeadSubTrans
                    (by simpa [aSub] using hABoth.2)
                    hTy
            · by_cases hHeadDtCons : ∃ s d i, f = Term.DtCons s d i
              · rcases hHeadDtCons with ⟨s, d, i, rfl⟩
                let aSub :=
                  __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
                have hNotBinder :
                    ∀ q v vs,
                      Term.DtCons s d i ≠
                        Term.Apply q
                          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
                  intro q v vs hEq
                  cases hEq
                have hTranslate :
                    __eo_to_smt (Term.Apply (Term.DtCons s d i) a) =
                      SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i))
                        (__eo_to_smt a) := by
                  rfl
                have hGeneric :
                    __smtx_typeof
                        (SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i))
                          (__eo_to_smt a)) =
                      __smtx_typeof_apply
                        (__smtx_typeof (__eo_to_smt (Term.DtCons s d i)))
                        (__smtx_typeof (__eo_to_smt a)) := by
                  have hReserved :
                      __eo_to_smt_reserved_datatype_name s = false :=
                    SubstituteSupport.dtcons_reserved_false_of_apply_has_smt_translation
                      hFTrans
                  change
                    __smtx_typeof
                        (SmtTerm.Apply
                          (native_ite
                            (__eo_to_smt_reserved_datatype_name s)
                            SmtTerm.None
                            (SmtTerm.DtCons s
                              (__eo_to_smt_datatype_decl d)
                              i))
                          (__eo_to_smt a)) =
                      __smtx_typeof_apply
                        (__smtx_typeof
                          (native_ite
                            (__eo_to_smt_reserved_datatype_name s)
                            SmtTerm.None
                            (SmtTerm.DtCons s
                              (__eo_to_smt_datatype_decl d)
                              i)))
                        (__smtx_typeof (__eo_to_smt a))
                  rw [hReserved]
                  simp [native_ite]
                  rw [__smtx_typeof.eq_def]
                have hArgs :=
                  SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                    (Term.DtCons s d i) a hTranslate hGeneric hFTrans
                have hHeadTrans :
                    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) :=
                  hArgs.1
                have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
                have hHeadNe :
                    __substitute_simul_rec (Term.Boolean isRename)
                        (Term.DtCons s d i) xs ts bvs ≠
                      Term.Stuck :=
                  SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
                    (Term.DtCons s d i) a xs ts bvs hXsEnv hBvsEnv hTs
                    hNotBinder hTy
                have hHeadSubTrans :
                    RuleProofs.eo_has_smt_translation
                      (__substitute_simul_rec (Term.Boolean isRename)
                        (Term.DtCons s d i) xs ts bvs) :=
                  SubstituteSupport.substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
                    (Term.DtCons s d i) xs ts bvs hXsEnv hBvsEnv hTs
                    (by intro f x h; cases h)
                    (by intro name T h; cases h)
                    (by intro h; cases h)
                    hHeadTrans hHeadNe
                have hATy : __eo_typeof aSub ≠ Term.Stuck := by
                  simpa [aSub] using
                    SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
                      (Term.DtCons s d i) a xs ts bvs hXsEnv hBvsEnv hTs
                      hNotBinder hHeadSubTrans hTy
                have hABoth :
                    __eo_typeof aSub = __eo_typeof a ∧
                      RuleProofs.eo_has_smt_translation aSub := by
                  simpa [aSub] using
                    hRec
                      (G := a) (bvs' := bvs)
                      (by
                        simp
                        omega)
                      hXsEnv hBvsEnv hATrans hTs hActuals
                      (by simpa [aSub] using hATy)
                refine ⟨?_, ?_⟩
                · exact
                    SubstituteSupport.substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
                      (Term.DtCons s d i) a xs ts bvs
                      hXsEnv hBvsEnv hTs
                      (by intro f x h; cases h)
                      (by intro name T h; cases h)
                      (by intro h; cases h)
                      hNotBinder hTranslate hGeneric hFTrans
                      (fun _ _ => by simpa [aSub] using hABoth.1)
                      hTy
                · exact
                    SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
                      (Term.DtCons s d i) a xs ts bvs hXsEnv hBvsEnv hTs
                      hNotBinder hHeadSubTrans
                      (by simpa [aSub] using hABoth.2)
                      hTy
              · by_cases hHeadApply : ∃ g x, f = Term.Apply g x
                · rcases hHeadApply with ⟨g, x1, rfl⟩
                  by_cases hHeadAnd : g = Term.UOp UserOp.and
                  · subst g
                    exact
                      substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                        UserOp.and x1 a xs ts bvs hXsEnv hBvsEnv hTs
                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                        hFTrans hTy
                        (fun h =>
                          and_args_have_smt_translation_of_has_smt_translation h)
                        (fun X Y hApp => by
                          change
                            __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                              Term.Stuck at hApp
                          cases hXTy : __eo_typeof X <;>
                            cases hYTy : __eo_typeof Y <;>
                            simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢)
                        (fun X₁ Y₁ X₂ Y₂ hX hY => by
                          change
                            __eo_typeof_or (__eo_typeof X₁) (__eo_typeof X₂) =
                              __eo_typeof_or (__eo_typeof Y₁) (__eo_typeof Y₂)
                          rw [hX, hY])
                        (fun X Y hXTrans hYTrans hApp => by
                          unfold RuleProofs.eo_has_smt_translation
                          change
                            __smtx_typeof
                                (SmtTerm.and (__eo_to_smt X) (__eo_to_smt Y)) ≠
                              SmtType.None
                          change
                            __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                              Term.Stuck at hApp
                          have hArgTy :
                              __eo_typeof X = Term.Bool ∧
                                __eo_typeof Y = Term.Bool := by
                            cases hXTy : __eo_typeof X <;>
                              cases hYTy : __eo_typeof Y <;>
                              simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢
                          have hXSmt :=
                            TranslationProofs.eo_to_smt_typeof_matches_translation
                              X hXTrans
                          have hYSmt :=
                            TranslationProofs.eo_to_smt_typeof_matches_translation
                              Y hYTrans
                          rw [typeof_and_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                          simp [native_ite, native_Teq])
                        (fun hXTrans hXTy =>
                          hRec
                            (G := x1) (bvs' := bvs)
                            (by simp; omega)
                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                        (fun hATrans hATy =>
                          hRec
                            (G := a) (bvs' := bvs)
                            (by simp; omega)
                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                  · by_cases hHeadOr : g = Term.UOp UserOp.or
                    · subst g
                      exact
                        substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                          UserOp.or x1 a xs ts bvs hXsEnv hBvsEnv hTs
                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                          hFTrans hTy
                          (fun h =>
                            or_args_have_smt_translation_of_has_smt_translation h)
                          (fun X Y hApp => by
                            change
                              __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                                Term.Stuck at hApp
                            cases hXTy : __eo_typeof X <;>
                              cases hYTy : __eo_typeof Y <;>
                              simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢)
                          (fun X₁ Y₁ X₂ Y₂ hX hY => by
                            change
                              __eo_typeof_or (__eo_typeof X₁) (__eo_typeof X₂) =
                                __eo_typeof_or (__eo_typeof Y₁) (__eo_typeof Y₂)
                            rw [hX, hY])
                          (fun X Y hXTrans hYTrans hApp => by
                            unfold RuleProofs.eo_has_smt_translation
                            change
                              __smtx_typeof
                                  (SmtTerm.or (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                SmtType.None
                            change
                              __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                                Term.Stuck at hApp
                            have hArgTy :
                                __eo_typeof X = Term.Bool ∧
                                  __eo_typeof Y = Term.Bool := by
                              cases hXTy : __eo_typeof X <;>
                                cases hYTy : __eo_typeof Y <;>
                                simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢
                            have hXSmt :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                X hXTrans
                            have hYSmt :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                Y hYTrans
                            rw [typeof_or_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                            simp [native_ite, native_Teq])
                          (fun hXTrans hXTy =>
                            hRec
                              (G := x1) (bvs' := bvs)
                              (by simp; omega)
                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                          (fun hATrans hATy =>
                            hRec
                              (G := a) (bvs' := bvs)
                              (by simp; omega)
                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                    · by_cases hHeadImp : g = Term.UOp UserOp.imp
                      · subst g
                        exact
                          substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                            UserOp.imp x1 a xs ts bvs hXsEnv hBvsEnv hTs
                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                            hFTrans hTy
                            (fun h =>
                              imp_args_have_smt_translation_of_has_smt_translation h)
                            (fun X Y hApp => by
                              change
                                __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                                  Term.Stuck at hApp
                              cases hXTy : __eo_typeof X <;>
                                cases hYTy : __eo_typeof Y <;>
                                simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢)
                            (fun X₁ Y₁ X₂ Y₂ hX hY => by
                              change
                                __eo_typeof_or (__eo_typeof X₁) (__eo_typeof X₂) =
                                  __eo_typeof_or (__eo_typeof Y₁) (__eo_typeof Y₂)
                              rw [hX, hY])
                            (fun X Y hXTrans hYTrans hApp => by
                              unfold RuleProofs.eo_has_smt_translation
                              change
                                __smtx_typeof
                                    (SmtTerm.imp (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                  SmtType.None
                              change
                                __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                                  Term.Stuck at hApp
                              have hArgTy :
                                  __eo_typeof X = Term.Bool ∧
                                    __eo_typeof Y = Term.Bool := by
                                cases hXTy : __eo_typeof X <;>
                                  cases hYTy : __eo_typeof Y <;>
                                  simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢
                              have hXSmt :=
                                TranslationProofs.eo_to_smt_typeof_matches_translation
                                  X hXTrans
                              have hYSmt :=
                                TranslationProofs.eo_to_smt_typeof_matches_translation
                                  Y hYTrans
                              rw [typeof_imp_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                              simp [native_ite, native_Teq])
                            (fun hXTrans hXTy =>
                              hRec
                                (G := x1) (bvs' := bvs)
                                (by simp; omega)
                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                            (fun hATrans hATy =>
                              hRec
                                (G := a) (bvs' := bvs)
                                (by simp; omega)
                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                      · by_cases hHeadXor : g = Term.UOp UserOp.xor
                        · subst g
                          exact
                            substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                              UserOp.xor x1 a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans hTy
                              (fun h =>
                                xor_args_have_smt_translation_of_has_smt_translation h)
                              (fun X Y hApp => by
                                change
                                  __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                                    Term.Stuck at hApp
                                cases hXTy : __eo_typeof X <;>
                                  cases hYTy : __eo_typeof Y <;>
                                  simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢)
                              (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                change
                                  __eo_typeof_or (__eo_typeof X₁) (__eo_typeof X₂) =
                                    __eo_typeof_or (__eo_typeof Y₁) (__eo_typeof Y₂)
                                rw [hX, hY])
                              (fun X Y hXTrans hYTrans hApp => by
                                unfold RuleProofs.eo_has_smt_translation
                                change
                                  __smtx_typeof
                                      (SmtTerm.xor (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                    SmtType.None
                                change
                                  __eo_typeof_or (__eo_typeof X) (__eo_typeof Y) ≠
                                    Term.Stuck at hApp
                                have hArgTy :
                                    __eo_typeof X = Term.Bool ∧
                                      __eo_typeof Y = Term.Bool := by
                                  cases hXTy : __eo_typeof X <;>
                                    cases hYTy : __eo_typeof Y <;>
                                    simp [__eo_typeof_or, hXTy, hYTy] at hApp ⊢
                                have hXSmt :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    X hXTrans
                                have hYSmt :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    Y hYTrans
                                rw [typeof_xor_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                                simp [native_ite, native_Teq])
                              (fun hXTrans hXTy =>
                                hRec
                                  (G := x1) (bvs' := bvs)
                                  (by simp; omega)
                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                              (fun hATrans hATy =>
                                hRec
                                  (G := a) (bvs' := bvs)
                                  (by simp; omega)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                        · by_cases hHeadEq : g = Term.UOp UserOp.eq
                          · subst g
                            exact
                              substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                UserOp.eq x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                hFTrans hTy
                                (fun h =>
                                  eq_args_have_smt_translation_of_has_smt_translation h)
                                (fun X Y hApp => by
                                  change
                                    __eo_typeof_eq (__eo_typeof X) (__eo_typeof Y) ≠
                                      Term.Stuck at hApp
                                  have hEqTy :=
                                    eo_typeof_eq_eq_bool_of_ne_stuck hApp
                                  exact
                                    eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof X) (__eo_typeof Y) hEqTy)
                                (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                  change
                                    __eo_typeof_eq (__eo_typeof X₁) (__eo_typeof X₂) =
                                      __eo_typeof_eq (__eo_typeof Y₁) (__eo_typeof Y₂)
                                  rw [hX, hY])
                                (fun X Y hXTrans hYTrans hApp => by
                                  unfold RuleProofs.eo_has_smt_translation
                                  change
                                    __smtx_typeof
                                        (SmtTerm.eq (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                      SmtType.None
                                  change
                                    __eo_typeof_eq (__eo_typeof X) (__eo_typeof Y) ≠
                                      Term.Stuck at hApp
                                  have hEqTy :
                                      __eo_typeof_eq (__eo_typeof X) (__eo_typeof Y) =
                                        Term.Bool :=
                                    eo_typeof_eq_eq_bool_of_ne_stuck hApp
                                  have hTypesEq :
                                      __eo_typeof X = __eo_typeof Y :=
                                    support_eo_typeof_eq_bool_operands_eq
                                      (__eo_typeof X) (__eo_typeof Y) hEqTy
                                  have hXSmt :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                      X hXTrans
                                  have hYSmt :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                      Y hYTrans
                                  have hXNN :
                                      __eo_to_smt_type (__eo_typeof X) ≠ SmtType.None :=
                                    eo_to_smt_typeof_ne_none_of_has_smt_translation
                                      X hXTrans
                                  have hYNN :
                                      __eo_to_smt_type (__eo_typeof Y) ≠ SmtType.None :=
                                    eo_to_smt_typeof_ne_none_of_has_smt_translation
                                      Y hYTrans
                                  rw [typeof_eq_eq, hXSmt, hYSmt, hTypesEq]
                                  exact smt_typeof_eq_self_ne_none_of_ne_none hYNN)
                                (fun hXTrans hXTy =>
                                  hRec
                                    (G := x1) (bvs' := bvs)
                                    (by simp; omega)
                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                (fun hATrans hATy =>
                                  hRec
                                    (G := a) (bvs' := bvs)
                                    (by simp; omega)
                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                          · by_cases hHeadPlus : g = Term.UOp UserOp.plus
                            · subst g
                              exact
                                substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                  UserOp.plus x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                  hFTrans hTy
                                  (fun h =>
                                    plus_args_have_smt_translation_of_has_smt_translation h)
                                  (fun X Y hApp => by
                                    change
                                      __eo_typeof_plus (__eo_typeof X) (__eo_typeof Y) ≠
                                        Term.Stuck at hApp
                                    rcases
                                        eo_typeof_plus_arg_types_of_ne_stuck hApp with
                                      ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
                                    · constructor
                                      · rw [hXTy]
                                        decide
                                      · rw [hYTy]
                                        decide
                                    · constructor
                                      · rw [hXTy]
                                        decide
                                      · rw [hYTy]
                                        decide)
                                  (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                    change
                                      __eo_typeof_plus (__eo_typeof X₁) (__eo_typeof X₂) =
                                        __eo_typeof_plus (__eo_typeof Y₁) (__eo_typeof Y₂)
                                    rw [hX, hY])
                                  (fun X Y hXTrans hYTrans hApp => by
                                    unfold RuleProofs.eo_has_smt_translation
                                    change
                                      __smtx_typeof
                                          (SmtTerm.plus (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                        SmtType.None
                                    change
                                      __eo_typeof_plus (__eo_typeof X) (__eo_typeof Y) ≠
                                        Term.Stuck at hApp
                                    have hXSmt :=
                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                        X hXTrans
                                    have hYSmt :=
                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                        Y hYTrans
                                    rcases
                                        eo_typeof_plus_arg_types_of_ne_stuck hApp with
                                      ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
                                    · rw [typeof_plus_eq, hXSmt, hYSmt, hXTy, hYTy]
                                      simp [__eo_to_smt_type,
                                        __smtx_typeof_arith_overload_op_2]
                                    · rw [typeof_plus_eq, hXSmt, hYSmt, hXTy, hYTy]
                                      simp [__eo_to_smt_type,
                                        __smtx_typeof_arith_overload_op_2])
                                  (fun hXTrans hXTy =>
                                    hRec
                                      (G := x1) (bvs' := bvs)
                                      (by simp; omega)
                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                  (fun hATrans hATy =>
                                    hRec
                                      (G := a) (bvs' := bvs)
                                      (by simp; omega)
                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                            · by_cases hHeadNeg : g = Term.UOp UserOp.neg
                              · subst g
                                exact
                                  substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                    UserOp.neg x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                    hFTrans hTy
                                    (fun h =>
                                      neg_args_have_smt_translation_of_has_smt_translation h)
                                    (fun X Y hApp => by
                                      change
                                        __eo_typeof_plus (__eo_typeof X) (__eo_typeof Y) ≠
                                          Term.Stuck at hApp
                                      rcases
                                          eo_typeof_plus_arg_types_of_ne_stuck hApp with
                                        ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
                                      · constructor
                                        · rw [hXTy]
                                          decide
                                        · rw [hYTy]
                                          decide
                                      · constructor
                                        · rw [hXTy]
                                          decide
                                        · rw [hYTy]
                                          decide)
                                    (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                      change
                                        __eo_typeof_plus (__eo_typeof X₁) (__eo_typeof X₂) =
                                          __eo_typeof_plus (__eo_typeof Y₁) (__eo_typeof Y₂)
                                      rw [hX, hY])
                                    (fun X Y hXTrans hYTrans hApp => by
                                      unfold RuleProofs.eo_has_smt_translation
                                      change
                                        __smtx_typeof
                                            (SmtTerm.neg (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                          SmtType.None
                                      change
                                        __eo_typeof_plus (__eo_typeof X) (__eo_typeof Y) ≠
                                          Term.Stuck at hApp
                                      have hXSmt :=
                                        TranslationProofs.eo_to_smt_typeof_matches_translation
                                          X hXTrans
                                      have hYSmt :=
                                        TranslationProofs.eo_to_smt_typeof_matches_translation
                                          Y hYTrans
                                      rcases
                                          eo_typeof_plus_arg_types_of_ne_stuck hApp with
                                        ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
                                      · rw [typeof_neg_eq, hXSmt, hYSmt, hXTy, hYTy]
                                        simp [__eo_to_smt_type,
                                          __smtx_typeof_arith_overload_op_2]
                                      · rw [typeof_neg_eq, hXSmt, hYSmt, hXTy, hYTy]
                                        simp [__eo_to_smt_type,
                                          __smtx_typeof_arith_overload_op_2])
                                    (fun hXTrans hXTy =>
                                      hRec
                                        (G := x1) (bvs' := bvs)
                                        (by simp; omega)
                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                    (fun hATrans hATy =>
                                      hRec
                                        (G := a) (bvs' := bvs)
                                        (by simp; omega)
                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                              · by_cases hHeadMult : g = Term.UOp UserOp.mult
                                · subst g
                                  exact
                                    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                      UserOp.mult x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                      hFTrans hTy
                                      (fun h =>
                                        mult_args_have_smt_translation_of_has_smt_translation h)
                                      (fun X Y hApp => by
                                        change
                                          __eo_typeof_plus (__eo_typeof X) (__eo_typeof Y) ≠
                                            Term.Stuck at hApp
                                        rcases
                                            eo_typeof_plus_arg_types_of_ne_stuck hApp with
                                          ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
                                        · constructor
                                          · rw [hXTy]
                                            decide
                                          · rw [hYTy]
                                            decide
                                        · constructor
                                          · rw [hXTy]
                                            decide
                                          · rw [hYTy]
                                            decide)
                                      (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                        change
                                          __eo_typeof_plus (__eo_typeof X₁) (__eo_typeof X₂) =
                                            __eo_typeof_plus (__eo_typeof Y₁) (__eo_typeof Y₂)
                                        rw [hX, hY])
                                      (fun X Y hXTrans hYTrans hApp => by
                                        unfold RuleProofs.eo_has_smt_translation
                                        change
                                          __smtx_typeof
                                              (SmtTerm.mult (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                            SmtType.None
                                        change
                                          __eo_typeof_plus (__eo_typeof X) (__eo_typeof Y) ≠
                                            Term.Stuck at hApp
                                        have hXSmt :=
                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                            X hXTrans
                                        have hYSmt :=
                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                            Y hYTrans
                                        rcases
                                            eo_typeof_plus_arg_types_of_ne_stuck hApp with
                                          ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
                                        · rw [typeof_mult_eq, hXSmt, hYSmt, hXTy, hYTy]
                                          simp [__eo_to_smt_type,
                                            __smtx_typeof_arith_overload_op_2]
                                        · rw [typeof_mult_eq, hXSmt, hYSmt, hXTy, hYTy]
                                          simp [__eo_to_smt_type,
                                            __smtx_typeof_arith_overload_op_2])
                                      (fun hXTrans hXTy =>
                                        hRec
                                          (G := x1) (bvs' := bvs)
                                          (by simp; omega)
                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                      (fun hATrans hATy =>
                                        hRec
                                          (G := a) (bvs' := bvs)
                                          (by simp; omega)
                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                · by_cases hHeadLt : g = Term.UOp UserOp.lt
                                  · subst g
                                    exact
                                      substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                        UserOp.lt x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                        hFTrans hTy
                                        (fun h =>
                                          lt_args_have_smt_translation_of_has_smt_translation h)
                                        (fun X Y hApp => by
                                          change
                                            __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                              Term.Stuck at hApp
                                          exact
                                            eo_typeof_lt_args_not_stuck_of_ne_stuck hApp)
                                        (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                          change
                                            __eo_typeof_lt (__eo_typeof X₁) (__eo_typeof X₂) =
                                              __eo_typeof_lt (__eo_typeof Y₁) (__eo_typeof Y₂)
                                          rw [hX, hY])
                                        (fun X Y hXTrans hYTrans hApp => by
                                          unfold RuleProofs.eo_has_smt_translation
                                          change
                                            __smtx_typeof
                                                (SmtTerm.lt (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                              SmtType.None
                                          change
                                            __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                              Term.Stuck at hApp
                                          rw [typeof_lt_eq]
                                          exact
                                            smt_arith_ret_bool_non_none_of_eo_typeof_lt_ne_stuck
                                              X Y hXTrans hYTrans hApp)
                                        (fun hXTrans hXTy =>
                                          hRec
                                            (G := x1) (bvs' := bvs)
                                            (by simp; omega)
                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                        (fun hATrans hATy =>
                                          hRec
                                            (G := a) (bvs' := bvs)
                                            (by simp; omega)
                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                  · by_cases hHeadLeq : g = Term.UOp UserOp.leq
                                    · subst g
                                      exact
                                        substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                          UserOp.leq x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                          hFTrans hTy
                                          (fun h =>
                                            leq_args_have_smt_translation_of_has_smt_translation h)
                                          (fun X Y hApp => by
                                            change
                                              __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                Term.Stuck at hApp
                                            exact
                                              eo_typeof_lt_args_not_stuck_of_ne_stuck hApp)
                                          (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                            change
                                              __eo_typeof_lt (__eo_typeof X₁) (__eo_typeof X₂) =
                                                __eo_typeof_lt (__eo_typeof Y₁) (__eo_typeof Y₂)
                                            rw [hX, hY])
                                          (fun X Y hXTrans hYTrans hApp => by
                                            unfold RuleProofs.eo_has_smt_translation
                                            change
                                              __smtx_typeof
                                                  (SmtTerm.leq (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                SmtType.None
                                            change
                                              __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                Term.Stuck at hApp
                                            rw [typeof_leq_eq]
                                            exact
                                              smt_arith_ret_bool_non_none_of_eo_typeof_lt_ne_stuck
                                                X Y hXTrans hYTrans hApp)
                                          (fun hXTrans hXTy =>
                                            hRec
                                              (G := x1) (bvs' := bvs)
                                              (by simp; omega)
                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                          (fun hATrans hATy =>
                                            hRec
                                              (G := a) (bvs' := bvs)
                                              (by simp; omega)
                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                    · by_cases hHeadGt : g = Term.UOp UserOp.gt
                                      · subst g
                                        exact
                                          substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                            UserOp.gt x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                            hFTrans hTy
                                            (fun h =>
                                              gt_args_have_smt_translation_of_has_smt_translation h)
                                            (fun X Y hApp => by
                                              change
                                                __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                  Term.Stuck at hApp
                                              exact
                                                eo_typeof_lt_args_not_stuck_of_ne_stuck hApp)
                                            (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                              change
                                                __eo_typeof_lt (__eo_typeof X₁) (__eo_typeof X₂) =
                                                  __eo_typeof_lt (__eo_typeof Y₁) (__eo_typeof Y₂)
                                              rw [hX, hY])
                                            (fun X Y hXTrans hYTrans hApp => by
                                              unfold RuleProofs.eo_has_smt_translation
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.gt (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                  SmtType.None
                                              change
                                                __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                  Term.Stuck at hApp
                                              rw [typeof_gt_eq]
                                              exact
                                                smt_arith_ret_bool_non_none_of_eo_typeof_lt_ne_stuck
                                                  X Y hXTrans hYTrans hApp)
                                            (fun hXTrans hXTy =>
                                              hRec
                                                (G := x1) (bvs' := bvs)
                                                (by simp; omega)
                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                            (fun hATrans hATy =>
                                              hRec
                                                (G := a) (bvs' := bvs)
                                                (by simp; omega)
                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                      · by_cases hHeadGeq : g = Term.UOp UserOp.geq
                                        · subst g
                                          exact
                                            substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                              UserOp.geq x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans hTy
                                              (fun h =>
                                                geq_args_have_smt_translation_of_has_smt_translation h)
                                              (fun X Y hApp => by
                                                change
                                                  __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                    Term.Stuck at hApp
                                                exact
                                                  eo_typeof_lt_args_not_stuck_of_ne_stuck hApp)
                                              (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                change
                                                  __eo_typeof_lt (__eo_typeof X₁) (__eo_typeof X₂) =
                                                    __eo_typeof_lt (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                rw [hX, hY])
                                              (fun X Y hXTrans hYTrans hApp => by
                                                unfold RuleProofs.eo_has_smt_translation
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.geq (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                    SmtType.None
                                                change
                                                  __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                    Term.Stuck at hApp
                                                rw [typeof_geq_eq]
                                                exact
                                                  smt_arith_ret_bool_non_none_of_eo_typeof_lt_ne_stuck
                                                    X Y hXTrans hYTrans hApp)
                                              (fun hXTrans hXTy =>
                                                hRec
                                                  (G := x1) (bvs' := bvs)
                                                  (by simp; omega)
                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                              (fun hATrans hATy =>
                                                hRec
                                                  (G := a) (bvs' := bvs)
                                                  (by simp; omega)
                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                        · by_cases hHeadDiv : g = Term.UOp UserOp.div
                                          · subst g
                                            exact
                                              substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                UserOp.div x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans hTy
                                                (fun h =>
                                                  div_args_have_smt_translation_of_has_smt_translation h)
                                                (fun X Y hApp => by
                                                  change
                                                    __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                      Term.Stuck at hApp
                                                  exact
                                                    eo_int_binop_args_not_stuck
                                                      (eo_typeof_div_arg_types_of_ne_stuck hApp))
                                                (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                  change
                                                    __eo_typeof_div (__eo_typeof X₁) (__eo_typeof X₂) =
                                                      __eo_typeof_div (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                  rw [hX, hY])
                                                (fun X Y hXTrans hYTrans hApp => by
                                                  unfold RuleProofs.eo_has_smt_translation
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.div (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                      SmtType.None
                                                  change
                                                    __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                      Term.Stuck at hApp
                                                  have hArgTy :=
                                                    eo_typeof_div_arg_types_of_ne_stuck hApp
                                                  have hXSmt :=
                                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                                      X hXTrans
                                                  have hYSmt :=
                                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                                      Y hYTrans
                                                  rw [typeof_div_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                                                  simp [__eo_to_smt_type, native_ite, native_Teq])
                                                (fun hXTrans hXTy =>
                                                  hRec
                                                    (G := x1) (bvs' := bvs)
                                                    (by simp; omega)
                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                (fun hATrans hATy =>
                                                  hRec
                                                    (G := a) (bvs' := bvs)
                                                    (by simp; omega)
                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                          · by_cases hHeadMod : g = Term.UOp UserOp.mod
                                            · subst g
                                              exact
                                                substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                  UserOp.mod x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans hTy
                                                  (fun h =>
                                                    mod_args_have_smt_translation_of_has_smt_translation h)
                                                  (fun X Y hApp => by
                                                    change
                                                      __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                        Term.Stuck at hApp
                                                    exact
                                                      eo_int_binop_args_not_stuck
                                                        (eo_typeof_div_arg_types_of_ne_stuck hApp))
                                                  (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                    change
                                                      __eo_typeof_div (__eo_typeof X₁) (__eo_typeof X₂) =
                                                        __eo_typeof_div (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                    rw [hX, hY])
                                                  (fun X Y hXTrans hYTrans hApp => by
                                                    unfold RuleProofs.eo_has_smt_translation
                                                    change
                                                      __smtx_typeof
                                                          (SmtTerm.mod (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                        SmtType.None
                                                    change
                                                      __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                        Term.Stuck at hApp
                                                    have hArgTy :=
                                                      eo_typeof_div_arg_types_of_ne_stuck hApp
                                                    have hXSmt :=
                                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                                        X hXTrans
                                                    have hYSmt :=
                                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                                        Y hYTrans
                                                    rw [typeof_mod_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                                                    simp [__eo_to_smt_type, native_ite, native_Teq])
                                                  (fun hXTrans hXTy =>
                                                    hRec
                                                      (G := x1) (bvs' := bvs)
                                                      (by simp; omega)
                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                  (fun hATrans hATy =>
                                                    hRec
                                                      (G := a) (bvs' := bvs)
                                                      (by simp; omega)
                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                            · first
                                              | by_cases hHeadDivisible :
                                                  g = Term.UOp UserOp.divisible
                                                · subst g
                                                  exact
                                                    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                      UserOp.divisible x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans hTy
                                                      (fun h =>
                                                        divisible_args_have_smt_translation_of_has_smt_translation h)
                                                      (fun X Y hApp => by
                                                        change
                                                          __eo_typeof_divisible (__eo_typeof X) (__eo_typeof Y) ≠
                                                            Term.Stuck at hApp
                                                        exact
                                                          eo_int_binop_args_not_stuck
                                                            (eo_typeof_divisible_arg_types_of_ne_stuck hApp))
                                                      (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                        change
                                                          __eo_typeof_divisible (__eo_typeof X₁) (__eo_typeof X₂) =
                                                            __eo_typeof_divisible (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                        rw [hX, hY])
                                                      (fun X Y hXTrans hYTrans hApp => by
                                                        unfold RuleProofs.eo_has_smt_translation
                                                        change
                                                          __smtx_typeof
                                                              (SmtTerm.divisible (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                            SmtType.None
                                                        change
                                                          __eo_typeof_divisible (__eo_typeof X) (__eo_typeof Y) ≠
                                                            Term.Stuck at hApp
                                                        have hArgTy :=
                                                          eo_typeof_divisible_arg_types_of_ne_stuck hApp
                                                        have hXSmt :=
                                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                                            X hXTrans
                                                        have hYSmt :=
                                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                                            Y hYTrans
                                                        rw [typeof_divisible_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                                                        simp [__eo_to_smt_type, native_ite, native_Teq])
                                                      (fun hXTrans hXTy =>
                                                        hRec
                                                          (G := x1) (bvs' := bvs)
                                                          (by simp; omega)
                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                      (fun hATrans hATy =>
                                                        hRec
                                                          (G := a) (bvs' := bvs)
                                                          (by simp; omega)
                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                · by_cases hHeadDivTotal :
                                                    g = Term.UOp UserOp.div_total
                                                  · subst g
                                                    exact
                                                      substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                        UserOp.div_total x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                        hFTrans hTy
                                                        (fun h =>
                                                          div_total_args_have_smt_translation_of_has_smt_translation h)
                                                        (fun X Y hApp => by
                                                          change
                                                            __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                              Term.Stuck at hApp
                                                          exact
                                                            eo_int_binop_args_not_stuck
                                                              (eo_typeof_div_arg_types_of_ne_stuck hApp))
                                                        (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                          change
                                                            __eo_typeof_div (__eo_typeof X₁) (__eo_typeof X₂) =
                                                              __eo_typeof_div (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                          rw [hX, hY])
                                                        (fun X Y hXTrans hYTrans hApp => by
                                                          unfold RuleProofs.eo_has_smt_translation
                                                          change
                                                            __smtx_typeof
                                                                (SmtTerm.div_total (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                              SmtType.None
                                                          change
                                                            __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                              Term.Stuck at hApp
                                                          have hArgTy :=
                                                            eo_typeof_div_arg_types_of_ne_stuck hApp
                                                          have hXSmt :=
                                                            TranslationProofs.eo_to_smt_typeof_matches_translation
                                                              X hXTrans
                                                          have hYSmt :=
                                                            TranslationProofs.eo_to_smt_typeof_matches_translation
                                                              Y hYTrans
                                                          rw [typeof_div_total_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                                                          simp [__eo_to_smt_type, native_ite, native_Teq])
                                                        (fun hXTrans hXTy =>
                                                          hRec
                                                            (G := x1) (bvs' := bvs)
                                                            (by simp; omega)
                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                        (fun hATrans hATy =>
                                                          hRec
                                                            (G := a) (bvs' := bvs)
                                                            (by simp; omega)
                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                  · by_cases hHeadModTotal :
                                                      g = Term.UOp UserOp.mod_total
                                                    · subst g
                                                      exact
                                                        substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                          UserOp.mod_total x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                          hFTrans hTy
                                                          (fun h =>
                                                            mod_total_args_have_smt_translation_of_has_smt_translation h)
                                                          (fun X Y hApp => by
                                                            change
                                                              __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                                Term.Stuck at hApp
                                                            exact
                                                              eo_int_binop_args_not_stuck
                                                                (eo_typeof_div_arg_types_of_ne_stuck hApp))
                                                          (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                            change
                                                              __eo_typeof_div (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                __eo_typeof_div (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                            rw [hX, hY])
                                                          (fun X Y hXTrans hYTrans hApp => by
                                                            unfold RuleProofs.eo_has_smt_translation
                                                            change
                                                              __smtx_typeof
                                                                  (SmtTerm.mod_total (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                SmtType.None
                                                            change
                                                              __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
                                                                Term.Stuck at hApp
                                                            have hArgTy :=
                                                              eo_typeof_div_arg_types_of_ne_stuck hApp
                                                            have hXSmt :=
                                                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                                                X hXTrans
                                                            have hYSmt :=
                                                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                                                Y hYTrans
                                                            rw [typeof_mod_total_eq, hXSmt, hYSmt, hArgTy.1, hArgTy.2]
                                                            simp [__eo_to_smt_type, native_ite, native_Teq])
                                                          (fun hXTrans hXTy =>
                                                            hRec
                                                              (G := x1) (bvs' := bvs)
                                                              (by simp; omega)
                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                          (fun hATrans hATy =>
                                                            hRec
                                                              (G := a) (bvs' := bvs)
                                                              (by simp; omega)
                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                    · first
                                                      | by_cases hHeadQdiv :
                                                          g = Term.UOp UserOp.qdiv
                                                        · subst g
                                                          exact
                                                            substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                              UserOp.qdiv x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                              hFTrans hTy
                                                              (fun h =>
                                                                qdiv_args_have_smt_translation_of_has_smt_translation h)
                                                              (fun X Y hApp => by
                                                                change
                                                                  __eo_typeof_qdiv (__eo_typeof X) (__eo_typeof Y) ≠
                                                                    Term.Stuck at hApp
                                                                exact
                                                                  eo_typeof_qdiv_args_not_stuck_of_ne_stuck hApp)
                                                              (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                change
                                                                  __eo_typeof_qdiv (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                    __eo_typeof_qdiv (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                rw [hX, hY])
                                                              (fun X Y hXTrans hYTrans hApp => by
                                                                unfold RuleProofs.eo_has_smt_translation
                                                                change
                                                                  __smtx_typeof
                                                                      (SmtTerm.qdiv (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                    SmtType.None
                                                                change
                                                                  __eo_typeof_qdiv (__eo_typeof X) (__eo_typeof Y) ≠
                                                                    Term.Stuck at hApp
                                                                rw [typeof_qdiv_eq]
                                                                exact
                                                                  smt_arith_ret_real_non_none_of_eo_typeof_qdiv_ne_stuck
                                                                    X Y hXTrans hYTrans hApp)
                                                              (fun hXTrans hXTy =>
                                                                hRec
                                                                  (G := x1) (bvs' := bvs)
                                                                  (by simp; omega)
                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                              (fun hATrans hATy =>
                                                                hRec
                                                                  (G := a) (bvs' := bvs)
                                                                  (by simp; omega)
                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                        · by_cases hHeadQdivTotal :
                                                            g = Term.UOp UserOp.qdiv_total
                                                          · subst g
                                                            exact
                                                              substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                UserOp.qdiv_total x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                hFTrans hTy
                                                                (fun h =>
                                                                  qdiv_total_args_have_smt_translation_of_has_smt_translation h)
                                                                (fun X Y hApp => by
                                                                  change
                                                                    __eo_typeof_qdiv (__eo_typeof X) (__eo_typeof Y) ≠
                                                                      Term.Stuck at hApp
                                                                  exact
                                                                    eo_typeof_qdiv_args_not_stuck_of_ne_stuck hApp)
                                                                (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                  change
                                                                    __eo_typeof_qdiv (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                      __eo_typeof_qdiv (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                  rw [hX, hY])
                                                                (fun X Y hXTrans hYTrans hApp => by
                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                  change
                                                                    __smtx_typeof
                                                                        (SmtTerm.qdiv_total (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                      SmtType.None
                                                                  change
                                                                    __eo_typeof_qdiv (__eo_typeof X) (__eo_typeof Y) ≠
                                                                      Term.Stuck at hApp
                                                                  rw [typeof_qdiv_total_eq]
                                                                  exact
                                                                    smt_arith_ret_real_non_none_of_eo_typeof_qdiv_ne_stuck
                                                                      X Y hXTrans hYTrans hApp)
                                                                (fun hXTrans hXTy =>
                                                                  hRec
                                                                    (G := x1) (bvs' := bvs)
                                                                    (by simp; omega)
                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                (fun hATrans hATy =>
                                                                  hRec
                                                                    (G := a) (bvs' := bvs)
                                                                    (by simp; omega)
                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                          · by_cases hHeadConcat :
                                                              g = Term.UOp UserOp.concat
                                                            · subst g
                                                              exact
                                                                substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                  UserOp.concat x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                  hFTrans hTy
                                                                  (fun h =>
                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                      (eoOp := UserOp.concat) (smtOp := SmtTerm.concat)
                                                                      (by rfl) bv_concat_args_have_smt_translation_of_non_none h)
                                                                  (fun X Y hApp => by
                                                                    change
                                                                      __eo_typeof_concat (__eo_typeof X) (__eo_typeof Y) ≠
                                                                        Term.Stuck at hApp
                                                                    exact
                                                                      eo_typeof_concat_args_not_stuck_of_ne_stuck hApp)
                                                                  (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                    change
                                                                      __eo_typeof_concat (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                        __eo_typeof_concat (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                    rw [hX, hY])
                                                                  (fun X Y hXTrans hYTrans hApp => by
                                                                    unfold RuleProofs.eo_has_smt_translation
                                                                    change
                                                                      __smtx_typeof
                                                                          (SmtTerm.concat (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                        SmtType.None
                                                                    change
                                                                      __eo_typeof_concat (__eo_typeof X) (__eo_typeof Y) ≠
                                                                        Term.Stuck at hApp
                                                                    rw [typeof_concat_eq]
                                                                    exact
                                                                      smt_concat_non_none_of_eo_typeof_concat_ne_stuck
                                                                        X Y hXTrans hYTrans hApp)
                                                                  (fun hXTrans hXTy =>
                                                                    hRec
                                                                      (G := x1) (bvs' := bvs)
                                                                      (by simp; omega)
                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                  (fun hATrans hATy =>
                                                                    hRec
                                                                      (G := a) (bvs' := bvs)
                                                                      (by simp; omega)
                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                            · by_cases hHeadBvand :
                                                                g = Term.UOp UserOp.bvand
                                                              · subst g
                                                                exact
                                                                  substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                    UserOp.bvand x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                    hFTrans hTy
                                                                    (fun h =>
                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                        (eoOp := UserOp.bvand) (smtOp := SmtTerm.bvand)
                                                                        (by rfl)
                                                                        (fun hNN =>
                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                        h)
                                                                    (fun X Y hApp => by
                                                                      change
                                                                        __eo_typeof_bvand (__eo_typeof X) (__eo_typeof Y) ≠
                                                                          Term.Stuck at hApp
                                                                      exact
                                                                        eo_typeof_bvand_args_not_stuck_of_ne_stuck hApp)
                                                                    (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                      change
                                                                        __eo_typeof_bvand (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                          __eo_typeof_bvand (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                      rw [hX, hY])
                                                                    (fun X Y hXTrans hYTrans hApp => by
                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                      change
                                                                        __smtx_typeof
                                                                            (SmtTerm.bvand (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                          SmtType.None
                                                                      change
                                                                        __eo_typeof_bvand (__eo_typeof X) (__eo_typeof Y) ≠
                                                                          Term.Stuck at hApp
                                                                      rw [__smtx_typeof.eq_def]
                                                                      exact
                                                                        smt_bv_binop_non_none_of_eo_typeof_bvand_ne_stuck
                                                                          X Y hXTrans hYTrans hApp)
                                                                    (fun hXTrans hXTy =>
                                                                      hRec
                                                                        (G := x1) (bvs' := bvs)
                                                                        (by simp; omega)
                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                    (fun hATrans hATy =>
                                                                      hRec
                                                                        (G := a) (bvs' := bvs)
                                                                        (by simp; omega)
                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                              · by_cases hHeadBvor :
                                                                  g = Term.UOp UserOp.bvor
                                                                · subst g
                                                                  exact
                                                                    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                      UserOp.bvor x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                      hFTrans hTy
                                                                      (fun h =>
                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                          (eoOp := UserOp.bvor) (smtOp := SmtTerm.bvor)
                                                                          (by rfl)
                                                                          (fun hNN =>
                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                          h)
                                                                      (fun X Y hApp => by
                                                                        change
                                                                          __eo_typeof_bvand (__eo_typeof X) (__eo_typeof Y) ≠
                                                                            Term.Stuck at hApp
                                                                        exact
                                                                          eo_typeof_bvand_args_not_stuck_of_ne_stuck hApp)
                                                                      (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                        change
                                                                          __eo_typeof_bvand (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                            __eo_typeof_bvand (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                        rw [hX, hY])
                                                                      (fun X Y hXTrans hYTrans hApp => by
                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                        change
                                                                          __smtx_typeof
                                                                              (SmtTerm.bvor (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                            SmtType.None
                                                                        change
                                                                          __eo_typeof_bvand (__eo_typeof X) (__eo_typeof Y) ≠
                                                                            Term.Stuck at hApp
                                                                        rw [__smtx_typeof.eq_def]
                                                                        exact
                                                                          smt_bv_binop_non_none_of_eo_typeof_bvand_ne_stuck
                                                                            X Y hXTrans hYTrans hApp)
                                                                      (fun hXTrans hXTy =>
                                                                        hRec
                                                                          (G := x1) (bvs' := bvs)
                                                                          (by simp; omega)
                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                      (fun hATrans hATy =>
                                                                        hRec
                                                                          (G := a) (bvs' := bvs)
                                                                          (by simp; omega)
                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                · by_cases hHeadBvnand :
                                                                    g = Term.UOp UserOp.bvnand
                                                                  · subst g
                                                                    exact
                                                                      substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                        UserOp.bvnand SmtTerm.bvnand x1 a xs ts bvs
                                                                        hXsEnv hBvsEnv hTs
                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                        hFTrans hTy
                                                                        (fun X Y => by rfl)
                                                                        (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                        (fun X Y => by rfl)
                                                                        (fun hXTrans hXTy =>
                                                                          hRec
                                                                            (G := x1) (bvs' := bvs)
                                                                            (by simp; omega)
                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                        (fun hATrans hATy =>
                                                                          hRec
                                                                            (G := a) (bvs' := bvs)
                                                                            (by simp; omega)
                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                  · by_cases hHeadBvnor :
                                                                      g = Term.UOp UserOp.bvnor
                                                                    · subst g
                                                                      exact
                                                                        substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                          UserOp.bvnor SmtTerm.bvnor x1 a xs ts bvs
                                                                          hXsEnv hBvsEnv hTs
                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                          hFTrans hTy
                                                                          (fun X Y => by rfl)
                                                                          (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                          (fun X Y => by rfl)
                                                                          (fun hXTrans hXTy =>
                                                                            hRec
                                                                              (G := x1) (bvs' := bvs)
                                                                              (by simp; omega)
                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                          (fun hATrans hATy =>
                                                                            hRec
                                                                              (G := a) (bvs' := bvs)
                                                                              (by simp; omega)
                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                    · by_cases hHeadBvxor :
                                                                        g = Term.UOp UserOp.bvxor
                                                                      · subst g
                                                                        exact
                                                                          substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                            UserOp.bvxor SmtTerm.bvxor x1 a xs ts bvs
                                                                            hXsEnv hBvsEnv hTs
                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                            hFTrans hTy
                                                                            (fun X Y => by rfl)
                                                                            (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                            (fun X Y => by rfl)
                                                                            (fun hXTrans hXTy =>
                                                                              hRec
                                                                                (G := x1) (bvs' := bvs)
                                                                                (by simp; omega)
                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                            (fun hATrans hATy =>
                                                                              hRec
                                                                                (G := a) (bvs' := bvs)
                                                                                (by simp; omega)
                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                      · by_cases hHeadBvxnor :
                                                                          g = Term.UOp UserOp.bvxnor
                                                                        · subst g
                                                                          exact
                                                                            substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                              UserOp.bvxnor SmtTerm.bvxnor x1 a xs ts bvs
                                                                              hXsEnv hBvsEnv hTs
                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                              hFTrans hTy
                                                                              (fun X Y => by rfl)
                                                                              (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                              (fun X Y => by rfl)
                                                                              (fun hXTrans hXTy =>
                                                                                hRec
                                                                                  (G := x1) (bvs' := bvs)
                                                                                  (by simp; omega)
                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                              (fun hATrans hATy =>
                                                                                hRec
                                                                                  (G := a) (bvs' := bvs)
                                                                                  (by simp; omega)
                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                        · by_cases hHeadBvadd :
                                                                            g = Term.UOp UserOp.bvadd
                                                                          · subst g
                                                                            exact
                                                                              substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                UserOp.bvadd SmtTerm.bvadd x1 a xs ts bvs
                                                                                hXsEnv hBvsEnv hTs
                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                hFTrans hTy
                                                                                (fun X Y => by rfl)
                                                                                (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                (fun X Y => by rfl)
                                                                                (fun hXTrans hXTy =>
                                                                                  hRec
                                                                                    (G := x1) (bvs' := bvs)
                                                                                    (by simp; omega)
                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                (fun hATrans hATy =>
                                                                                  hRec
                                                                                    (G := a) (bvs' := bvs)
                                                                                    (by simp; omega)
                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                          · by_cases hHeadBvmul :
                                                                              g = Term.UOp UserOp.bvmul
                                                                            · subst g
                                                                              exact
                                                                                substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                  UserOp.bvmul SmtTerm.bvmul x1 a xs ts bvs
                                                                                  hXsEnv hBvsEnv hTs
                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                  hFTrans hTy
                                                                                  (fun X Y => by rfl)
                                                                                  (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                  (fun X Y => by rfl)
                                                                                  (fun hXTrans hXTy =>
                                                                                    hRec
                                                                                      (G := x1) (bvs' := bvs)
                                                                                      (by simp; omega)
                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                  (fun hATrans hATy =>
                                                                                    hRec
                                                                                      (G := a) (bvs' := bvs)
                                                                                      (by simp; omega)
                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                            · by_cases hHeadBvudiv :
                                                                                g = Term.UOp UserOp.bvudiv
                                                                              · subst g
                                                                                exact
                                                                                  substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                    UserOp.bvudiv SmtTerm.bvudiv x1 a xs ts bvs
                                                                                    hXsEnv hBvsEnv hTs
                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                    hFTrans hTy
                                                                                    (fun X Y => by rfl)
                                                                                    (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                    (fun X Y => by rfl)
                                                                                    (fun hXTrans hXTy =>
                                                                                      hRec
                                                                                        (G := x1) (bvs' := bvs)
                                                                                        (by simp; omega)
                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                    (fun hATrans hATy =>
                                                                                      hRec
                                                                                        (G := a) (bvs' := bvs)
                                                                                        (by simp; omega)
                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                              · by_cases hHeadBvurem :
                                                                                  g = Term.UOp UserOp.bvurem
                                                                                · subst g
                                                                                  exact
                                                                                    substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                      UserOp.bvurem SmtTerm.bvurem x1 a xs ts bvs
                                                                                      hXsEnv hBvsEnv hTs
                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                      hFTrans hTy
                                                                                      (fun X Y => by rfl)
                                                                                      (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                      (fun X Y => by rfl)
                                                                                      (fun hXTrans hXTy =>
                                                                                        hRec
                                                                                          (G := x1) (bvs' := bvs)
                                                                                          (by simp; omega)
                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                      (fun hATrans hATy =>
                                                                                        hRec
                                                                                          (G := a) (bvs' := bvs)
                                                                                          (by simp; omega)
                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                · by_cases hHeadBvsub :
                                                                                    g = Term.UOp UserOp.bvsub
                                                                                  · subst g
                                                                                    exact
                                                                                      substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                        UserOp.bvsub SmtTerm.bvsub x1 a xs ts bvs
                                                                                        hXsEnv hBvsEnv hTs
                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                        hFTrans hTy
                                                                                        (fun X Y => by rfl)
                                                                                        (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                        (fun X Y => by rfl)
                                                                                        (fun hXTrans hXTy =>
                                                                                          hRec
                                                                                            (G := x1) (bvs' := bvs)
                                                                                            (by simp; omega)
                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                        (fun hATrans hATy =>
                                                                                          hRec
                                                                                            (G := a) (bvs' := bvs)
                                                                                            (by simp; omega)
                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                  · by_cases hHeadBvsdiv :
                                                                                      g = Term.UOp UserOp.bvsdiv
                                                                                    · subst g
                                                                                      exact
                                                                                        substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                          UserOp.bvsdiv SmtTerm.bvsdiv x1 a xs ts bvs
                                                                                          hXsEnv hBvsEnv hTs
                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                          hFTrans hTy
                                                                                          (fun X Y => by rfl)
                                                                                          (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                          (fun X Y => by rfl)
                                                                                          (fun hXTrans hXTy =>
                                                                                            hRec
                                                                                              (G := x1) (bvs' := bvs)
                                                                                              (by simp; omega)
                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                          (fun hATrans hATy =>
                                                                                            hRec
                                                                                              (G := a) (bvs' := bvs)
                                                                                              (by simp; omega)
                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                    · by_cases hHeadBvsrem :
                                                                                        g = Term.UOp UserOp.bvsrem
                                                                                      · subst g
                                                                                        exact
                                                                                          substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                            UserOp.bvsrem SmtTerm.bvsrem x1 a xs ts bvs
                                                                                            hXsEnv hBvsEnv hTs
                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                            hFTrans hTy
                                                                                            (fun X Y => by rfl)
                                                                                            (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                            (fun X Y => by rfl)
                                                                                            (fun hXTrans hXTy =>
                                                                                              hRec
                                                                                                (G := x1) (bvs' := bvs)
                                                                                                (by simp; omega)
                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                            (fun hATrans hATy =>
                                                                                              hRec
                                                                                                (G := a) (bvs' := bvs)
                                                                                                (by simp; omega)
                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                      · by_cases hHeadBvsmod :
                                                                                          g = Term.UOp UserOp.bvsmod
                                                                                        · subst g
                                                                                          exact
                                                                                            substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                              UserOp.bvsmod SmtTerm.bvsmod x1 a xs ts bvs
                                                                                              hXsEnv hBvsEnv hTs
                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                              hFTrans hTy
                                                                                              (fun X Y => by rfl)
                                                                                              (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                              (fun X Y => by rfl)
                                                                                              (fun hXTrans hXTy =>
                                                                                                hRec
                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                  (by simp; omega)
                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                              (fun hATrans hATy =>
                                                                                                hRec
                                                                                                  (G := a) (bvs' := bvs)
                                                                                                  (by simp; omega)
                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                        · by_cases hHeadBvshl :
                                                                                            g = Term.UOp UserOp.bvshl
                                                                                          · subst g
                                                                                            exact
                                                                                              substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                UserOp.bvshl SmtTerm.bvshl x1 a xs ts bvs
                                                                                                hXsEnv hBvsEnv hTs
                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                hFTrans hTy
                                                                                                (fun X Y => by rfl)
                                                                                                (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                (fun X Y => by rfl)
                                                                                                (fun hXTrans hXTy =>
                                                                                                  hRec
                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                    (by simp; omega)
                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                (fun hATrans hATy =>
                                                                                                  hRec
                                                                                                    (G := a) (bvs' := bvs)
                                                                                                    (by simp; omega)
                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                          · by_cases hHeadBvlshr :
                                                                                              g = Term.UOp UserOp.bvlshr
                                                                                            · subst g
                                                                                              exact
                                                                                                substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                  UserOp.bvlshr SmtTerm.bvlshr x1 a xs ts bvs
                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                  hFTrans hTy
                                                                                                  (fun X Y => by rfl)
                                                                                                  (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                  (fun X Y => by rfl)
                                                                                                  (fun hXTrans hXTy =>
                                                                                                    hRec
                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                      (by simp; omega)
                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                  (fun hATrans hATy =>
                                                                                                    hRec
                                                                                                      (G := a) (bvs' := bvs)
                                                                                                      (by simp; omega)
                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                            · by_cases hHeadBvashr :
                                                                                                g = Term.UOp UserOp.bvashr
                                                                                              · subst g
                                                                                                exact
                                                                                                  substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                    UserOp.bvashr SmtTerm.bvashr x1 a xs ts bvs
                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hTy
                                                                                                    (fun X Y => by rfl)
                                                                                                    (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                    (fun X Y => by rfl)
                                                                                                    (fun hXTrans hXTy =>
                                                                                                      hRec
                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                        (by simp; omega)
                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                    (fun hATrans hATy =>
                                                                                                      hRec
                                                                                                        (G := a) (bvs' := bvs)
                                                                                                        (by simp; omega)
                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                              · by_cases hHeadBvcomp :
                                                                                                  g = Term.UOp UserOp.bvcomp
                                                                                                · subst g
                                                                                                  exact
                                                                                                    substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                      UserOp.bvcomp SmtTerm.bvcomp __eo_typeof_bvcomp
                                                                                                      (SmtType.BitVec 1) x1 a xs ts bvs
                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                      hFTrans hTy
                                                                                                      (fun X Y => by rfl)
                                                                                                      (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                      (fun X Y => by rfl)
                                                                                                      (fun h => eo_typeof_bvcomp_arg_types_of_ne_stuck h)
                                                                                                      (by simp)
                                                                                                      (fun hXTrans hXTy =>
                                                                                                        hRec
                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a) (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                · by_cases hHeadBvult :
                                                                                                    g = Term.UOp UserOp.bvult
                                                                                                  · subst g
                                                                                                    exact
                                                                                                      substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                        UserOp.bvult SmtTerm.bvult __eo_typeof_bvult
                                                                                                        SmtType.Bool x1 a xs ts bvs
                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                        hFTrans hTy
                                                                                                        (fun X Y => by rfl)
                                                                                                        (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                        (fun X Y => by rfl)
                                                                                                        (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                        (by simp)
                                                                                                        (fun hXTrans hXTy =>
                                                                                                          hRec
                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                            (by simp; omega)
                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                        (fun hATrans hATy =>
                                                                                                          hRec
                                                                                                            (G := a) (bvs' := bvs)
                                                                                                            (by simp; omega)
                                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                  · by_cases hHeadBvule :
                                                                                                      g = Term.UOp UserOp.bvule
                                                                                                    · subst g
                                                                                                      exact
                                                                                                        substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                          UserOp.bvule SmtTerm.bvule __eo_typeof_bvult
                                                                                                          SmtType.Bool x1 a xs ts bvs
                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                          hFTrans hTy
                                                                                                          (fun X Y => by rfl)
                                                                                                          (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                          (fun X Y => by rfl)
                                                                                                          (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                          (by simp)
                                                                                                          (fun hXTrans hXTy =>
                                                                                                            hRec
                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                              (by simp; omega)
                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                          (fun hATrans hATy =>
                                                                                                            hRec
                                                                                                              (G := a) (bvs' := bvs)
                                                                                                              (by simp; omega)
                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                    · by_cases hHeadBvugt :
                                                                                                        g = Term.UOp UserOp.bvugt
                                                                                                      · subst g
                                                                                                        exact
                                                                                                          substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                            UserOp.bvugt SmtTerm.bvugt __eo_typeof_bvult
                                                                                                            SmtType.Bool x1 a xs ts bvs
                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                            hFTrans hTy
                                                                                                            (fun X Y => by rfl)
                                                                                                            (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                            (fun X Y => by rfl)
                                                                                                            (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                            (by simp)
                                                                                                            (fun hXTrans hXTy =>
                                                                                                              hRec
                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                (by simp; omega)
                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                            (fun hATrans hATy =>
                                                                                                              hRec
                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                (by simp; omega)
                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                      · by_cases hHeadBvuge :
                                                                                                          g = Term.UOp UserOp.bvuge
                                                                                                        · subst g
                                                                                                          exact
                                                                                                            substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                              UserOp.bvuge SmtTerm.bvuge __eo_typeof_bvult
                                                                                                              SmtType.Bool x1 a xs ts bvs
                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                              hFTrans hTy
                                                                                                              (fun X Y => by rfl)
                                                                                                              (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                              (fun X Y => by rfl)
                                                                                                              (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                              (by simp)
                                                                                                              (fun hXTrans hXTy =>
                                                                                                                hRec
                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                  (by simp; omega)
                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                              (fun hATrans hATy =>
                                                                                                                hRec
                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                  (by simp; omega)
                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                        · by_cases hHeadBvslt :
                                                                                                            g = Term.UOp UserOp.bvslt
                                                                                                          · subst g
                                                                                                            exact
                                                                                                              substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                UserOp.bvslt SmtTerm.bvslt __eo_typeof_bvult
                                                                                                                SmtType.Bool x1 a xs ts bvs
                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                hFTrans hTy
                                                                                                                (fun X Y => by rfl)
                                                                                                                (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                (fun X Y => by rfl)
                                                                                                                (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                (by simp)
                                                                                                                (fun hXTrans hXTy =>
                                                                                                                  hRec
                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                    (by simp; omega)
                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                (fun hATrans hATy =>
                                                                                                                  hRec
                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                    (by simp; omega)
                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                          · by_cases hHeadBvsle :
                                                                                                              g = Term.UOp UserOp.bvsle
                                                                                                            · subst g
                                                                                                              exact
                                                                                                                substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                  UserOp.bvsle SmtTerm.bvsle __eo_typeof_bvult
                                                                                                                  SmtType.Bool x1 a xs ts bvs
                                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                  hFTrans hTy
                                                                                                                  (fun X Y => by rfl)
                                                                                                                  (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                  (fun X Y => by rfl)
                                                                                                                  (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                  (by simp)
                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                    hRec
                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                      (by simp; omega)
                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                  (fun hATrans hATy =>
                                                                                                                    hRec
                                                                                                                      (G := a) (bvs' := bvs)
                                                                                                                      (by simp; omega)
                                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                            · by_cases hHeadBvsgt :
                                                                                                                g = Term.UOp UserOp.bvsgt
                                                                                                              · subst g
                                                                                                                exact
                                                                                                                  substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                    UserOp.bvsgt SmtTerm.bvsgt __eo_typeof_bvult
                                                                                                                    SmtType.Bool x1 a xs ts bvs
                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                    hFTrans hTy
                                                                                                                    (fun X Y => by rfl)
                                                                                                                    (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                    (fun X Y => by rfl)
                                                                                                                    (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                    (by simp)
                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                      hRec
                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                        (by simp; omega)
                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                    (fun hATrans hATy =>
                                                                                                                      hRec
                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                        (by simp; omega)
                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                              · by_cases hHeadBvsge :
                                                                                                                  g = Term.UOp UserOp.bvsge
                                                                                                                · subst g
                                                                                                                  exact
                                                                                                                    substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                      UserOp.bvsge SmtTerm.bvsge __eo_typeof_bvult
                                                                                                                      SmtType.Bool x1 a xs ts bvs
                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                      hFTrans hTy
                                                                                                                      (fun X Y => by rfl)
                                                                                                                      (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                      (fun X Y => by rfl)
                                                                                                                      (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                      (by simp)
                                                                                                                      (fun hXTrans hXTy =>
                                                                                                                        hRec
                                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                                          (by simp; omega)
                                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                      (fun hATrans hATy =>
                                                                                                                        hRec
                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                          (by simp; omega)
                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                · by_cases hHeadBvuaddo :
                                                                                                                    g = Term.UOp UserOp.bvuaddo
                                                                                                                  · subst g
                                                                                                                    exact
                                                                                                                      substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                        UserOp.bvuaddo SmtTerm.bvuaddo __eo_typeof_bvult
                                                                                                                        SmtType.Bool x1 a xs ts bvs
                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                        hFTrans hTy
                                                                                                                        (fun X Y => by rfl)
                                                                                                                        (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                        (fun X Y => by rfl)
                                                                                                                        (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                        (by simp)
                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                          hRec
                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                            (by simp; omega)
                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                        (fun hATrans hATy =>
                                                                                                                          hRec
                                                                                                                            (G := a) (bvs' := bvs)
                                                                                                                            (by simp; omega)
                                                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                  · by_cases hHeadBvsaddo :
                                                                                                                      g = Term.UOp UserOp.bvsaddo
                                                                                                                    · subst g
                                                                                                                      exact
                                                                                                                        substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                          UserOp.bvsaddo SmtTerm.bvsaddo __eo_typeof_bvult
                                                                                                                          SmtType.Bool x1 a xs ts bvs
                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                          hFTrans hTy
                                                                                                                          (fun X Y => by rfl)
                                                                                                                          (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                          (fun X Y => by rfl)
                                                                                                                          (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                          (by simp)
                                                                                                                          (fun hXTrans hXTy =>
                                                                                                                            hRec
                                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                                              (by simp; omega)
                                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                          (fun hATrans hATy =>
                                                                                                                            hRec
                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                              (by simp; omega)
                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                    · by_cases hHeadBvumulo :
                                                                                                                        g = Term.UOp UserOp.bvumulo
                                                                                                                      · subst g
                                                                                                                        exact
                                                                                                                          substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                            UserOp.bvumulo SmtTerm.bvumulo __eo_typeof_bvult
                                                                                                                            SmtType.Bool x1 a xs ts bvs
                                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                            hFTrans hTy
                                                                                                                            (fun X Y => by rfl)
                                                                                                                            (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                            (fun X Y => by rfl)
                                                                                                                            (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                            (by simp)
                                                                                                                            (fun hXTrans hXTy =>
                                                                                                                              hRec
                                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                                (by simp; omega)
                                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                            (fun hATrans hATy =>
                                                                                                                              hRec
                                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                                (by simp; omega)
                                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                      · by_cases hHeadBvsmulo :
                                                                                                                          g = Term.UOp UserOp.bvsmulo
                                                                                                                        · subst g
                                                                                                                          exact
                                                                                                                            substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                              UserOp.bvsmulo SmtTerm.bvsmulo __eo_typeof_bvult
                                                                                                                              SmtType.Bool x1 a xs ts bvs
                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                              hFTrans hTy
                                                                                                                              (fun X Y => by rfl)
                                                                                                                              (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                              (fun X Y => by rfl)
                                                                                                                              (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                              (by simp)
                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                hRec
                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                  (by simp; omega)
                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                              (fun hATrans hATy =>
                                                                                                                                hRec
                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                  (by simp; omega)
                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                        · by_cases hHeadBvusubo :
                                                                                                                            g = Term.UOp UserOp.bvusubo
                                                                                                                          · subst g
                                                                                                                            exact
                                                                                                                              substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                UserOp.bvusubo SmtTerm.bvusubo __eo_typeof_bvult
                                                                                                                                SmtType.Bool x1 a xs ts bvs
                                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                hFTrans hTy
                                                                                                                                (fun X Y => by rfl)
                                                                                                                                (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                                (fun X Y => by rfl)
                                                                                                                                (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                                (by simp)
                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                  hRec
                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                    (by simp; omega)
                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                (fun hATrans hATy =>
                                                                                                                                  hRec
                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                    (by simp; omega)
                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                          · by_cases hHeadBvssubo :
                                                                                                                              g = Term.UOp UserOp.bvssubo
                                                                                                                            · subst g
                                                                                                                              exact
                                                                                                                                substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                  UserOp.bvssubo SmtTerm.bvssubo __eo_typeof_bvult
                                                                                                                                  SmtType.Bool x1 a xs ts bvs
                                                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                  hFTrans hTy
                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                  (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                  (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                                  (by simp)
                                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                                    hRec
                                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                                      (by simp; omega)
                                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                    hRec
                                                                                                                                      (G := a) (bvs' := bvs)
                                                                                                                                      (by simp; omega)
                                                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                            · by_cases hHeadBvsdivo :
                                                                                                                                g = Term.UOp UserOp.bvsdivo
                                                                                                                              · subst g
                                                                                                                                exact
                                                                                                                                  substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                    UserOp.bvsdivo SmtTerm.bvsdivo __eo_typeof_bvult
                                                                                                                                    SmtType.Bool x1 a xs ts bvs
                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                    hFTrans hTy
                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                    (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                    (fun h => eo_typeof_bvult_arg_types_of_ne_stuck h)
                                                                                                                                    (by simp)
                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                      hRec
                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                        (by simp; omega)
                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                      hRec
                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                        (by simp; omega)
                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                              · by_cases hHeadBvultbv :
                                                                                                                                  g = Term.UOp UserOp.bvultbv
                                                                                                                                · subst g
                                                                                                                                  exact
                                                                                                                                    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                      UserOp.bvultbv x1 a xs ts bvs
                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                      hFTrans hTy
                                                                                                                                      (fun h =>
                                                                                                                                        bvultbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                      (fun X Y hApp => by
                                                                                                                                        change
                                                                                                                                          __eo_typeof_bvcomp (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                            Term.Stuck at hApp
                                                                                                                                        rcases eo_typeof_bvcomp_arg_types_of_ne_stuck hApp with
                                                                                                                                          ⟨w, hXTy, hYTy⟩
                                                                                                                                        constructor
                                                                                                                                        · intro hStuck
                                                                                                                                          rw [hXTy] at hStuck
                                                                                                                                          cases hStuck
                                                                                                                                        · intro hStuck
                                                                                                                                          rw [hYTy] at hStuck
                                                                                                                                          cases hStuck)
                                                                                                                                      (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                        change
                                                                                                                                          __eo_typeof_bvcomp (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                            __eo_typeof_bvcomp (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                        rw [hX, hY])
                                                                                                                                      (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                                                                                        change
                                                                                                                                          __smtx_typeof
                                                                                                                                            (SmtTerm.ite
                                                                                                                                              (SmtTerm.bvult (__eo_to_smt X) (__eo_to_smt Y))
                                                                                                                                              (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
                                                                                                                                            SmtType.None
                                                                                                                                        change
                                                                                                                                          __eo_typeof_bvcomp (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                            Term.Stuck at hApp
                                                                                                                                        exact
                                                                                                                                          smt_bv_cmp_to_bv1_non_none_of_eo_typeof_bvcomp_ne_stuck
                                                                                                                                            SmtTerm.bvult
                                                                                                                                            (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                                            X Y hXTrans hYTrans hApp)
                                                                                                                                      (fun hXTrans hXTy =>
                                                                                                                                        hRec
                                                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                                                          (by simp; omega)
                                                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                        hRec
                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                          (by simp; omega)
                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                · by_cases hHeadBvsltbv :
                                                                                                                                    g = Term.UOp UserOp.bvsltbv
                                                                                                                                  · subst g
                                                                                                                                    exact
                                                                                                                                      substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                        UserOp.bvsltbv x1 a xs ts bvs
                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                        hFTrans hTy
                                                                                                                                        (fun h =>
                                                                                                                                          bvsltbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                        (fun X Y hApp => by
                                                                                                                                          change
                                                                                                                                            __eo_typeof_bvcomp (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                              Term.Stuck at hApp
                                                                                                                                          rcases eo_typeof_bvcomp_arg_types_of_ne_stuck hApp with
                                                                                                                                            ⟨w, hXTy, hYTy⟩
                                                                                                                                          constructor
                                                                                                                                          · intro hStuck
                                                                                                                                            rw [hXTy] at hStuck
                                                                                                                                            cases hStuck
                                                                                                                                          · intro hStuck
                                                                                                                                            rw [hYTy] at hStuck
                                                                                                                                            cases hStuck)
                                                                                                                                        (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                          change
                                                                                                                                            __eo_typeof_bvcomp (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                              __eo_typeof_bvcomp (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                          rw [hX, hY])
                                                                                                                                        (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                                                                                          change
                                                                                                                                            __smtx_typeof
                                                                                                                                              (SmtTerm.ite
                                                                                                                                                (SmtTerm.bvslt (__eo_to_smt X) (__eo_to_smt Y))
                                                                                                                                                (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
                                                                                                                                              SmtType.None
                                                                                                                                          change
                                                                                                                                            __eo_typeof_bvcomp (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                              Term.Stuck at hApp
                                                                                                                                          exact
                                                                                                                                            smt_bv_cmp_to_bv1_non_none_of_eo_typeof_bvcomp_ne_stuck
                                                                                                                                              SmtTerm.bvslt
                                                                                                                                              (fun X Y => by rw [__smtx_typeof.eq_def])
                                                                                                                                              X Y hXTrans hYTrans hApp)
                                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                                          hRec
                                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                                            (by simp; omega)
                                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                        (fun hATrans hATy =>
                                                                                                                                          hRec
                                                                                                                                            (G := a) (bvs' := bvs)
                                                                                                                                            (by simp; omega)
                                                                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                  · by_cases hHeadSelect :
                                                                                                                                      g = Term.UOp UserOp.select
                                                                                                                                    · subst g
                                                                                                                                      exact
                                                                                                                                        substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                          UserOp.select x1 a xs ts bvs
                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                          hFTrans hTy
                                                                                                                                          (fun h =>
                                                                                                                                            select_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                          (fun X Y hApp => by
                                                                                                                                            change
                                                                                                                                              __eo_typeof_select (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                Term.Stuck at hApp
                                                                                                                                            exact
                                                                                                                                              eo_typeof_select_args_not_stuck_of_ne_stuck hApp)
                                                                                                                                          (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                            change
                                                                                                                                              __eo_typeof_select (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                                __eo_typeof_select (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                            rw [hX, hY])
                                                                                                                                          (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                            unfold RuleProofs.eo_has_smt_translation
                                                                                                                                            change
                                                                                                                                              __smtx_typeof
                                                                                                                                                (SmtTerm.select (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                                                                                                SmtType.None
                                                                                                                                            change
                                                                                                                                              __eo_typeof_select (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                Term.Stuck at hApp
                                                                                                                                            exact
                                                                                                                                              smt_select_non_none_of_eo_typeof_select_ne_stuck
                                                                                                                                                X Y hXTrans hYTrans hApp)
                                                                                                                                          (fun hXTrans hXTy =>
                                                                                                                                            hRec
                                                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                                                              (by simp; omega)
                                                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                            hRec
                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                              (by simp; omega)
                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                    · by_cases hHeadStrConcat :
                                                                                                                                        g = Term.UOp UserOp.str_concat
                                                                                                                                      · subst g
                                                                                                                                        exact
                                                                                                                                          substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                            UserOp.str_concat x1 a xs ts bvs
                                                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                            hFTrans hTy
                                                                                                                                            (fun h =>
                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                (eoOp := UserOp.str_concat) (smtOp := SmtTerm.str_concat)
                                                                                                                                                (by rfl)
                                                                                                                                                (fun hNN =>
                                                                                                                                                  seq_binop_args_have_smt_translation_of_non_none
                                                                                                                                                    (typeof_str_concat_eq (__eo_to_smt x1) (__eo_to_smt a))
                                                                                                                                                    hNN)
                                                                                                                                                h)
                                                                                                                                            (fun X Y hApp => by
                                                                                                                                              change
                                                                                                                                                __eo_typeof_str_concat (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                  Term.Stuck at hApp
                                                                                                                                              exact
                                                                                                                                                eo_typeof_str_concat_args_not_stuck_of_ne_stuck hApp)
                                                                                                                                            (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                              change
                                                                                                                                                __eo_typeof_str_concat (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                                  __eo_typeof_str_concat (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                              rw [hX, hY])
                                                                                                                                            (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                              unfold RuleProofs.eo_has_smt_translation
                                                                                                                                              change
                                                                                                                                                __smtx_typeof
                                                                                                                                                  (SmtTerm.str_concat (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                                                                                                  SmtType.None
                                                                                                                                              change
                                                                                                                                                __eo_typeof_str_concat (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                  Term.Stuck at hApp
                                                                                                                                              exact
                                                                                                                                                smt_str_concat_non_none_of_eo_typeof_str_concat_ne_stuck
                                                                                                                                                  X Y hXTrans hYTrans hApp)
                                                                                                                                            (fun hXTrans hXTy =>
                                                                                                                                              hRec
                                                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                                                (by simp; omega)
                                                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                            (fun hATrans hATy =>
                                                                                                                                              hRec
                                                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                                                (by simp; omega)
                                                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                      · by_cases hHeadStrContains :
                                                                                                                                          g = Term.UOp UserOp.str_contains
                                                                                                                                        · subst g
                                                                                                                                          exact
                                                                                                                                            substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
                                                                                                                                              UserOp.str_contains x1 a xs ts bvs
                                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                              hFTrans hTy
                                                                                                                                              (fun h =>
                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                  (eoOp := UserOp.str_contains) (smtOp := SmtTerm.str_contains)
                                                                                                                                                  (by rfl)
                                                                                                                                                  (fun hNN =>
                                                                                                                                                    seq_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                      (ret := SmtType.Bool)
                                                                                                                                                      (typeof_str_contains_eq (__eo_to_smt x1) (__eo_to_smt a))
                                                                                                                                                      hNN)
                                                                                                                                                  h)
                                                                                                                                              (fun X Y hApp => by
                                                                                                                                                change
                                                                                                                                                  __eo_typeof_str_contains (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                    Term.Stuck at hApp
                                                                                                                                                exact
                                                                                                                                                  eo_typeof_str_contains_args_not_stuck_of_ne_stuck hApp)
                                                                                                                                              (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                                change
                                                                                                                                                  __eo_typeof_str_contains (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                                    __eo_typeof_str_contains (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                                rw [hX, hY])
                                                                                                                                              (fun X Y hXTrans hYTrans _ _ hApp => by
                                                                                                                                                unfold RuleProofs.eo_has_smt_translation
                                                                                                                                                change
                                                                                                                                                  __smtx_typeof
                                                                                                                                                    (SmtTerm.str_contains (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                                                                                                    SmtType.None
                                                                                                                                                change
                                                                                                                                                  __eo_typeof_str_contains (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                    Term.Stuck at hApp
                                                                                                                                                exact
                                                                                                                                                  smt_str_contains_non_none_of_eo_typeof_str_contains_ne_stuck
                                                                                                                                                    X Y hXTrans hYTrans hApp)
                                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                                hRec
                                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                                  (by simp; omega)
                                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                              (fun hATrans hATy =>
                                                                                                                                                hRec
                                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                                  (by simp; omega)
                                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                        · by_cases hHeadStrPrefixof :
                                                                                                                                            g = Term.UOp UserOp.str_prefixof
                                                                                                                                          · subst g
                                                                                                                                            exact
                                                                                                                                              substitute_simul_str_prefixof_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                hFTrans hTy
                                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                                  hRec
                                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                                    (by simp; omega)
                                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                (fun hATrans hATy =>
                                                                                                                                                  hRec
                                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                                    (by simp; omega)
                                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                          · by_cases hHeadStrSuffixof :
                                                                                                                                              g = Term.UOp UserOp.str_suffixof
                                                                                                                                            · subst g
                                                                                                                                              exact
                                                                                                                                                substitute_simul_str_suffixof_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                  x1 a xs ts bvs hXsEnv hBvsEnv hTs
                                                                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                  hFTrans hTy
                                                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                                                    hRec
                                                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                                                      (by simp; omega)
                                                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                                    hRec
                                                                                                                                                      (G := a) (bvs' := bvs)
                                                                                                                                                      (by simp; omega)
                                                                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                            · by_cases hHeadStrAt :
                                                                                                                                                g = Term.UOp UserOp.str_at
                                                                                                                                              · subst g
                                                                                                                                                exact
                                                                                                                                                  substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                    UserOp.str_at x1 a xs ts bvs
                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                    hFTrans hTy
                                                                                                                                                    (fun h =>
                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                        (eoOp := UserOp.str_at) (smtOp := SmtTerm.str_at)
                                                                                                                                                        (by rfl)
                                                                                                                                                        (fun hNN =>
                                                                                                                                                          str_at_args_have_smt_translation_of_non_none hNN)
                                                                                                                                                        h)
                                                                                                                                                    (fun X Y hApp => by
                                                                                                                                                      change
                                                                                                                                                        __eo_typeof_str_at (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                          Term.Stuck at hApp
                                                                                                                                                      exact
                                                                                                                                                        eo_typeof_str_at_args_not_stuck_of_ne_stuck hApp)
                                                                                                                                                    (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                                      change
                                                                                                                                                        __eo_typeof_str_at (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                                          __eo_typeof_str_at (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                                      rw [hX, hY])
                                                                                                                                                    (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                                                                                                      change
                                                                                                                                                        __smtx_typeof
                                                                                                                                                          (SmtTerm.str_at (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                                                                                                          SmtType.None
                                                                                                                                                      change
                                                                                                                                                        __eo_typeof_str_at (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                          Term.Stuck at hApp
                                                                                                                                                      exact
                                                                                                                                                        smt_str_at_non_none_of_eo_typeof_str_at_ne_stuck
                                                                                                                                                          X Y hXTrans hYTrans hApp)
                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                      hRec
                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                        (by simp; omega)
                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                      hRec
                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                        (by simp; omega)
                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                              · by_cases hHeadStrLt :
                                                                                                                                                  g = Term.UOp UserOp.str_lt
                                                                                                                                                · subst g
                                                                                                                                                  exact
                                                                                                                                                    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                      UserOp.str_lt x1 a xs ts bvs
                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                      hFTrans hTy
                                                                                                                                                      (fun h =>
                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                          (eoOp := UserOp.str_lt) (smtOp := SmtTerm.str_lt)
                                                                                                                                                          (by rfl)
                                                                                                                                                          (fun hNN =>
                                                                                                                                                            seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                              (ret := SmtType.Bool)
                                                                                                                                                              (typeof_str_lt_eq (__eo_to_smt x1) (__eo_to_smt a))
                                                                                                                                                              hNN)
                                                                                                                                                          h)
                                                                                                                                                      (fun X Y hApp => by
                                                                                                                                                        change
                                                                                                                                                          __eo_typeof_str_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                            Term.Stuck at hApp
                                                                                                                                                        exact
                                                                                                                                                          eo_typeof_str_lt_args_not_stuck_of_ne_stuck hApp)
                                                                                                                                                      (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                                        change
                                                                                                                                                          __eo_typeof_str_lt (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                                            __eo_typeof_str_lt (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                                        rw [hX, hY])
                                                                                                                                                      (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                                                                                                        change
                                                                                                                                                          __smtx_typeof
                                                                                                                                                            (SmtTerm.str_lt (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                                                                                                            SmtType.None
                                                                                                                                                        change
                                                                                                                                                          __eo_typeof_str_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                            Term.Stuck at hApp
                                                                                                                                                        exact
                                                                                                                                                          smt_seq_char_bool_binop_non_none_of_eo_typeof_str_lt_ne_stuck
                                                                                                                                                            SmtTerm.str_lt
                                                                                                                                                            (fun X Y => typeof_str_lt_eq X Y)
                                                                                                                                                            X Y hXTrans hYTrans hApp)
                                                                                                                                                      (fun hXTrans hXTy =>
                                                                                                                                                        hRec
                                                                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                                                                          (by simp; omega)
                                                                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                        hRec
                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                          (by simp; omega)
                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                · by_cases hHeadStrLeq :
                                                                                                                                                    g = Term.UOp UserOp.str_leq
                                                                                                                                                  · subst g
                                                                                                                                                    exact
                                                                                                                                                      substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                        UserOp.str_leq x1 a xs ts bvs
                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                        hFTrans hTy
                                                                                                                                                        (fun h =>
                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                            (eoOp := UserOp.str_leq) (smtOp := SmtTerm.str_leq)
                                                                                                                                                            (by rfl)
                                                                                                                                                            (fun hNN =>
                                                                                                                                                              seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                (ret := SmtType.Bool)
                                                                                                                                                                (typeof_str_leq_eq (__eo_to_smt x1) (__eo_to_smt a))
                                                                                                                                                                hNN)
                                                                                                                                                            h)
                                                                                                                                                        (fun X Y hApp => by
                                                                                                                                                          change
                                                                                                                                                            __eo_typeof_str_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                              Term.Stuck at hApp
                                                                                                                                                          exact
                                                                                                                                                            eo_typeof_str_lt_args_not_stuck_of_ne_stuck hApp)
                                                                                                                                                        (fun X₁ Y₁ X₂ Y₂ hX hY => by
                                                                                                                                                          change
                                                                                                                                                            __eo_typeof_str_lt (__eo_typeof X₁) (__eo_typeof X₂) =
                                                                                                                                                              __eo_typeof_str_lt (__eo_typeof Y₁) (__eo_typeof Y₂)
                                                                                                                                                          rw [hX, hY])
                                                                                                                                                        (fun X Y hXTrans hYTrans hApp => by
                                                                                                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                                                                                                          change
                                                                                                                                                            __smtx_typeof
                                                                                                                                                              (SmtTerm.str_leq (__eo_to_smt X) (__eo_to_smt Y)) ≠
                                                                                                                                                              SmtType.None
                                                                                                                                                          change
                                                                                                                                                            __eo_typeof_str_lt (__eo_typeof X) (__eo_typeof Y) ≠
                                                                                                                                                              Term.Stuck at hApp
                                                                                                                                                          exact
                                                                                                                                                            smt_seq_char_bool_binop_non_none_of_eo_typeof_str_lt_ne_stuck
                                                                                                                                                              SmtTerm.str_leq
                                                                                                                                                              (fun X Y => typeof_str_leq_eq X Y)
                                                                                                                                                              X Y hXTrans hYTrans hApp)
                                                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                                                          hRec
                                                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                                                            (by simp; omega)
                                                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                        (fun hATrans hATy =>
                                                                                                                                                          hRec
                                                                                                                                                            (G := a) (bvs' := bvs)
                                                                                                                                                            (by simp; omega)
                                                                                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                  · by_cases hHeadReRange :
                                                                                                                                                      g = Term.UOp UserOp.re_range
                                                                                                                                                    · subst g
                                                                                                                                                      exact
                                                                                                                                                        substitute_simul_re_range_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                          x1 a xs ts bvs
                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                          hFTrans hTy
                                                                                                                                                          (fun hXTrans hXTy =>
                                                                                                                                                            hRec
                                                                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                                                                              (by simp; omega)
                                                                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                            hRec
                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                              (by simp; omega)
                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                    · by_cases hHeadReConcat :
                                                                                                                                                        g = Term.UOp UserOp.re_concat
                                                                                                                                                      · subst g
                                                                                                                                                        exact
                                                                                                                                                          substitute_simul_reglan_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                            UserOp.re_concat SmtTerm.re_concat x1 a xs ts bvs
                                                                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                            hFTrans hTy
                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                            (fun X Y => typeof_re_concat_eq X Y)
                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                            (fun hXTrans hXTy =>
                                                                                                                                                              hRec
                                                                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                                                                (by simp; omega)
                                                                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                            (fun hATrans hATy =>
                                                                                                                                                              hRec
                                                                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                                                                (by simp; omega)
                                                                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                      · by_cases hHeadReInter :
                                                                                                                                                          g = Term.UOp UserOp.re_inter
                                                                                                                                                        · subst g
                                                                                                                                                          exact
                                                                                                                                                            substitute_simul_reglan_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                              UserOp.re_inter SmtTerm.re_inter x1 a xs ts bvs
                                                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                              hFTrans hTy
                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                              (fun X Y => typeof_re_inter_eq X Y)
                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                                                hRec
                                                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                              (fun hATrans hATy =>
                                                                                                                                                                hRec
                                                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                        · by_cases hHeadReUnion :
                                                                                                                                                            g = Term.UOp UserOp.re_union
                                                                                                                                                          · subst g
                                                                                                                                                            exact
                                                                                                                                                              substitute_simul_reglan_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                UserOp.re_union SmtTerm.re_union x1 a xs ts bvs
                                                                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                hFTrans hTy
                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                (fun X Y => typeof_re_union_eq X Y)
                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                                                  hRec
                                                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                (fun hATrans hATy =>
                                                                                                                                                                  hRec
                                                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                          · by_cases hHeadReDiff :
                                                                                                                                                              g = Term.UOp UserOp.re_diff
                                                                                                                                                            · subst g
                                                                                                                                                              exact
                                                                                                                                                                substitute_simul_reglan_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                  UserOp.re_diff SmtTerm.re_diff x1 a xs ts bvs
                                                                                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                  hFTrans hTy
                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                  (fun X Y => typeof_re_diff_eq X Y)
                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                                                                    hRec
                                                                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                                                    hRec
                                                                                                                                                                      (G := a) (bvs' := bvs)
                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                            · by_cases hHeadStrInRe :
                                                                                                                                                                g = Term.UOp UserOp.str_in_re
                                                                                                                                                              · subst g
                                                                                                                                                                exact
                                                                                                                                                                  substitute_simul_str_in_re_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                    x1 a xs ts bvs
                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                      hRec
                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                      hRec
                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                              · by_cases hHeadSeqNth :
                                                                                                                                                                  g = Term.UOp UserOp.seq_nth
                                                                                                                                                                · subst g
                                                                                                                                                                  exact
                                                                                                                                                                    substitute_simul_seq_nth_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                      x1 a xs ts bvs
                                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                      hFTrans hTy
                                                                                                                                                                      (fun hXTrans hXTy =>
                                                                                                                                                                        hRec
                                                                                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                                        hRec
                                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                · by_cases hHeadSetUnion :
                                                                                                                                                                    g = Term.UOp UserOp.set_union
                                                                                                                                                                  · subst g
                                                                                                                                                                    exact
                                                                                                                                                                      substitute_simul_set_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                        UserOp.set_union SmtTerm.set_union x1 a xs ts bvs
                                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                        hFTrans hTy
                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                        (fun X Y => typeof_set_union_eq X Y)
                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                                                                          hRec
                                                                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                        (fun hATrans hATy =>
                                                                                                                                                                          hRec
                                                                                                                                                                            (G := a) (bvs' := bvs)
                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                  · by_cases hHeadSetInter :
                                                                                                                                                                      g = Term.UOp UserOp.set_inter
                                                                                                                                                                    · subst g
                                                                                                                                                                      exact
                                                                                                                                                                        substitute_simul_set_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                          UserOp.set_inter SmtTerm.set_inter x1 a xs ts bvs
                                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                          hFTrans hTy
                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                          (fun X Y => typeof_set_inter_eq X Y)
                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                          (fun hXTrans hXTy =>
                                                                                                                                                                            hRec
                                                                                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                                            hRec
                                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                    · by_cases hHeadSetMinus :
                                                                                                                                                                        g = Term.UOp UserOp.set_minus
                                                                                                                                                                      · subst g
                                                                                                                                                                        exact
                                                                                                                                                                          substitute_simul_set_binop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                            UserOp.set_minus SmtTerm.set_minus x1 a xs ts bvs
                                                                                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                            hFTrans hTy
                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                            (fun X Y => typeof_set_minus_eq X Y)
                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                            (fun hXTrans hXTy =>
                                                                                                                                                                              hRec
                                                                                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                            (fun hATrans hATy =>
                                                                                                                                                                              hRec
                                                                                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                      · by_cases hHeadSetMember :
                                                                                                                                                                          g = Term.UOp UserOp.set_member
                                                                                                                                                                        · subst g
                                                                                                                                                                          exact
                                                                                                                                                                            substitute_simul_set_member_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                              x1 a xs ts bvs
                                                                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                              hFTrans hTy
                                                                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                                                                hRec
                                                                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                              (fun hATrans hATy =>
                                                                                                                                                                                hRec
                                                                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                        · by_cases hHeadSetSubset :
                                                                                                                                                                            g = Term.UOp UserOp.set_subset
                                                                                                                                                                          · subst g
                                                                                                                                                                            exact
                                                                                                                                                                              substitute_simul_set_subset_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                x1 a xs ts bvs
                                                                                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                hFTrans hTy
                                                                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                                                                  hRec
                                                                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                (fun hATrans hATy =>
                                                                                                                                                                                  hRec
                                                                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                          · by_cases hHeadSetsDeqDiff :
                                                                                                                                                                              g =
                                                                                                                                                                                Term.UOp UserOp._at_sets_deq_diff
                                                                                                                                                                            · subst g
                                                                                                                                                                              exact
                                                                                                                                                                                substitute_simul_sets_deq_diff_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                  x1 a xs ts bvs
                                                                                                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                  hFTrans hTy
                                                                                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                                                                                    hRec
                                                                                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                                                                      hRec
                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                            · by_cases hHeadStringsDeqDiff :
                                                                                                                                                                                g =
                                                                                                                                                                                  Term.UOp UserOp._at_strings_deq_diff
                                                                                                                                                                              · subst g
                                                                                                                                                                                exact
                                                                                                                                                                                  substitute_simul_strings_deq_diff_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                    x1 a xs ts bvs
                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                      hRec
                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                      hRec
                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                              · by_cases hHeadStringsStoiResult :
                                                                                                                                                                                  g =
                                                                                                                                                                                    Term.UOp UserOp._at_strings_stoi_result
                                                                                                                                                                                · subst g
                                                                                                                                                                                  exact
                                                                                                                                                                                    substitute_simul_strings_stoi_result_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                      x1 a xs ts bvs
                                                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                      hFTrans hTy
                                                                                                                                                                                      (fun hXTrans hXTy =>
                                                                                                                                                                                        hRec
                                                                                                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                                                        hRec
                                                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                · by_cases hHeadStringsItosResult :
                                                                                                                                                                                    g =
                                                                                                                                                                                      Term.UOp UserOp._at_strings_itos_result
                                                                                                                                                                                  · subst g
                                                                                                                                                                                    exact
                                                                                                                                                                                      substitute_simul_strings_itos_result_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                        x1 a xs ts bvs
                                                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                        hFTrans hTy
                                                                                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                                                                                          hRec
                                                                                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                        (fun hATrans hATy =>
                                                                                                                                                                                          hRec
                                                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                  · by_cases hHeadArrayDeqDiff :
                                                                                                                                                                                      g =
                                                                                                                                                                                        Term.UOp UserOp._at_array_deq_diff
                                                                                                                                                                                    · subst g
                                                                                                                                                                                      exact
                                                                                                                                                                                        substitute_simul_array_deq_diff_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                          x1 a xs ts bvs
                                                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                          hFTrans hTy
                                                                                                                                                                                          (fun hXTrans hXTy =>
                                                                                                                                                                                            hRec
                                                                                                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                                                            hRec
                                                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                    · by_cases hHeadFromBools :
                                                                                                                                                                                        g =
                                                                                                                                                                                          Term.UOp UserOp._at_from_bools
                                                                                                                                                                                      · subst g
                                                                                                                                                                                        exact
                                                                                                                                                                                          substitute_simul_from_bools_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                            x1 a xs ts bvs
                                                                                                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                            hFTrans hTy
                                                                                                                                                                                            (fun hXTrans hXTy =>
                                                                                                                                                                                              hRec
                                                                                                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                            (fun hATrans hATy =>
                                                                                                                                                                                              hRec
                                                                                                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                      · by_cases hHeadStringsNumOccur :
                                                                                                                                                                                          g =
                                                                                                                                                                                            Term.UOp UserOp._at_strings_num_occur
                                                                                                                                                                                        · subst g
                                                                                                                                                                                          exact
                                                                                                                                                                                            substitute_simul_strings_num_occur_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                              x1 a xs ts bvs
                                                                                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                              hFTrans hTy
                                                                                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                                                                                hRec
                                                                                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                              (fun hATrans hATy =>
                                                                                                                                                                                                hRec
                                                                                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                        · by_cases hHeadIte :
                                                                                                                                                                                            ∃ c,
                                                                                                                                                                                              g =
                                                                                                                                                                                                Term.Apply (Term.UOp UserOp.ite) c
                                                                                                                                                                                          · rcases hHeadIte with ⟨c, rfl⟩
                                                                                                                                                                                            exact
                                                                                                                                                                                              substitute_simul_ite_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                c x1 a xs ts bvs
                                                                                                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                                                                                                hFTrans hTy
                                                                                                                                                                                                (fun hCTrans hCTy =>
                                                                                                                                                                                                  hRec
                                                                                                                                                                                                    (G := c) (bvs' := bvs)
                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                    hXsEnv hBvsEnv hCTrans hTs hActuals hCTy)
                                                                                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                                                                                  hRec
                                                                                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                (fun hATrans hATy =>
                                                                                                                                                                                                  hRec
                                                                                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                          · by_cases hHeadBvite :
                                                                                                                                                                                              ∃ c,
                                                                                                                                                                                                g =
                                                                                                                                                                                                  Term.Apply (Term.UOp UserOp.bvite) c
                                                                                                                                                                                            · rcases hHeadBvite with ⟨c, rfl⟩
                                                                                                                                                                                              exact
                                                                                                                                                                                                substitute_simul_bvite_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                  c x1 a xs ts bvs
                                                                                                                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                                                                                                                  hFTrans hTy
                                                                                                                                                                                                  (fun hCTrans hCTy =>
                                                                                                                                                                                                    hRec
                                                                                                                                                                                                      (G := c) (bvs' := bvs)
                                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                                      hXsEnv hBvsEnv hCTrans hTs hActuals hCTy)
                                                                                                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                                                                                                    hRec
                                                                                                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                                                                                    hRec
                                                                                                                                                                                                      (G := a) (bvs' := bvs)
                                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                            · by_cases hHeadStore :
                                                                                                                                                                                                ∃ arr,
                                                                                                                                                                                                  g =
                                                                                                                                                                                                    Term.Apply (Term.UOp UserOp.store) arr
                                                                                                                                                                                              · rcases hHeadStore with ⟨arr, rfl⟩
                                                                                                                                                                                                exact
                                                                                                                                                                                                  substitute_simul_store_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                    arr x1 a xs ts bvs
                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                    (fun hArrTrans hArrTy =>
                                                                                                                                                                                                      hRec
                                                                                                                                                                                                        (G := arr) (bvs' := bvs)
                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                        hXsEnv hBvsEnv hArrTrans hTs hActuals hArrTy)
                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                      hRec
                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                      hRec
                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                              · by_cases hHeadStrSubstr :
                                                                                                                                                                                                  ∃ s,
                                                                                                                                                                                                    g =
                                                                                                                                                                                                      Term.Apply (Term.UOp UserOp.str_substr) s
                                                                                                                                                                                                · rcases hHeadStrSubstr with ⟨s, rfl⟩
                                                                                                                                                                                                  exact
                                                                                                                                                                                                    substitute_simul_str_substr_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                      s x1 a xs ts bvs
                                                                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                                                                      hFTrans hTy
                                                                                                                                                                                                      (fun hSTrans hSTy =>
                                                                                                                                                                                                        hRec
                                                                                                                                                                                                          (G := s) (bvs' := bvs)
                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                          hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                      (fun hXTrans hXTy =>
                                                                                                                                                                                                        hRec
                                                                                                                                                                                                          (G := x1) (bvs' := bvs)
                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                          hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                                                                        hRec
                                                                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                · by_cases hHeadStrReplace :
                                                                                                                                                                                                    ∃ s,
                                                                                                                                                                                                      g =
                                                                                                                                                                                                        Term.Apply (Term.UOp UserOp.str_replace) s
                                                                                                                                                                                                  · rcases hHeadStrReplace with ⟨s, rfl⟩
                                                                                                                                                                                                    exact
                                                                                                                                                                                                      substitute_simul_str_replace_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                        s x1 a xs ts bvs
                                                                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                                                                        hFTrans hTy
                                                                                                                                                                                                        (fun hSTrans hSTy =>
                                                                                                                                                                                                          hRec
                                                                                                                                                                                                            (G := s) (bvs' := bvs)
                                                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                                                            hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                                                                                                          hRec
                                                                                                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                                                                            hRec
                                                                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                  · by_cases hHeadStrReplaceAll :
                                                                                                                                                                                                      ∃ s,
                                                                                                                                                                                                        g =
                                                                                                                                                                                                          Term.Apply (Term.UOp UserOp.str_replace_all) s
                                                                                                                                                                                                    · rcases hHeadStrReplaceAll with ⟨s, rfl⟩
                                                                                                                                                                                                      exact
                                                                                                                                                                                                        substitute_simul_str_replace_all_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                          s x1 a xs ts bvs
                                                                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                                                                          hFTrans hTy
                                                                                                                                                                                                          (fun hSTrans hSTy =>
                                                                                                                                                                                                            hRec
                                                                                                                                                                                                              (G := s) (bvs' := bvs)
                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                              hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                          (fun hXTrans hXTy =>
                                                                                                                                                                                                            hRec
                                                                                                                                                                                                              (G := x1) (bvs' := bvs)
                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                              hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                                                                            hRec
                                                                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                    · by_cases hHeadStrIndexof :
                                                                                                                                                                                                        ∃ s,
                                                                                                                                                                                                          g =
                                                                                                                                                                                                            Term.Apply (Term.UOp UserOp.str_indexof) s
                                                                                                                                                                                                      · rcases hHeadStrIndexof with ⟨s, rfl⟩
                                                                                                                                                                                                        exact
                                                                                                                                                                                                          substitute_simul_str_indexof_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                            s x1 a xs ts bvs
                                                                                                                                                                                                            hXsEnv hBvsEnv hTs
                                                                                                                                                                                                            hFTrans hTy
                                                                                                                                                                                                            (fun hSTrans hSTy =>
                                                                                                                                                                                                              hRec
                                                                                                                                                                                                                (G := s) (bvs' := bvs)
                                                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                                                hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                            (fun hXTrans hXTy =>
                                                                                                                                                                                                              hRec
                                                                                                                                                                                                                (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                                                hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                            (fun hATrans hATy =>
                                                                                                                                                                                                              hRec
                                                                                                                                                                                                                (G := a) (bvs' := bvs)
                                                                                                                                                                                                                (by simp; omega)
                                                                                                                                                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                      · by_cases hHeadStrUpdate :
                                                                                                                                                                                                          ∃ s,
                                                                                                                                                                                                            g =
                                                                                                                                                                                                              Term.Apply (Term.UOp UserOp.str_update) s
                                                                                                                                                                                                        · rcases hHeadStrUpdate with ⟨s, rfl⟩
                                                                                                                                                                                                          exact
                                                                                                                                                                                                            substitute_simul_str_update_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                              s x1 a xs ts bvs
                                                                                                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                                                                                                              hFTrans hTy
                                                                                                                                                                                                              (fun hSTrans hSTy =>
                                                                                                                                                                                                                hRec
                                                                                                                                                                                                                  (G := s) (bvs' := bvs)
                                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                                  hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                                                                                                hRec
                                                                                                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                              (fun hATrans hATy =>
                                                                                                                                                                                                                hRec
                                                                                                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                        · by_cases hHeadStrReplaceRe :
                                                                                                                                                                                                            ∃ s,
                                                                                                                                                                                                              g =
                                                                                                                                                                                                                Term.Apply (Term.UOp UserOp.str_replace_re) s
                                                                                                                                                                                                          · rcases hHeadStrReplaceRe with ⟨s, rfl⟩
                                                                                                                                                                                                            exact
                                                                                                                                                                                                              substitute_simul_str_replace_re_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                s x1 a xs ts bvs
                                                                                                                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                hFTrans hTy
                                                                                                                                                                                                                (fun hSTrans hSTy =>
                                                                                                                                                                                                                  hRec
                                                                                                                                                                                                                    (G := s) (bvs' := bvs)
                                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                                    hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                                                                                                  hRec
                                                                                                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                (fun hATrans hATy =>
                                                                                                                                                                                                                  hRec
                                                                                                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                          · by_cases hHeadStrReplaceReAll :
                                                                                                                                                                                                              ∃ s,
                                                                                                                                                                                                                g =
                                                                                                                                                                                                                  Term.Apply (Term.UOp UserOp.str_replace_re_all) s
                                                                                                                                                                                                            · rcases hHeadStrReplaceReAll with ⟨s, rfl⟩
                                                                                                                                                                                                              exact
                                                                                                                                                                                                                substitute_simul_str_replace_re_all_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                  s x1 a xs ts bvs
                                                                                                                                                                                                                  hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                  hFTrans hTy
                                                                                                                                                                                                                  (fun hSTrans hSTy =>
                                                                                                                                                                                                                    hRec
                                                                                                                                                                                                                      (G := s) (bvs' := bvs)
                                                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                                                      hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                  (fun hXTrans hXTy =>
                                                                                                                                                                                                                    hRec
                                                                                                                                                                                                                      (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                                                      hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                                                                                                    hRec
                                                                                                                                                                                                                      (G := a) (bvs' := bvs)
                                                                                                                                                                                                                      (by simp; omega)
                                                                                                                                                                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                            · by_cases hHeadStrIndexofRe :
                                                                                                                                                                                                                ∃ s,
                                                                                                                                                                                                                  g =
                                                                                                                                                                                                                    Term.Apply (Term.UOp UserOp.str_indexof_re) s
                                                                                                                                                                                                              · rcases hHeadStrIndexofRe with ⟨s, rfl⟩
                                                                                                                                                                                                                exact
                                                                                                                                                                                                                  substitute_simul_str_indexof_re_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                    s x1 a xs ts bvs
                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                                    (fun hSTrans hSTy =>
                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                        (G := s) (bvs' := bvs)
                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                        hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                              · by_cases hHeadSetInsert :
                                                                                                                                                                                                                  g = Term.UOp UserOp.set_insert
                                                                                                                                                                                                                · subst g
                                                                                                                                                                                                                  exact
                                                                                                                                                                                                                    substitute_simul_set_insert_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                      x1 a xs ts bvs
                                                                                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                      hFTrans hTy
                                                                                                                                                                                                                      (fun t hLt hTTrans hTTyNe => by
                                                                                                                                                                                                                        have hBoth :=
                                                                                                                                                                                                                          hRec
                                                                                                                                                                                                                            (G := t) (bvs' := bvs)
                                                                                                                                                                                                                            (by
                                                                                                                                                                                                                              exact Nat.lt_trans hLt (by simp; omega))
                                                                                                                                                                                                                            hXsEnv hBvsEnv hTTrans hTs hActuals hTTyNe
                                                                                                                                                                                                                        have hSubMatch :=
                                                                                                                                                                                                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                                                                                                                                                                                                            (__substitute_simul_rec (Term.Boolean isRename) t xs ts bvs)
                                                                                                                                                                                                                            hBoth.2
                                                                                                                                                                                                                        have hOrigMatch :=
                                                                                                                                                                                                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                                                                                                                                                                                                            t hTTrans
                                                                                                                                                                                                                        rw [hSubMatch, hOrigMatch, hBoth.1])
                                                                                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                                                                                        hRec
                                                                                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                · by_cases hHeadTuple :
                                                                                                                                                                                                                    g = Term.UOp UserOp.tuple
                                                                                                                                                                                                                  · subst g
                                                                                                                                                                                                                    exact
                                                                                                                                                                                                                      substitute_simul_tuple_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                        x1 a xs ts bvs
                                                                                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                        hFTrans hTy
                                                                                                                                                                                                                        (fun hXTrans hXTy =>
                                                                                                                                                                                                                          hRec
                                                                                                                                                                                                                            (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                                                                            hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                        (fun hATrans hATy =>
                                                                                                                                                                                                                          hRec
                                                                                                                                                                                                                            (G := a) (bvs' := bvs)
                                                                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                  · by_cases hHeadForall :
                                                                                                                                                                                                                      g = Term.UOp UserOp.forall
                                                                                                                                                                                                                    · subst g
                                                                                                                                                                                                                      exfalso
                                                                                                                                                                                                                      exact
                                                                                                                                                                                                                        false_of_forall_non_list_has_smt_translation
                                                                                                                                                                                                                          (P := False)
                                                                                                                                                                                                                          (by
                                                                                                                                                                                                                            intro v vs hX
                                                                                                                                                                                                                            exact
                                                                                                                                                                                                                              hBinder
                                                                                                                                                                                                                                ⟨Term.UOp UserOp.forall,
                                                                                                                                                                                                                                  v, vs, by
                                                                                                                                                                                                                                    exact
                                                                                                                                                                                                                                      congrArg
                                                                                                                                                                                                                                        (fun z =>
                                                                                                                                                                                                                                          Term.Apply
                                                                                                                                                                                                                                            (Term.UOp UserOp.forall) z)
                                                                                                                                                                                                                                        hX⟩)
                                                                                                                                                                                                                          (by
                                                                                                                                                                                                                            simpa
                                                                                                                                                                                                                              [RuleProofs.eo_has_smt_translation,
                                                                                                                                                                                                                                eoHasSmtTranslation]
                                                                                                                                                                                                                              using hFTrans)
                                                                                                                                                                                                                    · by_cases hHeadExists :
                                                                                                                                                                                                                        g = Term.UOp UserOp.exists
                                                                                                                                                                                                                      · subst g
                                                                                                                                                                                                                        exfalso
                                                                                                                                                                                                                        exact
                                                                                                                                                                                                                          false_of_exists_non_list_has_smt_translation
                                                                                                                                                                                                                            (P := False)
                                                                                                                                                                                                                            (by
                                                                                                                                                                                                                              intro v vs hX
                                                                                                                                                                                                                              exact
                                                                                                                                                                                                                                hBinder
                                                                                                                                                                                                                                  ⟨Term.UOp UserOp.exists,
                                                                                                                                                                                                                                    v, vs, by
                                                                                                                                                                                                                                      exact
                                                                                                                                                                                                                                        congrArg
                                                                                                                                                                                                                                          (fun z =>
                                                                                                                                                                                                                                            Term.Apply
                                                                                                                                                                                                                                              (Term.UOp UserOp.exists) z)
                                                                                                                                                                                                                                          hX⟩)
                                                                                                                                                                                                                            (by
                                                                                                                                                                                                                              simpa
                                                                                                                                                                                                                                [RuleProofs.eo_has_smt_translation,
                                                                                                                                                                                                                                  eoHasSmtTranslation]
                                                                                                                                                                                                                                using hFTrans)
                                                                                                                                                                                                                      · by_cases hHeadUpdate :
                                                                                                                                                                                                                          ∃ idx,
                                                                                                                                                                                                                            g =
                                                                                                                                                                                                                              Term.UOp1 UserOp1.update idx
                                                                                                                                                                                                                        · rcases hHeadUpdate with ⟨idx, rfl⟩
                                                                                                                                                                                                                          exact
                                                                                                                                                                                                                            substitute_simul_uop1_update_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                              idx x1 a xs ts bvs
                                                                                                                                                                                                                              hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                              hFTrans hTy
                                                                                                                                                                                                                              (fun hXTrans hXTy =>
                                                                                                                                                                                                                                hRec
                                                                                                                                                                                                                                  (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                                                  hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                              (fun hATrans hATy =>
                                                                                                                                                                                                                                hRec
                                                                                                                                                                                                                                  (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                  (by simp; omega)
                                                                                                                                                                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                        · by_cases hHeadTupleUpdate :
                                                                                                                                                                                                                            ∃ idx,
                                                                                                                                                                                                                              g =
                                                                                                                                                                                                                                Term.UOp1 UserOp1.tuple_update idx
                                                                                                                                                                                                                          · rcases hHeadTupleUpdate with ⟨idx, rfl⟩
                                                                                                                                                                                                                            exact
                                                                                                                                                                                                                              substitute_simul_uop1_tuple_update_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                idx x1 a xs ts bvs
                                                                                                                                                                                                                                hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                hFTrans hTy
                                                                                                                                                                                                                                (fun hXTrans hXTy =>
                                                                                                                                                                                                                                  hRec
                                                                                                                                                                                                                                    (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                                (fun hATrans hATy =>
                                                                                                                                                                                                                                  hRec
                                                                                                                                                                                                                                    (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                    (by simp; omega)
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                          · by_cases hStringSkolem :
                                                                                                                                                                                                                              g =
                                                                                                                                                                                                                                  Term.UOp UserOp._at_strings_num_occur_re ∨
                                                                                                                                                                                                                                (∃ s,
                                                                                                                                                                                                                                  g =
                                                                                                                                                                                                                                    Term.Apply
                                                                                                                                                                                                                                      (Term.UOp UserOp._at_strings_occur_index) s) ∨
                                                                                                                                                                                                                                (∃ s,
                                                                                                                                                                                                                                  g =
                                                                                                                                                                                                                                    Term.Apply
                                                                                                                                                                                                                                      (Term.UOp UserOp._at_strings_occur_index_re) s) ∨
                                                                                                                                                                                                                                (∃ s p,
                                                                                                                                                                                                                                  g =
                                                                                                                                                                                                                                    Term.Apply
                                                                                                                                                                                                                                      (Term.Apply
                                                                                                                                                                                                                                        (Term.UOp UserOp._at_strings_replace_all_result) s) p) ∨
                                                                                                                                                                                                                                (∃ s p,
                                                                                                                                                                                                                                  g =
                                                                                                                                                                                                                                    Term.Apply
                                                                                                                                                                                                                                      (Term.Apply
                                                                                                                                                                                                                                        (Term.UOp UserOp._at_strings_replace_re_all_result) s) p)
                                                                                                                                                                                                                            · rcases hStringSkolem with
                                                                                                                                                                                                                                hNumOccurRe | hOccurIndex | hOccurIndexRe |
                                                                                                                                                                                                                                  hReplaceAllResult | hReplaceReAllResult
                                                                                                                                                                                                                              · subst g
                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                  substitute_simul_strings_num_occur_re_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                    x1 a xs ts bvs
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                              · rcases hOccurIndex with ⟨s, rfl⟩
                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                  substitute_simul_strings_occur_index_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                    s x1 a xs ts bvs
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                                                    (fun hSTrans hSTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := s) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                              · rcases hOccurIndexRe with ⟨s, rfl⟩
                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                  substitute_simul_strings_occur_index_re_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                    s x1 a xs ts bvs
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                                                    (fun hSTrans hSTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := s) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                              · rcases hReplaceAllResult with ⟨s, p, rfl⟩
                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                  substitute_simul_strings_replace_all_result_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                    s p x1 a xs ts bvs
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                                                    (fun hSTrans hSTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := s) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                                    (fun hPTrans hPTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := p) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hPTrans hTs hActuals hPTy)
                                                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                              · rcases hReplaceReAllResult with ⟨s, p, rfl⟩
                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                  substitute_simul_strings_replace_re_all_result_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                    s p x1 a xs ts bvs
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                    hFTrans hTy
                                                                                                                                                                                                                                    (fun hSTrans hSTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := s) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hSTrans hTs hActuals hSTy)
                                                                                                                                                                                                                                    (fun hPTrans hPTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := p) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hPTrans hTs hActuals hPTy)
                                                                                                                                                                                                                                    (fun hXTrans hXTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := x1) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hXTrans hTs hActuals hXTy)
                                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                            · have hHeadStringsNumOccurRe :
                                                                                                                                                                                                                                  g ≠ Term.UOp UserOp._at_strings_num_occur_re :=
                                                                                                                                                                                                                                fun h => hStringSkolem (Or.inl h)
                                                                                                                                                                                                                              have hHeadStringsOccurIndex :
                                                                                                                                                                                                                                  ¬ ∃ s,
                                                                                                                                                                                                                                    g =
                                                                                                                                                                                                                                      Term.Apply
                                                                                                                                                                                                                                        (Term.UOp UserOp._at_strings_occur_index) s :=
                                                                                                                                                                                                                                fun h => hStringSkolem (Or.inr (Or.inl h))
                                                                                                                                                                                                                              have hHeadStringsOccurIndexRe :
                                                                                                                                                                                                                                  ¬ ∃ s,
                                                                                                                                                                                                                                    g =
                                                                                                                                                                                                                                      Term.Apply
                                                                                                                                                                                                                                        (Term.UOp UserOp._at_strings_occur_index_re) s :=
                                                                                                                                                                                                                                fun h => hStringSkolem (Or.inr (Or.inr (Or.inl h)))
                                                                                                                                                                                                                              have hHeadStringsReplaceAllResult :
                                                                                                                                                                                                                                  ¬ ∃ s p,
                                                                                                                                                                                                                                    g =
                                                                                                                                                                                                                                      Term.Apply
                                                                                                                                                                                                                                        (Term.Apply
                                                                                                                                                                                                                                          (Term.UOp UserOp._at_strings_replace_all_result) s) p :=
                                                                                                                                                                                                                                fun h =>
                                                                                                                                                                                                                                  hStringSkolem
                                                                                                                                                                                                                                    (Or.inr (Or.inr (Or.inr (Or.inl h))))
                                                                                                                                                                                                                              have hHeadStringsReplaceReAllResult :
                                                                                                                                                                                                                                  ¬ ∃ s p,
                                                                                                                                                                                                                                    g =
                                                                                                                                                                                                                                      Term.Apply
                                                                                                                                                                                                                                        (Term.Apply
                                                                                                                                                                                                                                          (Term.UOp UserOp._at_strings_replace_re_all_result) s) p :=
                                                                                                                                                                                                                                fun h =>
                                                                                                                                                                                                                                  hStringSkolem
                                                                                                                                                                                                                                    (Or.inr (Or.inr (Or.inr (Or.inr h))))
                                                                                                                                                                                                                              by_cases hGVar :
                                                                                                                                                                                                                              ∃ name T,
                                                                                                                                                                                                                                g =
                                                                                                                                                                                                                                  Term.Var name T
                                                                                                                                                                                                                              · rcases hGVar with ⟨name, T, rfl⟩
                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                  substitute_simul_apply_apply_var_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                    name T x1 a xs ts bvs
                                                                                                                                                                                                                                    hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                    hFTrans
                                                                                                                                                                                                                                    (fun hHeadTrans hHeadTy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := Term.Apply (Term.Var name T) x1)
                                                                                                                                                                                                                                        (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hHeadTrans hTs hActuals hHeadTy)
                                                                                                                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                                                                                                                      hRec
                                                                                                                                                                                                                                        (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                        (by simp; omega)
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                                    (substitute_simul_apply_apply_var_head_generic_head_typeof_ne_stuck
                                                                                                                                                                                                                                      name T x1 a xs ts bvs
                                                                                                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                      hFTrans hTy)
                                                                                                                                                                                                                                    hTy
                                                                                                                                                                                                                              · by_cases hGUConst :
                                                                                                                                                                                                                                  ∃ i U,
                                                                                                                                                                                                                                    g =
                                                                                                                                                                                                                                      Term.UConst i U
                                                                                                                                                                                                                                · rcases hGUConst with ⟨i, U, rfl⟩
                                                                                                                                                                                                                                  exact
                                                                                                                                                                                                                                    substitute_simul_apply_apply_atom_base_generic_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                      (Term.UConst i U) x1 a xs ts bvs
                                                                                                                                                                                                                                      hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                      (by intro f y hEq; cases hEq)
                                                                                                                                                                                                                                      (by intro name T hEq; cases hEq)
                                                                                                                                                                                                                                      (by intro hEq; cases hEq)
                                                                                                                                                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                                                      (by
                                                                                                                                                                                                                                        change
                                                                                                                                                                                                                                          __smtx_typeof
                                                                                                                                                                                                                                              (SmtTerm.Apply
                                                                                                                                                                                                                                                (SmtTerm.UConst
                                                                                                                                                                                                                                                  (native_uconst_id i)
                                                                                                                                                                                                                                                  (__eo_to_smt_type U))
                                                                                                                                                                                                                                                (__eo_to_smt x1)) =
                                                                                                                                                                                                                                            __smtx_typeof_apply
                                                                                                                                                                                                                                              (__smtx_typeof
                                                                                                                                                                                                                                                (SmtTerm.UConst
                                                                                                                                                                                                                                                  (native_uconst_id i)
                                                                                                                                                                                                                                                  (__eo_to_smt_type U)))
                                                                                                                                                                                                                                              (__smtx_typeof (__eo_to_smt x1))
                                                                                                                                                                                                                                        rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                                                      hFTrans
                                                                                                                                                                                                                                      (fun hHeadTrans hHeadTy =>
                                                                                                                                                                                                                                        hRec
                                                                                                                                                                                                                                          (G := Term.Apply (Term.UConst i U) x1)
                                                                                                                                                                                                                                          (bvs' := bvs)
                                                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                                                          hXsEnv hBvsEnv hHeadTrans hTs hActuals hHeadTy)
                                                                                                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                                                                                                        hRec
                                                                                                                                                                                                                                          (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                                      (substitute_simul_apply_apply_atom_base_generic_head_typeof_ne_stuck
                                                                                                                                                                                                                                        (Term.UConst i U) x1 a xs ts bvs
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                        (by intro f y hEq; cases hEq)
                                                                                                                                                                                                                                        (by intro name T hEq; cases hEq)
                                                                                                                                                                                                                                        (by intro hEq; cases hEq)
                                                                                                                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                        (by
                                                                                                                                                                                                                                          change
                                                                                                                                                                                                                                            __smtx_typeof
                                                                                                                                                                                                                                                (SmtTerm.Apply
                                                                                                                                                                                                                                                  (SmtTerm.UConst
                                                                                                                                                                                                                                                    (native_uconst_id i)
                                                                                                                                                                                                                                                    (__eo_to_smt_type U))
                                                                                                                                                                                                                                                  (__eo_to_smt x1)) =
                                                                                                                                                                                                                                              __smtx_typeof_apply
                                                                                                                                                                                                                                                (__smtx_typeof
                                                                                                                                                                                                                                                  (SmtTerm.UConst
                                                                                                                                                                                                                                                    (native_uconst_id i)
                                                                                                                                                                                                                                                    (__eo_to_smt_type U)))
                                                                                                                                                                                                                                                (__smtx_typeof (__eo_to_smt x1))
                                                                                                                                                                                                                                          rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                        hFTrans hTy)
                                                                                                                                                                                                                                      hTy
                                                                                                                                                                                                                                · by_cases hGDtCons :
                                                                                                                                                                                                                                    ∃ s d i,
                                                                                                                                                                                                                                      g =
                                                                                                                                                                                                                                        Term.DtCons s d i
                                                                                                                                                                                                                                  · rcases hGDtCons with ⟨s, d, i, rfl⟩
                                                                                                                                                                                                                                    have hOuterTranslate :
                                                                                                                                                                                                                                        __eo_to_smt (Term.Apply (Term.Apply (Term.DtCons s d i) x1) a) =
                                                                                                                                                                                                                                          SmtTerm.Apply
                                                                                                                                                                                                                                            (__eo_to_smt (Term.Apply (Term.DtCons s d i) x1))
                                                                                                                                                                                                                                            (__eo_to_smt a) := by
                                                                                                                                                                                                                                      rfl
                                                                                                                                                                                                                                    have hGenericOuter :
                                                                                                                                                                                                                                        __smtx_typeof
                                                                                                                                                                                                                                            (SmtTerm.Apply
                                                                                                                                                                                                                                              (__eo_to_smt (Term.Apply (Term.DtCons s d i) x1))
                                                                                                                                                                                                                                              (__eo_to_smt a)) =
                                                                                                                                                                                                                                          __smtx_typeof_apply
                                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt (Term.Apply (Term.DtCons s d i) x1)))
                                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt a)) :=
                                                                                                                                                                                                                                      generic_apply_type_of_non_special_head_closed
                                                                                                                                                                                                                                        (__eo_to_smt (Term.Apply (Term.DtCons s d i) x1))
                                                                                                                                                                                                                                        (__eo_to_smt a)
                                                                                                                                                                                                                                        (TranslationProofs.eo_to_smt_apply_ne_dt_sel
                                                                                                                                                                                                                                          (Term.DtCons s d i) x1)
                                                                                                                                                                                                                                        (TranslationProofs.eo_to_smt_apply_ne_dt_tester
                                                                                                                                                                                                                                          (Term.DtCons s d i) x1)
                                                                                                                                                                                                                                    have hHeadTrans :
                                                                                                                                                                                                                                        RuleProofs.eo_has_smt_translation
                                                                                                                                                                                                                                          (Term.Apply (Term.DtCons s d i) x1) :=
                                                                                                                                                                                                                                      (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                                                                                                                                                                                                                                        (Term.Apply (Term.DtCons s d i) x1) a
                                                                                                                                                                                                                                        hOuterTranslate hGenericOuter hFTrans).1
                                                                                                                                                                                                                                    have hReserved :
                                                                                                                                                                                                                                        __eo_to_smt_reserved_datatype_name s = false :=
                                                                                                                                                                                                                                      SubstituteSupport.dtcons_reserved_false_of_apply_has_smt_translation
                                                                                                                                                                                                                                        hHeadTrans
                                                                                                                                                                                                                                    exact
                                                                                                                                                                                                                                      substitute_simul_apply_apply_atom_base_generic_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                        (Term.DtCons s d i) x1 a xs ts bvs
                                                                                                                                                                                                                                        hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                        (by intro f y hEq; cases hEq)
                                                                                                                                                                                                                                        (by intro name T hEq; cases hEq)
                                                                                                                                                                                                                                        (by intro hEq; cases hEq)
                                                                                                                                                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                        (by
                                                                                                                                                                                                                                          change
                                                                                                                                                                                                                                            __smtx_typeof
                                                                                                                                                                                                                                                (SmtTerm.Apply
                                                                                                                                                                                                                                                  (native_ite
                                                                                                                                                                                                                                                    (__eo_to_smt_reserved_datatype_name s)
                                                                                                                                                                                                                                                    SmtTerm.None
                                                                                                                                                                                                                                                    (SmtTerm.DtCons s
                                                                                                                                                                                                                                                      (__eo_to_smt_datatype_decl d)
                                                                                                                                                                                                                                                      i))
                                                                                                                                                                                                                                                  (__eo_to_smt x1)) =
                                                                                                                                                                                                                                              __smtx_typeof_apply
                                                                                                                                                                                                                                                (__smtx_typeof
                                                                                                                                                                                                                                                  (native_ite
                                                                                                                                                                                                                                                    (__eo_to_smt_reserved_datatype_name s)
                                                                                                                                                                                                                                                    SmtTerm.None
                                                                                                                                                                                                                                                    (SmtTerm.DtCons s
                                                                                                                                                                                                                                                      (__eo_to_smt_datatype_decl d)
                                                                                                                                                                                                                                                      i)))
                                                                                                                                                                                                                                                (__smtx_typeof (__eo_to_smt x1))
                                                                                                                                                                                                                                          rw [hReserved]
                                                                                                                                                                                                                                          simp [native_ite]
                                                                                                                                                                                                                                          rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                        hFTrans
                                                                                                                                                                                                                                        (fun hHeadTrans hHeadTy =>
                                                                                                                                                                                                                                          hRec
                                                                                                                                                                                                                                            (G := Term.Apply (Term.DtCons s d i) x1)
                                                                                                                                                                                                                                            (bvs' := bvs)
                                                                                                                                                                                                                                            (by simp; omega)
                                                                                                                                                                                                                                            hXsEnv hBvsEnv hHeadTrans hTs hActuals hHeadTy)
                                                                                                                                                                                                                                       (fun hATrans hATy =>
                                                                                                                                                                                                                                         hRec
                                                                                                                                                                                                                                           (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                           (by simp; omega)
                                                                                                                                                                                                                                           hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                                        (substitute_simul_apply_apply_atom_base_generic_head_typeof_ne_stuck
                                                                                                                                                                                                                                          (Term.DtCons s d i) x1 a xs ts bvs
                                                                                                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                          (by intro f y hEq; cases hEq)
                                                                                                                                                                                                                                          (by intro name T hEq; cases hEq)
                                                                                                                                                                                                                                          (by intro hEq; cases hEq)
                                                                                                                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                                                          (by
                                                                                                                                                                                                                                            change
                                                                                                                                                                                                                                              __smtx_typeof
                                                                                                                                                                                                                                                  (SmtTerm.Apply
                                                                                                                                                                                                                                                    (native_ite
                                                                                                                                                                                                                                                      (__eo_to_smt_reserved_datatype_name s)
                                                                                                                                                                                                                                                      SmtTerm.None
                                                                                                                                                                                                                                                      (SmtTerm.DtCons s
                                                                                                                                                                                                                                                        (__eo_to_smt_datatype_decl d)
                                                                                                                                                                                                                                                        i))
                                                                                                                                                                                                                                                    (__eo_to_smt x1)) =
                                                                                                                                                                                                                                                __smtx_typeof_apply
                                                                                                                                                                                                                                                  (__smtx_typeof
                                                                                                                                                                                                                                                    (native_ite
                                                                                                                                                                                                                                                      (__eo_to_smt_reserved_datatype_name s)
                                                                                                                                                                                                                                                      SmtTerm.None
                                                                                                                                                                                                                                                      (SmtTerm.DtCons s
                                                                                                                                                                                                                                                        (__eo_to_smt_datatype_decl d)
                                                                                                                                                                                                                                                        i)))
                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt x1))
                                                                                                                                                                                                                                            rw [hReserved]
                                                                                                                                                                                                                                            simp [native_ite]
                                                                                                                                                                                                                                            rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                                                          hFTrans hTy)
                                                                                                                                                                                                                                       hTy
                                                                                                                                                                                                                                  · let hUOp : ApplyApplyUOpBranchExclusions g :=
                                                                                                                                                                                                                                      { notOr := hHeadOr,
                                                                                                                                                                                                                                        notAnd := hHeadAnd,
                                                                                                                                                                                                                                        notImp := hHeadImp,
                                                                                                                                                                                                                                        notXor := hHeadXor,
                                                                                                                                                                                                                                        notEq := hHeadEq,
                                                                                                                                                                                                                                        notPlus := hHeadPlus,
                                                                                                                                                                                                                                        notNeg := hHeadNeg,
                                                                                                                                                                                                                                        notMult := hHeadMult,
                                                                                                                                                                                                                                        notLt := hHeadLt,
                                                                                                                                                                                                                                        notLeq := hHeadLeq,
                                                                                                                                                                                                                                        notGt := hHeadGt,
                                                                                                                                                                                                                                        notGeq := hHeadGeq,
                                                                                                                                                                                                                                        notDiv := hHeadDiv,
                                                                                                                                                                                                                                        notMod := hHeadMod,
                                                                                                                                                                                                                                        notDivisible := hHeadDivisible,
                                                                                                                                                                                                                                        notDivTotal := hHeadDivTotal,
                                                                                                                                                                                                                                        notModTotal := hHeadModTotal,
                                                                                                                                                                                                                                        notSelect := hHeadSelect,
                                                                                                                                                                                                                                        notArrayDeqDiff := hHeadArrayDeqDiff,
                                                                                                                                                                                                                                        notConcat := hHeadConcat,
                                                                                                                                                                                                                                        notBvand := hHeadBvand,
                                                                                                                                                                                                                                        notBvor := hHeadBvor,
                                                                                                                                                                                                                                        notBvnand := hHeadBvnand,
                                                                                                                                                                                                                                        notBvnor := hHeadBvnor,
                                                                                                                                                                                                                                        notBvxor := hHeadBvxor,
                                                                                                                                                                                                                                        notBvxnor := hHeadBvxnor,
                                                                                                                                                                                                                                        notBvcomp := hHeadBvcomp,
                                                                                                                                                                                                                                        notBvadd := hHeadBvadd,
                                                                                                                                                                                                                                        notBvmul := hHeadBvmul,
                                                                                                                                                                                                                                        notBvudiv := hHeadBvudiv,
                                                                                                                                                                                                                                        notBvurem := hHeadBvurem,
                                                                                                                                                                                                                                        notBvsub := hHeadBvsub,
                                                                                                                                                                                                                                        notBvsdiv := hHeadBvsdiv,
                                                                                                                                                                                                                                        notBvsrem := hHeadBvsrem,
                                                                                                                                                                                                                                        notBvsmod := hHeadBvsmod,
                                                                                                                                                                                                                                        notBvult := hHeadBvult,
                                                                                                                                                                                                                                        notBvule := hHeadBvule,
                                                                                                                                                                                                                                        notBvugt := hHeadBvugt,
                                                                                                                                                                                                                                        notBvuge := hHeadBvuge,
                                                                                                                                                                                                                                        notBvslt := hHeadBvslt,
                                                                                                                                                                                                                                        notBvsle := hHeadBvsle,
                                                                                                                                                                                                                                        notBvsgt := hHeadBvsgt,
                                                                                                                                                                                                                                        notBvsge := hHeadBvsge,
                                                                                                                                                                                                                                        notBvshl := hHeadBvshl,
                                                                                                                                                                                                                                        notBvlshr := hHeadBvlshr,
                                                                                                                                                                                                                                        notBvashr := hHeadBvashr,
                                                                                                                                                                                                                                        notBvuaddo := hHeadBvuaddo,
                                                                                                                                                                                                                                        notBvsaddo := hHeadBvsaddo,
                                                                                                                                                                                                                                        notBvumulo := hHeadBvumulo,
                                                                                                                                                                                                                                        notBvsmulo := hHeadBvsmulo,
                                                                                                                                                                                                                                        notBvusubo := hHeadBvusubo,
                                                                                                                                                                                                                                        notBvssubo := hHeadBvssubo,
                                                                                                                                                                                                                                        notBvsdivo := hHeadBvsdivo,
                                                                                                                                                                                                                                        notBvultbv := hHeadBvultbv,
                                                                                                                                                                                                                                        notBvsltbv := hHeadBvsltbv,
                                                                                                                                                                                                                                        notFromBools := hHeadFromBools,
                                                                                                                                                                                                                                        notStrConcat := hHeadStrConcat,
                                                                                                                                                                                                                                        notStrContains := hHeadStrContains,
                                                                                                                                                                                                                                        notStrAt := hHeadStrAt,
                                                                                                                                                                                                                                        notStrPrefixof := hHeadStrPrefixof,
                                                                                                                                                                                                                                        notStrSuffixof := hHeadStrSuffixof,
                                                                                                                                                                                                                                        notStrLt := hHeadStrLt,
                                                                                                                                                                                                                                        notStrLeq := hHeadStrLeq,
                                                                                                                                                                                                                                        notReRange := hHeadReRange,
                                                                                                                                                                                                                                        notReConcat := hHeadReConcat,
                                                                                                                                                                                                                                        notReInter := hHeadReInter,
                                                                                                                                                                                                                                        notReUnion := hHeadReUnion,
                                                                                                                                                                                                                                        notReDiff := hHeadReDiff,
                                                                                                                                                                                                                                        notStrInRe := hHeadStrInRe,
                                                                                                                                                                                                                                        notSeqNth := hHeadSeqNth,
                                                                                                                                                                                                                                        notStringsDeqDiff := hHeadStringsDeqDiff,
                                                                                                                                                                                                                                        notStringsStoiResult := hHeadStringsStoiResult,
                                                                                                                                                                                                                                        notStringsItosResult := hHeadStringsItosResult,
                                                                                                                                                                                                                                        notStringsNumOccur := hHeadStringsNumOccur,
                                                                                                                                                                                                                                        notStringsNumOccurRe := hHeadStringsNumOccurRe,
                                                                                                                                                                                                                                        notTuple := hHeadTuple,
                                                                                                                                                                                                                                        notSetUnion := hHeadSetUnion,
                                                                                                                                                                                                                                        notSetInter := hHeadSetInter,
                                                                                                                                                                                                                                        notSetMinus := hHeadSetMinus,
                                                                                                                                                                                                                                        notSetMember := hHeadSetMember,
                                                                                                                                                                                                                                        notSetSubset := hHeadSetSubset,
                                                                                                                                                                                                                                        notSetInsert := hHeadSetInsert,
                                                                                                                                                                                                                                        notSetsDeqDiff := hHeadSetsDeqDiff,
                                                                                                                                                                                                                                        notQdiv := hHeadQdiv,
                                                                                                                                                                                                                                        notQdivTotal := hHeadQdivTotal,
                                                                                                                                                                                                                                        notForall := hHeadForall,
                                                                                                                                                                                                                                        notExists := hHeadExists }
                                                                                                                                                                                                                                    let hApplyUOp : ApplyApplyApplyUOpBranchExclusions g :=
                                                                                                                                                                                                                                      { notIte := hHeadIte,
                                                                                                                                                                                                                                        notStore := hHeadStore,
                                                                                                                                                                                                                                        notBvite := hHeadBvite,
                                                                                                                                                                                                                                        notStrSubstr := hHeadStrSubstr,
                                                                                                                                                                                                                                        notStrReplace := hHeadStrReplace,
                                                                                                                                                                                                                                        notStrReplaceAll := hHeadStrReplaceAll,
                                                                                                                                                                                                                                        notStrIndexof := hHeadStrIndexof,
                                                                                                                                                                                                                                        notStrUpdate := hHeadStrUpdate,
                                                                                                                                                                                                                                        notStrReplaceRe := hHeadStrReplaceRe,
                                                                                                                                                                                                                                        notStrReplaceReAll := hHeadStrReplaceReAll,
                                                                                                                                                                                                                                        notStrIndexofRe := hHeadStrIndexofRe,
                                                                                                                                                                                                                                        notStringsOccurIndex := hHeadStringsOccurIndex,
                                                                                                                                                                                                                                        notStringsOccurIndexRe := hHeadStringsOccurIndexRe }
                                                                                                                                                                                                                                    let hApplyApplyUOp :
                                                                                                                                                                                                                                        ApplyApplyApplyApplyUOpBranchExclusions g :=
                                                                                                                                                                                                                                      { notStringsReplaceAllResult :=
                                                                                                                                                                                                                                          hHeadStringsReplaceAllResult,
                                                                                                                                                                                                                                        notStringsReplaceReAllResult :=
                                                                                                                                                                                                                                          hHeadStringsReplaceReAllResult }
                                                                                                                                                                                                                                    by_cases hGUOp :
                                                                                                                                                                                                                                      ∃ op,
                                                                                                                                                                                                                                        g = Term.UOp op
                                                                                                                                                                                                                                    · rcases hGUOp with ⟨op, rfl⟩
                                                                                                                                                                                                                                      exact
                                                                                                                                                                                                                                        substitute_simul_apply_apply_uop_generic_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                          op x1 a xs ts bvs
                                                                                                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                          (eo_to_smt_apply_apply_generic_of_branch_exclusions
                                                                                                                                                                                                                                            (g := Term.UOp op) (x := x1) (a := a)
                                                                                                                                                                                                                                            hUOp hHeadUpdate hHeadTupleUpdate hApplyUOp
                                                                                                                                                                                                                                            hApplyApplyUOp)
                                                                                                                                                                                                                                          hFTrans
                                                                                                                                                                                                                                          (fun hHeadTrans hHeadTy =>
                                                                                                                                                                                                                                            hRec
                                                                                                                                                                                                                                              (G := Term.Apply (Term.UOp op) x1)
                                                                                                                                                                                                                                              (bvs' := bvs)
                                                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                                                              hXsEnv hBvsEnv hHeadTrans hTs hActuals hHeadTy)
                                                                                                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                                                                                                            hRec
                                                                                                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                                          hTy
                                                                                                                                                                                                                                    · exact
                                                                                                                                                                                                                                        substitute_simul_apply_apply_branch_residual_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                                                                                                                          g x1 a xs ts bvs
                                                                                                                                                                                                                                          hXsEnv hBvsEnv hTs
                                                                                                                                                                                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                          hUOp hHeadUpdate hHeadTupleUpdate hApplyUOp
                                                                                                                                                                                                                                          hApplyApplyUOp
                                                                                                                                                                                                                                          (fun op hEq => hGUOp ⟨op, hEq⟩)
                                                                                                                                                                                                                                          hFTrans
                                                                                                                                                                                                                                          (fun hHeadTrans hHeadTy =>
                                                                                                                                                                                                                                            hRec
                                                                                                                                                                                                                                              (G := Term.Apply g x1)
                                                                                                                                                                                                                                              (bvs' := bvs)
                                                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                                                              hXsEnv hBvsEnv hHeadTrans hTs hActuals hHeadTy)
                                                                                                                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                                                                                                                            hRec
                                                                                                                                                                                                                                              (G := a) (bvs' := bvs)
                                                                                                                                                                                                                                              (by simp; omega)
                                                                                                                                                                                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                                                                                                                                                                                          hTy
                · by_cases hHeadSpecial :
                    (∃ op, f = Term.UOp op) ∨
                      (∃ op x, f = Term.UOp1 op x) ∨
                      (∃ op x y, f = Term.UOp2 op x y) ∨
                      (∃ op w x y, f = Term.UOp3 op w x y) ∨
                      (∃ s d i j, f = Term.DtSel s d i j) ∨
                      f = Term.Stuck
                  · by_cases hHeadNot : f = Term.UOp UserOp.not
                    · subst f
                      refine ⟨?_, ?_⟩
                      · exact
                          SubstituteSupport.substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                            UserOp.not a xs ts bvs hXsEnv hBvsEnv hTs
                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                            hFTrans
                            (fun h =>
                              not_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X hApp => by
                              change __eo_typeof_not (__eo_typeof X) ≠
                                Term.Stuck at hApp
                              intro hX
                              rw [hX] at hApp
                              exact hApp rfl)
                            (fun X Y hXY => by
                              change __eo_typeof_not (__eo_typeof X) =
                                __eo_typeof_not (__eo_typeof Y)
                              rw [hXY])
                            (fun hATrans hATy =>
                              (hRec
                                (G := a) (bvs' := bvs)
                                (by simp)
                                hXsEnv hBvsEnv hATrans hTs hActuals hATy).1)
                            hTy
                      · exact
                          SubstituteTranslatabilitySupport.substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                            UserOp.not a xs ts bvs hXsEnv hBvsEnv hTs
                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                            hFTrans hTy
                            (fun h =>
                              not_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X hApp => by
                              change __eo_typeof_not (__eo_typeof X) ≠
                                Term.Stuck at hApp
                              intro hX
                              rw [hX] at hApp
                              exact hApp rfl)
                            (fun X hXTrans hApp => by
                              have hXBool : __eo_typeof X = Term.Bool := by
                                change __eo_typeof_not (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                cases hXTy : __eo_typeof X <;>
                                  simp [__eo_typeof_not, hXTy] at hApp ⊢
                              have hXBoolType : RuleProofs.eo_has_bool_type X :=
                                RuleProofs.eo_typeof_bool_implies_has_bool_type
                                  X hXTrans hXBool
                              exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                (Term.Apply (Term.UOp UserOp.not) X)
                                (RuleProofs.eo_has_bool_type_not_of_bool_arg
                                  X hXBoolType))
                            (fun hATrans hATy =>
                              (hRec
                                (G := a) (bvs' := bvs)
                                (by simp)
                                hXsEnv hBvsEnv hATrans hTs hActuals hATy).2)
                    · by_cases hHeadAbs : f = Term.UOp UserOp.abs
                      · subst f
                        refine ⟨?_, ?_⟩
                        · exact
                            SubstituteSupport.substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                              UserOp.abs a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans
                              (fun h =>
                                abs_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X hApp => by
                                change __eo_typeof_abs (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                intro hX
                                rw [hX] at hApp
                                exact hApp rfl)
                              (fun X Y hXY => by
                                change __eo_typeof_abs (__eo_typeof X) =
                                  __eo_typeof_abs (__eo_typeof Y)
                                rw [hXY])
                              (fun hATrans hATy =>
                                (hRec
                                  (G := a) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy).1)
                              hTy
                        · exact
                            SubstituteTranslatabilitySupport.substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                              UserOp.abs a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans hTy
                              (fun h =>
                                abs_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X hApp => by
                                change __eo_typeof_abs (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                  hArg | hArg
                                · rw [hArg]
                                  intro h
                                  cases h
                                · rw [hArg]
                                  intro h
                                  cases h)
                              (fun X hXTrans hApp => by
                                have hXMatch :
                                    __smtx_typeof (__eo_to_smt X) =
                                      __eo_to_smt_type (__eo_typeof X) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    X hXTrans
                                unfold RuleProofs.eo_has_smt_translation
                                change
                                  __smtx_typeof (SmtTerm.abs (__eo_to_smt X)) ≠
                                    SmtType.None
                                rw [typeof_abs_eq]
                                change __eo_typeof_abs (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                  hArgInt | hArgReal
                                · have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                    rw [hXMatch, hArgInt]
                                    rfl
                                  simp [__smtx_typeof_arith_overload_op_1,
                                    hSmtArg]
                                · have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                    rw [hXMatch, hArgReal]
                                    rfl
                                  simp [__smtx_typeof_arith_overload_op_1,
                                    hSmtArg])
                              (fun hATrans hATy =>
                                (hRec
                                  (G := a) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy).2)
                      · by_cases hHeadToReal : f = Term.UOp UserOp.to_real
                        · subst f
                          exact
                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                              UserOp.to_real a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans hTy
                              (fun h =>
                                to_real_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X hApp => by
                                change __eo_typeof_to_real (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rw [eo_typeof_to_real_arg_arith_of_ne_stuck hApp]
                                intro h
                                cases h)
                              (fun X Y hXY => by
                                change __eo_typeof_to_real (__eo_typeof X) =
                                  __eo_typeof_to_real (__eo_typeof Y)
                                rw [hXY])
                              (fun X hXTrans hApp => by
                                have hXMatch :
                                    __smtx_typeof (__eo_to_smt X) =
                                      __eo_to_smt_type (__eo_typeof X) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    X hXTrans
                                unfold RuleProofs.eo_has_smt_translation
                                change
                                  __smtx_typeof (SmtTerm.to_real (__eo_to_smt X)) ≠
                                    SmtType.None
                                rw [typeof_to_real_eq]
                                change __eo_typeof_to_real (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                have hArgInt :=
                                  eo_typeof_to_real_arg_arith_of_ne_stuck hApp
                                have hSmtArg :
                                    __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                  rw [hXMatch, hArgInt]
                                  rfl
                                simp [hSmtArg, native_ite, native_Teq])
                              (fun hATrans hATy =>
                                hRec
                                  (G := a) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                        · by_cases hHeadToInt : f = Term.UOp UserOp.to_int
                          · subst f
                            exact
                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                UserOp.to_int a xs ts bvs hXsEnv hBvsEnv hTs
                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                hFTrans hTy
                                (fun h =>
                                  to_int_arg_has_smt_translation_of_has_smt_translation h)
                                (fun X hApp => by
                                  change __eo_typeof_to_int (__eo_typeof X) ≠
                                    Term.Stuck at hApp
                                  have hArgReal :
                                      __eo_typeof X = Term.UOp UserOp.Real :=
                                    eo_typeof_to_int_arg_real_of_ne_stuck hApp
                                  rw [hArgReal]
                                  intro h
                                  cases h)
                                (fun X Y hXY => by
                                  change __eo_typeof_to_int (__eo_typeof X) =
                                    __eo_typeof_to_int (__eo_typeof Y)
                                  rw [hXY])
                                (fun X hXTrans hApp => by
                                  have hXMatch :
                                      __smtx_typeof (__eo_to_smt X) =
                                        __eo_to_smt_type (__eo_typeof X) :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                      X hXTrans
                                  unfold RuleProofs.eo_has_smt_translation
                                  change
                                    __smtx_typeof (SmtTerm.to_int (__eo_to_smt X)) ≠
                                      SmtType.None
                                  rw [typeof_to_int_eq]
                                  have hArgReal :
                                      __eo_typeof X = Term.UOp UserOp.Real := by
                                    apply eo_typeof_to_int_arg_real_of_ne_stuck
                                    change __eo_typeof_to_int (__eo_typeof X) ≠
                                      Term.Stuck at hApp
                                    exact hApp
                                  have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                    rw [hXMatch, hArgReal]
                                    rfl
                                  simp [hSmtArg, native_ite, native_Teq])
                                (fun hATrans hATy =>
                                  hRec
                                    (G := a) (bvs' := bvs)
                                    (by simp)
                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                          · by_cases hHeadIsInt : f = Term.UOp UserOp.is_int
                            · subst f
                              exact
                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                  UserOp.is_int a xs ts bvs hXsEnv hBvsEnv hTs
                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                  hFTrans hTy
                                  (fun h =>
                                    is_int_arg_has_smt_translation_of_has_smt_translation h)
                                  (fun X hApp => by
                                    change __eo_typeof_is_int (__eo_typeof X) ≠
                                      Term.Stuck at hApp
                                    have hArgReal :
                                        __eo_typeof X = Term.UOp UserOp.Real :=
                                      eo_typeof_is_int_arg_real_of_ne_stuck hApp
                                    rw [hArgReal]
                                    intro h
                                    cases h)
                                  (fun X Y hXY => by
                                    change __eo_typeof_is_int (__eo_typeof X) =
                                      __eo_typeof_is_int (__eo_typeof Y)
                                    rw [hXY])
                                  (fun X hXTrans hApp => by
                                    have hXMatch :
                                        __smtx_typeof (__eo_to_smt X) =
                                          __eo_to_smt_type (__eo_typeof X) :=
                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                        X hXTrans
                                    unfold RuleProofs.eo_has_smt_translation
                                    change
                                      __smtx_typeof (SmtTerm.is_int (__eo_to_smt X)) ≠
                                        SmtType.None
                                    rw [typeof_is_int_eq]
                                    have hArgReal :
                                        __eo_typeof X = Term.UOp UserOp.Real := by
                                      apply eo_typeof_is_int_arg_real_of_ne_stuck
                                      change __eo_typeof_is_int (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      exact hApp
                                    have hSmtArg :
                                        __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                      rw [hXMatch, hArgReal]
                                      rfl
                                    simp [hSmtArg, native_ite, native_Teq])
                                  (fun hATrans hATy =>
                                    hRec
                                      (G := a) (bvs' := bvs)
                                      (by simp)
                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                            · by_cases hHeadUneg :
                                f = Term.UOp UserOp.__eoo_neg_2
                              · subst f
                                exact
                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                    UserOp.__eoo_neg_2 a xs ts bvs
                                    hXsEnv hBvsEnv hTs
                                    (fun q v vs hEq =>
                                      hBinder ⟨q, v, vs, hEq⟩)
                                    hFTrans hTy
                                    (fun h =>
                                      uneg_arg_has_smt_translation_of_has_smt_translation h)
                                    (fun X hApp => by
                                      change __eo_typeof_abs (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                        hArg | hArg
                                      · rw [hArg]
                                        intro h
                                        cases h
                                      · rw [hArg]
                                        intro h
                                        cases h)
                                    (fun X Y hXY => by
                                      change __eo_typeof_abs (__eo_typeof X) =
                                        __eo_typeof_abs (__eo_typeof Y)
                                      rw [hXY])
                                    (fun X hXTrans hApp => by
                                      have hXMatch :
                                          __smtx_typeof (__eo_to_smt X) =
                                            __eo_to_smt_type (__eo_typeof X) :=
                                        TranslationProofs.eo_to_smt_typeof_matches_translation
                                          X hXTrans
                                      unfold RuleProofs.eo_has_smt_translation
                                      change
                                        __smtx_typeof
                                            (SmtTerm.uneg (__eo_to_smt X)) ≠
                                          SmtType.None
                                      rw [typeof_uneg_eq]
                                      change __eo_typeof_abs (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                        hArgInt | hArgReal
                                      · have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) =
                                              SmtType.Int := by
                                          rw [hXMatch, hArgInt]
                                          rfl
                                        simp [__smtx_typeof_arith_overload_op_1,
                                          hSmtArg]
                                      · have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) =
                                              SmtType.Real := by
                                          rw [hXMatch, hArgReal]
                                          rfl
                                        simp [__smtx_typeof_arith_overload_op_1,
                                          hSmtArg])
                                    (fun hATrans hATy =>
                                      hRec
                                        (G := a)
                                        (bvs' := bvs)
                                        (by simp)
                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                              · by_cases hHeadPow2 :
                                  f = Term.UOp UserOp.int_pow2
                                · subst f
                                  exact
                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                      UserOp.int_pow2 a xs ts bvs
                                      hXsEnv hBvsEnv hTs
                                      (fun q v vs hEq =>
                                        hBinder ⟨q, v, vs, hEq⟩)
                                      hFTrans hTy
                                      (fun h =>
                                        int_pow2_arg_has_smt_translation_of_has_smt_translation h)
                                      (fun X hApp => by
                                        change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                          Term.Stuck at hApp
                                        rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                        intro h
                                        cases h)
                                      (fun X Y hXY => by
                                        change __eo_typeof_int_pow2 (__eo_typeof X) =
                                          __eo_typeof_int_pow2 (__eo_typeof Y)
                                        rw [hXY])
                                      (fun X hXTrans hApp => by
                                        have hXMatch :
                                            __smtx_typeof (__eo_to_smt X) =
                                              __eo_to_smt_type (__eo_typeof X) :=
                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                            X hXTrans
                                        unfold RuleProofs.eo_has_smt_translation
                                        change
                                          __smtx_typeof
                                              (SmtTerm.int_pow2 (__eo_to_smt X)) ≠
                                            SmtType.None
                                        rw [typeof_int_pow2_eq]
                                        change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                          Term.Stuck at hApp
                                        have hArgInt :=
                                          eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                        have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) =
                                              SmtType.Int := by
                                          rw [hXMatch, hArgInt]
                                          rfl
                                        simp [hSmtArg, native_ite, native_Teq])
                                      (fun hATrans hATy =>
                                        hRec
                                          (G := a)
                                          (bvs' := bvs)
                                          (by simp)
                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                · by_cases hHeadLog2 :
                                    f = Term.UOp UserOp.int_log2
                                  · subst f
                                    exact
                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                        UserOp.int_log2 a xs ts bvs
                                        hXsEnv hBvsEnv hTs
                                        (fun q v vs hEq =>
                                          hBinder ⟨q, v, vs, hEq⟩)
                                        hFTrans hTy
                                        (fun h =>
                                          int_log2_arg_has_smt_translation_of_has_smt_translation h)
                                        (fun X hApp => by
                                          change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                            Term.Stuck at hApp
                                          rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                          intro h
                                          cases h)
                                        (fun X Y hXY => by
                                          change __eo_typeof_int_pow2 (__eo_typeof X) =
                                            __eo_typeof_int_pow2 (__eo_typeof Y)
                                          rw [hXY])
                                        (fun X hXTrans hApp => by
                                          have hXMatch :
                                              __smtx_typeof (__eo_to_smt X) =
                                                __eo_to_smt_type (__eo_typeof X) :=
                                            TranslationProofs.eo_to_smt_typeof_matches_translation
                                              X hXTrans
                                          unfold RuleProofs.eo_has_smt_translation
                                          change
                                            __smtx_typeof
                                                (SmtTerm.int_log2 (__eo_to_smt X)) ≠
                                              SmtType.None
                                          rw [typeof_int_log2_eq]
                                          change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                            Term.Stuck at hApp
                                          have hArgInt :=
                                            eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                          have hSmtArg :
                                              __smtx_typeof (__eo_to_smt X) =
                                                SmtType.Int := by
                                            rw [hXMatch, hArgInt]
                                            rfl
                                          simp [hSmtArg, native_ite, native_Teq])
                                        (fun hATrans hATy =>
                                          hRec
                                            (G := a)
                                            (bvs' := bvs)
                                            (by simp)
                                            hXsEnv hBvsEnv hATrans hTs hActuals
                                            hATy)
                                  · by_cases hHeadPurify :
                                      f = Term.UOp UserOp._at_purify
                                    · subst f
                                      exact
                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                          UserOp._at_purify a xs ts bvs
                                          hXsEnv hBvsEnv hTs
                                          (fun q v vs hEq =>
                                            hBinder ⟨q, v, vs, hEq⟩)
                                          hFTrans hTy
                                          (fun h =>
                                            purify_arg_has_smt_translation_of_has_smt_translation h)
                                          (fun X hApp => by
                                            change
                                              __eo_typeof__at_purify
                                                  (__eo_typeof X) ≠
                                                Term.Stuck at hApp
                                            simpa [eo_typeof_purify_eq] using hApp)
                                          (fun X Y hXY => by
                                            change
                                              __eo_typeof__at_purify
                                                  (__eo_typeof X) =
                                                __eo_typeof__at_purify
                                                  (__eo_typeof Y)
                                            rw [hXY])
                                          (fun X hXTrans hApp => by
                                            unfold RuleProofs.eo_has_smt_translation
                                            change
                                              __smtx_typeof
                                                  (SmtTerm._at_purify
                                                    (__eo_to_smt X)) ≠
                                                SmtType.None
                                            rw [__smtx_typeof.eq_13]
                                            simpa [RuleProofs.eo_has_smt_translation]
                                              using hXTrans)
                                          (fun hATrans hATy =>
                                            hRec
                                              (G := a)
                                              (bvs' := bvs)
                                              (by simp)
                                              hXsEnv hBvsEnv hATrans hTs
                                              hActuals hATy)
                                    · by_cases hHeadIntIspow2 :
                                        f = Term.UOp UserOp.int_ispow2
                                      · subst f
                                        exact
                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                            UserOp.int_ispow2 a xs ts bvs
                                            hXsEnv hBvsEnv hTs
                                            (fun q v vs hEq =>
                                              hBinder ⟨q, v, vs, hEq⟩)
                                            hFTrans hTy
                                            (fun h =>
                                              int_ispow2_arg_has_smt_translation_of_has_smt_translation h)
                                            (fun X hApp => by
                                              change
                                                __eo_typeof_int_ispow2
                                                    (__eo_typeof X) ≠
                                                  Term.Stuck at hApp
                                              rw [
                                                eo_typeof_int_ispow2_arg_int_of_ne_stuck
                                                  hApp]
                                              intro h
                                              cases h)
                                            (fun X Y hXY => by
                                              change
                                                __eo_typeof_int_ispow2
                                                    (__eo_typeof X) =
                                                  __eo_typeof_int_ispow2
                                                    (__eo_typeof Y)
                                              rw [hXY])
                                            (fun X hXTrans hApp => by
                                              have hXMatch :
                                                  __smtx_typeof (__eo_to_smt X) =
                                                    __eo_to_smt_type
                                                      (__eo_typeof X) :=
                                                TranslationProofs.eo_to_smt_typeof_matches_translation
                                                  X hXTrans
                                              unfold RuleProofs.eo_has_smt_translation
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.and
                                                      (SmtTerm.geq (__eo_to_smt X)
                                                        (SmtTerm.Numeral 0))
                                                      (SmtTerm.eq (__eo_to_smt X)
                                                        (SmtTerm.int_pow2
                                                          (SmtTerm.int_log2
                                                            (__eo_to_smt X))))) ≠
                                                  SmtType.None
                                              change
                                                __eo_typeof_int_ispow2
                                                    (__eo_typeof X) ≠
                                                  Term.Stuck at hApp
                                              have hArgInt :=
                                                eo_typeof_int_ispow2_arg_int_of_ne_stuck
                                                  hApp
                                              have hSmtArg :
                                                  __smtx_typeof (__eo_to_smt X) =
                                                    SmtType.Int := by
                                                rw [hXMatch, hArgInt]
                                                rfl
                                              rw [typeof_and_eq, typeof_geq_eq,
                                                typeof_eq_eq, typeof_int_pow2_eq,
                                                typeof_int_log2_eq, hSmtArg,
                                                __smtx_typeof.eq_2]
                                              simp [
                                                __smtx_typeof_arith_overload_op_2_ret,
                                                __smtx_typeof_eq,
                                                __smtx_typeof_guard,
                                                native_ite, native_Teq])
                                            (fun hATrans hATy =>
                                              hRec
                                                (G := a) 
                                                 (bvs' := bvs)
                                                (by simp)
                                                hXsEnv hBvsEnv hATrans hTs
                                                hActuals hATy)
                                      · by_cases hHeadIntDivByZero :
                                          f =
                                            Term.UOp UserOp._at_int_div_by_zero
                                        · subst f
                                          exact
                                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                              UserOp._at_int_div_by_zero
                                              a xs ts bvs hXsEnv hBvsEnv hTs
                                              (fun q v vs hEq =>
                                                hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans hTy
                                              (fun h =>
                                                int_div_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                              (fun X hApp => by
                                                change
                                                  __eo_typeof_int_pow2
                                                      (__eo_typeof X) ≠
                                                    Term.Stuck at hApp
                                                rw [
                                                  eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                    hApp]
                                                intro h
                                                cases h)
                                              (fun X Y hXY => by
                                                change
                                                  __eo_typeof_int_pow2
                                                      (__eo_typeof X) =
                                                    __eo_typeof_int_pow2
                                                      (__eo_typeof Y)
                                                rw [hXY])
                                              (fun X hXTrans hApp => by
                                                have hXMatch :
                                                    __smtx_typeof (__eo_to_smt X) =
                                                      __eo_to_smt_type
                                                        (__eo_typeof X) :=
                                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                                    X hXTrans
                                                unfold RuleProofs.eo_has_smt_translation
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.div (__eo_to_smt X)
                                                        (SmtTerm.Numeral 0)) ≠
                                                    SmtType.None
                                                rw [typeof_div_eq]
                                                change
                                                  __eo_typeof_int_pow2
                                                      (__eo_typeof X) ≠
                                                    Term.Stuck at hApp
                                                have hArgInt :=
                                                  eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                    hApp
                                                have hSmtArg :
                                                    __smtx_typeof (__eo_to_smt X) =
                                                      SmtType.Int := by
                                                  rw [hXMatch, hArgInt]
                                                  rfl
                                                simp [hSmtArg, __smtx_typeof.eq_2,
                                                  native_ite, native_Teq])
                                              (fun hATrans hATy =>
                                                hRec
                                                  (G := a) 
                                                   (bvs' := bvs)
                                                  (by simp)
                                                  hXsEnv hBvsEnv hATrans hTs
                                                  hActuals hATy)
                                        · by_cases hHeadModByZero :
                                            f =
                                              Term.UOp UserOp._at_mod_by_zero
                                          · subst f
                                            exact
                                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                UserOp._at_mod_by_zero
                                                a xs ts bvs hXsEnv hBvsEnv hTs
                                                (fun q v vs hEq =>
                                                  hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans hTy
                                                (fun h =>
                                                  mod_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                (fun X hApp => by
                                                  change
                                                    __eo_typeof_int_pow2
                                                        (__eo_typeof X) ≠
                                                      Term.Stuck at hApp
                                                  rw [
                                                    eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                      hApp]
                                                  intro h
                                                  cases h)
                                                (fun X Y hXY => by
                                                  change
                                                    __eo_typeof_int_pow2
                                                        (__eo_typeof X) =
                                                      __eo_typeof_int_pow2
                                                        (__eo_typeof Y)
                                                  rw [hXY])
                                                (fun X hXTrans hApp => by
                                                  have hXMatch :
                                                      __smtx_typeof (__eo_to_smt X) =
                                                        __eo_to_smt_type
                                                          (__eo_typeof X) :=
                                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                                      X hXTrans
                                                  unfold RuleProofs.eo_has_smt_translation
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.mod (__eo_to_smt X)
                                                          (SmtTerm.Numeral 0)) ≠
                                                      SmtType.None
                                                  rw [typeof_mod_eq]
                                                  change
                                                    __eo_typeof_int_pow2
                                                        (__eo_typeof X) ≠
                                                      Term.Stuck at hApp
                                                  have hArgInt :=
                                                    eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                      hApp
                                                  have hSmtArg :
                                                      __smtx_typeof (__eo_to_smt X) =
                                                        SmtType.Int := by
                                                    rw [hXMatch, hArgInt]
                                                    rfl
                                                  simp [hSmtArg,
                                                    __smtx_typeof.eq_2,
                                                    native_ite, native_Teq])
                                                (fun hATrans hATy =>
                                                  hRec
                                                    (G := a) 
                                                     (bvs' := bvs)
                                                    (by simp)
                                                    hXsEnv hBvsEnv hATrans hTs
                                                    hActuals hATy)
                                          · by_cases hHeadQDivByZero :
                                              f =
                                                Term.UOp UserOp._at_div_by_zero
                                            · subst f
                                              exact
                                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                  UserOp._at_div_by_zero
                                                  a xs ts bvs hXsEnv hBvsEnv hTs
                                                  (fun q v vs hEq =>
                                                    hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans hTy
                                                  (fun h =>
                                                    qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                  (fun X hApp => by
                                                    change
                                                      __eo_typeof__at_div_by_zero
                                                          (__eo_typeof X) ≠
                                                        Term.Stuck at hApp
                                                    rw [
                                                      eo_typeof_at_div_by_zero_arg_real_of_ne_stuck
                                                        hApp]
                                                    intro h
                                                    cases h)
                                                  (fun X Y hXY => by
                                                    change
                                                      __eo_typeof__at_div_by_zero
                                                          (__eo_typeof X) =
                                                        __eo_typeof__at_div_by_zero
                                                          (__eo_typeof Y)
                                                    rw [hXY])
                                                  (fun X hXTrans hApp => by
                                                    have hXMatch :
                                                        __smtx_typeof
                                                            (__eo_to_smt X) =
                                                          __eo_to_smt_type
                                                            (__eo_typeof X) :=
                                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                                        X hXTrans
                                                    unfold RuleProofs.eo_has_smt_translation
                                                    change
                                                      __smtx_typeof
                                                          (SmtTerm.qdiv
                                                            (__eo_to_smt X)
                                                            (SmtTerm.Rational
                                                              (native_mk_rational
                                                                0 1))) ≠
                                                        SmtType.None
                                                    change
                                                      __eo_typeof__at_div_by_zero
                                                          (__eo_typeof X) ≠
                                                        Term.Stuck at hApp
                                                    have hArgReal :=
                                                      eo_typeof_at_div_by_zero_arg_real_of_ne_stuck
                                                        hApp
                                                    have hSmtArg :
                                                        __smtx_typeof
                                                            (__eo_to_smt X) =
                                                          SmtType.Real := by
                                                      rw [hXMatch, hArgReal]
                                                      rfl
                                                    have hRatTy :
                                                        __smtx_typeof
                                                            (SmtTerm.Rational
                                                              (native_mk_rational
                                                                0 1)) =
                                                          SmtType.Real := by
                                                      unfold __smtx_typeof
                                                      rfl
                                                    rw [typeof_qdiv_eq, hSmtArg,
                                                      hRatTy]
                                                    simp [
                                                      __smtx_typeof_arith_overload_op_2_ret])
                                                  (fun hATrans hATy =>
                                                    hRec
                                                      (G := a) 
                                                      (bvs' := bvs)
                                                      (by simp)
                                                      hXsEnv hBvsEnv hATrans hTs
                                                      hActuals hATy)
                                            · by_cases hHeadBvnot :
                                                f = Term.UOp UserOp.bvnot
                                              · subst f
                                                exact
                                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                    UserOp.bvnot a xs ts bvs
                                                    hXsEnv hBvsEnv hTs
                                                    (fun q v vs hEq =>
                                                      hBinder ⟨q, v, vs, hEq⟩)
                                                    hFTrans hTy
                                                    (fun h =>
                                                      bvnot_arg_has_smt_translation_of_has_smt_translation h)
                                                    (fun X hApp => by
                                                      change
                                                        __eo_typeof_bvnot
                                                            (__eo_typeof X) ≠
                                                          Term.Stuck at hApp
                                                      rcases
                                                          eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                            hApp with
                                                        ⟨w, hArg⟩
                                                      rw [hArg]
                                                      intro h
                                                      cases h)
                                                    (fun X Y hXY => by
                                                      change
                                                        __eo_typeof_bvnot
                                                            (__eo_typeof X) =
                                                          __eo_typeof_bvnot
                                                            (__eo_typeof Y)
                                                      rw [hXY])
                                                    (fun X hXTrans hApp => by
                                                      unfold RuleProofs.eo_has_smt_translation
                                                      change
                                                        __smtx_typeof
                                                            (SmtTerm.bvnot
                                                              (__eo_to_smt X)) ≠
                                                          SmtType.None
                                                      change
                                                        __eo_typeof_bvnot
                                                            (__eo_typeof X) ≠
                                                          Term.Stuck at hApp
                                                      rcases
                                                          eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                            hApp with
                                                        ⟨w, hArgEo⟩
                                                      rcases
                                                          smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                            hXTrans hArgEo with
                                                        ⟨n, hSmtArg⟩
                                                      rw [smt_typeof_bvnot_eq, hSmtArg]
                                                      simp [__smtx_typeof_bv_op_1])
                                                    (fun hATrans hATy =>
                                                      hRec
                                                        (G := a) 
                                                        (bvs' := bvs)
                                                        (by simp)
                                                        hXsEnv hBvsEnv hATrans
                                                        hTs hActuals hATy)
                                              · by_cases hHeadBvneg :
                                                  f = Term.UOp UserOp.bvneg
                                                · subst f
                                                  exact
                                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                      UserOp.bvneg a xs ts bvs
                                                      hXsEnv hBvsEnv hTs
                                                      (fun q v vs hEq =>
                                                        hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans hTy
                                                      (fun h =>
                                                        bvneg_arg_has_smt_translation_of_has_smt_translation h)
                                                      (fun X hApp => by
                                                        change
                                                          __eo_typeof_bvnot
                                                              (__eo_typeof X) ≠
                                                            Term.Stuck at hApp
                                                        rcases
                                                            eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                              hApp with
                                                          ⟨w, hArg⟩
                                                        rw [hArg]
                                                        intro h
                                                        cases h)
                                                      (fun X Y hXY => by
                                                        change
                                                          __eo_typeof_bvnot
                                                              (__eo_typeof X) =
                                                            __eo_typeof_bvnot
                                                              (__eo_typeof Y)
                                                        rw [hXY])
                                                      (fun X hXTrans hApp => by
                                                        unfold RuleProofs.eo_has_smt_translation
                                                        change
                                                          __smtx_typeof
                                                              (SmtTerm.bvneg
                                                                (__eo_to_smt X)) ≠
                                                            SmtType.None
                                                        change
                                                          __eo_typeof_bvnot
                                                              (__eo_typeof X) ≠
                                                            Term.Stuck at hApp
                                                        rcases
                                                            eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                              hApp with
                                                          ⟨w, hArgEo⟩
                                                        rcases
                                                            smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                              hXTrans hArgEo with
                                                          ⟨n, hSmtArg⟩
                                                        rw [smt_typeof_bvneg_eq,
                                                          hSmtArg]
                                                        simp [__smtx_typeof_bv_op_1])
                                                      (fun hATrans hATy =>
                                                        hRec
                                                          (G := a) 
                                                          (bvs' := bvs)
                                                          (by simp)
                                                          hXsEnv hBvsEnv hATrans
                                                          hTs hActuals hATy)
                                                · by_cases hHeadBvnego :
                                                    f = Term.UOp UserOp.bvnego
                                                  · subst f
                                                    exact
                                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                        UserOp.bvnego a xs ts bvs
                                                        hXsEnv hBvsEnv hTs
                                                        (fun q v vs hEq =>
                                                          hBinder
                                                            ⟨q, v, vs, hEq⟩)
                                                        hFTrans hTy
                                                        (fun h =>
                                                          bvnego_arg_has_smt_translation_of_has_smt_translation h)
                                                        (fun X hApp => by
                                                          change
                                                            __eo_typeof_bvnego
                                                                (__eo_typeof X) ≠
                                                              Term.Stuck at hApp
                                                          rcases
                                                              eo_typeof_bvnego_arg_bitvec_of_ne_stuck
                                                                hApp with
                                                            ⟨w, hArg⟩
                                                          rw [hArg]
                                                          intro h
                                                          cases h)
                                                        (fun X Y hXY => by
                                                          change
                                                            __eo_typeof_bvnego
                                                                (__eo_typeof X) =
                                                              __eo_typeof_bvnego
                                                                (__eo_typeof Y)
                                                          rw [hXY])
                                                        (fun X hXTrans hApp => by
                                                          unfold RuleProofs.eo_has_smt_translation
                                                          change
                                                            __smtx_typeof
                                                                (SmtTerm.bvnego
                                                                  (__eo_to_smt X)) ≠
                                                              SmtType.None
                                                          change
                                                            __eo_typeof_bvnego
                                                                (__eo_typeof X) ≠
                                                              Term.Stuck at hApp
                                                          rcases
                                                              eo_typeof_bvnego_arg_bitvec_of_ne_stuck
                                                                hApp with
                                                            ⟨w, hArgEo⟩
                                                          rcases
                                                              smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                hXTrans hArgEo with
                                                            ⟨n, hSmtArg⟩
                                                          rw [smt_typeof_bvnego_eq,
                                                            hSmtArg]
                                                          simp [
                                                            __smtx_typeof_bv_op_1_ret])
                                                        (fun hATrans hATy =>
                                                          hRec
                                                            (G := a)
                                                            (bvs' := bvs)
                                                            (by simp)
                                                            hXsEnv hBvsEnv
                                                            hATrans hTs
                                                            hActuals hATy)
                                                  · by_cases hHeadBvsize :
                                                      f =
                                                        Term.UOp UserOp._at_bvsize
                                                    · subst f
                                                      exact
                                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                          UserOp._at_bvsize
                                                          a xs ts bvs
                                                          hXsEnv hBvsEnv hTs
                                                          (fun q v vs hEq =>
                                                            hBinder
                                                              ⟨q, v, vs, hEq⟩)
                                                          hFTrans hTy
                                                          (fun h =>
                                                            bvsize_arg_has_smt_translation_of_has_smt_translation h)
                                                          (fun X hApp => by
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) ≠
                                                                Term.Stuck at hApp
                                                            rcases
                                                                eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                  hApp with
                                                              ⟨w, hArg⟩
                                                            rw [hArg]
                                                            intro h
                                                            cases h)
                                                          (fun X Y hXY => by
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) =
                                                                __eo_typeof__at_bvsize
                                                                  (__eo_typeof Y)
                                                            rw [hXY])
                                                          (fun X hXTrans hApp => by
                                                            unfold RuleProofs.eo_has_smt_translation
                                                            change
                                                              __smtx_typeof
                                                                  (native_ite
                                                                    (native_zleq 0
                                                                      (__eo_to_smt_bv_size
                                                                        (__smtx_typeof
                                                                          (__eo_to_smt X))))
                                                                    (SmtTerm._at_purify
                                                                      (SmtTerm.Numeral
                                                                        (__eo_to_smt_bv_size
                                                                          (__smtx_typeof
                                                                            (__eo_to_smt X)))))
                                                                    SmtTerm.None) ≠
                                                                SmtType.None
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) ≠
                                                                Term.Stuck at hApp
                                                            rcases
                                                                eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                  hApp with
                                                              ⟨w, hArgEo⟩
                                                            rcases
                                                                smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                  hXTrans hArgEo with
                                                              ⟨n, hSmtArg⟩
                                                            rw [hSmtArg]
                                                            simp [__eo_to_smt_bv_size,
                                                              __smtx_typeof.eq_13,
                                                              __smtx_typeof.eq_2,
                                                              native_ite, native_zleq,
                                                              SmtEval.native_zleq,
                                                              Smtm.native_nat_to_int])
                                                          (fun hATrans hATy =>
                                                            hRec
                                                              (G := a)
                                                              (bvs' := bvs)
                                                              (by simp)
                                                              hXsEnv hBvsEnv
                                                              hATrans hTs
                                                              hActuals hATy)
                                                    · by_cases hHeadBvredand :
                                                        f =
                                                          Term.UOp UserOp.bvredand
                                                      · subst f
                                                        exact
                                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                            UserOp.bvredand
                                                            a xs ts bvs
                                                            hXsEnv hBvsEnv hTs
                                                            (fun q v vs hEq =>
                                                              hBinder
                                                                ⟨q, v, vs, hEq⟩)
                                                            hFTrans hTy
                                                            (fun h =>
                                                              bvredand_arg_has_smt_translation_of_has_smt_translation h)
                                                            (fun X hApp => by
                                                              change
                                                                __eo_typeof_bvredand
                                                                    (__eo_typeof X) ≠
                                                                  Term.Stuck at hApp
                                                              rcases
                                                                  eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                    hApp with
                                                                ⟨w, hArg⟩
                                                              rw [hArg]
                                                              intro h
                                                              cases h)
                                                            (fun X Y hXY => by
                                                              change
                                                                __eo_typeof_bvredand
                                                                    (__eo_typeof X) =
                                                                  __eo_typeof_bvredand
                                                                    (__eo_typeof Y)
                                                              rw [hXY])
                                                            (fun X hXTrans hApp => by
                                                              unfold RuleProofs.eo_has_smt_translation
                                                              change
                                                                __smtx_typeof
                                                                    (SmtTerm.bvcomp
                                                                      (__eo_to_smt X)
                                                                      (SmtTerm.bvnot
                                                                        (SmtTerm.Binary
                                                                          (__eo_to_smt_bv_size
                                                                            (__smtx_typeof
                                                                              (__eo_to_smt X)))
                                                                          0))) ≠
                                                                  SmtType.None
                                                              change
                                                                __eo_typeof_bvredand
                                                                    (__eo_typeof X) ≠
                                                                  Term.Stuck at hApp
                                                              rcases
                                                                  eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                    hApp with
                                                                ⟨w, hArgEo⟩
                                                              rcases
                                                                  smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                    hXTrans hArgEo with
                                                                ⟨n, hSmtArg⟩
                                                              rw [smt_typeof_bvcomp_eq,
                                                                hSmtArg,
                                                                smt_typeof_bvnot_eq]
                                                              simp [__eo_to_smt_bv_size,
                                                                smt_typeof_binary_nat_to_int_zero,
                                                                __smtx_typeof_bv_op_1,
                                                                __smtx_typeof_bv_op_2_ret,
                                                                native_ite,
                                                                native_nateq,
                                                                Smtm.native_nateq])
                                                            (fun hATrans hATy =>
                                                              hRec
                                                                (G := a)
                                                                (bvs' := bvs)
                                                                (by simp)
                                                                hXsEnv hBvsEnv
                                                                hATrans hTs
                                                                hActuals hATy)
                                                      · by_cases hHeadBvredor :
                                                          f =
                                                            Term.UOp UserOp.bvredor
                                                        · subst f
                                                          exact
                                                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                              UserOp.bvredor
                                                              a xs ts bvs
                                                              hXsEnv hBvsEnv hTs
                                                              (fun q v vs hEq =>
                                                                hBinder
                                                                  ⟨q, v, vs, hEq⟩)
                                                              hFTrans hTy
                                                              (fun h =>
                                                                bvredor_arg_has_smt_translation_of_has_smt_translation h)
                                                              (fun X hApp => by
                                                                change
                                                                  __eo_typeof_bvredand
                                                                      (__eo_typeof X) ≠
                                                                    Term.Stuck at hApp
                                                                rcases
                                                                    eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                      hApp with
                                                                  ⟨w, hArg⟩
                                                                rw [hArg]
                                                                intro h
                                                                cases h)
                                                              (fun X Y hXY => by
                                                                change
                                                                  __eo_typeof_bvredand
                                                                      (__eo_typeof X) =
                                                                    __eo_typeof_bvredand
                                                                      (__eo_typeof Y)
                                                                rw [hXY])
                                                              (fun X hXTrans hApp => by
                                                                unfold RuleProofs.eo_has_smt_translation
                                                                change
                                                                  __smtx_typeof
                                                                      (SmtTerm.bvnot
                                                                        (SmtTerm.bvcomp
                                                                          (__eo_to_smt X)
                                                                          (SmtTerm.Binary
                                                                            (__eo_to_smt_bv_size
                                                                              (__smtx_typeof
                                                                                (__eo_to_smt X)))
                                                                            0))) ≠
                                                                    SmtType.None
                                                                change
                                                                  __eo_typeof_bvredand
                                                                      (__eo_typeof X) ≠
                                                                    Term.Stuck at hApp
                                                                rcases
                                                                    eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                      hApp with
                                                                  ⟨w, hArgEo⟩
                                                                rcases
                                                                    smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                      hXTrans hArgEo with
                                                                  ⟨n, hSmtArg⟩
                                                                rw [smt_typeof_bvnot_eq,
                                                                  smt_typeof_bvcomp_eq,
                                                                  hSmtArg]
                                                                simp [
                                                                  __eo_to_smt_bv_size,
                                                                  smt_typeof_binary_nat_to_int_zero,
                                                                  __smtx_typeof_bv_op_1,
                                                                  __smtx_typeof_bv_op_2_ret,
                                                                  native_ite,
                                                                  native_nateq,
                                                                  Smtm.native_nateq])
                                                              (fun hATrans hATy =>
                                                                hRec
                                                                  (G := a)
                                                                  (bvs' := bvs)
                                                                  (by simp)
                                                                  hXsEnv hBvsEnv
                                                                  hATrans hTs
                                                                  hActuals hATy)
                                                        · by_cases hHeadStrLen :
                                                            f =
                                                              Term.UOp UserOp.str_len
                                                          · subst f
                                                            exact
                                                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                UserOp.str_len
                                                                a xs ts bvs
                                                                hXsEnv hBvsEnv hTs
                                                                (fun q v vs hEq =>
                                                                  hBinder
                                                                    ⟨q, v, vs,
                                                                      hEq⟩)
                                                                hFTrans hTy
                                                                (fun h =>
                                                                  str_len_arg_has_smt_translation_of_has_smt_translation h)
                                                                (fun X hApp => by
                                                                  change
                                                                    __eo_typeof_str_len
                                                                        (__eo_typeof X) ≠
                                                                      Term.Stuck at hApp
                                                                  rcases
                                                                      eo_typeof_str_len_arg_seq_of_ne_stuck
                                                                        hApp with
                                                                    ⟨V, hArg⟩
                                                                  rw [hArg]
                                                                  intro h
                                                                  cases h)
                                                                (fun X Y hXY => by
                                                                  change
                                                                    __eo_typeof_str_len
                                                                        (__eo_typeof X) =
                                                                      __eo_typeof_str_len
                                                                        (__eo_typeof Y)
                                                                  rw [hXY])
                                                                (fun X hXTrans hApp => by
                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                  change
                                                                    __smtx_typeof
                                                                        (SmtTerm.str_len
                                                                          (__eo_to_smt X)) ≠
                                                                      SmtType.None
                                                                  change
                                                                    __eo_typeof_str_len
                                                                        (__eo_typeof X) ≠
                                                                      Term.Stuck at hApp
                                                                  rcases
                                                                      eo_typeof_str_len_arg_seq_of_ne_stuck
                                                                        hApp with
                                                                    ⟨V, hArgEo⟩
                                                                  rcases
                                                                      smt_typeof_eo_to_smt_seq_of_typeof_seq
                                                                        hXTrans
                                                                        hArgEo with
                                                                    ⟨T, hSmtArg⟩
                                                                  rw [typeof_str_len_eq,
                                                                    hSmtArg]
                                                                  simp [
                                                                    __smtx_typeof_seq_op_1_ret])
                                                                (fun hATrans hATy =>
                                                                  hRec
                                                                    (G := a)
                                                                    (bvs' := bvs)
                                                                    (by simp)
                                                                    hXsEnv hBvsEnv
                                                                    hATrans hTs
                                                                    hActuals hATy)
                                                          · by_cases hHeadStrRev :
                                                              f =
                                                                Term.UOp
                                                                  UserOp.str_rev
                                                            · subst f
                                                              exact
                                                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                  UserOp.str_rev
                                                                  a xs ts bvs
                                                                  hXsEnv hBvsEnv hTs
                                                                  (fun q v vs hEq =>
                                                                    hBinder
                                                                      ⟨q, v, vs,
                                                                        hEq⟩)
                                                                  hFTrans hTy
                                                                  (fun h =>
                                                                    str_rev_arg_has_smt_translation_of_has_smt_translation h)
                                                                  (fun X hApp => by
                                                                    change
                                                                      __eo_typeof_str_rev
                                                                          (__eo_typeof X) ≠
                                                                        Term.Stuck at hApp
                                                                    rcases
                                                                        eo_typeof_str_rev_arg_seq_of_ne_stuck
                                                                          hApp with
                                                                      ⟨V, hArg⟩
                                                                    rw [hArg]
                                                                    intro h
                                                                    cases h)
                                                                  (fun X Y hXY => by
                                                                    change
                                                                      __eo_typeof_str_rev
                                                                          (__eo_typeof X) =
                                                                        __eo_typeof_str_rev
                                                                          (__eo_typeof Y)
                                                                    rw [hXY])
                                                                  (fun X hXTrans hApp => by
                                                                    unfold RuleProofs.eo_has_smt_translation
                                                                    change
                                                                      __smtx_typeof
                                                                          (SmtTerm.str_rev
                                                                            (__eo_to_smt X)) ≠
                                                                        SmtType.None
                                                                    change
                                                                      __eo_typeof_str_rev
                                                                          (__eo_typeof X) ≠
                                                                        Term.Stuck at hApp
                                                                    rcases
                                                                        eo_typeof_str_rev_arg_seq_of_ne_stuck
                                                                          hApp with
                                                                      ⟨V, hArgEo⟩
                                                                    rcases
                                                                        smt_typeof_eo_to_smt_seq_of_typeof_seq
                                                                          hXTrans
                                                                          hArgEo with
                                                                      ⟨T, hSmtArg⟩
                                                                    rw [typeof_str_rev_eq,
                                                                      hSmtArg]
                                                                    simp [
                                                                      __smtx_typeof_seq_op_1])
                                                                  (fun hATrans hATy =>
                                                                    hRec
                                                                      (G := a)
                                                                      (bvs' := bvs)
                                                                      (by simp)
                                                                      hXsEnv
                                                                      hBvsEnv
                                                                      hATrans hTs
                                                                      hActuals
                                                                      hATy)
                                                            · by_cases hHeadStrToInt :
                                                                f =
                                                                  Term.UOp
                                                                    UserOp.str_to_int
                                                              · subst f
                                                                exact
                                                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                    UserOp.str_to_int
                                                                    a xs ts bvs
                                                                    hXsEnv hBvsEnv
                                                                    hTs
                                                                    (fun q v vs hEq =>
                                                                      hBinder
                                                                        ⟨q, v, vs,
                                                                          hEq⟩)
                                                                    hFTrans hTy
                                                                    (fun h =>
                                                                      str_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                    (fun X hApp => by
                                                                      change
                                                                        __eo_typeof_str_to_code
                                                                            (__eo_typeof X) ≠
                                                                          Term.Stuck at hApp
                                                                      rw [
                                                                        eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                          hApp]
                                                                      intro h
                                                                      cases h)
                                                                    (fun X Y hXY => by
                                                                      change
                                                                        __eo_typeof_str_to_code
                                                                            (__eo_typeof X) =
                                                                          __eo_typeof_str_to_code
                                                                            (__eo_typeof Y)
                                                                      rw [hXY])
                                                                    (fun X hXTrans hApp => by
                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                      change
                                                                        __smtx_typeof
                                                                            (SmtTerm.str_to_int
                                                                              (__eo_to_smt X)) ≠
                                                                          SmtType.None
                                                                      change
                                                                        __eo_typeof_str_to_code
                                                                            (__eo_typeof X) ≠
                                                                          Term.Stuck at hApp
                                                                      have hArgEo :=
                                                                        eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                          hApp
                                                                      have hSmtArg :=
                                                                        smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                          hXTrans
                                                                          hArgEo
                                                                      rw [typeof_str_to_int_eq,
                                                                        hSmtArg]
                                                                      simp [native_ite,
                                                                        native_Teq])
                                                                    (fun hATrans hATy =>
                                                                      hRec
                                                                        (G := a)
                                                                        (bvs' := bvs)
                                                                        (by simp)
                                                                        hXsEnv
                                                                        hBvsEnv
                                                                        hATrans hTs
                                                                        hActuals
                                                                        hATy)
                                                              · by_cases hHeadStrToRe :
                                                                  f =
                                                                    Term.UOp
                                                                      UserOp.str_to_re
                                                                · subst f
                                                                  exact
                                                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                      UserOp.str_to_re
                                                                      a xs ts bvs
                                                                      hXsEnv
                                                                      hBvsEnv hTs
                                                                      (fun q v vs hEq =>
                                                                        hBinder
                                                                          ⟨q, v, vs,
                                                                            hEq⟩)
                                                                      hFTrans hTy
                                                                      (fun h =>
                                                                        str_to_re_arg_has_smt_translation_of_has_smt_translation h)
                                                                      (fun X hApp => by
                                                                        change
                                                                          __eo_typeof_str_to_re
                                                                              (__eo_typeof X) ≠
                                                                            Term.Stuck at hApp
                                                                        rw [
                                                                          eo_typeof_str_to_re_arg_seq_char_of_ne_stuck
                                                                            hApp]
                                                                        intro h
                                                                        cases h)
                                                                      (fun X Y hXY => by
                                                                        change
                                                                          __eo_typeof_str_to_re
                                                                              (__eo_typeof X) =
                                                                            __eo_typeof_str_to_re
                                                                              (__eo_typeof Y)
                                                                        rw [hXY])
                                                                      (fun X hXTrans hApp => by
                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                        change
                                                                          __smtx_typeof
                                                                              (SmtTerm.str_to_re
                                                                                (__eo_to_smt X)) ≠
                                                                            SmtType.None
                                                                        change
                                                                          __eo_typeof_str_to_re
                                                                              (__eo_typeof X) ≠
                                                                            Term.Stuck at hApp
                                                                        have hArgEo :=
                                                                          eo_typeof_str_to_re_arg_seq_char_of_ne_stuck
                                                                            hApp
                                                                        have hSmtArg :=
                                                                          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                            hXTrans
                                                                            hArgEo
                                                                        rw [typeof_str_to_re_eq,
                                                                          hSmtArg]
                                                                        simp [native_ite,
                                                                          native_Teq])
                                                                      (fun hATrans hATy =>
                                                                        hRec
                                                                          (G := a)
                                                                          (bvs' := bvs)
                                                                          (by simp)
                                                                          hXsEnv
                                                                          hBvsEnv
                                                                          hATrans
                                                                          hTs
                                                                          hActuals
                                                                          hATy)
                                                                · by_cases hHeadReMult :
                                                                    f =
                                                                      Term.UOp
                                                                        UserOp.re_mult
                                                                  · subst f
                                                                    exact
                                                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                        UserOp.re_mult
                                                                        a xs ts bvs
                                                                        hXsEnv
                                                                        hBvsEnv hTs
                                                                        (fun q v vs hEq =>
                                                                          hBinder
                                                                            ⟨q, v,
                                                                              vs,
                                                                              hEq⟩)
                                                                        hFTrans hTy
                                                                        (fun h =>
                                                                          re_mult_arg_has_smt_translation_of_has_smt_translation h)
                                                                        (fun X hApp => by
                                                                          change
                                                                            __eo_typeof_re_mult
                                                                                (__eo_typeof X) ≠
                                                                              Term.Stuck at hApp
                                                                          rw [
                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                              hApp]
                                                                          intro h
                                                                          cases h)
                                                                        (fun X Y hXY => by
                                                                          change
                                                                            __eo_typeof_re_mult
                                                                                (__eo_typeof X) =
                                                                              __eo_typeof_re_mult
                                                                                (__eo_typeof Y)
                                                                          rw [hXY])
                                                                        (fun X hXTrans hApp => by
                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                          change
                                                                            __smtx_typeof
                                                                                (SmtTerm.re_mult
                                                                                  (__eo_to_smt X)) ≠
                                                                              SmtType.None
                                                                          change
                                                                            __eo_typeof_re_mult
                                                                                (__eo_typeof X) ≠
                                                                              Term.Stuck at hApp
                                                                          have hArgEo :=
                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                              hApp
                                                                          have hSmtArg :=
                                                                            smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                              hXTrans
                                                                              hArgEo
                                                                          rw [typeof_re_mult_eq,
                                                                            hSmtArg]
                                                                          simp [
                                                                            native_ite,
                                                                            native_Teq])
                                                                        (fun hATrans hATy =>
                                                                          hRec
                                                                            (G := a)
                                                                            (bvs' := bvs)
                                                                            (by simp)
                                                                            hXsEnv
                                                                            hBvsEnv
                                                                            hATrans
                                                                            hTs
                                                                            hActuals
                                                                            hATy)
                                                                  · by_cases hHeadStrToLower :
                                                                      f =
                                                                        Term.UOp
                                                                          UserOp.str_to_lower
                                                                    · subst f
                                                                      exact
                                                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                          UserOp.str_to_lower
                                                                          a xs ts
                                                                          bvs
                                                                          hXsEnv
                                                                          hBvsEnv
                                                                          hTs
                                                                          (fun q v vs hEq =>
                                                                            hBinder
                                                                              ⟨q, v,
                                                                                vs,
                                                                                hEq⟩)
                                                                          hFTrans
                                                                          hTy
                                                                          (fun h =>
                                                                            str_to_lower_arg_has_smt_translation_of_has_smt_translation h)
                                                                          (fun X hApp => by
                                                                            change
                                                                              __eo_typeof_str_to_lower
                                                                                  (__eo_typeof X) ≠
                                                                                Term.Stuck at hApp
                                                                            rw [
                                                                              eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                hApp]
                                                                            intro h
                                                                            cases h)
                                                                          (fun X Y hXY => by
                                                                            change
                                                                              __eo_typeof_str_to_lower
                                                                                  (__eo_typeof X) =
                                                                                __eo_typeof_str_to_lower
                                                                                  (__eo_typeof Y)
                                                                            rw [hXY])
                                                                          (fun X hXTrans hApp => by
                                                                            unfold RuleProofs.eo_has_smt_translation
                                                                            change
                                                                              __smtx_typeof
                                                                                  (SmtTerm.str_to_lower
                                                                                    (__eo_to_smt X)) ≠
                                                                                SmtType.None
                                                                            change
                                                                              __eo_typeof_str_to_lower
                                                                                  (__eo_typeof X) ≠
                                                                                Term.Stuck at hApp
                                                                            have hArgEo :=
                                                                              eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                hApp
                                                                            have hSmtArg :=
                                                                              smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                hXTrans
                                                                                hArgEo
                                                                            rw [
                                                                              typeof_str_to_lower_eq,
                                                                              hSmtArg]
                                                                            simp [
                                                                              native_ite,
                                                                              native_Teq])
                                                                          (fun hATrans hATy =>
                                                                            hRec
                                                                              (G := a)
                                                                              (bvs' := bvs)
                                                                              (by simp)
                                                                              hXsEnv
                                                                              hBvsEnv
                                                                              hATrans
                                                                              hTs
                                                                              hActuals
                                                                              hATy)
                                                                    · by_cases hHeadStrToUpper :
                                                                        f =
                                                                          Term.UOp
                                                                            UserOp.str_to_upper
                                                                      · subst f
                                                                        exact
                                                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                            UserOp.str_to_upper
                                                                            a xs ts
                                                                            bvs
                                                                            hXsEnv
                                                                            hBvsEnv
                                                                            hTs
                                                                            (fun q v vs hEq =>
                                                                              hBinder
                                                                                ⟨q, v,
                                                                                  vs,
                                                                                  hEq⟩)
                                                                            hFTrans
                                                                            hTy
                                                                            (fun h =>
                                                                              str_to_upper_arg_has_smt_translation_of_has_smt_translation h)
                                                                            (fun X hApp => by
                                                                              change
                                                                                __eo_typeof_str_to_lower
                                                                                    (__eo_typeof X) ≠
                                                                                  Term.Stuck at hApp
                                                                              rw [
                                                                                eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                  hApp]
                                                                              intro h
                                                                              cases h)
                                                                            (fun X Y hXY => by
                                                                              change
                                                                                __eo_typeof_str_to_lower
                                                                                    (__eo_typeof X) =
                                                                                  __eo_typeof_str_to_lower
                                                                                    (__eo_typeof Y)
                                                                              rw [hXY])
                                                                            (fun X hXTrans hApp => by
                                                                              unfold RuleProofs.eo_has_smt_translation
                                                                              change
                                                                                __smtx_typeof
                                                                                    (SmtTerm.str_to_upper
                                                                                      (__eo_to_smt X)) ≠
                                                                                  SmtType.None
                                                                              change
                                                                                __eo_typeof_str_to_lower
                                                                                    (__eo_typeof X) ≠
                                                                                  Term.Stuck at hApp
                                                                              have hArgEo :=
                                                                                eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                  hApp
                                                                              have hSmtArg :=
                                                                                smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                  hXTrans
                                                                                  hArgEo
                                                                              rw [
                                                                                typeof_str_to_upper_eq,
                                                                                hSmtArg]
                                                                              simp [
                                                                                native_ite,
                                                                                native_Teq])
                                                                            (fun hATrans hATy =>
                                                                              hRec
                                                                                (G := a)
                                                                                (bvs' := bvs)
                                                                                (by simp)
                                                                                hXsEnv
                                                                                hBvsEnv
                                                                                hATrans
                                                                                hTs
                                                                                hActuals
                                                                                hATy)
                                                                      · by_cases hHeadStrToCode :
                                                                          f =
                                                                            Term.UOp
                                                                              UserOp.str_to_code
                                                                        · subst f
                                                                          exact
                                                                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                              UserOp.str_to_code
                                                                              a xs ts
                                                                              bvs
                                                                              hXsEnv
                                                                              hBvsEnv
                                                                              hTs
                                                                              (fun q v vs hEq =>
                                                                                hBinder
                                                                                  ⟨q, v,
                                                                                    vs,
                                                                                    hEq⟩)
                                                                              hFTrans
                                                                              hTy
                                                                              (fun h =>
                                                                                str_to_code_arg_has_smt_translation_of_has_smt_translation h)
                                                                              (fun X hApp => by
                                                                                change
                                                                                  __eo_typeof_str_to_code
                                                                                      (__eo_typeof X) ≠
                                                                                    Term.Stuck at hApp
                                                                                rw [
                                                                                  eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                                    hApp]
                                                                                intro h
                                                                                cases h)
                                                                              (fun X Y hXY => by
                                                                                change
                                                                                  __eo_typeof_str_to_code
                                                                                      (__eo_typeof X) =
                                                                                    __eo_typeof_str_to_code
                                                                                      (__eo_typeof Y)
                                                                                rw [hXY])
                                                                              (fun X hXTrans hApp => by
                                                                                unfold RuleProofs.eo_has_smt_translation
                                                                                change
                                                                                  __smtx_typeof
                                                                                      (SmtTerm.str_to_code
                                                                                        (__eo_to_smt X)) ≠
                                                                                    SmtType.None
                                                                                change
                                                                                  __eo_typeof_str_to_code
                                                                                      (__eo_typeof X) ≠
                                                                                    Term.Stuck at hApp
                                                                                have hArgEo :=
                                                                                  eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                                    hApp
                                                                                have hSmtArg :=
                                                                                  smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                    hXTrans
                                                                                    hArgEo
                                                                                rw [
                                                                                  typeof_str_to_code_eq,
                                                                                  hSmtArg]
                                                                                simp [
                                                                                  native_ite,
                                                                                  native_Teq])
                                                                              (fun hATrans hATy =>
                                                                                hRec
                                                                                  (G := a)
                                                                                  (bvs' := bvs)
                                                                                  (by simp)
                                                                                  hXsEnv
                                                                                  hBvsEnv
                                                                                  hATrans
                                                                                  hTs
                                                                                  hActuals
                                                                                  hATy)
                                                                        · by_cases hHeadStrFromCode :
                                                                            f =
                                                                              Term.UOp
                                                                                UserOp.str_from_code
                                                                          · subst f
                                                                            exact
                                                                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                UserOp.str_from_code
                                                                                a xs ts
                                                                                bvs
                                                                                hXsEnv
                                                                                hBvsEnv
                                                                                hTs
                                                                                (fun q v vs hEq =>
                                                                                  hBinder
                                                                                    ⟨q, v,
                                                                                      vs,
                                                                                      hEq⟩)
                                                                                hFTrans
                                                                                hTy
                                                                                (fun h =>
                                                                                  str_from_code_arg_has_smt_translation_of_has_smt_translation h)
                                                                                (fun X hApp => by
                                                                                  change
                                                                                    __eo_typeof_str_from_code
                                                                                        (__eo_typeof X) ≠
                                                                                      Term.Stuck at hApp
                                                                                  rw [
                                                                                    eo_typeof_str_from_code_arg_int_of_ne_stuck
                                                                                      hApp]
                                                                                  intro h
                                                                                  cases h)
                                                                                (fun X Y hXY => by
                                                                                  change
                                                                                    __eo_typeof_str_from_code
                                                                                        (__eo_typeof X) =
                                                                                      __eo_typeof_str_from_code
                                                                                        (__eo_typeof Y)
                                                                                  rw [hXY])
                                                                                (fun X hXTrans hApp => by
                                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                                  change
                                                                                    __smtx_typeof
                                                                                        (SmtTerm.str_from_code
                                                                                          (__eo_to_smt X)) ≠
                                                                                      SmtType.None
                                                                                  change
                                                                                    __eo_typeof_str_from_code
                                                                                        (__eo_typeof X) ≠
                                                                                      Term.Stuck at hApp
                                                                                  have hArgEo :=
                                                                                    eo_typeof_str_from_code_arg_int_of_ne_stuck
                                                                                      hApp
                                                                                  have hSmtArg :=
                                                                                    smt_typeof_eo_to_smt_int_of_typeof_int
                                                                                      hXTrans
                                                                                      hArgEo
                                                                                  rw [
                                                                                    typeof_str_from_code_eq,
                                                                                    hSmtArg]
                                                                                  simp [
                                                                                    native_ite,
                                                                                    native_Teq])
                                                                                (fun hATrans hATy =>
                                                                                  hRec
                                                                                    (G := a)
                                                                                    (bvs' := bvs)
                                                                                    (by simp)
                                                                                    hXsEnv
                                                                                    hBvsEnv
                                                                                    hATrans
                                                                                    hTs
                                                                                    hActuals
                                                                                    hATy)
                                                                          · by_cases hHeadStrIsDigit :
                                                                              f =
                                                                                Term.UOp
                                                                                  UserOp.str_is_digit
                                                                            · subst f
                                                                              exact
                                                                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                  UserOp.str_is_digit
                                                                                  a xs ts
                                                                                  bvs
                                                                                  hXsEnv
                                                                                  hBvsEnv
                                                                                  hTs
                                                                                  (fun q v vs hEq =>
                                                                                    hBinder
                                                                                      ⟨q,
                                                                                        v,
                                                                                        vs,
                                                                                        hEq⟩)
                                                                                  hFTrans
                                                                                  hTy
                                                                                  (fun h =>
                                                                                    str_is_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                                  (fun X hApp => by
                                                                                    change
                                                                                      __eo_typeof_str_is_digit
                                                                                          (__eo_typeof X) ≠
                                                                                        Term.Stuck at hApp
                                                                                    rw [
                                                                                      eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck
                                                                                        hApp]
                                                                                    intro h
                                                                                    cases h)
                                                                                  (fun X Y hXY => by
                                                                                    change
                                                                                      __eo_typeof_str_is_digit
                                                                                          (__eo_typeof X) =
                                                                                        __eo_typeof_str_is_digit
                                                                                          (__eo_typeof Y)
                                                                                    rw [hXY])
                                                                                  (fun X hXTrans hApp => by
                                                                                    unfold RuleProofs.eo_has_smt_translation
                                                                                    change
                                                                                      __smtx_typeof
                                                                                          (SmtTerm.str_is_digit
                                                                                            (__eo_to_smt X)) ≠
                                                                                        SmtType.None
                                                                                    change
                                                                                      __eo_typeof_str_is_digit
                                                                                          (__eo_typeof X) ≠
                                                                                        Term.Stuck at hApp
                                                                                    have hArgEo :=
                                                                                      eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck
                                                                                        hApp
                                                                                    have hSmtArg :=
                                                                                      smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                        hXTrans
                                                                                        hArgEo
                                                                                    rw [
                                                                                      typeof_str_is_digit_eq,
                                                                                      hSmtArg]
                                                                                    simp [
                                                                                      native_ite,
                                                                                      native_Teq])
                                                                                  (fun hATrans hATy =>
                                                                                    hRec
                                                                                      (G := a)
                                                                                      (bvs' := bvs)
                                                                                      (by simp)
                                                                                      hXsEnv
                                                                                      hBvsEnv
                                                                                      hATrans
                                                                                      hTs
                                                                                      hActuals
                                                                                      hATy)
                                                                            · by_cases hHeadStrFromInt :
                                                                                f =
                                                                                  Term.UOp
                                                                                    UserOp.str_from_int
                                                                              · subst f
                                                                                exact
                                                                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                    UserOp.str_from_int
                                                                                    a xs ts
                                                                                    bvs
                                                                                    hXsEnv
                                                                                    hBvsEnv
                                                                                    hTs
                                                                                    (fun q v vs hEq =>
                                                                                      hBinder
                                                                                        ⟨q,
                                                                                          v,
                                                                                          vs,
                                                                                          hEq⟩)
                                                                                    hFTrans
                                                                                    hTy
                                                                                    (fun h =>
                                                                                      str_from_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                                    (fun X hApp => by
                                                                                      change
                                                                                        __eo_typeof_str_from_code
                                                                                            (__eo_typeof X) ≠
                                                                                          Term.Stuck at hApp
                                                                                      rw [
                                                                                        eo_typeof_str_from_code_arg_int_of_ne_stuck
                                                                                          hApp]
                                                                                      intro h
                                                                                      cases h)
                                                                                    (fun X Y hXY => by
                                                                                      change
                                                                                        __eo_typeof_str_from_code
                                                                                            (__eo_typeof X) =
                                                                                          __eo_typeof_str_from_code
                                                                                            (__eo_typeof Y)
                                                                                      rw [hXY])
                                                                                    (fun X hXTrans hApp => by
                                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                                      change
                                                                                        __smtx_typeof
                                                                                            (SmtTerm.str_from_int
                                                                                              (__eo_to_smt X)) ≠
                                                                                          SmtType.None
                                                                                      change
                                                                                        __eo_typeof_str_from_code
                                                                                            (__eo_typeof X) ≠
                                                                                          Term.Stuck at hApp
                                                                                      have hArgEo :=
                                                                                        eo_typeof_str_from_code_arg_int_of_ne_stuck
                                                                                          hApp
                                                                                      have hSmtArg :=
                                                                                        smt_typeof_eo_to_smt_int_of_typeof_int
                                                                                          hXTrans
                                                                                          hArgEo
                                                                                      rw [
                                                                                        typeof_str_from_int_eq,
                                                                                        hSmtArg]
                                                                                      simp [
                                                                                        native_ite,
                                                                                        native_Teq])
                                                                                    (fun hATrans hATy =>
                                                                                      hRec
                                                                                        (G := a)
                                                                                        (bvs' := bvs)
                                                                                        (by simp)
                                                                                        hXsEnv
                                                                                        hBvsEnv
                                                                                        hATrans
                                                                                        hTs
                                                                                        hActuals
                                                                                        hATy)
                                                                              · by_cases hHeadRePlus :
                                                                                  f =
                                                                                    Term.UOp
                                                                                      UserOp.re_plus
                                                                                · subst f
                                                                                  exact
                                                                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                      UserOp.re_plus
                                                                                      a xs ts
                                                                                      bvs
                                                                                      hXsEnv
                                                                                      hBvsEnv
                                                                                      hTs
                                                                                      (fun q v vs hEq =>
                                                                                        hBinder
                                                                                          ⟨q,
                                                                                            v,
                                                                                            vs,
                                                                                            hEq⟩)
                                                                                      hFTrans
                                                                                      hTy
                                                                                      (fun h =>
                                                                                        re_plus_arg_has_smt_translation_of_has_smt_translation h)
                                                                                      (fun X hApp => by
                                                                                        change
                                                                                          __eo_typeof_re_mult
                                                                                              (__eo_typeof X) ≠
                                                                                            Term.Stuck at hApp
                                                                                        rw [
                                                                                          eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                                            hApp]
                                                                                        intro h
                                                                                        cases h)
                                                                                      (fun X Y hXY => by
                                                                                        change
                                                                                          __eo_typeof_re_mult
                                                                                              (__eo_typeof X) =
                                                                                            __eo_typeof_re_mult
                                                                                              (__eo_typeof Y)
                                                                                        rw [hXY])
                                                                                      (fun X hXTrans hApp => by
                                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                                        change
                                                                                          __smtx_typeof
                                                                                              (SmtTerm.re_plus
                                                                                                (__eo_to_smt X)) ≠
                                                                                            SmtType.None
                                                                                        change
                                                                                          __eo_typeof_re_mult
                                                                                              (__eo_typeof X) ≠
                                                                                            Term.Stuck at hApp
                                                                                        have hArgEo :=
                                                                                          eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                                            hApp
                                                                                        have hSmtArg :=
                                                                                          smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                                            hXTrans
                                                                                            hArgEo
                                                                                        rw [
                                                                                          typeof_re_plus_eq,
                                                                                          hSmtArg]
                                                                                        simp [
                                                                                          native_ite,
                                                                                          native_Teq])
                                                                                      (fun hATrans hATy =>
                                                                                        hRec
                                                                                          (G := a)
                                                                                          (bvs' := bvs)
                                                                                          (by simp)
                                                                                          hXsEnv
                                                                                          hBvsEnv
                                                                                          hATrans
                                                                                          hTs
                                                                                          hActuals
                                                                                          hATy)
                                                                                · by_cases hHeadReOpt :
                                                                                    f =
                                                                                      Term.UOp
                                                                                        UserOp.re_opt
                                                                                  · subst f
                                                                                    exact
                                                                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                        UserOp.re_opt
                                                                                        a xs ts
                                                                                        bvs
                                                                                        hXsEnv
                                                                                        hBvsEnv
                                                                                        hTs
                                                                                        (fun q v vs hEq =>
                                                                                          hBinder
                                                                                            ⟨q,
                                                                                              v,
                                                                                              vs,
                                                                                              hEq⟩)
                                                                                        hFTrans
                                                                                        hTy
                                                                                        (fun h =>
                                                                                          re_opt_arg_has_smt_translation_of_has_smt_translation h)
                                                                                        (fun X hApp => by
                                                                                          change
                                                                                            __eo_typeof_re_mult
                                                                                                (__eo_typeof X) ≠
                                                                                              Term.Stuck at hApp
                                                                                          rw [
                                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                                              hApp]
                                                                                          intro h
                                                                                          cases h)
                                                                                        (fun X Y hXY => by
                                                                                          change
                                                                                            __eo_typeof_re_mult
                                                                                                (__eo_typeof X) =
                                                                                              __eo_typeof_re_mult
                                                                                                (__eo_typeof Y)
                                                                                          rw [hXY])
                                                                                        (fun X hXTrans hApp => by
                                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                                          change
                                                                                            __smtx_typeof
                                                                                                (SmtTerm.re_opt
                                                                                                  (__eo_to_smt X)) ≠
                                                                                              SmtType.None
                                                                                          change
                                                                                            __eo_typeof_re_mult
                                                                                                (__eo_typeof X) ≠
                                                                                              Term.Stuck at hApp
                                                                                          have hArgEo :=
                                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                                              hApp
                                                                                          have hSmtArg :=
                                                                                            smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                                              hXTrans
                                                                                              hArgEo
                                                                                          rw [
                                                                                            typeof_re_opt_eq,
                                                                                            hSmtArg]
                                                                                          simp [
                                                                                            native_ite,
                                                                                            native_Teq])
                                                                                        (fun hATrans hATy =>
                                                                                          hRec
                                                                                            (G := a)
                                                                                            (bvs' := bvs)
                                                                                            (by simp)
                                                                                            hXsEnv
                                                                                            hBvsEnv
                                                                                            hATrans
                                                                                            hTs
                                                                                            hActuals
                                                                                            hATy)
                                                                                  · by_cases hHeadReComp :
                                                                                      f =
                                                                                        Term.UOp
                                                                                          UserOp.re_comp
                                                                                    · subst f
                                                                                      exact
                                                                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                          UserOp.re_comp
                                                                                          a xs ts
                                                                                          bvs
                                                                                          hXsEnv
                                                                                          hBvsEnv
                                                                                          hTs
                                                                                          (fun q v vs hEq =>
                                                                                            hBinder
                                                                                              ⟨q,
                                                                                                v,
                                                                                                vs,
                                                                                                hEq⟩)
                                                                                          hFTrans
                                                                                          hTy
                                                                                          (fun h =>
                                                                                            re_comp_arg_has_smt_translation_of_has_smt_translation h)
                                                                                          (fun X hApp => by
                                                                                            change
                                                                                              __eo_typeof_re_mult
                                                                                                  (__eo_typeof X) ≠
                                                                                                Term.Stuck at hApp
                                                                                            rw [
                                                                                              eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                                                hApp]
                                                                                            intro h
                                                                                            cases h)
                                                                                          (fun X Y hXY => by
                                                                                            change
                                                                                              __eo_typeof_re_mult
                                                                                                  (__eo_typeof X) =
                                                                                                __eo_typeof_re_mult
                                                                                                  (__eo_typeof Y)
                                                                                            rw [
                                                                                              hXY])
                                                                                          (fun X hXTrans hApp => by
                                                                                            unfold RuleProofs.eo_has_smt_translation
                                                                                            change
                                                                                              __smtx_typeof
                                                                                                  (SmtTerm.re_comp
                                                                                                    (__eo_to_smt X)) ≠
                                                                                                SmtType.None
                                                                                            change
                                                                                              __eo_typeof_re_mult
                                                                                                  (__eo_typeof X) ≠
                                                                                                Term.Stuck at hApp
                                                                                            have hArgEo :=
                                                                                              eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                                                hApp
                                                                                            have hSmtArg :=
                                                                                              smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                                                hXTrans
                                                                                                hArgEo
                                                                                            rw [
                                                                                              typeof_re_comp_eq,
                                                                                              hSmtArg]
                                                                                            simp [
                                                                                              native_ite,
                                                                                              native_Teq])
                                                                                          (fun hATrans hATy =>
                                                                                            hRec
                                                                                              (G := a)
                                                                                              (bvs' := bvs)
                                                                                              (by simp)
                                                                                              hXsEnv
                                                                                              hBvsEnv
                                                                                              hATrans
                                                                                              hTs
                                                                                              hActuals
                                                                                              hATy)
                                                                                    · by_cases hHeadUbvToInt :
                                                                                        f =
                                                                                          Term.UOp
                                                                                            UserOp.ubv_to_int
                                                                                      · subst f
                                                                                        exact
                                                                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                            UserOp.ubv_to_int
                                                                                            a xs ts
                                                                                            bvs
                                                                                            hXsEnv
                                                                                            hBvsEnv
                                                                                            hTs
                                                                                            (fun q v vs hEq =>
                                                                                              hBinder
                                                                                                ⟨q,
                                                                                                  v,
                                                                                                  vs,
                                                                                                  hEq⟩)
                                                                                            hFTrans
                                                                                            hTy
                                                                                            (fun h =>
                                                                                              ubv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                                            (fun X hApp => by
                                                                                              change
                                                                                                __eo_typeof__at_bvsize
                                                                                                    (__eo_typeof X) ≠
                                                                                                  Term.Stuck at hApp
                                                                                              rcases
                                                                                                  eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                                                    hApp with
                                                                                                ⟨w,
                                                                                                  hArg⟩
                                                                                              rw [
                                                                                                hArg]
                                                                                              intro h
                                                                                              cases h)
                                                                                            (fun X Y hXY => by
                                                                                              change
                                                                                                __eo_typeof__at_bvsize
                                                                                                    (__eo_typeof X) =
                                                                                                  __eo_typeof__at_bvsize
                                                                                                    (__eo_typeof Y)
                                                                                              rw [
                                                                                                hXY])
                                                                                            (fun X hXTrans hApp => by
                                                                                              unfold RuleProofs.eo_has_smt_translation
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.ubv_to_int
                                                                                                      (__eo_to_smt X)) ≠
                                                                                                  SmtType.None
                                                                                              change
                                                                                                __eo_typeof__at_bvsize
                                                                                                    (__eo_typeof X) ≠
                                                                                                  Term.Stuck at hApp
                                                                                              rcases
                                                                                                  eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                                                    hApp with
                                                                                                ⟨w,
                                                                                                  hArgEo⟩
                                                                                              rcases
                                                                                                  smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                                                    hXTrans
                                                                                                    hArgEo with
                                                                                                ⟨n,
                                                                                                  hSmtArg⟩
                                                                                              rw [
                                                                                                smt_typeof_ubv_to_int_eq,
                                                                                                hSmtArg]
                                                                                              simp [
                                                                                                __smtx_typeof_bv_op_1_ret])
                                                                                            (fun hATrans hATy =>
                                                                                              hRec
                                                                                                (G := a)
                                                                                                (bvs' := bvs)
                                                                                                (by simp)
                                                                                                hXsEnv
                                                                                                hBvsEnv
                                                                                                hATrans
                                                                                                hTs
                                                                                                hActuals
                                                                                                hATy)
                                                                                      · by_cases hHeadSbvToInt :
                                                                                          f =
                                                                                            Term.UOp
                                                                                              UserOp.sbv_to_int
                                                                                        · subst f
                                                                                          exact
                                                                                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                              UserOp.sbv_to_int
                                                                                              a xs ts
                                                                                              bvs
                                                                                              hXsEnv
                                                                                              hBvsEnv
                                                                                              hTs
                                                                                              (fun q v vs hEq =>
                                                                                                hBinder
                                                                                                  ⟨q,
                                                                                                    v,
                                                                                                    vs,
                                                                                                    hEq⟩)
                                                                                              hFTrans
                                                                                              hTy
                                                                                              (fun h =>
                                                                                                sbv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                                              (fun X hApp => by
                                                                                                change
                                                                                                  __eo_typeof__at_bvsize
                                                                                                      (__eo_typeof X) ≠
                                                                                                    Term.Stuck at hApp
                                                                                                rcases
                                                                                                    eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                                                      hApp with
                                                                                                  ⟨w,
                                                                                                    hArg⟩
                                                                                                rw [
                                                                                                  hArg]
                                                                                                intro h
                                                                                                cases h)
                                                                                              (fun X Y hXY => by
                                                                                                change
                                                                                                  __eo_typeof__at_bvsize
                                                                                                      (__eo_typeof X) =
                                                                                                    __eo_typeof__at_bvsize
                                                                                                      (__eo_typeof Y)
                                                                                                rw [
                                                                                                  hXY])
                                                                                              (fun X hXTrans hApp => by
                                                                                                unfold RuleProofs.eo_has_smt_translation
                                                                                                change
                                                                                                  __smtx_typeof
                                                                                                      (SmtTerm.sbv_to_int
                                                                                                        (__eo_to_smt X)) ≠
                                                                                                    SmtType.None
                                                                                                change
                                                                                                  __eo_typeof__at_bvsize
                                                                                                      (__eo_typeof X) ≠
                                                                                                    Term.Stuck at hApp
                                                                                                rcases
                                                                                                    eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                                                      hApp with
                                                                                                  ⟨w,
                                                                                                    hArgEo⟩
                                                                                                rcases
                                                                                                    smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                                                      hXTrans
                                                                                                      hArgEo with
                                                                                                  ⟨n,
                                                                                                    hSmtArg⟩
                                                                                                rw [
                                                                                                  smt_typeof_sbv_to_int_eq,
                                                                                                  hSmtArg]
                                                                                                simp [
                                                                                                  __smtx_typeof_bv_op_1_ret])
                                                                                              (fun hATrans hATy =>
                                                                                                hRec
                                                                                                  (G := a)
                                                                                                  (bvs' := bvs)
                                                                                                  (by simp)
                                                                                                  hXsEnv
                                                                                                  hBvsEnv
                                                                                                  hATrans
                                                                                                  hTs
                                                                                                  hActuals
                                                                                                  hATy)
                                                                                        · by_cases hHeadStringsStoiNonDigit :
                                                                                            f =
                                                                                              Term.UOp
                                                                                                UserOp._at_strings_stoi_non_digit
                                                                                          · subst f
                                                                                            exact
                                                                                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                UserOp._at_strings_stoi_non_digit
                                                                                                a xs ts
                                                                                                bvs
                                                                                                hXsEnv
                                                                                                hBvsEnv
                                                                                                hTs
                                                                                                (fun q v vs hEq =>
                                                                                                  hBinder
                                                                                                    ⟨q,
                                                                                                      v,
                                                                                                      vs,
                                                                                                      hEq⟩)
                                                                                                hFTrans
                                                                                                hTy
                                                                                                (fun h =>
                                                                                                  strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                (fun X hApp => by
                                                                                                  change
                                                                                                    __eo_typeof_str_to_code
                                                                                                        (__eo_typeof X) ≠
                                                                                                      Term.Stuck at hApp
                                                                                                  rw [
                                                                                                    eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                                                      hApp]
                                                                                                  intro h
                                                                                                  cases h)
                                                                                                (fun X Y hXY => by
                                                                                                  change
                                                                                                    __eo_typeof_str_to_code
                                                                                                        (__eo_typeof X) =
                                                                                                      __eo_typeof_str_to_code
                                                                                                        (__eo_typeof Y)
                                                                                                  rw [
                                                                                                    hXY])
                                                                                                (fun X hXTrans hApp => by
                                                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                                                  change
                                                                                                    __smtx_typeof
                                                                                                        (SmtTerm.str_indexof_re
                                                                                                          (__eo_to_smt X)
                                                                                                          (SmtTerm.re_comp
                                                                                                            (SmtTerm.re_range
                                                                                                              (SmtTerm.String
                                                                                                                (native_string_lit
                                                                                                                  "0"))
                                                                                                              (SmtTerm.String
                                                                                                                (native_string_lit
                                                                                                                  "9"))))
                                                                                                          (SmtTerm.Numeral
                                                                                                            0)) ≠
                                                                                                      SmtType.None
                                                                                                  change
                                                                                                    __eo_typeof_str_to_code
                                                                                                        (__eo_typeof X) ≠
                                                                                                      Term.Stuck at hApp
                                                                                                  have hArgEo :=
                                                                                                    eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                                                      hApp
                                                                                                  have hSmtArg :=
                                                                                                    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                                      hXTrans
                                                                                                      hArgEo
                                                                                                  have hZeroCharTy :
                                                                                                      __smtx_typeof
                                                                                                          (SmtTerm.String
                                                                                                            (native_string_lit
                                                                                                              "0")) =
                                                                                                        SmtType.Seq
                                                                                                          SmtType.Char := by
                                                                                                    rw [
                                                                                                      __smtx_typeof.eq_4]
                                                                                                    simp [
                                                                                                      native_string_lit,
                                                                                                      native_string_valid,
                                                                                                      native_char_valid,
                                                                                                      native_ite]
                                                                                                  have hNineCharTy :
                                                                                                      __smtx_typeof
                                                                                                          (SmtTerm.String
                                                                                                            (native_string_lit
                                                                                                              "9")) =
                                                                                                        SmtType.Seq
                                                                                                          SmtType.Char := by
                                                                                                    rw [
                                                                                                      __smtx_typeof.eq_4]
                                                                                                    simp [
                                                                                                      native_string_lit,
                                                                                                      native_string_valid,
                                                                                                      native_char_valid,
                                                                                                      native_ite]
                                                                                                  rw [
                                                                                                    typeof_str_indexof_re_eq,
                                                                                                    typeof_re_comp_eq,
                                                                                                    typeof_re_range_eq,
                                                                                                    hSmtArg,
                                                                                                    hZeroCharTy,
                                                                                                    hNineCharTy,
                                                                                                    __smtx_typeof.eq_2]
                                                                                                  simp [
                                                                                                    native_ite,
                                                                                                    native_Teq])
                                                                                                (fun hATrans hATy =>
                                                                                                  hRec
                                                                                                    (G := a)
                                                                                                    (bvs' := bvs)
                                                                                                    (by simp)
                                                                                                    hXsEnv
                                                                                                    hBvsEnv
                                                                                                    hATrans
                                                                                                    hTs
                                                                                                    hActuals
                                                                                                    hATy)
                                                                                          · by_cases hHeadSeqUnit :
                                                                                              f =
                                                                                                Term.UOp
                                                                                                  UserOp.seq_unit
                                                                                            · subst f
                                                                                              exact
                                                                                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
                                                                                                  UserOp.seq_unit
                                                                                                  a xs
                                                                                                  ts
                                                                                                  bvs
                                                                                                  hXsEnv
                                                                                                  hBvsEnv
                                                                                                  hTs
                                                                                                  (fun q v vs hEq =>
                                                                                                    hBinder
                                                                                                      ⟨q,
                                                                                                        v,
                                                                                                        vs,
                                                                                                        hEq⟩)
                                                                                                  hFTrans
                                                                                                  hTy
                                                                                                  (fun h =>
                                                                                                    seq_unit_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                  (fun X hApp => by
                                                                                                    change
                                                                                                      __eo_typeof_seq_unit
                                                                                                          (__eo_typeof X) ≠
                                                                                                        Term.Stuck at hApp
                                                                                                    exact
                                                                                                      eo_typeof_seq_unit_arg_not_stuck_of_ne_stuck
                                                                                                        hApp)
                                                                                                  (fun X Y hXY => by
                                                                                                    change
                                                                                                      __eo_typeof_seq_unit
                                                                                                          (__eo_typeof X) =
                                                                                                        __eo_typeof_seq_unit
                                                                                                          (__eo_typeof Y)
                                                                                                    rw [
                                                                                                      hXY])
                                                                                                  (fun X hXTrans hXTyEq hApp => by
                                                                                                    unfold RuleProofs.eo_has_smt_translation
                                                                                                    change
                                                                                                      __smtx_typeof
                                                                                                          (SmtTerm.seq_unit
                                                                                                            (__eo_to_smt
                                                                                                              X)) ≠
                                                                                                        SmtType.None
                                                                                                    change
                                                                                                      __eo_typeof_seq_unit
                                                                                                          (__eo_typeof X) ≠
                                                                                                        Term.Stuck at hApp
                                                                                                    have hFTransEo :
                                                                                                        eoHasSmtTranslation
                                                                                                          (Term.Apply
                                                                                                            (Term.UOp UserOp.seq_unit)
                                                                                                            a) := by
                                                                                                      simpa [
                                                                                                        RuleProofs.eo_has_smt_translation,
                                                                                                        eoHasSmtTranslation]
                                                                                                        using hFTrans
                                                                                                    have hATrans :
                                                                                                        RuleProofs.eo_has_smt_translation
                                                                                                          a := by
                                                                                                      simpa [
                                                                                                        RuleProofs.eo_has_smt_translation,
                                                                                                        eoHasSmtTranslation]
                                                                                                        using
                                                                                                          seq_unit_arg_has_smt_translation_of_has_smt_translation
                                                                                                            hFTransEo
                                                                                                    exact
                                                                                                      smt_seq_unit_non_none_of_has_smt_translation_type_eq
                                                                                                        a X hFTrans hATrans hXTrans hXTyEq)
                                                                                                  (fun hATrans hATy =>
                                                                                                    hRec
                                                                                                      (G := a)
                                                                                                      (bvs' := bvs)
                                                                                                      (by simp)
                                                                                                      hXsEnv
                                                                                                      hBvsEnv
                                                                                                      hATrans
                                                                                                      hTs
                                                                                                      hActuals
                                                                                                      hATy)
                                                                                            · by_cases hHeadSetSingleton :
                                                                                                f =
                                                                                                  Term.UOp
                                                                                                    UserOp.set_singleton
                                                                                              · subst f
                                                                                                exact
                                                                                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
                                                                                                    UserOp.set_singleton
                                                                                                    a xs
                                                                                                    ts
                                                                                                    bvs
                                                                                                    hXsEnv
                                                                                                    hBvsEnv
                                                                                                    hTs
                                                                                                    (fun q v vs hEq =>
                                                                                                      hBinder
                                                                                                        ⟨q,
                                                                                                          v,
                                                                                                          vs,
                                                                                                          hEq⟩)
                                                                                                    hFTrans
                                                                                                    hTy
                                                                                                    (fun h =>
                                                                                                      set_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                    (fun X hApp => by
                                                                                                      change
                                                                                                        __eo_typeof_set_singleton
                                                                                                            (__eo_typeof X) ≠
                                                                                                          Term.Stuck at hApp
                                                                                                      exact
                                                                                                        eo_typeof_set_singleton_arg_not_stuck_of_ne_stuck
                                                                                                          hApp)
                                                                                                    (fun X Y hXY => by
                                                                                                      change
                                                                                                        __eo_typeof_set_singleton
                                                                                                            (__eo_typeof X) =
                                                                                                          __eo_typeof_set_singleton
                                                                                                            (__eo_typeof Y)
                                                                                                      rw [
                                                                                                        hXY])
                                                                                                    (fun X hXTrans hXTyEq hApp => by
                                                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                                                      change
                                                                                                        __smtx_typeof
                                                                                                            (SmtTerm.set_singleton
                                                                                                              (__eo_to_smt
                                                                                                                X)) ≠
                                                                                                          SmtType.None
                                                                                                      change
                                                                                                        __eo_typeof_set_singleton
                                                                                                            (__eo_typeof X) ≠
                                                                                                          Term.Stuck at hApp
                                                                                                      have hFTransEo :
                                                                                                          eoHasSmtTranslation
                                                                                                            (Term.Apply
                                                                                                              (Term.UOp UserOp.set_singleton)
                                                                                                              a) := by
                                                                                                        simpa [
                                                                                                          RuleProofs.eo_has_smt_translation,
                                                                                                          eoHasSmtTranslation]
                                                                                                          using hFTrans
                                                                                                      have hATrans :
                                                                                                          RuleProofs.eo_has_smt_translation
                                                                                                            a := by
                                                                                                        simpa [
                                                                                                          RuleProofs.eo_has_smt_translation,
                                                                                                          eoHasSmtTranslation]
                                                                                                          using
                                                                                                            set_singleton_arg_has_smt_translation_of_has_smt_translation
                                                                                                              hFTransEo
                                                                                                      exact
                                                                                                        smt_set_singleton_non_none_of_has_smt_translation_type_eq
                                                                                                          a X hFTrans hATrans hXTrans hXTyEq)
                                                                                                    (fun hATrans hATy =>
                                                                                                      hRec
                                                                                                        (G := a)
                                                                                                        (bvs' := bvs)
                                                                                                        (by simp)
                                                                                                        hXsEnv
                                                                                                        hBvsEnv
                                                                                                        hATrans
                                                                                                        hTs
                                                                                                        hActuals
                                                                                                        hATy)
                                                                                              · by_cases hHeadSetChoose :
                                                                                                  f =
                                                                                                    Term.UOp
                                                                                                      UserOp.set_choose
                                                                                                · subst f
                                                                                                  exact
                                                                                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                      UserOp.set_choose
                                                                                                      a xs
                                                                                                      ts
                                                                                                      bvs
                                                                                                      hXsEnv
                                                                                                      hBvsEnv
                                                                                                      hTs
                                                                                                      (fun q v vs hEq =>
                                                                                                        hBinder
                                                                                                          ⟨q,
                                                                                                            v,
                                                                                                            vs,
                                                                                                            hEq⟩)
                                                                                                      hFTrans
                                                                                                      hTy
                                                                                                      (fun h =>
                                                                                                        set_choose_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                      (fun X hApp => by
                                                                                                        change
                                                                                                          __eo_typeof_set_choose
                                                                                                              (__eo_typeof X) ≠
                                                                                                            Term.Stuck at hApp
                                                                                                        rcases
                                                                                                            eo_typeof_set_choose_arg_set_of_ne_stuck
                                                                                                              hApp with
                                                                                                          ⟨T,
                                                                                                            hArg⟩
                                                                                                        rw [
                                                                                                          hArg]
                                                                                                        intro h
                                                                                                        cases h)
                                                                                                      (fun X Y hXY => by
                                                                                                        change
                                                                                                          __eo_typeof_set_choose
                                                                                                              (__eo_typeof X) =
                                                                                                            __eo_typeof_set_choose
                                                                                                              (__eo_typeof Y)
                                                                                                        rw [
                                                                                                          hXY])
                                                                                                      (fun X hXTrans hApp => by
                                                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                                                        change
                                                                                                          __smtx_typeof
                                                                                                              (SmtTerm.map_diff
                                                                                                                (__eo_to_smt
                                                                                                                  X)
                                                                                                                (SmtTerm.set_empty
                                                                                                                  (__eo_to_smt_set_elem_type
                                                                                                                    (__smtx_typeof
                                                                                                                      (__eo_to_smt
                                                                                                                        X))))) ≠
                                                                                                            SmtType.None
                                                                                                        change
                                                                                                          __eo_typeof_set_choose
                                                                                                              (__eo_typeof X) ≠
                                                                                                            Term.Stuck at hApp
                                                                                                        rcases
                                                                                                            eo_typeof_set_choose_arg_set_of_ne_stuck
                                                                                                              hApp with
                                                                                                          ⟨T,
                                                                                                            hArgEo⟩
                                                                                                        have hSmtArg :=
                                                                                                          smt_typeof_eo_to_smt_set_of_typeof_set
                                                                                                            hXTrans
                                                                                                            hArgEo
                                                                                                        have hEmpty :=
                                                                                                          smt_typeof_set_empty_of_eo_set_arg
                                                                                                            hXTrans
                                                                                                            hArgEo
                                                                                                        have hEmpty' :
                                                                                                            __smtx_typeof
                                                                                                                (SmtTerm.set_empty
                                                                                                                  (__eo_to_smt_type
                                                                                                                    T)) =
                                                                                                              SmtType.Set
                                                                                                                (__eo_to_smt_type
                                                                                                                  T) := by
                                                                                                          simpa [
                                                                                                            hSmtArg,
                                                                                                            __eo_to_smt_set_elem_type]
                                                                                                            using
                                                                                                              hEmpty
                                                                                                        have hElemNN :
                                                                                                            __eo_to_smt_type
                                                                                                                T ≠
                                                                                                              SmtType.None :=
                                                                                                          smt_typeof_eo_to_smt_set_elem_ne_none_of_typeof_set
                                                                                                            hXTrans
                                                                                                            hArgEo
                                                                                                        rw [
                                                                                                          typeof_map_diff_eq,
                                                                                                          hEmpty,
                                                                                                          hSmtArg]
                                                                                                        simp [
                                                                                                          __smtx_typeof_map_diff,
                                                                                                          native_ite,
                                                                                                          native_Teq,
                                                                                                          hElemNN])
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp)
                                                                                                          hXsEnv
                                                                                                          hBvsEnv
                                                                                                          hATrans
                                                                                                          hTs
                                                                                                          hActuals
                                                                                                              hATy)
                                                                                                · by_cases hHeadSetIsEmpty :
                                                                                                    f =
                                                                                                      Term.UOp
                                                                                                        UserOp.set_is_empty
                                                                                                  · subst f
                                                                                                    exact
                                                                                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                        UserOp.set_is_empty
                                                                                                        a xs
                                                                                                        ts
                                                                                                        bvs
                                                                                                        hXsEnv
                                                                                                        hBvsEnv
                                                                                                        hTs
                                                                                                        (fun q v vs hEq =>
                                                                                                          hBinder
                                                                                                            ⟨q,
                                                                                                              v,
                                                                                                              vs,
                                                                                                              hEq⟩)
                                                                                                        hFTrans
                                                                                                        hTy
                                                                                                        (fun h =>
                                                                                                          set_is_empty_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                        (fun X hApp => by
                                                                                                          change
                                                                                                            __eo_typeof_set_is_empty
                                                                                                                (__eo_typeof X) ≠
                                                                                                              Term.Stuck at hApp
                                                                                                          rcases
                                                                                                              eo_typeof_set_is_empty_arg_set_of_ne_stuck
                                                                                                                hApp with
                                                                                                            ⟨T,
                                                                                                              hArg⟩
                                                                                                          rw [
                                                                                                            hArg]
                                                                                                          intro h
                                                                                                          cases h)
                                                                                                        (fun X Y hXY => by
                                                                                                          change
                                                                                                            __eo_typeof_set_is_empty
                                                                                                                (__eo_typeof X) =
                                                                                                              __eo_typeof_set_is_empty
                                                                                                                (__eo_typeof Y)
                                                                                                          rw [
                                                                                                            hXY])
                                                                                                        (fun X hXTrans hApp => by
                                                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                                                          change
                                                                                                            __smtx_typeof
                                                                                                                (SmtTerm.eq
                                                                                                                  (__eo_to_smt
                                                                                                                    X)
                                                                                                                  (SmtTerm.set_empty
                                                                                                                    (__eo_to_smt_set_elem_type
                                                                                                                      (__smtx_typeof
                                                                                                                        (__eo_to_smt
                                                                                                                          X))))) ≠
                                                                                                              SmtType.None
                                                                                                          change
                                                                                                            __eo_typeof_set_is_empty
                                                                                                                (__eo_typeof X) ≠
                                                                                                              Term.Stuck at hApp
                                                                                                          rcases
                                                                                                              eo_typeof_set_is_empty_arg_set_of_ne_stuck
                                                                                                                hApp with
                                                                                                            ⟨T,
                                                                                                              hArgEo⟩
                                                                                                          have hSmtArg :=
                                                                                                            smt_typeof_eo_to_smt_set_of_typeof_set
                                                                                                              hXTrans
                                                                                                              hArgEo
                                                                                                          have hEmpty :=
                                                                                                            smt_typeof_set_empty_of_eo_set_arg
                                                                                                              hXTrans
                                                                                                              hArgEo
                                                                                                          have hEmpty' :
                                                                                                              __smtx_typeof
                                                                                                                  (SmtTerm.set_empty
                                                                                                                    (__eo_to_smt_type
                                                                                                                      T)) =
                                                                                                                SmtType.Set
                                                                                                                  (__eo_to_smt_type
                                                                                                                    T) := by
                                                                                                            simpa [
                                                                                                              hSmtArg,
                                                                                                              __eo_to_smt_set_elem_type]
                                                                                                              using
                                                                                                                hEmpty
                                                                                                          rw [
                                                                                                            typeof_eq_eq,
                                                                                                            hEmpty,
                                                                                                            hSmtArg]
                                                                                                          simp [
                                                                                                            __smtx_typeof_eq,
                                                                                                            __smtx_typeof_guard,
                                                                                                            native_ite,
                                                                                                            native_Teq])
                                                                                                        (fun hATrans hATy =>
                                                                                                          hRec
                                                                                                            (G := a)
                                                                                                            (bvs' := bvs)
                                                                                                            (by simp)
                                                                                                            hXsEnv
                                                                                                            hBvsEnv
                                                                                                            hATrans
                                                                                                            hTs
                                                                                                            hActuals
                                                                                                            hATy)
                                                                                                  · by_cases hHeadSetIsSingleton :
                                                                                                      f =
                                                                                                        Term.UOp
                                                                                                          UserOp.set_is_singleton
                                                                                                    · subst f
                                                                                                      exact
                                                                                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                          UserOp.set_is_singleton
                                                                                                          a xs
                                                                                                          ts
                                                                                                          bvs
                                                                                                          hXsEnv
                                                                                                          hBvsEnv
                                                                                                          hTs
                                                                                                          (fun q v vs hEq =>
                                                                                                            hBinder
                                                                                                              ⟨q,
                                                                                                                v,
                                                                                                                vs,
                                                                                                                hEq⟩)
                                                                                                          hFTrans
                                                                                                          hTy
                                                                                                          (fun h =>
                                                                                                            set_is_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                          (fun X hApp => by
                                                                                                            change
                                                                                                              __eo_typeof_set_is_empty
                                                                                                                  (__eo_typeof X) ≠
                                                                                                                Term.Stuck at hApp
                                                                                                            rcases
                                                                                                                eo_typeof_set_is_empty_arg_set_of_ne_stuck
                                                                                                                  hApp with
                                                                                                              ⟨T,
                                                                                                                hArg⟩
                                                                                                            rw [
                                                                                                              hArg]
                                                                                                            intro h
                                                                                                            cases h)
                                                                                                          (fun X Y hXY => by
                                                                                                            change
                                                                                                              __eo_typeof_set_is_empty
                                                                                                                  (__eo_typeof X) =
                                                                                                                __eo_typeof_set_is_empty
                                                                                                                  (__eo_typeof Y)
                                                                                                            rw [
                                                                                                              hXY])
                                                                                                          (fun X hXTrans hApp => by
                                                                                                            unfold RuleProofs.eo_has_smt_translation
                                                                                                            change
                                                                                                              __smtx_typeof
                                                                                                                  (SmtTerm.eq
                                                                                                                    (__eo_to_smt
                                                                                                                      X)
                                                                                                                    (SmtTerm.set_singleton
                                                                                                                      (SmtTerm.map_diff
                                                                                                                        (__eo_to_smt
                                                                                                                          X)
                                                                                                                        (SmtTerm.set_empty
                                                                                                                          (__eo_to_smt_set_elem_type
                                                                                                                            (__smtx_typeof
                                                                                                                              (__eo_to_smt
                                                                                                                                X))))))) ≠
                                                                                                                SmtType.None
                                                                                                            change
                                                                                                              __eo_typeof_set_is_empty
                                                                                                                  (__eo_typeof X) ≠
                                                                                                                Term.Stuck at hApp
                                                                                                            rcases
                                                                                                                eo_typeof_set_is_empty_arg_set_of_ne_stuck
                                                                                                                  hApp with
                                                                                                              ⟨T,
                                                                                                                hArgEo⟩
                                                                                                            have hSmtArg :=
                                                                                                              smt_typeof_eo_to_smt_set_of_typeof_set
                                                                                                                hXTrans
                                                                                                                hArgEo
                                                                                                            have hEmpty :=
                                                                                                              smt_typeof_set_empty_of_eo_set_arg
                                                                                                                hXTrans
                                                                                                                hArgEo
                                                                                                            have hEmpty' :
                                                                                                                __smtx_typeof
                                                                                                                    (SmtTerm.set_empty
                                                                                                                      (__eo_to_smt_type
                                                                                                                        T)) =
                                                                                                                  SmtType.Set
                                                                                                                    (__eo_to_smt_type
                                                                                                                      T) := by
                                                                                                              simpa [
                                                                                                                hSmtArg,
                                                                                                                __eo_to_smt_set_elem_type]
                                                                                                                using
                                                                                                                  hEmpty
                                                                                                            have hDiffTy :
                                                                                                                __smtx_typeof
                                                                                                                    (SmtTerm.map_diff
                                                                                                                      (__eo_to_smt
                                                                                                                        X)
                                                                                                                      (SmtTerm.set_empty
                                                                                                                        (__eo_to_smt_set_elem_type
                                                                                                                          (__smtx_typeof
                                                                                                                            (__eo_to_smt
                                                                                                                              X))))) =
                                                                                                                  __eo_to_smt_type
                                                                                                                    T := by
                                                                                                              have hElemNN :
                                                                                                                  __eo_to_smt_type
                                                                                                                      T ≠
                                                                                                                    SmtType.None :=
                                                                                                                smt_typeof_eo_to_smt_set_elem_ne_none_of_typeof_set
                                                                                                                  hXTrans
                                                                                                                  hArgEo
                                                                                                              rw [
                                                                                                                typeof_map_diff_eq,
                                                                                                                hEmpty,
                                                                                                                hSmtArg]
                                                                                                              simp [
                                                                                                                __smtx_typeof_map_diff,
                                                                                                                native_ite,
                                                                                                                native_Teq]
                                                                                                            have hSetWf :
                                                                                                                __smtx_type_wf
                                                                                                                    (SmtType.Set
                                                                                                                      (__eo_to_smt_type
                                                                                                                        T)) =
                                                                                                                  true :=
                                                                                                              Smtm.smt_term_set_type_wf_of_non_none
                                                                                                                (__eo_to_smt
                                                                                                                  X)
                                                                                                                hXTrans
                                                                                                                hSmtArg
                                                                                                            have hSingletonTy :
                                                                                                                __smtx_typeof
                                                                                                                    (SmtTerm.set_singleton
                                                                                                                      (SmtTerm.map_diff
                                                                                                                        (__eo_to_smt
                                                                                                                          X)
                                                                                                                        (SmtTerm.set_empty
                                                                                                                          (__eo_to_smt_set_elem_type
                                                                                                                            (__smtx_typeof
                                                                                                                              (__eo_to_smt
                                                                                                                                X)))))) =
                                                                                                                  SmtType.Set
                                                                                                                    (__eo_to_smt_type
                                                                                                                      T) := by
                                                                                                              rw [
                                                                                                                smtx_typeof_set_singleton_term_eq,
                                                                                                                hDiffTy]
                                                                                                              simp [
                                                                                                                __smtx_typeof_guard_wf,
                                                                                                                hSetWf,
                                                                                                                native_ite]
                                                                                                            rw [
                                                                                                              typeof_eq_eq,
                                                                                                              hSingletonTy,
                                                                                                              hSmtArg]
                                                                                                            simp [
                                                                                                              __smtx_typeof_eq,
                                                                                                              __smtx_typeof_guard,
                                                                                                              native_ite,
                                                                                                              native_Teq])
                                                                                                          (fun hATrans hATy =>
                                                                                                            hRec
                                                                                                              (G := a)
                                                                                                              (bvs' := bvs)
                                                                                                              (by simp)
                                                                                                              hXsEnv
                                                                                                              hBvsEnv
                                                                                                              hATrans
                                                                                                              hTs
                                                                                                              hActuals
                                                                                                              hATy)
                                                                                                    · by_cases hHeadDistinct :
                                                                                                        f =
                                                                                                          Term.UOp
                                                                                                            UserOp.distinct
                                                                                                      · subst f
                                                                                                        exact
                                                                                                          substitute_simul_distinct_preserves_type_and_translation
                                                                                                            a xs ts bvs hXsEnv hBvsEnv hTs hFTrans hTy
                                                                                                            (fun t hLtA hTTrans hTTy => by
                                                                                                              have hBoth :=
                                                                                                                hRec
                                                                                                                  (G := t)
                                                                                                                  (by
                                                                                                                    simp at hLtA ⊢
                                                                                                                    omega)
                                                                                                                  hXsEnv hBvsEnv hTTrans hTs hActuals hTTy
                                                                                                              have hSubMatch :=
                                                                                                                TranslationProofs.eo_to_smt_typeof_matches_translation
                                                                                                                  (__substitute_simul_rec (Term.Boolean isRename) t xs ts bvs)
                                                                                                                  hBoth.2
                                                                                                              have hOrigMatch :=
                                                                                                                TranslationProofs.eo_to_smt_typeof_matches_translation t hTTrans
                                                                                                              rw [hSubMatch, hBoth.1, ← hOrigMatch])
                                                                                                      · by_cases hHeadDtSel :
                                                                                                        ∃ s d i j,
                                                                                                          f =
                                                                                                            Term.DtSel
                                                                                                              s
                                                                                                              d
                                                                                                              i
                                                                                                              j
                                                                                                        · rcases
                                                                                                            hHeadDtSel with
                                                                                                          ⟨s,
                                                                                                            d,
                                                                                                            i,
                                                                                                            j,
                                                                                                            rfl⟩
                                                                                                          exact
                                                                                                            substitute_simul_apply_dtsel_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                              s
                                                                                                              d
                                                                                                              i
                                                                                                              j
                                                                                                              a xs
                                                                                                              ts
                                                                                                              bvs
                                                                                                              hXsEnv
                                                                                                              hBvsEnv
                                                                                                              hTs
                                                                                                              hFTrans
                                                                                                              (fun hATrans hATy =>
                                                                                                                hRec
                                                                                                                  (G := a)
                                                                                                                  (bvs' := bvs)
                                                                                                                  (by
                                                                                                                    simp
                                                                                                                    omega)
                                                                                                                  hXsEnv
                                                                                                                  hBvsEnv
                                                                                                                  hATrans
                                                                                                                  hTs
                                                                                                                  hActuals
                                                                                                                  hATy)
                                                                                                              hTy
                                                                                                        · by_cases hHeadUOp1 :
                                                                                                            ∃ op idx,
                                                                                                              f =
                                                                                                                Term.UOp1
                                                                                                                  op
                                                                                                                  idx
                                                                                                          · rcases
                                                                                                              hHeadUOp1 with
                                                                                                            ⟨op,
                                                                                                              idx,
                                                                                                              rfl⟩
                                                                                                            by_cases hSeqEmpty :
                                                                                                                op =
                                                                                                                  UserOp1.seq_empty
                                                                                                            · subst op
                                                                                                              exact
                                                                                                                False.elim
                                                                                                                  (false_of_apply_uop1_seq_empty_has_smt_translation
                                                                                                                    idx
                                                                                                                    a
                                                                                                                    hFTrans)
                                                                                                            · by_cases hSetEmpty :
                                                                                                                op =
                                                                                                                  UserOp1.set_empty
                                                                                                              · subst op
                                                                                                                exact
                                                                                                                  False.elim
                                                                                                                    (false_of_apply_uop1_set_empty_has_smt_translation
                                                                                                                      idx
                                                                                                                      a
                                                                                                                      hFTrans)
                                                                                                              · by_cases hUpdate :
                                                                                                                  op =
                                                                                                                    UserOp1.update
                                                                                                                · subst op
                                                                                                                  exact
                                                                                                                    False.elim
                                                                                                                      (false_of_apply_uop1_update_has_smt_translation
                                                                                                                        idx
                                                                                                                        a
                                                                                                                        hFTrans)
                                                                                                                · by_cases hTupleUpdate :
                                                                                                                    op =
                                                                                                                      UserOp1.tuple_update
                                                                                                                  · subst op
                                                                                                                    exact
                                                                                                                      False.elim
                                                                                                                        (false_of_apply_uop1_tuple_update_has_smt_translation
                                                                                                                          idx
                                                                                                                          a
                                                                                                                          hFTrans)
                                                                                                                  · by_cases hReExp :
                                                                                                                      op =
                                                                                                                        UserOp1.re_exp
                                                                                                                    · subst op
                                                                                                                      exact
                                                                                                                        substitute_simul_apply_re_exp_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                          idx
                                                                                                                          a
                                                                                                                          xs
                                                                                                                          ts
                                                                                                                          bvs
                                                                                                                          hXsEnv
                                                                                                                          hBvsEnv
                                                                                                                          hTs
                                                                                                                          hFTrans
                                                                                                                          (fun hATrans hATy =>
                                                                                                                            hRec
                                                                                                                              (G := a)
                                                                                                                              (bvs' := bvs)
                                                                                                                              (by
                                                                                                                                simp
                                                                                                                                omega)
                                                                                                                              hXsEnv
                                                                                                                              hBvsEnv
                                                                                                                              hATrans
                                                                                                                              hTs
                                                                                                                              hActuals
                                                                                                                              hATy)
                                                                                                                          hTy
                                                                                                                    · by_cases hIntToBv :
                                                                                                                        op =
                                                                                                                          UserOp1.int_to_bv
                                                                                                                      · subst op
                                                                                                                        exact
                                                                                                                          substitute_simul_apply_int_to_bv_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                            idx
                                                                                                                            a
                                                                                                                            xs
                                                                                                                            ts
                                                                                                                            bvs
                                                                                                                            hXsEnv
                                                                                                                            hBvsEnv
                                                                                                                            hTs
                                                                                                                            hFTrans
                                                                                                                            (fun hATrans hATy =>
                                                                                                                              hRec
                                                                                                                                (G := a)
                                                                                                                                (bvs' := bvs)
                                                                                                                                (by
                                                                                                                                  simp
                                                                                                                                  omega)
                                                                                                                                hXsEnv
                                                                                                                                hBvsEnv
                                                                                                                                hATrans
                                                                                                                                hTs
                                                                                                                                hActuals
                                                                                                                                hATy)
                                                                                                                            hTy
                                                                                                                      · by_cases hRepeat :
                                                                                                                          op =
                                                                                                                            UserOp1.repeat
                                                                                                                        · subst op
                                                                                                                          exact
                                                                                                                            substitute_simul_apply_repeat_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                              idx
                                                                                                                              a
                                                                                                                              xs
                                                                                                                              ts
                                                                                                                              bvs
                                                                                                                              hXsEnv
                                                                                                                              hBvsEnv
                                                                                                                              hTs
                                                                                                                              hFTrans
                                                                                                                              (fun hATrans hATy =>
                                                                                                                                hRec
                                                                                                                                  (G := a)
                                                                                                                                  (bvs' := bvs)
                                                                                                                                  (by
                                                                                                                                    simp
                                                                                                                                    omega)
                                                                                                                                  hXsEnv
                                                                                                                                  hBvsEnv
                                                                                                                                  hATrans
                                                                                                                                  hTs
                                                                                                                                  hActuals
                                                                                                                                  hATy)
                                                                                                                              hTy
                                                                                                                        · by_cases hZeroExtend :
                                                                                                                            op =
                                                                                                                              UserOp1.zero_extend
                                                                                                                          · subst op
                                                                                                                            exact
                                                                                                                              substitute_simul_apply_zero_extend_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                idx
                                                                                                                                a
                                                                                                                                xs
                                                                                                                                ts
                                                                                                                                bvs
                                                                                                                                hXsEnv
                                                                                                                                hBvsEnv
                                                                                                                                hTs
                                                                                                                                hFTrans
                                                                                                                                (fun hATrans hATy =>
                                                                                                                                  hRec
                                                                                                                                    (G := a)
                                                                                                                                    (bvs' := bvs)
                                                                                                                                    (by
                                                                                                                                      simp
                                                                                                                                      omega)
                                                                                                                                    hXsEnv
                                                                                                                                    hBvsEnv
                                                                                                                                    hATrans
                                                                                                                                    hTs
                                                                                                                                    hActuals
                                                                                                                                    hATy)
                                                                                                                                hTy
                                                                                                                          · by_cases hSignExtend :
                                                                                                                              op =
                                                                                                                                UserOp1.sign_extend
                                                                                                                            · subst op
                                                                                                                              exact
                                                                                                                                substitute_simul_apply_sign_extend_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                  idx
                                                                                                                                  a
                                                                                                                                  xs
                                                                                                                                  ts
                                                                                                                                  bvs
                                                                                                                                  hXsEnv
                                                                                                                                  hBvsEnv
                                                                                                                                  hTs
                                                                                                                                  hFTrans
                                                                                                                                  (fun hATrans hATy =>
                                                                                                                                    hRec
                                                                                                                                      (G := a)
                                                                                                                                      (bvs' := bvs)
                                                                                                                                      (by
                                                                                                                                        simp
                                                                                                                                        omega)
                                                                                                                                      hXsEnv
                                                                                                                                      hBvsEnv
                                                                                                                                      hATrans
                                                                                                                                      hTs
                                                                                                                                      hActuals
                                                                                                                                      hATy)
                                                                                                                                  hTy
                                                                                                                            · by_cases hRotateLeft :
                                                                                                                                op =
                                                                                                                                  UserOp1.rotate_left
                                                                                                                              · subst op
                                                                                                                                exact
                                                                                                                                  substitute_simul_apply_rotate_left_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                    idx
                                                                                                                                    a
                                                                                                                                    xs
                                                                                                                                    ts
                                                                                                                                    bvs
                                                                                                                                    hXsEnv
                                                                                                                                    hBvsEnv
                                                                                                                                    hTs
                                                                                                                                    hFTrans
                                                                                                                                    (fun hATrans hATy =>
                                                                                                                                      hRec
                                                                                                                                        (G := a)
                                                                                                                                        (bvs' := bvs)
                                                                                                                                        (by
                                                                                                                                          simp
                                                                                                                                          omega)
                                                                                                                                        hXsEnv
                                                                                                                                        hBvsEnv
                                                                                                                                        hATrans
                                                                                                                                        hTs
                                                                                                                                        hActuals
                                                                                                                                        hATy)
                                                                                                                                    hTy
                                                                                                                              · by_cases hRotateRight :
                                                                                                                                  op =
                                                                                                                                    UserOp1.rotate_right
                                                                                                                                · subst op
                                                                                                                                  exact
                                                                                                                                    substitute_simul_apply_rotate_right_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                      idx
                                                                                                                                      a
                                                                                                                                      xs
                                                                                                                                      ts
                                                                                                                                      bvs
                                                                                                                                      hXsEnv
                                                                                                                                      hBvsEnv
                                                                                                                                      hTs
                                                                                                                                      hFTrans
                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                        hRec
                                                                                                                                          (G := a)
                                                                                                                                          (bvs' := bvs)
                                                                                                                                          (by
                                                                                                                                            simp
                                                                                                                                            omega)
                                                                                                                                          hXsEnv
                                                                                                                                          hBvsEnv
                                                                                                                                          hATrans
                                                                                                                                          hTs
                                                                                                                                            hActuals
                                                                                                                                            hATy)
                                                                                                                                      hTy
                                                                                                                                · by_cases hAtBit :
                                                                                                                                    op =
                                                                                                                                      UserOp1._at_bit
                                                                                                                                  · subst op
                                                                                                                                    exact
                                                                                                                                      substitute_simul_apply_at_bit_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                        idx
                                                                                                                                        a
                                                                                                                                        xs
                                                                                                                                        ts
                                                                                                                                        bvs
                                                                                                                                        hXsEnv
                                                                                                                                        hBvsEnv
                                                                                                                                        hTs
                                                                                                                                        hFTrans
                                                                                                                                        (fun hATrans hATy =>
                                                                                                                                          hRec
                                                                                                                                            (G := a)
                                                                                                                                            (bvs' := bvs)
                                                                                                                                            (by
                                                                                                                                              simp
                                                                                                                                              omega)
                                                                                                                                            hXsEnv
                                                                                                                                            hBvsEnv
                                                                                                                                            hATrans
                                                                                                                                            hTs
                                                                                                                                            hActuals
                                                                                                                                            hATy)
                                                                                                                                        hTy
                                                                                                                                  · by_cases hIs :
                                                                                                                                      op =
                                                                                                                                        UserOp1.is
                                                                                                                                    · subst op
                                                                                                                                      exact
                                                                                                                                        substitute_simul_apply_is_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                          idx
                                                                                                                                          a
                                                                                                                                          xs
                                                                                                                                          ts
                                                                                                                                          bvs
                                                                                                                                          hXsEnv
                                                                                                                                          hBvsEnv
                                                                                                                                          hTs
                                                                                                                                          hFTrans
                                                                                                                                          (fun hATrans hATy =>
                                                                                                                                            hRec
                                                                                                                                              (G := a)
                                                                                                                                              (bvs' := bvs)
                                                                                                                                              (by
                                                                                                                                                simp
                                                                                                                                                omega)
                                                                                                                                              hXsEnv
                                                                                                                                              hBvsEnv
                                                                                                                                              hATrans
                                                                                                                                              hTs
                                                                                                                                              hActuals
                                                                                                                                              hATy)
                                                                                                                                          hTy
                                                                                                                                    · by_cases hTupleSelect :
                                                                                                                                        op =
                                                                                                                                          UserOp1.tuple_select
                                                                                                                                      · subst op
                                                                                                                                        exact
                                                                                                                                          substitute_simul_apply_tuple_select_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                                            idx
                                                                                                                                            a
                                                                                                                                            xs
                                                                                                                                            ts
                                                                                                                                            bvs
                                                                                                                                            hXsEnv
                                                                                                                                            hBvsEnv
                                                                                                                                            hTs
                                                                                                                                            hFTrans
                                                                                                                                            (fun hATrans hATy =>
                                                                                                                                              hRec
                                                                                                                                                (G := a)
                                                                                                                                                (bvs' := bvs)
                                                                                                                                                (by
                                                                                                                                                  simp
                                                                                                                                                  omega)
                                                                                                                                                hXsEnv
                                                                                                                                                hBvsEnv
                                                                                                                                                hATrans
                                                                                                                                                hTs
                                                                                                                                                hActuals
                                                                                                                                                hATy)
                                                                                                                                            hTy
                                                                                                                                      · cases op <;> contradiction
                                                                                                          · by_cases hHeadUOp2 :
                                                                                                              ∃ op x y,
                                                                                                                f =
                                                                                                                  Term.UOp2
                                                                                                                    op
                                                                                                                    x
                                                                                                                    y
                                                                                                            · rcases
                                                                                                                hHeadUOp2 with
                                                                                                              ⟨op,
                                                                                                                x,
                                                                                                                y,
                                                                                                                rfl⟩
                                                                                                              cases op
                                                                                                              case pos.extract =>
                                                                                                                exact
                                                                                                                  substitute_simul_apply_extract_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                    x
                                                                                                                    y
                                                                                                                    a
                                                                                                                    xs
                                                                                                                    ts
                                                                                                                    bvs
                                                                                                                    hXsEnv
                                                                                                                    hBvsEnv
                                                                                                                    hTs
                                                                                                                    hFTrans
                                                                                                                    (fun hATrans hATy =>
                                                                                                                      hRec
                                                                                                                        (G := a)
                                                                                                                        (bvs' := bvs)
                                                                                                                        (by
                                                                                                                          simp
                                                                                                                          omega)
                                                                                                                        hXsEnv
                                                                                                                        hBvsEnv
                                                                                                                        hATrans
                                                                                                                        hTs
                                                                                                                        hActuals
                                                                                                                        hATy)
                                                                                                                    hTy
                                                                                                              case pos.re_loop =>
                                                                                                                exact
                                                                                                                  substitute_simul_apply_re_loop_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                    x
                                                                                                                    y
                                                                                                                    a
                                                                                                                    xs
                                                                                                                    ts
                                                                                                                    bvs
                                                                                                                    hXsEnv
                                                                                                                    hBvsEnv
                                                                                                                    hTs
                                                                                                                    hFTrans
                                                                                                                    (fun hATrans hATy =>
                                                                                                                      hRec
                                                                                                                        (G := a)
                                                                                                                        (bvs' := bvs)
                                                                                                                        (by
                                                                                                                          simp
                                                                                                                          omega)
                                                                                                                        hXsEnv
                                                                                                                        hBvsEnv
                                                                                                                        hATrans
                                                                                                                        hTs
                                                                                                                        hActuals
                                                                                                                        hATy)
                                                                                                                    hTy
                                                                                                              case pos._at_quantifiers_skolemize =>
                                                                                                                exact
                                                                                                                  substitute_simul_apply_quant_skolemize_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                    x
                                                                                                                    y
                                                                                                                    a
                                                                                                                    xs
                                                                                                                    ts
                                                                                                                    bvs
                                                                                                                    hXsEnv
                                                                                                                    hBvsEnv
                                                                                                                    hTs
                                                                                                                    hEntryTypes
                                                                                                                    hFTrans
                                                                                                                    (fun hATrans hATy =>
                                                                                                                      hRec
                                                                                                                        (G := a)
                                                                                                                        (bvs' := bvs)
                                                                                                                        (by
                                                                                                                          simp
                                                                                                                          omega)
                                                                                                                        hXsEnv
                                                                                                                        hBvsEnv
                                                                                                                        hATrans
                                                                                                                        hTs
                                                                                                                        hActuals
                                                                                                                        hATy)
                                                                                                                    hTy
                                                                                                              case pos._at_const =>
                                                                                                                exact
                                                                                                                  substitute_simul_apply_at_const_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                    x
                                                                                                                    y
                                                                                                                    a
                                                                                                                    xs
                                                                                                                    ts
                                                                                                                    bvs
                                                                                                                    hXsEnv
                                                                                                                    hBvsEnv
                                                                                                                    hTs
                                                                                                                    hEntryTypes
                                                                                                                    hFTrans
                                                                                                                    (fun hATrans hATy =>
                                                                                                                      hRec
                                                                                                                        (G := a)
                                                                                                                        (bvs' := bvs)
                                                                                                                        (by
                                                                                                                          simp
                                                                                                                          omega)
                                                                                                                        hXsEnv
                                                                                                                        hBvsEnv
                                                                                                                        hATrans
                                                                                                                        hTs
                                                                                                                        hActuals
                                                                                                                        hATy)
                                                                                                                    hTy
                                                                                                            · by_cases hHeadUOp3 :
                                                                                                                ∃ op x y z,
                                                                                                                  f =
                                                                                                                    Term.UOp3
                                                                                                                      op
                                                                                                                      x
                                                                                                                      y
                                                                                                                      z
                                                                                                              · rcases
                                                                                                                  hHeadUOp3 with
                                                                                                                ⟨op,
                                                                                                                  x,
                                                                                                                  y,
                                                                                                                  z,
                                                                                                                  rfl⟩
                                                                                                                cases op
                                                                                                                case pos._at_re_unfold_pos_component =>
                                                                                                                  exact
                                                                                                                    False.elim
                                                                                                                      (false_of_apply_uop3_re_unfold_pos_component_has_smt_translation
                                                                                                                        x
                                                                                                                        y
                                                                                                                        z
                                                                                                                        a
                                                                                                                        hFTrans)
                                                                                                                case pos._at_witness_string_length =>
                                                                                                                  exact
                                                                                                                    substitute_simul_apply_witness_string_length_preserves_type_and_translation_of_typeof_ne_stuck
                                                                                                                      x
                                                                                                                      y
                                                                                                                      z
                                                                                                                      a
                                                                                                                      xs
                                                                                                                      ts
                                                                                                                      bvs
                                                                                                                      hXsEnv
                                                                                                                      hBvsEnv
                                                                                                                      hTs
                                                                                                                      hEntryTypes
                                                                                                                      hFTrans
                                                                                                                      (fun hATrans hATy =>
                                                                                                                        hRec
                                                                                                                          (G := a)
                                                                                                                          (bvs' := bvs)
                                                                                                                          (by
                                                                                                                            simp
                                                                                                                            omega)
                                                                                                                          hXsEnv
                                                                                                                          hBvsEnv
                                                                                                                          hATrans
                                                                                                                          hTs
                                                                                                                          hActuals
                                                                                                                          hATy)
                                                                                                                      hTy
                                                                                                              · by_cases hHeadStuck :
                                                                                                                  f =
                                                                                                                    Term.Stuck
                                                                                                                · subst f
                                                                                                                  exact
                                                                                                                    False.elim
                                                                                                                      (false_of_apply_stuck_has_smt_translation
                                                                                                                        a
                                                                                                                        hFTrans)
                                                                                                                · rcases hHeadSpecial with hUOp | hRest
                                                                                                                  · rcases hUOp with ⟨op, hOpEq⟩
                                                                                                                    exact
                                                                                                                      False.elim
                                                                                                                        (false_of_exhausted_unary_uop_apply_has_smt_translation
                                                                                                                          hOpEq
                                                                                                                          hFTrans
                                                                                                                          hHeadNot
                                                                                                                          hHeadDistinct
                                                                                                                          hHeadPurify
                                                                                                                          hHeadToReal
                                                                                                                          hHeadToInt
                                                                                                                          hHeadIsInt
                                                                                                                          hHeadAbs
                                                                                                                          hHeadUneg
                                                                                                                          hHeadPow2
                                                                                                                          hHeadLog2
                                                                                                                          hHeadIntIspow2
                                                                                                                          hHeadIntDivByZero
                                                                                                                          hHeadModByZero
                                                                                                                          hHeadBvsize
                                                                                                                          hHeadBvnot
                                                                                                                          hHeadBvneg
                                                                                                                          hHeadBvnego
                                                                                                                          hHeadBvredand
                                                                                                                          hHeadBvredor
                                                                                                                          hHeadStrLen
                                                                                                                          hHeadStrRev
                                                                                                                          hHeadStrToLower
                                                                                                                          hHeadStrToUpper
                                                                                                                          hHeadStrToCode
                                                                                                                          hHeadStrFromCode
                                                                                                                          hHeadStrIsDigit
                                                                                                                          hHeadStrToInt
                                                                                                                          hHeadStrFromInt
                                                                                                                          hHeadStrToRe
                                                                                                                          hHeadStringsStoiNonDigit
                                                                                                                          hHeadReMult
                                                                                                                          hHeadRePlus
                                                                                                                          hHeadReOpt
                                                                                                                          hHeadReComp
                                                                                                                          hHeadSeqUnit
                                                                                                                          hHeadSetSingleton
                                                                                                                          hHeadSetChoose
                                                                                                                          hHeadSetIsEmpty
                                                                                                                          hHeadSetIsSingleton
                                                                                                                          hHeadQDivByZero
                                                                                                                          hHeadUbvToInt
                                                                                                                          hHeadSbvToInt)
                                                                                                                  · rcases hRest with hUOp1 | hRest
                                                                                                                    · rcases hUOp1 with ⟨op, x, hOpEq⟩
                                                                                                                      exact False.elim (hHeadUOp1 ⟨op, x, hOpEq⟩)
                                                                                                                    · rcases hRest with hUOp2 | hRest
                                                                                                                      · rcases hUOp2 with ⟨op, x, y, hOpEq⟩
                                                                                                                        exact False.elim (hHeadUOp2 ⟨op, x, y, hOpEq⟩)
                                                                                                                      · rcases hRest with hUOp3 | hRest
                                                                                                                        · rcases hUOp3 with ⟨op, w, x, y, hOpEq⟩
                                                                                                                          exact False.elim (hHeadUOp3 ⟨op, w, x, y, hOpEq⟩)
                                                                                                                        · rcases hRest with hDtSel | hStuck
                                                                                                                          · rcases hDtSel with ⟨s, d, i, j, hDtSelEq⟩
                                                                                                                            exact False.elim (hHeadDtSel ⟨s, d, i, j, hDtSelEq⟩)
                                                                                                                          · exact False.elim (hHeadStuck hStuck)
                  · have hHeadNotApply : ∀ g x, f ≠ Term.Apply g x := by
                      intro g x hEq
                      exact hHeadApply ⟨g, x, hEq⟩
                    have hHeadNotVar : ∀ name T, f ≠ Term.Var name T := by
                      intro name T hEq
                      exact hHeadVar ⟨name, T, hEq⟩
                    have hNoUOp : ∀ op, f ≠ Term.UOp op := by
                      intro op hEq
                      exact hHeadSpecial (Or.inl ⟨op, hEq⟩)
                    have hNoUOp1 :
                        ∀ op x, f ≠ Term.UOp1 op x := by
                      intro op x hEq
                      exact hHeadSpecial (Or.inr (Or.inl ⟨op, x, hEq⟩))
                    have hNoUOp2 :
                        ∀ op x y, f ≠ Term.UOp2 op x y := by
                      intro op x y hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inl ⟨op, x, y, hEq⟩)))
                    have hNoUOp3 :
                        ∀ op w x y, f ≠ Term.UOp3 op w x y := by
                      intro op w x y hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨op, w, x, y, hEq⟩))))
                    have hNoDtSel :
                        ∀ s d i j, f ≠ Term.DtSel s d i j := by
                      intro s d i j hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨s, d, i, j, hEq⟩)))))
                    have hHeadNotStuck : f ≠ Term.Stuck := by
                      intro hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hEq)))))
                    have hNotBinder :
                        ∀ q v vs,
                          f ≠
                            Term.Apply q
                              (Term.Apply (Term.Apply Term.__eo_List_cons v)
                                vs) := by
                      intro q v vs hEq
                      exact hHeadNotApply q
                        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                        hEq
                    have hSmtConds :=
                      generic_atom_head_smt_apply_conditions
                        f a hHeadNotApply hHeadNotVar hNoUOp hNoUOp1
                        hNoUOp2 hNoUOp3
                        (fun s d i hEq => hHeadDtCons ⟨s, d, i, hEq⟩)
                        hNoDtSel hHeadNotStuck
                        (fun i U hEq => hHeadUConst ⟨i, U, hEq⟩)
                    exact
                      substitute_simul_apply_atom_generic_preserves_type_and_translation_of_typeof_ne_stuck
                        f a xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes
                        hHeadNotApply hHeadNotVar hHeadNotStuck hNotBinder
                        hSmtConds.1 hSmtConds.2.1 hSmtConds.2.2 hFTrans
                        (fun hATrans hATy =>
                          hRec
                            (G := a) (bvs' := bvs)
                            (by
                              simp
                              omega)
                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                        hTy
      · by_cases hVar : ∃ name T, F = Term.Var name T
        · rcases hVar with ⟨name, T, rfl⟩
          exact ⟨
            SubstituteSupport.substitute_simul_rec_var_any_typeof_eq
              name T xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes hFTrans,
            substitute_simul_var_any_has_smt_translation_of_typeof_ne_stuck
              name T xs ts bvs hXsEnv hBvsEnv hFTrans hTs hTy⟩
        · by_cases hStuck : F = Term.Stuck
          · subst F
            exact False.elim
              ((RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans) rfl)
          · have hNotApply : ∀ f a, F ≠ Term.Apply f a := by
              intro f a hEq
              exact hApply ⟨f, a, hEq⟩
            have hNotVar : ∀ name T, F ≠ Term.Var name T := by
              intro name T hEq
              exact hVar ⟨name, T, hEq⟩
            exact ⟨
              SubstituteSupport.substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
                _ xs ts bvs hXsEnv hBvsEnv hTs
                hNotApply hNotVar hStuck
                hTy,
              substitute_simul_atom_has_smt_translation_of_typeof_ne_stuck
                _ xs ts bvs hXsEnv hBvsEnv hTs
                hNotApply hNotVar hStuck
                hFTrans hTy⟩

private theorem substitute_simul_false_binder_preserves
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof
      (substResult false
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs) ≠ Term.Stuck)
    (hRec : SubstitutionPreservationRec false
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) xs ts) :
    SubstitutionPreservationResult false
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
      xs ts bvs := by
  let binders := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
  let bodySub :=
    __substitute_simul_rec (Term.Boolean false) a xs ts
      (__eo_list_concat Term.__eo_List_cons binders bvs)
  have hFTrans' :
      eoHasSmtTranslation (Term.Apply (Term.Apply q binders) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
      binders] using hFTrans
  have hQ :
      q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hFTrans'
  rcases eo_var_env_of_list_branch_has_smt_translation hFTrans' with
    ⟨binderVars, hBinderEnv⟩
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q binders) a) xs ts bvs =
        __eo_mk_apply (Term.Apply q binders) bodySub := by
    simpa [binders, bodySub] using
      substitute_simul_quant_eq_of_typeof_ne_stuck
        q v vs a xs ts bvs hXsEnv hBvsEnv hTs hTy
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.Apply q binders) bodySub) ≠
        Term.Stuck := by
    have hTyRaw :
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false)
              (Term.Apply (Term.Apply q binders) a) xs ts bvs) ≠
          Term.Stuck := by
      simpa [substResult, binders] using hTy
    rwa [hSubstEq] at hTyRaw
  have hMk :
      __eo_mk_apply (Term.Apply q binders) bodySub =
        Term.Apply (Term.Apply q binders) bodySub :=
    eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
      q binders bodySub hTyMk
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply q binders) bodySub) ≠
        Term.Stuck := by
    rwa [hMk] at hTyMk
  have hBodyBool : __eo_typeof bodySub = Term.Bool :=
    eo_typeof_body_bool_of_quant_type_ne_stuck
      hQ hBinderEnv hTyApply
  have hBodyTy : __eo_typeof bodySub ≠ Term.Stuck := by
    rw [hBodyBool]
    intro h
    cases h
  have hBodyTrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using
        body_has_smt_translation_of_list_branch_has_smt_translation
          hFTrans'
  have hBvsEnv' :
      EoVarEnvPerm
        (__eo_list_concat Term.__eo_List_cons binders bvs)
        (binderVars.reverse ++ bvsVars) :=
    EoVarEnvPerm.concat_rev hBinderEnv hBvsEnv
  have hBodyType :
      __eo_typeof bodySub = __eo_typeof a := by
    simpa [bodySub] using
      (hRec
        (G := a)
        (bvs' := __eo_list_concat Term.__eo_List_cons binders bvs)
        (by
          simp
          omega)
        hXsEnv hBvsEnv' hBodyTrans hTs hActuals
        (by simpa [bodySub] using hBodyTy)).1
  have hBodySubTrans :
      RuleProofs.eo_has_smt_translation bodySub := by
    simpa [bodySub] using
      (hRec
        (G := a)
        (bvs' := __eo_list_concat Term.__eo_List_cons binders bvs)
        (by
          simp
          omega)
        hXsEnv hBvsEnv' hBodyTrans hTs hActuals
        (by simpa [bodySub] using hBodyTy)).2
  refine ⟨?_, ?_⟩
  · simpa [substResult, binders, bodySub] using
      SubstituteSupport.substitute_simul_quant_typeof_eq_of_typeof_ne_stuck
        q v vs a xs ts bvs hXsEnv hBvsEnv hTs
        hFTrans hBodyType hTy
  · simpa [substResult, binders, bodySub] using
      substitute_simul_quant_has_smt_translation_of_typeof_ne_stuck
        q v vs a xs ts bvs hXsEnv hBvsEnv hTs
        hFTrans hBodySubTrans hTy

/--
Combined substitution preservation under an arbitrary bound-variable
accumulator.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof (substResult false F xs ts bvs) ≠ Term.Stuck) :
    SubstitutionPreservationResult false F xs ts bvs :=
  substitute_simul_preserves_type_and_translation_with_binder_lt
    (sizeOf F + 1) F xs ts bvs
    (fun q v vs a bvs =>
      substitute_simul_false_binder_preserves q v vs a xs ts bvs)
    (by omega) hXsEnv hBvsEnv hFTrans hTs hActuals hTy

/--
Instantiate-facing combined preservation for a Boolean-typed substitution result.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
      __eo_typeof F ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) := by
  have hBodyTrans :
      RuleProofs.eo_has_smt_translation F :=
    forall_body_has_smt_translation_of_has_smt_translation xs F hForall
  rcases forall_binders_env_of_has_smt_translation xs F hForall with
    ⟨_binderVars, hXsEnv⟩
  exact
    substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
      F xs ts Term.__eo_List_nil
      (EoVarEnvPerm.of_exact hXsEnv)
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hBodyTrans hTs hActuals
      (by
        intro hStuck
        rw [hStuck] at hTy
        cases hTy)

end SubstitutePreservationSupport
