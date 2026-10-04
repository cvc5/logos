module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericOps
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericOps
public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySetHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySetHelpers

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace SubstitutePreservationSupport

theorem substitute_simul_set_insert_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_insert) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) x) y) xs ts bvs) ≠
        Term.Stuck)
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.set_insert x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder
      hFTrans hTy
      (fun h =>
        set_insert_args_have_smt_translation_of_non_none h)
      (fun X Y hApp => by
        change __eo_typeof_set_insert (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact eo_typeof_set_insert_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_set_insert (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_set_insert (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt X)) (__eo_to_smt Y)) ≠
            SmtType.None
        change __eo_typeof_set_insert (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact
          smt_set_insert_non_none_of_eo_typeof_set_insert_ne_stuck
            X Y hXTrans hYTrans hApp)
      hRecX hRecY

end SubstitutePreservationSupport
