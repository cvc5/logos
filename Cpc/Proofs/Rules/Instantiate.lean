
module

public import Cpc.Proofs.RuleSupport.InstantiateSupport
import all Cpc.Proofs.RuleSupport.InstantiateSupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/--
`instantiate` rule properties.

Boilerplate (arg/premise destructuring, `Stuck` discharge, translation
obligation) mirrors `BooleanElimSupport.cmd_step_and_elim_properties`; the
soundness obligation delegates to `InstantiateRule.instantiate_sound`.
-/
public theorem cmd_step_instantiate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.instantiate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.instantiate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.instantiate args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.instantiate args premises ≠ Term.Stuck :=
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  -- The single premise term is `prem`; the program result is the substitution.
                  let prem : Term := __eo_state_proven_nth s n1
                  change __eo_prog_instantiate a1 (Proof.pf prem) ≠ Term.Stuck at hProg
                  -- Shape: prem is a `forall`, result is the substitution.
                  obtain ⟨xs, F, hPremShape, hIsInst, hResEq⟩ :=
                    InstantiateRule.prog_instantiate_shape a1 prem hProg
                  -- The premise (the forall) is Bool-typed, hence translatable.
                  have hPremBool : RuleProofs.eo_has_bool_type prem :=
                    hPremisesBool prem (by simp [prem, premiseTermList])
                  rw [hPremShape] at hPremBool
                  -- The premise (the forall) has an SMT translation.
                  have hWf :
                      RuleProofs.eo_has_smt_translation
                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) :=
                    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hPremBool
                  -- The instantiate argument is a list of translatable actuals.
                  have hActualsTrans : EoListAllHaveSmtTranslation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOkMask,
                      argTranslationOkMasked] using hCmdTrans
                  -- The binder list reflects an EO variable environment with
                  -- well-formed SMT types, and the `__is_instantiation` guard
                  -- certifies the actuals are correctly typed against it.
                  obtain ⟨binderVars, hXsEnv⟩ :=
                    SubstituteTranslatabilitySupport.forall_binders_env_of_has_smt_translation xs F hWf
                  have hBinderWf :
                      ∀ s T, (s, T) ∈ binderVars ->
                        __smtx_type_wf (__eo_to_smt_type T) = true :=
                    SubstituteTranslatabilitySupport.forall_binder_types_wf_of_has_smt_translation
                      hWf hXsEnv
                  have hActuals : SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes xs a1 :=
                    InstantiateRule.substActualsHaveSmtTypes_of_is_instantiation
                      hXsEnv hBinderWf hActualsTrans hIsInst
                  -- The program result has EO Bool type.
                  have hSubstTypeof :
                      __eo_typeof
                        (__substitute_simul_rec (Term.Boolean false) F xs a1
                          Term.__eo_List_nil) = Term.Bool := by
                    change __eo_typeof (__eo_prog_instantiate a1 (Proof.pf prem)) =
                      Term.Bool at hResultTy
                    rw [hResEq] at hResultTy
                    exact hResultTy
                  -- The result preservation facts come from the combined theorem.
                  have hResPreserves :
                      __eo_typeof
                          (__substitute_simul_rec (Term.Boolean false) F xs a1
                            Term.__eo_List_nil) =
                        __eo_typeof F ∧
                        RuleProofs.eo_has_smt_translation
                          (__substitute_simul_rec (Term.Boolean false) F xs a1
                            Term.__eo_List_nil) :=
                    SubstitutePreservationSupport.substitute_simul_preserves_type_and_translation_of_typeof_bool
                      F xs a1 hWf hActualsTrans hActuals hSubstTypeof
                  -- Package the combined preservation result as SMT Bool-typed.
                  have hResBool :
                      RuleProofs.eo_has_bool_type
                        (__substitute_simul_rec (Term.Boolean false) F xs a1
                          Term.__eo_List_nil) :=
                    RuleProofs.eo_typeof_bool_implies_has_bool_type
                      (__substitute_simul_rec (Term.Boolean false) F xs a1
                        Term.__eo_List_nil)
                      hResPreserves.2
                      hSubstTypeof
                  refine ⟨?_, ?_⟩
                  · -- facts_of_true
                    intro hEvid
                    have hPremTrue : eo_interprets M prem true :=
                      hEvid prem (by simp [prem, premiseTermList])
                    rw [hPremShape] at hPremTrue
                    change eo_interprets M (__eo_prog_instantiate a1 (Proof.pf prem)) true
                    rw [hResEq]
                    exact InstantiateRule.instantiate_sound M hM xs F a1
                      hPremTrue hWf hActualsTrans hActuals hResBool
                  · -- has_smt_translation
                    change RuleProofs.eo_has_smt_translation
                      (__eo_prog_instantiate a1 (Proof.pf prem))
                    rw [hResEq]
                    exact hResPreserves.2
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
