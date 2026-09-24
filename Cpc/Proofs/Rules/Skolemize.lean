module

public import Cpc.Proofs.RuleSupport.SkolemizeSupport
import all Cpc.Proofs.RuleSupport.SkolemizeSupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

open SkolemizeRule in
/--
`skolemize` rule properties.

Boilerplate (arg/premise destructuring, `Stuck` discharge) mirrors
`cmd_step_instantiate_properties`; the guards are reflected into key
distinctness and body closedness, the skolem list is typed against the
binders, and the soundness obligation delegates to
`SkolemizeRule.skolemize_sound`.
-/
public theorem cmd_step_skolemize_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolemize args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.skolemize args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolemize args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.skolemize args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | cons a1 args =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              let prem : Term := __eo_state_proven_nth s n1
              change __eo_prog_skolemize (Proof.pf prem) ≠ Term.Stuck at hProg
              obtain ⟨x, G, hPremShape, hClosedGuard, hSetofGuard, hResEq⟩ :=
                prog_skolemize_shape prem hProg
              -- The premise is Bool-typed, hence the quantifier translates.
              have hPremBool : RuleProofs.eo_has_bool_type prem :=
                hPremisesBool prem (by simp [prem, premiseTermList])
              rw [hPremShape] at hPremBool
              have hForallBool :
                  __smtx_typeof (__eo_to_smt (forallTerm x G)) = SmtType.Bool :=
                smtx_typeof_not_arg_eq_bool (__eo_to_smt (forallTerm x G))
                  (show __smtx_typeof
                      (SmtTerm.not (__eo_to_smt (forallTerm x G))) =
                    SmtType.Bool from hPremBool)
              have hForallTrans :
                  RuleProofs.eo_has_smt_translation (forallTerm x G) := by
                show __smtx_typeof (__eo_to_smt (forallTerm x G)) ≠ SmtType.None
                rw [hForallBool]
                intro h
                cases h
              have hxNonNil : x ≠ Term.__eo_List_nil :=
                forall_binders_non_nil_of_has_smt_translation x G hForallTrans
              obtain ⟨vars, hEnv⟩ :=
                forall_binders_env_of_has_smt_translation x G hForallTrans
              have hWfAll :
                  ∀ p ∈ vars, __smtx_type_wf (__eo_to_smt_type p.2) = true := by
                intro p hp
                exact forall_binder_types_wf_of_has_smt_translation
                  hForallTrans hEnv p.1 p.2 (by simpa using hp)
              have hGBool : __smtx_typeof (__eo_to_smt G) = SmtType.Bool :=
                forall_body_has_bool_type_of_has_smt_translation x G hForallTrans
              have hHBool :
                  __smtx_typeof (SmtTerm.not (__eo_to_smt G)) = SmtType.Bool := by
                rw [typeof_not_eq, hGBool]
                simp [native_ite, native_Teq]
              have hFTrans : RuleProofs.eo_has_smt_translation (notTerm G) := by
                show __smtx_typeof (__eo_to_smt (notTerm G)) ≠ SmtType.None
                rw [eo_to_smt_not_eq, hHBool]
                intro h
                cases h
              -- Guard reflections.
              have hD : DistinctList (smtKeys vars) :=
                distinct_smtKeys hWfAll (distinct_of_setof_guard hEnv hSetofGuard)
              have hClosedG : SmtTermClosedIn (smtKeys vars) (__eo_to_smt G) :=
                body_closedIn_of_guard hEnv
                  (by
                    simpa [RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hForallTrans)
                  hClosedGuard
              have hClosedH :
                  SmtTermClosedIn (smtKeys vars)
                    (SmtTerm.not (__eo_to_smt G)) := hClosedG
              -- The skolem list is typed against the binders.
              have hEntryFacts := skolem_entry_facts x G vars hEnv hWfAll hHBool
              have hActuals : SubstActualsHaveSmtTypes x
                  (mkSkolemList (forallTerm x G) vars 0) :=
                substActuals_skolems (forallTerm x G) hEnv 0 hEntryFacts
              have hTs : EoListAllHaveSmtTranslation
                  (mkSkolemList (forallTerm x G) vars 0) :=
                eoListAll_skolems (forallTerm x G) vars 0
                  (fun j hj => (hEntryFacts j hj).2.1)
              -- Rewrite the checker's skolem list into its mirror.
              have hSkolemsEq :
                  __mk_skolems x (forallTerm x G) (Term.Numeral 0) =
                    mkSkolemList (forallTerm x G) vars 0 :=
                mk_skolems_eq_mkSkolemList x G hEnv 0
              rw [hSkolemsEq] at hResEq
              -- The program result has EO Bool type.
              have hSubstTypeof :
                  __eo_typeof
                    (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
                      (mkSkolemList (forallTerm x G) vars 0)
                      Term.__eo_List_nil) = Term.Bool := by
                change __eo_typeof (__eo_prog_skolemize (Proof.pf prem)) =
                  Term.Bool at hResultTy
                rw [hResEq] at hResultTy
                exact hResultTy
              -- Combined type/translation preservation for the substitution.
              have hResPreserves :
                  __eo_typeof
                      (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
                        (mkSkolemList (forallTerm x G) vars 0)
                        Term.__eo_List_nil) = __eo_typeof (notTerm G) ∧
                    RuleProofs.eo_has_smt_translation
                      (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
                        (mkSkolemList (forallTerm x G) vars 0)
                        Term.__eo_List_nil) :=
                SubstitutePreservationSupport.substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
                  (notTerm G) x (mkSkolemList (forallTerm x G) vars 0)
                  Term.__eo_List_nil
                  (EoVarEnvPerm.of_exact hEnv)
                  (EoVarEnvPerm.of_exact EoVarEnv.nil)
                  hFTrans hTs hActuals
                  (by
                    rw [hSubstTypeof]
                    intro h
                    cases h)
              have hResBool :
                  RuleProofs.eo_has_bool_type
                    (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
                      (mkSkolemList (forallTerm x G) vars 0)
                      Term.__eo_List_nil) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type _
                  hResPreserves.2 hSubstTypeof
              refine ⟨?_, ?_⟩
              · -- facts_of_true
                intro hEvid
                have hPremTrue : eo_interprets M prem true :=
                  hEvid prem (by simp [prem, premiseTermList])
                rw [hPremShape] at hPremTrue
                change eo_interprets M
                  (__eo_prog_skolemize (Proof.pf prem)) true
                rw [hResEq]
                exact skolemize_sound M hM x G vars hEnv hxNonNil hWfAll hD
                  hClosedH hPremTrue hFTrans hTs hActuals hResBool
              · -- has_smt_translation
                change RuleProofs.eo_has_smt_translation
                  (__eo_prog_skolemize (Proof.pf prem))
                rw [hResEq]
                exact hResPreserves.2
