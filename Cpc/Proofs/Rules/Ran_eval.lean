module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport
public import Cpc.Proofs.RuleSupport.CoveringsSupport
import all Cpc.Proofs.RuleSupport.CoveringsSupport

open Eo
open SmtEval
open Smtm
open CoveringsProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- What a successful `ran_eval` step was given, and what it concludes. -/
private theorem prog_ran_eval_inv (x r p X1 X2 : Term)
    (h : __eo_prog_ran_eval x r p (Proof.pf X1) (Proof.pf X2) ≠ Term.Stuck) :
    ∃ q, X1 = Term.Apply (Term.UOp1 UserOp1._at_is_root q) r ∧
      __cov_lit_poly X2 = p ∧
      __cov_lit_holds X2 (Term.Rational (native_mk_rational 0 1)) = Term.Boolean false ∧
      __upoly_to_list (__upoly_of_term x p) = q ∧
      __cov_lit_poly X2 ≠ Term.Stuck ∧ __upoly_to_list (__upoly_of_term x p) ≠ Term.Stuck ∧
      x ≠ Term.Stuck ∧
      __eo_prog_ran_eval x r p (Proof.pf X1) (Proof.pf X2) =
        Term.Apply (Term.UOp UserOp.not) (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) r) := by
  unfold __eo_prog_ran_eval at h ⊢
  split at h
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · rename_i x r p _ _ _ _ _ q r2 F hx hr hp hX1 hX2
    cases hX1
    cases hX2
    obtain ⟨h1, h1b⟩ := eo_requires_eq_body h
    rw [h1b] at h
    have hn2 := eo_requires_left_ne_stuck h
    obtain ⟨h2, h2b⟩ := eo_requires_eq_body h
    rw [h2b] at h
    obtain ⟨h3, h3b⟩ := eo_requires_eq_body h
    rw [h3b] at h
    have hn4 := eo_requires_left_ne_stuck h
    obtain ⟨h4, h4b⟩ := eo_requires_eq_body h
    have hr2 : r2 = r := by
      have hrS : r2 ≠ Term.Stuck := by rintro rfl; cases r <;> simp_all [__eo_eq]
      cases r2 <;> cases r <;> simp_all [__eo_eq, native_teq]
    subst hr2
    exact ⟨q, rfl, h2, h3, h4, hn2, hn4, hx, by rw [h1b, h2b, h3b, h4b]⟩
  · exact absurd rfl h

private theorem eo_typeof_not_eq_bool (x r : Term)
    (hTy : __eo_typeof (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) r)) = Term.Bool) :
    __eo_typeof x = __eo_typeof r := by
  have hNot : __eo_typeof_not
      (__eo_typeof_eq (__eo_typeof x) (__eo_typeof r)) = Term.Bool := hTy
  have hEqTy : __eo_typeof_eq (__eo_typeof x) (__eo_typeof r) = Term.Bool := by
    revert hNot; generalize __eo_typeof_eq (__eo_typeof x) (__eo_typeof r) = T
    intro hNot; cases T <;> simp_all [__eo_typeof_not]
  exact (RuleProofs.eo_typeof_eq_bool_same _ _ hEqTy).1

/-- The conclusion of `ran_eval` is a Boolean, and holds in every model of its premises. -/
private theorem ran_eval_sound (M : SmtModel) (hM : model_wf M) (x r p X1 X2 : Term)
    (hxT : RuleProofs.eo_has_smt_translation x)
    (hX1B : RuleProofs.eo_has_bool_type X1)
    (hTy : __eo_typeof (__eo_prog_ran_eval x r p (Proof.pf X1) (Proof.pf X2)) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_ran_eval x r p (Proof.pf X1) (Proof.pf X2)) ∧
    (eo_interprets M X1 true -> eo_interprets M X2 true ->
      eo_interprets M (__eo_prog_ran_eval x r p (Proof.pf X1) (Proof.pf X2)) true) := by
  have hProg := term_ne_stuck_of_typeof_bool hTy
  obtain ⟨q, rfl, hLit, hHolds, hList, hLitNS, hListNS, hx, hEq⟩ :=
    prog_ran_eval_inv x r p X1 X2 hProg
  rw [hEq] at hTy ⊢
  have hrR := is_root_typed q r hX1B
  have hxR : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation x hxT, eo_typeof_not_eq_bool x r hTy,
      ← TranslationProofs.eo_to_smt_typeof_matches_translation r (by rw [hrR]; simp), hrR]
  have hEqBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) r) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x r (hxR.trans hrR.symm) (by rw [hxR]; simp)
  refine ⟨RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqBool, fun hX1 hX2 => ?_⟩
  -- the literal
  obtain ⟨neg, rel, p', z, rfl, hz, hp'⟩ := cov_lit_poly_shape X2 hLitNS
  rw [hLit] at hp'
  subst hp'
  obtain ⟨hpA, hSem⟩ := covLit_true M hM neg rel p z hz hX2
  have hNot0 : ¬ litSem neg rel 0 := by
    have hz0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
    rw [hz0, cov_lit_holds_rat] at hHolds
    simpa using hHolds
  -- the polynomial
  have hOT : __upoly_of_term x p ≠ Term.Stuck := by
    intro hs; rw [hs] at hListNS; exact hListNS (by simp [__upoly_to_list])
  obtain ⟨f, ⟨l, hl, hfl⟩, hpf⟩ :=
    upoly_of_term_den (covDen_ofTermVal M hM) x p hx hpA hOT
  have hq : RatList q l := hList ▸ upoly_to_list_of_wf hl
  -- the root
  obtain ⟨_, hroot⟩ := is_root_true M hM hq r hX1
  have hNe : covDen M x ≠ covDen M r := by
    intro h
    apply hNot0
    rw [hpf, ← hfl, h, hroot] at hSem
    exact hSem
  apply RuleProofs.eo_interprets_not_of_false
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_false _ _ hEqBool ?_
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) r) =
    SmtTerm.eq (__eo_to_smt x) (__eo_to_smt r) by rfl]
  simp [__smtx_model_eval, eval_of_real M hM x hxR, eval_of_real M hM r hrR,
    __smtx_model_eval_eq, native_veq, hNe]

public theorem cmd_step_ran_eval_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ran_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ran_eval args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ran_eval args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ran_eval args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨x, _ | ⟨r, _ | ⟨p, _ | ⟨_, _⟩⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨n1, _ | ⟨n2, _ | ⟨_, _⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hxT : RuleProofs.eo_has_smt_translation x := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
  have hTy : __eo_typeof (__eo_prog_ran_eval x r p
      (Proof.pf (__eo_state_proven_nth s n1)) (Proof.pf (__eo_state_proven_nth s n2))) =
        Term.Bool := hResultTy
  have hSound := ran_eval_sound M hM x r p _ _ hxT
    (hPremisesBool _ (by simp [premiseTermList])) hTy
  refine ⟨fun hTrue => ?_, ?_⟩
  · exact hSound.2 (hTrue _ (by simp [premiseTermList])) (hTrue _ (by simp [premiseTermList]))
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hSound.1
