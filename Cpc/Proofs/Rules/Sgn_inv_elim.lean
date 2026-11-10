module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoveringsSupport
import all Cpc.Proofs.RuleSupport.CoveringsSupport

open Eo
open SmtEval
open Smtm
open CoveringsProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_eq_true {a b : Term} (h : __eo_eq a b = Term.Boolean true) : b = a := by
  cases a <;> cases b <;> simp_all [__eo_eq, native_teq]

/-- What a successful `sgn_inv_elim` step was given, and what it concludes. -/
private theorem prog_sgn_inv_elim_inv (x p s l r X1 X2 : Term)
    (h : __eo_prog_sgn_inv_elim x p s l r (Proof.pf X1) (Proof.pf X2) ≠ Term.Stuck) :
    ∃ q, X1 = Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv q) l) r ∧
      __cov_lit_poly X2 = p ∧ __cov_lit_poly X2 ≠ Term.Stuck ∧
      __upoly_to_list (__upoly_of_term x p) = q ∧
      __upoly_to_list (__upoly_of_term x p) ≠ Term.Stuck ∧
      __eo_is_q s = Term.Boolean true ∧
      __cov_bound_lt l s = Term.Boolean true ∧
      __cov_bound_lt s r = Term.Boolean true ∧
      __cov_lit_holds X2 (__upoly_eval (__upoly_of_term x p) s) = Term.Boolean false ∧
      x ≠ Term.Stuck ∧
      __eo_prog_sgn_inv_elim x p s l r (Proof.pf X1) (Proof.pf X2) =
        __eo_ite (__eo_is_eq (__mk_cover_piece x l r) (Term.Boolean true)) (Term.Boolean false)
          (__eo_mk_apply (Term.UOp UserOp.not) (__mk_cover_piece x l r)) := by
  unfold __eo_prog_sgn_inv_elim at h ⊢
  split at h
  all_goals try exact absurd rfl h
  rename_i x p s l r _ _ _ _ _ _ _ q l2 r2 F hx _ _ _ _ hX1 hX2
  cases hX1
  cases hX2
  simp only at h ⊢
  obtain ⟨h1, h1b⟩ := eo_requires_eq_body h
  rw [h1b] at h
  have hn2 := eo_requires_left_ne_stuck h
  obtain ⟨h2, h2b⟩ := eo_requires_eq_body h
  rw [h2b] at h
  have hn3 := eo_requires_left_ne_stuck h
  obtain ⟨h3, h3b⟩ := eo_requires_eq_body h
  rw [h3b] at h
  obtain ⟨h4, h4b⟩ := eo_requires_eq_body h
  rw [h4b] at h
  obtain ⟨h5, h5b⟩ := eo_requires_eq_body h
  rw [h5b] at h
  obtain ⟨h6, h6b⟩ := eo_requires_eq_body h
  rw [h6b] at h
  obtain ⟨h7, h7b⟩ := eo_requires_eq_body h
  obtain ⟨hl, hr⟩ := eo_and_true_inv h1
  have hl' := eo_eq_true hl
  have hr' := eo_eq_true hr
  subst hl' hr'
  exact ⟨q, rfl, h2, hn2, h3, hn3, h4, h5, h6, h7, hx, by
    rw [h1b, h2b, h3b, h4b, h5b, h6b, h7b]⟩

private theorem conclusion_cases (P : Term)
    (h : __eo_ite (__eo_is_eq P (Term.Boolean true)) (Term.Boolean false)
      (__eo_mk_apply (Term.UOp UserOp.not) P) ≠ Term.Stuck) :
    P ≠ Term.Stuck ∧
    ((P = Term.Boolean true ∧ __eo_ite (__eo_is_eq P (Term.Boolean true)) (Term.Boolean false)
        (__eo_mk_apply (Term.UOp UserOp.not) P) = Term.Boolean false) ∨
     (P ≠ Term.Boolean true ∧ __eo_ite (__eo_is_eq P (Term.Boolean true)) (Term.Boolean false)
        (__eo_mk_apply (Term.UOp UserOp.not) P) = Term.Apply (Term.UOp UserOp.not) P)) := by
  have hP : P ≠ Term.Stuck := by
    rintro rfl
    simp [__eo_ite, __eo_is_eq, __eo_mk_apply, native_ite, native_teq, native_and,
      native_not] at h
  refine ⟨hP, ?_⟩
  by_cases hT : P = Term.Boolean true
  · subst hT
    left
    simp [__eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not]
  · right
    refine ⟨hT, ?_⟩
    cases P <;> simp_all [__eo_ite, __eo_is_eq, __eo_mk_apply, native_ite, native_teq,
      native_and, native_not]

private theorem eo_has_bool_type_false : RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  unfold RuleProofs.eo_has_bool_type
  rw [__eo_to_smt.eq_def]
  simp [__smtx_typeof]

/-- The conclusion of `sgn_inv_elim` is a Boolean, and holds in every model of its premises. -/
private theorem sgn_inv_elim_sound (M : SmtModel) (hM : model_wf M) (x p s l r X1 X2 : Term)
    (hxT : RuleProofs.eo_has_smt_translation x)
    (hX1B : RuleProofs.eo_has_bool_type X1)
    (hTy : __eo_typeof (__eo_prog_sgn_inv_elim x p s l r (Proof.pf X1) (Proof.pf X2)) =
      Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sgn_inv_elim x p s l r (Proof.pf X1) (Proof.pf X2)) ∧
    (eo_interprets M X1 true -> eo_interprets M X2 true ->
      eo_interprets M (__eo_prog_sgn_inv_elim x p s l r (Proof.pf X1) (Proof.pf X2)) true) := by
  have hProg := term_ne_stuck_of_typeof_bool hTy
  obtain ⟨q, rfl, hLit, hLitNS, hList, hListNS, hsq, hbl, hbr, hHolds, hx, hEq⟩ :=
    prog_sgn_inv_elim_inv x p s l r X1 X2 hProg
  rw [hEq] at hTy hProg ⊢
  obtain ⟨hlS, hrS⟩ := sgn_inv_typed q l r hX1B
  have hlA : l ≠ Term.UOp UserOp._at__at_cov_minus_inf -> CovArith l := fun hne => by
    rcases hlS with h | h; exact absurd h hne; exact finEnd_covArith h
  have hrA : r ≠ Term.UOp UserOp._at__at_cov_plus_inf -> CovArith r := fun hne => by
    rcases hrS with h | h; exact absurd h hne; exact finEnd_covArith h
  have hcovT : ∀ e, CovArith e -> RuleProofs.eo_has_smt_translation e := by
    intro e he; unfold RuleProofs.eo_has_smt_translation; rcases he with h | h <;> rw [h] <;> simp
  obtain ⟨hPns, hc⟩ := conclusion_cases _ hProg
  -- the premises rule out the piece
  have hcontra : eo_interprets M (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv q) l) r)
      true -> eo_interprets M X2 true ->
      eo_interprets M (__mk_cover_piece x l r) true -> False := by
    intro hX1 hX2 hPT
    have hsq' : ∃ sq, s = Term.Rational sq := by
      cases s <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]
    obtain ⟨sq, rfl⟩ := hsq'
    have hInL := bound_lt_left M hM hlS hbl
    have hInR := bound_lt_right M hM hrS hbr
    rcases piece_true M hM x l r hPns hlA hrA hPT with ⟨hxL, hxR⟩ | ⟨rfl, hlm, hlp, _⟩
    · obtain ⟨neg, rel, p', z, rfl, hz, hp'⟩ := cov_lit_poly_shape _ hLitNS
      rw [hLit] at hp'
      subst hp'
      obtain ⟨hpA, hSem⟩ := covLit_true M hM neg rel p z hz hX2
      have hOT : __upoly_of_term x p ≠ Term.Stuck := by
        intro hs; rw [hs] at hListNS; exact hListNS (by simp [__upoly_to_list])
      obtain ⟨f, ⟨lw, hwf, hlev⟩, hpf⟩ :=
        upoly_of_term_den (covDen_ofTermVal M hM) x p hx hpA hOT
      have hq : RatList q lw := hList ▸ upoly_to_list_of_wf hwf
      obtain ⟨rv, hrv, hrv'⟩ := upoly_eval_rat hwf sq
      rw [hrv, cov_lit_holds_rat] at hHolds
      have hNot : ¬ litSem neg rel (rv : Real) := by simpa using hHolds
      rw [hpf, ← hlev] at hSem
      apply hNot
      rw [hrv']
      refine (litSem_of_same_sign neg rel ?_).mp hSem
      rcases sgn_inv_true M hM hq l r hX1 with h | h | h
      · exact Or.inl ⟨h _ hxL hxR, h _ hInL hInR⟩
      · exact Or.inr (Or.inl ⟨h _ hxL hxR, h _ hInL hInR⟩)
      · exact Or.inr (Or.inr ⟨h _ hxL hxR, h _ hInL hInR⟩)
    · rcases hInL with h | h; exact hlm h
      rcases hInR with h' | h'; exact hlp h'
      linarith
  rcases hc with ⟨hT, hE⟩ | ⟨hT, hE⟩
  · rw [hE]
    refine ⟨eo_has_bool_type_false, fun hX1 hX2 => ?_⟩
    exact False.elim (hcontra hX1 hX2 (by rw [hT]; exact RuleProofs.eo_interprets_true M))
  · rw [hE] at hTy ⊢
    have hPTy : __eo_typeof (__mk_cover_piece x l r) = Term.Bool := by
      have hNot : __eo_typeof_not (__eo_typeof (__mk_cover_piece x l r)) = Term.Bool := hTy
      revert hNot; generalize __eo_typeof (__mk_cover_piece x l r) = T
      intro hNot; cases T <;> simp_all [__eo_typeof_not]
    have hPB := piece_bool x l r hPns hxT (fun h => hcovT _ (hlA h)) (fun h => hcovT _ (hrA h)) hPTy
    refine ⟨RuleProofs.eo_has_bool_type_not_of_bool_arg _ hPB, fun hX1 hX2 => ?_⟩
    rcases interprets_true_or_false M hM _ hPB with h | h
    · exact False.elim (hcontra hX1 hX2 h)
    · exact RuleProofs.eo_interprets_not_of_false M _ h

public theorem cmd_step_sgn_inv_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sgn_inv_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sgn_inv_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sgn_inv_elim args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sgn_inv_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨x, _ | ⟨p, _ | ⟨sv, _ | ⟨l, _ | ⟨r, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨n1, _ | ⟨n2, _ | ⟨_, _⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hxT : RuleProofs.eo_has_smt_translation x := by
    simpa [cmdTranslationOk, cArgListTranslationOkMask, argTranslationOkMasked] using hCmdTrans.1
  have hTy : __eo_typeof (__eo_prog_sgn_inv_elim x p sv l r
      (Proof.pf (__eo_state_proven_nth s n1)) (Proof.pf (__eo_state_proven_nth s n2))) =
        Term.Bool := hResultTy
  have hSound := sgn_inv_elim_sound M hM x p sv l r _ _ hxT
    (hPremisesBool _ (by simp [premiseTermList])) hTy
  refine ⟨fun hTrue => ?_, ?_⟩
  · exact hSound.2 (hTrue _ (by simp [premiseTermList])) (hTrue _ (by simp [premiseTermList]))
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hSound.1
