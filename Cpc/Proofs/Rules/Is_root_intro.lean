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

private theorem prog_is_root_intro_inv (p r st : Term)
    (h : __eo_prog_is_root_intro p r st ≠ Term.Stuck) :
    __cov_is_root (__upoly_of_term (__upoly_term_var p) p) r st = Term.Boolean true ∧
    r ≠ Term.Stuck ∧
    __eo_prog_is_root_intro p r st =
      Term.Apply (Term.UOp1 UserOp1._at_is_root
        (__upoly_to_list (__upoly_of_term (__upoly_term_var p) p))) r := by
  have hp : p ≠ Term.Stuck := by rintro rfl; simp [__eo_prog_is_root_intro] at h
  have hr : r ≠ Term.Stuck := by rintro rfl; cases p <;> simp_all [__eo_prog_is_root_intro]
  have hst : st ≠ Term.Stuck := by
    rintro rfl; cases p <;> cases r <;> simp_all [__eo_prog_is_root_intro]
  have hEq : __eo_prog_is_root_intro p r st =
      __eo_requires (__cov_is_root (__upoly_of_term (__upoly_term_var p) p) r st) (Term.Boolean true)
        (__eo_mk_apply (Term.UOp1 UserOp1._at_is_root
          (__upoly_to_list (__upoly_of_term (__upoly_term_var p) p))) r) := by
    rw [__eo_prog_is_root_intro.eq_def]
    simp_all
  rw [hEq] at h ⊢
  obtain ⟨h1, h2⟩ := eo_requires_eq_body h
  refine ⟨h1, hr, ?_⟩
  rw [h2]
  cases r <;> simp_all [__eo_mk_apply]

private theorem is_root_intro_sound (M : SmtModel) (hM : model_wf M) (p r st : Term)
    (hrT : RuleProofs.eo_has_smt_translation r)
    (hTy : __eo_typeof (__eo_prog_is_root_intro p r st) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_is_root_intro p r st) ∧
    eo_interprets M (__eo_prog_is_root_intro p r st) true := by
  have hProg := term_ne_stuck_of_typeof_bool hTy
  obtain ⟨hroot, hrS, hEq⟩ := prog_is_root_intro_inv p r st hProg
  rw [hEq] at hTy ⊢
  -- the polynomial
  have hvS : __upoly_of_term (__upoly_term_var p) p ≠ Term.Stuck := by
    intro hs; rw [hs] at hroot; simp [__cov_is_root] at hroot
  have hxS : __upoly_term_var p ≠ Term.Stuck := by
    intro hs; rw [hs] at hvS; simp [__upoly_of_term] at hvS
  obtain ⟨pp, hP⟩ := upoly_of_term_cpoly _ hxS p hvS
  obtain ⟨lst, hwf, hcanon, hpp⟩ := hP
  have hL := upoly_to_list_of_wf hwf
  -- `r` is real
  have hrR : __smtx_typeof (__eo_to_smt r) = SmtType.Real := by
    have hT : __eo_typeof__at_is_root
        (__eo_typeof (__upoly_to_list (__upoly_of_term (__upoly_term_var p) p)))
        (__eo_typeof r) = Term.Bool := hTy
    have hr' : __eo_typeof r = Term.UOp UserOp.Real := by
      revert hT; generalize __eo_typeof r = T; generalize __eo_typeof _ = U
      intro hT; cases U <;> cases T <;> simp_all [__eo_typeof__at_is_root]
      all_goals (rename_i op; cases op <;> simp_all)
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation r hrT, hr']
    rfl
  refine ⟨is_root_bool hL r hrR, ?_⟩
  -- `r` is a root
  have hfin : FinEnd r := by
    rcases cov_is_root_shape hroot with h | ⟨c, a, b, d, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, a, b, d, rfl, hrR⟩
  have hz := cov_is_root_sound M hM ⟨lst, hwf, hcanon, hpp⟩ r st hfin hroot
  rw [← hpp, eval_toPoly] at hz
  exact is_root_true_of_root M hM hL r hrR hz

public theorem cmd_step_is_root_intro_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.is_root_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.is_root_intro args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.is_root_intro args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.is_root_intro args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨p, _ | ⟨r, _ | ⟨st, _ | ⟨_, _⟩⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨_, _⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hT := hCmdTrans
  simp only [cmdTranslationOk, cArgListTranslationOkMask, argTranslationOkMasked] at hT
  have hTy : __eo_typeof (__eo_prog_is_root_intro p r st) = Term.Bool := hResultTy
  have hSound := is_root_intro_sound M hM p r st hT.2.1 hTy
  exact ⟨fun _ => hSound.2, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hSound.1⟩
