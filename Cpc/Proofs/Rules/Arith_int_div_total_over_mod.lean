module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev divModTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.div_total)
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) t) s)) s

private theorem int_emod_ediv_self (x y : Int) : (x % y) / y = 0 := by
  rcases Classical.em (y = 0) with h | h
  · simp [h]
  · have h1 := Int.emod_nonneg x h
    have h2 := Int.emod_lt x h
    generalize x % y = r at h1 h2 ⊢
    rcases Int.lt_or_le 0 y with hy | hy
    · exact Int.ediv_eq_zero_of_lt h1 (by omega)
    · have : y = -(-y) := by omega
      rw [this, Int.ediv_neg]
      have : r / (-y) = 0 := Int.ediv_eq_zero_of_lt h1 (by omega)
      omega

private theorem prog_arith_int_div_total_over_mod_eq
    (t s : Term) (ht : t ≠ Term.Stuck) (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_int_div_total_over_mod t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) (divModTerm t s))
        (Term.Numeral 0) := by
  cases t <;> cases s <;> simp [__eo_prog_arith_int_div_total_over_mod] at ht hs ⊢

private theorem eo_typeof_div_int_of_ne_stuck (A B : Term)
    (h : __eo_typeof_div A B ≠ Term.Stuck) : A = Term.Int ∧ B = Term.Int := by
  cases A with
  | UOp op =>
      cases op <;> cases B <;> simp [__eo_typeof_div] at h ⊢
      all_goals (rename_i op'; cases op' <;> simp [__eo_typeof_div] at h ⊢)
  | _ => simp [__eo_typeof_div] at h

private theorem arg_types_of_prog_arith_int_div_total_over_mod_bool
    (t s : Term) (ht : t ≠ Term.Stuck) (hs : s ≠ Term.Stuck)
    (h : __eo_typeof (__eo_prog_arith_int_div_total_over_mod t s) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  rw [prog_arith_int_div_total_over_mod_eq t s ht hs] at h
  change __eo_typeof_eq (__eo_typeof (divModTerm t s))
    (__eo_typeof (Term.Numeral 0)) = Term.Bool at h
  rcases RuleProofs.eo_typeof_eq_bool_same _ _ h with ⟨_hSame, hNonStuck⟩
  change __eo_typeof_div (__eo_typeof_div (__eo_typeof t) (__eo_typeof s))
    (__eo_typeof s) ≠ Term.Stuck at hNonStuck
  rcases eo_typeof_div_int_of_ne_stuck _ _ hNonStuck with ⟨hInner, _⟩
  exact eo_typeof_div_int_of_ne_stuck _ _ (by rw [hInner]; simp)

private theorem smt_types_of_args
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (h : __eo_typeof (__eo_prog_arith_int_div_total_over_mod t s) = Term.Bool) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Int := by
  have ht := RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  rcases arg_types_of_prog_arith_int_div_total_over_mod_bool t s ht hs h with
    ⟨hTTy, hSTy⟩
  exact ⟨TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTTy,
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSTy⟩

private theorem typed___eo_prog_arith_int_div_total_over_mod_impl
    (t s : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.eo_has_smt_translation s ->
  __eo_typeof (__eo_prog_arith_int_div_total_over_mod t s) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_int_div_total_over_mod t s) := by
  intro hTTrans hSTrans hResultTy
  have ht := RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  rcases smt_types_of_args t s hTTrans hSTrans hResultTy with ⟨hSmtT, hSmtS⟩
  have hLhsTy : __smtx_typeof (__eo_to_smt (divModTerm t s)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.div_total
      (SmtTerm.mod_total (__eo_to_smt t) (__eo_to_smt s)) (__eo_to_smt s)) = SmtType.Int
    rw [typeof_div_total_eq, typeof_mod_total_eq]
    simp [native_ite, native_Teq, hSmtT, hSmtS]
  have hRhsTy : __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
    rw [__smtx_typeof.eq_2]
  rw [prog_arith_int_div_total_over_mod_eq t s ht hs]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_arith_int_div_total_over_mod_impl
    (M : SmtModel) (hM : model_wf M) (t s : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.eo_has_smt_translation s ->
  __eo_typeof (__eo_prog_arith_int_div_total_over_mod t s) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_int_div_total_over_mod t s) true := by
  intro hTTrans hSTrans hResultTy
  have hProgBool :=
    typed___eo_prog_arith_int_div_total_over_mod_impl t s hTTrans hSTrans hResultTy
  have ht := RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  rcases smt_types_of_args t s hTTrans hSTrans hResultTy with ⟨hSmtT, hSmtS⟩
  rw [prog_arith_int_div_total_over_mod_eq t s ht hs] at hProgBool ⊢
  rcases int_value_canonical
      (smt_model_eval_preserves_type M hM (__eo_to_smt t) SmtType.Int hSmtT
        (by simp) type_inhabited_int) with ⟨a, hEvalT⟩
  rcases int_value_canonical
      (smt_model_eval_preserves_type M hM (__eo_to_smt s) SmtType.Int hSmtS
        (by simp) type_inhabited_int) with ⟨b, hEvalS⟩
  have hEvalLhs :
      __smtx_model_eval M (__eo_to_smt (divModTerm t s)) = SmtValue.Numeral 0 := by
    change __smtx_model_eval M (SmtTerm.div_total
      (SmtTerm.mod_total (__eo_to_smt t) (__eo_to_smt s)) (__eo_to_smt s)) =
        SmtValue.Numeral 0
    rw [__smtx_model_eval.eq_31, __smtx_model_eval.eq_32, hEvalT, hEvalS]
    change SmtValue.Numeral (native_div_total (native_mod_total a b) b) =
      SmtValue.Numeral 0
    simp only [SmtEval.native_div_total, SmtEval.native_mod_total, int_emod_ediv_self]
  have hEvalRhs :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) = SmtValue.Numeral 0 := by
    change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
    rw [__smtx_model_eval.eq_2]
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hProgBool <| by
    rw [hEvalLhs, hEvalRhs]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_arith_int_div_total_over_mod_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total_over_mod args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_div_total_over_mod args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total_over_mod args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_int_div_total_over_mod args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hT1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.1
                  have hT2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.2
                  change __eo_typeof (__eo_prog_arith_int_div_total_over_mod a1 a2) =
                    Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M
                      (__eo_prog_arith_int_div_total_over_mod a1 a2) true
                    exact facts___eo_prog_arith_int_div_total_over_mod_impl M hM a1 a2
                      hT1Trans hT2Trans hResultTy
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_int_div_total_over_mod a1 a2)
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_arith_int_div_total_over_mod a1 a2)
                      (typed___eo_prog_arith_int_div_total_over_mod_impl a1 a2
                        hT1Trans hT2Trans hResultTy)
