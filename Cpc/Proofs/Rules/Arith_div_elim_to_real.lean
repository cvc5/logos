module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev qdivTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y

private abbrev toRealTerm (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.to_real) x

private theorem prog_arith_div_elim_to_real_eq
    (x y : Term) (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_prog_arith_div_elim_to_real x y =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (qdivTerm (toRealTerm x) (toRealTerm y))) (qdivTerm x y) := by
  cases x <;> cases y <;> simp [__eo_prog_arith_div_elim_to_real] at hx hy ⊢

private theorem eo_typeof_to_real_int_of_ne_stuck (A : Term)
    (h : __eo_typeof_to_real A ≠ Term.Stuck) : A = Term.Int := by
  cases A with
  | UOp op => cases op <;> simp [__eo_typeof_to_real] at h ⊢
  | _ => simp [__eo_typeof_to_real] at h

private theorem eo_typeof_qdiv_args_ne_stuck (A B : Term)
    (h : __eo_typeof_qdiv A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  constructor
  · intro hA; subst hA; simp [__eo_typeof_qdiv] at h
  · intro hB; subst hB
    cases A <;> simp [__eo_typeof_qdiv] at h

private theorem arg_types_of_prog_arith_div_elim_to_real_bool
    (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck)
    (h : __eo_typeof (__eo_prog_arith_div_elim_to_real x y) = Term.Bool) :
    __eo_typeof x = Term.Int ∧ __eo_typeof y = Term.Int := by
  rw [prog_arith_div_elim_to_real_eq x y hx hy] at h
  change __eo_typeof_eq (__eo_typeof (qdivTerm (toRealTerm x) (toRealTerm y)))
    (__eo_typeof (qdivTerm x y)) = Term.Bool at h
  rcases RuleProofs.eo_typeof_eq_bool_same _ _ h with ⟨_hSame, hNonStuck⟩
  change __eo_typeof_qdiv (__eo_typeof_to_real (__eo_typeof x))
    (__eo_typeof_to_real (__eo_typeof y)) ≠ Term.Stuck at hNonStuck
  rcases eo_typeof_qdiv_args_ne_stuck _ _ hNonStuck with ⟨hX, hY⟩
  exact ⟨eo_typeof_to_real_int_of_ne_stuck _ hX,
    eo_typeof_to_real_int_of_ne_stuck _ hY⟩

private theorem typed___eo_prog_arith_div_elim_to_real_impl
    (x y : Term) :
  RuleProofs.eo_has_smt_translation x ->
  RuleProofs.eo_has_smt_translation y ->
  __eo_typeof (__eo_prog_arith_div_elim_to_real x y) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_div_elim_to_real x y) := by
  intro hXTrans hYTrans hResultTy
  have hx := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hy := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  rcases arg_types_of_prog_arith_div_elim_to_real_bool x y hx hy hResultTy with
    ⟨hXTy, hYTy⟩
  have hSmtX : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x Term.Int (__eo_to_smt x) rfl hXTrans hXTy
  have hSmtY : __smtx_typeof (__eo_to_smt y) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y Term.Int (__eo_to_smt y) rfl hYTrans hYTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (qdivTerm (toRealTerm x) (toRealTerm y))) =
        SmtType.Real := by
    change __smtx_typeof (SmtTerm.qdiv (SmtTerm.to_real (__eo_to_smt x))
      (SmtTerm.to_real (__eo_to_smt y))) = SmtType.Real
    rw [typeof_qdiv_eq, typeof_to_real_eq, typeof_to_real_eq]
    simp [native_ite, native_Teq, hSmtX, hSmtY, __smtx_typeof_arith_overload_op_2_ret]
  have hRhsTy : __smtx_typeof (__eo_to_smt (qdivTerm x y)) = SmtType.Real := by
    change __smtx_typeof (SmtTerm.qdiv (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Real
    rw [typeof_qdiv_eq]
    simp [hSmtX, hSmtY, __smtx_typeof_arith_overload_op_2_ret]
  rw [prog_arith_div_elim_to_real_eq x y hx hy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_arith_div_elim_to_real_impl
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
  RuleProofs.eo_has_smt_translation x ->
  RuleProofs.eo_has_smt_translation y ->
  __eo_typeof (__eo_prog_arith_div_elim_to_real x y) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_div_elim_to_real x y) true := by
  intro hXTrans hYTrans hResultTy
  have hProgBool :=
    typed___eo_prog_arith_div_elim_to_real_impl x y hXTrans hYTrans hResultTy
  have hx := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hy := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  rcases arg_types_of_prog_arith_div_elim_to_real_bool x y hx hy hResultTy with
    ⟨hXTy, hYTy⟩
  rw [prog_arith_div_elim_to_real_eq x y hx hy] at hProgBool ⊢
  have hSmtX : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x Term.Int (__eo_to_smt x) rfl hXTrans hXTy
  have hSmtY : __smtx_typeof (__eo_to_smt y) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y Term.Int (__eo_to_smt y) rfl hYTrans hYTy
  rcases int_value_canonical
      (smt_model_eval_preserves_type M hM (__eo_to_smt x) SmtType.Int hSmtX
        (by simp) type_inhabited_int) with ⟨a, hEvalX⟩
  rcases int_value_canonical
      (smt_model_eval_preserves_type M hM (__eo_to_smt y) SmtType.Int hSmtY
        (by simp) type_inhabited_int) with ⟨b, hEvalY⟩
  have hEval :
      __smtx_model_eval M (__eo_to_smt (qdivTerm (toRealTerm x) (toRealTerm y))) =
        __smtx_model_eval M (__eo_to_smt (qdivTerm x y)) := by
    change __smtx_model_eval M (SmtTerm.qdiv (SmtTerm.to_real (__eo_to_smt x))
        (SmtTerm.to_real (__eo_to_smt y))) =
      __smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt x) (__eo_to_smt y))
    rw [__smtx_model_eval.eq_134, __smtx_model_eval.eq_134,
      __smtx_model_eval.eq_21, __smtx_model_eval.eq_21, hEvalX, hEvalY]
    rfl
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hProgBool <| by
    rw [hEval]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_arith_div_elim_to_real_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_div_elim_to_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_div_elim_to_real args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_div_elim_to_real args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_div_elim_to_real args premises ≠
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
                  change __eo_typeof (__eo_prog_arith_div_elim_to_real a1 a2) =
                    Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_arith_div_elim_to_real a1 a2) true
                    exact facts___eo_prog_arith_div_elim_to_real_impl M hM a1 a2
                      hT1Trans hT2Trans hResultTy
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_div_elim_to_real a1 a2)
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_arith_div_elim_to_real a1 a2)
                      (typed___eo_prog_arith_div_elim_to_real_impl a1 a2
                        hT1Trans hT2Trans hResultTy)
