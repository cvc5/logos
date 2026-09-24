module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.SeqStringRegex
import all Cpc.Proofs.TypePreservation.SeqStringRegex

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem prog_re_repeat_elim_eq_of_ne_stuck (n1 x1 : Term) :
    n1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    __eo_prog_re_repeat_elim n1 x1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.re_exp n1) x1))
        (Term.Apply (Term.UOp2 UserOp2.re_loop n1 n1) x1) := by
  intro hN1 hX1
  cases n1 <;> cases x1 <;> simp [__eo_prog_re_repeat_elim] at hN1 hX1 ⊢

private theorem typeof_re_exp_inv (T i R : Term)
    (hNe : __eo_typeof_re_exp T i R ≠ Term.Stuck) :
    ∃ n : native_Int,
      i = Term.Numeral n ∧
      native_zleq 0 n = true ∧
      R = Term.UOp UserOp.RegLan := by
  unfold __eo_typeof_re_exp at hNe
  split at hNe
  · exact False.elim (hNe rfl)
  · have hGt : __eo_gt i (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hNe
    cases i with
    | Numeral n =>
        have hLt : -1 < n := by
          simpa [__eo_gt, native_zlt, SmtEval.native_zlt] using hGt
        have hNonneg : native_zleq 0 n = true := by
          simpa [native_zleq, SmtEval.native_zleq] using
            (show 0 <= n from Int.add_one_le_iff.mpr hLt)
        exact ⟨n, rfl, hNonneg, rfl⟩
    | _ =>
        simp [__eo_gt] at hGt
  · exact False.elim (hNe rfl)

private theorem re_repeat_args_of_result_bool (n1 x1 : Term) :
    __eo_typeof (__eo_prog_re_repeat_elim n1 x1) = Term.Bool ->
    ∃ n : native_Int,
      n1 = Term.Numeral n ∧
      native_zleq 0 n = true ∧
      __eo_typeof x1 = Term.UOp UserOp.RegLan := by
  intro hTy
  by_cases hN1 : n1 = Term.Stuck
  · subst n1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hX1 : x1 = Term.Stuck
    · subst x1
      cases n1 <;> simp [__eo_prog_re_repeat_elim] at hN1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_re_repeat_elim_eq_of_ne_stuck n1 x1 hN1 hX1] at hTy
      have hLeftNN :
          __eo_typeof_re_exp (__eo_typeof n1) n1 (__eo_typeof x1) ≠ Term.Stuck :=
        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
          (__eo_typeof_re_exp (__eo_typeof n1) n1 (__eo_typeof x1))
          (__eo_typeof_re_loop (__eo_typeof n1) n1 (__eo_typeof n1) n1
            (__eo_typeof x1)) hTy).1
      rcases typeof_re_exp_inv (__eo_typeof n1) n1 (__eo_typeof x1) hLeftNN with
        ⟨n, hN1, hNonneg, hXTy⟩
      exact ⟨n, hN1, hNonneg, hXTy⟩

private theorem smt_typeof_re_repeat_sides
    (n1 x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_re_repeat_elim n1 x1) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp n1) x1)) =
      SmtType.RegLan ∧
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop n1 n1) x1)) =
      SmtType.RegLan := by
  intro hX1Trans hResultTy
  rcases re_repeat_args_of_result_bool n1 x1 hResultTy with
    ⟨n, rfl, hNonneg, hXTy⟩
  have hX1SmtTy :
      __smtx_typeof (__eo_to_smt x1) = SmtType.RegLan :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.UOp UserOp.RegLan) (__eo_to_smt x1) rfl hX1Trans hXTy
  constructor
  · change __smtx_typeof (SmtTerm.re_exp (SmtTerm.Numeral n) (__eo_to_smt x1)) =
      SmtType.RegLan
    rw [typeof_re_exp_eq]
    simp [__smtx_typeof_re_exp, hX1SmtTy, hNonneg, native_ite]
  · change __smtx_typeof
      (SmtTerm.re_loop (SmtTerm.Numeral n) (SmtTerm.Numeral n) (__eo_to_smt x1)) =
      SmtType.RegLan
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop, hX1SmtTy, hNonneg, native_ite]

private theorem typed___eo_prog_re_repeat_elim_impl (n1 x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_re_repeat_elim n1 x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_re_repeat_elim n1 x1) := by
  intro hX1Trans hResultTy
  have hN1NotStuck : n1 ≠ Term.Stuck := by
    rcases re_repeat_args_of_result_bool n1 x1 hResultTy with ⟨n, hN, _⟩
    subst n1
    simp
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases smt_typeof_re_repeat_sides n1 x1 hX1Trans hResultTy with
    ⟨hLeftTy, hRightTy⟩
  rw [prog_re_repeat_elim_eq_of_ne_stuck n1 x1 hN1NotStuck hX1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 UserOp1.re_exp n1) x1)
    (Term.Apply (Term.UOp2 UserOp2.re_loop n1 n1) x1)
    (by rw [hLeftTy, hRightTy])
    (by rw [hLeftTy]; simp)

private theorem eval_re_loop_same_bounds
    (M : SmtModel) (n : native_Int) (x1 : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral n) (Term.Numeral n)) x1)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp (Term.Numeral n)) x1)) := by
  change __smtx_model_eval M
      (SmtTerm.re_loop (SmtTerm.Numeral n) (SmtTerm.Numeral n) (__eo_to_smt x1)) =
    __smtx_model_eval M (SmtTerm.re_exp (SmtTerm.Numeral n) (__eo_to_smt x1))
  have hNumEval :
      __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
    rw [__smtx_model_eval.eq_def] <;> simp only
  conv =>
    lhs
    rw [__smtx_model_eval.eq_def]
    simp only
    rw [hNumEval]
  conv =>
    rhs
    rw [__smtx_model_eval.eq_def]
    simp only
    rw [hNumEval]
  have hDiffZero : Int.toNat (n + -n) = 0 := by
    omega
  cases __smtx_model_eval M (__eo_to_smt x1) <;>
  simp [__smtx_model_eval_re_loop, __smtx_model_eval_re_exp,
    __smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_ite,
    __smtx_re_loop_rec, SmtEval.native_zlt, SmtEval.native_zplus,
    SmtEval.native_zneg, native_int_to_nat, hDiffZero]

private theorem facts___eo_prog_re_repeat_elim_impl
    (M : SmtModel) (hM : model_wf M) (n1 x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof (__eo_prog_re_repeat_elim n1 x1) = Term.Bool ->
    eo_interprets M (__eo_prog_re_repeat_elim n1 x1) true := by
  intro hX1Trans hResultTy
  rcases re_repeat_args_of_result_bool n1 x1 hResultTy with
    ⟨n, hN1Eq, _hNonneg, _hXTy⟩
  subst n1
  have hN1NotStuck : Term.Numeral n ≠ Term.Stuck := by simp
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_re_repeat_elim (Term.Numeral n) x1) :=
    typed___eo_prog_re_repeat_elim_impl (Term.Numeral n) x1 hX1Trans hResultTy
  rw [prog_re_repeat_elim_eq_of_ne_stuck (Term.Numeral n) x1 hN1NotStuck hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_re_repeat_elim_eq_of_ne_stuck (Term.Numeral n) x1 hN1NotStuck hX1NotStuck]
      using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp (Term.Numeral n)) x1)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral n) (Term.Numeral n)) x1)))
    rw [eval_re_loop_same_bounds M n x1]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_re_repeat_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_repeat_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_repeat_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_repeat_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_repeat_elim args premises ≠ Term.Stuck :=
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
          | nil =>
              cases premises with
              | nil =>
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                    hATransPair.2.1
                  change __eo_typeof (__eo_prog_re_repeat_elim a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_re_repeat_elim a1 a2) true
                    exact facts___eo_prog_re_repeat_elim_impl M hM a1 a2
                      hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_re_repeat_elim_impl a1 a2
                        hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
