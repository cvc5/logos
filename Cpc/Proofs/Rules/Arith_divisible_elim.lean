module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev divisibleTerm (n t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.divisible) n) t

private abbrev modTotalTerm (t n : Term) : Term :=
  Term.Apply (Term.Apply Term.mod_total t) n

private abbrev modZeroTerm (t n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (modTotalTerm t n)) (Term.Numeral 0)

private abbrev divisiblePremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.eq n) (Term.Numeral 0)))
    (Term.Boolean false)

private abbrev divisibleConclusion (n t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (divisibleTerm n t)) (modZeroTerm t n)

private theorem eo_to_smt_divisible_eq (n t : Term) :
    __eo_to_smt (divisibleTerm n t) =
      SmtTerm.divisible (__eo_to_smt n) (__eo_to_smt t) := by
  rfl

private theorem eo_to_smt_mod_total_eq (t n : Term) :
    __eo_to_smt (modTotalTerm t n) =
      SmtTerm.mod_total (__eo_to_smt t) (__eo_to_smt n) := by
  rfl

private theorem smtx_eval_divisible_term_eq
    (M : SmtModel) (n t : SmtTerm) :
    __smtx_model_eval M (SmtTerm.divisible n t) =
      __smtx_model_eval_divisible
        (__smtx_model_eval M n) (__smtx_model_eval M t) := by
  rw [__smtx_model_eval.eq_28]

private theorem smtx_eval_mod_total_term_eq
    (M : SmtModel) (t n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod_total t n) =
      __smtx_model_eval_mod_total
        (__smtx_model_eval M t) (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_32]

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    a Term.Int (__eo_to_smt a) rfl hTrans hTy

private theorem prog_arith_divisible_elim_info
    (n t P : Term)
    (hProg : __eo_prog_arith_divisible_elim n t (Proof.pf P) ≠ Term.Stuck) :
    ∃ n0,
      P = divisiblePremise n0 ∧
      n0 = n ∧
      __eo_prog_arith_divisible_elim n t (Proof.pf P) =
        divisibleConclusion n t := by
  unfold __eo_prog_arith_divisible_elim at hProg
  split at hProg <;> try contradiction
  next a b c d h1 h2 heq =>
    cases heq
    have hd : d = _ :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst hd
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_arith_divisible_elim, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      divisibleConclusion, divisibleTerm, modZeroTerm, modTotalTerm]

private theorem typeof_args_of_prog_arith_divisible_elim_bool
    (n t P : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hProgEq :
      __eo_prog_arith_divisible_elim n t (Proof.pf P) =
        divisibleConclusion n t)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_divisible_elim n t (Proof.pf P)) =
        Term.Bool) :
    __eo_typeof n = Term.Int ∧ __eo_typeof t = Term.Int := by
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (divisibleTerm n t))
      (__eo_typeof (modZeroTerm t n)) = Term.Bool at hResultTy
  change __eo_typeof_eq (__eo_typeof_divisible (__eo_typeof n) (__eo_typeof t))
      (__eo_typeof_eq (__eo_typeof (modTotalTerm t n))
        (__eo_typeof (Term.Numeral 0))) = Term.Bool at hResultTy
  change __eo_typeof_eq (__eo_typeof_divisible (__eo_typeof n) (__eo_typeof t))
      (__eo_typeof_eq (__eo_typeof_div (__eo_typeof t) (__eo_typeof n))
        (__eo_typeof (Term.Numeral 0))) = Term.Bool at hResultTy
  have hZeroTy : __eo_typeof (Term.Numeral 0) = Term.Int := by
    native_decide
  rw [hZeroTy] at hResultTy
  cases hn : __eo_typeof n with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_eq, __eo_typeof_divisible, __eo_typeof_div,
          __eo_requires, __eo_eq, native_ite, native_teq, native_not, hn]
          at hResultTy ⊢
      case Int =>
        cases ht : __eo_typeof t with
        | UOp op2 =>
            cases op2 <;>
              simp [__eo_typeof_eq, __eo_typeof_divisible, __eo_typeof_div,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hn, ht] at hResultTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_divisible, __eo_typeof_div,
              __eo_requires, __eo_eq, native_ite, native_teq, native_not,
              hn, ht] at hResultTy
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_divisible, __eo_typeof_div,
        __eo_requires, __eo_eq, native_ite, native_teq, native_not, hn]
        at hResultTy

private theorem typed___eo_prog_arith_divisible_elim_impl
    (n t P : Term) :
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation t ->
    __eo_prog_arith_divisible_elim n t (Proof.pf P) =
      divisibleConclusion n t ->
    __eo_typeof (__eo_prog_arith_divisible_elim n t (Proof.pf P)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_divisible_elim n t (Proof.pf P)) := by
  intro hNTrans hTTrans hProgEq hResultTy
  have hArgsTy :=
    typeof_args_of_prog_arith_divisible_elim_bool n t P hNTrans hTTrans
      hProgEq hResultTy
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    smtx_typeof_of_eo_int n hNTrans hArgsTy.1
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hArgsTy.2
  have hDivisibleTy :
      __smtx_typeof (__eo_to_smt (divisibleTerm n t)) = SmtType.Bool := by
    rw [eo_to_smt_divisible_eq, typeof_divisible_eq]
    simp [native_ite, native_Teq, hNSmtTy, hTSmtTy]
  have hModTotalTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm t n)) = SmtType.Int := by
    rw [eo_to_smt_mod_total_eq, typeof_mod_total_eq]
    simp [native_ite, native_Teq, hTSmtTy, hNSmtTy]
  have hModZeroTy : RuleProofs.eo_has_bool_type (modZeroTerm t n) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (modTotalTerm t n) (Term.Numeral 0)
      (by
        rw [hModTotalTy]
        change SmtType.Int = __smtx_typeof (SmtTerm.Numeral 0)
        rw [__smtx_typeof.eq_2])
      (by
        rw [hModTotalTy]
        decide)
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (divisibleTerm n t) (modZeroTerm t n)
    (hDivisibleTy.trans hModZeroTy.symm)
    (by
      rw [hDivisibleTy]
      decide)

private theorem facts___eo_prog_arith_divisible_elim_impl
    (M : SmtModel) (hM : model_wf M) (n t P : Term) :
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation t ->
    __eo_prog_arith_divisible_elim n t (Proof.pf P) =
      divisibleConclusion n t ->
    __eo_typeof (__eo_prog_arith_divisible_elim n t (Proof.pf P)) =
      Term.Bool ->
    eo_interprets M (__eo_prog_arith_divisible_elim n t (Proof.pf P)) true := by
  intro hNTrans hTTrans hProgEq hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_divisible_elim n t (Proof.pf P)) :=
    typed___eo_prog_arith_divisible_elim_impl n t P
      hNTrans hTTrans hProgEq hResultTy
  have hProgBool' :
      RuleProofs.eo_has_bool_type (divisibleConclusion n t) := by
    simpa [hProgEq] using hProgBool
  have hArgsTy :=
    typeof_args_of_prog_arith_divisible_elim_bool n t P hNTrans hTTrans
      hProgEq hResultTy
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    smtx_typeof_of_eo_int n hNTrans hArgsTy.1
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hArgsTy.2
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt n) SmtType.Int hNSmtTy
      (by simp) type_inhabited_int
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t) SmtType.Int hTSmtTy
      (by simp) type_inhabited_int
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hTEvalTy with ⟨ti, hTEval⟩
  have hEvalDivisible :
      __smtx_model_eval M (__eo_to_smt (divisibleTerm n t)) =
        __smtx_model_eval_eq
          (SmtValue.Numeral (native_mod_total ti ni)) (SmtValue.Numeral 0) := by
    rw [eo_to_smt_divisible_eq, smtx_eval_divisible_term_eq]
    rw [hNEval, hTEval]
    simp [__smtx_model_eval_divisible, __smtx_model_eval_mod_total]
  have hEvalModZero :
      __smtx_model_eval M (__eo_to_smt (modZeroTerm t n)) =
        __smtx_model_eval_eq
          (SmtValue.Numeral (native_mod_total ti ni)) (SmtValue.Numeral 0) := by
    have hEvalZero :
        __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) =
          SmtValue.Numeral 0 := by
      change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
      rw [__smtx_model_eval.eq_2]
    rw [RuleProofs.eo_to_smt_eq_eq, eo_to_smt_mod_total_eq,
      smtx_eval_eq_term_eq, smtx_eval_mod_total_term_eq]
    rw [hTEval, hNEval, hEvalZero]
    simp [__smtx_model_eval_mod_total]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (divisibleTerm n t) (modZeroTerm t n) hProgBool' <| by
      rw [hEvalDivisible, hEvalModZero]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval_eq
          (SmtValue.Numeral (native_mod_total ti ni)) (SmtValue.Numeral 0))

public theorem cmd_step_arith_divisible_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_divisible_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_divisible_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_divisible_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_divisible_elim args premises ≠
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
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons p premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let N1 := a1
                      let T1 := a2
                      let P := __eo_state_proven_nth s p
                      have hArgsTrans :
                          cArgListTranslationOk
                            (CArgList.cons N1
                              (CArgList.cons T1 CArgList.nil)) := by
                        simpa [cmdTranslationOk] using hCmdTrans
                      have hNTrans :
                          RuleProofs.eo_has_smt_translation N1 := by
                        simpa [cArgListTranslationOk] using hArgsTrans.1
                      have hTTrans :
                          RuleProofs.eo_has_smt_translation T1 := by
                        simpa [cArgListTranslationOk] using hArgsTrans.2
                      change __eo_typeof
                          (__eo_prog_arith_divisible_elim N1 T1 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      change __eo_prog_arith_divisible_elim N1 T1 (Proof.pf P) ≠
                        Term.Stuck at hProg
                      rcases prog_arith_divisible_elim_info N1 T1 P hProg with
                        ⟨_N0, _hPEq, _hN0Eq, hProgEq⟩
                      refine ⟨?_, ?_⟩
                      · intro _hPremTrue
                        change eo_interprets M
                          (__eo_prog_arith_divisible_elim N1 T1 (Proof.pf P))
                          true
                        exact facts___eo_prog_arith_divisible_elim_impl
                          M hM N1 T1 P hNTrans hTTrans hProgEq hResultTy
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_arith_divisible_elim N1 T1 (Proof.pf P))
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (__eo_prog_arith_divisible_elim N1 T1 (Proof.pf P))
                          (typed___eo_prog_arith_divisible_elim_impl
                            N1 T1 P hNTrans hTTrans hProgEq hResultTy)
