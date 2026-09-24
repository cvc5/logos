module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev modTotalTerm (t c : Term) : Term :=
  Term.Apply (Term.Apply Term.mod_total t) c

private abbrev modOverModPremise (c : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.eq c) (Term.Numeral 0)))
    (Term.Boolean false)

private abbrev modOverMod1Conclusion (c r : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (modTotalTerm (modTotalTerm r c) c))
    (modTotalTerm r c)

private theorem eo_to_smt_mod_total_eq (x y : Term) :
    __eo_to_smt (modTotalTerm x y) =
      SmtTerm.mod_total (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem smtx_eval_mod_total_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod_total x y) =
      __smtx_model_eval_mod_total
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    a Term.Int (__eo_to_smt a) rfl hTrans hTy

private theorem prog_arith_mod_over_mod_1_info
    (c r P : Term)
    (hProg : __eo_prog_arith_mod_over_mod_1 c r (Proof.pf P) ≠ Term.Stuck) :
    ∃ c0,
      P = modOverModPremise c0 ∧
      c0 = c ∧
      __eo_prog_arith_mod_over_mod_1 c r (Proof.pf P) =
        modOverMod1Conclusion c r := by
  unfold __eo_prog_arith_mod_over_mod_1 at hProg
  split at hProg <;> try contradiction
  next a b c d h1 h2 heq =>
    cases heq
    have hd : d = _ :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst hd
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_arith_mod_over_mod_1, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      modOverModPremise, modOverMod1Conclusion, modTotalTerm]

private theorem typeof_args_of_prog_arith_mod_over_mod_1_bool
    (c r P : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hProgEq :
      __eo_prog_arith_mod_over_mod_1 c r (Proof.pf P) =
        modOverMod1Conclusion c r)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_mod_over_mod_1 c r (Proof.pf P)) =
        Term.Bool) :
    __eo_typeof c = Term.Int ∧ __eo_typeof r = Term.Int := by
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (modTotalTerm (modTotalTerm r c) c))
      (__eo_typeof (modTotalTerm r c)) = Term.Bool at hResultTy
  change __eo_typeof_eq
      (__eo_typeof_div (__eo_typeof (modTotalTerm r c)) (__eo_typeof c))
      (__eo_typeof_div (__eo_typeof r) (__eo_typeof c)) = Term.Bool
    at hResultTy
  change __eo_typeof_eq
      (__eo_typeof_div
        (__eo_typeof_div (__eo_typeof r) (__eo_typeof c)) (__eo_typeof c))
      (__eo_typeof_div (__eo_typeof r) (__eo_typeof c)) = Term.Bool
    at hResultTy
  cases hc : __eo_typeof c with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
          native_ite, native_teq, native_not, hc] at hResultTy ⊢
      case Int =>
        cases hr : __eo_typeof r with
        | UOp op2 =>
            cases op2 <;>
              simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
                native_ite, native_teq, native_not, hc, hr] at hResultTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
              native_ite, native_teq, native_not, hc, hr] at hResultTy
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
        native_ite, native_teq, native_not, hc] at hResultTy

private theorem typed___eo_prog_arith_mod_over_mod_1_impl
    (c r P : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation r ->
    __eo_prog_arith_mod_over_mod_1 c r (Proof.pf P) =
      modOverMod1Conclusion c r ->
    __eo_typeof (__eo_prog_arith_mod_over_mod_1 c r (Proof.pf P)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_mod_over_mod_1 c r (Proof.pf P)) := by
  intro hCTrans hRTrans hProgEq hResultTy
  have hArgsTy :=
    typeof_args_of_prog_arith_mod_over_mod_1_bool c r P hCTrans hRTrans
      hProgEq hResultTy
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    smtx_typeof_of_eo_int c hCTrans hArgsTy.1
  have hRSmtTy : __smtx_typeof (__eo_to_smt r) = SmtType.Int :=
    smtx_typeof_of_eo_int r hRTrans hArgsTy.2
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm r c)) = SmtType.Int := by
    rw [eo_to_smt_mod_total_eq, typeof_mod_total_eq]
    simp [native_ite, native_Teq, hRSmtTy, hCSmtTy]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm (modTotalTerm r c) c)) =
        SmtType.Int := by
    rw [eo_to_smt_mod_total_eq, typeof_mod_total_eq]
    simp [native_ite, native_Teq, hRhsTy, hCSmtTy]
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation (modTotalTerm (modTotalTerm r c) c) := by
    simp [RuleProofs.eo_has_smt_translation, hLhsTy]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (modTotalTerm (modTotalTerm r c) c) (modTotalTerm r c)
    (by rw [hLhsTy, hRhsTy]) hLhsTrans

private theorem facts___eo_prog_arith_mod_over_mod_1_impl
    (M : SmtModel) (hM : model_wf M) (c r P : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation r ->
    __eo_prog_arith_mod_over_mod_1 c r (Proof.pf P) =
      modOverMod1Conclusion c r ->
    __eo_typeof (__eo_prog_arith_mod_over_mod_1 c r (Proof.pf P)) =
      Term.Bool ->
    eo_interprets M (__eo_prog_arith_mod_over_mod_1 c r (Proof.pf P)) true := by
  intro hCTrans hRTrans hProgEq hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_mod_over_mod_1 c r (Proof.pf P)) :=
    typed___eo_prog_arith_mod_over_mod_1_impl c r P
      hCTrans hRTrans hProgEq hResultTy
  have hProgBool' :
      RuleProofs.eo_has_bool_type (modOverMod1Conclusion c r) := by
    simpa [hProgEq] using hProgBool
  have hArgsTy :=
    typeof_args_of_prog_arith_mod_over_mod_1_bool c r P hCTrans hRTrans
      hProgEq hResultTy
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    smtx_typeof_of_eo_int c hCTrans hArgsTy.1
  have hRSmtTy : __smtx_typeof (__eo_to_smt r) = SmtType.Int :=
    smtx_typeof_of_eo_int r hRTrans hArgsTy.2
  have hCEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt c) SmtType.Int hCSmtTy
      (by simp) type_inhabited_int
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt r) SmtType.Int hRSmtTy
      (by simp) type_inhabited_int
  rcases int_value_canonical hCEvalTy with ⟨ci, hCEval⟩
  rcases int_value_canonical hREvalTy with ⟨ri, hREval⟩
  have hEvalRhs :
      __smtx_model_eval M (__eo_to_smt (modTotalTerm r c)) =
        SmtValue.Numeral (native_mod_total ri ci) := by
    rw [eo_to_smt_mod_total_eq, smtx_eval_mod_total_term_eq]
    rw [hREval, hCEval]
    simp [__smtx_model_eval_mod_total]
  have hEvalLhs :
      __smtx_model_eval M
          (__eo_to_smt (modTotalTerm (modTotalTerm r c) c)) =
        SmtValue.Numeral (native_mod_total (native_mod_total ri ci) ci) := by
    rw [eo_to_smt_mod_total_eq, smtx_eval_mod_total_term_eq]
    rw [hEvalRhs, hCEval]
    simp [__smtx_model_eval_mod_total]
  have hModIdentity :
      native_mod_total (native_mod_total ri ci) ci = native_mod_total ri ci := by
    unfold native_mod_total
    change ri % ci % ci = ri % ci
    rw [Int.emod_emod]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (modTotalTerm (modTotalTerm r c) c) (modTotalTerm r c) hProgBool' <| by
      rw [hEvalLhs, hEvalRhs, hModIdentity]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Numeral (native_mod_total ri ci))

public theorem cmd_step_arith_mod_over_mod_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mod_over_mod_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mod_over_mod_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mod_over_mod_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_mod_over_mod_1 args premises ≠
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
                      let C1 := a1
                      let R1 := a2
                      let P := __eo_state_proven_nth s p
                      have hArgsTrans :
                          cArgListTranslationOk
                            (CArgList.cons C1
                              (CArgList.cons R1 CArgList.nil)) := by
                        simpa [cmdTranslationOk] using hCmdTrans
                      have hCTrans :
                          RuleProofs.eo_has_smt_translation C1 := by
                        simpa [cArgListTranslationOk] using hArgsTrans.1
                      have hRTrans :
                          RuleProofs.eo_has_smt_translation R1 := by
                        simpa [cArgListTranslationOk] using hArgsTrans.2
                      change __eo_typeof
                          (__eo_prog_arith_mod_over_mod_1 C1 R1
                            (Proof.pf P)) = Term.Bool at hResultTy
                      change __eo_prog_arith_mod_over_mod_1 C1 R1
                        (Proof.pf P) ≠ Term.Stuck at hProg
                      rcases prog_arith_mod_over_mod_1_info C1 R1 P hProg with
                        ⟨_C0, _hPEq, _hC0Eq, hProgEq⟩
                      refine ⟨?_, ?_⟩
                      · intro _hPremTrue
                        change eo_interprets M
                          (__eo_prog_arith_mod_over_mod_1 C1 R1
                            (Proof.pf P)) true
                        exact facts___eo_prog_arith_mod_over_mod_1_impl
                          M hM C1 R1 P hCTrans hRTrans hProgEq hResultTy
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_arith_mod_over_mod_1 C1 R1
                            (Proof.pf P))
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (__eo_prog_arith_mod_over_mod_1 C1 R1
                            (Proof.pf P))
                          (typed___eo_prog_arith_mod_over_mod_1_impl
                            C1 R1 P hCTrans hRTrans hProgEq hResultTy)
