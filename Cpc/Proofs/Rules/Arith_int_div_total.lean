module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev divTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.div t) s

private abbrev divTotalTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.div_total t) s

private abbrev divTotalPremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.eq s) (Term.Numeral 0)))
    (Term.Boolean false)

private abbrev divTotalConclusion (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (divTerm t s)) (divTotalTerm t s)

private theorem eo_to_smt_div_eq (x y : Term) :
    __eo_to_smt (divTerm x y) =
      SmtTerm.div (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_to_smt_div_total_eq (x y : Term) :
    __eo_to_smt (divTotalTerm x y) =
      SmtTerm.div_total (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem smtx_eval_div_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.div x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_div_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_div_total xv yv)) := by
  rw [__smtx_model_eval.eq_26]

private theorem smtx_eval_div_total_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.div_total x y) =
      __smtx_model_eval_div_total
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_31]

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    a Term.Int (__eo_to_smt a) rfl hTrans hTy

private theorem prog_arith_int_div_total_info
    (t s P : Term)
    (hProg : __eo_prog_arith_int_div_total t s (Proof.pf P) ≠ Term.Stuck) :
    ∃ s0,
      P = divTotalPremise s0 ∧
      s0 = s ∧
      __eo_prog_arith_int_div_total t s (Proof.pf P) =
        divTotalConclusion t s := by
  unfold __eo_prog_arith_int_div_total at hProg
  split at hProg <;> try contradiction
  next a b c d h1 h2 heq =>
    cases heq
    have hd : d = _ :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst hd
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_arith_int_div_total, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      divTotalConclusion, divTerm, divTotalTerm]

private theorem typeof_args_of_prog_arith_int_div_total_bool
    (t s P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hProgEq :
      __eo_prog_arith_int_div_total t s (Proof.pf P) =
        divTotalConclusion t s)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_int_div_total t s (Proof.pf P)) =
        Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (divTerm t s))
      (__eo_typeof (divTotalTerm t s)) = Term.Bool at hResultTy
  change __eo_typeof_eq (__eo_typeof_div (__eo_typeof t) (__eo_typeof s))
      (__eo_typeof_div (__eo_typeof t) (__eo_typeof s)) = Term.Bool at hResultTy
  cases ht : __eo_typeof t with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
          native_ite, native_teq, native_not, ht] at hResultTy ⊢
      case Int =>
        cases hs : __eo_typeof s with
        | UOp op2 =>
            cases op2 <;>
              simp [__eo_typeof_eq, __eo_typeof_div, __eo_requires,
                native_ite, native_teq, native_not, ht, hs] at hResultTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_div, ht, hs] at hResultTy
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_div, ht] at hResultTy

private theorem typed___eo_prog_arith_int_div_total_impl
    (t s P : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    __eo_prog_arith_int_div_total t s (Proof.pf P) =
      divTotalConclusion t s ->
    __eo_typeof (__eo_prog_arith_int_div_total t s (Proof.pf P)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_int_div_total t s (Proof.pf P)) := by
  intro hTTrans hSTrans hProgEq hResultTy
  have hArgsTy :=
    typeof_args_of_prog_arith_int_div_total_bool t s P hTTrans hSTrans
      hProgEq hResultTy
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hArgsTy.1
  have hSSmtTy : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    smtx_typeof_of_eo_int s hSTrans hArgsTy.2
  have hDivTy :
      __smtx_typeof (__eo_to_smt (divTerm t s)) = SmtType.Int := by
    rw [eo_to_smt_div_eq, typeof_div_eq]
    simp [native_ite, native_Teq, hTSmtTy, hSSmtTy]
  have hDivTotalTy :
      __smtx_typeof (__eo_to_smt (divTotalTerm t s)) = SmtType.Int := by
    rw [eo_to_smt_div_total_eq, typeof_div_total_eq]
    simp [native_ite, native_Teq, hTSmtTy, hSSmtTy]
  have hDivTrans : RuleProofs.eo_has_smt_translation (divTerm t s) := by
    simp [RuleProofs.eo_has_smt_translation, hDivTy]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (divTerm t s) (divTotalTerm t s)
    (by rw [hDivTy, hDivTotalTy]) hDivTrans

private theorem facts___eo_prog_arith_int_div_total_impl
    (M : SmtModel) (hM : model_wf M) (t s P : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    __eo_prog_arith_int_div_total t s (Proof.pf P) =
      divTotalConclusion t s ->
    __eo_typeof (__eo_prog_arith_int_div_total t s (Proof.pf P)) =
      Term.Bool ->
    eo_interprets M (divTotalPremise s) true ->
    eo_interprets M (__eo_prog_arith_int_div_total t s (Proof.pf P)) true := by
  intro hTTrans hSTrans hProgEq hResultTy hPrem
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_int_div_total t s (Proof.pf P)) :=
    typed___eo_prog_arith_int_div_total_impl t s P
      hTTrans hSTrans hProgEq hResultTy
  have hProgBool' :
      RuleProofs.eo_has_bool_type (divTotalConclusion t s) := by
    simpa [hProgEq] using hProgBool
  have hArgsTy :=
    typeof_args_of_prog_arith_int_div_total_bool t s P hTTrans hSTrans
      hProgEq hResultTy
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hArgsTy.1
  have hSSmtTy : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    smtx_typeof_of_eo_int s hSTrans hArgsTy.2
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t) SmtType.Int hTSmtTy
      (by simp) type_inhabited_int
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt s) SmtType.Int hSSmtTy
      (by simp) type_inhabited_int
  rcases int_value_canonical hTEvalTy with ⟨ti, hTEval⟩
  rcases int_value_canonical hSEvalTy with ⟨si, hSEval⟩
  have hSNotZeroEq :
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt s))
        (SmtValue.Numeral 0) = SmtValue.Boolean false :=
    by
      have hEval0 :
          __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) =
            SmtValue.Numeral 0 := by
        change __smtx_model_eval M (SmtTerm.Numeral 0) =
          SmtValue.Numeral 0
        rw [__smtx_model_eval.eq_2]
      have h :=
        RuleProofs.model_eval_eq_false_of_eq_false_eq_true M s
          (Term.Numeral 0) hPrem
      rwa [hEval0] at h
  have hSNeZeroBool : native_zeq si 0 = false := by
    rw [hSEval] at hSNotZeroEq
    simpa [__smtx_model_eval_eq, native_veq, native_zeq] using hSNotZeroEq
  have hSNeZeroDecide : decide (si = 0) = false := by
    simpa [native_zeq] using hSNeZeroBool
  have hEvalDiv :
      __smtx_model_eval M (__eo_to_smt (divTerm t s)) =
        SmtValue.Numeral (native_div_total ti si) := by
    rw [eo_to_smt_div_eq, smtx_eval_div_term_eq]
    rw [hSEval, hTEval]
    simp [__smtx_model_eval_eq, __smtx_model_eval_ite,
      __smtx_model_eval_div_total, native_veq, hSNeZeroDecide]
  have hEvalDivTotal :
      __smtx_model_eval M (__eo_to_smt (divTotalTerm t s)) =
        SmtValue.Numeral (native_div_total ti si) := by
    rw [eo_to_smt_div_total_eq, smtx_eval_div_total_term_eq]
    rw [hTEval, hSEval]
    simp [__smtx_model_eval_div_total]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (divTerm t s) (divTotalTerm t s) hProgBool' <| by
      rw [hEvalDiv, hEvalDivTotal]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Numeral (native_div_total ti si))

public theorem cmd_step_arith_int_div_total_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_div_total args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_int_div_total args premises ≠
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
                      let T1 := a1
                      let S1 := a2
                      let P := __eo_state_proven_nth s p
                      have hArgsTrans :
                          cArgListTranslationOk
                            (CArgList.cons T1
                              (CArgList.cons S1 CArgList.nil)) := by
                        simpa [cmdTranslationOk] using hCmdTrans
                      have hTTrans :
                          RuleProofs.eo_has_smt_translation T1 := by
                        simpa [cArgListTranslationOk] using hArgsTrans.1
                      have hSTrans :
                          RuleProofs.eo_has_smt_translation S1 := by
                        simpa [cArgListTranslationOk] using hArgsTrans.2
                      change __eo_typeof
                          (__eo_prog_arith_int_div_total T1 S1 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      change __eo_prog_arith_int_div_total T1 S1 (Proof.pf P) ≠
                        Term.Stuck at hProg
                      rcases prog_arith_int_div_total_info T1 S1 P hProg with
                        ⟨S0, hPEq, hS0Eq, hProgEq⟩
                      refine ⟨?_, ?_⟩
                      · intro hPremTrue
                        change eo_interprets M
                          (__eo_prog_arith_int_div_total T1 S1 (Proof.pf P))
                          true
                        have hPremS :
                            eo_interprets M (divTotalPremise S1) true := by
                          have hPTrue : eo_interprets M P true :=
                            hPremTrue P (by simp [premiseTermList, P])
                          rw [hPEq, hS0Eq] at hPTrue
                          exact hPTrue
                        exact facts___eo_prog_arith_int_div_total_impl
                          M hM T1 S1 P hTTrans hSTrans hProgEq
                          hResultTy hPremS
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_arith_int_div_total T1 S1 (Proof.pf P))
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (__eo_prog_arith_int_div_total T1 S1 (Proof.pf P))
                          (typed___eo_prog_arith_int_div_total_impl
                            T1 S1 P hTTrans hSTrans hProgEq hResultTy)
