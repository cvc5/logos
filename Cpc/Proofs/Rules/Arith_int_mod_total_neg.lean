module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev negTerm (t : Term) : Term :=
  Term.Apply Term.__eoo_neg_2 t

private abbrev ltZeroPremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.lt s) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev modTotalTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.mod_total t) s

private abbrev modTotalNegConclusion (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (modTotalTerm t s))
    (modTotalTerm t (negTerm s))

private theorem eo_to_smt_uneg_eq (x : Term) :
    __eo_to_smt (negTerm x) = SmtTerm.uneg (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_mod_total_eq (x y : Term) :
    __eo_to_smt (modTotalTerm x y) =
      SmtTerm.mod_total (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eval_uneg (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.uneg a) =
      __smtx_model_eval_uneg (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

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

private theorem prog_arith_int_mod_total_neg_info
    (t s P : Term)
    (hProg : __eo_prog_arith_int_mod_total_neg t s (Proof.pf P) ≠ Term.Stuck) :
    ∃ s0,
      P = ltZeroPremise s0 ∧
      s0 = s ∧
      __eo_prog_arith_int_mod_total_neg t s (Proof.pf P) =
        modTotalNegConclusion t s := by
  unfold __eo_prog_arith_int_mod_total_neg at hProg
  split at hProg <;> try contradiction
  next a b c d h1 h2 heq =>
    cases heq
    have hd : d = _ :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst hd
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_arith_int_mod_total_neg, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      modTotalNegConclusion, ltZeroPremise, modTotalTerm, negTerm]

private theorem typeof_args_of_prog_arith_int_mod_total_neg_bool
    (t s P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hProgEq :
      __eo_prog_arith_int_mod_total_neg t s (Proof.pf P) =
        modTotalNegConclusion t s)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_int_mod_total_neg t s (Proof.pf P)) =
        Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (modTotalTerm t s))
      (__eo_typeof (modTotalTerm t (negTerm s))) = Term.Bool at hResultTy
  change __eo_typeof_eq (__eo_typeof_div (__eo_typeof t) (__eo_typeof s))
      (__eo_typeof_div (__eo_typeof t) (__eo_typeof (negTerm s))) =
        Term.Bool at hResultTy
  change __eo_typeof_eq (__eo_typeof_div (__eo_typeof t) (__eo_typeof s))
      (__eo_typeof_div (__eo_typeof t) (__eo_typeof_abs (__eo_typeof s))) =
        Term.Bool at hResultTy
  cases ht : __eo_typeof t with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_eq, __eo_typeof_div, __eo_typeof_abs,
          __eo_requires, __is_arith_type, __eo_eq, native_ite,
          native_teq, native_not, SmtEval.native_not, ht] at hResultTy ⊢
      case Int =>
        cases hs : __eo_typeof s with
        | UOp op2 =>
            cases op2 <;>
              simp [__eo_typeof_eq, __eo_typeof_div, __eo_typeof_abs,
                __eo_requires, __is_arith_type, __eo_eq, native_ite,
                native_teq, native_not, SmtEval.native_not, ht, hs]
                at hResultTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_div, __eo_typeof_abs,
              __eo_requires, __is_arith_type, __eo_eq, native_ite,
              native_teq, native_not, SmtEval.native_not, ht, hs]
              at hResultTy
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_div, __eo_typeof_abs,
        __eo_requires, __is_arith_type, __eo_eq, native_ite,
        native_teq, native_not, SmtEval.native_not, ht] at hResultTy

private theorem int_uneg_smt_type
    (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (negTerm t)) = SmtType.Int := by
  rw [eo_to_smt_uneg_eq, typeof_uneg_eq]
  simp [__smtx_typeof_arith_overload_op_1, hTy]

private theorem typed___eo_prog_arith_int_mod_total_neg_impl
    (t s P : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    __eo_prog_arith_int_mod_total_neg t s (Proof.pf P) =
      modTotalNegConclusion t s ->
    __eo_typeof (__eo_prog_arith_int_mod_total_neg t s (Proof.pf P)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_int_mod_total_neg t s (Proof.pf P)) := by
  intro hTTrans hSTrans hProgEq hResultTy
  have hArgsTy :=
    typeof_args_of_prog_arith_int_mod_total_neg_bool t s P hTTrans hSTrans
      hProgEq hResultTy
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hArgsTy.1
  have hSSmtTy : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    smtx_typeof_of_eo_int s hSTrans hArgsTy.2
  have hNegSTy : __smtx_typeof (__eo_to_smt (negTerm s)) = SmtType.Int :=
    int_uneg_smt_type s hSSmtTy
  have hModTotalTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm t s)) = SmtType.Int := by
    rw [eo_to_smt_mod_total_eq, typeof_mod_total_eq]
    simp [native_ite, native_Teq, hTSmtTy, hSSmtTy]
  have hModTotalNegSTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm t (negTerm s))) =
        SmtType.Int := by
    rw [eo_to_smt_mod_total_eq, typeof_mod_total_eq]
    simp [native_ite, native_Teq, hTSmtTy, hNegSTy]
  have hModTotalTrans :
      RuleProofs.eo_has_smt_translation (modTotalTerm t s) := by
    simp [RuleProofs.eo_has_smt_translation, hModTotalTy]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (modTotalTerm t s) (modTotalTerm t (negTerm s))
    (by rw [hModTotalTy, hModTotalNegSTy]) hModTotalTrans

private theorem facts___eo_prog_arith_int_mod_total_neg_impl
    (M : SmtModel) (hM : model_wf M) (t s P : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    __eo_prog_arith_int_mod_total_neg t s (Proof.pf P) =
      modTotalNegConclusion t s ->
    __eo_typeof (__eo_prog_arith_int_mod_total_neg t s (Proof.pf P)) =
      Term.Bool ->
    eo_interprets M (__eo_prog_arith_int_mod_total_neg t s (Proof.pf P)) true := by
  intro hTTrans hSTrans hProgEq hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_int_mod_total_neg t s (Proof.pf P)) :=
    typed___eo_prog_arith_int_mod_total_neg_impl t s P
      hTTrans hSTrans hProgEq hResultTy
  have hProgBool' :
      RuleProofs.eo_has_bool_type (modTotalNegConclusion t s) := by
    simpa [hProgEq] using hProgBool
  have hArgsTy :=
    typeof_args_of_prog_arith_int_mod_total_neg_bool t s P hTTrans hSTrans
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
  have hEvalNegS :
      __smtx_model_eval M (__eo_to_smt (negTerm s)) =
        SmtValue.Numeral (-si) := by
    rw [eo_to_smt_uneg_eq, eval_uneg, hSEval]
    simp [__smtx_model_eval_uneg, native_zneg]
  have hEvalModTotal :
      __smtx_model_eval M (__eo_to_smt (modTotalTerm t s)) =
        SmtValue.Numeral (native_mod_total ti si) := by
    rw [eo_to_smt_mod_total_eq, smtx_eval_mod_total_term_eq]
    rw [hTEval, hSEval]
    simp [__smtx_model_eval_mod_total]
  have hEvalModTotalNegS :
      __smtx_model_eval M (__eo_to_smt (modTotalTerm t (negTerm s))) =
        SmtValue.Numeral (native_mod_total ti (-si)) := by
    rw [eo_to_smt_mod_total_eq, smtx_eval_mod_total_term_eq]
    rw [hTEval, hEvalNegS]
    simp [__smtx_model_eval_mod_total]
  have hModIdentity :
      native_mod_total ti si = native_mod_total ti (-si) := by
    unfold native_mod_total
    change ti % si = ti % -si
    rw [Int.emod_neg]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (modTotalTerm t s) (modTotalTerm t (negTerm s)) hProgBool' <| by
      rw [hEvalModTotal, hEvalModTotalNegS, hModIdentity]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Numeral (native_mod_total ti (-si)))

public theorem cmd_step_arith_int_mod_total_neg_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_mod_total_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_mod_total_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_mod_total_neg args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_int_mod_total_neg args premises ≠
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
                          (__eo_prog_arith_int_mod_total_neg T1 S1
                            (Proof.pf P)) = Term.Bool at hResultTy
                      change __eo_prog_arith_int_mod_total_neg T1 S1
                        (Proof.pf P) ≠ Term.Stuck at hProg
                      rcases prog_arith_int_mod_total_neg_info T1 S1 P hProg with
                        ⟨_S0, _hPEq, _hS0Eq, hProgEq⟩
                      refine ⟨?_, ?_⟩
                      · intro _hPremTrue
                        change eo_interprets M
                          (__eo_prog_arith_int_mod_total_neg T1 S1
                            (Proof.pf P)) true
                        exact facts___eo_prog_arith_int_mod_total_neg_impl
                          M hM T1 S1 P hTTrans hSTrans hProgEq hResultTy
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_arith_int_mod_total_neg T1 S1
                            (Proof.pf P))
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (__eo_prog_arith_int_mod_total_neg T1 S1
                            (Proof.pf P))
                          (typed___eo_prog_arith_int_mod_total_neg_impl
                            T1 S1 P hTTrans hSTrans hProgEq hResultTy)
