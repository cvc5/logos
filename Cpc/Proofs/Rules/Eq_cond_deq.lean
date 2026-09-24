module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev mkNot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) x

private abbrev mkAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

private def eqCondDeqBody (t s r : Term) : Term :=
  mkEq (mkEq (mkEq t s) (mkEq t r))
    (mkAnd (mkNot (mkEq t s))
      (mkAnd (mkNot (mkEq t r)) (Term.Boolean true)))

private theorem prog_eq_cond_deq_eq
    (t s r s2 r2 : Term)
    (hTNotStuck : t ≠ Term.Stuck)
    (hSNotStuck : s ≠ Term.Stuck)
    (hRNotStuck : r ≠ Term.Stuck) :
    __eo_prog_eq_cond_deq t s r
      (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false))) =
      __eo_requires (__eo_and (__eo_eq s s2) (__eo_eq r r2))
        (Term.Boolean true) (eqCondDeqBody t s r) := by
  cases t <;> cases s <;> cases r <;>
    simp [__eo_prog_eq_cond_deq, eqCondDeqBody, mkEq, mkNot, mkAnd]
      at hTNotStuck hSNotStuck hRNotStuck ⊢

private theorem shape_of_prog_eq_cond_deq_not_stuck
    (t s r p : Term)
    (h : __eo_prog_eq_cond_deq t s r (Proof.pf p) ≠ Term.Stuck) :
    ∃ s2 r2 : Term, p = mkEq (mkEq s2 r2) (Term.Boolean false) := by
  by_cases ht : t = Term.Stuck
  · subst t
    simp [__eo_prog_eq_cond_deq] at h
  by_cases hs : s = Term.Stuck
  · subst s
    simp [__eo_prog_eq_cond_deq] at h
  by_cases hr : r = Term.Stuck
  · subst r
    simp [__eo_prog_eq_cond_deq] at h
  cases p with
  | Apply pEqFalse pFalse =>
      cases pEqFalse with
      | Apply pEq inner =>
          cases pEq with
          | UOp op =>
              by_cases hOp : op = UserOp.eq
              · subst op
                cases inner with
                | Apply innerEqRight r2 =>
                    cases innerEqRight with
                    | Apply innerEqLeft s2 =>
                        cases innerEqLeft with
                        | UOp opInner =>
                            by_cases hOpInner : opInner = UserOp.eq
                            · subst opInner
                              cases pFalse with
                              | Boolean b =>
                                  cases b
                                  · exact ⟨s2, r2, rfl⟩
                                  · simp [__eo_prog_eq_cond_deq] at h
                              | _ =>
                                  simp [__eo_prog_eq_cond_deq] at h
                            · cases opInner <;> first
                                | exact False.elim (hOpInner rfl)
                                | simp [__eo_prog_eq_cond_deq] at h
                        | _ =>
                            simp [__eo_prog_eq_cond_deq] at h
                    | _ =>
                        simp [__eo_prog_eq_cond_deq] at h
                | _ =>
                    simp [__eo_prog_eq_cond_deq] at h
              · cases op <;> first
                  | exact False.elim (hOp rfl)
                  | simp [__eo_prog_eq_cond_deq] at h
          | _ =>
              simp [__eo_prog_eq_cond_deq] at h
      | _ =>
          simp [__eo_prog_eq_cond_deq] at h
  | _ =>
      simp [__eo_prog_eq_cond_deq] at h

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem eo_typeof_eq_nonstuck_bool (A B : Term) :
    __eo_typeof_eq A B ≠ Term.Stuck ->
    __eo_typeof_eq A B = Term.Bool := by
  intro hNonStuck
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at hNonStuck ⊢
  all_goals
    assumption

private theorem requires_and_eq_self_true_body
    (s r body : Term)
    (hSNotStuck : s ≠ Term.Stuck)
    (hRNotStuck : r ≠ Term.Stuck) :
    __eo_requires (__eo_and (__eo_eq s s) (__eo_eq r r))
      (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and, eo_eq_self_true_of_ne_stuck s hSNotStuck,
    eo_eq_self_true_of_ne_stuck r hRNotStuck, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

private theorem operand_types_of_eq_cond_deq_body_bool
    (t s r : Term) :
    __eo_typeof (eqCondDeqBody t s r) = Term.Bool ->
    __eo_typeof t = __eo_typeof s ∧
      __eo_typeof t = __eo_typeof r ∧
      __eo_typeof t ≠ Term.Stuck := by
  intro h
  change __eo_typeof_eq
    (__eo_typeof (mkEq (mkEq t s) (mkEq t r)))
    (__eo_typeof (mkAnd (mkNot (mkEq t s))
      (mkAnd (mkNot (mkEq t r)) (Term.Boolean true)))) = Term.Bool at h
  have hLeftNotStuck :
      __eo_typeof (mkEq (mkEq t s) (mkEq t r)) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ h).1
  change __eo_typeof_eq (__eo_typeof (mkEq t s)) (__eo_typeof (mkEq t r))
    ≠ Term.Stuck at hLeftNotStuck
  have hLeftBool :
      __eo_typeof_eq (__eo_typeof (mkEq t s)) (__eo_typeof (mkEq t r)) =
        Term.Bool :=
    eo_typeof_eq_nonstuck_bool _ _ hLeftNotStuck
  have hEqTsNotStuck : __eo_typeof (mkEq t s) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftBool).1
  have hEqTrNotStuck : __eo_typeof (mkEq t r) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftBool).2
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof s) ≠ Term.Stuck
    at hEqTsNotStuck
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof r) ≠ Term.Stuck
    at hEqTrNotStuck
  have hEqTsBool :
      __eo_typeof_eq (__eo_typeof t) (__eo_typeof s) = Term.Bool :=
    eo_typeof_eq_nonstuck_bool _ _ hEqTsNotStuck
  have hEqTrBool :
      __eo_typeof_eq (__eo_typeof t) (__eo_typeof r) = Term.Bool :=
    eo_typeof_eq_nonstuck_bool _ _ hEqTrNotStuck
  exact ⟨RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hEqTsBool,
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hEqTrBool,
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hEqTsBool).1⟩

private theorem smtx_model_eval_eq_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

private theorem smt_value_rel_eq_cond_deq
    (vt vs vr : SmtValue)
    (hsr : __smtx_model_eval_eq vs vr = SmtValue.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq
        (__smtx_model_eval_eq vt vs)
        (__smtx_model_eval_eq vt vr))
      (__smtx_model_eval_and
        (__smtx_model_eval_not (__smtx_model_eval_eq vt vs))
        (__smtx_model_eval_and
          (__smtx_model_eval_not (__smtx_model_eval_eq vt vr))
          (SmtValue.Boolean true))) := by
  rcases smtx_model_eval_eq_boolean vt vs with ⟨bts, hTs⟩
  rcases smtx_model_eval_eq_boolean vt vr with ⟨btr, hTr⟩
  cases bts <;> cases btr
  · rw [hTs, hTr]
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
      __smtx_model_eval_and, __smtx_model_eval_not, native_veq,
      SmtEval.native_and, SmtEval.native_not]
  · rw [hTs, hTr]
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
      __smtx_model_eval_and, __smtx_model_eval_not, native_veq,
      SmtEval.native_and, SmtEval.native_not]
  · rw [hTs, hTr]
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
      __smtx_model_eval_and, __smtx_model_eval_not, native_veq,
      SmtEval.native_and, SmtEval.native_not]
  · have hVsVt : RuleProofs.smt_value_rel vs vt :=
      RuleProofs.smt_value_rel_symm vt vs hTs
    have hVsVr : RuleProofs.smt_value_rel vs vr :=
      RuleProofs.smt_value_rel_trans vs vt vr hVsVt hTr
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hVsVr
    rw [hVsVr] at hsr
    cases hsr

private theorem typed_eq_cond_deq_body_impl
    (t s r : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation r ->
    __eo_typeof (eqCondDeqBody t s r) = Term.Bool ->
    RuleProofs.eo_has_bool_type (eqCondDeqBody t s r) := by
  intro hTTrans hSTrans hRTrans hBodyTy
  rcases operand_types_of_eq_cond_deq_body_bool t s r hBodyTy with
    ⟨hTS, hTR, _hTNN⟩
  have hTSmtTy :
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTTrans rfl
  have hSSmtTy :
      __smtx_typeof (__eo_to_smt s) = __eo_to_smt_type (__eo_typeof s) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s (__eo_typeof s) (__eo_to_smt s) rfl hSTrans rfl
  have hRSmtTy :
      __smtx_typeof (__eo_to_smt r) = __eo_to_smt_type (__eo_typeof r) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      r (__eo_typeof r) (__eo_to_smt r) rfl hRTrans rfl
  have hSameTS :
      __smtx_typeof (__eo_to_smt t) = __smtx_typeof (__eo_to_smt s) := by
    rw [hTSmtTy, hSSmtTy, hTS]
  have hSameTR :
      __smtx_typeof (__eo_to_smt t) = __smtx_typeof (__eo_to_smt r) := by
    rw [hTSmtTy, hRSmtTy, hTR]
  have hEqTS : RuleProofs.eo_has_bool_type (mkEq t s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t s hSameTS hTTrans
  have hEqTR : RuleProofs.eo_has_bool_type (mkEq t r) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t r hSameTR hTTrans
  have hEqEq : RuleProofs.eo_has_bool_type (mkEq (mkEq t s) (mkEq t r)) :=
    CnfSupport.eo_has_bool_type_eq_of_bool_args (mkEq t s) (mkEq t r)
      hEqTS hEqTR
  have hNotTS : RuleProofs.eo_has_bool_type (mkNot (mkEq t s)) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg (mkEq t s) hEqTS
  have hNotTR : RuleProofs.eo_has_bool_type (mkNot (mkEq t r)) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg (mkEq t r) hEqTR
  have hInnerAnd :
      RuleProofs.eo_has_bool_type
        (mkAnd (mkNot (mkEq t r)) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkNot (mkEq t r)) (Term.Boolean true) hNotTR
      RuleProofs.eo_has_bool_type_true
  have hRhs :
      RuleProofs.eo_has_bool_type
        (mkAnd (mkNot (mkEq t s))
          (mkAnd (mkNot (mkEq t r)) (Term.Boolean true))) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args
      (mkNot (mkEq t s))
      (mkAnd (mkNot (mkEq t r)) (Term.Boolean true))
      hNotTS hInnerAnd
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (mkEq (mkEq t s) (mkEq t r))
    (mkAnd (mkNot (mkEq t s))
      (mkAnd (mkNot (mkEq t r)) (Term.Boolean true)))
    hEqEq hRhs

private theorem typed___eo_prog_eq_cond_deq_impl
    (t s r s2 r2 : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation r ->
    __eo_typeof
      (__eo_prog_eq_cond_deq t s r
        (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false)))) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_eq_cond_deq t s r
        (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false)))) := by
  intro hTTrans hSTrans hRTrans hResultTy
  have hTNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hSNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hRNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProg :
      __eo_prog_eq_cond_deq t s r
        (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false))) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [prog_eq_cond_deq_eq t s r s2 r2 hTNotStuck hSNotStuck hRNotStuck]
    at hProg hResultTy
  rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
      s r s2 r2 (eqCondDeqBody t s r) hProg with
    ⟨hS2, hR2⟩
  subst s2
  subst r2
  have hBodyTy : __eo_typeof (eqCondDeqBody t s r) = Term.Bool := by
    simpa [requires_and_eq_self_true_body s r (eqCondDeqBody t s r)
      hSNotStuck hRNotStuck] using hResultTy
  rw [prog_eq_cond_deq_eq t s r s r hTNotStuck hSNotStuck hRNotStuck]
  rw [requires_and_eq_self_true_body s r (eqCondDeqBody t s r)
    hSNotStuck hRNotStuck]
  exact typed_eq_cond_deq_body_impl t s r hTTrans hSTrans hRTrans hBodyTy

private theorem facts___eo_prog_eq_cond_deq_impl
    (M : SmtModel) (hM : model_wf M) (t s r s2 r2 : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation s ->
    RuleProofs.eo_has_smt_translation r ->
    __eo_typeof
      (__eo_prog_eq_cond_deq t s r
        (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false)))) = Term.Bool ->
    eo_interprets M (mkEq (mkEq s2 r2) (Term.Boolean false)) true ->
    eo_interprets M
      (__eo_prog_eq_cond_deq t s r
        (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false)))) true := by
  intro hTTrans hSTrans hRTrans hResultTy hPremTrue
  have hTNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hSNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hRNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProg :
      __eo_prog_eq_cond_deq t s r
        (Proof.pf (mkEq (mkEq s2 r2) (Term.Boolean false))) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [prog_eq_cond_deq_eq t s r s2 r2 hTNotStuck hSNotStuck hRNotStuck]
    at hProg hResultTy
  rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
      s r s2 r2 (eqCondDeqBody t s r) hProg with
    ⟨hS2, hR2⟩
  subst s2
  subst r2
  have hBodyTy : __eo_typeof (eqCondDeqBody t s r) = Term.Bool := by
    simpa [requires_and_eq_self_true_body s r (eqCondDeqBody t s r)
      hSNotStuck hRNotStuck] using hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_eq_cond_deq t s r
          (Proof.pf (mkEq (mkEq s r) (Term.Boolean false)))) :=
    typed___eo_prog_eq_cond_deq_impl t s r s r
      hTTrans hSTrans hRTrans (by
        simpa [prog_eq_cond_deq_eq t s r s r hTNotStuck hSNotStuck hRNotStuck,
          requires_and_eq_self_true_body s r (eqCondDeqBody t s r)
            hSNotStuck hRNotStuck] using hBodyTy)
  have hSrFalse :
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt r)) = SmtValue.Boolean false :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M s r hPremTrue
  rw [prog_eq_cond_deq_eq t s r s r hTNotStuck hSNotStuck hRNotStuck]
  rw [requires_and_eq_self_true_body s r (eqCondDeqBody t s r)
    hSNotStuck hRNotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · -- v4.33 unfolds `eqCondDeqBody` in the goal, so peel the `__eo_requires`
    -- guard first and only then unfold, or the lemma instance stops matching.
    have hB : RuleProofs.eo_has_bool_type (eqCondDeqBody t s r) := by
      simpa [prog_eq_cond_deq_eq t s r s r hTNotStuck hSNotStuck hRNotStuck,
        requires_and_eq_self_true_body s r (eqCondDeqBody t s r)
          hSNotStuck hRNotStuck] using hProgBool
    simpa [eqCondDeqBody, mkEq, mkAnd, mkNot] using hB
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkEq (mkEq t s) (mkEq t r))))
      (__smtx_model_eval M
        (__eo_to_smt
          (mkAnd (mkNot (mkEq t s))
            (mkAnd (mkNot (mkEq t r)) (Term.Boolean true)))))
    rw [show __eo_to_smt (mkEq (mkEq t s) (mkEq t r)) =
        SmtTerm.eq (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt s))
          (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt r)) by rfl]
    rw [show __eo_to_smt
          (mkAnd (mkNot (mkEq t s))
            (mkAnd (mkNot (mkEq t r)) (Term.Boolean true))) =
        SmtTerm.and
          (SmtTerm.not (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt s)))
          (SmtTerm.and
            (SmtTerm.not (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt r)))
            (SmtTerm.Boolean true)) by rfl]
    simp [smtx_eval_eq_term_eq, smtx_eval_and_term_eq,
      smtx_eval_not_term_eq, __smtx_model_eval.eq_1]
    exact smt_value_rel_eq_cond_deq
      (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (__eo_to_smt r))
      hSrFalse

public theorem cmd_step_eq_cond_deq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_cond_deq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.eq_cond_deq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_cond_deq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.eq_cond_deq args premises ≠ Term.Stuck :=
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n1 premises =>
                      cases premises with
                      | nil =>
                          let T1 := a1
                          let S1 := a2
                          let R1 := a3
                          let P1 := __eo_state_proven_nth s n1
                          have hTranses :
                              RuleProofs.eo_has_smt_translation T1 ∧
                                RuleProofs.eo_has_smt_translation S1 ∧
                                RuleProofs.eo_has_smt_translation R1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk,
                              RuleProofs.eo_has_smt_translation,
                              eoHasSmtTranslation] using hCmdTrans
                          change __eo_typeof
                            (__eo_prog_eq_cond_deq T1 S1 R1 (Proof.pf P1)) =
                              Term.Bool at hResultTy
                          change __eo_prog_eq_cond_deq T1 S1 R1 (Proof.pf P1) ≠
                            Term.Stuck at hProg
                          rcases shape_of_prog_eq_cond_deq_not_stuck
                              T1 S1 R1 P1 hProg with
                            ⟨S2, R2, hP1⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremTrue :
                                eo_interprets M
                                  (mkEq (mkEq S2 R2) (Term.Boolean false)) true := by
                              have hStatePremTrue :=
                                hTrue (__eo_state_proven_nth s n1)
                                  (by simp [premiseTermList])
                              simpa [P1, hP1] using hStatePremTrue
                            change eo_interprets M
                              (__eo_prog_eq_cond_deq T1 S1 R1
                                (Proof.pf P1)) true
                            rw [hP1]
                            exact facts___eo_prog_eq_cond_deq_impl M hM
                              T1 S1 R1 S2 R2 hTranses.1 hTranses.2.1
                              hTranses.2.2 (by simpa [hP1] using hResultTy)
                              hPremTrue
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_eq_cond_deq T1 S1 R1
                                (Proof.pf P1))
                            rw [hP1]
                            exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_eq_cond_deq_impl T1 S1 R1 S2 R2
                                hTranses.1 hTranses.2.1 hTranses.2.2
                                (by simpa [hP1] using hResultTy))
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
