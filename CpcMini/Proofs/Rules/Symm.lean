module

public import CpcMini.Proofs.RuleSupport.Support
import all CpcMini.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shows that the EO program for `symm_impl` is well typed. -/
theorem typed___eo_prog_symm_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
by
  intro hXBool hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | Apply g b =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type b a hXBool with
                    ⟨hTy, hNonNone⟩
                  have hNonNone' : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                    simpa [hTy] using hNonNone
                  have hEqTy :
                      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
                        (__smtx_typeof (__eo_to_smt b)) = SmtType.Bool := by
                    exact (RuleProofs.smtx_typeof_eq_bool_iff
                      (__smtx_typeof (__eo_to_smt a))
                      (__smtx_typeof (__eo_to_smt b))).mpr ⟨hTy.symm, hNonNone'⟩
                  exact by
                    simp [RuleProofs.eo_has_bool_type, __eo_prog_symm, __mk_symm, __eo_to_smt,
                      __smtx_typeof, hEqTy]
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply f2 a2 =>
                  cases f2 with
                  | Apply g2 b2 =>
                      cases g2 with
                      | UOp op2 =>
                          cases op2 with
                          | eq =>
                              have hInnerBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b2) a2) :=
                                RuleProofs.eo_has_bool_type_not_arg
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b2) a2) hXBool
                              rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                  b2 a2 hInnerBool with
                                ⟨hTy, hNonNone⟩
                              have hNonNone' : __smtx_typeof (__eo_to_smt a2) ≠ SmtType.None := by
                                simpa [hTy] using hNonNone
                              have hEqTy :
                                  __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a2))
                                    (__smtx_typeof (__eo_to_smt b2)) = SmtType.Bool := by
                                exact (RuleProofs.smtx_typeof_eq_bool_iff
                                  (__smtx_typeof (__eo_to_smt a2))
                                  (__smtx_typeof (__eo_to_smt b2))).mpr ⟨hTy.symm, hNonNone'⟩
                              exact by
                                simp [RuleProofs.eo_has_bool_type, __eo_prog_symm, __mk_symm,
                                  __eo_to_smt, __smtx_typeof, hEqTy, native_ite, native_Teq]
                          | _ =>
                              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
                      | _ =>
                          exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
                  | _ =>
                      exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))

/-- Shows that `eo_interprets_not_false` implies `true`. -/
private theorem eo_interprets_not_false_implies_true (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) false -> eo_interprets M t true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_false hty hEval =>
      have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
        simp [__eo_to_smt, __smtx_typeof, native_Teq, native_ite] at hty
        exact hty
      cases ht : __smtx_model_eval M (__eo_to_smt t) <;>
        simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_not, ht] at hEval
      case Boolean b =>
        cases b <;> simp [SmtEval.native_not] at hEval
        exact smt_interprets.intro_true M (__eo_to_smt t) htyt ht

/-- Establishes an equality relating `eo_interprets` and `symm_true`. -/
private theorem eo_interprets_eq_symm_true (M : SmtModel) (a b : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) a) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true := by
  intro hEqTrue
  rcases RuleProofs.eo_eq_operands_same_smt_type M b a hEqTrue with ⟨hTy, hNonNone⟩
  have hNonNone' : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
    simpa [hTy] using hNonNone
  have hTySymm :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
    have hEqTy :
        __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
          (__smtx_typeof (__eo_to_smt b)) = SmtType.Bool := by
      exact (RuleProofs.smtx_typeof_eq_bool_iff
        (__smtx_typeof (__eo_to_smt a)) (__smtx_typeof (__eo_to_smt b))).mpr
          ⟨hTy.symm, hNonNone'⟩
    simpa [RuleProofs.eo_has_bool_type, __eo_to_smt, __smtx_typeof] using hEqTy
  apply RuleProofs.eo_interprets_eq_of_rel M a b
  · exact hTySymm
  · exact RuleProofs.smt_value_rel_symm M _ _ (RuleProofs.eo_interprets_eq_rel M b a hEqTrue)

/-- Proves correctness of the EO program for `symm_impl`. -/
theorem correct___eo_prog_symm_impl
    (M : SmtModel) (_hM : model_wf M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  intro hXTrue hTy
  have hProgNotStuck : __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hTy
  cases x1 with
  | Apply f a =>
      cases f with
      | Apply g b =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  simpa [__eo_prog_symm, __mk_symm] using
                    eo_interprets_eq_symm_true M a b hXTrue
              | _ =>
                  exfalso
                  exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
          | _ =>
              exfalso
              exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply f2 a2 =>
                  cases f2 with
                  | Apply g2 b2 =>
                      cases g2 with
                      | UOp op2 =>
                          cases op2 with
                          | eq =>
                              let symmEq := Term.Apply (Term.Apply (Term.UOp UserOp.eq) a2) b2
                              let symmNot := Term.Apply (Term.UOp UserOp.not) symmEq
                              rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M _hM symmNot hTy with
                                ⟨bsymm, hEvalSymmNot⟩
                              cases bsymm with
                              | true =>
                                  exact RuleProofs.eo_interprets_of_bool_eval
                                    M symmNot true hTy hEvalSymmNot
                              | false =>
                                  have hSymmNotFalse : eo_interprets M symmNot false :=
                                    RuleProofs.eo_interprets_of_bool_eval
                                      M symmNot false hTy hEvalSymmNot
                                  have hSymmEqTrue : eo_interprets M symmEq true :=
                                    eo_interprets_not_false_implies_true M symmEq hSymmNotFalse
                                  have hOrigEqTrue :
                                      eo_interprets M
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b2) a2) true :=
                                    eo_interprets_eq_symm_true M b2 a2 hSymmEqTrue
                                  have hOrigEqFalse :
                                      eo_interprets M
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b2) a2) false :=
                                    RuleProofs.eo_interprets_not_true_implies_false M _ hXTrue
                                  exact False.elim
                                    ((RuleProofs.eo_interprets_true_not_false M _ hOrigEqTrue)
                                      hOrigEqFalse)
                          | _ =>
                              exfalso
                              exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
                      | _ =>
                          exfalso
                          exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
                  | _ =>
                      exfalso
                      exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
              | _ =>
                  exfalso
                  exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
          | _ =>
              exfalso
              exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
      | _ =>
          exfalso
          exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])
  | _ =>
      exfalso
      exact hProgNotStuck (by simp [__eo_prog_symm, __mk_symm])

/-- Derives the checker facts exposed by the EO program for `symm_impl`. -/
theorem facts___eo_prog_symm_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_symm (Proof.pf x1)) true :=
by
  intro hXTrue hProg
  let hXBool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hXTrue
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
    typed___eo_prog_symm_impl x1 hXBool hProg
  exact correct___eo_prog_symm_impl M hM x1 hXTrue hBool

/-- Packages the properties required for the `symm` checker step. -/
public theorem cmd_step_symm_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.symm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.symm args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.symm args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X := __eo_state_proven_nth s n1
              refine ⟨?_, ?_⟩
              · intro hEvidence
                exact facts___eo_prog_symm_impl M hM X
                  (hEvidence.true_here X (by simp [X, premiseTermList]))
                  (by simpa [X, premiseTermList, __eo_cmd_step_proven] using hProg)
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_symm_impl X
                    (hPremisesBool X (by simp [X, premiseTermList]))
                    (by simpa [X, premiseTermList, __eo_cmd_step_proven] using hProg))
          | cons n2 premises =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
