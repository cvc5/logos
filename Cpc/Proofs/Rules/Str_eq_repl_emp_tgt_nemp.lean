module

public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev empTgtEmptyPremise (emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len emp))
    (Term.Numeral 0)

private abbrev empTgtNonemptyPremise (z emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq z) emp))
    (Term.Boolean false)

private abbrev empTgtValue (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z

private abbrev empTgtLhs (x y z emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (empTgtValue x y z)) emp

private abbrev empTgtRhs (x y emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x) emp))
    (Term.Apply
      (Term.Apply Term.and
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq y) emp)))
      (Term.Boolean true))

private abbrev empTgtConclusion (x y z emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (empTgtLhs x y z emp))
    (empTgtRhs x y emp)

private theorem prog_str_eq_repl_emp_tgt_nemp_info
    (x y z emp P1 P2 : Term)
    (hProg :
      __eo_prog_str_eq_repl_emp_tgt_nemp x y z emp
          (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck) :
    ∃ emp0 z0 emp1,
      P1 = empTgtEmptyPremise emp0 ∧
      P2 = empTgtNonemptyPremise z0 emp1 ∧
      emp0 = emp ∧ z0 = z ∧ emp1 = emp ∧
      __eo_prog_str_eq_repl_emp_tgt_nemp x y z emp
          (Proof.pf P1) (Proof.pf P2) =
        empTgtConclusion x y z emp := by
  unfold __eo_prog_str_eq_repl_emp_tgt_nemp at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases eqs_of_requires3_and_eq_true_not_stuck hProg with
      ⟨hEmp0, hZ0, hEmp1⟩
    subst_vars
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_eq_repl_emp_tgt_nemp, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, empTgtConclusion, empTgtLhs, empTgtRhs,
      empTgtValue]

private theorem typed___eo_prog_str_eq_repl_emp_tgt_nemp_impl
    (x y z emp P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_eq_repl_emp_tgt_nemp x y z emp
          (Proof.pf P1) (Proof.pf P2) =
        empTgtConclusion x y z emp) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_eq_repl_emp_tgt_nemp x y z emp
        (Proof.pf P1) (Proof.pf P2)) := by
  let value := empTgtValue x y z
  let lhs := empTgtLhs x y z emp
  let eqXEmp := Term.Apply (Term.Apply Term.eq x) emp
  let eqYEmp := Term.Apply (Term.Apply Term.eq y) emp
  let notEqYEmp := Term.Apply Term.not eqYEmp
  let innerAnd := Term.Apply (Term.Apply Term.and notEqYEmp) (Term.Boolean true)
  let rhs := empTgtRhs x y emp
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type value emp
      (by rw [hValueTy, hEmpSmtTy]) (by rw [hValueTy]; simp)
  have hEqXEmpTy : __smtx_typeof (__eo_to_smt eqXEmp) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x emp
      (by rw [hXSmtTy, hEmpSmtTy]) (by rw [hXSmtTy]; simp)
  have hEqYEmpTy : __smtx_typeof (__eo_to_smt eqYEmp) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type y emp
      (by rw [hYSmtTy, hEmpSmtTy]) (by rw [hYSmtTy]; simp)
  have hNotEqYEmpTy :
      __smtx_typeof (__eo_to_smt notEqYEmp) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.not (__eo_to_smt eqYEmp)) = SmtType.Bool
    rw [typeof_not_eq, hEqYEmpTy]
    simp [native_ite, native_Teq]
  have hInnerAndTy :
      __smtx_typeof (__eo_to_smt innerAnd) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.and (__eo_to_smt notEqYEmp) (SmtTerm.Boolean true)) =
      SmtType.Bool
    rw [typeof_and_eq]
    simp [hNotEqYEmpTy, __smtx_typeof.eq_1, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.and (__eo_to_smt eqXEmp) (__eo_to_smt innerAnd)) =
      SmtType.Bool
    rw [typeof_and_eq]
    simp [hEqXEmpTy, hInnerAndTy, native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (empTgtConclusion x y z emp) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_eq_repl_emp_tgt_nemp_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z emp P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (empTgtEmptyPremise emp) true)
    (hPrem2 : eo_interprets M (empTgtNonemptyPremise z emp) true)
    (hProgEq :
      __eo_prog_str_eq_repl_emp_tgt_nemp x y z emp
          (Proof.pf P1) (Proof.pf P2) =
        empTgtConclusion x y z emp) :
    eo_interprets M
      (__eo_prog_str_eq_repl_emp_tgt_nemp x y z emp
        (Proof.pf P1) (Proof.pf P2)) true := by
  let lhs := empTgtLhs x y z emp
  let rhs := empTgtRhs x y emp
  have hBool : RuleProofs.eo_has_bool_type
      (empTgtConclusion x y z emp) := by
    simpa [hProgEq] using
      typed___eo_prog_str_eq_repl_emp_tgt_nemp_impl x y z emp P1 P2
        hXTrans hYTrans hZTrans hEmpTrans hXTy hYTy hZTy hEmpTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  have hZEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt z)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hZSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt z) (by
        unfold term_has_non_none_type
        rw [hZSmtTy]
        simp)
  have hEmpEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt emp)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hEmpSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt emp) (by
        unfold term_has_non_none_type
        rw [hEmpSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  rcases seq_value_canonical hEmpEvalTy with ⟨semp, hEmpEval⟩
  have hEmpNil : native_unpack_seq semp = [] := by
    have hLenZero : native_seq_len (native_unpack_seq semp) = 0 := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
      cases hPrem1 with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt emp))
                (SmtTerm.Numeral 0)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hEmpEval,
            smtx_eval_numeral_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq] using hEval
    exact list_eq_nil_of_native_seq_len_zero _ hLenZero
  have hZEmpNe : sz ≠ semp := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (__eo_to_smt z) (__eo_to_smt emp))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq, hZEval, hEmpEval,
          smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_eq, native_veq] using hEval
  have hSxTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSyTy :
      __smtx_typeof_seq_value sy = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hYEval] using hYEvalTy
  have hSzTy :
      __smtx_typeof_seq_value sz = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hZEval] using hZEvalTy
  have hSempTy :
      __smtx_typeof_seq_value semp = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hEmpEval] using hEmpEvalTy
  have hSxElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSyElem : __smtx_elem_typeof_seq_value sy = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  have hSzElem : __smtx_elem_typeof_seq_value sz = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSzTy
  have hSempElem : __smtx_elem_typeof_seq_value semp = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSempTy
  have hZNonempty : native_unpack_seq sz ≠ [] := by
    intro hZNil
    apply hZEmpNe
    exact seq_eq_of_unpack_eq_of_elem_eq sz semp
      (by rw [hSzElem, hSempElem]) (by rw [hZNil, hEmpNil])
  have hValueIff :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
            (native_unpack_seq sz)) = semp ↔
        sx = semp ∧ sy ≠ semp := by
    constructor
    · intro hValue
      have hLists := congrArg native_unpack_seq hValue
      have hReplace :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
              (native_unpack_seq sz) = [] := by
        simpa [Smtm.native_unpack_pack_seq, hEmpNil] using hLists
      rcases (native_seq_replace_eq_nil_iff_of_repl_ne_nil _ _ _
          hZNonempty).mp hReplace with ⟨hXNil, hYNonempty⟩
      refine ⟨?_, ?_⟩
      · exact seq_eq_of_unpack_eq_of_elem_eq sx semp
          (by rw [hSxElem, hSempElem]) (by rw [hXNil, hEmpNil])
      · intro hYEmp
        have hYUnpack := congrArg native_unpack_seq hYEmp
        exact hYNonempty (by simpa [hEmpNil] using hYUnpack)
    · rintro ⟨hXEmp, hYEmp⟩
      have hXNil : native_unpack_seq sx = [] := by
        have := congrArg native_unpack_seq hXEmp
        simpa [hEmpNil] using this
      have hYNonempty : native_unpack_seq sy ≠ [] := by
        intro hYNil
        apply hYEmp
        exact seq_eq_of_unpack_eq_of_elem_eq sy semp
          (by rw [hSyElem, hSempElem]) (by rw [hYNil, hEmpNil])
      have hReplace :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
              (native_unpack_seq sz) = [] :=
        (native_seq_replace_eq_nil_iff_of_repl_ne_nil _ _ _ hZNonempty).2
          ⟨hXNil, hYNonempty⟩
      rw [hReplace, hSxElem]
      simpa [hSempElem, hEmpNil] using native_pack_unpack_seq semp
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt emp)) =
      __smtx_model_eval M
        (SmtTerm.and (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt emp))
          (SmtTerm.and
            (SmtTerm.not (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt emp)))
            (SmtTerm.Boolean true)))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_and_term_eq, smtx_eval_eq_term_eq, smtx_eval_and_term_eq,
      smtx_eval_not_term_eq, smtx_eval_eq_term_eq, hXEval, hYEval, hZEval,
      hEmpEval, smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_eq,
      __smtx_model_eval_and, __smtx_model_eval_not, native_veq, native_and,
      SmtEval.native_not, hValueIff]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_repl_emp_tgt_nemp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_emp_tgt_nemp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_repl_emp_tgt_nemp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_emp_tgt_nemp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_repl_emp_tgt_nemp args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons a3 args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons a4 args =>
                  cases args with
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | nil => exact absurd rfl hProg
                      | cons n1 premises =>
                          cases premises with
                          | nil => exact absurd rfl hProg
                          | cons n2 premises =>
                              cases premises with
                              | cons _ _ => exact absurd rfl hProg
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  let P2 := __eo_state_proven_nth s n2
                                  have hA1Trans :
                                      RuleProofs.eo_has_smt_translation a1 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.1
                                  have hA2Trans :
                                      RuleProofs.eo_has_smt_translation a2 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.2.1
                                  have hA3Trans :
                                      RuleProofs.eo_has_smt_translation a3 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.2.1
                                  have hA4Trans :
                                      RuleProofs.eo_has_smt_translation a4 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.2.2.1
                                  change __eo_typeof
                                      (__eo_prog_str_eq_repl_emp_tgt_nemp
                                        a1 a2 a3 a4 (Proof.pf P1)
                                        (Proof.pf P2)) =
                                    Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_eq_repl_emp_tgt_nemp
                                          a1 a2 a3 a4 (Proof.pf P1)
                                          (Proof.pf P2) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_eq_repl_emp_tgt_nemp_info
                                      a1 a2 a3 a4 P1 P2 hRuleProg with
                                    ⟨emp0, z0, emp1, hP1, hP2, hEmp0, hZ0,
                                      hEmp1, hProgEq⟩
                                  subst emp0
                                  subst z0
                                  subst emp1
                                  rw [hProgEq] at hResultTy
                                  have hOuterLeftTy :
                                      __eo_typeof
                                          (empTgtLhs a1 a2 a3 a4) ≠
                                        Term.Stuck := by
                                    change __eo_typeof_eq
                                        (__eo_typeof
                                          (empTgtLhs a1 a2 a3 a4))
                                        (__eo_typeof
                                          (empTgtRhs a1 a2 a4)) =
                                      Term.Bool at hResultTy
                                    exact
                                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                        (__eo_typeof
                                          (empTgtLhs a1 a2 a3 a4))
                                        (__eo_typeof
                                          (empTgtRhs a1 a2 a4))
                                        hResultTy).1
                                  have hInnerLeftBool :
                                      __eo_typeof
                                          (empTgtLhs a1 a2 a3 a4) =
                                        Term.Bool := by
                                    change __eo_typeof_eq
                                        (__eo_typeof
                                          (empTgtValue a1 a2 a3))
                                        (__eo_typeof a4) = Term.Bool
                                    exact eo_typeof_eq_nonstuck_bool _ _
                                      hOuterLeftTy
                                  have hValueTy :
                                      __eo_typeof
                                          (empTgtValue a1 a2 a3) ≠
                                        Term.Stuck := by
                                    change __eo_typeof_eq
                                        (__eo_typeof
                                          (empTgtValue a1 a2 a3))
                                        (__eo_typeof a4) =
                                      Term.Bool at hInnerLeftBool
                                    exact
                                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                        (__eo_typeof
                                          (empTgtValue a1 a2 a3))
                                        (__eo_typeof a4)
                                        hInnerLeftBool).1
                                  rcases
                                      eo_typeof_str_replace_args_of_ne_stuck
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) hValueTy with
                                    ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                                  have hValueTyEq :
                                      __eo_typeof
                                          (empTgtValue a1 a2 a3) =
                                        Term.Apply Term.Seq T := by
                                    change __eo_typeof_str_replace
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) =
                                      Term.Apply Term.Seq T
                                    have hValueNN := hValueTy
                                    change __eo_typeof_str_replace
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) ≠
                                      Term.Stuck at hValueNN
                                    rw [hA1Ty, hA2Ty, hA3Ty] at hValueNN
                                    rw [hA1Ty, hA2Ty, hA3Ty]
                                    exact
                                      eo_typeof_str_replace_result_of_seq_args
                                        T hValueNN
                                  have hSameTy :
                                      __eo_typeof
                                          (empTgtValue a1 a2 a3) =
                                        __eo_typeof a4 :=
                                    RuleProofs.eo_typeof_eq_bool_operands_eq
                                      (__eo_typeof
                                        (empTgtValue a1 a2 a3))
                                      (__eo_typeof a4) hInnerLeftBool
                                  have hA4Ty :
                                      __eo_typeof a4 =
                                        Term.Apply Term.Seq T := by
                                    rw [← hSameTy]
                                    exact hValueTyEq
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem1Raw :
                                        eo_interprets M P1 true :=
                                      hTrue P1 (by
                                        simp [P1, premiseTermList])
                                    have hPrem2Raw :
                                        eo_interprets M P2 true :=
                                      hTrue P2 (by
                                        simp [P2, premiseTermList])
                                    have hPrem1 :
                                        eo_interprets M
                                          (empTgtEmptyPremise a4) true := by
                                      simpa [hP1] using hPrem1Raw
                                    have hPrem2 :
                                        eo_interprets M
                                          (empTgtNonemptyPremise a3 a4)
                                          true := by
                                      simpa [hP2] using hPrem2Raw
                                    exact
                                      facts___eo_prog_str_eq_repl_emp_tgt_nemp_impl
                                        M hM a1 a2 a3 a4 P1 P2 hA1Trans
                                        hA2Trans hA3Trans hA4Trans hA1Ty
                                        hA2Ty hA3Ty hA4Ty hPrem1 hPrem2
                                        hProgEq
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (typed___eo_prog_str_eq_repl_emp_tgt_nemp_impl
                                          a1 a2 a3 a4 P1 P2 hA1Trans
                                          hA2Trans hA3Trans hA4Trans hA1Ty
                                          hA2Ty hA3Ty hA4Ty hProgEq)
