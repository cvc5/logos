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

private abbrev lenOneEmpEmptyPremise (emp : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len emp))
    (Term.Numeral 0)

private abbrev lenOneEmpLengthPremise (y : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len y))
    (Term.Numeral 1)

private abbrev lenOneEmpValue (x y emp : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) emp

private abbrev lenOneEmpLhs (x y emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lenOneEmpValue x y emp)) emp

private abbrev lenOneEmpRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.str_prefixof x) y

private abbrev lenOneEmpConclusion (x y emp : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lenOneEmpLhs x y emp))
    (lenOneEmpRhs x y)

private theorem prog_str_eq_repl_len_one_emp_prefix_info
    (x y emp P1 P2 : Term)
    (hProg :
      __eo_prog_str_eq_repl_len_one_emp_prefix x y emp
          (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck) :
    ∃ emp0 y0,
      P1 = lenOneEmpEmptyPremise emp0 ∧
      P2 = lenOneEmpLengthPremise y0 ∧
      emp0 = emp ∧ y0 = y ∧
      __eo_prog_str_eq_repl_len_one_emp_prefix x y emp
          (Proof.pf P1) (Proof.pf P2) =
        lenOneEmpConclusion x y emp := by
  unfold __eo_prog_str_eq_repl_len_one_emp_prefix at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hEmp, hY⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_eq_repl_len_one_emp_prefix, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, lenOneEmpConclusion, lenOneEmpLhs,
      lenOneEmpRhs, lenOneEmpValue]

private theorem typed___eo_prog_str_eq_repl_len_one_emp_prefix_impl
    (x y emp P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_eq_repl_len_one_emp_prefix x y emp
          (Proof.pf P1) (Proof.pf P2) =
        lenOneEmpConclusion x y emp) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_eq_repl_len_one_emp_prefix x y emp
        (Proof.pf P1) (Proof.pf P2)) := by
  let value := lenOneEmpValue x y emp
  let lhs := lenOneEmpLhs x y emp
  let rhs := lenOneEmpRhs x y
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hEmpSmtTy := smtx_typeof_of_eo_seq emp T hEmpTrans hEmpTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt emp)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hEmpSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type value emp
      (by rw [hValueTy, hEmpSmtTy]) (by rw [hValueTy]; simp)
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_prefixof (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_prefixof_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (lenOneEmpConclusion x y emp) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_eq_repl_len_one_emp_prefix_impl
    (M : SmtModel) (hM : model_wf M)
    (x y emp P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hEmpTrans : RuleProofs.eo_has_smt_translation emp)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hEmpTy : __eo_typeof emp = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (lenOneEmpEmptyPremise emp) true)
    (hPrem2 : eo_interprets M (lenOneEmpLengthPremise y) true)
    (hProgEq :
      __eo_prog_str_eq_repl_len_one_emp_prefix x y emp
          (Proof.pf P1) (Proof.pf P2) =
        lenOneEmpConclusion x y emp) :
    eo_interprets M
      (__eo_prog_str_eq_repl_len_one_emp_prefix x y emp
        (Proof.pf P1) (Proof.pf P2)) true := by
  let lhs := lenOneEmpLhs x y emp
  let rhs := lenOneEmpRhs x y
  have hBool : RuleProofs.eo_has_bool_type
      (lenOneEmpConclusion x y emp) := by
    simpa [hProgEq] using
      typed___eo_prog_str_eq_repl_len_one_emp_prefix_impl
        x y emp P1 P2 hXTrans hYTrans hEmpTrans hXTy hYTy hEmpTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
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
  have hYLen : (native_unpack_seq sy).length = 1 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt y))
              (SmtTerm.Numeral 1)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hYEval,
          smtx_eval_numeral_term_eq] at hEval
        have hLenInt :
            (Int.ofNat (native_unpack_seq sy).length : Int) = 1 := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        change Int.ofNat (native_unpack_seq sy).length = Int.ofNat 1 at hLenInt
        exact Int.ofNat.inj hLenInt
  have hSxTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSyTy :
      __smtx_typeof_seq_value sy = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hYEval] using hYEvalTy
  have hSempTy :
      __smtx_typeof_seq_value semp = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hEmpEval] using hEmpEvalTy
  have hSxElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSyElem : __smtx_elem_typeof_seq_value sy = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  have hSempElem : __smtx_elem_typeof_seq_value semp = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSempTy
  have hYNonempty : native_unpack_seq sy ≠ [] := by
    intro hNil
    rw [hNil] at hYLen
    contradiction
  have hValueIff :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
            (native_unpack_seq semp)) = semp ↔
        native_unpack_seq sx = [] ∨ sx = sy := by
    constructor
    · intro hValue
      have hLists := congrArg native_unpack_seq hValue
      have hReplace :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
              [] = [] := by
        simpa [Smtm.native_unpack_pack_seq, hEmpNil] using hLists
      rcases
          (native_seq_replace_empty_repl_eq_nil_iff_of_pat_ne_nil
            _ _ hYNonempty).mp hReplace with hXNil | hXY
      · exact Or.inl hXNil
      · exact Or.inr <|
          seq_eq_of_unpack_eq_of_elem_eq sx sy
            (by rw [hSxElem, hSyElem]) hXY
    · intro hCases
      have hListCases :
          native_unpack_seq sx = [] ∨
            native_unpack_seq sx = native_unpack_seq sy := by
        rcases hCases with hXNil | hXY
        · exact Or.inl hXNil
        · exact Or.inr (congrArg native_unpack_seq hXY)
      have hReplace :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
              [] = [] :=
        (native_seq_replace_empty_repl_eq_nil_iff_of_pat_ne_nil
          _ _ hYNonempty).2 hListCases
      rw [hEmpNil, hReplace, hSxElem]
      simpa [hSempElem, hEmpNil] using native_pack_unpack_seq semp
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt emp))
          (__eo_to_smt emp)) =
      __smtx_model_eval M
        (SmtTerm.str_prefixof (__eo_to_smt x) (__eo_to_smt y))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_str_prefixof_term_eq, hXEval, hYEval, hEmpEval,
      smtx_eval_str_prefixof_len_one_eq sx sy (__eo_to_smt_type T)
        hSxTy hSyTy hYLen]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_eq,
      native_veq, hValueIff]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_repl_len_one_emp_prefix_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_len_one_emp_prefix args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_repl_len_one_emp_prefix args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_len_one_emp_prefix args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_repl_len_one_emp_prefix args premises ≠
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
                              change __eo_typeof
                                  (__eo_prog_str_eq_repl_len_one_emp_prefix
                                    a1 a2 a3 (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_eq_repl_len_one_emp_prefix
                                      a1 a2 a3 (Proof.pf P1) (Proof.pf P2) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases
                                  prog_str_eq_repl_len_one_emp_prefix_info
                                    a1 a2 a3 P1 P2 hRuleProg with
                                ⟨emp0, y0, hP1, hP2, hEmp0, hY0, hProgEq⟩
                              subst emp0
                              subst y0
                              rw [hProgEq] at hResultTy
                              have hOuterLeftTy :
                                  __eo_typeof
                                      (lenOneEmpLhs a1 a2 a3) ≠
                                    Term.Stuck := by
                                change __eo_typeof_eq
                                    (__eo_typeof (lenOneEmpLhs a1 a2 a3))
                                    (__eo_typeof (lenOneEmpRhs a1 a2)) =
                                  Term.Bool at hResultTy
                                exact
                                  (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                    (__eo_typeof (lenOneEmpLhs a1 a2 a3))
                                    (__eo_typeof (lenOneEmpRhs a1 a2))
                                    hResultTy).1
                              have hInnerLeftBool :
                                  __eo_typeof (lenOneEmpLhs a1 a2 a3) =
                                    Term.Bool := by
                                change __eo_typeof_eq
                                    (__eo_typeof (lenOneEmpValue a1 a2 a3))
                                    (__eo_typeof a3) = Term.Bool
                                exact eo_typeof_eq_nonstuck_bool _ _
                                  hOuterLeftTy
                              have hValueTy :
                                  __eo_typeof
                                      (lenOneEmpValue a1 a2 a3) ≠
                                    Term.Stuck := by
                                change __eo_typeof_eq
                                    (__eo_typeof (lenOneEmpValue a1 a2 a3))
                                    (__eo_typeof a3) =
                                  Term.Bool at hInnerLeftBool
                                exact
                                  (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                    (__eo_typeof
                                      (lenOneEmpValue a1 a2 a3))
                                    (__eo_typeof a3) hInnerLeftBool).1
                              rcases eo_typeof_str_replace_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a2)
                                  (__eo_typeof a3) hValueTy with
                                ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPrem1Raw : eo_interprets M P1 true :=
                                  hTrue P1 (by
                                    simp [P1, premiseTermList])
                                have hPrem2Raw : eo_interprets M P2 true :=
                                  hTrue P2 (by
                                    simp [P2, premiseTermList])
                                have hPrem1 :
                                    eo_interprets M
                                      (lenOneEmpEmptyPremise a3) true := by
                                  simpa [hP1] using hPrem1Raw
                                have hPrem2 :
                                    eo_interprets M
                                      (lenOneEmpLengthPremise a2) true := by
                                  simpa [hP2] using hPrem2Raw
                                exact
                                  facts___eo_prog_str_eq_repl_len_one_emp_prefix_impl
                                    M hM a1 a2 a3 P1 P2 hA1Trans hA2Trans
                                    hA3Trans hA1Ty hA2Ty hA3Ty hPrem1 hPrem2
                                    hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_eq_repl_len_one_emp_prefix_impl
                                      a1 a2 a3 P1 P2 hA1Trans hA2Trans
                                      hA3Trans hA1Ty hA2Ty hA3Ty hProgEq)
