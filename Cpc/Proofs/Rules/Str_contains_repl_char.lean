module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev containsReplCharLengthPremise (w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len w))
    (Term.Numeral 1)

private abbrev containsReplCharAbsentPremise (y w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains y) w))
    (Term.Boolean false)

private abbrev containsReplCharValue (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z

private abbrev containsReplCharContains (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) y

private abbrev containsReplCharLhs (x y z w : Term) : Term :=
  containsReplCharContains (containsReplCharValue x y z) w

private abbrev containsReplCharRhs (x y z w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.or (containsReplCharContains x w))
    (Term.Apply
      (Term.Apply Term.or
        (Term.Apply
          (Term.Apply Term.and (containsReplCharContains x y))
          (Term.Apply
            (Term.Apply Term.and (containsReplCharContains z w))
            (Term.Boolean true))))
      (Term.Boolean false))

private abbrev containsReplCharConclusion (x y z w : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (containsReplCharLhs x y z w))
    (containsReplCharRhs x y z w)

private theorem prog_str_contains_repl_char_info
    (x y z w P1 P2 : Term)
    (hProg :
      __eo_prog_str_contains_repl_char x y z w
          (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck) :
    ∃ w0 y0 w1,
      P1 = containsReplCharLengthPremise w0 ∧
      P2 = containsReplCharAbsentPremise y0 w1 ∧
      w0 = w ∧ y0 = y ∧ w1 = w ∧
      __eo_prog_str_contains_repl_char x y z w
          (Proof.pf P1) (Proof.pf P2) =
        containsReplCharConclusion x y z w := by
  unfold __eo_prog_str_contains_repl_char at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases eqs_of_requires3_and_eq_true_not_stuck hProg with
      ⟨hW0, hY0, hW1⟩
    subst_vars
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_repl_char, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, containsReplCharConclusion,
      containsReplCharLhs, containsReplCharRhs, containsReplCharValue,
      containsReplCharContains]

private theorem typed___eo_prog_str_contains_repl_char_impl
    (x y z w P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_contains_repl_char x y z w
          (Proof.pf P1) (Proof.pf P2) =
        containsReplCharConclusion x y z w) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_contains_repl_char x y z w
        (Proof.pf P1) (Proof.pf P2)) := by
  let value := containsReplCharValue x y z
  let lhs := containsReplCharLhs x y z w
  let cxw := containsReplCharContains x w
  let cxy := containsReplCharContains x y
  let czw := containsReplCharContains z w
  let innerAnd := Term.Apply (Term.Apply Term.and czw) (Term.Boolean true)
  let outerAnd := Term.Apply (Term.Apply Term.and cxy) innerAnd
  let innerOr := Term.Apply (Term.Apply Term.or outerAnd) (Term.Boolean false)
  let rhs := containsReplCharRhs x y z w
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hLhsTy : RuleProofs.eo_has_bool_type lhs := by
    change __smtx_typeof
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt w)) = SmtType.Bool
    rw [typeof_str_contains_eq, typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, hWSmtTy,
      __smtx_typeof_seq_op_3, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hCxwTy : RuleProofs.eo_has_bool_type cxw := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt w)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hWSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hCxyTy : RuleProofs.eo_has_bool_type cxy := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hCzwTy : RuleProofs.eo_has_bool_type czw := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt z) (__eo_to_smt w)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hZSmtTy, hWSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hInnerAndTy : RuleProofs.eo_has_bool_type innerAnd :=
    RuleProofs.eo_has_bool_type_and_of_bool_args czw (Term.Boolean true)
      hCzwTy RuleProofs.eo_has_bool_type_true
  have hOuterAndTy : RuleProofs.eo_has_bool_type outerAnd :=
    RuleProofs.eo_has_bool_type_and_of_bool_args cxy innerAnd
      hCxyTy hInnerAndTy
  have hInnerOrTy : RuleProofs.eo_has_bool_type innerOr :=
    RuleProofs.eo_has_bool_type_or_of_bool_args outerAnd (Term.Boolean false)
      hOuterAndTy RuleProofs.eo_has_bool_type_false
  have hRhsTy : RuleProofs.eo_has_bool_type rhs :=
    RuleProofs.eo_has_bool_type_or_of_bool_args cxw innerOr
      hCxwTy hInnerOrTy
  have hBool : RuleProofs.eo_has_bool_type
      (containsReplCharConclusion x y z w) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_contains_repl_char_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z w P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (containsReplCharLengthPremise w) true)
    (hPrem2 : eo_interprets M (containsReplCharAbsentPremise y w) true)
    (hProgEq :
      __eo_prog_str_contains_repl_char x y z w
          (Proof.pf P1) (Proof.pf P2) =
        containsReplCharConclusion x y z w) :
    eo_interprets M
      (__eo_prog_str_contains_repl_char x y z w
        (Proof.pf P1) (Proof.pf P2)) true := by
  let lhs := containsReplCharLhs x y z w
  let rhs := containsReplCharRhs x y z w
  have hBool : RuleProofs.eo_has_bool_type
      (containsReplCharConclusion x y z w) := by
    simpa [hProgEq] using
      typed___eo_prog_str_contains_repl_char_impl
        x y z w P1 P2 hXTrans hYTrans hZTrans hWTrans
        hXTy hYTy hZTy hWTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
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
  have hWEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt w)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hWSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt w) (by
        unfold term_has_non_none_type
        rw [hWSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  rcases seq_value_canonical hWEvalTy with ⟨sw, hWEval⟩
  have hWLen : (native_unpack_seq sw).length = 1 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt w))
              (SmtTerm.Numeral 1)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hWEval,
          smtx_eval_numeral_term_eq] at hEval
        have hLenInt :
            (Int.ofNat (native_unpack_seq sw).length : Int) = 1 := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        change Int.ofNat (native_unpack_seq sw).length = Int.ofNat 1 at hLenInt
        exact Int.ofNat.inj hLenInt
  have hYNotContainsW :
      native_seq_contains (native_unpack_seq sy) (native_unpack_seq sw) =
        false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt w))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hYEval, hWEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt w)) =
      __smtx_model_eval M
        (SmtTerm.or
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt w))
          (SmtTerm.or
            (SmtTerm.and
              (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y))
              (SmtTerm.and
                (SmtTerm.str_contains (__eo_to_smt z) (__eo_to_smt w))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean false)))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_or_term_eq, smtx_eval_str_contains_term_eq,
      smtx_eval_or_term_eq, smtx_eval_and_term_eq,
      smtx_eval_str_contains_term_eq, smtx_eval_and_term_eq,
      smtx_eval_str_contains_term_eq, hXEval, hYEval, hZEval, hWEval,
      smtx_eval_boolean_term_eq, smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_replace,
      __smtx_model_eval_or, __smtx_model_eval_and,
      Smtm.native_unpack_pack_seq, SmtEval.native_or, SmtEval.native_and,
      native_seq_contains_replace_char _ _ _ _ hWLen hYNotContainsW]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_repl_char_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_repl_char args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_char args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_repl_char args premises ≠
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
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.1
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
                                      (__eo_prog_str_contains_repl_char
                                        a1 a2 a3 a4 (Proof.pf P1)
                                        (Proof.pf P2)) =
                                    Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_contains_repl_char
                                          a1 a2 a3 a4 (Proof.pf P1)
                                          (Proof.pf P2) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_contains_repl_char_info
                                      a1 a2 a3 a4 P1 P2 hRuleProg with
                                    ⟨w0, y0, w1, hP1, hP2, hW0, hY0,
                                      hW1, hProgEq⟩
                                  subst w0
                                  subst y0
                                  subst w1
                                  rw [hProgEq] at hResultTy
                                  have hLhsNN :
                                      __eo_typeof
                                          (containsReplCharLhs
                                            a1 a2 a3 a4) ≠
                                        Term.Stuck := by
                                    change __eo_typeof_eq
                                        (__eo_typeof
                                          (containsReplCharLhs
                                            a1 a2 a3 a4))
                                        (__eo_typeof
                                          (containsReplCharRhs
                                            a1 a2 a3 a4)) =
                                      Term.Bool at hResultTy
                                    exact
                                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                        (__eo_typeof
                                          (containsReplCharLhs
                                            a1 a2 a3 a4))
                                        (__eo_typeof
                                          (containsReplCharRhs
                                            a1 a2 a3 a4)) hResultTy).1
                                  have hArgTypes :
                                      ∃ T,
                                        __eo_typeof a1 =
                                            Term.Apply Term.Seq T ∧
                                          __eo_typeof a2 =
                                            Term.Apply Term.Seq T ∧
                                          __eo_typeof a3 =
                                            Term.Apply Term.Seq T ∧
                                          __eo_typeof a4 =
                                            Term.Apply Term.Seq T := by
                                    change __eo_typeof_str_contains
                                        (__eo_typeof
                                          (containsReplCharValue a1 a2 a3))
                                        (__eo_typeof a4) ≠
                                      Term.Stuck at hLhsNN
                                    rcases eo_typeof_str_contains_args_of_ne_stuck
                                        (__eo_typeof
                                          (containsReplCharValue a1 a2 a3))
                                        (__eo_typeof a4) hLhsNN with
                                      ⟨T, hValueTy, hA4Ty⟩
                                    have hValueNN :
                                        __eo_typeof
                                            (containsReplCharValue a1 a2 a3) ≠
                                          Term.Stuck := by
                                      rw [hValueTy]
                                      simp
                                    change __eo_typeof_str_replace
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) ≠
                                      Term.Stuck at hValueNN
                                    rcases eo_typeof_str_replace_args_of_ne_stuck
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) hValueNN with
                                      ⟨U, hA1Ty, hA2Ty, hA3Ty⟩
                                    have hValueTyU :
                                        __eo_typeof
                                            (containsReplCharValue a1 a2 a3) =
                                          Term.Apply Term.Seq U := by
                                      change __eo_typeof_str_replace
                                          (__eo_typeof a1) (__eo_typeof a2)
                                          (__eo_typeof a3) =
                                        Term.Apply Term.Seq U
                                      have hRawNN := hValueNN
                                      rw [hA1Ty, hA2Ty, hA3Ty] at hRawNN
                                      rw [hA1Ty, hA2Ty, hA3Ty]
                                      exact
                                        eo_typeof_str_replace_result_of_seq_args
                                          U hRawNN
                                    rw [hValueTy] at hValueTyU
                                    cases hValueTyU
                                    exact ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                                  rcases hArgTypes with
                                    ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
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
                                          (containsReplCharLengthPremise a4)
                                          true := by
                                      simpa [hP1] using hPrem1Raw
                                    have hPrem2 :
                                        eo_interprets M
                                          (containsReplCharAbsentPremise a2 a4)
                                          true := by
                                      simpa [hP2] using hPrem2Raw
                                    exact
                                      facts___eo_prog_str_contains_repl_char_impl
                                        M hM a1 a2 a3 a4 P1 P2 hA1Trans
                                        hA2Trans hA3Trans hA4Trans hA1Ty
                                        hA2Ty hA3Ty hA4Ty hPrem1 hPrem2
                                        hProgEq
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (typed___eo_prog_str_contains_repl_char_impl
                                          a1 a2 a3 a4 P1 P2 hA1Trans
                                          hA2Trans hA3Trans hA4Trans hA1Ty
                                          hA2Ty hA3Ty hA4Ty hProgEq)
