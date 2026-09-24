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

private abbrev tgtLenPremise (pat repl : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len pat))
    (Term.Apply Term.str_len repl)

private abbrev tgtLenValue (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) pat) repl

private abbrev tgtLenLhs (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (tgtLenValue x pat repl)) repl

private abbrev tgtLenRhs (x pat repl : Term) : Term :=
  Term.Apply
    (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x) pat))
    (Term.Apply
      (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x) repl))
      (Term.Boolean false))

private abbrev tgtLenConclusion (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (tgtLenLhs x pat repl))
    (tgtLenRhs x pat repl)

private theorem prog_str_eq_repl_tgt_eq_len_info
    (x pat repl P : Term)
    (hProg : __eo_prog_str_eq_repl_tgt_eq_len x pat repl (Proof.pf P) ≠
      Term.Stuck) :
    ∃ pat0 repl0,
      P = tgtLenPremise pat0 repl0 ∧ pat0 = pat ∧ repl0 = repl ∧
      __eo_prog_str_eq_repl_tgt_eq_len x pat repl (Proof.pf P) =
        tgtLenConclusion x pat repl := by
  unfold __eo_prog_str_eq_repl_tgt_eq_len at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hPat, hRepl⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_eq_repl_tgt_eq_len, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, tgtLenConclusion, tgtLenLhs, tgtLenRhs,
      tgtLenValue]

private theorem typed___eo_prog_str_eq_repl_tgt_eq_len_impl
    (x pat repl P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_eq_repl_tgt_eq_len x pat repl (Proof.pf P) =
        tgtLenConclusion x pat repl) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_eq_repl_tgt_eq_len x pat repl (Proof.pf P)) := by
  let value := tgtLenValue x pat repl
  let lhs := tgtLenLhs x pat repl
  let eqXPat := Term.Apply (Term.Apply Term.eq x) pat
  let eqXRepl := Term.Apply (Term.Apply Term.eq x) repl
  let innerOr := Term.Apply (Term.Apply Term.or eqXRepl) (Term.Boolean false)
  let rhs := tgtLenRhs x pat repl
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hPatSmtTy := smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy := smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
          (__eo_to_smt repl)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hPatSmtTy, hReplSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type value repl
      (by rw [hValueTy, hReplSmtTy]) (by rw [hValueTy]; simp)
  have hEqXPatTy : __smtx_typeof (__eo_to_smt eqXPat) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x pat
      (by rw [hXSmtTy, hPatSmtTy]) (by rw [hXSmtTy]; simp)
  have hEqXReplTy : __smtx_typeof (__eo_to_smt eqXRepl) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x repl
      (by rw [hXSmtTy, hReplSmtTy]) (by rw [hXSmtTy]; simp)
  have hInnerOrTy :
      __smtx_typeof (__eo_to_smt innerOr) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.or (__eo_to_smt eqXRepl) (SmtTerm.Boolean false)) =
      SmtType.Bool
    rw [typeof_or_eq]
    simp [hEqXReplTy, __smtx_typeof.eq_1, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.or (__eo_to_smt eqXPat) (__eo_to_smt innerOr)) =
      SmtType.Bool
    rw [typeof_or_eq]
    simp [hEqXPatTy, hInnerOrTy, native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (tgtLenConclusion x pat repl) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_eq_repl_tgt_eq_len_impl
    (M : SmtModel) (hM : model_wf M) (x pat repl P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (tgtLenPremise pat repl) true)
    (hProgEq :
      __eo_prog_str_eq_repl_tgt_eq_len x pat repl (Proof.pf P) =
        tgtLenConclusion x pat repl) :
    eo_interprets M
      (__eo_prog_str_eq_repl_tgt_eq_len x pat repl (Proof.pf P)) true := by
  let lhs := tgtLenLhs x pat repl
  let rhs := tgtLenRhs x pat repl
  have hBool : RuleProofs.eo_has_bool_type
      (tgtLenConclusion x pat repl) := by
    simpa [hProgEq] using
      typed___eo_prog_str_eq_repl_tgt_eq_len_impl x pat repl P
        hXTrans hPatTrans hReplTrans hXTy hPatTy hReplTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hPatSmtTy := smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy := smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hPatEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt pat)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPatSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt pat) (by
        unfold term_has_non_none_type
        rw [hPatSmtTy]
        simp)
  have hReplEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hReplSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hPatEvalTy with ⟨spat, hPatEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨srepl, hReplEval⟩
  have hLen :
      (native_unpack_seq spat).length = (native_unpack_seq srepl).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt pat))
              (SmtTerm.str_len (__eo_to_smt repl))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
          smtx_eval_str_len_term_eq, hPatEval, hReplEval] at hEval
        have hLenInt :
            ((native_unpack_seq spat).length : Int) =
              ((native_unpack_seq srepl).length : Int) := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_seq_len, native_veq] using hEval
        exact Int.ofNat_inj.mp hLenInt
  have hSxTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSpatTy :
      __smtx_typeof_seq_value spat = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hPatEval] using hPatEvalTy
  have hSreplTy :
      __smtx_typeof_seq_value srepl = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hReplEval] using hReplEvalTy
  have hSxElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSpatElem : __smtx_elem_typeof_seq_value spat = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSpatTy
  have hSreplElem : __smtx_elem_typeof_seq_value srepl = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSreplTy
  have hValueIff :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
            (native_unpack_seq srepl)) = srepl ↔
        sx = spat ∨ sx = srepl := by
    constructor
    · intro hValue
      have hLists := congrArg native_unpack_seq hValue
      have hReplace :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
              (native_unpack_seq srepl) = native_unpack_seq srepl := by
        simpa [Smtm.native_unpack_pack_seq] using hLists
      rcases (native_seq_replace_eq_repl_iff_of_same_len _ _ _ hLen).mp
          hReplace with hXPat | hXRepl
      · left
        exact seq_eq_of_unpack_eq_of_elem_eq sx spat
          (by rw [hSxElem, hSpatElem]) hXPat
      · right
        exact seq_eq_of_unpack_eq_of_elem_eq sx srepl
          (by rw [hSxElem, hSreplElem]) hXRepl
    · intro hEq
      have hListEq :
          native_unpack_seq sx = native_unpack_seq spat ∨
            native_unpack_seq sx = native_unpack_seq srepl := by
        rcases hEq with hXPat | hXRepl
        · exact Or.inl (congrArg native_unpack_seq hXPat)
        · exact Or.inr (congrArg native_unpack_seq hXRepl)
      have hReplace :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
              (native_unpack_seq srepl) = native_unpack_seq srepl :=
        (native_seq_replace_eq_repl_iff_of_same_len _ _ _ hLen).2 hListEq
      rw [hReplace, hSxElem]
      simpa [hSreplElem] using native_pack_unpack_seq srepl
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
            (__eo_to_smt repl))
          (__eo_to_smt repl)) =
      __smtx_model_eval M
        (SmtTerm.or (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt pat))
          (SmtTerm.or (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt repl))
            (SmtTerm.Boolean false)))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_or_term_eq, smtx_eval_eq_term_eq, smtx_eval_or_term_eq,
      smtx_eval_eq_term_eq, hXEval, hPatEval, hReplEval,
      smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_eq,
      __smtx_model_eval_or, native_veq, native_or, hValueIff]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_repl_tgt_eq_len_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_tgt_eq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_repl_tgt_eq_len args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_tgt_eq_len args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_repl_tgt_eq_len args premises ≠
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
                  | cons n premises =>
                      cases premises with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          let P := __eo_state_proven_nth s n
                          have hA1Trans :
                              RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.1
                          have hA2Trans :
                              RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.1
                          have hA3Trans :
                              RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.2.1
                          change __eo_typeof
                              (__eo_prog_str_eq_repl_tgt_eq_len a1 a2 a3
                                (Proof.pf P)) = Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_eq_repl_tgt_eq_len a1 a2 a3
                                  (Proof.pf P) ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_eq_repl_tgt_eq_len_info
                              a1 a2 a3 P hRuleProg with
                            ⟨pat0, repl0, hPremShape, hPat0, hRepl0, hProgEq⟩
                          subst pat0
                          subst repl0
                          rw [hProgEq] at hResultTy
                          have hOuterLeftTy :
                              __eo_typeof (tgtLenLhs a1 a2 a3) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof (tgtLenLhs a1 a2 a3))
                                (__eo_typeof (tgtLenRhs a1 a2 a3)) =
                              Term.Bool at hResultTy
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof (tgtLenLhs a1 a2 a3))
                                (__eo_typeof (tgtLenRhs a1 a2 a3))
                                hResultTy).1
                          have hInnerLeftBool :
                              __eo_typeof (tgtLenLhs a1 a2 a3) =
                                Term.Bool := by
                            change __eo_typeof_eq
                                (__eo_typeof (tgtLenValue a1 a2 a3))
                                (__eo_typeof a3) = Term.Bool
                            exact eo_typeof_eq_nonstuck_bool _ _ hOuterLeftTy
                          have hValueTy :
                              __eo_typeof (tgtLenValue a1 a2 a3) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof (tgtLenValue a1 a2 a3))
                                (__eo_typeof a3) = Term.Bool at hInnerLeftBool
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof (tgtLenValue a1 a2 a3))
                                (__eo_typeof a3) hInnerLeftBool).1
                          rcases eo_typeof_str_replace_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a3) hValueTy with
                            ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (tgtLenPremise a2 a3) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_eq_repl_tgt_eq_len_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (typed___eo_prog_str_eq_repl_tgt_eq_len_impl
                                  a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                  hA1Ty hA2Ty hA3Ty hProgEq)
