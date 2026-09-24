module

public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrReplReplLookaheadIdSimpProof

private abbrev neqPremise (w z : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq w) z))
    (Term.Boolean false)

private abbrev lenPremise (w z : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.geq (Term.Apply Term.str_len w))
        (Term.Apply Term.str_len z)))
    (Term.Boolean true)

private abbrev replace (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) pat) repl

private abbrev lhs (y z w : Term) : Term :=
  replace (replace y w y) y z

private abbrev rhs (y z w : Term) : Term :=
  replace (replace y w z) y z

private abbrev concl (y z w : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lhs y z w)) (rhs y z w)

private theorem prog_info
    (y z w P1 P2 : Term)
    (hProg :
      __eo_prog_str_repl_repl_lookahead_id_simp y z w
          (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck) :
    ∃ w0 z0 w1 z1,
      P1 = neqPremise w0 z0 ∧
      P2 = lenPremise w1 z1 ∧
      w0 = w ∧ z0 = z ∧ w1 = w ∧ z1 = z ∧
      __eo_prog_str_repl_repl_lookahead_id_simp y z w
          (Proof.pf P1) (Proof.pf P2) = concl y z w := by
  unfold __eo_prog_str_repl_repl_lookahead_id_simp at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases StrContainsReplCharSupport.eqs_of_requires4_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ hProg with
      ⟨hW0, hZ0, hW1, hZ1⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_repl_repl_lookahead_id_simp,
      __eo_requires, __eo_eq, __eo_and, SmtEval.native_ite,
      native_teq, native_and, SmtEval.native_not, concl, lhs, rhs,
      replace]

private theorem typed_program
    (y z w P1 P2 : Term)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_repl_repl_lookahead_id_simp y z w
          (Proof.pf P1) (Proof.pf P2) = concl y z w) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_repl_repl_lookahead_id_simp y z w
        (Proof.pf P1) (Proof.pf P2)) := by
  have hYSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq
    y T hYTrans hYTy
  have hZSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq
    z T hZTrans hZTy
  have hWSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq
    w T hWTrans hWTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs y z w)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt w)
            (__eo_to_smt y))
          (__eo_to_smt y) (__eo_to_smt z)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq, typeof_str_replace_eq]
    simp [hYSmtTy, hZSmtTy, hWSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs y z w)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt w)
            (__eo_to_smt z))
          (__eo_to_smt y) (__eo_to_smt z)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq, typeof_str_replace_eq]
    simp [hYSmtTy, hZSmtTy, hWSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type (concl y z w) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs y z w) (rhs y z w)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem facts_program
    (M : SmtModel) (hM : model_wf M)
    (y z w P1 P2 : Term)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hNePrem : eo_interprets M (neqPremise w z) true)
    (hLenPrem : eo_interprets M (lenPremise w z) true)
    (hProgEq :
      __eo_prog_str_repl_repl_lookahead_id_simp y z w
          (Proof.pf P1) (Proof.pf P2) = concl y z w) :
    eo_interprets M
      (__eo_prog_str_repl_repl_lookahead_id_simp y z w
        (Proof.pf P1) (Proof.pf P2)) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl y z w) := by
    simpa [hProgEq] using typed_program y z w P1 P2
      hYTrans hZTrans hWTrans hYTy hZTy hWTy hProgEq
  have hYSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq
    y T hYTrans hYTy
  have hZSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq
    z T hZTrans hZTy
  have hWSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq
    w T hWTrans hWTy
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
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  rcases seq_value_canonical hWEvalTy with ⟨sw, hWEval⟩
  have hSwTy :
      __smtx_typeof_seq_value sw = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hWEval] using hWEvalTy
  have hSzTy :
      __smtx_typeof_seq_value sz = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hZEval] using hZEvalTy
  have hElem :
      __smtx_elem_typeof_seq_value sw =
        __smtx_elem_typeof_seq_value sz := by
    rw [elem_typeof_seq_value_of_typeof_seq_value hSwTy,
      elem_typeof_seq_value_of_typeof_seq_value hSzTy]
  have hSeqNe : sw ≠ sz := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hNePrem
    cases hNePrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (__eo_to_smt w) (__eo_to_smt z))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq,
          hWEval, hZEval,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_eq, native_veq] using hEval
  have hListsNe : native_unpack_seq sw ≠ native_unpack_seq sz := by
    intro hUnpack
    apply hSeqNe
    exact StrEqReplSupport.seq_eq_of_unpack_eq_of_elem_eq
      sw sz hElem hUnpack
  have hReplLe :
      (native_unpack_seq sz).length ≤
        (native_unpack_seq sw).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLenPrem
    cases hLenPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_len (__eo_to_smt w))
                (SmtTerm.str_len (__eo_to_smt z)))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
          hWEval, hZEval,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq (Int.ofNat (native_unpack_seq sz).length)
                (Int.ofNat (native_unpack_seq sw).length) = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        exact Int.ofNat_le.mp (by
          simpa [SmtEval.native_zleq] using hLeBool)
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs y z w)) =
        __smtx_model_eval M (__eo_to_smt (rhs y z w)) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt w)
            (__eo_to_smt y))
          (__eo_to_smt y) (__eo_to_smt z)) =
      __smtx_model_eval M
        (SmtTerm.str_replace
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt w)
            (__eo_to_smt z))
          (__eo_to_smt y) (__eo_to_smt z))
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      StrEqReplSupport.smtx_eval_str_replace_term_eq,
      StrEqReplSupport.smtx_eval_str_replace_term_eq,
      StrEqReplSupport.smtx_eval_str_replace_term_eq,
      hYEval, hZEval, hWEval]
    simp only [__smtx_model_eval_str_replace,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
    rw [StringRewriteSupport.native_seq_replace_lookahead_id
      (native_unpack_seq sy) (native_unpack_seq sw)
      (native_unpack_seq sz) hListsNe hReplLe]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs y z w) (rhs y z w)
    hBool <| by
      rw [hEvalEq]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt (rhs y z w)))

end StrReplReplLookaheadIdSimpProof

public theorem cmd_step_str_repl_repl_lookahead_id_simp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk
      (CCmd.step CRule.str_repl_repl_lookahead_id_simp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof
      (__eo_cmd_step_proven s CRule.str_repl_repl_lookahead_id_simp
        args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_lookahead_id_simp
      args premises) := by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_repl_repl_lookahead_id_simp
          args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a1 args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons a2 args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons a3 args =>
        cases args with
        | cons _ _ => exact False.elim (hProg rfl)
        | nil =>
          cases premises with
          | nil => exact False.elim (hProg rfl)
          | cons n1 premises =>
            cases premises with
            | nil => exact False.elim (hProg rfl)
            | cons n2 premises =>
              cases premises with
              | cons _ _ => exact False.elim (hProg rfl)
              | nil =>
                let P1 := __eo_state_proven_nth s n1
                let P2 := __eo_state_proven_nth s n2
                have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                  hCmdTrans.1
                have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                  hCmdTrans.2.1
                have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                  hCmdTrans.2.2.1
                change __eo_typeof
                    (__eo_prog_str_repl_repl_lookahead_id_simp
                      a1 a2 a3 (Proof.pf P1) (Proof.pf P2)) =
                  Term.Bool at hResultTy
                have hRuleProg :
                    __eo_prog_str_repl_repl_lookahead_id_simp
                        a1 a2 a3 (Proof.pf P1) (Proof.pf P2) ≠
                      Term.Stuck :=
                  term_ne_stuck_of_typeof_bool hResultTy
                rcases StrReplReplLookaheadIdSimpProof.prog_info
                    a1 a2 a3 P1 P2 hRuleProg with
                  ⟨w0, z0, w1, z1, hP1, hP2,
                    hW0, hZ0, hW1, hZ1, hProgEq⟩
                subst w0
                subst z0
                subst w1
                subst z1
                rw [hProgEq] at hResultTy
                have hLhsNN :
                    __eo_typeof
                        (StrReplReplLookaheadIdSimpProof.lhs
                          a1 a2 a3) ≠ Term.Stuck := by
                  change __eo_typeof_eq
                      (__eo_typeof
                        (StrReplReplLookaheadIdSimpProof.lhs
                          a1 a2 a3))
                      (__eo_typeof
                        (StrReplReplLookaheadIdSimpProof.rhs
                          a1 a2 a3)) = Term.Bool at hResultTy
                  exact
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      _ _ hResultTy).1
                change __eo_typeof_str_replace
                    (__eo_typeof
                      (StrReplReplLookaheadIdSimpProof.replace
                        a1 a3 a1))
                    (__eo_typeof a1) (__eo_typeof a2) ≠
                  Term.Stuck at hLhsNN
                rcases StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                    _ _ _ hLhsNN with
                  ⟨T, hInnerTy, hA1Ty, hA2Ty⟩
                have hInnerNN :
                    __eo_typeof
                        (StrReplReplLookaheadIdSimpProof.replace
                          a1 a3 a1) ≠ Term.Stuck := by
                  rw [hInnerTy]
                  simp
                change __eo_typeof_str_replace
                    (__eo_typeof a1) (__eo_typeof a3)
                    (__eo_typeof a1) ≠ Term.Stuck at hInnerNN
                rcases StrEqReplSupport.eo_typeof_str_replace_args_of_ne_stuck
                    _ _ _ hInnerNN with
                  ⟨U, hA1Ty', hA3Ty, _hA1Ty''⟩
                rw [hA1Ty] at hA1Ty'
                cases hA1Ty'
                refine ⟨?_, ?_⟩
                · intro hTrue
                  have hPrem1Raw : eo_interprets M P1 true :=
                    hTrue P1 (by simp [P1, premiseTermList])
                  have hPrem2Raw : eo_interprets M P2 true :=
                    hTrue P2 (by simp [P2, premiseTermList])
                  have hPrem1 :
                      eo_interprets M
                        (StrReplReplLookaheadIdSimpProof.neqPremise
                          a3 a2) true := by
                    simpa [hP1] using hPrem1Raw
                  have hPrem2 :
                      eo_interprets M
                        (StrReplReplLookaheadIdSimpProof.lenPremise
                          a3 a2) true := by
                    simpa [hP2] using hPrem2Raw
                  exact StrReplReplLookaheadIdSimpProof.facts_program
                    M hM a1 a2 a3 P1 P2
                    hA1Trans hA2Trans hA3Trans
                    hA1Ty hA2Ty hA3Ty hPrem1 hPrem2 hProgEq
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    (StrReplReplLookaheadIdSimpProof.typed_program
                      a1 a2 a3 P1 P2 hA1Trans hA2Trans hA3Trans
                      hA1Ty hA2Ty hA3Ty hProgEq)
