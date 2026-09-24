module

public import Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport

open Eo
open SmtEval
open Smtm
open StrLeqConcatSupport
open StrLeqConcatNarySupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev leqConcatFalseLenPremise (t s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len t))
    (Term.Apply Term.str_len s)

private abbrev leqConcatFalseLeqPremise (t s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq t) s))
    (Term.Boolean false)

private abbrev leqConcatFalseTail (x tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat x) tail

private abbrev leqConcatFalseSide
    (pfx x tail : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.str_concat) pfx
    (leqConcatFalseTail x tail)

private abbrev leqConcatFalseCore
    (pfx t s tTail sTail : Term) : Term :=
  Term.Apply
    (Term.Apply Term.str_leq
      (leqConcatFalseSide pfx t tTail))
    (leqConcatFalseSide pfx s sTail)

private abbrev leqConcatFalseConclusion
    (pfx t s tTail sTail : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (leqConcatFalseCore pfx t s tTail sTail))
    (Term.Boolean false)

private abbrev rawLeqConcatFalseConclusion
    (left right : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_leq) left) right))
    (Term.Boolean false)

private theorem raw_leq_concat_false_conclusion_eq
    (left right : Term)
    (h : rawLeqConcatFalseConclusion left right ≠ Term.Stuck) :
    rawLeqConcatFalseConclusion left right =
      Term.Apply
        (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq left) right))
        (Term.Boolean false) := by
  let f1 := __eo_mk_apply (Term.UOp UserOp.str_leq) left
  let inner := __eo_mk_apply f1 right
  let f2 := __eo_mk_apply (Term.UOp UserOp.eq) inner
  have hf2 : f2 ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f2 (Term.Boolean false)
      (by simpa [rawLeqConcatFalseConclusion, f1, inner, f2] using h)
  have hInner : inner ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) inner hf2
  have hf1 : f1 ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f1 right hInner
  have e1 : f1 = Term.Apply (Term.UOp UserOp.str_leq) left :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_leq) left hf1
  have e2 : inner = Term.Apply f1 right :=
    eo_mk_apply_eq_apply_of_ne_stuck f1 right hInner
  have e3 : f2 = Term.Apply (Term.UOp UserOp.eq) inner :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) inner hf2
  have e4 : __eo_mk_apply f2 (Term.Boolean false) =
      Term.Apply f2 (Term.Boolean false) :=
    eo_mk_apply_eq_apply_of_ne_stuck f2 (Term.Boolean false)
      (by simpa [rawLeqConcatFalseConclusion, f1, inner, f2] using h)
  change __eo_mk_apply f2 (Term.Boolean false) = _
  rw [e4, e3, e2, e1]

private theorem prog_str_leq_concat_false_info
    (pfx t s tTail sTail P1 P2 : Term)
    (hProg :
      __eo_prog_str_leq_concat_false pfx t s tTail sTail
          (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck) :
    ∃ t0 s0 t1 s1,
      P1 = leqConcatFalseLenPremise t0 s0 ∧
      P2 = leqConcatFalseLeqPremise t1 s1 ∧
      t0 = t ∧ s0 = s ∧ t1 = t ∧ s1 = s ∧
      __eo_prog_str_leq_concat_false pfx t s tTail sTail
          (Proof.pf P1) (Proof.pf P2) =
        leqConcatFalseConclusion pfx t s tTail sTail := by
  let Pfx := pfx
  let T := t
  let S := s
  let TTail := tTail
  let STail := sTail
  unfold __eo_prog_str_leq_concat_false at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases eqs_of_requires4_and_eq_true_not_stuck _ _ _ _ _ _ _ _ _
        hProg with ⟨hT0, hS0, hT1, hS1⟩
    subst_vars
    let left := leqConcatFalseSide Pfx T TTail
    let right := leqConcatFalseSide Pfx S STail
    have hBody :
        __eo_prog_str_leq_concat_false Pfx T S TTail STail
            (Proof.pf (leqConcatFalseLenPremise T S))
            (Proof.pf (leqConcatFalseLeqPremise T S)) =
          rawLeqConcatFalseConclusion left right := by
      simp_all [__eo_prog_str_leq_concat_false, __eo_requires, __eo_eq,
        __eo_and, SmtEval.native_ite, native_teq, native_and,
        SmtEval.native_not, rawLeqConcatFalseConclusion, left, right,
        Pfx, T, S, TTail, STail,
        leqConcatFalseSide, leqConcatFalseTail,
        leqConcatFalseLenPremise, leqConcatFalseLeqPremise]
    have hRawNe : rawLeqConcatFalseConclusion left right ≠ Term.Stuck := by
      have hResultNe := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
      simpa [rawLeqConcatFalseConclusion, left, right,
        leqConcatFalseSide, leqConcatFalseTail, Pfx, T, S, TTail,
        STail] using hResultNe
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [hBody]
    simpa [left, right, leqConcatFalseConclusion,
      leqConcatFalseCore, Pfx, T, S, TTail, STail] using
        raw_leq_concat_false_conclusion_eq left right hRawNe

private theorem native_str_leq_bool_false_ne
    {s t : native_String}
    (h : native_str_leq_bool s t = false) : s ≠ t := by
  intro hEq
  subst t
  simp [native_str_leq_bool, SmtEval.native_or] at h

public theorem cmd_step_str_leq_concat_false_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_concat_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_leq_concat_false args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_concat_false args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_leq_concat_false args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons pfx args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons t args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons s0 args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons tTail args =>
                  cases args with
                  | nil => exact absurd rfl hProg
                  | cons sTail args =>
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
                                      have hPrefixTrans :
                                          RuleProofs.eo_has_smt_translation
                                            pfx := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.1
                                      have hTTrans :
                                          RuleProofs.eo_has_smt_translation t := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.2.1
                                      have hSTrans :
                                          RuleProofs.eo_has_smt_translation s0 := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.2.2.1
                                      have hTTailTrans :
                                          RuleProofs.eo_has_smt_translation
                                            tTail := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.2.2.2.1
                                      have hSTailTrans :
                                          RuleProofs.eo_has_smt_translation
                                            sTail := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.2.2.2.2.1
                                      change __eo_typeof
                                          (__eo_prog_str_leq_concat_false
                                            pfx t s0 tTail sTail
                                            (Proof.pf P1) (Proof.pf P2)) =
                                        Term.Bool at hResultTy
                                      have hRuleProg :
                                          __eo_prog_str_leq_concat_false
                                              pfx t s0 tTail sTail
                                              (Proof.pf P1) (Proof.pf P2) ≠
                                            Term.Stuck :=
                                        term_ne_stuck_of_typeof_bool hResultTy
                                      rcases prog_str_leq_concat_false_info
                                          pfx t s0 tTail sTail P1 P2
                                          hRuleProg with
                                        ⟨t0, s1, t1, s2, hP1, hP2,
                                          hT0, hS1, hT1, hS2, hProgEq⟩
                                      subst t0
                                      subst s1
                                      subst t1
                                      subst s2
                                      rw [hProgEq] at hResultTy
                                      let z1 := leqConcatFalseTail t tTail
                                      let z2 := leqConcatFalseTail s0 sTail
                                      let left :=
                                        leqConcatFalseSide pfx t tTail
                                      let right :=
                                        leqConcatFalseSide pfx s0 sTail
                                      let core :=
                                        leqConcatFalseCore pfx t s0
                                          tTail sTail
                                      have hCoreEoTy :
                                          __eo_typeof core = Term.Bool := by
                                        change __eo_typeof_eq
                                            (__eo_typeof core) Term.Bool =
                                          Term.Bool at hResultTy
                                        exact
                                          RuleProofs.eo_typeof_eq_bool_operands_eq
                                            _ _ hResultTy
                                      have hCoreNN :
                                          __eo_typeof core ≠ Term.Stuck := by
                                        rw [hCoreEoTy]
                                        decide
                                      change __eo_typeof_str_lt
                                          (__eo_typeof left)
                                          (__eo_typeof right) ≠
                                        Term.Stuck at hCoreNN
                                      have hSides :=
                                        eo_typeof_str_leq_args_of_ne_stuck
                                          (__eo_typeof left)
                                          (__eo_typeof right) hCoreNN
                                      have hLeftEoTy := hSides.1
                                      have hRightEoTy := hSides.2
                                      have hLeftNe : left ≠ Term.Stuck := by
                                        intro h
                                        rw [h] at hLeftEoTy
                                        cases hLeftEoTy
                                      have hRightNe : right ≠ Term.Stuck := by
                                        intro h
                                        rw [h] at hRightEoTy
                                        cases hRightEoTy
                                      have hLeftFacts :=
                                        StrConcatClashSupport.concat_clash_rev_list_concat_facts
                                          pfx z1 (by
                                            simpa [left, z1,
                                              leqConcatFalseSide,
                                              leqConcatFalseTail] using
                                                hLeftNe)
                                      have hRightFacts :=
                                        StrConcatClashSupport.concat_clash_rev_list_concat_facts
                                          pfx z2 (by
                                            simpa [right, z2,
                                              leqConcatFalseSide,
                                              leqConcatFalseTail] using
                                                hRightNe)
                                      have hList := hLeftFacts.1
                                      have hLeftEqRec :
                                          left =
                                            __eo_list_concat_rec pfx z1 := by
                                        simpa [left, z1,
                                          leqConcatFalseSide,
                                          leqConcatFalseTail] using
                                          StrConcatClashSupport.concat_clash_rev_list_concat_eq_rec
                                            pfx z1 (by
                                              simpa [left, z1,
                                                leqConcatFalseSide,
                                                leqConcatFalseTail] using
                                                  hLeftNe)
                                      have hRightEqRec :
                                          right =
                                            __eo_list_concat_rec pfx z2 := by
                                        simpa [right, z2,
                                          leqConcatFalseSide,
                                          leqConcatFalseTail] using
                                          StrConcatClashSupport.concat_clash_rev_list_concat_eq_rec
                                            pfx z2 (by
                                              simpa [right, z2,
                                                leqConcatFalseSide,
                                                leqConcatFalseTail] using
                                                  hRightNe)
                                      have hLeftRecEoTy :
                                          __eo_typeof
                                              (__eo_list_concat_rec pfx z1) =
                                            Term.Apply Term.Seq Term.Char := by
                                        rw [← hLeftEqRec]
                                        exact hLeftEoTy
                                      have hRightRecEoTy :
                                          __eo_typeof
                                              (__eo_list_concat_rec pfx z2) =
                                            Term.Apply Term.Seq Term.Char := by
                                        rw [← hRightEqRec]
                                        exact hRightEoTy
                                      have hZ1EoTy :=
                                        StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                                          pfx z1 Term.Char hList
                                            hLeftRecEoTy
                                      have hZ2EoTy :=
                                        StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                                          pfx z2 Term.Char hList
                                            hRightRecEoTy
                                      have hZ1Args :=
                                        StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                          t tTail Term.Char (by
                                            simpa [z1,
                                              leqConcatFalseTail] using
                                                hZ1EoTy)
                                      have hZ2Args :=
                                        StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                          s0 sTail Term.Char (by
                                            simpa [z2,
                                              leqConcatFalseTail] using
                                                hZ2EoTy)
                                      have hTTy :=
                                        smtx_typeof_of_eo_seq_char t
                                          hTTrans hZ1Args.1
                                      have hTTailTy :=
                                        smtx_typeof_of_eo_seq_char tTail
                                          hTTailTrans hZ1Args.2
                                      have hSTy :=
                                        smtx_typeof_of_eo_seq_char s0
                                          hSTrans hZ2Args.1
                                      have hSTailTy :=
                                        smtx_typeof_of_eo_seq_char sTail
                                          hSTailTrans hZ2Args.2
                                      have hZ1Ty :
                                          __smtx_typeof (__eo_to_smt z1) =
                                            SmtType.Seq SmtType.Char := by
                                        simpa [z1, leqConcatFalseTail] using
                                          smt_typeof_str_concat_of_seq
                                            t tTail SmtType.Char hTTy hTTailTy
                                      have hZ2Ty :
                                          __smtx_typeof (__eo_to_smt z2) =
                                            SmtType.Seq SmtType.Char := by
                                        simpa [z2, leqConcatFalseTail] using
                                          smt_typeof_str_concat_of_seq
                                            s0 sTail SmtType.Char hSTy hSTailTy
                                      have hZ1Trans :
                                          RuleProofs.eo_has_smt_translation z1 := by
                                        unfold RuleProofs.eo_has_smt_translation
                                        rw [hZ1Ty]
                                        exact seq_ne_none SmtType.Char
                                      have hZ2Trans :
                                          RuleProofs.eo_has_smt_translation z2 := by
                                        unfold RuleProofs.eo_has_smt_translation
                                        rw [hZ2Ty]
                                        exact seq_ne_none SmtType.Char
                                      have hLeftRecTy :=
                                        smtx_typeof_list_concat_rec_of_eo_type
                                          pfx z1 Term.Char hList
                                          hPrefixTrans hZ1Trans hLeftRecEoTy
                                      have hRightRecTy :=
                                        smtx_typeof_list_concat_rec_of_eo_type
                                          pfx z2 Term.Char hList
                                          hPrefixTrans hZ2Trans hRightRecEoTy
                                      have hLeftTy :
                                          __smtx_typeof (__eo_to_smt left) =
                                            SmtType.Seq SmtType.Char := by
                                        rw [hLeftEqRec]
                                        simpa using hLeftRecTy
                                      have hRightTy :
                                          __smtx_typeof (__eo_to_smt right) =
                                            SmtType.Seq SmtType.Char := by
                                        rw [hRightEqRec]
                                        simpa using hRightRecTy
                                      have hCoreBool :
                                          RuleProofs.eo_has_bool_type core := by
                                        change __smtx_typeof
                                            (SmtTerm.str_leq
                                              (__eo_to_smt left)
                                              (__eo_to_smt right)) =
                                          SmtType.Bool
                                        rw [typeof_str_leq_eq]
                                        simp [hLeftTy, hRightTy,
                                          native_ite, native_Teq]
                                      have hConclusionBool :
                                          RuleProofs.eo_has_bool_type
                                            (leqConcatFalseConclusion pfx t
                                              s0 tTail sTail) :=
                                        RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                          core (Term.Boolean false)
                                          (by rw [hCoreBool]; rfl)
                                          (by rw [hCoreBool]; decide)
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
                                              (leqConcatFalseLenPremise t s0)
                                              true := by
                                          simpa [hP1] using hPrem1Raw
                                        have hPrem2 :
                                            eo_interprets M
                                              (leqConcatFalseLeqPremise t s0)
                                              true := by
                                          simpa [hP2] using hPrem2Raw
                                        have hTEvalTy :
                                            __smtx_typeof_value
                                                (__smtx_model_eval M
                                                  (__eo_to_smt t)) =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [hTTy] using
                                            smt_model_eval_preserves_type_of_non_none
                                              M hM (__eo_to_smt t) (by
                                                unfold term_has_non_none_type
                                                rw [hTTy]
                                                simp)
                                        have hTTailEvalTy :
                                            __smtx_typeof_value
                                                (__smtx_model_eval M
                                                  (__eo_to_smt tTail)) =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [hTTailTy] using
                                            smt_model_eval_preserves_type_of_non_none
                                              M hM (__eo_to_smt tTail) (by
                                                unfold term_has_non_none_type
                                                rw [hTTailTy]
                                                simp)
                                        have hSEvalTy :
                                            __smtx_typeof_value
                                                (__smtx_model_eval M
                                                  (__eo_to_smt s0)) =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [hSTy] using
                                            smt_model_eval_preserves_type_of_non_none
                                              M hM (__eo_to_smt s0) (by
                                                unfold term_has_non_none_type
                                                rw [hSTy]
                                                simp)
                                        have hSTailEvalTy :
                                            __smtx_typeof_value
                                                (__smtx_model_eval M
                                                  (__eo_to_smt sTail)) =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [hSTailTy] using
                                            smt_model_eval_preserves_type_of_non_none
                                              M hM (__eo_to_smt sTail) (by
                                                unfold term_has_non_none_type
                                                rw [hSTailTy]
                                                simp)
                                        rcases seq_value_canonical hTEvalTy with
                                          ⟨st, hTEval⟩
                                        rcases seq_value_canonical hTTailEvalTy with
                                          ⟨stTail, hTTailEval⟩
                                        rcases seq_value_canonical hSEvalTy with
                                          ⟨ss, hSEval⟩
                                        rcases seq_value_canonical hSTailEvalTy with
                                          ⟨ssTail, hSTailEval⟩
                                        have hStTy :
                                            __smtx_typeof_seq_value st =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [__smtx_typeof_value,
                                            hTEval] using hTEvalTy
                                        have hStTailTy :
                                            __smtx_typeof_seq_value stTail =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [__smtx_typeof_value,
                                            hTTailEval] using hTTailEvalTy
                                        have hSsTy :
                                            __smtx_typeof_seq_value ss =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [__smtx_typeof_value,
                                            hSEval] using hSEvalTy
                                        have hSsTailTy :
                                            __smtx_typeof_seq_value ssTail =
                                              SmtType.Seq SmtType.Char := by
                                          simpa [__smtx_typeof_value,
                                            hSTailEval] using hSTailEvalTy
                                        have hStPack :
                                            native_pack_string
                                                (native_unpack_string st) = st :=
                                          native_pack_string_unpack_string_of_typeof_seq_char
                                            st hStTy
                                        have hStTailPack :
                                            native_pack_string
                                                (native_unpack_string stTail) =
                                              stTail :=
                                          native_pack_string_unpack_string_of_typeof_seq_char
                                            stTail hStTailTy
                                        have hSsPack :
                                            native_pack_string
                                                (native_unpack_string ss) = ss :=
                                          native_pack_string_unpack_string_of_typeof_seq_char
                                            ss hSsTy
                                        have hSsTailPack :
                                            native_pack_string
                                                (native_unpack_string ssTail) =
                                              ssTail :=
                                          native_pack_string_unpack_string_of_typeof_seq_char
                                            ssTail hSsTailTy
                                        have hLen :
                                            (native_unpack_string st).length =
                                              (native_unpack_string ss).length := by
                                          rw [RuleProofs.eo_interprets_iff_smt_interprets]
                                            at hPrem1
                                          cases hPrem1 with
                                          | intro_true _ hEval =>
                                              change __smtx_model_eval M
                                                  (SmtTerm.eq
                                                    (SmtTerm.str_len
                                                      (__eo_to_smt t))
                                                    (SmtTerm.str_len
                                                      (__eo_to_smt s0))) =
                                                SmtValue.Boolean true at hEval
                                              rw [smtx_eval_eq_term_eq,
                                                smtx_eval_str_len_term_eq,
                                                smtx_eval_str_len_term_eq,
                                                hTEval, hSEval] at hEval
                                              have hLenInt :
                                                  ((native_unpack_seq st).length : Int) =
                                                    ((native_unpack_seq ss).length : Int) := by
                                                simpa [__smtx_model_eval_str_len,
                                                  __smtx_model_eval_eq,
                                                  native_seq_len, native_veq] using
                                                    hEval
                                              have hListLen :
                                                  (native_unpack_seq st).length =
                                                    (native_unpack_seq ss).length :=
                                                Int.ofNat_inj.mp hLenInt
                                              simpa [native_unpack_string] using
                                                hListLen
                                        have hLeqFalse :
                                            native_str_leq_bool
                                                (native_unpack_string st)
                                                (native_unpack_string ss) =
                                              false := by
                                          rw [RuleProofs.eo_interprets_iff_smt_interprets]
                                            at hPrem2
                                          cases hPrem2 with
                                          | intro_true _ hEval =>
                                              change __smtx_model_eval M
                                                  (SmtTerm.eq
                                                    (SmtTerm.str_leq
                                                      (__eo_to_smt t)
                                                      (__eo_to_smt s0))
                                                    (SmtTerm.Boolean false)) =
                                                SmtValue.Boolean true at hEval
                                              rw [smtx_eval_eq_term_eq,
                                                smtx_eval_str_leq_term_eq,
                                                hTEval, hSEval,
                                                smtx_eval_boolean_term_eq,
                                                ← hStPack, ← hSsPack,
                                                smtx_eval_str_leq_pack_string]
                                                at hEval
                                              simpa [__smtx_model_eval_eq,
                                                native_veq] using hEval
                                        have hStringNe :
                                            native_unpack_string st ≠
                                              native_unpack_string ss :=
                                          native_str_leq_bool_false_ne hLeqFalse
                                        have hConcat1Pack :
                                            native_pack_seq
                                                (__smtx_elem_typeof_seq_value st)
                                                (native_unpack_seq st ++
                                                  native_unpack_seq stTail) =
                                              native_pack_string
                                                (native_unpack_string st ++
                                                  native_unpack_string stTail) :=
                                          native_pack_seq_concat_eq_pack_string_append
                                            st stTail hStTy hStTailTy
                                        have hConcat2Pack :
                                            native_pack_seq
                                                (__smtx_elem_typeof_seq_value ss)
                                                (native_unpack_seq ss ++
                                                  native_unpack_seq ssTail) =
                                              native_pack_string
                                                (native_unpack_string ss ++
                                                  native_unpack_string ssTail) :=
                                          native_pack_seq_concat_eq_pack_string_append
                                            ss ssTail hSsTy hSsTailTy
                                        have hTailEval :
                                            __smtx_model_eval M
                                                (__eo_to_smt
                                                  (mkStrLeq z1 z2)) =
                                              SmtValue.Boolean false := by
                                          change __smtx_model_eval M
                                              (SmtTerm.str_leq
                                                (SmtTerm.str_concat
                                                  (__eo_to_smt t)
                                                  (__eo_to_smt tTail))
                                                (SmtTerm.str_concat
                                                  (__eo_to_smt s0)
                                                  (__eo_to_smt sTail))) =
                                            SmtValue.Boolean false
                                          rw [smtx_eval_str_leq_term_eq,
                                            smtx_eval_str_concat_term_eq,
                                            smtx_eval_str_concat_term_eq,
                                            hTEval, hTTailEval, hSEval,
                                            hSTailEval]
                                          change __smtx_model_eval_str_leq
                                              (SmtValue.Seq
                                                (native_pack_seq
                                                  (__smtx_elem_typeof_seq_value st)
                                                  (native_unpack_seq st ++
                                                    native_unpack_seq stTail)))
                                              (SmtValue.Seq
                                                (native_pack_seq
                                                  (__smtx_elem_typeof_seq_value ss)
                                                  (native_unpack_seq ss ++
                                                    native_unpack_seq ssTail))) =
                                            SmtValue.Boolean false
                                          rw [hConcat1Pack, hConcat2Pack,
                                            smtx_eval_str_leq_pack_string,
                                            native_str_leq_bool_append_both_of_same_len_ne
                                              _ _ _ _ hLen hStringNe,
                                            hLeqFalse]
                                        have hPrefixCancel :=
                                          smtx_eval_str_leq_list_concat_rec_common
                                            M hM pfx z1 z2 hList hZ1Ty hZ2Ty
                                              (by simpa using hLeftRecTy)
                                              (by simpa using hRightRecTy)
                                        have hCoreEval :
                                            __smtx_model_eval M
                                                (__eo_to_smt core) =
                                              SmtValue.Boolean false := by
                                          change __smtx_model_eval M
                                              (__eo_to_smt
                                                (mkStrLeq left right)) =
                                            SmtValue.Boolean false
                                          rw [hLeftEqRec, hRightEqRec]
                                          exact hPrefixCancel.trans hTailEval
                                        change eo_interprets M
                                          (__eo_prog_str_leq_concat_false
                                            pfx t s0 tTail sTail
                                            (Proof.pf P1) (Proof.pf P2)) true
                                        rw [hProgEq]
                                        exact
                                          RuleProofs.eo_interprets_eq_of_rel M
                                            core (Term.Boolean false)
                                            hConclusionBool (by
                                              rw [hCoreEval]
                                              change RuleProofs.smt_value_rel
                                                (SmtValue.Boolean false)
                                                (SmtValue.Boolean false)
                                              exact
                                                RuleProofs.smt_value_rel_refl
                                                  (SmtValue.Boolean false))
                                      · change
                                          RuleProofs.eo_has_smt_translation
                                            (__eo_prog_str_leq_concat_false
                                              pfx t s0 tTail sTail
                                              (Proof.pf P1) (Proof.pf P2))
                                        rw [hProgEq]
                                        exact
                                          RuleProofs.eo_has_smt_translation_of_has_bool_type
                                            _ hConclusionBool
