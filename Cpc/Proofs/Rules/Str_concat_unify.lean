module

public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm
open StrConcatUnifySupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev rawStrConcatUnifyConclusion
    (pfx s2 s3 t1 t2 : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq)
      (strConcatUnifyLeftEq pfx s2 s3 t1 t2))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__str_nary_elim (strConcatUnifyTail s2 s3)))
      (__str_nary_elim (strConcatUnifyTail t1 t2)))

private theorem raw_str_concat_unify_eq
    (pfx s2 s3 t1 t2 : Term)
    (h : rawStrConcatUnifyConclusion pfx s2 s3 t1 t2 ≠ Term.Stuck) :
    rawStrConcatUnifyConclusion pfx s2 s3 t1 t2 =
      strConcatUnifyConclusion pfx s2 s3 t1 t2 := by
  let sElim := __str_nary_elim (strConcatUnifyTail s2 s3)
  let tElim := __str_nary_elim (strConcatUnifyTail t1 t2)
  let f := __eo_mk_apply (Term.UOp UserOp.eq) sElim
  let rhs := __eo_mk_apply f tElim
  have hRhs : rhs ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (strConcatUnifyLeftEq pfx s2 s3 t1 t2)) rhs
      (by simpa [rawStrConcatUnifyConclusion, sElim, tElim, f, rhs] using h)
  have hF : f ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f tElim hRhs
  have eF : f = Term.Apply (Term.UOp UserOp.eq) sElim :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) sElim hF
  have eRhs : rhs = Term.Apply f tElim :=
    eo_mk_apply_eq_apply_of_ne_stuck f tElim hRhs
  have eOuter :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (strConcatUnifyLeftEq pfx s2 s3 t1 t2)) rhs =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (strConcatUnifyLeftEq pfx s2 s3 t1 t2)) rhs :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _
      (by simpa [rawStrConcatUnifyConclusion, sElim, tElim, f, rhs] using h)
  change __eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq)
        (strConcatUnifyLeftEq pfx s2 s3 t1 t2)) rhs =
    strConcatUnifyConclusion pfx s2 s3 t1 t2
  rw [eOuter, eRhs, eF]

public theorem cmd_step_str_concat_unify_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_unify args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_unify args premises ≠
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
                  | nil => exact absurd rfl hProg
                  | cons a5 args =>
                      cases args with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          cases premises with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
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
                                  cArgListTranslationOk] using hCmdTrans.2.2.1
                              have hA4Trans :
                                  RuleProofs.eo_has_smt_translation a4 := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.2.2.2.1
                              have hA5Trans :
                                  RuleProofs.eo_has_smt_translation a5 := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.2.2.1
                              have hA1Ne :=
                                RuleProofs.term_ne_stuck_of_has_smt_translation
                                  a1 hA1Trans
                              have hA2Ne :=
                                RuleProofs.term_ne_stuck_of_has_smt_translation
                                  a2 hA2Trans
                              have hA3Ne :=
                                RuleProofs.term_ne_stuck_of_has_smt_translation
                                  a3 hA3Trans
                              have hA4Ne :=
                                RuleProofs.term_ne_stuck_of_has_smt_translation
                                  a4 hA4Trans
                              have hA5Ne :=
                                RuleProofs.term_ne_stuck_of_has_smt_translation
                                  a5 hA5Trans
                              change __eo_typeof
                                  (__eo_prog_str_concat_unify a1 a2 a3 a4 a5) =
                                Term.Bool at hResultTy
                              have hRawBody :
                                  __eo_prog_str_concat_unify a1 a2 a3 a4 a5 =
                                    rawStrConcatUnifyConclusion
                                      a1 a2 a3 a4 a5 := by
                                simp [__eo_prog_str_concat_unify,
                                  rawStrConcatUnifyConclusion,
                                  strConcatUnifyLeftEq, strConcatUnifyTail,
                                  hA1Ne, hA2Ne, hA3Ne, hA4Ne, hA5Ne,
                                  mkEq, mkConcat]
                              have hRawNe :
                                  rawStrConcatUnifyConclusion a1 a2 a3 a4 a5 ≠
                                    Term.Stuck := by
                                rw [← hRawBody]
                                exact term_ne_stuck_of_typeof_bool hResultTy
                              have hProgEq :
                                  __eo_prog_str_concat_unify a1 a2 a3 a4 a5 =
                                    strConcatUnifyConclusion a1 a2 a3 a4 a5 :=
                                hRawBody.trans
                                  (raw_str_concat_unify_eq a1 a2 a3 a4 a5
                                    hRawNe)
                              have hConclusionTy :
                                  __eo_typeof
                                      (strConcatUnifyConclusion
                                        a1 a2 a3 a4 a5) = Term.Bool := by
                                simpa [hProgEq] using hResultTy
                              rcases str_concat_unify_smt_types_of_eo_type
                                  a1 a2 a3 a4 a5 hA1Trans hA2Trans hA3Trans
                                  hA4Trans hA5Trans hConclusionTy with
                                ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty, hA5Ty,
                                  hElimSNe, hElimTNe⟩
                              have hBool := eo_has_bool_type_str_concat_unify
                                a1 a2 a3 a4 a5 T hA1Ty hA2Ty hA3Ty hA4Ty
                                  hA5Ty hElimSNe hElimTNe
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_str_concat_unify
                                    a1 a2 a3 a4 a5) true
                                rw [hProgEq]
                                exact eo_interprets_str_concat_unify M hM
                                  a1 a2 a3 a4 a5 T hA1Ty hA2Ty hA3Ty hA4Ty
                                  hA5Ty hElimSNe hElimTNe
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_concat_unify
                                    a1 a2 a3 a4 a5)
                                rw [hProgEq]
                                exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _ hBool
