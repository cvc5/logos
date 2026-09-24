module

public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm
open StrConcatUnifySupport
open StrConcatClashSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev rawMkEq (x y : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) x) y

private theorem raw_mk_eq_args_ne_stuck (x y : Term)
    (h : rawMkEq x y ≠ Term.Stuck) :
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck := by
  have hy := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (__eo_mk_apply (Term.UOp UserOp.eq) x) y h
  have hf := eo_mk_apply_fun_ne_stuck_of_ne_stuck
    (__eo_mk_apply (Term.UOp UserOp.eq) x) y h
  have hx := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.eq) x hf
  exact ⟨hx, hy⟩

private theorem raw_mk_eq_eq (x y : Term)
    (h : rawMkEq x y ≠ Term.Stuck) :
    rawMkEq x y = mkEq x y := by
  have hf := eo_mk_apply_fun_ne_stuck_of_ne_stuck
    (__eo_mk_apply (Term.UOp UserOp.eq) x) y h
  have ef : __eo_mk_apply (Term.UOp UserOp.eq) x =
      Term.Apply (Term.UOp UserOp.eq) x :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) x hf
  calc
    rawMkEq x y =
        Term.Apply (__eo_mk_apply (Term.UOp UserOp.eq) x) y :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.eq) x) y h
    _ = mkEq x y := by rw [ef]

private abbrev rawStrConcatUnifyRevAppend
    (suffix head middle : Term) : Term :=
  let nil := strConcatUnifyRevNil head
  let rawZ :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
    (__eo_list_concat (Term.UOp UserOp.str_concat) middle rawZ)

private theorem raw_str_concat_unify_rev_append_eq
    (suffix head middle : Term)
    (h : rawStrConcatUnifyRevAppend suffix head middle ≠ Term.Stuck) :
    rawStrConcatUnifyRevAppend suffix head middle =
      strConcatUnifyRevAppend head middle suffix := by
  let nil := strConcatUnifyRevNil head
  let rawZ :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil
  let rawLc :=
    __eo_list_concat (Term.UOp UserOp.str_concat) middle rawZ
  have hRawLc : rawLc ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) head) rawLc
      (by simpa [rawStrConcatUnifyRevAppend, rawLc, rawZ, nil] using h)
  have hRawZList :=
    (concat_clash_rev_list_concat_facts middle rawZ
      (by simpa [rawLc] using hRawLc)).2
  have hRawZ : rawZ ≠ Term.Stuck := by
    intro hz
    rw [hz] at hRawZList
    simp [__eo_is_list] at hRawZList
  have eRawZ : rawZ = mkConcat suffix nil :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil hRawZ
  have eRawLc :
      rawLc = __eo_list_concat (Term.UOp UserOp.str_concat) middle
        (mkConcat suffix nil) := by
    change __eo_list_concat (Term.UOp UserOp.str_concat) middle rawZ = _
    rw [eRawZ]
  have eRawAppend :
      rawStrConcatUnifyRevAppend suffix head middle =
        mkConcat head rawLc := by
    simpa [rawStrConcatUnifyRevAppend, rawLc, rawZ, nil] using
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) head) rawLc
        (by simpa [rawStrConcatUnifyRevAppend, rawLc, rawZ, nil] using h)
  rw [eRawAppend, eRawLc]

private abbrev rawStrConcatUnifyRevConclusion
    (suffix sHead sMiddle tHead tMiddle : Term) : Term :=
  let sAppend := rawStrConcatUnifyRevAppend suffix sHead sMiddle
  let tAppend := rawStrConcatUnifyRevAppend suffix tHead tMiddle
  let sNorm := __str_nary_elim (mkConcat sHead sMiddle)
  let tNorm := __str_nary_elim (mkConcat tHead tMiddle)
  rawMkEq (rawMkEq sAppend tAppend) (rawMkEq sNorm tNorm)

private theorem raw_str_concat_unify_rev_eq
    (suffix sHead sMiddle tHead tMiddle : Term)
    (h : rawStrConcatUnifyRevConclusion
        suffix sHead sMiddle tHead tMiddle ≠ Term.Stuck) :
    rawStrConcatUnifyRevConclusion
        suffix sHead sMiddle tHead tMiddle =
      strConcatUnifyRevConclusion
        suffix sHead sMiddle tHead tMiddle := by
  let sAppend := rawStrConcatUnifyRevAppend suffix sHead sMiddle
  let tAppend := rawStrConcatUnifyRevAppend suffix tHead tMiddle
  let sNorm := __str_nary_elim (mkConcat sHead sMiddle)
  let tNorm := __str_nary_elim (mkConcat tHead tMiddle)
  let rawLeft := rawMkEq sAppend tAppend
  let rawRight := rawMkEq sNorm tNorm
  have hOuter : rawMkEq rawLeft rawRight ≠ Term.Stuck := by
    simpa [rawStrConcatUnifyRevConclusion, rawLeft, rawRight,
      sAppend, tAppend, sNorm, tNorm] using h
  have hOuterArgs := raw_mk_eq_args_ne_stuck rawLeft rawRight hOuter
  have hLeftArgs := raw_mk_eq_args_ne_stuck sAppend tAppend hOuterArgs.1
  have eSAppend := raw_str_concat_unify_rev_append_eq
    suffix sHead sMiddle hLeftArgs.1
  have eTAppend := raw_str_concat_unify_rev_append_eq
    suffix tHead tMiddle hLeftArgs.2
  have eOuter := raw_mk_eq_eq rawLeft rawRight hOuter
  have eLeft : rawLeft = mkEq sAppend tAppend := by
    simpa [rawLeft] using raw_mk_eq_eq sAppend tAppend hOuterArgs.1
  have eRight : rawRight = mkEq sNorm tNorm := by
    simpa [rawRight] using raw_mk_eq_eq sNorm tNorm hOuterArgs.2
  have eSAppend' :
      sAppend = strConcatUnifyRevAppend sHead sMiddle suffix := by
    simpa [sAppend] using eSAppend
  have eTAppend' :
      tAppend = strConcatUnifyRevAppend tHead tMiddle suffix := by
    simpa [tAppend] using eTAppend
  change rawMkEq rawLeft rawRight =
    strConcatUnifyRevConclusion suffix sHead sMiddle tHead tMiddle
  rw [eOuter, eLeft, eRight, eSAppend', eTAppend']

public theorem cmd_step_str_concat_unify_rev_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_unify_rev args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify_rev args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_unify_rev args premises ≠
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
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.2.1
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
                                  (__eo_prog_str_concat_unify_rev
                                    a1 a2 a3 a4 a5) = Term.Bool at hResultTy
                              have hRawBody :
                                  __eo_prog_str_concat_unify_rev
                                      a1 a2 a3 a4 a5 =
                                    rawStrConcatUnifyRevConclusion
                                      a1 a2 a3 a4 a5 := by
                                simp [__eo_prog_str_concat_unify_rev,
                                  rawStrConcatUnifyRevConclusion,
                                  rawStrConcatUnifyRevAppend,
                                  strConcatUnifyRevNil, rawMkEq,
                                  hA1Ne, hA2Ne, hA3Ne, hA4Ne, hA5Ne,
                                  mkEq, mkConcat]
                              have hRawNe :
                                  rawStrConcatUnifyRevConclusion
                                      a1 a2 a3 a4 a5 ≠ Term.Stuck := by
                                rw [← hRawBody]
                                exact term_ne_stuck_of_typeof_bool hResultTy
                              have hProgEq :
                                  __eo_prog_str_concat_unify_rev
                                      a1 a2 a3 a4 a5 =
                                    strConcatUnifyRevConclusion
                                      a1 a2 a3 a4 a5 :=
                                hRawBody.trans
                                  (raw_str_concat_unify_rev_eq
                                    a1 a2 a3 a4 a5 hRawNe)
                              have hConclusionTy :
                                  __eo_typeof
                                      (strConcatUnifyRevConclusion
                                        a1 a2 a3 a4 a5) = Term.Bool := by
                                simpa [hProgEq] using hResultTy
                              rcases str_concat_unify_rev_smt_types_of_eo_type
                                  a1 a2 a3 a4 a5 hA1Trans hA2Trans
                                  hA3Trans hA4Trans hA5Trans hConclusionTy with
                                ⟨T, hA1Ty, hA2Ty, hA4Ty,
                                  hSNormTy, hTNormTy, hSAppendTy,
                                  hTAppendTy, hA3List, hA5List,
                                  hA3Cases, hA5Cases⟩
                              have hBool := eo_has_bool_type_str_concat_unify_rev
                                a1 a2 a3 a4 a5 T hSNormTy hTNormTy
                                  hSAppendTy hTAppendTy
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_str_concat_unify_rev
                                    a1 a2 a3 a4 a5) true
                                rw [hProgEq]
                                exact eo_interprets_str_concat_unify_rev M hM
                                  a1 a2 a3 a4 a5 T hA1Ty hA2Ty hA4Ty
                                  hSNormTy hTNormTy hSAppendTy hTAppendTy
                                  hA3List hA5List hA3Cases hA5Cases
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_concat_unify_rev
                                    a1 a2 a3 a4 a5)
                                rw [hProgEq]
                                exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    (strConcatUnifyRevConclusion
                                      a1 a2 a3 a4 a5) hBool
