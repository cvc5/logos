module

public import Cpc.Proofs.RuleSupport.StrContainsConcatSupport
import all Cpc.Proofs.RuleSupport.StrContainsConcatSupport

open Eo
open SmtEval
open Smtm
open StrContainsConcatSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev containsConcatFindPremise (middle needle : Term) : Term :=
  mkEq (containsTerm middle needle) (Term.Boolean true)

private abbrev containsConcatFindConclusion
    (pfx middle needle suffix : Term) : Term :=
  mkEq (containsTerm (concatMiddle pfx middle suffix) needle)
    (Term.Boolean true)

private abbrev rawContainsConcatFindConclusion
    (whole needle : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_contains) whole) needle))
    (Term.Boolean true)

private theorem raw_contains_concat_find_conclusion_eq
    (whole needle : Term)
    (h : rawContainsConcatFindConclusion whole needle ≠ Term.Stuck) :
    rawContainsConcatFindConclusion whole needle =
      mkEq (containsTerm whole needle) (Term.Boolean true) := by
  let fContains := __eo_mk_apply (Term.UOp UserOp.str_contains) whole
  let inner := __eo_mk_apply fContains needle
  let fEq := __eo_mk_apply (Term.UOp UserOp.eq) inner
  have hFEq : fEq ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck fEq (Term.Boolean true)
      (by simpa [rawContainsConcatFindConclusion, fContains, inner, fEq]
        using h)
  have hInner : inner ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) inner hFEq
  have hFContains : fContains ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck fContains needle hInner
  have e1 : fContains = Term.Apply (Term.UOp UserOp.str_contains) whole :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.str_contains) whole hFContains
  have e2 : inner = Term.Apply fContains needle :=
    eo_mk_apply_eq_apply_of_ne_stuck fContains needle hInner
  have e3 : fEq = Term.Apply (Term.UOp UserOp.eq) inner :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) inner hFEq
  have e4 : __eo_mk_apply fEq (Term.Boolean true) =
      Term.Apply fEq (Term.Boolean true) :=
    eo_mk_apply_eq_apply_of_ne_stuck fEq (Term.Boolean true)
      (by simpa [rawContainsConcatFindConclusion, fContains, inner, fEq]
        using h)
  change __eo_mk_apply fEq (Term.Boolean true) = _
  rw [e4, e3, e2, e1]

private theorem prog_str_contains_concat_find_info
    (pfx middle needle suffix P : Term)
    (hProg :
      __eo_prog_str_contains_concat_find pfx middle needle suffix
          (Proof.pf P) ≠ Term.Stuck) :
    ∃ middle0 needle0,
      P = containsConcatFindPremise middle0 needle0 ∧
      middle0 = middle ∧ needle0 = needle ∧
      __eo_prog_str_contains_concat_find pfx middle needle suffix
          (Proof.pf P) =
        containsConcatFindConclusion pfx middle needle suffix := by
  let Pfx := pfx
  let Middle := middle
  let Needle := needle
  let Suffix := suffix
  unfold __eo_prog_str_contains_concat_find at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hMiddle, hNeedle⟩
    subst_vars
    let whole := concatMiddle Pfx Middle Suffix
    have hBody :
        __eo_prog_str_contains_concat_find Pfx Middle Needle Suffix
            (Proof.pf (containsConcatFindPremise Middle Needle)) =
          rawContainsConcatFindConclusion whole Needle := by
      simp_all [__eo_prog_str_contains_concat_find, __eo_requires,
        __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
        SmtEval.native_not, rawContainsConcatFindConclusion, whole,
        Pfx, Middle, Needle, Suffix, concatMiddle,
        containsConcatFindPremise]
    have hRawNe :
        rawContainsConcatFindConclusion whole Needle ≠ Term.Stuck := by
      have hResultNe := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
      simpa [rawContainsConcatFindConclusion, whole, concatMiddle,
        Pfx, Middle, Needle, Suffix] using hResultNe
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    rw [hBody]
    simpa [whole, containsConcatFindConclusion, Pfx, Middle, Needle,
      Suffix] using
        raw_contains_concat_find_conclusion_eq whole Needle hRawNe

private theorem eval_contains_of_interprets_true
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (h : eo_interprets M
      (mkEq (containsTerm x y) (Term.Boolean true)) true) :
    __smtx_model_eval M (__eo_to_smt (containsTerm x y)) =
      SmtValue.Boolean true := by
  have hXEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x)
      (SmtType.Seq T) hXTy (seq_ne_none T) (type_inhabited_seq T)
  have hYEvalTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt y)
      (SmtType.Seq T) hYTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq
            (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq,
        StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
        hXEval, hYEval,
        show __smtx_model_eval M (SmtTerm.Boolean true) =
            SmtValue.Boolean true by rw [__smtx_model_eval.eq_def]] at hEval
      have hNative :
          native_seq_contains (native_unpack_seq sx)
              (native_unpack_seq sy) = true := by
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
      rw [str_contains_eval_eq M x y sx sy hXEval hYEval, hNative]

public theorem cmd_step_str_contains_concat_find_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_concat_find args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_concat_find args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_concat_find args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_concat_find args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons pfx args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons middle args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons needle args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons suffix args =>
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
                              have hPfxTrans :
                                  RuleProofs.eo_has_smt_translation pfx := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.1
                              have hMiddleTrans :
                                  RuleProofs.eo_has_smt_translation middle := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.2.1
                              have hNeedleTrans :
                                  RuleProofs.eo_has_smt_translation needle := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.1
                              have hSuffixTrans :
                                  RuleProofs.eo_has_smt_translation suffix := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_contains_concat_find
                                    pfx middle needle suffix (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_contains_concat_find
                                      pfx middle needle suffix (Proof.pf P) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_contains_concat_find_info
                                  pfx middle needle suffix P hRuleProg with
                                ⟨middle0, needle0, hP, hMiddle0, hNeedle0,
                                  hProgEq⟩
                              subst middle0
                              subst needle0
                              rw [hProgEq] at hResultTy
                              let whole := concatMiddle pfx middle suffix
                              let core := containsTerm whole needle
                              have hCoreEoTy : __eo_typeof core = Term.Bool := by
                                change __eo_typeof_eq (__eo_typeof core)
                                    Term.Bool = Term.Bool at hResultTy
                                exact
                                  RuleProofs.eo_typeof_eq_bool_operands_eq
                                    _ _ hResultTy
                              have hCoreNN :
                                  __eo_typeof core ≠ Term.Stuck := by
                                rw [hCoreEoTy]
                                decide
                              change __eo_typeof_str_contains
                                  (__eo_typeof whole) (__eo_typeof needle) ≠
                                Term.Stuck at hCoreNN
                              rcases
                                  StrContainsReplCharSupport.eo_typeof_str_contains_args_of_ne_stuck
                                    (__eo_typeof whole) (__eo_typeof needle)
                                    hCoreNN with
                                ⟨U, hWholeEoTy, hNeedleEoTy⟩
                              have hStructure :=
                                concat_middle_structure pfx middle suffix U
                                  (by simpa [whole] using hWholeEoTy)
                              have hTypes :=
                                concat_middle_smt_types pfx middle suffix U
                                  hPfxTrans hMiddleTrans hSuffixTrans
                                  (by simpa [whole] using hWholeEoTy)
                              let T := __eo_to_smt_type U
                              have hWholeTy :
                                  __smtx_typeof (__eo_to_smt whole) =
                                    SmtType.Seq T := by
                                simpa [whole, T] using hTypes.1
                              have hMiddleTy :
                                  __smtx_typeof (__eo_to_smt middle) =
                                    SmtType.Seq T := by
                                simpa [T] using hTypes.2.1
                              have hSuffixTy :
                                  __smtx_typeof (__eo_to_smt suffix) =
                                    SmtType.Seq T := by
                                simpa [T] using hTypes.2.2
                              have hNeedleTy :
                                  __smtx_typeof (__eo_to_smt needle) =
                                    SmtType.Seq T := by
                                simpa [T] using
                                  StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof
                                    needle U hNeedleTrans hNeedleEoTy
                              have hConclusionBool :
                                  RuleProofs.eo_has_bool_type
                                    (containsConcatFindConclusion
                                      pfx middle needle suffix) := by
                                simpa [containsConcatFindConclusion, whole]
                                  using eo_has_bool_type_contains_eq_bool
                                    whole needle true T hWholeTy hNeedleTy
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M
                                      (containsConcatFindPremise
                                        middle needle) true := by
                                  simpa [hP] using hPremRaw
                                have hMiddleContains :=
                                  eval_contains_of_interprets_true M hM
                                    middle needle T hMiddleTy hNeedleTy hPrem
                                have hWholeContains :=
                                  eval_contains_concat_middle M hM pfx middle
                                    suffix needle T hStructure.1
                                    hStructure.2.2.1 hWholeTy hMiddleTy
                                    hSuffixTy hNeedleTy hMiddleContains
                                change eo_interprets M
                                  (__eo_prog_str_contains_concat_find
                                    pfx middle needle suffix (Proof.pf P)) true
                                rw [hProgEq]
                                exact eo_interprets_contains_eq_bool_of_eval
                                  M whole needle true
                                  (by simpa [containsConcatFindConclusion,
                                    whole] using hConclusionBool)
                                  hWholeContains
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_contains_concat_find
                                    pfx middle needle suffix (Proof.pf P))
                                rw [hProgEq]
                                exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _ hConclusionBool
