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

private abbrev containsConcatFindContraPremise (outer middle : Term) : Term :=
  mkEq (containsTerm outer middle) (Term.Boolean false)

private abbrev containsConcatFindContraConclusion
    (pfx middle outer suffix : Term) : Term :=
  mkEq (containsTerm outer (concatMiddle pfx middle suffix))
    (Term.Boolean false)

private abbrev rawContainsConcatFindContraConclusion
    (outer whole : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.str_contains) outer) whole))
    (Term.Boolean false)

private theorem raw_contains_concat_find_contra_conclusion_eq
    (outer whole : Term)
    (h : rawContainsConcatFindContraConclusion outer whole ≠ Term.Stuck) :
    rawContainsConcatFindContraConclusion outer whole =
      mkEq (containsTerm outer whole) (Term.Boolean false) := by
  let inner :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_contains) outer) whole
  let fEq := __eo_mk_apply (Term.UOp UserOp.eq) inner
  have hFEq : fEq ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck fEq (Term.Boolean false)
      (by simpa [rawContainsConcatFindContraConclusion, inner, fEq] using h)
  have hInner : inner ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) inner hFEq
  have e1 : inner =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) outer) whole :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_contains) outer) whole hInner
  have e2 : fEq = Term.Apply (Term.UOp UserOp.eq) inner :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) inner hFEq
  have e3 : __eo_mk_apply fEq (Term.Boolean false) =
      Term.Apply fEq (Term.Boolean false) :=
    eo_mk_apply_eq_apply_of_ne_stuck fEq (Term.Boolean false)
      (by simpa [rawContainsConcatFindContraConclusion, inner, fEq] using h)
  change __eo_mk_apply fEq (Term.Boolean false) = _
  rw [e3, e2, e1]

private theorem prog_str_contains_concat_find_contra_info
    (pfx middle outer suffix P : Term)
    (hProg :
      __eo_prog_str_contains_concat_find_contra pfx middle outer suffix
          (Proof.pf P) ≠ Term.Stuck) :
    ∃ outer0 middle0,
      P = containsConcatFindContraPremise outer0 middle0 ∧
      outer0 = outer ∧ middle0 = middle ∧
      __eo_prog_str_contains_concat_find_contra pfx middle outer suffix
          (Proof.pf P) =
        containsConcatFindContraConclusion pfx middle outer suffix := by
  let Pfx := pfx
  let Middle := middle
  let Outer := outer
  let Suffix := suffix
  unfold __eo_prog_str_contains_concat_find_contra at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hOuter, hMiddle⟩
    subst_vars
    let whole := concatMiddle Pfx Middle Suffix
    have hBody :
        __eo_prog_str_contains_concat_find_contra Pfx Middle Outer Suffix
            (Proof.pf (containsConcatFindContraPremise Outer Middle)) =
          rawContainsConcatFindContraConclusion Outer whole := by
      simp_all [__eo_prog_str_contains_concat_find_contra, __eo_requires,
        __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
        SmtEval.native_not, rawContainsConcatFindContraConclusion, whole,
        Pfx, Middle, Outer, Suffix, concatMiddle,
        containsConcatFindContraPremise]
    have hRawNe :
        rawContainsConcatFindContraConclusion Outer whole ≠ Term.Stuck := by
      have hResultNe := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
      simpa [rawContainsConcatFindContraConclusion, whole, concatMiddle,
        Pfx, Middle, Outer, Suffix] using hResultNe
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    rw [hBody]
    simpa [whole, containsConcatFindContraConclusion, Pfx, Middle, Outer,
      Suffix] using
        raw_contains_concat_find_contra_conclusion_eq Outer whole hRawNe

public theorem cmd_step_str_contains_concat_find_contra_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_concat_find_contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_concat_find_contra args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_concat_find_contra args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_concat_find_contra
          args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons pfx args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons middle args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons outer args =>
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
                              have hOuterTrans :
                                  RuleProofs.eo_has_smt_translation outer := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.1
                              have hSuffixTrans :
                                  RuleProofs.eo_has_smt_translation suffix := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_contains_concat_find_contra
                                    pfx middle outer suffix (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_contains_concat_find_contra
                                      pfx middle outer suffix (Proof.pf P) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_contains_concat_find_contra_info
                                  pfx middle outer suffix P hRuleProg with
                                ⟨outer0, middle0, hP, hOuter0, hMiddle0,
                                  hProgEq⟩
                              subst outer0
                              subst middle0
                              rw [hProgEq] at hResultTy
                              let whole := concatMiddle pfx middle suffix
                              let core := containsTerm outer whole
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
                                  (__eo_typeof outer) (__eo_typeof whole) ≠
                                Term.Stuck at hCoreNN
                              rcases
                                  StrContainsReplCharSupport.eo_typeof_str_contains_args_of_ne_stuck
                                    (__eo_typeof outer) (__eo_typeof whole)
                                    hCoreNN with
                                ⟨U, hOuterEoTy, hWholeEoTy⟩
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
                              have hOuterTy :
                                  __smtx_typeof (__eo_to_smt outer) =
                                    SmtType.Seq T := by
                                simpa [T] using
                                  StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof
                                    outer U hOuterTrans hOuterEoTy
                              have hConclusionBool :
                                  RuleProofs.eo_has_bool_type
                                    (containsConcatFindContraConclusion
                                      pfx middle outer suffix) := by
                                simpa [containsConcatFindContraConclusion,
                                  whole] using
                                    eo_has_bool_type_contains_eq_bool
                                      outer whole false T hOuterTy hWholeTy
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M
                                      (containsConcatFindContraPremise
                                        outer middle) true := by
                                  simpa [hP] using hPremRaw
                                have hOuterMiddle :=
                                  eval_contains_of_interprets_eq_bool M hM
                                    outer middle false T hOuterTy hMiddleTy
                                    hPrem
                                have hMiddleSelf :=
                                  eval_contains_self M hM middle T hMiddleTy
                                have hWholeMiddle :=
                                  eval_contains_concat_middle M hM pfx middle
                                    suffix middle T hStructure.1
                                    hStructure.2.2.1 hWholeTy hMiddleTy
                                    hSuffixTy hMiddleTy hMiddleSelf
                                have hOuterWhole :=
                                  eval_contains_false_of_contained_witness
                                    M hM outer whole middle T hOuterTy
                                    hWholeTy hMiddleTy hOuterMiddle
                                    hWholeMiddle
                                change eo_interprets M
                                  (__eo_prog_str_contains_concat_find_contra
                                    pfx middle outer suffix (Proof.pf P)) true
                                rw [hProgEq]
                                exact eo_interprets_contains_eq_bool_of_eval
                                  M outer whole false
                                  (by simpa
                                    [containsConcatFindContraConclusion,
                                      whole] using hConclusionBool)
                                  hOuterWhole
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_contains_concat_find_contra
                                    pfx middle outer suffix (Proof.pf P))
                                rw [hProgEq]
                                exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _ hConclusionBool
