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

private abbrev eqCtnFalsePremise (outer middle : Term) : Term :=
  mkEq (containsTerm outer middle) (Term.Boolean false)

private abbrev eqCtnFalseInner
    (pfx middle suffix outer : Term) : Term :=
  mkEq (concatMiddle pfx middle suffix) outer

private abbrev eqCtnFalseConclusion
    (pfx middle suffix outer : Term) : Term :=
  mkEq (eqCtnFalseInner pfx middle suffix outer) (Term.Boolean false)

private abbrev rawEqCtnFalseConclusion (whole outer : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq) whole) outer))
    (Term.Boolean false)

private theorem raw_eq_ctn_false_conclusion_eq
    (whole outer : Term)
    (h : rawEqCtnFalseConclusion whole outer ≠ Term.Stuck) :
    rawEqCtnFalseConclusion whole outer =
      mkEq (mkEq whole outer) (Term.Boolean false) := by
  let fInner := __eo_mk_apply (Term.UOp UserOp.eq) whole
  let inner := __eo_mk_apply fInner outer
  let fOuter := __eo_mk_apply (Term.UOp UserOp.eq) inner
  have hFOuter : fOuter ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck fOuter (Term.Boolean false)
      (by simpa [rawEqCtnFalseConclusion, fInner, inner, fOuter] using h)
  have hInner : inner ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) inner hFOuter
  have hFInner : fInner ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck fInner outer hInner
  have e1 : fInner = Term.Apply (Term.UOp UserOp.eq) whole :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) whole hFInner
  have e2 : inner = Term.Apply fInner outer :=
    eo_mk_apply_eq_apply_of_ne_stuck fInner outer hInner
  have e3 : fOuter = Term.Apply (Term.UOp UserOp.eq) inner :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) inner hFOuter
  have e4 : __eo_mk_apply fOuter (Term.Boolean false) =
      Term.Apply fOuter (Term.Boolean false) :=
    eo_mk_apply_eq_apply_of_ne_stuck fOuter (Term.Boolean false)
      (by simpa [rawEqCtnFalseConclusion, fInner, inner, fOuter] using h)
  change __eo_mk_apply fOuter (Term.Boolean false) = _
  rw [e4, e3, e2, e1]

private theorem prog_str_eq_ctn_false_info
    (pfx middle suffix outer P : Term)
    (hProg :
      __eo_prog_str_eq_ctn_false pfx middle suffix outer (Proof.pf P) ≠
        Term.Stuck) :
    ∃ outer0 middle0,
      P = eqCtnFalsePremise outer0 middle0 ∧
      outer0 = outer ∧ middle0 = middle ∧
      __eo_prog_str_eq_ctn_false pfx middle suffix outer (Proof.pf P) =
        eqCtnFalseConclusion pfx middle suffix outer := by
  let Pfx := pfx
  let Middle := middle
  let Suffix := suffix
  let Outer := outer
  unfold __eo_prog_str_eq_ctn_false at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hOuter, hMiddle⟩
    subst_vars
    let whole := concatMiddle Pfx Middle Suffix
    have hBody :
        __eo_prog_str_eq_ctn_false Pfx Middle Suffix Outer
            (Proof.pf (eqCtnFalsePremise Outer Middle)) =
          rawEqCtnFalseConclusion whole Outer := by
      simp_all [__eo_prog_str_eq_ctn_false, __eo_requires, __eo_eq,
        __eo_and, SmtEval.native_ite, native_teq, native_and,
        SmtEval.native_not, rawEqCtnFalseConclusion, whole, Pfx,
        Middle, Suffix, Outer, concatMiddle, eqCtnFalsePremise]
    have hRawNe : rawEqCtnFalseConclusion whole Outer ≠ Term.Stuck := by
      have hResultNe := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
      simpa [rawEqCtnFalseConclusion, whole, concatMiddle, Pfx,
        Middle, Suffix, Outer] using hResultNe
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    rw [hBody]
    simpa [whole, eqCtnFalseConclusion, eqCtnFalseInner, Pfx, Middle,
      Suffix, Outer] using
        raw_eq_ctn_false_conclusion_eq whole Outer hRawNe

private theorem eo_has_bool_type_eq_false
    (x y : Term) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type
      (mkEq (mkEq x y) (Term.Boolean false)) := by
  have hInnerTy : RuleProofs.eo_has_bool_type (mkEq x y) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x y
      (by rw [hXTy, hYTy]) (by rw [hXTy]; exact seq_ne_none T)
  have hFalseTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mkEq x y) (Term.Boolean false)
    (by rw [hInnerTy, hFalseTy]) (by rw [hInnerTy]; decide)

public theorem cmd_step_str_eq_ctn_false_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_ctn_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_ctn_false args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_ctn_false args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_ctn_false args premises ≠
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
          | cons suffix args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons outer args =>
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
                              have hSuffixTrans :
                                  RuleProofs.eo_has_smt_translation suffix := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.1
                              have hOuterTrans :
                                  RuleProofs.eo_has_smt_translation outer := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_eq_ctn_false pfx middle suffix
                                    outer (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_eq_ctn_false pfx middle suffix
                                      outer (Proof.pf P) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_eq_ctn_false_info pfx middle
                                  suffix outer P hRuleProg with
                                ⟨outer0, middle0, hP, hOuter0, hMiddle0,
                                  hProgEq⟩
                              subst outer0
                              subst middle0
                              rw [hProgEq] at hResultTy
                              let whole := concatMiddle pfx middle suffix
                              let inner := mkEq whole outer
                              have hInnerEoTy :
                                  __eo_typeof inner = Term.Bool := by
                                change __eo_typeof_eq (__eo_typeof inner)
                                    Term.Bool = Term.Bool at hResultTy
                                exact
                                  RuleProofs.eo_typeof_eq_bool_operands_eq
                                    _ _ hResultTy
                              change __eo_typeof_eq (__eo_typeof whole)
                                  (__eo_typeof outer) = Term.Bool at hInnerEoTy
                              have hSameEoTy :
                                  __eo_typeof whole = __eo_typeof outer :=
                                RuleProofs.eo_typeof_eq_bool_operands_eq
                                  _ _ hInnerEoTy
                              have hWholeEoNN :
                                  __eo_typeof whole ≠ Term.Stuck :=
                                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof whole) (__eo_typeof outer)
                                  hInnerEoTy).1
                              have hWholeNe : whole ≠ Term.Stuck := by
                                intro h
                                rw [h] at hWholeEoNN
                                exact hWholeEoNN rfl
                              have hFacts :=
                                StrConcatClashSupport.concat_clash_rev_list_concat_facts
                                  pfx (concatTail middle suffix)
                                  (by simpa [whole] using hWholeNe)
                              have hEqRec :=
                                StrConcatClashSupport.concat_clash_rev_list_concat_eq_rec
                                  pfx (concatTail middle suffix)
                                  (by simpa [whole] using hWholeNe)
                              have hRecEoNN :
                                  __eo_typeof
                                      (__eo_list_concat_rec pfx
                                        (concatTail middle suffix)) ≠
                                    Term.Stuck := by
                                rw [← hEqRec]
                                simpa [whole] using hWholeEoNN
                              have hTailEoNN :
                                  __eo_typeof (concatTail middle suffix) ≠
                                    Term.Stuck :=
                                StrConcatClashSupport.concat_clash_rev_list_concat_rec_right_type_ne_stuck
                                  pfx (concatTail middle suffix) hFacts.1
                                  hRecEoNN
                              rcases eo_typeof_str_concat_seq_of_ne_stuck
                                  middle suffix hTailEoNN with
                                ⟨U, hMiddleEoTy, hSuffixEoTy, hTailEoTy⟩
                              have hRecEoTy :=
                                eo_typeof_list_concat_rec_of_right_seq
                                  pfx (concatTail middle suffix) U hFacts.1
                                  hTailEoTy hRecEoNN
                              have hWholeEoTy :
                                  __eo_typeof whole = Term.Apply Term.Seq U := by
                                rw [show whole =
                                    __eo_list_concat_rec pfx
                                      (concatTail middle suffix) by
                                  simpa [whole] using hEqRec]
                                exact hRecEoTy
                              have hOuterEoTy :
                                  __eo_typeof outer = Term.Apply Term.Seq U := by
                                rw [← hSameEoTy]
                                exact hWholeEoTy
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
                                    (eqCtnFalseConclusion pfx middle suffix
                                      outer) := by
                                simpa [eqCtnFalseConclusion,
                                  eqCtnFalseInner, whole] using
                                    eo_has_bool_type_eq_false whole outer T
                                      hWholeTy hOuterTy
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M
                                      (eqCtnFalsePremise outer middle) true := by
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
                                have hInnerEval :=
                                  eval_eq_false_of_contains_witness M hM
                                    whole outer middle T hWholeTy hOuterTy
                                    hMiddleTy hWholeMiddle hOuterMiddle
                                change eo_interprets M
                                  (__eo_prog_str_eq_ctn_false pfx middle suffix
                                    outer (Proof.pf P)) true
                                rw [hProgEq]
                                exact RuleProofs.eo_interprets_eq_of_rel M
                                  inner (Term.Boolean false)
                                  (by simpa [eqCtnFalseConclusion,
                                    eqCtnFalseInner, inner, whole] using
                                      hConclusionBool) <| by
                                    change RuleProofs.smt_value_rel
                                      (__smtx_model_eval M
                                        (__eo_to_smt inner))
                                      (__smtx_model_eval M
                                        (SmtTerm.Boolean false))
                                    rw [show __smtx_model_eval M
                                        (__eo_to_smt inner) =
                                          SmtValue.Boolean false by
                                      simpa [inner] using hInnerEval,
                                      show __smtx_model_eval M
                                          (SmtTerm.Boolean false) =
                                            SmtValue.Boolean false by
                                        rw [__smtx_model_eval.eq_def]]
                                    exact RuleProofs.smt_value_rel_refl
                                      (SmtValue.Boolean false)
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_str_eq_ctn_false pfx middle suffix
                                    outer (Proof.pf P))
                                rw [hProgEq]
                                exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _ hConclusionBool
