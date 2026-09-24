module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev eoAnd (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B

private abbrev eoNot (A : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) A

private abbrev andConfInner (w ys zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.and) ys (eoAnd (eoNot w) zs)

private abbrev andConfTail (w ys zs : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) w)
    (andConfInner w ys zs)

private abbrev andConfOuter (xs w ys zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.and) xs (andConfTail w ys zs)

private theorem prog_bool_and_conf_eq_of_ne_stuck
    (xs w ys zs : Term) :
    xs ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    __eo_prog_bool_and_conf xs w ys zs =
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq)
        (andConfOuter xs w ys zs)) (Term.Boolean false) := by
  intro hXs hW hYs hZs
  simpa [andConfOuter, andConfTail, andConfInner, eoAnd, eoNot] using
    __eo_prog_bool_and_conf.eq_5 xs w ys zs hXs hW hYs hZs

private theorem facts___eo_prog_bool_and_conf_impl
    (M : SmtModel) (hM : model_wf M) (xs w ys zs : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation w ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_and_conf xs w ys zs) = Term.Bool ->
    eo_interprets M (__eo_prog_bool_and_conf xs w ys zs) true := by
  intro hXsTrans hWTrans hYsTrans hZsTrans hResultTy
  have hXsNe : xs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hWNe : w ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hYsNe : ys ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hZsNe : zs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation zs hZsTrans
  have hProgEq :=
    prog_bool_and_conf_eq_of_ne_stuck xs w ys zs hXsNe hWNe hYsNe hZsNe
  have hProgNe : __eo_prog_bool_and_conf xs w ys zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [hProgEq] at hProgNe hResultTy
  have hHeadNe := CnfSupport.mk_apply_ne_stuck_left hProgNe
  have hOuterNe : andConfOuter xs w ys zs ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hHeadNe
  have hOuterType : __eo_typeof (andConfOuter xs w ys zs) = Term.Bool :=
    CnfSupport.typeof_mk_eq_bool_left_const_bool hOuterNe hResultTy
  have hXsList : CnfSupport.AndList xs :=
    CnfSupport.andList_of_concat_ne_stuck_left hOuterNe
  have hTailList : CnfSupport.AndList (andConfTail w ys zs) :=
    CnfSupport.andList_of_concat_ne_stuck_right hOuterNe
  have hTailType : __eo_typeof (andConfTail w ys zs) = Term.Bool :=
    CnfSupport.andList_concat_typeof_bool_right hXsList hTailList hOuterType
  have hWType : __eo_typeof w = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_left_bool hTailType
  have hInnerType : __eo_typeof (andConfInner w ys zs) = Term.Bool :=
    CnfSupport.typeof_mk_apply_and_right_bool hTailType
  have hWBool : RuleProofs.eo_has_bool_type w :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type w hWTrans hWType
  have hInnerList : CnfSupport.AndList (andConfInner w ys zs) :=
    CnfSupport.andList_tail_of_mk_apply_and hTailList
  have hInnerNe : andConfInner w ys zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hInnerType
  have hYsList : CnfSupport.AndList ys :=
    CnfSupport.andList_of_concat_ne_stuck_left hInnerNe
  have hTail2List : CnfSupport.AndList (eoAnd (eoNot w) zs) :=
    CnfSupport.andList_of_concat_ne_stuck_right hInnerNe
  have hZsList : CnfSupport.AndList zs :=
    CnfSupport.andList_tail_of_apply_and hTail2List
  have hXsBool : RuleProofs.eo_has_bool_type xs :=
    CnfSupport.andList_has_bool_type_of_translation hXsList hXsTrans
  have hYsBool : RuleProofs.eo_has_bool_type ys :=
    CnfSupport.andList_has_bool_type_of_translation hYsList hYsTrans
  have hZsBool : RuleProofs.eo_has_bool_type zs :=
    CnfSupport.andList_has_bool_type_of_translation hZsList hZsTrans
  have hNotWBool : RuleProofs.eo_has_bool_type (eoNot w) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg w hWBool
  have hTail2Bool : RuleProofs.eo_has_bool_type (eoAnd (eoNot w) zs) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args (eoNot w) zs hNotWBool hZsBool
  have hInnerBool : RuleProofs.eo_has_bool_type (andConfInner w ys zs) :=
    CnfSupport.andList_concat_preserves_bool_type hYsList hTail2List
      hYsBool hTail2Bool
  have hTailEq :
      andConfTail w ys zs = eoAnd w (andConfInner w ys zs) := by
    exact CnfSupport.mk_apply_eq_apply (by simp) hInnerNe
  have hTailBool : RuleProofs.eo_has_bool_type (andConfTail w ys zs) := by
    rw [hTailEq]
    exact RuleProofs.eo_has_bool_type_and_of_bool_args w
      (andConfInner w ys zs) hWBool hInnerBool
  have hTailFalse : eo_interprets M (andConfTail w ys zs) false := by
    rcases CnfSupport.eo_interprets_bool_cases M hM w hWBool with hWTrue | hWFalse
    · have hNotWFalse : eo_interprets M (eoNot w) false :=
        CnfSupport.eo_interprets_not_false_of_true M w hWTrue
      have hTail2False : eo_interprets M (eoAnd (eoNot w) zs) false :=
        CnfSupport.eo_interprets_and_false_of_left_false M hM
          (eoNot w) zs hNotWFalse hZsBool
      have hInnerFalse : eo_interprets M (andConfInner w ys zs) false :=
        CnfSupport.andList_concat_false_of_right_false M hM
          hYsList hTail2List hYsBool hTail2Bool hTail2False
      rw [hTailEq]
      exact CnfSupport.eo_interprets_and_false_of_right_false M hM
        w (andConfInner w ys zs) hWBool hInnerFalse
    · rw [hTailEq]
      exact CnfSupport.eo_interprets_and_false_of_left_false M hM
        w (andConfInner w ys zs) hWFalse hInnerBool
  have hOuterFalse : eo_interprets M (andConfOuter xs w ys zs) false :=
    CnfSupport.andList_concat_false_of_right_false M hM
      hXsList hTailList hXsBool hTailBool hTailFalse
  rw [hProgEq]
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.eq)
    (a := andConfOuter xs w ys zs) (by simp) hOuterNe]
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (andConfOuter xs w ys zs))
    (a := Term.Boolean false) (by simp) (by simp)]
  exact CnfSupport.eo_interprets_eq_true_of_false_false M
    (andConfOuter xs w ys zs) (Term.Boolean false)
    hOuterFalse (CnfSupport.eo_interprets_false M)

public theorem cmd_step_bool_and_conf_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_and_conf args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_and_conf args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_and_conf args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_and_conf args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hTransPack :
                              RuleProofs.eo_has_smt_translation a1 ∧
                              RuleProofs.eo_has_smt_translation a2 ∧
                              RuleProofs.eo_has_smt_translation a3 ∧
                              RuleProofs.eo_has_smt_translation a4 ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                          have hA1Trans := hTransPack.1
                          have hA2Trans := hTransPack.2.1
                          have hA3Trans := hTransPack.2.2.1
                          have hA4Trans := hTransPack.2.2.2.1
                          change __eo_typeof (__eo_prog_bool_and_conf a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          have hTrue : eo_interprets M
                              (__eo_prog_bool_and_conf a1 a2 a3 a4) true :=
                            facts___eo_prog_bool_and_conf_impl M hM a1 a2 a3 a4
                              hA1Trans hA2Trans hA3Trans hA4Trans hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTruePremises
                            exact hTrue
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue)
