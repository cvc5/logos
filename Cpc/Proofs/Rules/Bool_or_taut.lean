module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev eoOr (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B

private abbrev eoNot (A : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) A

private abbrev orTautInner (w ys zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.or) ys (eoOr (eoNot w) zs)

private abbrev orTautTail (w ys zs : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.or) w)
    (orTautInner w ys zs)

private abbrev orTautOuter (xs w ys zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.or) xs (orTautTail w ys zs)

private theorem prog_bool_or_taut_eq_of_ne_stuck
    (xs w ys zs : Term) :
    xs ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck ->
    __eo_prog_bool_or_taut xs w ys zs =
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq)
        (orTautOuter xs w ys zs)) (Term.Boolean true) := by
  intro hXs hW hYs hZs
  simpa [orTautOuter, orTautTail, orTautInner, eoOr, eoNot] using
    __eo_prog_bool_or_taut.eq_5 xs w ys zs hXs hW hYs hZs

private theorem facts___eo_prog_bool_or_taut_impl
    (M : SmtModel) (hM : model_wf M) (xs w ys zs : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation w ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation zs ->
    __eo_typeof (__eo_prog_bool_or_taut xs w ys zs) = Term.Bool ->
    eo_interprets M (__eo_prog_bool_or_taut xs w ys zs) true := by
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
    prog_bool_or_taut_eq_of_ne_stuck xs w ys zs hXsNe hWNe hYsNe hZsNe
  have hProgNe : __eo_prog_bool_or_taut xs w ys zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [hProgEq] at hProgNe hResultTy
  have hHeadNe := CnfSupport.mk_apply_ne_stuck_left hProgNe
  have hOuterNe : orTautOuter xs w ys zs ≠ Term.Stuck :=
    CnfSupport.mk_apply_ne_stuck_right hHeadNe
  have hOuterType : __eo_typeof (orTautOuter xs w ys zs) = Term.Bool :=
    CnfSupport.typeof_mk_eq_bool_left_const_bool hOuterNe hResultTy
  have hXsList : CnfSupport.OrList xs :=
    CnfSupport.orList_of_concat_ne_stuck_left hOuterNe
  have hTailList : CnfSupport.OrList (orTautTail w ys zs) :=
    CnfSupport.orList_of_concat_ne_stuck_right hOuterNe
  have hTailType : __eo_typeof (orTautTail w ys zs) = Term.Bool :=
    CnfSupport.orList_concat_typeof_bool_right hXsList hTailList hOuterType
  have hWType : __eo_typeof w = Term.Bool :=
    CnfSupport.typeof_mk_apply_or_left_bool hTailType
  have hInnerType : __eo_typeof (orTautInner w ys zs) = Term.Bool :=
    CnfSupport.typeof_mk_apply_or_right_bool hTailType
  have hWBool : RuleProofs.eo_has_bool_type w :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type w hWTrans hWType
  have hInnerList : CnfSupport.OrList (orTautInner w ys zs) :=
    CnfSupport.orList_tail_of_mk_apply_or hTailList
  have hInnerNe : orTautInner w ys zs ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hInnerType
  have hYsList : CnfSupport.OrList ys :=
    CnfSupport.orList_of_concat_ne_stuck_left hInnerNe
  have hTail2List : CnfSupport.OrList (eoOr (eoNot w) zs) :=
    CnfSupport.orList_of_concat_ne_stuck_right hInnerNe
  have hZsList : CnfSupport.OrList zs :=
    CnfSupport.orList_tail_of_apply_or hTail2List
  have hXsBool : RuleProofs.eo_has_bool_type xs :=
    CnfSupport.orList_has_bool_type_of_translation hXsList hXsTrans
  have hYsBool : RuleProofs.eo_has_bool_type ys :=
    CnfSupport.orList_has_bool_type_of_translation hYsList hYsTrans
  have hZsBool : RuleProofs.eo_has_bool_type zs :=
    CnfSupport.orList_has_bool_type_of_translation hZsList hZsTrans
  have hNotWBool : RuleProofs.eo_has_bool_type (eoNot w) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg w hWBool
  have hTail2Bool : RuleProofs.eo_has_bool_type (eoOr (eoNot w) zs) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args (eoNot w) zs hNotWBool hZsBool
  have hInnerBool : RuleProofs.eo_has_bool_type (orTautInner w ys zs) :=
    CnfSupport.orList_concat_preserves_bool_type hYsList hTail2List
      hYsBool hTail2Bool
  have hTailEq :
      orTautTail w ys zs = eoOr w (orTautInner w ys zs) := by
    exact CnfSupport.mk_apply_eq_apply (by simp) hInnerNe
  have hTailBool : RuleProofs.eo_has_bool_type (orTautTail w ys zs) := by
    rw [hTailEq]
    exact RuleProofs.eo_has_bool_type_or_of_bool_args w
      (orTautInner w ys zs) hWBool hInnerBool
  have hTailTrue : eo_interprets M (orTautTail w ys zs) true := by
    rcases CnfSupport.eo_interprets_bool_cases M hM w hWBool with hWTrue | hWFalse
    · rw [hTailEq]
      exact RuleProofs.eo_interprets_or_left_intro M hM
        w (orTautInner w ys zs) hWTrue hInnerBool
    · have hNotWTrue : eo_interprets M (eoNot w) true :=
        RuleProofs.eo_interprets_not_of_false M w hWFalse
      have hTail2True : eo_interprets M (eoOr (eoNot w) zs) true :=
        RuleProofs.eo_interprets_or_left_intro M hM
          (eoNot w) zs hNotWTrue hZsBool
      have hInnerTrue : eo_interprets M (orTautInner w ys zs) true :=
        CnfSupport.orList_concat_true_of_right_true M hM
          hYsList hTail2List hYsBool hTail2Bool hTail2True
      rw [hTailEq]
      exact RuleProofs.eo_interprets_or_right_intro M hM
        w (orTautInner w ys zs) hWBool hInnerTrue
  have hOuterTrue : eo_interprets M (orTautOuter xs w ys zs) true :=
    CnfSupport.orList_concat_true_of_right_true M hM
      hXsList hTailList hXsBool hTailBool hTailTrue
  rw [hProgEq]
  rw [CnfSupport.mk_apply_eq_apply (f := Term.UOp UserOp.eq)
    (a := orTautOuter xs w ys zs) (by simp) hOuterNe]
  rw [CnfSupport.mk_apply_eq_apply
    (f := Term.Apply (Term.UOp UserOp.eq) (orTautOuter xs w ys zs))
    (a := Term.Boolean true) (by simp) (by simp)]
  exact CnfSupport.eo_interprets_eq_true_of_true_true M
    (orTautOuter xs w ys zs) (Term.Boolean true)
    hOuterTrue (RuleProofs.eo_interprets_true M)

public theorem cmd_step_bool_or_taut_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_taut args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_or_taut args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_taut args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_or_taut args premises ≠ Term.Stuck :=
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
                          change __eo_typeof (__eo_prog_bool_or_taut a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          have hTrue : eo_interprets M
                              (__eo_prog_bool_or_taut a1 a2 a3 a4) true :=
                            facts___eo_prog_bool_or_taut_impl M hM a1 a2 a3 a4
                              hA1Trans hA2Trans hA3Trans hA4Trans hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTruePremises
                            exact hTrue
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue)
