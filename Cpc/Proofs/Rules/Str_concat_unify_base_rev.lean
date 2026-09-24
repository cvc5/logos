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

private abbrev rawStrConcatUnifyBaseRevConclusion
    (suffix head middle A : Term) : Term :=
  let nil := strConcatUnifyRevNil head
  let rawZ :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil
  let rawAppend :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
      (__eo_list_concat (Term.UOp UserOp.str_concat) middle rawZ)
  let rawLeft :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) suffix) rawAppend
  let rawLeftFun := __eo_mk_apply (Term.UOp UserOp.eq) rawLeft
  let rawRightFun :=
    __eo_mk_apply (Term.UOp UserOp.eq) (strConcatUnifyBaseEmpty A)
  let rawRight :=
    __eo_mk_apply rawRightFun
      (__str_nary_elim (mkConcat head middle))
  __eo_mk_apply rawLeftFun rawRight

private theorem raw_str_concat_unify_base_rev_eq
    (suffix head middle A : Term)
    (h : rawStrConcatUnifyBaseRevConclusion suffix head middle A ≠
      Term.Stuck) :
    rawStrConcatUnifyBaseRevConclusion suffix head middle A =
      strConcatUnifyBaseRevConclusion suffix head middle A := by
  let nil := strConcatUnifyRevNil head
  let rawZ :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil
  let rawLc :=
    __eo_list_concat (Term.UOp UserOp.str_concat) middle rawZ
  let rawAppend :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head) rawLc
  let rawLeft :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) suffix) rawAppend
  let rawLeftFun := __eo_mk_apply (Term.UOp UserOp.eq) rawLeft
  let empty := strConcatUnifyBaseEmpty A
  let elim := __str_nary_elim (mkConcat head middle)
  let rawRightFun := __eo_mk_apply (Term.UOp UserOp.eq) empty
  let rawRight := __eo_mk_apply rawRightFun elim
  have hRawRight : rawRight ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck rawLeftFun rawRight
      (by simpa [rawStrConcatUnifyBaseRevConclusion, rawLeftFun, rawRight,
        rawRightFun, rawLeft, rawAppend, rawLc, rawZ, nil, empty, elim]
        using h)
  have hRawLeftFun : rawLeftFun ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck rawLeftFun rawRight
      (by simpa [rawStrConcatUnifyBaseRevConclusion, rawLeftFun, rawRight,
        rawRightFun, rawLeft, rawAppend, rawLc, rawZ, nil, empty, elim]
        using h)
  have hRawLeft : rawLeft ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) rawLeft
      hRawLeftFun
  have hRawAppend : rawAppend ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) suffix) rawAppend hRawLeft
  have hRawLc : rawLc ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) head) rawLc hRawAppend
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
  have eRawAppend : rawAppend = mkConcat head rawLc :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) head) rawLc hRawAppend
  have eRawLeft : rawLeft = mkEq suffix rawAppend :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) suffix) rawAppend hRawLeft
  have eRawLeftFun : rawLeftFun = Term.Apply (Term.UOp UserOp.eq) rawLeft :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) rawLeft
      hRawLeftFun
  have hRawRightFun : rawRightFun ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck rawRightFun elim hRawRight
  have eRawRightFun :
      rawRightFun = Term.Apply (Term.UOp UserOp.eq) empty :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) empty
      hRawRightFun
  have eRawRight : rawRight = mkEq empty elim :=
    calc
      rawRight = Term.Apply rawRightFun elim :=
        eo_mk_apply_eq_apply_of_ne_stuck rawRightFun elim hRawRight
      _ = mkEq empty elim := by rw [eRawRightFun]
  have eOuter :
      rawStrConcatUnifyBaseRevConclusion suffix head middle A =
        Term.Apply rawLeftFun rawRight :=
    eo_mk_apply_eq_apply_of_ne_stuck rawLeftFun rawRight
      (by simpa [rawStrConcatUnifyBaseRevConclusion, rawLeftFun, rawRight,
        rawRightFun, rawLeft, rawAppend, rawLc, rawZ, nil, empty, elim]
        using h)
  rw [eOuter, eRawLeftFun, eRawLeft, eRawAppend, eRawLc, eRawRight]

private theorem str_concat_unify_base_rev_type_shape
    (suffix head middle ty : Term)
    (h : __eo_prog_str_concat_unify_base_rev suffix head middle ty ≠
      Term.Stuck) :
    ∃ A, ty = Term.Apply Term.Seq A := by
  have hs : suffix ≠ Term.Stuck := by
    intro hs
    subst suffix
    simp [__eo_prog_str_concat_unify_base_rev] at h
  have hh : head ≠ Term.Stuck := by
    intro hh
    subst head
    cases suffix <;> simp [__eo_prog_str_concat_unify_base_rev] at h
  have hm : middle ≠ Term.Stuck := by
    intro hm
    subst middle
    cases suffix <;> cases head <;>
      simp [__eo_prog_str_concat_unify_base_rev] at h
  cases ty <;>
    simp [__eo_prog_str_concat_unify_base_rev, hs, hh, hm] at h ⊢
  case Apply f A =>
    cases f <;>
      simp [__eo_prog_str_concat_unify_base_rev, hs, hh, hm] at h ⊢
    case UOp op =>
      cases op <;>
        simp [__eo_prog_str_concat_unify_base_rev, hs, hh, hm] at h ⊢

public theorem cmd_step_str_concat_unify_base_rev_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify_base_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_unify_base_rev args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify_base_rev args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_unify_base_rev args premises ≠
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
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          change __eo_typeof
                              (__eo_prog_str_concat_unify_base_rev
                                a1 a2 a3 a4) = Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_concat_unify_base_rev
                                  a1 a2 a3 a4 ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases str_concat_unify_base_rev_type_shape
                              a1 a2 a3 a4 hRuleProg with ⟨A, hA4⟩
                          subst a4
                          have hA1Trans :
                              RuleProofs.eo_has_smt_translation a1 := by
                            exact hCmdTrans.1
                          have hA2Trans :
                              RuleProofs.eo_has_smt_translation a2 := by
                            exact hCmdTrans.2.1
                          have hA3Trans :
                              RuleProofs.eo_has_smt_translation a3 := by
                            exact hCmdTrans.2.2.1
                          have hA1Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation
                              a1 hA1Trans
                          have hA2Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation
                              a2 hA2Trans
                          have hA3Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation
                              a3 hA3Trans
                          have hRawBody :
                              __eo_prog_str_concat_unify_base_rev a1 a2 a3
                                  (Term.Apply Term.Seq A) =
                                rawStrConcatUnifyBaseRevConclusion
                                  a1 a2 a3 A := by
                            simp [__eo_prog_str_concat_unify_base_rev,
                              rawStrConcatUnifyBaseRevConclusion,
                              strConcatUnifyRevNil,
                              strConcatUnifyBaseEmpty, hA1Ne, hA2Ne,
                              hA3Ne, mkEq, mkConcat]
                          have hRawNe :
                              rawStrConcatUnifyBaseRevConclusion
                                  a1 a2 a3 A ≠ Term.Stuck := by
                            rw [← hRawBody]
                            exact term_ne_stuck_of_typeof_bool hResultTy
                          have hProgEq :
                              __eo_prog_str_concat_unify_base_rev a1 a2 a3
                                  (Term.Apply Term.Seq A) =
                                strConcatUnifyBaseRevConclusion
                                  a1 a2 a3 A :=
                            hRawBody.trans
                              (raw_str_concat_unify_base_rev_eq
                                a1 a2 a3 A hRawNe)
                          have hConclusionTy :
                              __eo_typeof
                                  (strConcatUnifyBaseRevConclusion
                                    a1 a2 a3 A) = Term.Bool := by
                            simpa [hProgEq] using hResultTy
                          rcases
                              str_concat_unify_base_rev_smt_types_of_eo_type
                                a1 a2 a3 A hA1Trans hA2Trans hA3Trans
                                hConclusionTy with
                            ⟨T, hA1Ty, hA2Ty, hEmptyTy, hElimTy,
                              hAppendTy, _hElimNe, hA3List, hA3Cases⟩
                          have hBool :=
                            eo_has_bool_type_str_concat_unify_base_rev
                              a1 a2 a3 A T hA1Ty hEmptyTy hElimTy
                              hAppendTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_str_concat_unify_base_rev a1 a2 a3
                                (Term.Apply Term.Seq A)) true
                            rw [hProgEq]
                            exact eo_interprets_str_concat_unify_base_rev
                              M hM a1 a2 a3 A T hA1Ty hA2Ty hEmptyTy
                              hElimTy hAppendTy hA3List hA3Cases
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_str_concat_unify_base_rev a1 a2 a3
                                (Term.Apply Term.Seq A))
                            rw [hProgEq]
                            exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                (strConcatUnifyBaseRevConclusion
                                  a1 a2 a3 A) hBool
