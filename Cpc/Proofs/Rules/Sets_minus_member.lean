module

public import Cpc.Proofs.RuleSupport.SetsMemberSupport
import all Cpc.Proofs.RuleSupport.SetsMemberSupport

open Eo
open SmtEval
open Smtm
open SetsMemberSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def setsMinusMemberFormula (x y z : Term) : Term :=
  let mem := Term.Apply Term.set_member x
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply mem (Term.Apply (Term.Apply Term.set_minus y) z)))
    (Term.Apply
      (Term.Apply Term.and (Term.Apply mem y))
      (Term.Apply
        (Term.Apply Term.and (Term.Apply Term.not (Term.Apply mem z)))
        (Term.Boolean true)))

private theorem eo_typeof_not_eq_bool_info
    {A : Term}
    (h : __eo_typeof_not A = Term.Bool) :
    A = Term.Bool := by
  cases A <;> simp [__eo_typeof_not] at h ⊢

private theorem setsMinusMember_eo_arg_types
    {x y z : Term}
    (hTy : __eo_typeof (setsMinusMemberFormula x y z) = Term.Bool) :
    ∃ T : Term,
      __eo_typeof x = T ∧
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Set) T ∧
          __eo_typeof z = Term.Apply (Term.UOp UserOp.Set) T ∧
            T ≠ Term.Stuck := by
  let lhsTy :=
    __eo_typeof_set_member (__eo_typeof x)
      (__eo_typeof_set_union (__eo_typeof y) (__eo_typeof z))
  let mxyTy := __eo_typeof_set_member (__eo_typeof x) (__eo_typeof y)
  let mxzTy := __eo_typeof_set_member (__eo_typeof x) (__eo_typeof z)
  let notMxzTy := __eo_typeof_not mxzTy
  let innerTy := __eo_typeof_or notMxzTy Term.Bool
  let rhsTy := __eo_typeof_or mxyTy innerTy
  have hEqTy : __eo_typeof_eq lhsTy rhsTy = Term.Bool := by
    simpa [setsMinusMemberFormula, lhsTy, mxyTy, mxzTy, notMxzTy, innerTy, rhsTy, __eo_typeof, __eo_typeof_eq, __eo_typeof_not, __eo_typeof_or, __eo_typeof_set_member, __eo_typeof_set_union] using hTy
  rcases eo_typeof_eq_eq_bool_info hEqTy with ⟨hSame, hLhsNS⟩
  have hRhsNS : rhsTy ≠ Term.Stuck := by
    rw [← hSame]
    exact hLhsNS
  rcases eo_typeof_or_ne_stuck hRhsNS with ⟨hmxyBool, hInnerBool⟩
  have hInnerNS : innerTy ≠ Term.Stuck := by
    rw [hInnerBool]
    decide
  rcases eo_typeof_or_ne_stuck hInnerNS with ⟨hNotMxzBool, _hTrueBool⟩
  have hmxzBool : mxzTy = Term.Bool :=
    eo_typeof_not_eq_bool_info hNotMxzBool
  rcases eo_typeof_set_member_eq_bool_info hmxyBool with
    ⟨T, hxT, hyT, hTNS⟩
  rcases eo_typeof_set_member_eq_bool_info hmxzBool with
    ⟨U, hxU, hzU, _hUNS⟩
  have hUT : U = T := hxU.symm.trans hxT
  have hzT : __eo_typeof z = Term.Apply (Term.UOp UserOp.Set) T := by
    simpa [hUT] using hzU
  exact ⟨T, hxT, hyT, hzT, hTNS⟩

private theorem prog_sets_minus_member_eq_of_ne_stuck
    {x y z : Term}
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck)
    (hz : z ≠ Term.Stuck) :
    __eo_prog_sets_minus_member x y z = setsMinusMemberFormula x y z := by
  simp [__eo_prog_sets_minus_member, setsMinusMemberFormula]

private theorem typed___eo_prog_sets_minus_member_impl
    (x y z : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hzTrans : RuleProofs.eo_has_smt_translation z)
    (hTy : __eo_typeof (__eo_prog_sets_minus_member x y z) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sets_minus_member x y z) := by
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hyNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hzNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hzTrans
  have hProgEq :
      __eo_prog_sets_minus_member x y z = setsMinusMemberFormula x y z :=
    prog_sets_minus_member_eq_of_ne_stuck hxNe hyNe hzNe
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hzMatch :
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation z hzTrans
  have hFormulaTy :
      __eo_typeof (setsMinusMemberFormula x y z) = Term.Bool := by
    rw [hProgEq] at hTy
    exact hTy
  rcases setsMinusMember_eo_arg_types (x := x) (y := y) (z := z)
      hFormulaTy with
    ⟨T, hxTy, hyTy, hzTy, _hTNS⟩
  have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hxTrans
    simpa [hxMatch, hxTy] using hxTrans
  have hxSmtTy :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type T := by
    simpa [hxTy] using hxMatch
  have hySmtTy :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hyTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hyMatch
  have hzSmtTy :
      __smtx_typeof (__eo_to_smt z) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hzTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hzMatch
  rw [hProgEq]
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.set_member (__eo_to_smt x)
            (SmtTerm.set_minus (__eo_to_smt y) (__eo_to_smt z)))
          (SmtTerm.and
            (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.and
              (SmtTerm.not (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt z)))
              (SmtTerm.Boolean true)))) = SmtType.Bool
  simp [typeof_eq_eq, typeof_set_member_eq, typeof_set_minus_eq,
    typeof_and_eq, typeof_not_eq, __smtx_typeof_set_member,
    __smtx_typeof_sets_op_2, __smtx_typeof_eq, __smtx_typeof_guard,
    native_ite, native_Teq, __smtx_typeof.eq_1, hxSmtTy, hySmtTy, hzSmtTy]

private theorem facts___eo_prog_sets_minus_member_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hzTrans : RuleProofs.eo_has_smt_translation z)
    (hTy : __eo_typeof (__eo_prog_sets_minus_member x y z) = Term.Bool) :
    eo_interprets M (__eo_prog_sets_minus_member x y z) true := by
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_sets_minus_member x y z) :=
    typed___eo_prog_sets_minus_member_impl x y z hxTrans hyTrans hzTrans hTy
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hyNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hzNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hzTrans
  have hProgEq :
      __eo_prog_sets_minus_member x y z = setsMinusMemberFormula x y z :=
    prog_sets_minus_member_eq_of_ne_stuck hxNe hyNe hzNe
  have hFormulaTy :
      __eo_typeof (setsMinusMemberFormula x y z) = Term.Bool := by
    rw [hProgEq] at hTy
    exact hTy
  rcases setsMinusMember_eo_arg_types (x := x) (y := y) (z := z)
      hFormulaTy with
    ⟨T, hxTy, hyTy, hzTy, _hTNS⟩
  have hxMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxTrans
  have hyMatch :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hyTrans
  have hzMatch :
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation z hzTrans
  have hTNN : __eo_to_smt_type T ≠ SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hxTrans
    simpa [hxMatch, hxTy] using hxTrans
  have hxSmtTy :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type T := by
    simpa [hxTy] using hxMatch
  have hySmtTy :
      __smtx_typeof (__eo_to_smt y) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hyTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hyMatch
  have hzSmtTy :
      __smtx_typeof (__eo_to_smt z) = SmtType.Set (__eo_to_smt_type T) := by
    simpa [hzTy, __eo_to_smt_type,
      TranslationProofs.smtx_typeof_guard_of_non_none
        (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hTNN] using hzMatch
  have hxEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        __eo_to_smt_type T := by
    simpa [hxSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hxTrans)
  have hyEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hySmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hyTrans)
  have hzEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt z)) =
        SmtType.Set (__eo_to_smt_type T) := by
    simpa [hzSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt z)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hzTrans)
  rcases set_value_canonical (v := __smtx_model_eval M (__eo_to_smt y))
      (A := __eo_to_smt_type T) hyEvalTy with
    ⟨my, hyVal⟩
  rcases set_value_canonical (v := __smtx_model_eval M (__eo_to_smt z))
      (A := __eo_to_smt_type T) hzEvalTy with
    ⟨mz, hzVal⟩
  have hMyTy :
      __smtx_typeof_map_value my = SmtType.Map (__eo_to_smt_type T) SmtType.Bool :=
    set_map_value_typed (by simpa [hyVal] using hyEvalTy)
  have hMzTy :
      __smtx_typeof_map_value mz = SmtType.Map (__eo_to_smt_type T) SmtType.Bool :=
    set_map_value_typed (by simpa [hzVal] using hzEvalTy)
  have hYCanEval :
      value_canonical (__smtx_model_eval M (__eo_to_smt y)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM y hyTrans
  have hYCanSet : value_canonical (SmtValue.Set my) := by
    simpa [hyVal] using hYCanEval
  have hMyCan : __smtx_map_canonical my = true := by
    have hParts := hYCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact hParts.1
  have hMyDef : __smtx_map_get_default my = SmtValue.Boolean false := by
    have hParts := hYCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact eq_of_native_veq_true hParts.2
  let acc :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value my))
      (SmtValue.Boolean false)
  have hAccTy :
      __smtx_typeof_map_value acc =
        SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
    dsimp [acc]
    simp [__smtx_typeof_map_value, __smtx_index_typeof_map, hMyTy,
      __smtx_typeof_value]
  have hAccCan : __smtx_map_canonical acc = true := by
    dsimp [acc]
    exact set_empty_map_canonical (__smtx_index_typeof_map (__smtx_typeof_map_value my))
  have hAccLookupFalse :
      __smtx_map_lookup acc (__smtx_model_eval M (__eo_to_smt x)) =
        SmtValue.Boolean false := by
    simp [acc, __smtx_map_lookup]
  have hMinusLookup :
      __smtx_map_lookup (__smtx_set_op_rec false my mz acc)
          (__smtx_model_eval M (__eo_to_smt x)) =
        native_ite
          (native_and
            (native_veq
              (__smtx_map_lookup my (__smtx_model_eval M (__eo_to_smt x)))
              (SmtValue.Boolean true))
            (native_iff
              (native_veq
                (__smtx_map_lookup mz (__smtx_model_eval M (__eo_to_smt x)))
                (SmtValue.Boolean true))
              false))
          (SmtValue.Boolean true)
          (__smtx_map_lookup acc (__smtx_model_eval M (__eo_to_smt x))) :=
    mss_op_lookup_acc false (m1 := my) (m2 := mz) (acc := acc)
      (A := __eo_to_smt_type T) (i := __smtx_model_eval M (__eo_to_smt x))
      hMyTy hMzTy hAccTy hMyCan hAccCan hMyDef
  have hYLookupTy :
      __smtx_typeof_value
          (__smtx_map_lookup my (__smtx_model_eval M (__eo_to_smt x))) =
        SmtType.Bool :=
    map_lookup_typed hMyTy hxEvalTy
  have hZLookupTy :
      __smtx_typeof_value
          (__smtx_map_lookup mz (__smtx_model_eval M (__eo_to_smt x))) =
        SmtType.Bool :=
    map_lookup_typed hMzTy hxEvalTy
  let mem := Term.Apply Term.set_member x
  let lhs := Term.Apply mem (Term.Apply (Term.Apply Term.set_minus y) z)
  let rhs :=
    Term.Apply
      (Term.Apply Term.and (Term.Apply mem y))
      (Term.Apply
        (Term.Apply Term.and (Term.Apply Term.not (Term.Apply mem z)))
        (Term.Boolean true))
  have hProgBool' : RuleProofs.eo_has_bool_type (setsMinusMemberFormula x y z) := by
    simpa [hProgEq] using hProgBool
  have hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [setsMinusMemberFormula, lhs, rhs, mem] using hProgBool'
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change
      __smtx_model_eval M
          (SmtTerm.set_member (__eo_to_smt x)
            (SmtTerm.set_minus (__eo_to_smt y) (__eo_to_smt z))) =
        __smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.and
              (SmtTerm.not (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt z)))
              (SmtTerm.Boolean true)))
    simp [__smtx_model_eval, __smtx_model_eval_set_member, __smtx_model_eval_set_minus,
      __smtx_set_minus, __smtx_map_select, hyVal, hzVal]
    rw [hMinusLookup]
    rcases bool_value_canonical hYLookupTy with ⟨yb, hyb⟩
    rcases bool_value_canonical hZLookupTy with ⟨zb, hzb⟩
    rw [hyb, hzb]
    cases yb <;> cases zb <;>
      simp [__smtx_model_eval_and, __smtx_model_eval_not, native_ite, native_veq,
        native_iff, SmtEval.native_and, SmtEval.native_not, hAccLookupFalse]
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))
  rw [hProgEq]
  simpa [setsMinusMemberFormula, lhs, rhs, mem] using
    RuleProofs.eo_interprets_eq_of_rel M lhs rhs hEqBool hRel

public theorem cmd_step_sets_minus_member_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_minus_member args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_minus_member args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_minus_member args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_minus_member args premises ≠ Term.Stuck :=
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
                  cases premises with
                  | nil =>
                      let X := a1
                      let Y := a2
                      let Z := a3
                      have hTranses :
                          RuleProofs.eo_has_smt_translation X ∧
                            RuleProofs.eo_has_smt_translation Y ∧
                            RuleProofs.eo_has_smt_translation Z := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      change __eo_typeof (__eo_prog_sets_minus_member X Y Z) = Term.Bool at hResultTy
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M (__eo_prog_sets_minus_member X Y Z) true
                        exact facts___eo_prog_sets_minus_member_impl M hM X Y Z
                          hTranses.1 hTranses.2.1 hTranses.2.2 hResultTy
                      · change RuleProofs.eo_has_smt_translation (__eo_prog_sets_minus_member X Y Z)
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (__eo_prog_sets_minus_member X Y Z)
                          (typed___eo_prog_sets_minus_member_impl X Y Z
                            hTranses.1 hTranses.2.1 hTranses.2.2 hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
