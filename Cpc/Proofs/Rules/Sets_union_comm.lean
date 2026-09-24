module

public import Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport
import all Cpc.Proofs.RuleSupport.SetsBasicRewritesSupport

open Eo
open SmtEval
open Smtm
open SetsEvalOpSupport
open SetsMemberSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev mkSetEq := SetsBasicRewritesSupport.mkEq
private abbrev mkSetUnion := SetsBasicRewritesSupport.mkSetUnion

private theorem prog_sets_union_comm_eq_of_ne_stuck
    (x y : Term)
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck) :
    __eo_prog_sets_union_comm x y =
      mkSetEq (mkSetUnion x y) (mkSetUnion y x) := by
  cases x <;> cases y <;>
    simp [__eo_prog_sets_union_comm, mkSetEq, mkSetUnion,
      SetsBasicRewritesSupport.mkEq, SetsBasicRewritesSupport.mkSetUnion] at hx hy ⊢

private theorem smtx_typeof_of_eo_set
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Set T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Set (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_set,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_set] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) hComponentNN)

private theorem smtx_typeof_set_union_of_same_set
    (x y : Term) (A : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Set A)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Set A) :
    __smtx_typeof (__eo_to_smt (mkSetUnion x y)) = SmtType.Set A := by
  change __smtx_typeof (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Set A
  rw [typeof_set_union_eq]
  simp [__smtx_typeof_sets_op_2, hxTy, hyTy, native_ite, native_Teq]

private theorem typed___eo_prog_sets_union_comm_impl
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : __eo_typeof (__eo_prog_sets_union_comm x y) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sets_union_comm x y) := by
  have hxNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hyNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hProg := prog_sets_union_comm_eq_of_ne_stuck x y hxNotStuck hyNotStuck
  rw [hProg] at hTy
  rcases SetsBasicRewritesSupport.eo_typeof_set_union_bool_info (x := x) (y := y)
      (rhs := mkSetUnion y x) hTy with
    ⟨T, hxEoTy, hyEoTy, _hrhsTy⟩
  have hxSmtTy := smtx_typeof_of_eo_set x T hxTrans hxEoTy
  have hySmtTy := smtx_typeof_of_eo_set y T hyTrans hyEoTy
  have hLhsTy :=
    smtx_typeof_set_union_of_same_set x y (__eo_to_smt_type T) hxSmtTy hySmtTy
  have hRhsTy :=
    smtx_typeof_set_union_of_same_set y x (__eo_to_smt_type T) hySmtTy hxSmtTy
  rw [hProg]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mkSetUnion x y) (mkSetUnion y x)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem set_union_comm_rel
    (mx my : SmtMap) (A : SmtType)
    (hMxCan : __smtx_map_canonical mx = true)
    (hMyCan : __smtx_map_canonical my = true)
    (hMxTy : __smtx_typeof_map_value mx = SmtType.Map A SmtType.Bool)
    (hMyTy : __smtx_typeof_map_value my = SmtType.Map A SmtType.Bool)
    (hMxDef : __smtx_map_get_default mx = SmtValue.Boolean false)
    (hMyDef : __smtx_map_get_default my = SmtValue.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_set_union (SmtValue.Set mx) (SmtValue.Set my))
      (__smtx_set_union (SmtValue.Set my) (SmtValue.Set mx)) := by
  let left :=
    __smtx_set_op_rec false mx
      (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
        (SmtValue.Boolean false)) my
  let right :=
    __smtx_set_op_rec false my
      (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value my))
        (SmtValue.Boolean false)) mx
  have hEmptyMxTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [hMxTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hEmptyMyTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value my))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [hMyTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hLeftCan : __smtx_map_canonical left = true := by
    dsimp [left]
    exact Smtm.mss_op_internal_canonical false hMxCan hMyCan
  have hRightCan : __smtx_map_canonical right = true := by
    dsimp [right]
    exact Smtm.mss_op_internal_canonical false hMyCan hMxCan
  have hLeftTy :
      __smtx_typeof_map_value left = SmtType.Map A SmtType.Bool := by
    dsimp [left]
    exact Smtm.mss_op_internal_typed false hMxTy hEmptyMxTy hMyTy
  have hRightTy :
      __smtx_typeof_map_value right = SmtType.Map A SmtType.Bool := by
    dsimp [right]
    exact Smtm.mss_op_internal_typed false hMyTy hEmptyMyTy hMxTy
  have hLeftDef :
      __smtx_map_get_default left = SmtValue.Boolean false := by
    dsimp [left]
    rw [Smtm.mss_op_internal_get_default false]
    exact hMyDef
  have hRightDef :
      __smtx_map_get_default right = SmtValue.Boolean false := by
    dsimp [right]
    rw [Smtm.mss_op_internal_get_default false]
    exact hMxDef
  have hLeaf : smt_map_default_leaf left = smt_map_default_leaf right := by
    rw [set_default_leaf hLeftCan hLeftTy hLeftDef,
      set_default_leaf hRightCan hRightTy hRightDef]
  have hLookup :
      ∀ v : SmtValue, __smtx_map_lookup left v = __smtx_map_lookup right v := by
    intro v
    dsimp [left, right]
    rw [set_union_lookup mx my A v hMxTy hMyTy hMxCan hMyCan hMxDef]
    rw [set_union_lookup my mx A v hMyTy hMxTy hMyCan hMxCan hMyDef]
    have hMxLookupTy :
        __smtx_typeof_value (__smtx_map_lookup mx v) = SmtType.Bool :=
      set_map_lookup_bool (m := mx) (A := A) (i := v) hMxTy
    have hMyLookupTy :
        __smtx_typeof_value (__smtx_map_lookup my v) = SmtType.Bool :=
      set_map_lookup_bool (m := my) (A := A) (i := v) hMyTy
    rcases bool_value_canonical hMxLookupTy with ⟨bx, hbx⟩
    rcases bool_value_canonical hMyLookupTy with ⟨byy, hbyy⟩
    rw [hbx, hbyy]
    cases bx <;> cases byy <;> simp [native_ite, native_veq]
  simpa [__smtx_set_union, left, right] using
    RuleProofs.smt_value_rel_set_of_lookup_eq left right hLeftCan hRightCan
      hLeaf hLookup

private theorem facts___eo_prog_sets_union_comm_impl
    (M : SmtModel) (hM : model_wf M)
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hTy : __eo_typeof (__eo_prog_sets_union_comm x y) = Term.Bool) :
    eo_interprets M (__eo_prog_sets_union_comm x y) true := by
  have hxNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hyNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hProg := prog_sets_union_comm_eq_of_ne_stuck x y hxNotStuck hyNotStuck
  have hFormulaTy :
      __eo_typeof (mkSetEq (mkSetUnion x y) (mkSetUnion y x)) = Term.Bool := by
    simpa [hProg] using hTy
  rcases SetsBasicRewritesSupport.eo_typeof_set_union_bool_info (x := x) (y := y)
      (rhs := mkSetUnion y x) hFormulaTy with
    ⟨T, hxEoTy, hyEoTy, _hrhsTy⟩
  have hxSmtTy := smtx_typeof_of_eo_set x T hxTrans hxEoTy
  have hySmtTy := smtx_typeof_of_eo_set y T hyTrans hyEoTy
  rcases set_value_facts M hM x (__eo_to_smt_type T) hxTrans hxSmtTy with
    ⟨mx, hXEval, hMxCan, hMxTy, hMxDef⟩
  rcases set_value_facts M hM y (__eo_to_smt_type T) hyTrans hySmtTy with
    ⟨my, hYEval, hMyCan, hMyTy, hMyDef⟩
  have hFormulaBool :
      RuleProofs.eo_has_bool_type (mkSetEq (mkSetUnion x y) (mkSetUnion y x)) := by
    simpa [hProg] using
      typed___eo_prog_sets_union_comm_impl x y hxTrans hyTrans hTy
  rw [hProg]
  simpa [mkSetEq, SetsBasicRewritesSupport.mkEq] using
    RuleProofs.eo_interprets_eq_of_rel M (mkSetUnion x y) (mkSetUnion y x)
      hFormulaBool
      (by
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)))
          (__smtx_model_eval M (SmtTerm.set_union (__eo_to_smt y) (__eo_to_smt x)))
        rw [model_eval_union_eq M (__eo_to_smt x) (__eo_to_smt y),
          model_eval_union_eq M (__eo_to_smt y) (__eo_to_smt x), hXEval, hYEval]
        exact set_union_comm_rel mx my (__eo_to_smt_type T)
          hMxCan hMyCan hMxTy hMyTy hMxDef hMyDef)

public theorem cmd_step_sets_union_comm_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_union_comm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_union_comm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_union_comm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_union_comm args premises ≠ Term.Stuck :=
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
              cases premises with
              | nil =>
                  have hTransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have ha1Trans : RuleProofs.eo_has_smt_translation a1 :=
                    hTransPair.1
                  have ha2Trans : RuleProofs.eo_has_smt_translation a2 :=
                    hTransPair.2.1
                  change __eo_typeof (__eo_prog_sets_union_comm a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_sets_union_comm a1 a2) true
                    exact facts___eo_prog_sets_union_comm_impl M hM a1 a2
                      ha1Trans ha2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_sets_union_comm_impl a1 a2
                        ha1Trans ha2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
