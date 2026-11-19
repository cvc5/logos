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
private abbrev mkSetInter := SetsBasicRewritesSupport.mkSetInter

private theorem prog_sets_inter_self_eq_of_ne_stuck
    (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_prog_sets_inter_self x = mkSetEq (mkSetInter x x) x := by
  cases x <;>
    simp [__eo_prog_sets_inter_self, mkSetEq, mkSetInter,
      SetsBasicRewritesSupport.mkEq, SetsBasicRewritesSupport.mkSetInter] at hx ⊢

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

private theorem smtx_typeof_set_inter_of_same_set
    (x y : Term) (A : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Set A)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Set A) :
    __smtx_typeof (__eo_to_smt (mkSetInter x y)) = SmtType.Set A := by
  change __smtx_typeof (SmtTerm.set_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Set A
  rw [typeof_set_inter_eq]
  simp [__smtx_typeof_sets_op_2, hxTy, hyTy, native_ite, native_Teq]

private theorem typed___eo_prog_sets_inter_self_impl
    (x : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (__eo_prog_sets_inter_self x) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sets_inter_self x) := by
  have hxNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hProg := prog_sets_inter_self_eq_of_ne_stuck x hxNotStuck
  rw [hProg] at hTy
  rcases SetsBasicRewritesSupport.eo_typeof_set_inter_bool_info (x := x) (y := x)
      (rhs := x) hTy with
    ⟨T, hxEoTy, _hxEoTy', _hrhsTy⟩
  have hxSmtTy := smtx_typeof_of_eo_set x T hxTrans hxEoTy
  have hLhsTy :=
    smtx_typeof_set_inter_of_same_set x x (__eo_to_smt_type T) hxSmtTy hxSmtTy
  rw [hProg]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mkSetInter x x) x
    (by rw [hLhsTy, hxSmtTy]) (by rw [hLhsTy]; simp)

private theorem set_inter_self_rel
    (mx : SmtMap) (A : SmtType)
    (hMxCan : __smtx_map_canonical uc mx = true)
    (hMxTy : __smtx_typeof_map_value mx = SmtType.Map A SmtType.Bool)
    (hMxDef : __smtx_map_get_default mx = SmtValue.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_set_inter (SmtValue.Set mx) (SmtValue.Set mx))
      (SmtValue.Set mx) := by
  let left :=
    __smtx_set_op_rec true mx mx
      (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
        (SmtValue.Boolean false))
  have hEmptyMxTy :
      __smtx_typeof_map_value
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
            (SmtValue.Boolean false)) = SmtType.Map A SmtType.Bool := by
    rw [hMxTy]
    simp [__smtx_index_typeof_map, __smtx_typeof_map_value,
      __smtx_typeof_value]
  have hEmptyMxCan :
      __smtx_map_canonical uc
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
            (SmtValue.Boolean false)) = true := by
    rw [hMxTy]
    exact Smtm.set_empty_map_canonical A
  have hLeftCan : __smtx_map_canonical uc left = true := by
    dsimp [left]
    exact Smtm.mss_op_internal_canonical true hMxCan hEmptyMxCan
  have hLeftTy :
      __smtx_typeof_map_value left = SmtType.Map A SmtType.Bool := by
    dsimp [left]
    exact Smtm.mss_op_internal_typed true hMxTy hMxTy hEmptyMxTy
  have hLeftDef :
      __smtx_map_get_default left = SmtValue.Boolean false := by
    dsimp [left]
    rw [Smtm.mss_op_internal_get_default true, hMxTy]
    rfl
  have hLeaf : smt_map_default_leaf left = smt_map_default_leaf mx := by
    rw [set_default_leaf hLeftCan hLeftTy hLeftDef,
      set_default_leaf hMxCan hMxTy hMxDef]
  have hLookup :
      ∀ v : SmtValue, __smtx_map_lookup left v = __smtx_map_lookup mx v := by
    intro v
    dsimp [left]
    rw [set_inter_lookup (mx := mx) (my := mx) (A := A) (i := v)
      hMxTy hMxTy hMxCan hMxDef]
    have hMxLookupTy :
        __smtx_typeof_value (__smtx_map_lookup mx v) = SmtType.Bool :=
      set_map_lookup_bool (m := mx) (A := A) (i := v) hMxTy
    rcases bool_value_canonical hMxLookupTy with ⟨bx, hbx⟩
    rw [hbx]
    cases bx <;> simp [native_ite, native_veq, SmtEval.native_and]
  simpa [__smtx_set_inter, left] using
    RuleProofs.smt_value_rel_set_of_lookup_eq left mx hLeftCan hMxCan
      hLeaf hLookup

private theorem facts___eo_prog_sets_inter_self_impl
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (__eo_prog_sets_inter_self x) = Term.Bool) :
    eo_interprets M (__eo_prog_sets_inter_self x) true := by
  have hxNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hProg := prog_sets_inter_self_eq_of_ne_stuck x hxNotStuck
  have hFormulaTy :
      __eo_typeof (mkSetEq (mkSetInter x x) x) = Term.Bool := by
    simpa [hProg] using hTy
  rcases SetsBasicRewritesSupport.eo_typeof_set_inter_bool_info (x := x) (y := x)
      (rhs := x) hFormulaTy with
    ⟨T, hxEoTy, _hxEoTy', _hrhsTy⟩
  have hxSmtTy := smtx_typeof_of_eo_set x T hxTrans hxEoTy
  rcases set_value_facts M hM x (__eo_to_smt_type T) hxTrans hxSmtTy with
    ⟨mx, hXEval, hMxCan, hMxTy, hMxDef⟩
  have hFormulaBool :
      RuleProofs.eo_has_bool_type (mkSetEq (mkSetInter x x) x) := by
    simpa [hProg] using
      typed___eo_prog_sets_inter_self_impl x hxTrans hTy
  rw [hProg]
  simpa [mkSetEq, SetsBasicRewritesSupport.mkEq] using
    RuleProofs.eo_interprets_eq_of_rel M (mkSetInter x x) x
      hFormulaBool
      (by
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.set_inter (__eo_to_smt x) (__eo_to_smt x)))
          (__smtx_model_eval M (__eo_to_smt x))
        rw [model_eval_inter_eq M (__eo_to_smt x) (__eo_to_smt x), hXEval]
        exact set_inter_self_rel mx (__eo_to_smt_type T)
          hMxCan hMxTy hMxDef)

public theorem cmd_step_sets_inter_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_inter_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_inter_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_inter_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.sets_inter_self args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hTransPair :
                  RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have ha1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hTransPair.1
              change __eo_typeof (__eo_prog_sets_inter_self a1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_sets_inter_self a1) true
                exact facts___eo_prog_sets_inter_self_impl M hM a1
                  ha1Trans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_sets_inter_self_impl a1
                    ha1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
