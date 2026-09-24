module

public import Cpc.Proofs.RuleSupport.ArraySupport
import all Cpc.Proofs.RuleSupport.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_arrays_read_over_write_1_eq
    (a i e i2 : Term) :
    __eo_prog_arrays_read_over_write_1
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2) =
      __eo_requires (__eo_eq i i2) (Term.Boolean true)
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i))
          e) := by
  rfl

private theorem shape_of_prog_arrays_read_over_write_1_not_stuck
    (x : Term)
    (h : __eo_prog_arrays_read_over_write_1 x ≠ Term.Stuck) :
    ∃ a i e i2 : Term,
      x =
        Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2 := by
  cases x with
  | Apply f i2 =>
      cases f with
      | Apply g storeTerm =>
          cases g with
          | UOp op =>
              cases op <;> try (simp [__eo_prog_arrays_read_over_write_1] at h)
              case select =>
                cases storeTerm with
                | Apply fStoreE e =>
                    cases fStoreE with
                    | Apply fStoreI i =>
                        cases fStoreI with
                        | Apply storeOp a =>
                            cases storeOp with
                            | UOp op =>
                                cases op <;> try (simp at h)
                                case store =>
                                  exact ⟨a, i, e, i2, rfl⟩
                            | _ =>
                                simp at h
                        | _ =>
                            simp at h
                    | _ =>
                        simp at h
                | _ =>
                    simp at h
          | _ =>
              simp [__eo_prog_arrays_read_over_write_1] at h
      | _ =>
          simp [__eo_prog_arrays_read_over_write_1] at h
  | _ =>
      simp [__eo_prog_arrays_read_over_write_1] at h

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem requires_eq_self_true_body (i body : Term)
    (hINotStuck : i ≠ Term.Stuck) :
    __eo_requires (__eo_eq i i) (Term.Boolean true) body = body := by
  simp [__eo_requires, eo_eq_self_true_of_ne_stuck i hINotStuck,
    native_ite, native_teq, native_not, SmtEval.native_not]

private theorem smt_types_of_select_store_arg
    (a i e idx : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) idx)) :
    ∃ A B : SmtType,
      __smtx_typeof (__eo_to_smt a) = SmtType.Map A B ∧
        __smtx_typeof (__eo_to_smt i) = A ∧
        __smtx_typeof (__eo_to_smt e) = B ∧
        __smtx_typeof (__eo_to_smt idx) = A ∧
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) idx)) = B ∧
        B ≠ SmtType.None ∧
        RuleProofs.eo_has_smt_translation a ∧
        RuleProofs.eo_has_smt_translation e := by
  let storeTerm := Term.Apply (Term.Apply (Term.Apply Term.store a) i) e
  let selectTerm := Term.Apply (Term.Apply Term.select storeTerm) idx
  have hSelectNN :
      term_has_non_none_type
        (SmtTerm.select (SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e))
          (__eo_to_smt idx)) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type,
      RuleProofs.eo_to_smt_select_eq, RuleProofs.eo_to_smt_store_eq,
      storeTerm, selectTerm] using hArgTrans
  rcases Smtm.select_args_of_non_none hSelectNN with ⟨A, B, hStoreTy, hIdxTy⟩
  have hStoreNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e)) := by
    unfold term_has_non_none_type
    rw [hStoreTy]
    simp
  rcases Smtm.store_args_of_non_none hStoreNN with ⟨A', B', hATy, hITy, hETy⟩
  have hStoreTy' :
      SmtType.Map A' B' = SmtType.Map A B := by
    rw [Smtm.typeof_store_eq] at hStoreTy
    simpa [Smtm.typeof_store_eq, __smtx_typeof_store, native_ite, native_Teq,
      hATy, hITy, hETy] using hStoreTy
  cases hStoreTy'
  have hSelectTy :
      __smtx_typeof
          (SmtTerm.select
            (SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e))
            (__eo_to_smt idx)) = B := by
    rw [Smtm.typeof_select_eq]
    simp [__smtx_typeof_select, native_ite, native_Teq, hStoreTy, hIdxTy]
  have hBNonNone : B ≠ SmtType.None := by
    unfold term_has_non_none_type at hSelectNN
    rw [hSelectTy] at hSelectNN
    exact hSelectNN
  have hATrans : RuleProofs.eo_has_smt_translation a := by
    simp [RuleProofs.eo_has_smt_translation, hATy]
  have hETrans : RuleProofs.eo_has_smt_translation e := by
    simpa [RuleProofs.eo_has_smt_translation, hETy] using hBNonNone
  exact ⟨A, B, hATy, hITy, hETy, hIdxTy, by
    simpa [RuleProofs.eo_to_smt_select_eq, RuleProofs.eo_to_smt_store_eq,
      storeTerm, selectTerm] using hSelectTy, hBNonNone, hATrans, hETrans⟩

private theorem typed___eo_prog_arrays_read_over_write_1_impl
    (a i e i2 : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2) ->
  __eo_typeof
      (__eo_prog_arrays_read_over_write_1
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2)) =
    Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_arrays_read_over_write_1
      (Term.Apply
        (Term.Apply Term.select
          (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2)) := by
  intro hArgTrans hResultTy
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i
  let body := Term.Apply (Term.Apply Term.eq lhs) e
  have hProg :
      __eo_prog_arrays_read_over_write_1
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2) ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rw [prog_arrays_read_over_write_1_eq a i e i2] at hProg hResultTy
  have hi2 : i2 = i :=
    RuleProofs.eq_of_requires_eq_true_not_stuck i i2 body hProg
  subst i2
  have hINotStuck : i ≠ Term.Stuck := by
    intro hi
    subst i
    simp [__eo_requires, __eo_eq, native_ite, native_teq
      ] at hProg
  rcases smt_types_of_select_store_arg a i e i hArgTrans with
    ⟨A, B, hATy, hITy, hETy, _hIdxTy, hLhsTy, hBNonNone, _hATrans, _hETrans⟩
  rw [prog_arrays_read_over_write_1_eq a i e i]
  rw [requires_eq_self_true_body i body hINotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs e
    (by rw [hLhsTy, hETy])
    (by
      rw [hLhsTy]
      exact hBNonNone)

private theorem facts___eo_prog_arrays_read_over_write_1_impl
    (M : SmtModel) (hM : model_wf M) (a i e i2 : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2) ->
  __eo_typeof
      (__eo_prog_arrays_read_over_write_1
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2)) =
    Term.Bool ->
  eo_interprets M
    (__eo_prog_arrays_read_over_write_1
      (Term.Apply
        (Term.Apply Term.select
          (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2)) true := by
  intro hArgTrans hResultTy
  let lhs :=
    Term.Apply
      (Term.Apply Term.select
        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i
  let body := Term.Apply (Term.Apply Term.eq lhs) e
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arrays_read_over_write_1
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2)) :=
    typed___eo_prog_arrays_read_over_write_1_impl a i e i2 hArgTrans hResultTy
  have hProg :
      __eo_prog_arrays_read_over_write_1
          (Term.Apply
            (Term.Apply Term.select
              (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2) ≠
        Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hProgBool
  rw [prog_arrays_read_over_write_1_eq a i e i2] at hProg
  have hi2 : i2 = i :=
    RuleProofs.eq_of_requires_eq_true_not_stuck i i2 body hProg
  subst i2
  have hINotStuck : i ≠ Term.Stuck := by
    intro hi
    subst i
    simp [__eo_requires, __eo_eq, native_ite, native_teq
      ] at hProg
  have hArgTrans' :
      RuleProofs.eo_has_smt_translation lhs := by
    simpa [lhs] using hArgTrans
  rcases smt_types_of_select_store_arg a i e i hArgTrans' with
    ⟨A, B, hATy, hITy, hETy, _hIdxTy, _hLhsTy, _hBNonNone, hATrans, _hETrans⟩
  have hACan : value_canonical (__smtx_model_eval M (__eo_to_smt a)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM a hATrans
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        SmtType.Map A B := by
    rw [Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
      (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hATrans)]
    exact hATy
  rcases Smtm.map_value_canonical hEvalATy with ⟨m, hEvalA⟩
  have hMapCan : __smtx_map_canonical m = true := by
    rw [hEvalA] at hACan
    simpa [value_canonical, __smtx_value_canonical] using hACan
  rw [prog_arrays_read_over_write_1_eq a i e i]
  have hBodyBool : RuleProofs.eo_has_bool_type body := by
    have h := hProgBool
    rw [prog_arrays_read_over_write_1_eq a i e i] at h
    rw [requires_eq_self_true_body i body hINotStuck] at h
    exact h
  rw [requires_eq_self_true_body i body hINotStuck]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs e hBodyBool <| by
    have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store
              (SmtValue.Map m)
              (__smtx_model_eval M (__eo_to_smt i))
              (__smtx_model_eval M (__eo_to_smt e)))
            (__smtx_model_eval M (__eo_to_smt i)) =
          __smtx_model_eval M (__eo_to_smt e) := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        Smtm.map_lookup_update_aux_same
          (m := m) (i := __smtx_model_eval M (__eo_to_smt i))
          (e := __smtx_model_eval M (__eo_to_smt e)) hMapCan
    simpa [lhs, RuleProofs.eo_to_smt_select_eq, RuleProofs.eo_to_smt_store_eq,
      __smtx_model_eval, hEvalA, hLookup] using
      RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt e))

public theorem cmd_step_arrays_read_over_write_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_read_over_write_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arrays_read_over_write_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_read_over_write_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arrays_read_over_write_1 args premises ≠ Term.Stuck :=
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
              have hArgTrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              change __eo_typeof (__eo_prog_arrays_read_over_write_1 a1) = Term.Bool
                at hResultTy
              have hProgArg : __eo_prog_arrays_read_over_write_1 a1 ≠ Term.Stuck :=
                term_ne_stuck_of_typeof_bool hResultTy
              rcases shape_of_prog_arrays_read_over_write_1_not_stuck a1 hProgArg with
                ⟨a, i, e, i2, rfl⟩
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_arrays_read_over_write_1
                    (Term.Apply
                      (Term.Apply Term.select
                        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2)) true
                exact facts___eo_prog_arrays_read_over_write_1_impl M hM
                  a i e i2 hArgTrans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_arrays_read_over_write_1
                    (Term.Apply
                      (Term.Apply Term.select
                        (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i2))
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_arrays_read_over_write_1_impl
                    a i e i2 hArgTrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
